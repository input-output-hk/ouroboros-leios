/*
 * diffusion.c — Two-phase pull-based diffusion protocol.
 *
 * Phase 1: Manifest diffusion (atomic).
 *   OFFER_MANIFEST → REQUEST_MANIFEST → RESPONSE_MANIFEST
 *
 * Phase 2: Payload diffusion (component-level, sparse bitmap requests).
 *   OFFER → REQUEST → RESPONSE
 *
 * Both phases share the same NEXT_OFFER pipelining credit pool.
 * Everything is identified by the SHA-256 hash of the manifest.
 *
 * v1 fetching strategy: request all missing components from every peer.
 */

#include "node.h"
#include "scheduler_bridge.h"
#include <openssl/evp.h>

/* ---------------------------------------------------------------------------
 * Wire protocol
 * ------------------------------------------------------------------------ */

enum msg_type {
    MSG_NEXT_OFFER     = 1,
    MSG_OFFER_MANIFEST    = 2,
    MSG_REQUEST_MANIFEST  = 3,
    MSG_RESPONSE_MANIFEST = 4,
    MSG_OFFER             = 5,
    MSG_REQUEST           = 6,
    MSG_RESPONSE          = 7,
    MSG_CANCEL_CHUNK      = 8,
    MSG_CANCELED_RESPONSE = 9,
};

/* Wire format (multi-byte values in network byte order):
 *
 * NEXT_OFFER:
 *   [1B type]
 *
 * OFFER_MANIFEST:
 *   [1B type][32B manifest_hash][4B manifest_size]
 *
 * REQUEST_MANIFEST:
 *   [1B type][32B manifest_hash]
 *
 * RESPONSE_MANIFEST:
 *   [1B type][32B manifest_hash][4B manifest_size][manifest_data]
 *   manifest_data: (32B component_hash + 2B component_size) per component
 *
 * OFFER:
 *   [1B type][32B manifest_hash]
 *
 * REQUEST (sparse bitmap):
 *   [1B type][32B manifest_hash][4B seqno][1B num_pairs][1B offset, 8B word] x N
 *
 * RESPONSE:
 *   [1B type][32B manifest_hash][4B seqno][4B payload_size][repeated: 2B comp_id, 2B comp_size, data]
 */

/* ---------------------------------------------------------------------------
 * Helpers
 * ------------------------------------------------------------------------ */

static void compute_sha256(const void *data, size_t len, uint8_t hash[HASH_SIZE]) {
    unsigned int digest_len;
    EVP_Digest(data, len, hash, &digest_len, EVP_sha256(), NULL);
}

/* Log-friendly hash prefix: first 8 bytes as hex */
static const char *hash_hex(const uint8_t hash[HASH_SIZE]) {
    static char buf[17];
    for (int i = 0; i < 8; i++)
        sprintf(buf + 2 * i, "%02x", hash[i]);
    return buf;
}

static int peer_index(const peer_t *p) {
    return (int)(p - G.peers);
}

/* Consume one offer credit from the receiver's pipelining window */
static void track_offer_received(peer_t *p) {
    p->offers_received++;
    if (p->offers_received >= OFFER_WINDOW_REFILL) {
        for (int i = 0; i < OFFER_WINDOW_REFILL; i++)
            send_request_offer(p);
        p->offers_received -= OFFER_WINDOW_REFILL;
    }
}

/* ---------------------------------------------------------------------------
 * Payload management
 * ------------------------------------------------------------------------ */

static payload_t *find_payload(const uint8_t hash[HASH_SIZE]) {
    for (int i = 0; i < G.num_payloads; i++) {
        if (memcmp(G.payloads[i].manifest_hash, hash, HASH_SIZE) == 0)
            return &G.payloads[i];
    }
    return NULL;
}

/* Create a payload entry knowing only the manifest hash and size.
 * Component arrays are allocated later when the manifest arrives. */
static payload_t *create_payload(const uint8_t hash[HASH_SIZE], uint32_t manifest_size) {
    if (G.num_payloads >= MAX_PAYLOADS) {
        logmsg("ERROR: payload table full");
        return NULL;
    }
    payload_t *p = &G.payloads[G.num_payloads++];
    memset(p, 0, sizeof(*p));
    memcpy(p->manifest_hash, hash, HASH_SIZE);
    p->manifest_size = manifest_size;
    clock_gettime(CLOCK_MONOTONIC, &p->first_seen);
    return p;
}

/* Parse a received manifest and allocate component arrays. */
static void parse_manifest(payload_t *pl) {
    pl->num_components = pl->manifest_size / MANIFEST_ENTRY_SIZE;
    pl->comp_sizes  = calloc(pl->num_components, sizeof(uint16_t));
    pl->comp_hashes = calloc(pl->num_components, HASH_SIZE);
    pl->components  = calloc(pl->num_components, sizeof(component_t));

    for (uint16_t i = 0; i < pl->num_components; i++) {
        const uint8_t *entry = pl->manifest_data + i * MANIFEST_ENTRY_SIZE;
        memcpy(pl->comp_hashes[i], entry, HASH_SIZE);
        uint16_t sz;
        memcpy(&sz, entry + HASH_SIZE, 2);
        pl->comp_sizes[i] = ntohs(sz);
    }
}

static void check_payload_complete(payload_t *p) {
    if (p->complete) return;
    if (p->num_have == p->num_components) {
        p->complete = true;
        clock_gettime(CLOCK_MONOTONIC, &p->completed_at);
        double latency_ms =
            (p->completed_at.tv_sec - p->first_seen.tv_sec) * 1000.0 +
            (p->completed_at.tv_nsec - p->first_seen.tv_nsec) / 1e6;
        logmsg("COMPLETE %s components=%u latency=%.3fms",
               hash_hex(p->manifest_hash), p->num_components, latency_ms);
    }
}

/* ---------------------------------------------------------------------------
 * Protocol: sending messages
 * ------------------------------------------------------------------------ */

void send_request_offer(peer_t *p) {
    uint8_t msg = MSG_NEXT_OFFER;
    peer_queue_write(p, &msg, 1);
    p->offers_sent++;
}

static void send_offer_manifest(peer_t *p, payload_t *pl) {
    /* 1B type + 32B hash + 4B size */
    uint8_t buf[1 + HASH_SIZE + 4];
    buf[0] = MSG_OFFER_MANIFEST;
    memcpy(buf + 1, pl->manifest_hash, HASH_SIZE);
    uint32_t net_sz = htonl(pl->manifest_size);
    memcpy(buf + 1 + HASH_SIZE, &net_sz, 4);
    peer_queue_write_priority(p, buf, sizeof(buf));
}

static void send_request_manifest(peer_t *p, const uint8_t hash[HASH_SIZE]) {
    /* 1B type + 32B hash */
    uint8_t buf[1 + HASH_SIZE];
    buf[0] = MSG_REQUEST_MANIFEST;
    memcpy(buf + 1, hash, HASH_SIZE);
    peer_queue_write_priority(p, buf, sizeof(buf));
}

static void send_response_manifest(peer_t *p, payload_t *pl) {
    /* 1B type + 32B hash + 4B size + manifest_data */
    size_t len = 1 + HASH_SIZE + 4 + pl->manifest_size;
    uint8_t *buf = malloc(len);
    size_t off = 0;

    buf[off++] = MSG_RESPONSE_MANIFEST;
    memcpy(buf + off, pl->manifest_hash, HASH_SIZE); off += HASH_SIZE;
    uint32_t net_sz = htonl(pl->manifest_size);
    memcpy(buf + off, &net_sz, 4); off += 4;
    memcpy(buf + off, pl->manifest_data, pl->manifest_size);

    peer_queue_write_priority(p, buf, len);
    free(buf);
}

static void send_offer(peer_t *p, payload_t *pl) {
    /* 1B type + 32B hash */
    uint8_t buf[1 + HASH_SIZE];
    buf[0] = MSG_OFFER;
    memcpy(buf + 1, pl->manifest_hash, HASH_SIZE);
    peer_queue_write_priority(p, buf, sizeof(buf));
}

#define BITMAP_WORDS ((MAX_COMPONENTS + 63) / 64)  /* 235 for 15000 */

static void send_request(peer_t *p, payload_t *pl,
                          const uint16_t *comp_ids, uint16_t count) {
    /* Build sparse bitmap */
    uint64_t bitmap[BITMAP_WORDS];
    memset(bitmap, 0, sizeof(bitmap));
    for (uint16_t i = 0; i < count; i++)
        bitmap[comp_ids[i] / 64] |= (uint64_t)1 << (comp_ids[i] % 64);

    uint8_t num_pairs = 0;
    for (int i = 0; i < BITMAP_WORDS; i++)
        if (bitmap[i]) num_pairs++;

    /* 1B type + 32B hash + 1B num_pairs + (1B offset + 8B word) * N */
    size_t len = 1 + HASH_SIZE + 1 + 9 * (size_t)num_pairs;
    uint8_t *buf = malloc(len);
    size_t off = 0;

    buf[off++] = MSG_REQUEST;
    memcpy(buf + off, pl->manifest_hash, HASH_SIZE); off += HASH_SIZE;
    buf[off++] = num_pairs;

    for (int i = 0; i < BITMAP_WORDS; i++) {
        if (!bitmap[i]) continue;
        buf[off++] = (uint8_t)i;
        uint64_t net_word = htobe64(bitmap[i]);
        memcpy(buf + off, &net_word, 8); off += 8;
    }

    peer_queue_write(p, buf, len);
    free(buf);
}

/* Send a bundled RESPONSE containing multiple components.
 * Wire format:
 *   [1B type][32B hash][4B seqno][4B payload_size][repeated: 2B comp_id, 2B comp_size, data]
 * payload_size covers everything after itself. */
static void send_response(peer_t *p, payload_t *pl,
                          uint32_t seqno,
                          const uint16_t *comp_ids, uint16_t count) {
    /* Compute total payload size. */
    uint32_t payload_size = 0;
    for (uint16_t i = 0; i < count; i++)
        payload_size += 2 + 2 + pl->components[comp_ids[i]].size;

    size_t len = 1 + HASH_SIZE + 4 + 4 + payload_size;
    uint8_t *buf = malloc(len);
    size_t off = 0;

    buf[off++] = MSG_RESPONSE;
    memcpy(buf + off, pl->manifest_hash, HASH_SIZE); off += HASH_SIZE;
    uint32_t net_seqno = htonl(seqno);
    memcpy(buf + off, &net_seqno, 4); off += 4;
    uint32_t net_psz = htonl(payload_size);
    memcpy(buf + off, &net_psz, 4); off += 4;

    for (uint16_t i = 0; i < count; i++) {
        uint16_t cid = comp_ids[i];
        component_t *c = &pl->components[cid];
        uint16_t net_cid = htons(cid);
        memcpy(buf + off, &net_cid, 2); off += 2;
        uint16_t net_sz = htons(c->size);
        memcpy(buf + off, &net_sz, 2); off += 2;
        memcpy(buf + off, c->data, c->size); off += c->size;
    }

    peer_queue_write_tagged(p, buf, len, pl->manifest_hash, seqno);
    free(buf);
}



/* Scheduler-driven request: send a request using a pre-built component bitmap.
 * Wire format: [1B type][32B hash][4B seqno][1B num_pairs][1B offset, 8B word] x N
 * The seqno is echoed in MSG_CANCEL_CHUNK so the receiver knows which request to abort. */
void send_request_bitmap(peer_t *p, const uint8_t hash[HASH_SIZE],
                         int seqno,
                         const uint8_t *bitmap, size_t bitmap_len) {
    /* Convert byte bitmap to sparse (offset, word) pairs. */
    size_t num_words = (bitmap_len + 7) / 8;
    uint8_t num_pairs = 0;
    for (size_t i = 0; i < num_words; i++) {
        uint64_t word = 0;
        for (size_t b = 0; b < 8 && i * 8 + b < bitmap_len; b++)
            word |= (uint64_t)bitmap[i * 8 + b] << (b * 8);
        if (word) num_pairs++;
    }

    size_t len = 1 + HASH_SIZE + 4 + 1 + 9 * (size_t)num_pairs;
    uint8_t *buf = malloc(len);
    size_t off = 0;

    buf[off++] = MSG_REQUEST;
    memcpy(buf + off, hash, HASH_SIZE); off += HASH_SIZE;
    uint32_t net_seqno = htonl((uint32_t)seqno);
    memcpy(buf + off, &net_seqno, 4); off += 4;
    buf[off++] = num_pairs;

    for (size_t i = 0; i < num_words; i++) {
        uint64_t word = 0;
        for (size_t b = 0; b < 8 && i * 8 + b < bitmap_len; b++)
            word |= (uint64_t)bitmap[i * 8 + b] << (b * 8);
        if (!word) continue;
        buf[off++] = (uint8_t)i;
        uint64_t net_word = htobe64(word);
        memcpy(buf + off, &net_word, 8); off += 8;
    }

    peer_queue_write(p, buf, len);
    free(buf);
}

/* Cancel a specific request by seqno.
 * Wire format: [1B type][4B seqno] */
void send_cancel_chunk(peer_t *p, int seqno) {
    uint8_t buf[5];
    buf[0] = MSG_CANCEL_CHUNK;
    uint32_t net_seqno = htonl((uint32_t)seqno);
    memcpy(buf + 1, &net_seqno, 4);
    peer_queue_write_priority(p, buf, sizeof(buf));
}

/* ---------------------------------------------------------------------------
 * Offer manifest and/or payload to all peers with credits
 * ------------------------------------------------------------------------ */

static void offer_manifest_to_all_peers(payload_t *pl) {
    for (int i = 0; i < G.num_peers; i++) {
        peer_t *peer = &G.peers[i];
        if (peer->connected && peer->offer_credits > 0) {
            peer->offer_credits--;
            send_offer_manifest(peer, pl);
        }
    }
}

static void offer_payload_to_all_peers(payload_t *pl) {
    for (int i = 0; i < G.num_peers; i++) {
        peer_t *peer = &G.peers[i];
        if (peer->connected && peer->offer_credits > 0) {
            peer->offer_credits--;
            send_offer(peer, pl);
        }
    }
}

/* v1 fetching: request ALL components we don't have, from this peer.
 * Splits into multiple REQUEST messages so each RESPONSE fits in
 * REQUEST_CHUNK_BYTES of component data. */
static void request_missing_components(peer_t *p, payload_t *pl) {
    if (pl->complete) return;

    uint16_t *chunk = malloc(pl->num_components * sizeof(uint16_t));
    uint16_t chunk_count = 0;
    uint32_t chunk_bytes = 0;

    for (uint16_t i = 0; i < pl->num_components; i++) {
        if (pl->components[i].size != 0) continue;

        uint32_t comp_wire = 2 + 2 + pl->comp_sizes[i];  /* comp_id + comp_size + data */
        if (chunk_count > 0 && chunk_bytes + comp_wire > REQUEST_CHUNK_BYTES) {
            send_request(p, pl, chunk, chunk_count);
            chunk_count = 0;
            chunk_bytes = 0;
        }
        chunk[chunk_count++] = i;
        chunk_bytes += comp_wire;
    }
    if (chunk_count > 0)
        send_request(p, pl, chunk, chunk_count);
    free(chunk);
}

/* Request components from peer if it has offered and we haven't asked yet. */
static void try_request_from(peer_t *p, payload_t *pl) {
    uint64_t bit = (uint64_t)1 << peer_index(p);
    if (!(pl->offered_by & bit)) return;
    if (pl->requested_from & bit) return;
    if (!pl->manifest_data) return;
    pl->requested_from |= bit;
    request_missing_components(p, pl);
}

/* ---------------------------------------------------------------------------
 * Protocol: handling incoming messages
 * ------------------------------------------------------------------------ */

size_t handle_message(peer_t *p, const uint8_t *data, size_t len) {
    if (len < 1) return 0;

    switch (data[0]) {

    case MSG_NEXT_OFFER: {
        p->offer_credits++;
        return 1;
    }

    case MSG_OFFER_MANIFEST: {
        /* 1B type + 32B hash + 4B size = 37 */
        if (len < 37) return 0;
        const uint8_t *hash = data + 1;
        uint32_t manifest_size;
        memcpy(&manifest_size, data + 33, 4);
        manifest_size = ntohl(manifest_size);

        track_offer_received(p);

        payload_t *pl = find_payload(hash);
        if (!pl) {
            pl = create_payload(hash, manifest_size);
            if (!pl) return 37;
            logmsg("NEW manifest %s size=%u from %s",
                   hash_hex(hash), manifest_size, p->addr_str);
        }

        /* Request manifest if we don't have it */
        if (!pl->manifest_data) {
            send_request_manifest(p, hash);
        }

        return 37;
    }

    case MSG_REQUEST_MANIFEST: {
        /* 1B type + 32B hash = 33 */
        if (len < 33) return 0;
        const uint8_t *hash = data + 1;

        payload_t *pl = find_payload(hash);
        if (pl && pl->manifest_data) {
            send_response_manifest(p, pl);
        } else {
            logmsg("WARN: REQUEST_MANIFEST for unknown/incomplete %s from %s",
                   hash_hex(hash), p->addr_str);
        }

        return 33;
    }

    case MSG_RESPONSE_MANIFEST: {
        /* 1B type + 32B hash + 4B size + data */
        if (len < 37) return 0;
        const uint8_t *hash = data + 1;
        uint32_t manifest_size;
        memcpy(&manifest_size, data + 33, 4);
        manifest_size = ntohl(manifest_size);

        size_t msg_len = 37 + manifest_size;
        if (len < msg_len) return 0;

        payload_t *pl = find_payload(hash);
        if (!pl) {
            logmsg("WARN: RESPONSE_MANIFEST for unknown %s", hash_hex(hash));
            return msg_len;
        }

        if (!pl->manifest_data) {
            /* Verify hash */
            uint8_t computed[HASH_SIZE];
            compute_sha256(data + 37, manifest_size, computed);
            if (memcmp(computed, hash, HASH_SIZE) != 0) {
                logmsg("WARN: manifest hash mismatch for %s from %s",
                       hash_hex(hash), p->addr_str);
                return msg_len;
            }

            pl->manifest_data = malloc(manifest_size);
            memcpy(pl->manifest_data, data + 37, manifest_size);
            pl->manifest_size = manifest_size;
            parse_manifest(pl);

            logmsg("MANIFEST %s components=%u from %s",
                   hash_hex(hash), pl->num_components, p->addr_str);

            /* Propagate: offer manifest to our peers */
            offer_manifest_to_all_peers(pl);

            /* Notify scheduler */
            scheduler_manifest_received(hash, pl->comp_sizes, pl->num_components);
        }

        return msg_len;
    }

    case MSG_OFFER: {
        /* 1B type + 32B hash = 33 */
        if (len < 33) return 0;
        const uint8_t *hash = data + 1;

        track_offer_received(p);

        payload_t *pl = find_payload(hash);
        if (!pl) return 33;

        pl->offered_by |= (uint64_t)1 << peer_index(p);

        /* Notify scheduler */
        {
            int peer_nid = ntohl(p->addr_ip) & 0xFF;
            scheduler_offer_received(peer_nid, hash, p);
        }

        return 33;
    }

    case MSG_REQUEST: {
        /* 1B type + 32B hash + 4B seqno + 1B num_pairs + (1B + 8B) * N */
        if (len < 38) return 0;
        const uint8_t *hash = data + 1;
        uint32_t seqno;
        memcpy(&seqno, data + 33, 4);
        seqno = ntohl(seqno);
        uint8_t num_pairs = data[37];

        size_t msg_len = 38 + 9 * (size_t)num_pairs;
        if (len < msg_len) return 0;

        payload_t *pl = find_payload(hash);
        if (!pl) {
            logmsg("WARN: REQUEST for unknown %s from %s",
                   hash_hex(hash), p->addr_str);
            return msg_len;
        }

        /* Collect requested component IDs, then send one bundled RESPONSE. */
        uint16_t *ids = malloc(pl->num_components * sizeof(uint16_t));
        uint16_t id_count = 0;

        for (uint8_t i = 0; i < num_pairs; i++) {
            uint8_t word_offset = data[38 + 9 * i];
            uint64_t word;
            memcpy(&word, data + 38 + 9 * i + 1, 8);
            word = be64toh(word);

            uint16_t base = (uint16_t)word_offset * 64;
            while (word) {
                int bit = __builtin_ctzll(word);
                uint16_t cid = base + bit;
                if (cid < pl->num_components && pl->components[cid].size > 0)
                    ids[id_count++] = cid;
                word &= word - 1;
            }
        }

        if (id_count > 0)
            send_response(p, pl, seqno, ids, id_count);
        free(ids);
        return msg_len;
    }

    case MSG_RESPONSE: {
        /* [1B type][32B hash][4B seqno][4B payload_size][repeated: 2B comp_id, 2B comp_size, data] */
        if (len < 41) return 0;
        const uint8_t *hash = data + 1;

        uint32_t seqno;
        memcpy(&seqno, data + 33, 4);
        seqno = ntohl(seqno);

        uint32_t payload_size;
        memcpy(&payload_size, data + 37, 4);
        payload_size = ntohl(payload_size);

        size_t msg_len = 1 + HASH_SIZE + 4 + 4 + payload_size;
        if (len < msg_len) return 0;

        payload_t *pl = find_payload(hash);
        if (!pl || !pl->manifest_data) {
            logmsg("WARN: RESPONSE for unknown %s", hash_hex(hash));
            return msg_len;
        }

        /* Parse bundled components. */
        size_t off = 1 + HASH_SIZE + 4 + 4;
        while (off < msg_len) {
            uint16_t comp_id;
            memcpy(&comp_id, data + off, 2);
            comp_id = ntohs(comp_id);
            off += 2;

            uint16_t comp_size;
            memcpy(&comp_size, data + off, 2);
            comp_size = ntohs(comp_size);
            off += 2;

            if (comp_id < pl->num_components && pl->components[comp_id].size == 0) {
                pl->components[comp_id].size = comp_size;
                memcpy(pl->components[comp_id].data, data + off, comp_size);
                pl->num_have++;
            }
            off += comp_size;
        }

        /* Notify scheduler. The seqno identifies which chunk.
         * The scheduler handles cancellation of redundant requests. */
        {
            int peer_nid = ntohl(p->addr_ip) & 0xFF;
            scheduler_chunk_delivered(peer_nid, (int)seqno, p);
        }

        bool was_complete = pl->complete;
        check_payload_complete(pl);
        if (pl->complete && !was_complete) {
            offer_payload_to_all_peers(pl);
        }

        return msg_len;
    }

    case MSG_CANCEL_CHUNK: {
        /* 1B type + 4B seqno = 5 */
        if (len < 5) return 0;
        uint32_t seqno;
        memcpy(&seqno, data + 1, 4);
        seqno = ntohl(seqno);

        /* Only confirm if we actually purged the response from our write
         * queue. If not purged, the original MSG_RESPONSE is already on the
         * wire (or fully kernel-buffered) and will arrive normally. */
        if (peer_purge_seqno(p, seqno)) {
            uint8_t resp[5];
            resp[0] = MSG_CANCELED_RESPONSE;
            uint32_t net_seqno = htonl(seqno);
            memcpy(resp + 1, &net_seqno, 4);
            peer_queue_write_priority(p, resp, sizeof(resp));
            logmsg("CANCEL_CHUNK seqno=%u from %s: purged", seqno, p->addr_str);
        } else {
            logmsg("CANCEL_CHUNK seqno=%u from %s: too late", seqno, p->addr_str);
        }

        return 5;
    }

    case MSG_CANCELED_RESPONSE: {
        /* 1B type + 4B seqno = 5 */
        if (len < 5) return 0;
        uint32_t seqno;
        memcpy(&seqno, data + 1, 4);
        seqno = ntohl(seqno);

        int peer_nid = ntohl(p->addr_ip) & 0xFF;
        scheduler_cancel_confirmed(peer_nid, (int)seqno, p);

        return 5;
    }

    default:
        logmsg("ERROR: unknown message type %u from %s", data[0], p->addr_str);
        return len;
    }
}

/* ---------------------------------------------------------------------------
 * Payload injection from schedule
 * ------------------------------------------------------------------------ */

void inject_scheduled_payload(void) {
    schedule_entry_t *e = &G.schedule[G.schedule_next];

    /* Build component data and compute per-component hashes */
    uint16_t nc = e->num_components;
    component_t *components = calloc(nc, sizeof(component_t));
    uint8_t (*comp_hashes)[HASH_SIZE] = calloc(nc, HASH_SIZE);

    size_t total_size = 0;
    for (uint16_t i = 0; i < nc; i++) {
        uint16_t sz = e->comp_sizes[i];
        components[i].size = sz;
        /* Fill with deterministic data (content doesn't matter for
         * diffusion). Seeded only by the component index so that
         * co-injections of the same components at different nodes
         * produce the same manifest hash. */
        memset(components[i].data, i & 0xff, sz);
        compute_sha256(components[i].data, sz, comp_hashes[i]);
        total_size += sz;
    }

    /* Build manifest: (32B hash + 2B size) per component */
    uint32_t manifest_size = nc * MANIFEST_ENTRY_SIZE;
    uint8_t *manifest_data = malloc(manifest_size);
    for (uint16_t i = 0; i < nc; i++) {
        uint8_t *entry = manifest_data + i * MANIFEST_ENTRY_SIZE;
        memcpy(entry, comp_hashes[i], HASH_SIZE);
        uint16_t net_sz = htons(e->comp_sizes[i]);
        memcpy(entry + HASH_SIZE, &net_sz, 2);
    }

    /* Compute manifest hash */
    uint8_t manifest_hash[HASH_SIZE];
    compute_sha256(manifest_data, manifest_size, manifest_hash);

    /* Create payload entry */
    payload_t *pl = create_payload(manifest_hash, manifest_size);
    if (!pl) {
        free(components);
        free(comp_hashes);
        free(manifest_data);
        return;
    }

    pl->manifest_data = manifest_data;
    pl->num_components = nc;
    pl->comp_sizes = malloc(nc * sizeof(uint16_t));
    memcpy(pl->comp_sizes, e->comp_sizes, nc * sizeof(uint16_t));
    pl->comp_hashes = comp_hashes;
    pl->components = components;
    pl->num_have = nc;
    pl->complete = true;
    clock_gettime(CLOCK_MONOTONIC, &pl->completed_at);

    logmsg("INJECT \"%s\" %s components=%u size=%zu",
           e->nickname, hash_hex(manifest_hash), nc, total_size);

    offer_manifest_to_all_peers(pl);
    offer_payload_to_all_peers(pl);
}
