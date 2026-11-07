#ifndef SCHEDULER_BRIDGE_H
#define SCHEDULER_BRIDGE_H

#include "node.h"

/* Initialize the embedded Python interpreter and import FetchScheduler. */
void scheduler_init(int hedge_threshold_bytes);

/* Events: call these from diffusion.c at the appropriate points.
 * Each reads CLOCK_REALTIME internally to compute elapsed time. */
void scheduler_peer_hint(int peer_id, int bw_mbit, int rtt_us);

void scheduler_manifest_received(const uint8_t hash[HASH_SIZE],
                                 const uint16_t *comp_sizes,
                                 uint16_t num_components);

void scheduler_offer_received(int peer_id,
                              const uint8_t hash[HASH_SIZE],
                              peer_t *peer);

void scheduler_chunk_delivered(int peer_id,
                               int seqno,
                               peer_t *peer);

void scheduler_cancel_confirmed(int peer_id,
                                int seqno,
                                peer_t *peer);

/* Fire a BdpEstimated event at the Python scheduler with the oracle
 * BDP values parsed from the topology JSON for this peer. Called from
 * the StartProbe action handler. */
void scheduler_bdp_estimated(int peer_id, peer_t *peer);

/* Timer callback — called from the epoll loop. */
void scheduler_timer_fired(int peer_id);  /* -1 for rebalance timer */

/* Epoll integration. */
bool is_scheduler_timer(void *ptr);
void handle_scheduler_timer(void *ptr);
bool is_oracle_timer(void *ptr);
void handle_oracle_timer(void *ptr);

#endif /* SCHEDULER_BRIDGE_H */
