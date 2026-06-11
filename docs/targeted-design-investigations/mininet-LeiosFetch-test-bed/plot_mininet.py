#!/usr/bin/env python3
"""
Plot per-edge end-to-end goodput from correlated sender write traces
and receiver pcap captures.

For each directed edge A->B:
  - Sender side: A's write trace (stdout) records when the application
    pushed bytes into the socket, with CLOCK_REALTIME timestamps taken
    BEFORE the write() syscall.
  - Receiver side: B's pcap captures when packets arrived after
    traversing the full tc stack (htb + netem + fq_codel).

Per-packet goodput is computed as payload_size / dt_prev (time since
previous significant packet).  To smooth over htb token-bucket artifacts
that cause per-packet rate spikes, we average over a rolling window of
RATE_WINDOW packets.
"""

import json
import os
import struct
import socket
import sys
from collections import defaultdict, Counter
from scapy.all import PcapReader, TCP, IP
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

def ip_node_id(ip):
    """Extract the integer node ID from an IP like '10.0.0.7' -> 7."""
    return int(ip.split('.')[-1])

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
RESULTS_DIR = os.environ.get("RESULTS_DIR", os.path.join(SCRIPT_DIR, "mininet-results"))
YMAX = 100           # Mbit/s; subplots exceeding this show a break indicator
YMIN = -10           # Mbit/s; reserved below the x-axis for loss tick marks
MIN_PAYLOAD = 50     # bytes; packets below this are excluded from rate timing
BIN_WIDTH = 0.1      # seconds; for the dashed binned overlay

def load_ip_names():
    """Build IP_NAMES from input.json in the results directory."""
    import json
    with open(os.path.join(RESULTS_DIR, "input.json")) as f:
        meta = json.load(f)
    node_ids = set()
    for e in meta["edges"]:
        node_ids.add(e["a"])
        node_ids.add(e["b"])
    return {"10.0.0.%d" % n: "node%d" % n for n in node_ids}

IP_NAMES = load_ip_names()
NODE_IPS = {v: k for k, v in IP_NAMES.items()}

TRACE_FMT = "<dIHI"  # double + uint32 + uint16 + uint32 = 18 bytes
TRACE_SZ = struct.calcsize(TRACE_FMT)


def load_node_events():
    """Parse INJECT and COMPLETE events from node stderr logs.

    Elapsed times in stderr are relative to the shared epoch (G.start_time),
    so they map directly to x-axis values.

    Returns (completions, injections) where each is
    dict: node_id -> [(elapsed_time, payload_hash_prefix), ...]"""
    import re
    completions = {}
    injections = {}
    for name in sorted(NODE_IPS.keys()):
        node_id = ip_node_id(NODE_IPS[name])
        path = os.path.join(RESULTS_DIR, name + ".stderr")
        if not os.path.exists(path):
            continue

        comp_events = []
        inj_events = []
        with open(path) as f:
            for line in f:
                m = re.match(r'\[.*? ([\d.-]+)\] COMPLETE (\S+)', line)
                if m:
                    comp_events.append((float(m.group(1)), m.group(2)[:8]))
                    continue
                m = re.match(r'\[.*? ([\d.-]+)\] INJECT .* (\S+) components', line)
                if m:
                    inj_events.append((float(m.group(1)), m.group(2)[:8]))
        completions[node_id] = comp_events
        injections[node_id] = inj_events
    return completions, injections


def load_schedule(meta):
    # Each schedule entry has `time` and `node` either both scalars
    # (single injection) or both arrays of equal, non-empty length
    # (same payload injected at several (time, node) pairs).
    out = []
    for e in meta.get("schedule", []):
        t, n = e["time"], e["node"]
        t_list = t if isinstance(t, list) else [t]
        n_list = n if isinstance(n, list) else [n]
        if not t_list or len(t_list) != len(n_list):
            raise ValueError(
                f"schedule entry {e.get('nickname')!r}: time and node must be "
                f"both scalars or both arrays of the same non-zero length")
        for time_s, node_id in zip(t_list, n_list):
            out.append((time_s, node_id, e["nickname"]))
    return out


def read_write_trace(node_name):
    """Read a node's stdout write trace.
    Returns dict: dst_ip -> [(wallclock, bytes_written), ...]"""
    path = os.path.join(RESULTS_DIR, node_name + ".stdout")
    if not os.path.exists(path):
        return {}
    with open(path, "rb") as f:
        data = f.read()

    by_dst = defaultdict(list)
    for i in range(len(data) // TRACE_SZ):
        wallclock, dip, dport, nbytes = struct.unpack_from(TRACE_FMT, data, i * TRACE_SZ)
        if nbytes == 0:
            continue
        ip_str = socket.inet_ntoa(struct.pack("<I", dip))
        by_dst[ip_str].append((wallclock, nbytes))

    for k in by_dst:
        by_dst[k].sort()
    return by_dst


def read_pcap_full(node_name, node_ip):
    """Single-pass scan of a node's pcap returning both ingress and egress data.
    Returns (recv_events, recv_count, send_times):
    - recv_events: dict src_ip -> [(wallclock, payload_bytes), ...] dedup by seq
                   (used for goodput; spurious retransmits suppressed)
    - recv_count:  dict src_ip -> Counter[(sport, dport, seq)] over ALL arrivals
                   (used for loss accounting; counts duplicates)
    - send_times:  dict dst_ip -> dict[(sport, dport, seq) -> [t1, t2, ...]]
                   (every send timestamp per segment, in order)
    """
    path = os.path.join(RESULTS_DIR, node_name + ".pcap")
    if not os.path.exists(path) or os.path.getsize(path) < 40:
        # Missing pcap, or smaller than a pcap header (24 B global + minimum
        # record header) — nothing to read. Happens for --duration 0 runs.
        return {}, {}, {}

    recv_events = defaultdict(list)
    recv_count = defaultdict(Counter)
    send_times = defaultdict(lambda: defaultdict(list))
    seen_recv = set()
    print(f"Reading {path}...", file=sys.stderr)
    with PcapReader(path) as reader:
        for pkt in reader:
            if not pkt.haslayer(IP) or not pkt.haslayer(TCP):
                continue
            src = pkt[IP].src
            dst = pkt[IP].dst
            t = float(pkt.time)
            sport = pkt[TCP].sport
            dport = pkt[TCP].dport
            seq = pkt[TCP].seq
            ip_hdr = pkt[IP].ihl * 4
            tcp_hdr = pkt[TCP].dataofs * 4
            payload = pkt[IP].len - ip_hdr - tcp_hdr
            if payload <= 0:
                continue
            key = (sport, dport, seq)
            if src == node_ip:
                send_times[dst][key].append(t)
            else:
                full_key = (src, sport, dport, seq)
                if full_key not in seen_recv:
                    seen_recv.add(full_key)
                    recv_events[src].append((t, payload))
                recv_count[src][key] += 1

    for k in recv_events:
        recv_events[k].sort()
    # Materialise nested defaultdicts.
    send_times_out = {dst: dict(d) for dst, d in send_times.items()}
    return dict(recv_events), dict(recv_count), send_times_out


def compute_rate_series(recv_events, write_events, link_delay_s, t_min):
    """Compute per-packet goodput from received packets.
    Uses sender write trace to avoid inflating dt across transfer gaps:
    if the sender only recently started writing, dt is capped at
    (recv_time - most_recent_write_time + link_delay).
    Returns (times, rates) arrays for plotting."""
    big = [(t - t_min, payload) for t, payload in recv_events if payload >= MIN_PAYLOAD]
    if len(big) < 2:
        return [], []

    # Build sorted list of write times (shifted to same t_min basis).
    wtimes = sorted(t - t_min for t, _ in write_events) if write_events else []

    def most_recent_write_before(t):
        """Binary search for the latest write time <= t."""
        lo, hi = 0, len(wtimes)
        while lo < hi:
            mid = (lo + hi) // 2
            if wtimes[mid] <= t:
                lo = mid + 1
            else:
                hi = mid
        return wtimes[lo - 1] if lo > 0 else None

    times = []
    rates = []
    for i in range(1, len(big)):
        dt_prev = big[i][0] - big[i-1][0]

        # Cap dt if the sender only started writing recently.
        w = most_recent_write_before(big[i][0])
        if w is not None:
            dt_write = big[i][0] - w + link_delay_s
            dt = min(dt_prev, dt_write)
        else:
            dt = dt_prev

        if dt <= 0:
            continue
        rate = big[i][1] * 8 / dt / 1e6
        times.append(big[i][0])
        rates.append(rate)

    return times, rates


def compute_binned_series(recv_events, t_min):
    """Compute 0.1s-binned goodput from received packets.
    Returns (times, rates) arrays for the dashed overlay."""
    if not recv_events:
        return [], []

    bins = defaultdict(int)
    for t, payload in recv_events:
        b = int((t - t_min) / BIN_WIDTH)
        bins[b] += payload

    if not bins:
        return [], []

    b_min = min(bins)
    b_max = max(bins)
    times = []
    rates = []
    for b in range(b_min, b_max + 1):
        times.append(b * BIN_WIDTH)
        rates.append(bins.get(b, 0) * 8 / BIN_WIDTH / 1e6)

    return times, rates


def plot():
    # Load metadata.
    with open(os.path.join(RESULTS_DIR, "input.json")) as f:
        meta = json.load(f)

    schedule = load_schedule(meta)

    edge_meta = {}
    for e in meta["edges"]:
        ip_a = "10.0.0.%d" % e["a"]
        ip_b = "10.0.0.%d" % e["b"]
        edge_meta[tuple(sorted([ip_a, ip_b], key=ip_node_id))] = e

    # Read epoch (shared time origin) from t0.txt.
    with open(os.path.join(RESULTS_DIR, "t0.txt")) as f:
        t_min = float(f.read().strip())

    # Read all write traces and pcaps. Each pcap is scanned once for
    # ingress events, ingress seq sets, and egress first-send timestamps.
    write_traces = {}  # node_name -> {dst_ip -> [(t, bytes)]}
    recv_pcaps = {}    # node_name -> {src_ip -> [(t, bytes)]}
    recv_count = {}    # node_name -> {src_ip -> Counter[(sport, dport, seq)]}
    send_times = {}    # node_name -> {dst_ip -> {(sport, dport, seq) -> [t, ...]}}

    for name, ip in sorted(NODE_IPS.items()):
        write_traces[name] = read_write_trace(name)
        recv_pcaps[name], recv_count[name], send_times[name] = read_pcap_full(name, ip)

    def loss_times(src_name, dst_name, src_ip, dst_ip):
        """Sender-side timestamps of dropped segments. For each
        (sport, dport, seq), n_loss = max(0, n_sent - n_received); the
        first n_loss send timestamps are taken as the loss events.
        Captures retransmission-recovered drops too. Includes both netem
        and AQM drops — no disambiguation."""
        sent = send_times.get(src_name, {}).get(dst_ip, {})
        arrived = recv_count.get(dst_name, {}).get(src_ip, Counter())
        out = []
        for k, ts in sent.items():
            n_loss = max(0, len(ts) - arrived.get(k, 0))
            out.extend(ts[:n_loss])
        out.sort()
        return out

    # Discover all directed edges that have recv data.
    directed_edges = set()
    for recv_name, by_src in recv_pcaps.items():
        recv_ip = NODE_IPS[recv_name]
        for src_ip in by_src:
            if src_ip in IP_NAMES:
                directed_edges.add((src_ip, recv_ip))

    # Debug: print loss-event times to stdout, per directed edge.
    for src_ip, dst_ip in sorted(directed_edges,
                                 key=lambda e: (ip_node_id(e[0]), ip_node_id(e[1]))):
        src_name = IP_NAMES[src_ip]
        dst_name = IP_NAMES[dst_ip]
        losses = loss_times(src_name, dst_name, src_ip, dst_ip)
        print("[%s -> %s] %d losses" % (src_name, dst_name, len(losses)))
        for t in losses:
            print("  %.6f" % (t - t_min))

    # Group into undirected edges.
    undirected = {}
    for src, dst in sorted(directed_edges):
        key = tuple(sorted([src, dst], key=ip_node_id))
        if key not in undirected:
            undirected[key] = []
        undirected[key].append((src, dst))

    undirected_edges = sorted(undirected.keys(),
                              key=lambda ips: tuple(ip_node_id(ip) for ip in ips))

    # Exclude edges where neither side pulls (no data flows).
    undirected_edges = [ue for ue in undirected_edges
                        if ue in edge_meta
                        and (edge_meta[ue]["a_pulls"]
                             or edge_meta[ue]["b_pulls"])]

    completions, injections = load_node_events()

    suptitle = ("Per-Edge End-to-End Goodput (Mininet, %d Mbit NICs, fq_codel, per-pkt)"
                % meta["nic_bw_mbit"])

    # Find global x range so all subplots share the same time axis.
    all_recv_times = [t - t_min for by_src in recv_pcaps.values()
                      for events in by_src.values() for t, _ in events]
    x_min = min(all_recv_times) * 1.02 if all_recv_times else -1
    x_max = max(all_recv_times) * 1.02 if all_recv_times else 1

    tuned = set(meta.get("tuned_initcwnd", []))
    nicknames = meta.get("node_nicknames", {})

    def node_parts(ip):
        node_id = ip_node_id(ip)
        name = IP_NAMES.get(ip, ip)
        if node_id in tuned:
            name += "*"
        nick = nicknames.get(str(node_id), "")
        return nick, name

    from io import BytesIO
    import base64

    def render_subplot(idx, uedge, scatter_alpha):
        """Render one edge subplot, return PNG bytes."""
        fig, ax = plt.subplots(1, 1, figsize=(14, 2.5))
        subplot_peak = 0

        # Injection markers (behind everything). Only those within the
        # observed data range — later scheduled injections never
        # happened and would expand the x-axis beyond the data.
        visible_schedule = [s for s in schedule if s[0] <= x_max]

        for time_s, node_id, nickname in visible_schedule:
            ax.axvline(time_s, color="magenta", linestyle="-", linewidth=0.8, alpha=0.6)

        if idx == 0:
            for time_s, node_id, nickname in visible_schedule:
                ax.annotate(f"{nickname}\nat node{node_id}",
                            xy=(time_s, 1.0), xycoords=("data", "axes fraction"),
                            xytext=(0, 20), textcoords="offset points",
                            fontsize=7, color="black", ha="center", va="bottom",
                            annotation_clip=False)

        # Solid binned line (behind the scatter).
        for src_ip, dst_ip in undirected[uedge]:
            dst_name = IP_NAMES[dst_ip]
            recv_events = recv_pcaps.get(dst_name, {}).get(src_ip, [])
            bin_times, bin_rates = compute_binned_series(recv_events, t_min)
            if bin_rates:
                subplot_peak = max(subplot_peak, max(bin_rates))
            color = "tab:blue" if src_ip == uedge[0] else "tab:orange"
            ax.plot(bin_times, bin_rates, color=color, alpha=0.9,
                    linestyle='-', linewidth=1.0)

        # Per-packet scatter (on top).
        for src_ip, dst_ip in undirected[uedge]:
            dst_name = IP_NAMES[dst_ip]
            src_name = IP_NAMES[src_ip]
            recv_events = recv_pcaps.get(dst_name, {}).get(src_ip, [])
            write_events = write_traces.get(src_name, {}).get(dst_ip, [])
            e = edge_meta.get(uedge, {})
            delay_str = e.get("delay", "0ms")
            link_delay_s = float(delay_str.rstrip("ms")) / 1000.0
            times, rates = compute_rate_series(recv_events, write_events,
                                               link_delay_s, t_min)
            if src_ip == uedge[0]:
                label = "left-to-right"
                color = "tab:blue"
            else:
                label = "right-to-left"
                color = "tab:orange"
            ax.plot(times, rates, color=color, alpha=scatter_alpha,
                    marker='.', markersize=2, linestyle='none',
                    label=label if times else None)

        # Payload event markers (inject + complete) near x-axis.
        marker_y = 3
        marker_dy = 3
        for side, ip in enumerate(uedge):
            nid = ip_node_id(ip)
            color = "tab:green" if side == 0 else "tab:red"
            mkr = '<' if side == 0 else '>'
            y = marker_y + side * marker_dy
            for t, _ in completions.get(nid, []):
                ax.plot(t, y, marker=mkr, markersize=4, color=color,
                        alpha=0.8, zorder=5)
            for t, _ in injections.get(nid, []):
                ax.plot(t, y, marker=mkr, markersize=4, color=color,
                        alpha=0.8, zorder=5)

        # Loss tick marks: one per dropped segment, at the sender's
        # first-send timestamp. Placed below y=0 so they don't overlap
        # the goodput scatter; color matches the directional line.
        loss_count_lr = 0
        loss_count_rl = 0
        for src_ip, dst_ip in undirected[uedge]:
            src_name = IP_NAMES[src_ip]
            dst_name = IP_NAMES[dst_ip]
            losses = loss_times(src_name, dst_name, src_ip, dst_ip)
            if not losses:
                continue
            rel = [t - t_min for t in losses]
            if src_ip == uedge[0]:
                color, y_loss = "tab:blue", -3.0
                loss_count_lr = len(losses)
            else:
                color, y_loss = "tab:orange", -7.0
                loss_count_rl = len(losses)
            ax.eventplot(rel, lineoffsets=y_loss, linelengths=3.0,
                         colors=color, alpha=0.7, linewidths=0.8)
        # Faint baseline at y=0 since ylim now extends below it.
        ax.axhline(0, color="black", linewidth=0.5, alpha=0.4)
        if loss_count_lr or loss_count_rl:
            ax.annotate("losses: %d / %d" % (loss_count_lr, loss_count_rl),
                        xy=(1.0, 0.0), xycoords="axes fraction",
                        xytext=(-3, 0.5), textcoords="offset points",
                        fontsize=7, ha="right", va="bottom", color="dimgray")

        # Title and axes.
        e = edge_meta.get(uedge, {})
        nick_a, name_a = node_parts(uedge[0])
        nick_b, name_b = node_parts(uedge[1])
        # Arrow indicates pull direction: points toward the puller.
        if e:
            left_id = ip_node_id(uedge[0])
            if left_id == e["a"]:
                a_pulls, b_pulls = e["a_pulls"], e["b_pulls"]
            else:
                a_pulls, b_pulls = e["b_pulls"], e["a_pulls"]
            if a_pulls and b_pulls:
                arrow = "<->"
            elif a_pulls:
                arrow = "<-"
            elif b_pulls:
                arrow = "->"
            else:
                arrow = "--"
        else:
            arrow = "<->"
        title = "%s %s %s %s %s" % (nick_a, name_a, arrow, name_b, nick_b)
        if e:
            ge = e.get("loss_gemodel")
            loss_str = "ge(%g%%)" % ge[0] if ge else "no loss"
            title += ", %d Mbit %s+%s %s" % (e["bw_mbit"], e["delay"], e["jitter"], loss_str)
        ax.set_title(title, fontsize=9, loc='right')
        ax.set_ylabel("Mbit/s")
        ax.set_ylim(YMIN, YMAX)
        ax.set_xlim(x_min, x_max)
        ax.grid(True, alpha=0.3)
        if idx == 0:
            leg = ax.legend(loc="upper right", fontsize=8)
            for lh in leg.legend_handles:
                lh.set_alpha(1.0)
        if subplot_peak > YMAX:
            ax.annotate("peak: %d Mbit/s" % int(subplot_peak),
                        xy=(0.0, 1.0), xycoords="axes fraction",
                        xytext=(3, -8), textcoords="offset points",
                        fontsize=9, fontweight="bold", ha="left", va="top",
                        color="red")
        if idx == len(undirected_edges) - 1:
            ax.set_xlabel("Time (seconds)")

        fig.tight_layout()
        buf = BytesIO()
        fig.savefig(buf, format='png', dpi=150, bbox_inches='tight')
        plt.close(fig)
        return buf.getvalue()

    # Render each edge at two scatter opacities.
    edge_pngs = []  # [(png_faded, png_opaque), ...]
    for idx, uedge in enumerate(undirected_edges):
        print(f"  edge {idx+1}/{len(undirected_edges)}...", file=sys.stderr)
        faded = render_subplot(idx, uedge, scatter_alpha=0.07)
        opaque = render_subplot(idx, uedge, scatter_alpha=0.6)
        edge_pngs.append((faded, opaque))

    html_path = os.path.join(RESULTS_DIR, "edge_utilization_mininet.html")
    with open(html_path, 'w') as f:
        f.write('<!DOCTYPE html><html><head><meta charset="utf-8">\n')
        f.write('<title>%s</title>\n' % suptitle)
        f.write('<style>\n')
        f.write('body{font-family:sans-serif;max-width:1400px;margin:auto}\n')
        f.write('.edge img{max-width:100%;height:auto;display:block}\n')
        f.write('.edge{margin-bottom:4px}\n')
        f.write('.edge label{font-size:12px;cursor:pointer}\n')
        f.write('.edge .opaque{display:none}\n')
        f.write('.edge input:checked ~ .opaque{display:block}\n')
        f.write('.edge input:checked ~ .faded{display:none}\n')
        f.write('</style>\n')
        f.write('</head><body>\n')
        f.write('<h2>%s</h2>\n' % suptitle)
        for i, (faded, opaque) in enumerate(edge_pngs):
            f64 = base64.b64encode(faded).decode()
            o64 = base64.b64encode(opaque).decode()
            f.write('<div class="edge">')
            f.write('<input type="checkbox" id="scatter-%d">' % i)
            f.write('<label for="scatter-%d"> scatter</label>\n' % i)
            f.write('<img class="faded" src="data:image/png;base64,%s">\n' % f64)
            f.write('<img class="opaque" src="data:image/png;base64,%s">\n' % o64)
            f.write('</div>\n')
        f.write('</body></html>\n')
    print(f"Wrote {html_path}", file=sys.stderr)


if __name__ == "__main__":
    plot()
