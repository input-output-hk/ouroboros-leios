#!/usr/bin/env python3
r"""
Mininet topology runner.

Reads a metadata.json topology description (via topo_config.py) and
runs the P2P diffusion protocol simulation with the specified network
parameters.

Each edge (A, B) in the topology is materialised as a "middlebox" host
sitting between A and B:

  host A --- veth --- middlebox --- veth --- host B

The middlebox owns the bottleneck: its egress toward B rate-limits with
fq_codel AQM. The end hosts themselves have no shaping; delay sits on
the host side of each veth (the "propagation" leg).

Each host has identity IP 10.0.0.<node_id>/32 on lo; each veth pair has
its own /24 subnet (10.<idx>.{1,2}.0/24). Middleboxes enable IP
forwarding and host routing tables direct 10.0.0.<peer>/32 traffic via
the correct middlebox.
"""

import os
import subprocess
import sys
import time
from mininet.net import Mininet
from mininet.node import Host
from mininet.nodelib import LinuxBridge
from mininet.link import TCLink
from mininet.log import setLogLevel

from topo_config import TopoConfig

NODE_BIN = '/sim/node'


def run(h, cmd):
    """Run a shell command that shouldn't ever fail on a Mininet host, raising on nonzero exit code.

    Also abort on any stderr line that doesn't start with 'Warning:',
    because `sysctl -w` is a known offender that prints 'Operation not
    permitted' to stderr but returns 0."""
    os.environ.setdefault('SHELL', '/bin/bash')
    proc = h.popen(cmd, shell=True,
                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = proc.communicate()
    non_warning = [l for l in stderr.decode().splitlines()
                   if l.strip() and not l.lstrip().startswith('Warning:')]
    if proc.returncode != 0 or non_warning:
        raise RuntimeError(
            "command failed on %s (exit %d): %s\n  stderr: %s"
            % (h.name, proc.returncode, cmd, stderr.decode().strip()))
    return stdout.decode()

# Capture enough of each packet for IP + TCP headers including options,
# but not the payload (we only need sizes and timestamps for goodput).
PCAP_SNAPLEN = 128


def build_network(cfg):
    """Create Mininet network with per-edge middleboxes (no shared bridge)."""
    net = Mininet(controller=None)

    hosts = {}
    for i in sorted(cfg.node_ids):
        hosts[i] = net.addHost('h%d' % i, ip=None)

    middleboxes = {}     # link_idx -> middlebox host
    link_intfs = {}      # link_idx -> (a_intf, mb_a_intf, mb_b_intf, b_intf)
    for idx, edge in enumerate(cfg.edges, start=1):
        a, b = edge[0], edge[1]
        mb = net.addHost('mb%d' % idx, ip=None)
        middleboxes[idx] = mb
        la = net.addLink(hosts[a], mb)
        lb = net.addLink(mb, hosts[b])
        link_intfs[idx] = (la.intf1.name, la.intf2.name, lb.intf1.name, lb.intf2.name)

    return net, hosts, middleboxes, link_intfs


def setup_addresses(cfg, hosts, middleboxes, link_intfs):
    """Assign /24 subnets, identity IPs on lo, routes, and enable forwarding."""
    for node_id, h in hosts.items():
        run(h, 'ip addr add 10.0.0.%d/32 dev lo' % node_id)

    for idx, edge in enumerate(cfg.edges, start=1):
        a, b = edge[0], edge[1]
        ha, mb = hosts[a], middleboxes[idx]
        hb = hosts[b]
        a_intf, mb_a_intf, mb_b_intf, b_intf = link_intfs[idx]

        # A-side: 10.idx.1.0/24; B-side: 10.idx.2.0/24.
        a_addr = '10.%d.1.1' % idx
        mb_a_addr = '10.%d.1.2' % idx
        mb_b_addr = '10.%d.2.1' % idx
        b_addr = '10.%d.2.2' % idx

        run(ha, 'ip addr add %s/24 dev %s' % (a_addr, a_intf))
        run(ha, 'ip link set %s up' % a_intf)
        run(mb, 'ip addr add %s/24 dev %s' % (mb_a_addr, mb_a_intf))
        run(mb, 'ip link set %s up' % mb_a_intf)
        run(mb, 'ip addr add %s/24 dev %s' % (mb_b_addr, mb_b_intf))
        run(mb, 'ip link set %s up' % mb_b_intf)
        run(hb, 'ip addr add %s/24 dev %s' % (b_addr, b_intf))
        run(hb, 'ip link set %s up' % b_intf)

        # Host → peer routes via middlebox. `src` pins the source IP to
        # the loopback identity so the peer sees us as 10.0.0.<node_id>.
        # Per-tuned-node initcwnd/initrwnd is folded into these /32 peer
        # routes since they are the longest-prefix match the kernel
        # actually consults for peer traffic.
        a_tune = ' initcwnd 200 initrwnd 200' if a in cfg.tuned_initcwnd else ''
        b_tune = ' initcwnd 200 initrwnd 200' if b in cfg.tuned_initcwnd else ''
        run(ha, 'ip route add 10.0.0.%d/32 via %s src 10.0.0.%d%s'
            % (b, mb_a_addr, a, a_tune))
        run(hb, 'ip route add 10.0.0.%d/32 via %s src 10.0.0.%d%s'
            % (a, mb_b_addr, b, b_tune))
        # Middlebox host routes for both endpoints.
        run(mb, 'ip route add 10.0.0.%d/32 via %s' % (a, a_addr))
        run(mb, 'ip route add 10.0.0.%d/32 via %s' % (b, b_addr))
        # Forwarding on the middlebox.
        run(mb, 'sysctl -w net.ipv4.ip_forward=1')


def setup_tc(cfg, hosts, middleboxes, link_intfs):
    """Bottleneck-AQM setup:
       - On each host's per-peer veth: netem delay+loss (propagation leg).
       - On each middlebox's egress toward B: htb + fq_codel (rate-limit + AQM).
    """
    for idx, edge in enumerate(cfg.edges, start=1):
        a, b = edge[0], edge[1]
        bw, delay, jitter, loss_ge = cfg.link_params(a, b)
        a_intf, mb_a_intf, mb_b_intf, b_intf = link_intfs[idx]
        ha, mb, hb = hosts[a], middleboxes[idx], hosts[b]

        # Propagation leg on each host's outbound eth (the link-specific
        # delay sits here, not at the bottleneck).
        apply_netem(ha, a_intf, delay, jitter, loss_ge)
        apply_netem(hb, b_intf, delay, jitter, loss_ge)

        # Rate + AQM on each middlebox egress.
        apply_rate_aqm(mb, mb_b_intf, bw)
        apply_rate_aqm(mb, mb_a_intf, bw)


def clear_qdisc(host, intf):
    """Delete the root qdisc if one is present; safe to call on a fresh interface."""
    show = run(host, 'tc qdisc show dev %s root' % intf)
    if show.strip() and 'noqueue' not in show and 'pfifo_fast' not in show:
        run(host, 'tc qdisc del dev %s root' % intf)


def apply_netem(host, intf, delay, jitter, loss_ge):
    if jitter and jitter != '0ms':
        args = 'limit 10000 delay %s %s 25%% distribution paretonormal' % (delay, jitter)
    else:
        args = 'limit 10000 delay %s' % delay
    if loss_ge is not None:
        # Split loss across the two propagation legs (A→mb and mb→B);
        # each leg gets half the good→bad probability.
        p, r, h1, k1 = loss_ge
        args += ' loss gemodel %.2f%% %.2f%% %.2f%% %.2f%%' % (p / 2, r, h1, k1)
    clear_qdisc(host, intf)
    run(host, 'tc qdisc add dev %s root handle 1: netem %s' % (intf, args))


def apply_rate_aqm(host, intf, bw_mbit):
    clear_qdisc(host, intf)
    run(host, 'tc qdisc add dev %s root handle 1: htb default 10 r2q 1' % intf)
    run(host, ('tc class add dev %s parent 1: classid 1:10 htb rate %dmbit '
               'ceil %dmbit burst 32k cburst 32k') % (intf, bw_mbit, bw_mbit))
    run(host, 'tc qdisc add dev %s parent 1:10 handle 10: fq_codel' % intf)


def tune_tcp(cfg, hosts):
    """Configure each end host's TCP stack for high bandwidth-delay product links."""
    for node_id, h in sorted(hosts.items()):
        # tcp_rmem/tcp_wmem are per-netns — the auto-tune ceiling we use
        # in lieu of setsockopt(SO_RCVBUF), which would be clamped to
        # the un-writable net.core.{r,w}mem_max.
        run(h, 'sysctl -w net.ipv4.tcp_rmem="4096 1048576 16777216"')
        run(h, 'sysctl -w net.ipv4.tcp_wmem="4096 1048576 16777216"')

        # initcwnd/initrwnd for tuned nodes is set on the /32 peer routes
        # in setup_addresses, since those are what the kernel matches for
        # peer-to-peer traffic.


def run_iperf_tests(cfg, hosts, duration=10):
    """Measure TCP throughput with iperf3 across every configured edge."""
    print('\n--- iperf3 tests ---', file=sys.stderr)
    for a, b, *_ in cfg.edges:
        if a not in hosts or b not in hosts:
            continue
        ha, hb = hosts[a], hosts[b]
        bw_expected, _, _, _ = cfg.link_params(a, b)
        # Server on b, client on a. Address b on its shared /24 IP.
        srv = hb.popen('iperf3 -s -1 -p 5201',
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        time.sleep(0.3)
        cli = ha.popen('iperf3 -c 10.0.0.%d -p 5201 -t %d -f m' % (b, duration),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        out, _ = cli.communicate()
        srv.wait()
        # Extract the final "sender" and "receiver" summary lines.
        summary = [l for l in out.decode().splitlines()
                   if 'sender' in l or 'receiver' in l]
        print('[%d -> %d, %d Mbit link]' % (a, b, bw_expected), file=sys.stderr)
        for l in summary:
            print('  ' + l, file=sys.stderr)


def run_simulation(cfg, net, hosts, log_dir, duration=None):
    if duration is None:
        duration = cfg.default_duration
    os.makedirs(log_dir, exist_ok=True)

    inputfile_path = os.path.join(log_dir, "input.json")

    # Start tcpdump on each host before launching nodes. Use -i any so
    # we capture across all per-peer veths without hardcoding names.
    for node_id, h in sorted(hosts.items()):
        pcap = '%s/node%d.pcap' % (log_dir, node_id)
        h.cmd('tcpdump -i any -w %s -s %d tcp &' % (pcap, PCAP_SNAPLEN))

    # Compute a shared epoch: schedule time 0 for all nodes.
    # Allow enough time for spawning (0.2s stagger per node) plus handshakes.
    num_nodes = len(hosts)
    epoch = time.time() + num_nodes * 0.2 + 1.0

    # Write epoch for plot alignment.
    with open(os.path.join(log_dir, 't0.txt'), 'w') as f:
        f.write('%.6f\n' % epoch)

    # Start nodes in reverse order so listeners are up before connectors.
    for node_id in sorted(hosts.keys(), reverse=True):
        h = hosts[node_id]
        cmd = '%s --id %d --inputfile %s --epoch %.6f' % (
            NODE_BIN, node_id, inputfile_path, epoch)

        log_stderr = '%s/node%d.stderr' % (log_dir, node_id)
        log_stdout = '%s/node%d.stdout' % (log_dir, node_id)

        h.cmd('%s > %s 2> %s &' % (cmd, log_stdout, log_stderr))
        print('Started node %d: %s' % (node_id, cmd))
        # Small stagger so listeners are ready before connectors reach them.
        time.sleep(0.2)

    if duration == 0:
        print('\nDuration 0: metadata written, skipping simulation.')
        return

    # Sample TCP_INFO every 200 ms for post-mortem inspection.
    for node_id, h in sorted(hosts.items()):
        log_path = '%s/node%d.ss' % (log_dir, node_id)
        h.cmd("(while :; do date +%%s.%%N; ss -tinem; sleep 0.2; done) > %s &" % log_path)

    print('\nWaiting %d seconds for simulation...' % duration)
    time.sleep(duration)

    for _, h in sorted(hosts.items()):
        h.cmd('pkill -f "ss -tinem" 2>/dev/null; true')

    # Stop tcpdump.
    for node_id, h in sorted(hosts.items()):
        h.cmd('kill %tcpdump')
    time.sleep(1)

    # Collect logs.
    print('\n--- Results ---')
    for node_id in sorted(hosts.keys()):
        log_path = '%s/node%d.stderr' % (log_dir, node_id)
        print('\n[node %d]' % node_id)
        print(hosts[node_id].cmd('cat %s' % log_path))


if __name__ == '__main__':
    import argparse
    import shutil
    parser = argparse.ArgumentParser()
    parser.add_argument('--duration', type=int, default=None,
                        help='seconds to run (default: from input.json; 0 = skip)')
    parser.add_argument('--results', default='/sim/mininet-results',
                        help='directory for output files')
    parser.add_argument('--iperf', action='store_true',
                        help='run iperf3 over each edge (in lieu of simulation)')
    args = parser.parse_args()

    # Read input.json from stdin, save to results directory.
    os.makedirs(args.results, exist_ok=True)
    inputfile_path = os.path.join(args.results, 'input.json')
    with open(inputfile_path, 'w') as f:
        shutil.copyfileobj(sys.stdin, f)

    cfg = TopoConfig(inputfile_path)

    setLogLevel('info')

    net, hosts, middleboxes, link_intfs = build_network(cfg)
    net.start()

    setup_addresses(cfg, hosts, middleboxes, link_intfs)
    setup_tc(cfg, hosts, middleboxes, link_intfs)
    tune_tcp(cfg, hosts)

    # Verify connectivity along every configured edge.
    print('\n--- Connectivity check ---')
    for edge in cfg.edges:
        a, b = edge[0], edge[1]
        out = hosts[a].cmd('ping -c1 -W1 10.0.0.%d >/dev/null 2>&1; echo $?' % b).strip()
        if out != '0':
            print('  h%d -> h%d: UNREACHABLE' % (a, b))

    if args.iperf:
        run_iperf_tests(cfg, hosts)
    else:
        run_simulation(cfg, net, hosts, args.results, duration=args.duration)
    net.stop()
