# Translate `ss -n -i -m -t -p <filter>` output into Prometheus metrics format
#
# Usage:
# ss_prom <filter>
#
# References
# 1. https://blog.mygraphql.com/en/notes/low-tec/network/tcp-inspect/
# 2. https://man7.org/linux/man-pages/man8/ss.8.html
# 3. https://prometheus.io/docs/concepts/metric_types/

SS_METRIC_PREFIX="ss_tcp"

# Function to split IP and Port from an address string (handles IPv4 and IPv6)
# Arguments: $1=address_port_string, $2=variable_name_for_ip, $3=variable_name_for_port
split_addr_port() {
  local addr_port_str="$1"
  local ip_var="$2"
  local port_var="$3"

  # Check for IPv6 format: [address]:port
  if [[ "$addr_port_str" =~ ^\[(.+)\]:([0-9A-Za-z]+)$ ]]; then
    # Capture groups for IPv6: BASH_REMATCH[1] is IP, BASH_REMATCH[2] is Port
    eval "$ip_var"="${BASH_REMATCH[1]}"
    eval "$port_var"="${BASH_REMATCH[2]}"
  elif [[ "$addr_port_str" =~ ^([0-9a-fA-F\.\:]+):([0-9A-Za-z]+)$ ]]; then
    # Capture groups for IPv4 or non-bracketed IPv6: BASH_REMATCH[1] is IP, BASH_REMATCH[2] is Port
    eval "$ip_var"="${BASH_REMATCH[1]}"
    eval "$port_var"="${BASH_REMATCH[2]}"
  else
    # Handle cases where the port is named (e.g., :https)
    IFS=':' read -r ip_val port_val <<<"$addr_port_str"
    eval "$ip_var"="$ip_val"
    eval "$port_var"="$port_val"
  fi
}

# Process input line by line
function ss_to_prometheus() {
  # Variables to store the labels of the current connection block
  local CURRENT_LABELS=""
  local CURRENT_SRC_IP=""
  local CURRENT_SRC_PORT=""
  local CURRENT_DST_IP=""
  local CURRENT_DST_PORT=""

  while IFS= read -r line; do
    # Skip header lines
    if [[ "$line" =~ ^State\ Recv-Q ]]; then
      continue
    fi

    # ESTAB 0 0 [2001:1620:713d:1300:6b8b:54dd:34fd:9bf9]:53608 [2a00:1450:400a:1001::65]:443 users:(("firefox",pid=3642,fd=208))
    if [[ "$line" =~ ^(ESTAB|LISTEN|CLOSE|SYN-SENT|TIME-WAIT) ]]; then
      # Reset metric extraction status
      CURRENT_LABELS=""

      # Split the line into an array to access address fields. We need to preserve spaces for now.
      # Temporarily use awk to isolate the fifth and sixth columns (Local:Port and Peer:Port)
      # because Bash field splitting is unreliable due to variable white space.
      line_="$(echo "$line" | tr -s ' ')"
      tcp_state="$(echo "$line_" | cut -d " " -f 1)"
      recv_q="$(echo "$line_" | cut -d " " -f 2)"
      send_q="$(echo "$line_" | cut -d " " -f 3)"
      local_addr_port="$(echo "$line_" | cut -d " " -f 4)"
      peer_addr_port="$(echo "$line_" | cut -d " " -f 5)"
      users="$(echo "$line_" | cut -d " " -f 6)"

      # Extract IPs and Ports
      split_addr_port "$local_addr_port" "CURRENT_SRC_IP" "CURRENT_SRC_PORT"
      split_addr_port "$peer_addr_port" "CURRENT_DST_IP" "CURRENT_DST_PORT"

      # Extract the program name and pid of the process
      # users:(("firefox",pid=3642,fd=208))
      if [[ "$users" =~ users:\(\(\"([^\"]+)\",pid=([0-9]+) ]]; then
        program="${BASH_REMATCH[1]}"
        pid="${BASH_REMATCH[2]}"
        CURRENT_LABELS="program=\"$program\",pid=\"$pid\","
      fi

      # Construct the Prometheus label string
      CURRENT_LABELS="${CURRENT_LABELS}src_ip=\"$CURRENT_SRC_IP\",src_port=\"$CURRENT_SRC_PORT\",dst_ip=\"$CURRENT_DST_IP\",dst_port=\"$CURRENT_DST_PORT\",tcp_state=\"$tcp_state\""

    # --- 2. Metric Line Check ---
    # If labels are set and the line contains metric keywords (is indented)
    elif [[ -n "$CURRENT_LABELS" ]] && [[ "$line" =~ skmem|rto|rtt|cwnd ]]; then

      # echo "# TYPE ${SS_METRIC_PREFIX}_recv_q gauge"
      echo "${SS_METRIC_PREFIX}_recv_q{$CURRENT_LABELS} $recv_q"
      # echo "# TYPE ${SS_METRIC_PREFIX}_send_q gauge"
      echo "${SS_METRIC_PREFIX}_send_q{$CURRENT_LABELS} $send_q"

      # --- Metric Extraction using Bash Regex ---

      # Regex captures: 1=AVG, 2=DEV
      # rtt:23.037/17.652
      if [[ "$line" =~ rtt:([0-9]+\.[0-9]+)/([0-9]+\.[0-9]+) ]]; then
        rtt_avg="${BASH_REMATCH[1]}"
        rtt_dev="${BASH_REMATCH[2]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rtt_avg_ms gauge"
        echo "${SS_METRIC_PREFIX}_rtt_avg_ms{$CURRENT_LABELS} $rtt_avg"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rtt_dev_ms gauge"
        echo "${SS_METRIC_PREFIX}_rtt_dev_ms{$CURRENT_LABELS} $rtt_dev"
      fi

      # skmem:(r0,rb131072,t0,tb46080,f0,w0,o0,bl0,d0)
      # Extract Receive Buffer (rbY from skmem:(rX,rbY,tZ,tbW))
      if [[ "$line" =~ skmem:\(r([0-9+]),rb([0-9]+),t([0-9]+),tb([0-9]+),f([0-9]+),w([0-9]+),o([0-9]+),bl([0-9]+),d([0-9]+) ]]; then
        rmem_alloc="${BASH_REMATCH[1]}"
        rcv_buf="${BASH_REMATCH[2]}"
        wmem_alloc="${BASH_REMATCH[3]}"
        snd_buf="${BASH_REMATCH[4]}"
        fwd_alloc="${BASH_REMATCH[5]}"
        wmem_queued="${BASH_REMATCH[6]}"
        opt_mem="${BASH_REMATCH[7]}"
        back_log="${BASH_REMATCH[8]}"
        sock_drop="${BASH_REMATCH[9]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rmem_alloc gauge"
        echo "${SS_METRIC_PREFIX}_rmem_alloc{$CURRENT_LABELS} $rmem_alloc"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rcv_buf gauge"
        echo "${SS_METRIC_PREFIX}_rcv_buf{$CURRENT_LABELS} $rcv_buf"
        # echo "# TYPE ${SS_METRIC_PREFIX}_wmem_alloc gauge"
        echo "${SS_METRIC_PREFIX}_wmem_alloc{$CURRENT_LABELS} $wmem_alloc"
        # echo "# TYPE ${SS_METRIC_PREFIX}_snd_buf gauge"
        echo "${SS_METRIC_PREFIX}_snd_buf{$CURRENT_LABELS} $snd_buf"
        # echo "# TYPE ${SS_METRIC_PREFIX}_fwd_alloc gauge"
        echo "${SS_METRIC_PREFIX}_fwd_alloc{$CURRENT_LABELS} $fwd_alloc"
        # echo "# TYPE ${SS_METRIC_PREFIX}_wmem_queued gauge"
        echo "${SS_METRIC_PREFIX}_wmem_queued{$CURRENT_LABELS} $wmem_queued"
        # echo "# TYPE ${SS_METRIC_PREFIX}_opt_mem gauge"
        echo "${SS_METRIC_PREFIX}_opt_mem{$CURRENT_LABELS} $opt_mem"
        # echo "# TYPE ${SS_METRIC_PREFIX}_back_log gauge"
        echo "${SS_METRIC_PREFIX}_back_log{$CURRENT_LABELS} $back_log"
        # echo "# TYPE ${SS_METRIC_PREFIX}_sock_drop gauge"
        echo "${SS_METRIC_PREFIX}_sock_drop{$CURRENT_LABELS} $sock_drop"
      fi

      # bytes_sent:33496
      if [[ "$line" =~ bytes_sent:([0-9]+) ]]; then
        bytes_sent="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_bytes_sent counter"
        echo "${SS_METRIC_PREFIX}_bytes_sent{$CURRENT_LABELS} $bytes_sent"
      fi

      # bytes_acked:33497
      if [[ "$line" =~ bytes_acked:([0-9]+) ]]; then
        bytes_acked="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_bytes_acked counter"
        echo "${SS_METRIC_PREFIX}_bytes_acked{$CURRENT_LABELS} $bytes_acked"
      fi

      # bytes_received:52142
      if [[ "$line" =~ bytes_received:([0-9]+) ]]; then
        bytes_received="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_bytes_received counter"
        echo "${SS_METRIC_PREFIX}_bytes_received{$CURRENT_LABELS} $bytes_received"
      fi

      # segs_out:852
      if [[ "$line" =~ segs_out:([0-9]+) ]]; then
        segs_out="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_segs_out counter"
        echo "${SS_METRIC_PREFIX}_segs_out{$CURRENT_LABELS} $segs_out"
      fi

      # segs_in:681
      if [[ "$line" =~ segs_in:([0-9]+) ]]; then
        segs_in="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_segs_in counter"
        echo "${SS_METRIC_PREFIX}_segs_in{$CURRENT_LABELS} $segs_in"
      fi

      # data_segs_out:491
      if [[ "$line" =~ data_segs_out:([0-9]+) ]]; then
        data_segs_out="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_data_segs_out counter"
        echo "${SS_METRIC_PREFIX}_data_segs_out{$CURRENT_LABELS} $data_segs_out"
      fi

      # data_segs_in:360
      if [[ "$line" =~ data_segs_in:([0-9]+) ]]; then
        data_segs_in="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_data_segs_in counter"
        echo "${SS_METRIC_PREFIX}_data_segs_in{$CURRENT_LABELS} $data_segs_in"
      fi

      # lastsnd:242
      if [[ "$line" =~ lastsnd:([0-9]+) ]]; then
        lastsnd="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_lastsnd_ms gauge"
        echo "${SS_METRIC_PREFIX}_lastsnd_ms{$CURRENT_LABELS} $lastsnd"
      fi

      # lastrcv:230
      if [[ "$line" =~ lastrcv:([0-9]+) ]]; then
        lastrcv="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_lastrcv_ms gauge"
        echo "${SS_METRIC_PREFIX}_lastrcv_ms{$CURRENT_LABELS} $lastrcv"
      fi

      # lastack:230
      if [[ "$line" =~ lastack:([0-9]+) ]]; then
        lastack="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_lastack_ms gauge"
        echo "${SS_METRIC_PREFIX}_lastack_ms{$CURRENT_LABELS} $lastack"
      fi

      # ato:40
      if [[ "$line" =~ ato:([0-9]+) ]]; then
        ato="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_ato_ms gauge"
        echo "${SS_METRIC_PREFIX}_ato_ms{$CURRENT_LABELS} $ato"
      fi

      # mss:1288
      if [[ "$line" =~ mss:([0-9]+) ]]; then
        mss="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_mss gauge"
        echo "${SS_METRIC_PREFIX}_mss{$CURRENT_LABELS} $mss"
      fi

      # pmtu:1500
      if [[ "$line" =~ pmtu:([0-9]+) ]]; then
        pmtu="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_pmtu gauge"
        echo "${SS_METRIC_PREFIX}_pmtu{$CURRENT_LABELS} $pmtu"
      fi

      # rcvmss:1288
      if [[ "$line" =~ rcvmss:([0-9]+) ]]; then
        rcvmss="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rcvmss gauge"
        echo "${SS_METRIC_PREFIX}_rcvmss{$CURRENT_LABELS} $rcvmss"
      fi

      # advmss:1448
      if [[ "$line" =~ advmss:([0-9]+) ]]; then
        advmss="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_advmss gauge"
        echo "${SS_METRIC_PREFIX}_advmss{$CURRENT_LABELS} $advmss"
      fi

      # cwnd:10
      if [[ "$line" =~ cwnd:([0-9]+) ]]; then
        cwnd="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_cwnd gauge"
        echo "${SS_METRIC_PREFIX}_cwnd{$CURRENT_LABELS} $cwnd"
      fi

      # rto:224
      if [[ "$line" =~ rto:([0-9]+) ]]; then
        rto="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rto_ms gauge"
        echo "${SS_METRIC_PREFIX}_rto_ms{$CURRENT_LABELS} $rto"
      fi

      # delivered:383
      if [[ "$line" =~ delivered:([0-9]+) ]]; then
        delivered="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_delivered gauge"
        echo "${SS_METRIC_PREFIX}_delivered{$CURRENT_LABELS} $delivered"
      fi

      # busy:9998ms
      if [[ "$line" =~ busy:([0-9]+)ms ]]; then
        busy="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_busy_ms gauge"
        echo "${SS_METRIC_PREFIX}_busy_ms{$CURRENT_LABELS} $busy"
      fi

      # rcv_space:14480
      if [[ "$line" =~ rcv_space:([0-9]+) ]]; then
        rcv_space="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rcv_space gauge"
        echo "${SS_METRIC_PREFIX}_rcv_space{$CURRENT_LABELS} $rcv_space"
      fi

      # rcv_ssthresh:86953
      if [[ "$line" =~ rcv_ssthresh:([0-9]+) ]]; then
        rcv_ssthresh="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rcv_ssthresh gauge"
        echo "${SS_METRIC_PREFIX}_rcv_ssthresh{$CURRENT_LABELS} $rcv_ssthresh"
      fi

      # minrtt:9.682
      if [[ "$line" =~ minrtt:([0-9]+.[0-9]+) ]]; then
        minrtt="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rcv_minrtt gauge"
        echo "${SS_METRIC_PREFIX}_minrtt{$CURRENT_LABELS} $minrtt"
      fi

      # snd_wnd:40960
      if [[ "$line" =~ snd_wnd:([0-9]+) ]]; then
        snd_wnd="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_snd_wnd gauge"
        echo "${SS_METRIC_PREFIX}_snd_wnd{$CURRENT_LABELS} $snd_wnd"
      fi

      # rcv_wnd:87040
      if [[ "$line" =~ rcv_wnd:([0-9]+) ]]; then
        rcv_wnd="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_rcv_wnd gauge"
        echo "${SS_METRIC_PREFIX}_rcv_wnd{$CURRENT_LABELS} $rcv_wnd"
      fi

      # notsent:49232
      if [[ "$line" =~ notsent:([0-9]+) ]]; then
        notsent="${BASH_REMATCH[1]}"
        # echo "# TYPE ${SS_METRIC_PREFIX}_notsent gauge"
        echo "${SS_METRIC_PREFIX}_notsent{$CURRENT_LABELS} $notsent"
      fi

      # Clear the labels for the next connection block
      CURRENT_LABELS=""
    fi
  done
}

# https://stackoverflow.com/questions/2683279/how-to-detect-if-a-script-is-being-sourced
(return 0 2>/dev/null) && sourced=1 || sourced=0

if [[ $sourced == 0 ]]; then
  ss -n -i -m -t -p "$@" | ss_to_prometheus
fi
