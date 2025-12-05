# X-RAY - socket stats with Grafana

Position your terminal into the current direcotry and enter the shell with

```shell
nix develop .#dev-x-ray
```

Or if you use Direnv with Nix

```shell
direnv allow
```

You can either work with this setup step by step, or use the
awesome [process-compose](https://f1bonacc1.github.io/process-compose/)

## Step by step
Let's make some sockets to monitor

```shell
nc -k -l 127.0.0.1 1337 &
echo hello | nc -p 1336 127.0.0.1 1337 &
```

Start the SS HTTP exporter that collects statistics about 1337 sockets

```shell
ss_http_exporter 127.0.0.1 9100 "dport = 1337" &
```

Check that it works

```shell
$ curl 127.0.0.1:9100
# TYPE ss_socket_recv_q gauge
ss_socket_recv_q{src_ip="127.0.0.1",src_port="ischat",dst_ip="127.0.0.1",dst_port="menandmice-dns",tcp_state="ESTAB"} 0
# TYPE ss_socket_send_q gauge
ss_socket_send_q{src_ip="127.0.0.1",src_port="ischat",dst_ip="127.0.0.1",dst_port="menandmice-dns",tcp_state="ESTAB"} 0
...
```

Start Prometheus so we can send metrics to it

```shell
prometheus --web.listen-address="0.0.0.0:9090" --web.enable-remote-write-receiver
```

Run Alloy configure to scrape the SS HTTP Exporter

```shell
alloy run alloy
```

Finally run Grafana

```shell
grafana server --config grafana.ini --homepath grafana
```

[Open Grafana in the browser](http://localhost:3001)

![Grafana screenshot](grafana-screenshot.png "Grafana screenshot")

Clean up

```shell
pkill "socat|grafana|prometheus|alloy"
```

## process-compose

Run the setup

```shell
process-compose -f process-compose.yaml
```

You should see

![process-compose](process-compose-screenshot.png "process-compose screenshot")

[Open Grafana in the browser](http://localhost:3001)
