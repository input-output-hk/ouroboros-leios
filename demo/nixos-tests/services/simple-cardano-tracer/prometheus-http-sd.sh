read -r REQUEST_LINE

if [[ "$REQUEST_LINE" =~ ^GET ]]; then
    INPUT_NODES=$(curl -H "Accept: application/json" "http://$CARDANO_TRACER_PROMETHEUS")

    PROMETHEUS_JSON=$(echo "$INPUT_NODES" | jq --arg ENDPOINT "$CARDANO_TRACER_PROMETHEUS" '
    to_entries
    | map({
        targets: [ $ENDPOINT ],
        labels: {
            "__metrics_path__": .value,
            "alias": .key,
            "type": "cardano-node"
        }
    })
   ')

    echo -e "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: ${#PROMETHEUS_JSON}\r\nConnection: close\r\n\r\n${PROMETHEUS_JSON}"
else
    echo -e "HTTP/1.1 405 Method Not Allowed\r\n\r\n"
fi
