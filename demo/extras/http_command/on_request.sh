read -r REQUEST_LINE

if [[ "$REQUEST_LINE" =~ ^GET ]]; then
  OUTPUT=$($COMMAND)

  echo -n -e "HTTP/1.1 200 OK\r\nContent-Length: ${#OUTPUT}\r\nConnection: keep-alive\r\n\r\n${OUTPUT}"
else
  echo -n -e "HTTP/1.1 405 Method Not Allowed\r\n\r\n"
fi
