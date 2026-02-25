#!/bin/bash
# Helper script to send LSP requests to Lean server with proper headers

send_lsp() {
  local json="$1"
  local length=$(echo -n "$json" | wc -c)
  printf "Content-Length: %d\r\n\r\n%s" "$length" "$json"
}

# Read each line from server-script.jsonl and send with headers
while IFS= read -r line; do
  if [ -n "$line" ]; then
    send_lsp "$line"
  fi
done < server-script.jsonl | lake env lean --server | jq -R 'fromjson? // .'
