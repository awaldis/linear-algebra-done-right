#!/usr/bin/env python3
"""Emit a fixed sequence of Lean LSP requests for TinyProofs.lean."""

from __future__ import annotations

import json
from pathlib import Path
import sys


def main() -> None:
    repo_root = Path(__file__).resolve().parent
    file_path = repo_root / "LinearAlgebraDoneRight" / "TinyProofs.lean"
    source = file_path.read_text()

    messages = [
        {
            "jsonrpc": "2.0",
            "id": 0,
            "method": "initialize",
            "params": {
                "processId": None,
                "clientInfo": {"name": "manual-script", "version": "0.1"},
                "rootUri": f"file://{repo_root}",
                "capabilities": {},
                "trace": "off",
                "workspaceFolders": [],
            },
        },
        {"jsonrpc": "2.0", "method": "initialized", "params": {}},
        {
            "jsonrpc": "2.0",
            "method": "textDocument/didOpen",
            "params": {
                "textDocument": {
                    "uri": f"file://{file_path}",
                    "languageId": "lean",
                    "version": 1,
                    "text": source,
                }
            },
        },
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "textDocument/hover",
            "params": {
                "textDocument": {"uri": f"file://{file_path}"},
                "position": {"line": 10, "character": 10},
            },
        },
        {"jsonrpc": "2.0", "id": 2, "method": "shutdown", "params": None},
        {"jsonrpc": "2.0", "method": "exit"},
    ]

    out = sys.stdout.buffer
    for msg in messages:
        body = json.dumps(msg, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        header = f"Content-Length: {len(body)}\r\n\r\n".encode("ascii")
        out.write(header)
        out.write(body)


if __name__ == "__main__":
    main()

