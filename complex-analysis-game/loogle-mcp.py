
import sys
import json
import requests

# This is a standalone MCP server for Loogle search.
# To use it, add its path to your MCP configuration.

def loogle_search(query):
    try:
        response = requests.get("https://loogle.lean-lang.org/json", params={"q": query})
        response.raise_for_status()
        return response.json()
    except Exception as e:
        return {"error": str(e)}

def main():
    while True:
        try:
            line = sys.stdin.readline()
            if not line:
                break
            request = json.loads(line)
            
            # Simple MCP/JSON-RPC protocol handler
            method = request.get("method")
            req_id = request.get("id")
            
            if method == "initialize":
                response = {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "protocolVersion": "2024-11-05",
                        "capabilities": {
                            "tools": {
                                "listChanged": False
                            }
                        },
                        "serverInfo": {
                            "name": "Loogle-MCP",
                            "version": "1.0.0"
                        }
                    }
                }
            elif method == "notifications/initialized":
                continue # Ignore initialized notification
            elif method == "tools/list":
                response = {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "tools": [
                            {
                                "name": "loogle_search",
                                "description": "Search for Lean 4 definitions and theorems using Loogle.",
                                "inputSchema": {
                                    "type": "object",
                                    "properties": {
                                        "query": {
                                            "type": "string",
                                            "description": "The search query (e.g., 'Syntax -> String')"
                                        }
                                    },
                                    "required": ["query"]
                                }
                            }
                        ]
                    }
                }
            elif method == "tools/call":
                params = request.get("params", {})
                if params.get("name") == "loogle_search":
                    query = params.get("arguments", {}).get("query")
                    search_result = loogle_search(query)
                    response = {
                        "jsonrpc": "2.0",
                        "id": req_id,
                        "result": {
                            "content": [
                                {
                                    "type": "text",
                                    "text": json.dumps(search_result, indent=2)
                                }
                            ]
                        }
                    }
                else:
                    response = {
                        "jsonrpc": "2.0",
                        "id": req_id,
                        "error": {"code": -32601, "message": "Method not found"}
                    }
            else:
                response = {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "error": {"code": -32601, "message": "Unsupported method"}
                }
            
            sys.stdout.write(json.dumps(response) + "\n")
            sys.stdout.flush()
        except Exception as e:
            pass

if __name__ == "__main__":
    main()
