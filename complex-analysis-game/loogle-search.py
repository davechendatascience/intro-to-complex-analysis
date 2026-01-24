import requests
import sys
import json

def tool_search_lean(query: str):
    # Loogle is often preferred for agents due to open API
    try:
        response = requests.get("https://loogle.lean-lang.org/json", params={"q": query})
        response.raise_for_status()
        return response.json()
    except Exception as e:
        return {"error": str(e)}

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python loogle-search.py <query>")
        sys.exit(1)
    
    query = " ".join(sys.argv[1:])
    result = tool_search_lean(query)
    print(json.dumps(result, indent=2))
