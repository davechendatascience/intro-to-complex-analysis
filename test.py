import asyncio
import sys
import shutil
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client
import os

# Configuration
SERVER_SCRIPT = "lean_linter.py"  # Name of your server file
LEAN_FILE_TO_TEST = "Game/Levels/Analysis/L01_Analytic.lean"        # Make sure this file exists!

async def main():
    # 1. Check if 'uv' is installed (since the server uses 'uv run')
    uv_path = shutil.which("uv")
    if not uv_path:
        print("Error: 'uv' not found. Please install uv first.")
        return

    # 2. Configure the server parameters
    # This simulates how Claude Desktop launches your server
    import sys
    server_params = StdioServerParameters(
        command=sys.executable,  # Use the current python interpreter
        args=[SERVER_SCRIPT], 
        env={
            "PYTHONUNBUFFERED": "1", # Force Python to flush stdout
            "PATH": os.environ["PATH"] # Inherit PATH so 'lake' is found
        } 
)

    print(f"🚀 Launching MCP Server: {SERVER_SCRIPT}...")
    
    try:
        async with stdio_client(server_params) as (read, write):
            async with ClientSession(read, write) as session:
                
                # 3. Initialize Connection
                print("⏳ Initializing connection...")
                await session.initialize()
                print("✅ Connected to Server!")

                # 4. List Tools
                print("\n📋 Listing Available Tools:")
                tools = await session.list_tools()
                for tool in tools.tools:
                    print(f"   - {tool.name}: {tool.description}")

                # 5. Test 'lint_snippet' (Live Linting)
                print("\n🧪 Testing 'lint_snippet'...")
                snippet = """
import Mathlib.Tactic.Lint
def hello := 1
#lint
"""
                result = await session.call_tool(
                    name="lint_snippet",
                    arguments={"code": snippet}
                )
                print("   Result:")
                # MCP returns a list of content blocks
                for content in result.content:
                    if content.type == "text":
                        print(f"   > {content.text}")

    except Exception as e:
        print(f"\n❌ Error: {e}")
        print("Tip: Make sure you are running this inside a valid Lean project folder with lakefile.lean!")

if __name__ == "__main__":
    asyncio.run(main())
