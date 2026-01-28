# /// script
# dependencies = [
#   "mcp[cli]"
# ]
# ///

import asyncio
import os
import json
import subprocess
import sys
import shutil
from typing import Optional, Dict, Any

from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import Tool, TextContent, EmbeddedResource, ImageContent

# Hardcode path if shutil.which fails
LAKE_PATH = shutil.which("lake") or "lake"

class LeanREPLManager:
    def __init__(self):
        self.project_root: Optional[str] = None

    def find_project_root(self, start_path: str) -> str:
        """Finds the nearest lakefile.lean going up the directory tree."""
        current = os.path.abspath(start_path)
        while True:
            if os.path.exists(os.path.join(current, "lakefile.lean")):
                return current
            parent = os.path.dirname(current)
            if parent == current:
                return start_path 
            current = parent

    def ensure_started(self, work_dir: str):
        """Locates the project root. No persistent process needed."""
        self.project_root = self.find_project_root(work_dir)

    def _run_oneshot_repl(self, cmd_payload: Dict[str, Any]) -> str:
        """
        Runs 'lake exe repl' as a fresh process for a single command.
        This guarantees EOF is sent and prevents Windows pipe hanging.
        """
        if not self.project_root:
            return "❌ Project root not found. Run ensure_started first."

        json_input = json.dumps(cmd_payload) + "\n"
        sys.stderr.write(f"[Debug] Running REPL in {self.project_root}...\n")

        try:
            # mimic: echo '{"cmd": "..."}' | lake exe repl
            result = subprocess.run(
                [LAKE_PATH, "exe", "repl"],
                input=json_input,
                cwd=self.project_root,
                capture_output=True,
                text=True,
                check=False, # We handle errors manually
                timeout=120, # Allow 2 mins for import Mathlib + linting
                encoding='utf-8'
            )

            # Check for non-zero exit that isn't just a lint failure
            if result.returncode != 0:
                # Sometimes repl exits with 1 but still prints JSON. Check stdout first.
                pass 

            stdout = result.stdout
            
            # Try to find valid JSON in the output (handling potential pretty-printing or noise)
            try:
                # First, try strict line-by-line (common case for tools)
                for line in stdout.splitlines():
                    if line.strip().startswith("{") and "messages" in line:
                         return self._format_response(json.loads(line))
            except:
                pass

            # Fallback: Try to parse the entire stdout (if pretty-printed)
            try:
                # Find the first brace
                start = stdout.find("{")
                if start != -1:
                    potential_json = stdout[start:]
                    return self._format_response(json.loads(potential_json))
            except:
                pass
            
            # If we fall through, look for general errors
            if result.stderr:
                return f"❌ REPL Error (stderr):\n{result.stderr}\n\nStdout:\n{stdout}"
            return f"❌ No valid JSON response found. Raw output:\n{stdout}..."

        except subprocess.TimeoutExpired:
            return "❌ Timeout: REPL took longer than 120s."
        except Exception as e:
            return f"❌ Unexpected Error: {e}"

    def lint_snippet(self, code: str) -> str:
        # We don't need a section wrapper because run_oneshot_repl spawns a fresh process.
        # Ensure Mathlib is imported (valid to have multiple imports at top).
        payload = f"import Mathlib\n{code}\n\n#lint"
        return self._run_oneshot_repl({"cmd": payload})

    def lint_file(self, file_path: str) -> str:
        if not self.project_root:
            return "❌ Project root unknown."

        # 1. Calculate module name from file path
        # e.g., C:\Proj\Mathlib\Algebra.lean -> Mathlib.Algebra
        try:
            rel_path = os.path.relpath(file_path, self.project_root)
        except ValueError:
            return f"❌ File {file_path} is not inside project root {self.project_root}"

        module_name = rel_path.replace(".lean", "").replace(os.sep, ".")
        
        # 2. Build it first (crucial for valid linting)
        sys.stderr.write(f"[Debug] Building {module_name}...\n")
        try:
            build_res = subprocess.run(
                [LAKE_PATH, "build", module_name],
                cwd=self.project_root,
                capture_output=True,
                text=True,
                check=True
            )
        except subprocess.CalledProcessError as e:
            return f"❌ Build Failed:\n{e.stderr}"

        # 3. Lint via import
        cmd = f"import {module_name}\n#lint"
        return self._run_oneshot_repl({"cmd": cmd})

    def _format_response(self, resp: Dict[str, Any]) -> str:
        messages = resp.get("messages", [])
        output = []
        
        # Filter out informational "linting..." messages if desired
        for msg in messages:
            sev = msg.get("severity", "info").upper()
            line = msg.get("pos", {}).get("line", "?")
            text = msg.get("data", "")
            
            # Formatting: [ERROR] Line 10: message
            output.append(f"[{sev}] Line {line}: {text}")
            
        if not output: 
            return "✅ No lint errors found."
        
        return "\n".join(output)

# --- Server Setup ---

repl_manager = LeanREPLManager()
app = Server("lean-linter")

@app.call_tool()
async def call_tool(name: str, arguments: dict) -> list[TextContent | ImageContent | EmbeddedResource]:
    cwd = os.path.dirname(os.path.abspath(__file__))
    
    # Try to infer project root from arguments if possible
    if arguments.get("file_path"):
        cwd = os.path.dirname(arguments.get("file_path"))
    
    try:
        repl_manager.ensure_started(cwd)
    except Exception as e:
        return [TextContent(type="text", text=f"Setup Error: {e}")]

    if name == "lint_snippet":
        code = arguments.get("code", "")
        result = repl_manager.lint_snippet(code)
        return [TextContent(type="text", text=result)]
    
    elif name == "lint_file":
        file_path = arguments.get("file_path")
        if not file_path:
            return [TextContent(type="text", text="Missing file_path argument")]
        result = repl_manager.lint_file(file_path)
        return [TextContent(type="text", text=result)]

    raise ValueError(f"Unknown tool {name}")

@app.list_tools()
async def list_tools() -> list[Tool]:
    return [
        Tool(
            name="lint_snippet",
            description="Lints a Lean code snippet. Handles imports automatically.",
            inputSchema={"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]}
        ),
        Tool(
            name="lint_file",
            description="Builds and lints a specific Lean file on disk.",
            inputSchema={"type": "object", "properties": {"file_path": {"type": "string"}}, "required": ["file_path"]}
        )
    ]

async def main():
    try:
        async with stdio_server() as (read, write):
            await app.run(read, write, app.create_initialization_options())
    except Exception as e:
        sys.stderr.write(f"[Server Crash] {e}\n")

if __name__ == "__main__":
    asyncio.run(main())
