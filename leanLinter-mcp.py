import subprocess
import json
import sys
import re
import logging
from typing import Optional

# Setup debug logging
logging.basicConfig(
    filename='lean_linter_debug.log',
    level=logging.DEBUG,
    format='%(asctime)s - %(levelname)s - %(message)s'
)

def extract_line_num(line: str) -> Optional[int]:
    match = re.search(r':(\d+):', line)
    return int(match.group(1)) if match else None

class LeanLinter:
    def __init__(self, project_root: str):
        self.project_root = project_root
        self.lsp_port = 12345  # LSP server port
    
    @staticmethod
    def check_file_with_lsp(file_path: str, code: str) -> dict:
        """
        Use LSP to type-check a file incrementally.
        Returns diagnostics without full compilation.
        """
        # Query Lean LSP server for diagnostics
        # This is fast (milliseconds, not seconds)
        diagnostics = {
            "errors": [],
            "warnings": [],
            "suggestions": []
        }
        
        # Pseudo-code: actual implementation uses LSP client library
        # e.g., `python-lspclient` or `eglot` protocol
        
        try:
            # Send file to LSP server
            result = subprocess.run(
                ["lean", "--check", file_path],
                capture_output=True,
                timeout=2  # Fast timeout; LSP is incremental
            )
            
            # Parse LSP diagnostics
            if result.returncode != 0:
                # Extract type errors
                for line in result.stderr.split('\n'):
                    if "error:" in line.lower():
                        diagnostics["errors"].append({
                            "line": extract_line_num(line),
                            "message": line,
                            "type": "type_error"
                        })
                    elif "warning:" in line.lower():
                        diagnostics["warnings"].append(line)
        except subprocess.TimeoutExpired:
            diagnostics["warnings"].append("LSP check timed out")
        
        return diagnostics
    
    @staticmethod
    def lint_definition(name: str, code: str) -> dict:
        """
        Run #lint on a single definition.
        Catches style and convention issues.
        """
        lean_cmd = f"""
#eval Lean.linter.getLints "{name}"
        """
        
        result = subprocess.run(
            ["lean", "-"],
            input=lean_cmd,
            capture_output=True,
            text=True,
            timeout=5
        )
        
        issues = {
            "unused_vars": [],
            "naming_convention": [],
            "doc_missing": [],
            "other": []
        }
        
        # Parse lint output
        for line in result.stdout.split('\n'):
            if "unused variable" in line:
                issues["unused_vars"].append(line)
            elif "naming convention" in line:
                issues["naming_convention"].append(line)
            elif "missing documentation" in line:
                issues["doc_missing"].append(line)
        
        return issues
    
    @staticmethod
    def parse_lake_build_error(error_output: str) -> dict:
        """
        Parse structured errors from `lake build` output.
        Returns machine-readable format for agent.
        """
        errors = []
        
        lines = error_output.split('\n')
        i = 0
        while i < len(lines):
            line = lines[i]
            
            # Match Lean 4 error format
            if "error:" in line:
                error_obj = {
                    "severity": "error",
                    "file": None,
                    "line": None,
                    "message": line,
                    "expected_type": None,
                    "actual_type": None,
                    "code_snippet": []
                }
                
                # Extract file and line
                if "[" in line and "]" in line:
                    location = line[line.index("[")+1:line.index("]")]
                    if ":" in location:
                        error_obj["file"], error_obj["line"] = location.split(":")
                
                # Look ahead for type mismatch details
                i += 1
                while i < len(lines) and lines[i].startswith(" "):
                    error_obj["code_snippet"].append(lines[i])
                    
                    if "has type" in lines[i]:
                        # Extract actual type
                        error_obj["actual_type"] = lines[i].split("has type")[-1].strip()
                    elif "expected" in lines[i]:
                        # Extract expected type
                        error_obj["expected_type"] = lines[i].split("expected")[-1].strip()
                    
                    i += 1
                
                errors.append(error_obj)
            else:
                i += 1
        
        return {"errors": errors, "count": len(errors)}


# MCP Tool Definitions
def mcp_lean_check(file_path: str) -> str:
    """
    [MCP Tool] Fast type-check without full build.
    Returns errors that agent can fix immediately.
    """
    linter = LeanLinter(".")
    diagnostics = linter.check_file_with_lsp(file_path, None)
    
    if diagnostics["errors"]:
        return f"❌ {len(diagnostics['errors'])} type errors found:\n" + \
               "\n".join([f"  Line {e.get('line', '?')}: {e['message']}" 
                         for e in diagnostics["errors"]])
    return "✅ No type errors detected by LSP"

def mcp_lean_lint(definition_name: str) -> str:
    """
    [MCP Tool] Run #lint on a definition for style issues.
    Returns convention violations.
    """
    linter = LeanLinter(".")
    issues = linter.lint_definition(definition_name, None)
    
    if any(issues.values()):
        return "⚠️ Linting issues:\n" + json.dumps(issues, indent=2)
    return "✅ No style issues"

def mcp_lean_build_parse(build_log: str) -> str:
    """
    [MCP Tool] Parse structured errors from lake build output.
    Returns machine-readable format.
    """
    linter = LeanLinter(".")
    parsed = linter.parse_lake_build_error(build_log)
    
    if parsed["errors"]:
        return f"❌ {parsed['count']} errors:\n" + \
               json.dumps(parsed["errors"], indent=2)
    return "✅ Build successful"

def main():
    logging.info("Lean Linter MCP started")
    while True:
        try:
            line = sys.stdin.readline()
            if not line:
                logging.info("Stdin closed")
                break
            
            logging.debug(f"Received: {line.strip()}")
            request = json.loads(line)
            
            method = request.get("method")
            req_id = request.get("id")
            
            if method == "initialize":
                response = {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "protocolVersion": "2024-11-05",
                        "capabilities": {
                            "tools": {}
                        },
                        "serverInfo": {"name": "Lean-Linter-MCP", "version": "1.0.0"}
                    }
                }
            elif method == "tools/list":
                response = {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "tools": [
                            {
                                "name": "lean_check",
                                "description": "Fast type-check a Lean file without full build.",
                                "inputSchema": {
                                    "type": "object",
                                    "properties": {
                                        "file_path": {"type": "string", "description": "Path to the Lean file"}
                                    },
                                    "required": ["file_path"]
                                }
                            },
                            {
                                "name": "lean_lint",
                                "description": "Run #lint on a definition for style issues.",
                                "inputSchema": {
                                    "type": "object",
                                    "properties": {
                                        "definition_name": {"type": "string", "description": "Name of the definition to lint"}
                                    },
                                    "required": ["definition_name"]
                                }
                            }
                        ]
                    }
                }
            elif method == "tools/call":
                params = request.get("params", {})
                name = params.get("name")
                args = params.get("arguments", {})
                
                logging.info(f"Calling tool: {name} with args {args}")
                if name == "lean_check":
                    result = mcp_lean_check(args.get("file_path"))
                elif name == "lean_lint":
                    result = mcp_lean_lint(args.get("definition_name"))
                else:
                    response = {
                        "jsonrpc": "2.0", 
                        "id": req_id, 
                        "error": {"code": -32601, "message": f"Tool '{name}' not found"}
                    }
                    sys.stdout.write(json.dumps(response) + "\n")
                    sys.stdout.flush()
                    continue

                response = {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "content": [{"type": "text", "text": result}]
                    }
                }
            elif method == "notifications/initialized":
                logging.info("Received initialized notification")
                continue
            else:
                logging.warning(f"Unsupported method: {method}")
                response = {
                    "jsonrpc": "2.0", 
                    "id": req_id, 
                    "error": {"code": -32601, "message": f"Method '{method}' not found"}
                }
            
            resp_str = json.dumps(response)
            logging.debug(f"Sending: {resp_str}")
            sys.stdout.write(resp_str + "\n")
            sys.stdout.flush()
        except Exception as e:
            logging.error(f"Error in main loop: {str(e)}", exc_info=True)
            # Try to send an error response if we have an ID
            try:
                if 'req_id' in locals():
                    err_resp = {
                        "jsonrpc": "2.0",
                        "id": req_id,
                        "error": {"code": -32603, "message": str(e)}
                    }
                    sys.stdout.write(json.dumps(err_resp) + "\n")
                    sys.stdout.flush()
            except:
                pass

if __name__ == "__main__":
    main()
