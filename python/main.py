import json
import subprocess
from typing import Any, Dict, Optional
from jsonrpcclient import request, parse, Ok, Error
from pathlib import Path


class LeanRpcClient:
    def __init__(self, cwd: Path = Path(__file__).parent, lean_path: Path = Path(__file__).parent / "../.lake/build/bin/lean-sdk"):
        """Initialize the LeanRPC client.

        Args:
            lean_path: Path to the Lean executable. If None, uses LeanRpc/.lake/build/bin/leanrpc
        """
        self.process = subprocess.Popen(
            [str(lean_path)],
            cwd=str(cwd),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )

    def _send_request(
        self, method: str, params: Optional[Dict[str, Any]] = None
    ) -> Any:
        """Send a JSON-RPC request to the LeanRPC server.

        Args:
            method: The RPC method to call
            params: Optional parameters for the method

        Returns:
            The response from the server
        """
        # Create the JSON-RPC request
        json_request = request(method, params)

        # Convert to string and calculate length
        request_str = json.dumps(json_request)
        request_bytes = request_str.encode('utf-8')
        content_length = len(request_bytes)

        # Format the message with headers
        message = f"Content-Length: {content_length}\r\n\r\n".encode('utf-8') + request_bytes + b"\n"

        # Send the message
        self.process.stdin.write(message)
        self.process.stdin.flush()

        # Read the response header
        header = self.process.stdout.readline().decode('utf-8').strip()
        if not header.startswith("Content-Length: "):
            raise RuntimeError(f"Invalid response header: {header}")

        # Parse content length
        content_length = int(header.split(": ")[1])

        # Skip the blank line
        self.process.stdout.readline()

        # Read the response body
        response_bytes = self.process.stdout.read(content_length)
        response_str = response_bytes.decode('utf-8')

        # Parse the response
        response = parse(json.loads(response_str))

        if isinstance(response, Ok):
            return response.result
        else:
            raise RuntimeError(f"RPC error: {response.message}")

    def close(self):
        """Close the connection to the LeanRPC server."""
        if self.process:
            self.process.stdin.close()
            self.process.stdout.close()
            self.process.stderr.close()
            self.process.terminate()
            self.process.wait()

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.close()


if __name__ == "__main__":
    client = LeanRpcClient(cwd=Path(__file__).parent.parent)
    print(client._send_request("runCommand", params={"cmd":
"""
import LeanSDK.JsonRpc -- can access external environment

macro "def_to_forall" _a:ident args:bracketedBinder* " : " b:term : term =>
  `(∀ $args*, $b)

#check id
"""}))
