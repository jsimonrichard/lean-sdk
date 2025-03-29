import json
import subprocess
from typing import Any, Dict, List, Optional
import jsonrpcclient
from pathlib import Path
import logging


class LeanRpcClient:
    def __init__(self, lean_project_path: Path | str):
        """Initialize the LeanRPC client.

        Args:
            lean_project_path: Path to the Lean project, which must have the LeanSDK as a git dependency.
        """
        self.lean_project_path = Path(lean_project_path)
        self.process = subprocess.Popen(
            ["lake", "exe", "lean-sdk"],
            cwd=self.lean_project_path,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )

    def _to_message_bytes(
        self, method: str, params: Optional[Dict[str, Any] | List[Any]] = None
    ) -> bytes:
        """
        Convert request to a JSON-RPC message with the correct headers.

        Args:
            method: The RPC method to call
            params: Optional parameters for the method

        Returns:
            The JSON-RPC message as a bytes object (in UTF-8)
        """
        json_request = jsonrpcclient.request(method, params)
        request_str = json.dumps(json_request)
        request_bytes = request_str.encode("utf-8")
        content_length = len(request_bytes)
        return (
            f"Content-Length: {content_length}\r\n\r\n".encode("utf-8") + request_bytes
        )

    def _write_message(
        self, method: str, params: Optional[Dict[str, Any] | List[Any]] = None
    ):
        """Write a JSON-RPC message to the LeanRPC server."""
        message = self._to_message_bytes(method, params)
        logging.debug(f"Sending message: {message.decode('utf-8')}")

        self.process.stdin.write(message)
        self.process.stdin.flush()

    def _read_response(self) -> Any:
        """Read the response from the LeanRPC server."""

        # Read the response header
        header = self.process.stdout.readline().decode("utf-8").strip()
        if not header.startswith("Content-Length: "):
            raise RuntimeError(f"Invalid response header: {header}")

        # Parse content length
        content_length = int(header.split(": ")[1])

        # Skip the blank line
        self.process.stdout.readline()

        # Read the response body
        response_bytes = self.process.stdout.read(content_length)
        response_str = response_bytes.decode("utf-8")
        logging.debug(f"Received response: {response_str}")
        # Parse the response
        return jsonrpcclient.parse(json.loads(response_str))

    def _send_request(
        self, method: str, params: Optional[Dict[str, Any] | List[Any]] = None
    ) -> Any:
        """Send a JSON-RPC request to the LeanRPC server.

        Args:
            method: The RPC method to call
            params: Optional parameters for the method

        Returns:
            The response from the server
        """
        self._write_message(method, params)

        response = self._read_response()
        if isinstance(response, jsonrpcclient.Ok):
            return response.result
        else:
            raise RuntimeError(f"Error from the lean server: {response.message}")

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


class LeanSession:
    def __init__(
        self,
        client: LeanRpcClient,
        env: Optional[int] = None,
        imports: Optional[List[str]] = None,
    ):
        self.client = client
        self.env = env

        if env and imports:
            raise RuntimeError(
                "Cannot specify both env and imports because imports have to stated at the top of the file"
            )

        if imports:
            self.run_command("\n".join([f"import {import_}" for import_ in imports]))

    def run_command(self, command: str):
        res = self.client._send_request(
            "runCommand", params={"cmd": command, "env": self.env}
        )
        if "env" not in res:
            raise RuntimeError(f"LeanRPC error: env missing from response: {res}")
        self.env = res["env"]

        return res["messages"] if "messages" in res else None

    def fork(self):
        return LeanSession(self.client, self.env, imports=None)


if __name__ == "__main__":
    client = LeanRpcClient(cwd=Path(__file__).parent.parent)
    print(
        client._send_request(
            "runCommand",
            params={
                "cmd": """
import LeanSDK.JsonRpc -- can access external environment

macro "def_to_forall" _a:ident args:bracketedBinder* " : " b:term : term =>
  `(∀ $args*, $b)

#check id
"""
            },
        )
    )
