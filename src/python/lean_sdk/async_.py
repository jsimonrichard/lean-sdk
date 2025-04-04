import asyncio
import json
from typing import Any, Dict, List, Optional
import jsonrpcclient
from pathlib import Path
import logging


logger = logging.getLogger(__name__)


class LeanRpcClientAsync:
    def __init__(
        self, lean_project_path: Path | str, process: asyncio.subprocess.Process
    ):
        self.lean_project_path = Path(lean_project_path)
        self.process = process

    @classmethod
    async def create(cls, lean_project_path: Path | str):
        """Initialize the LeanRPC client.

        Args:
            lean_project_path: Path to the Lean project, which must have the LeanSDK as a git dependency.
        """
        proc = await asyncio.create_subprocess_exec(
            "lake",
            "exe",
            "lean-sdk",
            cwd=lean_project_path,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            bufsize=0,
        )
        return cls(lean_project_path, proc)

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
        request_str = json.dumps(json_request, ensure_ascii=False)
        request_bytes = request_str.encode("utf-8")
        content_length = len(request_bytes)
        return (
            f"Content-Length: {content_length}\r\n\r\n".encode("utf-8") + request_bytes
        )

    async def _write_message(
        self, method: str, params: Optional[Dict[str, Any] | List[Any]] = None
    ):
        """Write a JSON-RPC message to the LeanRPC server."""
        message = self._to_message_bytes(method, params)

        self.process.stdin.write(message)
        await self.process.stdin.drain()

    async def _read_response(self) -> Any:
        """Read the response from the LeanRPC server."""

        # Read the response header
        header = (await self.process.stdout.readline()).decode("utf-8").strip()
        if not header.startswith("Content-Length: "):
            raise RuntimeError(f"Invalid response header: {header}")

        # Parse content length
        content_length = int(header.split(": ")[1])

        # Skip the blank line
        await self.process.stdout.readline()

        # Read the response body
        response_bytes = await self.process.stdout.read(content_length)
        response_str = response_bytes.decode("utf-8")
        # Parse the response
        return jsonrpcclient.parse(json.loads(response_str))

    async def _send_request(
        self, method: str, params: Optional[Dict[str, Any] | List[Any]] = None
    ) -> Any:
        """Send a JSON-RPC request to the LeanRPC server.

        Args:
            method: The RPC method to call
            params: Optional parameters for the method

        Returns:
            The response from the server
        """
        logger.debug(f"Sending message: {method}: {json.dumps(params, indent=4)}")
        await self._write_message(method, params)

        response = await self._read_response()
        if isinstance(response, jsonrpcclient.Ok):
            logger.debug(f"Received response: {json.dumps(response.result, indent=4)}")
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


class LeanSessionAsync:
    def __init__(
        self,
        client: LeanRpcClientAsync,
        env: Optional[int] = None,
    ):
        self.client = client
        self.env = env

    @classmethod
    async def create(
        cls,
        client: LeanRpcClientAsync,
        env: Optional[int] = None,
        imports: Optional[List[str]] = None,
    ):
        session = cls(client, env)

        if env and imports:
            raise RuntimeError(
                "Cannot specify both env and imports because imports have to stated at the top of the file"
            )

        if imports:
            msgs = await session.run_command(
                "\n".join([f"import {import_}" for import_ in imports])
            )
            if msgs:
                errors = [msg for msg in msgs if msg["severity"] == "error"]
                if errors:
                    raise RuntimeError(
                        f"Errors in imports: {errors}. Please check your imports and try again."
                    )

        return session

    async def run_command(self, command: str):
        res = await self.client._send_request(
            "runCommand", params={"cmd": command, "env": self.env}
        )
        if "env" not in res:
            raise RuntimeError(f"LeanRPC error: env missing from response: {res}")
        self.env = res["env"]

        return res["messages"] if "messages" in res else None

    def fork(self):
        return LeanSessionAsync(self.client, self.env)
