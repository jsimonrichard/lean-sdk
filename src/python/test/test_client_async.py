import pytest
import pytest_asyncio
from lean_sdk import LeanRpcClientAsync, LeanSessionAsync
from pathlib import Path


@pytest_asyncio.fixture
async def client():
    lean_project_path = Path(__file__).parent.parent.parent / "LeanSDK"
    return await LeanRpcClientAsync.create(lean_project_path)


@pytest_asyncio.fixture
async def session(client):
    return await LeanSessionAsync.create(client)


@pytest.mark.asyncio
async def test_client(session):
    res = await session.run_command("#check id")
    assert res == [
        {
            "severity": "info",
            "pos": {"line": 1, "column": 0},
            "endPos": {"line": 1, "column": 6},
            "data": "id.{u} {α : Sort u} (a : α) : α",
        }
    ]


@pytest.mark.asyncio
async def test_imports(client):
    session = await LeanSessionAsync.create(client, imports=["LeanSDK.JsonRpc"])
    res = await session.run_command("#check IO.FS.Stream.writeJsonRpcMessage")
    assert res == [
        {
            "severity": "info",
            "pos": {"line": 1, "column": 0},
            "endPos": {"line": 1, "column": 6},
            "data": "IO.FS.Stream.writeJsonRpcMessage (h : IO.FS.Stream) (msg : Lean.JsonRpc.Message) : IO Unit",
        }
    ]
