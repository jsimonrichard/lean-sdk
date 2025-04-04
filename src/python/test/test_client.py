import pytest
from lean_sdk import LeanRpcClient, LeanSession
from pathlib import Path


@pytest.fixture
def client():
    lean_project_path = Path(__file__).parent / "../../../test/MathlibTest"
    return LeanRpcClient(lean_project_path)


@pytest.fixture
def session(client):
    return LeanSession(client)


def test_client(session):
    res = session.run_command("#check id")
    assert res == [
        {
            "severity": "info",
            "pos": {"line": 1, "column": 0},
            "endPos": {"line": 1, "column": 6},
            "data": "id.{u} {α : Sort u} (a : α) : α",
        }
    ]


def test_imports(client):
    session = LeanSession(client, imports=["LeanSDK.JsonRpc"])
    res = session.run_command("#check IO.FS.Stream.writeJsonRpcMessage")
    assert res == [
        {
            "severity": "info",
            "pos": {"line": 1, "column": 0},
            "endPos": {"line": 1, "column": 6},
            "data": "IO.FS.Stream.writeJsonRpcMessage (h : IO.FS.Stream) (msg : Lean.JsonRpc.Message) : IO Unit",
        }
    ]

def test_cal_char(client):
    session = LeanSession(client, imports=["Mathlib"])
    session.run_command("open Topology")
    res = session.run_command("#check 𝓝")
    assert res == [
        {
            "severity": "info",
            "pos": {"line": 1, "column": 0},
            "endPos": {"line": 1, "column": 6},
            "data": "𝓝 : ?m.2 → Filter ?m.2",
        }
    ]
