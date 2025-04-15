import pytest
from lean_sdk import LeanRpcClient, LeanSession
from lean_sdk.schema import (
    CommandResponse,
    MessageSeverity,
    Message,
    Pos,
    Sorry,
    TacticResponse,
)
from pathlib import Path

# Overloads schema __eq__ definitions
import test.utils  # noqa: F401


@pytest.fixture
def client():
    lean_project_path = Path(__file__).parent / "../../../test/MathlibTest"
    return LeanRpcClient(lean_project_path)


@pytest.fixture
def session(client):
    return LeanSession(client)


@pytest.fixture
def session_mathlib(client):
    return LeanSession(client, imports=["Mathlib"])


def test_client(session):
    res = session.run_command("#check id")
    assert res == CommandResponse(
        messages=[
            Message(
                severity=MessageSeverity.info,
                pos=Pos(line=1, column=0),
                endPos=Pos(line=1, column=6),
                data="id.{u} {α : Sort u} (a : α) : α",
            )
        ],
        sorries=[],
        env=0,
    )


def test_imports(client):
    session = LeanSession(client, imports=["LeanSDK.JsonRpc"])
    res = session.run_command("#check IO.FS.Stream.writeJsonRpcMessage")
    assert res == CommandResponse(
        messages=[
            Message(
                severity=MessageSeverity.info,
                pos=Pos(line=1, column=0),
                endPos=Pos(line=1, column=6),
                data="IO.FS.Stream.writeJsonRpcMessage (h : IO.FS.Stream) (msg : Lean.JsonRpc.Message) : IO Unit",
            )
        ],
        sorries=[],
        env=0,
    )


def test_cal_char(client):
    session = LeanSession(client, imports=["Mathlib"])
    session.run_command("open Topology")
    res = session.run_command("#check 𝓝")
    assert res == CommandResponse(
        messages=[
            Message(
                severity=MessageSeverity.info,
                pos=Pos(line=1, column=0),
                endPos=Pos(line=1, column=6),
                data="𝓝 : ?m.2 → Filter ?m.2",
            )
        ],
        sorries=[],
        env=0,
    )


def test_tactic(session):
    res = session.run_command("example (x y : Prop) : x ↔ y := sorry")
    assert res == CommandResponse(
        messages=[
            Message(
                severity=MessageSeverity.warning,
                pos=Pos(line=1, column=0),
                endPos=Pos(line=1, column=7),
                data="declaration uses 'sorry'",
            )
        ],
        sorries=[
            Sorry(
                pos=Pos(line=1, column=32),
                endPos=Pos(line=1, column=37),
                goal="x y : Prop\n⊢ x ↔ y",
                proofState=0,
            )
        ],
        env=0,
    )

    ts = session.tactic_sessions[0]

    res = ts.apply_tactic("constructor")
    assert res == TacticResponse(
        proofState=0,
        goals=["case mp\nx y : Prop\n⊢ x → y", "case mpr\nx y : Prop\n⊢ y → x"],
        proofStatus=None,
        sorries=[],
    )

    res = ts.apply_tactic("sorry")
    assert res == TacticResponse(
        proofState=0,
        goals=["case mpr\nx y : Prop\n⊢ y → x"],
        proofStatus=None,
        sorries=[
            Sorry(
                pos=None,
                endPos=None,
                goal="case mp\nx y : Prop\n⊢ x → y",
                proofState=0,
            )
        ],
    )
