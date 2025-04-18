import asyncio
import pytest
import pytest_asyncio
from lean_sdk import LeanRpcClientAsync, LeanSessionAsync
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


@pytest_asyncio.fixture
async def client():
    lean_project_path = Path(__file__).parent / "../../../test/MathlibTest"
    return await LeanRpcClientAsync.create(lean_project_path)


@pytest_asyncio.fixture
async def session(client):
    return await LeanSessionAsync.create(client)


@pytest_asyncio.fixture
async def session_mathlib(client):
    return await LeanSessionAsync.create(client, imports=["Mathlib"])


@pytest.mark.asyncio
async def test_client(session):
    res = await session.run_command("#check id")
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


@pytest.mark.asyncio
async def test_imports(client):
    session = await LeanSessionAsync.create(client, imports=["LeanSDK.JsonRpc"])
    res = await session.run_command("#check IO.FS.Stream.writeJsonRpcMessage")
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


@pytest.mark.asyncio
async def test_cal_char(session_mathlib):
    res = await session_mathlib.run_command("open Topology")
    assert res == CommandResponse(
        messages=[],
        sorries=[],
        env=0,
    )
    res = await session_mathlib.run_command("#check 𝓝")
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


@pytest.mark.asyncio
async def test_tactic(session):
    res = await session.run_command("example (x y : Prop) : x ↔ y := sorry")
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

    res = await ts.apply_tactic("constructor")
    assert res == TacticResponse(
        proofState=0,
        goals=["case mp\nx y : Prop\n⊢ x → y", "case mpr\nx y : Prop\n⊢ y → x"],
        proofStatus=None,
        sorries=[],
    )

    res = await ts.apply_tactic("sorry")
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


@pytest.mark.asyncio
async def test_simultaneous_requests(session):
    session_b = session.fork()

    res1, res2 = await asyncio.gather(
        session.run_command("#check id"),
        session_b.run_command("#check id"),
    )
    assert res1 == res2
