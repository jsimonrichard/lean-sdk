/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import Lean.Data.Json
import Lean.Data.JsonRpc
import LeanSDK.JSON
import LeanSDK.Frontend
import LeanSDK.Util.Path
import LeanSDK.Lean.ContextInfo
import LeanSDK.Lean.Environment
import LeanSDK.Lean.InfoTree
import LeanSDK.Lean.InfoTree.ToJson
import LeanSDK.Snapshots
import LeanSDK.JsonRpc

open Lean.Json Lean.JsonRpc

/-!
# A LeanSDK for Lean.

Communicates via JSON on stdin and stdout. Commands should be separated by blank lines.

Commands may be of the form
```
{ "cmd" : "import Mathlib.Data.List.Basic\ndef f := 2" }
```
or
```
{ "cmd" : "example : f = 2 := rfl", "env" : 3 }
```

The `env` field, if present,
must contain a number received in the `env` field of a previous response,
and causes the command to be run in the existing environment.

If there is no `env` field, a new environment is created.

You can only use `import` commands when you do not specify the `env` field.

You can backtrack simply by using earlier values for `env`.

The results are of the form
```
{"sorries":
 [{"pos": {"line": 1, "column": 18},
   "endPos": {"line": 1, "column": 23},
   "goal": "\n⊢ Nat"}],
 "messages":
 [{"severity": "error",
   "pos": {"line": 1, "column": 23},
   "endPos": {"line": 1, "column": 26},
   "data":
   "type mismatch\n  rfl\nhas type\n  f = f : Prop\nbut is expected to have type\n  f = 2 : Prop"}],
 "env": 6}
 ```
 showing any messages generated, or sorries with their goal states.
 Information is generated for tactic mode sorries, but not for term mode sorries.
-/

open Lean Elab Lean.Json Lean.JsonRpc

namespace LeanSDK

/-- The monadic state for the Lean LeanSDK. -/
structure State where
  /--
  Environment snapshots after complete declarations.
  The user can run a declaration in a given environment using `{"cmd": "def f := 37", "env": 17}`.
  -/
  cmdStates : Array CommandSnapshot := #[]
  /--
  Proof states after individual tactics.
  The user can run a tactic in a given proof state using `{"tactic": "exact 42", "proofState": 5}`.
  Declarations with containing `sorry` record a proof state at each sorry,
  and report the numerical index for the recorded state at each sorry.
  -/
  proofStates : Array ProofSnapshot := #[]

/--
The Lean LeanSDK monad.

We only use this with `m := IO`, but it is set up as a monad transformer for flexibility.
-/
abbrev M (m : Type → Type) := StateT State m

variable {m} [Monad m] [MonadLiftT IO m]

abbrev E (m : Type → Type) := ExceptT JsonRpc.Message m

instance: MonadLiftT (M m) (E (M m)) where
  monadLift := ExceptT.lift


/-- Record an `CommandSnapshot` into the LeanSDK state, returning its index for future use. -/
def recordCommandSnapshot (state : CommandSnapshot) : M m Nat := do
  let id := (← get).cmdStates.size
  modify fun s => { s with cmdStates := s.cmdStates.push state }
  return id

/-- Record a `ProofSnapshot` into the LeanSDK state, returning its index for future use. -/
def recordProofSnapshot (proofState : ProofSnapshot) : M m Nat := do
  let id := (← get).proofStates.size
  modify fun s => { s with proofStates := s.proofStates.push proofState }
  return id

def sorries (trees : List InfoTree) (env? : Option Environment) : M m (List Sorry) :=
  trees.flatMap InfoTree.sorries |>.filter (fun t => match t.2.1 with
    | .term _ none => false
    | _ => true ) |>.mapM
      fun ⟨ctx, g, pos, endPos⟩ => do
        let (goal, proofState) ← match g with
        | .tactic g => do
           let s ← ProofSnapshot.create ctx none env? [g]
           pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term lctx (some t) => do
           let s ← ProofSnapshot.create ctx lctx env? [] [t]
           pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term _ none => unreachable!
        let proofStateId ← proofState.mapM recordProofSnapshot
        return Sorry.of goal pos endPos proofStateId

def ppTactic (ctx : ContextInfo) (stx : Syntax) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def tactics (trees : List InfoTree) : M m (List Tactic) :=
  trees.flatMap InfoTree.tactics |>.mapM
    fun ⟨ctx, stx, goals, pos, endPos, ns⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none none goals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let tactic := Format.pretty (← ppTactic ctx stx)
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Tactic.of goals tactic pos endPos proofStateId ns

/-- Record a `ProofSnapshot` and generate a JSON response for it. -/
def createProofStepReponse (proofState : ProofSnapshot) (old? : Option ProofSnapshot := none) :
    M m ProofStepResponse := do
  let messages := proofState.newMessages old?
  let messages ← messages.mapM fun m => Message.of m
  let traces ← proofState.newTraces old?
  let trees := proofState.newInfoTrees old?
  let trees ← match old? with
  | some old => do
    let (ctx, _) ← old.runMetaM do return { ← CommandContextInfo.save with }
    let ctx := PartialContextInfo.commandCtx ctx
    pure <| trees.map fun t => InfoTree.context ctx t
  | none => pure trees
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorries trees none
  let id ← recordProofSnapshot proofState
  return {
    proofState := id
    goals := (← proofState.ppGoals).map fun s => s!"{s}"
    messages
    sorries
    traces }

/-- Pickle a `CommandSnapshot`, generating a JSON response. -/
def pickleCommandSnapshot (n : PickleEnvironment) : M m (CommandResponse ⊕ Error) := do
  match (← get).cmdStates[n.env]? with
  | none => return .inr ⟨"Unknown environment."⟩
  | some env =>
    discard <| env.pickle n.pickleTo
    return .inl { env := n.env }

/-- Unpickle a `CommandSnapshot`, generating a JSON response. -/
def unpickleCommandSnapshot (n : UnpickleEnvironment) : M IO CommandResponse := do
  let (env, _) ← CommandSnapshot.unpickle n.unpickleEnvFrom
  let env ← recordCommandSnapshot env
  return { env }

/-- Pickle a `ProofSnapshot`, generating a JSON response. -/
-- This generates a new identifier, which perhaps is not what we want?
def pickleProofSnapshot (n : PickleProofState) : M m (ProofStepResponse ⊕ Error) := do
  match (← get).proofStates[n.proofState]? with
  | none => return .inr ⟨"Unknown proof State."⟩
  | some proofState =>
    discard <| proofState.pickle n.pickleTo
    return .inl (← createProofStepReponse proofState)

/-- Unpickle a `ProofSnapshot`, generating a JSON response. -/
def unpickleProofSnapshot (n : UnpickleProofState) : M IO (ProofStepResponse ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← do match n.env with
  | none => pure (none, false)
  | some i => do match (← get).cmdStates[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let (proofState, _) ← ProofSnapshot.unpickle n.unpickleProofStateFrom cmdSnapshot?
  Sum.inl <$> createProofStepReponse proofState

/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def runCommand (s : Command) : M IO (CommandResponse ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← do match s.env with
  | none => pure (none, false)
  | some i => do match (← get).cmdStates[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let initialCmdState? := cmdSnapshot?.map fun c => c.cmdState
  let (cmdState, messages, trees) ← try
    IO.processInput s.cmd initialCmdState?
  catch ex =>
    return .inr ⟨ex.toString⟩
  let messages ← messages.mapM fun m => Message.of m
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorries trees (initialCmdState?.map (·.env))
  let tactics ← match s.allTactics with
  | some true => tactics trees
  | _ => pure []
  let cmdSnapshot :=
  { cmdState
    cmdContext := (cmdSnapshot?.map fun c => c.cmdContext).getD
      { fileName := "",
        fileMap := default,
        snap? := none,
        cancelTk? := none } }
  let env ← recordCommandSnapshot cmdSnapshot
  let jsonTrees := match s.infotree with
  | some "full" => trees
  | some "tactics" => trees.flatMap InfoTree.retainTacticInfo
  | some "original" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainOriginal
  | some "substantive" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainSubstantive
  | _ => []
  let infotree ← if jsonTrees.isEmpty then
    pure none
  else
    pure <| some <| Json.arr (← jsonTrees.toArray.mapM fun t => t.toJson none)
  return .inl
    { env,
      messages,
      sorries,
      tactics
      infotree }

def processFile (s : File) : M IO (CommandResponse ⊕ Error) := do
  try
    let cmd ← IO.FS.readFile s.path
    runCommand { s with env := none, cmd }
  catch e =>
    pure <| .inr ⟨e.toString⟩

/--
Run a single tactic, returning the id of the new proof statement, and the new goals.
-/
-- TODO detect sorries?
def runProofStep (s : ProofStep) : M IO (ProofStepResponse ⊕ Error) := do
  match (← get).proofStates[s.proofState]? with
  | none => return .inr ⟨"Unknown proof state."⟩
  | some proofState =>
    try
      let proofState' ← proofState.runString s.tactic
      return .inl (← createProofStepReponse proofState' proofState)
    catch ex =>
      return .inr ⟨"Lean error:\n" ++ ex.toString⟩

end LeanSDK

open Lean.Json Lean.JsonRpc LeanSDK

instance [ToJson α] [ToJson β] : ToJson (α ⊕ β) where
  toJson x := match x with
  | .inl a => toJson a
  | .inr b => toJson b

/-- Commands accepted by the LeanSDK. -/
inductive Input
| command : LeanSDK.Command → Input
| file : LeanSDK.File → Input
| proofStep : LeanSDK.ProofStep → Input
| pickleEnvironment : LeanSDK.PickleEnvironment → Input
| unpickleEnvironment : LeanSDK.UnpickleEnvironment → Input
| pickleProofSnapshot : LeanSDK.PickleProofState → Input
| unpickleProofSnapshot : LeanSDK.UnpickleProofState → Input

/-- Parse a user input string to an input command. -/
def parse (json : Json) : IO Input := do
  match fromJson? json with
    | .ok (r : LeanSDK.ProofStep) => return .proofStep r
    | .error _ => match fromJson? json with
    | .ok (r : LeanSDK.PickleEnvironment) => return .pickleEnvironment r
    | .error _ => match fromJson? json with
    | .ok (r : LeanSDK.UnpickleEnvironment) => return .unpickleEnvironment r
    | .error _ => match fromJson? json with
    | .ok (r : LeanSDK.PickleProofState) => return .pickleProofSnapshot r
    | .error _ => match fromJson? json with
    | .ok (r : LeanSDK.UnpickleProofState) => return .unpickleProofSnapshot r
    | .error _ => match fromJson? json with
    | .ok (r : LeanSDK.Command) => return .command r
    | .error _ => match fromJson? json with
    | .ok (r : LeanSDK.File) => return .file r
    | .error e => throw <| IO.userError <| toString <| toJson <|
        (⟨"Could not parse as a valid JSON command:\n" ++ e⟩ : Error)


-- unsafe def server : IO Unit :=
--   StateT.run' loop {}
-- where loop : M IO Unit := do
--   let query ← getLines
--   if query = "" then
--     return ()
--   IO.println <| toString <| ← match ← parse query with
--   | .command r => return toJson (← runCommand r)
--   | .file r => return toJson (← processFile r)
--   | .proofStep r => return toJson (← runProofStep r)
--   | .pickleEnvironment r => return toJson (← pickleCommandSnapshot r)
--   | .unpickleEnvironment r => return toJson (← unpickleCommandSnapshot r)
--   | .pickleProofSnapshot r => return toJson (← pickleProofSnapshot r)
--   | .unpickleProofSnapshot r => return toJson (← unpickleProofSnapshot r)
--   loop

def toMethodInput [FromJson α] (id : RequestID) (params : Option Structured) : E (M IO) α := do
  match params with
  | none => throw $ .responseError id .invalidRequest "No parameters" none
  | some p => match fromJson? (toJson p) with
  | .error e => throw $ .responseError id .parseError e none
  | .ok command => pure command

def handler (id: RequestID) (method: String) (params: Option Structured) : E (M IO) JsonRpc.Message := do
  match method with
  | "runCommand" =>
    let command: LeanSDK.Command := ← toMethodInput id params
    pure $ .response id $ toJson (← runCommand command)
  | "processFile" =>
    let file: LeanSDK.File := ← toMethodInput id params
    pure $ .response id $ toJson (← processFile file)
  | "runProofStep" =>
    let proofStep: LeanSDK.ProofStep := ← toMethodInput id params
    pure $ .response id $ toJson (← runProofStep proofStep)
  | "pickleEnvironment" =>
    let pickleEnvironment: LeanSDK.PickleEnvironment := ← toMethodInput id params
    -- I don't know why the specializing type hint is necessary...
    pure $ .response id $ toJson (← (pickleCommandSnapshot pickleEnvironment : M IO (CommandResponse ⊕ Error)))
  | "unpickleEnvironment" =>
    let unpickleEnvironment: LeanSDK.UnpickleEnvironment := ← toMethodInput id params
    pure $ .response id $ toJson (← unpickleCommandSnapshot unpickleEnvironment)
  | _ => throw $ .responseError id .invalidRequest "Unknown method" none

def serverLoop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit :=
  StateT.run' loop {}
  where loop : M IO Unit := do
    while true do
      try
        match ← stdin.readJsonRpcMessage with
        | .request id method params =>
          stdout.writeJsonRpcMessage $ match ← handler id method params with
          | .ok msg | .error msg => msg
        | .notification _ _ => pure ()
        | .response id _ =>
          stdout.writeJsonRpcMessage $ Message.responseError id .invalidRequest "You send a response, but I'm the server!" .none
        | .responseError id _ _ _ =>
          stdout.writeJsonRpcMessage $ Message.responseError id .invalidRequest "You send a responseError, but I'm the server!" .none
      catch e => match e with
        | .userError "Cannot read JsonRpc message: Stream was closed" =>
          break
        | e =>
          stdout.writeJsonRpcMessage (Message.responseError .null .parseError e.toString .none)

/-- Main executable function, run as `lake exe LeanSDK`. -/
def main (args : List String) : IO Unit := do
  if args.any (· == "--help") || args.any (· == "-h") then
    IO.println "Usage: lake exe LeanSDK [--help | -h]

A Lean SDK that communicates via JSON-RPC on stdin and stdout.

Options:
  --help, -h    Display this help message and exit"
    return

  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  initSearchPath (← Lean.findSysroot)
  serverLoop stdin stdout
