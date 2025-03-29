import Lean.Data.Json
import Lean.Data.JsonRpc
import Lean.Data.Lsp.Communication

open Lean.Json Lean.JsonRpc

namespace IO.FS.Stream
-- copied from lean4's Lean/Data/Lsp/Communication.lean

private def parseHeaderField (s : String) : Option (String × String) := do
  guard $ s ≠ "" ∧ s.takeRight 2 = "\r\n"
  let xs := (s.dropRight 2).splitOn ": "
  match xs with
  | []  => none
  | [_] => none
  | name :: value :: rest =>
    let value := ": ".intercalate (value :: rest)
    some ⟨name, value⟩

private partial def readHeaderFields (h : IO.FS.Stream) : IO <| List (String × String) := do
  let l ← h.getLine
    if l.isEmpty then
      throw $ userError "Stream was closed"
    if l = "\r\n" then
      pure []
    else
      match parseHeaderField l with
      | some hf =>
        let tail ← readHeaderFields h
        pure (hf :: tail)
      | none =>
          throw $ userError s!"Invalid header field: {repr l}"

private def readContentLengthHeader (h : IO.FS.Stream) : IO Nat := do
    let fields ← readHeaderFields h
    match fields.lookup "Content-Length" with
    | some length => match length.toNat? with
      | some n => pure n
      | none   => throw $ userError s!"Content-Length header field value '{length}' is not a Nat"
    | none => throw $ userError s!"No Content-Length field in header: {fields}"

def readJsonRpcMessage (h : IO.FS.Stream) : IO Message := do
  try
    let nBytes ← readContentLengthHeader h
    h.readMessage nBytes
  catch e =>
    throw $ userError s!"Cannot read JsonRpc message: {e}"

abbrev writeJsonRpcMessage := writeLspMessage

end IO.FS.Stream
