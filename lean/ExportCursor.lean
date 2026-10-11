module
public meta import SmcTuring.Appendix.CursorImage
public meta import Lean.Data.Json.FromToJson.Basic
public meta import Lean.Data.Json.Parser
open Lean SmcTuring.Native SmcTuring.Appendix
public meta def cursorRow (mode : Mode) (layout : CursorLayout.Layout) (value : Nat) : Json :=
 Json.mkObj [("value",toJson value),("bytes",toJson ((CursorImage.bytes mode layout (BitVec.ofNat 32 value)).map BitVec.toNat))]
public meta def main : IO Unit := do
 let some path ← IO.getEnv "SMCTURING_CURSOR_SITES" | throw (IO.userError "missing sites")
 let some architecture ← IO.getEnv "SMCTURING_CURSOR_ARCH" | throw (IO.userError "missing mode")
 let source ← IO.FS.readFile path
 let result : Except String Json := do
  let input ← Json.parse source
  let pc ← input.getObjValAs? Nat "pc"
  let cursor ← input.getObjValAs? Nat "cursor"
  let head ← input.getObjValAs? Nat "head"
  let live ← input.getObjVal? "live"
  let rows ← live.getArr?
  let values ← rows.toList.mapM (fun row => row.getObjValAs? Nat "value")
  let mode := if architecture == "x86" then Mode.x86 else .x64
  let layout : CursorLayout.Layout := ⟨pc,cursor,head⟩
  let pointerOwner := (SmcTuring.Native.encode mode (.moffs 0)).map BitVec.toNat
  let tapeOwner := (DwordArithmetic.encode (DwordArithmetic.located mode (.store 0 0) head (head+6))).map BitVec.toNat
  pure (Json.mkObj [("pc",toJson pc),("cursor",toJson cursor),("head",toJson head),
    ("endpoint",toJson (CursorLayout.endPC mode layout)),
    ("initial",toJson ((CursorImage.bytes mode layout 2147483648).map BitVec.toNat)),
    ("owners",toJson [pointerOwner,tapeOwner]),
    ("live",toJson (values.map (cursorRow mode layout))),("checks",toJson (CursorLayout.checks mode layout)),
    ("middle",toJson (CursorLayout.middlePC mode layout)),
    ("relocations",toJson (if mode = .x86 then [6,6,6] else [4,4,8]))])
 match result with
 | .ok value => IO.println value.compress
 | .error message => throw (IO.userError message)
