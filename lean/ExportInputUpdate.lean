module
public meta import SmcTuring.Appendix.InputUpdateTrace
public meta import Lean.Data.Json.FromToJson.Basic
public meta import Lean.Data.Json.Parser
open Lean SmcTuring.Native SmcTuring.Appendix
public meta def updateRow (mode : Mode) (layout : InputUpdate.Layout) (old fresh : Nat) (chosen : Bool) : Json :=
 Json.mkObj [("old",toJson old),("fresh",toJson fresh),("chosen",toJson chosen),
   ("bytes",toJson ((InputUpdate.bytes mode layout (BitVec.ofNat 32 old) (BitVec.ofNat 32 fresh) chosen).map BitVec.toNat))]
public meta def main : IO Unit := do
 let some path ← IO.getEnv "SMCTURING_UPDATE_SITES" | throw (IO.userError "missing sites")
 let some architecture ← IO.getEnv "SMCTURING_UPDATE_ARCH" | throw (IO.userError "missing mode")
 let source ← IO.FS.readFile path
 let result : Except String Json := do
  let input ← Json.parse source
  let pc ← input.getObjValAs? Nat "pc"
  let cursor ← input.getObjValAs? Nat "cursor"
  let head ← input.getObjValAs? Nat "head"
  let live ← input.getObjVal? "live"
  let rows ← live.getArr?
  let mode := if architecture == "x86" then Mode.x86 else .x64
  let layout : InputUpdate.Layout := ⟨pc,cursor,head⟩
  let packets ← rows.toList.mapM (fun row => do
    let old ← row.getObjValAs? Nat "old"
    let fresh ← row.getObjValAs? Nat "fresh"
    let chosen ← row.getObjValAs? Bool "chosen"
    pure (updateRow mode layout old fresh chosen))
  let pointerOwner := (SmcTuring.Native.encode mode (.moffs 0)).map BitVec.toNat
  let tapeOwner := (DwordArithmetic.encode (DwordArithmetic.located mode (.store 0 0) head (head+6))).map BitVec.toNat
  let rawAnd := DwordArithmetic.located mode (.bitAnd 0 2147483648) (pc+10) (InputUpdate.field mode layout)
  let objectBytes := DwordArithmetic.encode (InputUpdate.xorForm mode layout 2147483648) ++
    DwordArithmetic.encode rawAnd ++ CursorImage.bytes mode (InputUpdate.body layout) 2147483648
  pure (Json.mkObj [("pc",toJson pc),("cursor",toJson cursor),("head",toJson head),
    ("endpoint",toJson (CursorLayout.endPC mode (InputUpdate.body layout))),
    ("initial",toJson ((InputUpdate.bytes mode layout 2147483648 2147483648 false).map BitVec.toNat)),
    ("object",toJson (objectBytes.map BitVec.toNat)),("owners",toJson [pointerOwner,tapeOwner]),
    ("live",toJson packets),("checks",toJson (InputUpdate.checks mode layout)),
    ("field",toJson (InputUpdate.field mode layout)),
    ("relocations",toJson (if mode = .x86 then [6,6,6,6,6] else [8,8,4,4,8]))])
 match result with
 | .ok value => IO.println value.compress
 | .error message => throw (IO.userError message)
