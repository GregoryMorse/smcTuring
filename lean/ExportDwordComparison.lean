module
public meta import SmcTuring.Appendix.DwordComparison
public meta import SmcTuring.Native.DwordOwner
public meta import Lean
open Lean SmcTuring.Native SmcTuring.Appendix
public meta def comparisonRow (mode : Mode) (layout : DwordComparison.Layout) (symbol : Nat) : Json :=
 Json.mkObj [("symbol",toJson symbol),("bytes",toJson ((DwordComparison.bytes mode layout (BitVec.ofNat 32 symbol)).map BitVec.toNat))]
public meta def main : IO Unit := do
 let some path ← IO.getEnv "SMCTURING_COMPARISON_SITES" | throw (IO.userError "missing sites")
 let some architecture ← IO.getEnv "SMCTURING_COMPARISON_ARCH" | throw (IO.userError "missing mode")
 let source ← IO.FS.readFile path
 let result : Except String Json := do
  let input ← Json.parse source
  let pc ← input.getObjValAs? Nat "pc"
  let scalar ← input.getObjValAs? Nat "scalar"
  let mask ← input.getObjValAs? Nat "mask"
  let live ← input.getObjVal? "live"
  let rows ← live.getArr?
  let values ← rows.toList.mapM (fun row => row.getObjValAs? Nat "symbol")
  let mode := if architecture == "x86" then Mode.x86 else .x64
  let layout : DwordComparison.Layout := ⟨pc,scalar,mask⟩
  let scalarOwner := (DwordOwner.bytes mode (scalar-6) 0).map BitVec.toNat
  let maskOwner := (DwordArithmetic.encode
    (DwordArithmetic.located mode (.bitAnd 0 2147483648) (mask-6) mask)).map BitVec.toNat
  pure (Json.mkObj [("pc",toJson pc),("scalar",toJson scalar),("mask",toJson mask),("endpoint",toJson (pc+39)),
    ("initial",toJson ((DwordComparison.bytes mode layout 2147483648).map BitVec.toNat)),
    ("owners",toJson [scalarOwner,maskOwner]),("live",toJson (values.map (comparisonRow mode layout))),
    ("checks",toJson (DwordComparison.checks mode layout)),
    ("relocations",toJson (if mode = .x86 then [6,6,6,6,6,6,6] else [8,8,4,5,4,8,8]))])
 match result with
 | .ok value => IO.println value.compress
 | .error message => throw (IO.userError message)
