module
public meta import SmcTuring.Native.ConversionOwnership
public meta import Lean
open Lean SmcTuring.Native SmcTuring.Native.ConversionLayout
public meta def main (args : List String) : IO Unit := do
  let mode := if args[0]! == "x64" then Mode.x64 else Mode.x86
  let layout : Layout := ⟨args[1]!.toNat!, args[2]!.toNat!, args[3]!.toNat!⟩
  let packets := (entries mode layout).map fun entry => Json.mkObj [
    ("pc",toJson entry.pc), ("bytes",toJson ((entry.bytes mode).map BitVec.toNat))]
  IO.println (Json.mkObj [("packets",toJson packets), ("end",toJson (endPC mode layout)),
    ("source",toJson layout.source), ("destination",toJson layout.destination),
    ("span",toJson (span mode)), ("ownerZeroBytes",toJson ((encode mode (.moffs 0)).map BitVec.toNat))]).compress
