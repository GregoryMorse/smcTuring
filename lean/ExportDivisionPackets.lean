module
public meta import SmcTuring.Appendix.DivisionPackets
public meta import SmcTuring.Appendix.DivisionLayout
public meta import Lean
open Lean SmcTuring.Appendix

/-- Independent executable export of the literal Lean codec/placement.
Finite comparison is evidence; it does not establish physical ISA refinement. -/
public meta def addressSites : DivisionByteCode.Form → List Nat
  | .common (.common (.storeAcc _)) => [1]
  | .common (.common (.callRelative _)) => []
  | _ => [2]

public meta def dynamicOffsets : DivisionByteCode.Form → List Nat
  | .common (.common (.immediate _ _ _)) => [6]
  | .common (.common (.callRelative _)) => [1]
  | .common (.addImmediate _ _) | .subtractImmediate _ _ => [6]
  | _ => []

public meta def packetJSON (pc : Nat) (form : DivisionByteCode.Form) : Json :=
  Json.mkObj [("pc", toJson pc), ("bytes", toJson ((DivisionByteCode.encode form).map BitVec.toNat)),
    ("address_relocations", toJson ((addressSites form).map (pc + ·))),
    ("dynamic_offsets", toJson (dynamicOffsets form))]

public meta def main (args : List String) : IO Unit := do
  if args.length != 17 then throw (IO.userError "Expected four origin/X/Y/result rows and one DEFSTACK instruction")
  let stack := args[16]!.toNat!
  let rows := (List.range 4).map fun mode =>
    let place : DivisionPackets.Placement :=
      { origin := args[4*mode]!.toNat!, inputX := args[4*mode+1]!.toNat!,
        inputY := args[4*mode+2]!.toNat!, result := args[4*mode+3]!.toNat!,
        stackInstruction := stack, unused := 0x1000000 + mode*32,
        mod := decide (mode % 2 = 1), signed := decide (2 ≤ mode) }
    let originalEntries := DivisionLayout.entries place 0 0
    let originalImage := originalEntries.map fun entry =>
      let sites := addressSites entry.packet.initial
      let relocs := if entry.pc = stack then sites ++ [6] else sites
      Json.mkObj [("pc",toJson entry.pc),("bytes",toJson (entry.bytes.map BitVec.toNat)),
        ("address_relocations",toJson (relocs.map (entry.pc+·))),
        ("owned_fields",toJson entry.fields)]
    let pure := DivisionPackets.positioned place.origin (DivisionPackets.packets place)
    let inactive := DivisionPackets.inactiveOwners place
    let slots := ([DivisionWords.Slot.x, .y, .result] ++
      ([DivisionBlocks.Block.initial, .guard, .body, .finish].flatMap
        (DivisionBlocks.written (DivisionPackets.layout place)))).eraseDups
    let fields := (slots.map (DivisionPackets.fields place)) ++ [stack+2,stack+6]
    let inactiveJSON := inactive.map fun (pc,form) =>
      let sites := addressSites form
      let relocs := if pc = stack then sites ++ [6] else sites
      Json.mkObj [("pc",toJson pc),("bytes",toJson ((DivisionByteCode.encode form).map BitVec.toNat)),
        ("address_relocations",toJson (relocs.map (pc+·))),
        ("dynamic_offsets",toJson (if pc = stack then [2,6] else [6]))]
    Json.mkObj [("mode",toJson mode),("origin",toJson place.origin),
      ("pure_span",toJson (DivisionPackets.span (DivisionPackets.packets place))),
      ("pure",toJson (pure.map fun (pc,form) => packetJSON pc form)),
      ("inactive",toJson inactiveJSON),("fields",toJson fields),
      ("original_image",toJson originalImage),
      ("original_image_fields",toJson (DivisionPacking.fields originalEntries)),
      ("admissible",toJson [
        decide (place.origin + DivisionLayout.pureSpan place ≤ place.inputX),
        decide (place.inputX+10 ≤ place.inputY), decide (place.inputY+10 ≤ place.result),
        decide (place.result+10 ≤ stack), decide (stack+10 ≤ 2^32),
        decide (stack+10 ≤ place.unused)])]
  IO.println (toJson rows).compress
