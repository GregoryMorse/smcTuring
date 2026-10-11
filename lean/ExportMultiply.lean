module
public meta import SmcTuring.Appendix.MultiplyLayout
public meta import Lean
open Lean SmcTuring.Appendix

meta def mulLayout : MultiplyBlocks.Layout :=
  { origin := 0, fields := fun _ => 0, pointer := 0, address := 0, entryDisplacement := 0, backDisplacement := 0 }

/-- Finite geometry comparator; evaluating JSON does not prove CPU semantics. -/
public meta def main (args : List String) : IO Unit := do
  if args.length != 5 then throw (IO.userError "Expected origin/inputX/inputY/result/stack instruction coordinates")
  let place : MultiplyPackets.Placement :=
    { origin := args[0]!.toNat!, inputX := args[1]!.toNat!, inputY := args[2]!.toNat!,
      result := args[3]!.toNat!, stackInstruction := args[4]!.toNat! }
  let absoluteOffsets : MultiplyByteCode.Form → List Nat := fun form => match form with
    | .common (.callRelative _) => []
    | .common (.storeAcc _) => [1]
    | _ => [2]
  let packetJson := fun (offset : Nat) (form : MultiplyByteCode.Form) (absolute : List Nat) =>
    Json.mkObj [("offset", toJson offset),
      ("bytes", toJson ((MultiplyByteCode.encode form).map BitVec.toNat)),
      ("absolute_offsets", toJson absolute)]
  let emitted := (MultiplyPackets.positioned 0 (MultiplyPackets.packets place)).map
    (fun (offset, form) => packetJson offset form (absoluteOffsets form))
  let owners := (MultiplyPackets.inactiveOwners place).map
    (fun (pc, form) => packetJson pc form (if pc = place.stackInstruction then [2,6] else [2]))
  let imageEntries := MultiplyLayout.entries place 0 0
  let imagePackets := imageEntries.map (fun entry =>
    Json.mkObj [("offset", toJson entry.pc),
      ("bytes", toJson (entry.bytes.map BitVec.toNat)),
      ("owned_fields", toJson entry.fields),
      ("absolute_offsets", toJson
        (if entry.pc = place.stackInstruction then [2,6] else absoluteOffsets entry.packet.initial))])
  let imageFields := MultiplyPacking.fields imageEntries
  let fieldCoords := [MultiplyWords.Slot.x, .y, .result, .factor, .multiplier, .total, .delta,
    .mask, .displacement, .bit, .addMask, .addend].map (MultiplyPackets.fields place)
  let metadata := [place.stackInstruction + 6, place.stackInstruction + 2]
  let layout := mulLayout
  let spans := [MultiplyBlocks.Block.initial, .guard, .body, .finish].map
    (fun block => (MultiplyBlocks.words layout block).map MultiplyControl.dataLength)
  IO.println (Json.mkObj [
    ("literal_packets", toJson emitted), ("owner_packets", toJson owners),
    ("initial_image_packets", toJson imagePackets), ("initial_image_fields", toJson imageFields),
    ("field_coordinates", toJson (fieldCoords ++ metadata)),
    ("data_lengths", toJson spans),
    ("guard_continuation", toJson (MultiplyBlocks.guardContinuation layout).toNat),
    ("guard", toJson (MultiplyBlocks.guardPC layout).toNat),
    ("body_continuation", toJson (MultiplyBlocks.bodyContinuation layout).toNat),
    ("body", toJson (MultiplyBlocks.bodyPC layout).toNat),
    ("exit_continuation", toJson (MultiplyBlocks.exitContinuation layout).toNat),
    ("exit", toJson (MultiplyBlocks.exitPC layout).toNat),
    ("end", toJson (MultiplyBlocks.endPC layout).toNat),
    ("delta", toJson (MultiplyBlocks.delta layout).toNat),
    ("back_delta", toJson (MultiplyBlocks.backDelta layout).toNat)]).compress
