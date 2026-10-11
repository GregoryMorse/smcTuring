module
public meta import SmcTuring.Appendix.ConstantCorrect
public meta import Lean
open Lean SmcTuring.Appendix

/-- An executable comparator of the proved compile-time emitter. This export
    evaluates data; it is not a substitute for the kernel correctness proof. -/
public meta def main (args : List String) : IO Unit := do
  let encode := fun op => match op with
    | ConstantWords.Instruction.selected (.store _ _) => Json.mkObj [("kind",toJson (0 : Nat)),("count",toJson (0 : Nat))]
    | .shiftLeft _ count => Json.mkObj [("kind",toJson (1 : Nat)),("count",toJson count)]
    | .selected (.exchange _) => Json.mkObj [("kind",toJson (2 : Nat)),("count",toJson (0 : Nat))]
    | .storeAcc _ => Json.mkObj [("kind",toJson (3 : Nat)),("count",toJson (0 : Nat))]
    | .selected (.addAcc _) => Json.mkObj [("kind",toJson (4 : Nat)),("count",toJson (0 : Nat))]
    | .addFrom _ _ => Json.mkObj [("kind",toJson (5 : Nat)),("count",toJson (0 : Nat))]
    | _ => Json.mkObj [("kind",toJson (99 : Nat))]
  let results := args.map fun arg =>
    let constant := arg.toNat!
    let value := BitVec.ofNat 32 constant
    let program := ConstantWords.program 0 1 value
    let packets := program.map fun op =>
      let packet := ConstantData.packet op
      let form := packet.initial
      let absolute : List Nat := match form with
        | .common (.common (.storeAcc _)) => [1]
        | .common (.common (.callRelative _)) => []
        | _ => [2]
      Json.mkObj [("bytes",toJson ((ConstantByteCode.encode form).map BitVec.toNat)),
        ("absolute_offsets",toJson absolute), ("owned_offsets",toJson packet.offsets)]
    let geometryEntries := (ConstantGeometry.whole 0 value 0 0x12345678).map fun entry =>
      let absolute : List Nat := match entry.packet.initial with
        | .common (.common (.storeAcc _)) => [1]
        | _ => [2]
      Json.mkObj [("pc",toJson entry.pc), ("bytes",toJson (entry.bytes.map BitVec.toNat)),
        ("absolute_offsets",toJson absolute), ("fields",toJson entry.fields)]
    Json.mkObj [("constant",toJson constant),
      ("geometry",Json.mkObj [("pure",toJson (ConstantGeometry.length value)),
        ("data",toJson (ConstantGeometry.data 0 value)), ("scratch",toJson (ConstantGeometry.scratch 0 value)),
        ("extent",toJson (ConstantGeometry.extent value)), ("entries",toJson geometryEntries)]),
      ("program",toJson (program.map encode)), ("packets",toJson packets),
      ("data_owner",toJson ((ConstantByteCode.encode (.common (.common (.immediate .store 0 0)))).map BitVec.toNat)),
      ("inactive_scratch_owner",toJson ((ConstantByteCode.encode (.common (.addImmediate 0 0x12345678))).map BitVec.toNat))]
  IO.println (toJson results).compress
