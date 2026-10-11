module
public meta import SmcTuring.Appendix.BranchPrefix
public meta import Lean

open Lean SmcTuring.Appendix

/-- Finite assembler comparator from the checked reference emitter definitions.
Evaluating this JSON is not a kernel proof or a hardware semantics theorem. -/
meta def branchRole (fields : Branching.Fields) (position : Nat) : String :=
  if position == fields.x then "x"
  else if position == fields.y then "y"
  else if position == fields.mask then "mask"
  else if position == fields.displacement then "displacement"
  else if position == fields.delta then "delta"
  else "invalid"

meta def branchPacket (fields : Branching.Fields) (instruction : Machine32.Instruction) : Json :=
  Json.mkObj [("bytes", toJson ((ByteCode.encode (ByteProgram.packet instruction).initial).map BitVec.toNat)),
    ("destination", toJson (branchRole fields (Machine32.destination instruction))),
    ("relocation_immediate", toJson (match instruction with
      | .store position _ => position == fields.delta
      | _ => false))]

meta def branchLayout (signed : Bool) (relation : BranchAlgebra.Relation) (name : String) : Json :=
  let fields := BranchLayout.fields 0 signed relation
  let start := BranchLayout.prefixStart 0
  let program := BranchLayout.program 0 signed relation
  Json.mkObj [("signed", toJson signed), ("relation", toJson name),
    ("prefix", toJson (program.map (branchPacket fields))),
    ("prefix_bytes", toJson (ByteProgram.span program)),
    ("and_offset", toJson (BranchLayout.andPC 0 signed relation - start)),
    ("xor_offset", toJson (BranchLayout.xorPC 0 signed relation - start)),
    ("call_offset", toJson (BranchLayout.callPC 0 signed relation - start)),
    ("fall_offset", toJson (BranchLayout.fallPC 0 signed relation - start)),
    ("field_offsets", Json.mkObj [("delta", toJson (fields.delta - start)),
      ("mask", toJson (fields.mask - start)), ("displacement", toJson (fields.displacement - start))]),
    ("tail_bytes", toJson (BytePacking.size (BranchLayout.tail 0))),
    ("continuation_bytes", toJson (BytePacking.size (BranchLayout.continuation 0)))]

meta def branchLayouts : List Json :=
  [false, true].flatMap fun signed =>
    [branchLayout signed .lt "lt", branchLayout signed .le "le", branchLayout signed .eq "eq",
     branchLayout signed .ne "ne", branchLayout signed .gt "gt", branchLayout signed .ge "ge"]

#eval IO.println (toJson branchLayouts).compress
