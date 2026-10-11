module
public import SmcTuring.Appendix.BranchExecution
public import SmcTuring.Appendix.ByteProgram

public section

namespace SmcTuring.Appendix.BranchLayout

open ByteImage
abbrev Word := BitVec 32
abbrev Relation := BranchAlgebra.Relation

@[expose] def gtFlag : Relation → Bool
  | .eq | .ne => false
  | _ => true
@[expose] def notFlag : Relation → Bool
  | .le | .eq | .ge => false
  | _ => true

/-- Bytes before the final AND/XOR pair, including the delta-setting MOV.
All instruction lengths are the literal selected codec lengths. -/
@[expose] def leading (signed : Bool) (relation : Relation) : Nat :=
  61 + (if signed then 40 else 0) + (if gtFlag relation then 0 else 12) + (if notFlag relation then 0 else 6)
@[expose] def prefixStart (base : Nat) : Nat := base + 10
@[expose] def andPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := prefixStart base + leading signed relation
@[expose] def xorPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := andPC base signed relation + 10
@[expose] def prefixEnd (base : Nat) (signed : Bool) (relation : Relation) : Nat := andPC base signed relation + 20
@[expose] def callPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := prefixEnd base signed relation + 6
@[expose] def fallPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := callPC base signed relation + 5
@[expose] def takenPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := fallPC base signed relation + 30
@[expose] def xPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := takenPC base signed relation + 30
@[expose] def yPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := xPC base signed relation + 10
@[expose] def endPC (base : Nat) (signed : Bool) (relation : Relation) : Nat := yPC base signed relation + 10

/-- Real own operands: AND +6 is Delta; XOR +6 is Mask; CALL +1 is Displacement.
The two input words are +6 of distinct inactive self-writing MOV owners. -/
@[expose] def fields (base : Nat) (signed : Bool) (relation : Relation) : Branching.Fields :=
  { x := xPC base signed relation + 6
    y := yPC base signed relation + 6
    mask := xorPC base signed relation + 6
    delta := andPC base signed relation + 6
    displacement := callPC base signed relation + 1 }

@[expose] def delta (base : Nat) (signed : Bool) (relation : Relation) : Word :=
  FieldRefinement.address (takenPC base signed relation) - FieldRefinement.address (fallPC base signed relation)
@[expose] def program (base : Nat) (signed : Bool) (relation : Relation) : List Machine32.Instruction :=
  Branching.relationProgram (fields base signed relation) signed relation (delta base signed relation)

@[expose] def stack (base : Nat) : Packet :=
  .both .store (FieldRefinement.address (base + 6)) (FieldRefinement.address (base + 6))
@[expose] def tail (base : Nat) : List Packet :=
  [.fixed (.memory .exchangeStack (FieldRefinement.address (base + 6))), .relative 0]
@[expose] def continuation (base : Nat) : List Packet :=
  [.fixed (.memory .exchangeStack (FieldRefinement.address (base + 6))),
   .fixed (.memory .addFour (FieldRefinement.address (base + 6))),
   .fixed (.memory .exchangeAcc (FieldRefinement.address (base + 6))),
   .fixed (.storeAcc (FieldRefinement.address (base + 2))),
   .fixed (.memory .exchangeAcc (FieldRefinement.address (base + 6)))]
@[expose] def storage (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) : List Packet :=
  [.immediate .store (FieldRefinement.address (fields base signed relation).x) x,
   .immediate .store (FieldRefinement.address (fields base signed relation).y) y]

/-- A literal reference image: one DEFSTACK owner, the predicate/patch prefix,
single XCHG/CALL, both five-instruction continuations, and two inactive data
owners. No host observations or hidden padding lie in any pure packet. The
finite trace stops at the declared continuation boundary; this is not source halt. -/
@[expose] def packets (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) : List Packet :=
  [stack base] ++ (program base signed relation).map ByteProgram.packet ++ tail base ++
    continuation base ++ continuation base ++ storage base signed relation x y
@[expose] def entries (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) : List Entry :=
  BytePacking.place base (packets base signed relation x y)
@[expose] def ownedFields (base : Nat) (signed : Bool) (relation : Relation) : List Nat :=
  [base + 2, base + 6, (fields base signed relation).delta, (fields base signed relation).mask,
    (fields base signed relation).displacement, (fields base signed relation).x, (fields base signed relation).y]

theorem span (layout : Branching.Fields) (signed : Bool) (relation : Relation) (value : Word) :
    ByteProgram.span (Branching.relationProgram layout signed relation value) = leading signed relation + 20 := by
  cases signed <;> cases relation <;>
    simp [ByteProgram.span, BytePacking.size, Branching.relationProgram, Branching.program,
      Branching.comparison, ByteProgram.packet, Packet.initial, ByteCode.encode_length,
      ByteCode.instructionLength, ByteCode.MemoryOp.trailer, leading, gtFlag, notFlag]

theorem tail_size (base : Nat) : BytePacking.size (tail base) = 11 := by
  simp [tail, BytePacking.size, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength, ByteCode.MemoryOp.trailer]

theorem continuation_size (base : Nat) : BytePacking.size (continuation base) = 30 := by
  simp [continuation, BytePacking.size, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength, ByteCode.MemoryOp.trailer]

theorem image_end (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    base + BytePacking.size (packets base signed relation x y) = endPC base signed relation := by
  have bodySize : BytePacking.size ((program base signed relation).map ByteProgram.packet) = leading signed relation + 20 :=
    span _ _ _ _
  have stackSize : BytePacking.size [stack base] = 10 := by
    simp [BytePacking.size, stack, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]
  have storageSize : BytePacking.size (storage base signed relation x y) = 20 := by
    simp [BytePacking.size, storage, Packet.initial, ByteCode.encode_length, ByteCode.instructionLength]
  simp only [packets, BytePacking.size_append, bodySize, stackSize, tail_size, continuation_size, storageSize]
  simp only [endPC, yPC, xPC, takenPC, fallPC, callPC, prefixEnd, andPC, prefixStart, Nat.add_assoc]

theorem linked (base : Nat) (signed : Bool) (relation : Relation) :
    ByteProgram.Linked (prefixStart base) (program base signed relation) := by
  cases signed <;> cases relation <;>
    simp [program, Branching.relationProgram, Branching.program, Branching.comparison,
      ByteProgram.Linked, ByteProgram.OwnOperand, ByteProgram.bytes, ByteProgram.packet,
      Packet.initial, ByteCode.encode_length, ByteCode.instructionLength, ByteCode.MemoryOp.trailer,
      fields, andPC, xorPC, callPC, prefixEnd, prefixStart, leading, gtFlag, notFlag,
      Branching.swapFields]

/-- Every writable code field is derived from the placed owner packets. -/
theorem image_fields (base : Nat) (signed : Bool) (relation : Relation) (x y : Word) :
    BytePacking.fields (entries base signed relation x y) = ownedFields base signed relation := by
  cases signed <;> cases relation <;>
    simp [entries, packets, program, Branching.relationProgram, Branching.program, Branching.comparison,
      BytePacking.place, BytePacking.fields, ByteProgram.packet, Packet.initial,
      Entry.fields, Packet.offsets, ByteCode.encode_length, ByteCode.instructionLength, ByteCode.MemoryOp.trailer,
      stack, tail, continuation, storage, ownedFields, fields, Branching.swapFields,
      andPC, xorPC, callPC, prefixEnd, prefixStart, leading, gtFlag, notFlag, xPC, yPC, takenPC, fallPC,
      Nat.add_assoc]

theorem separate_fields (base : Nat) (signed : Bool) (relation : Relation) :
    Branching.Separate (fields base signed relation) := by
  constructor <;> simp only [fields, xPC, yPC, takenPC, fallPC, callPC, prefixEnd, xorPC] <;> omega

theorem fields_owned (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (field : Nat) (member : field ∈ BranchExecution.fields (fields base signed relation)) :
    Owned (entries base signed relation x y) field := by
  apply (BytePacking.fields_owned _ field).mp
  rw [image_fields]
  simp only [BranchExecution.fields, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [ownedFields, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Word capacity and physical field separation follow from actual ownership
and a single complete image-extent bound. -/
theorem field_layout (base : Nat) (signed : Bool) (relation : Relation) (x y : Word)
    (capacity : endPC base signed relation ≤ 2 ^ 32) :
    FieldRefinement.Layout (BranchExecution.fields (fields base signed relation)) := by
  have full := BytePacking.placed_field_layout (packets base signed relation x y) base
    ((image_end base signed relation x y).trans_le capacity)
  constructor
  · intro field member
    exact full.fits field ((BytePacking.fields_owned _ field).mpr (fields_owned base signed relation x y field member))
  · intro first firstMember second secondMember different
    exact full.separate first ((BytePacking.fields_owned _ first).mpr (fields_owned base signed relation x y first firstMember))
      second ((BytePacking.fields_owned _ second).mpr (fields_owned base signed relation x y second secondMember)) different

end SmcTuring.Appendix.BranchLayout
