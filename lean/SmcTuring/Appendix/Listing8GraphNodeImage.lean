module
public import SmcTuring.Appendix.Listing8NodeTrace
public import SmcTuring.Appendix.Listing8GraphPointers

public section
namespace SmcTuring.Appendix.Listing8GraphNodeImage
open Native Listing8Prototypes Listing8SourceGraph
@[expose] def value (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes) : Listing8NodeBlock.Values mode :=
  ⟨(g.tape index).symbol,Arithmetic.encodeNat mode (nodePC mode origin g (g.tape index).back),
    Arithmetic.encodeNat mode (nodePC mode origin g (g.tape index).forward)⟩
@[expose] def declarations (mode : Mode) (origin : Nat) (g : Graph) := List.ofFn (value mode origin g)
@[expose] def image (mode : Mode) (origin : Nat) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8NodeTable.image mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g) memory

theorem length (mode : Mode) (origin : Nat) (g : Graph) : (declarations mode origin g).length=g.nodes := List.length_ofFn
theorem lookup (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes) :
    (declarations mode origin g)[index.val]?=some (value mode origin g index) := by
  simp only [declarations,List.getElem?_ofFn,index.isLt,dite_true]
theorem initial (mode : Mode) (origin : Nat) (g : Graph) (memory : ByteMemory.Memory) :
    Listing8NodeTable.Initial mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g)
      (image mode origin g memory) := Listing8NodeTable.initial_image mode _ _ memory
theorem current (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes) (memory : ByteMemory.Memory) :
    ByteMemory.bytesAt (image mode origin g memory) (nodePC mode origin g index) (nodeSpan mode)=
      Listing8NodeBlock.bytes mode (nodePC mode origin g index) (value mode origin g index) :=
  Listing8NodeTable.selected_current mode _ _ index.val _ (lookup mode origin g index) _ (initial mode origin g memory)
theorem fields (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes) (memory : ByteMemory.Memory) :
    DwordCode.get (image mode origin g memory) (nodePC mode origin g index+6)=(g.tape index).symbol ∧
    MixedMemory.getWord mode (image mode origin g memory) (pointerField mode (backEntry mode (nodePC mode origin g index)))=
      Arithmetic.encodeNat mode (nodePC mode origin g (g.tape index).back) ∧
    MixedMemory.getWord mode (image mode origin g memory) (pointerField mode (forwardEntry mode (nodePC mode origin g index)))=
      Arithmetic.encodeNat mode (nodePC mode origin g (g.tape index).forward) := by
  apply node_values
  rw [node_length]
  exact current mode origin g index memory

/-- Selecting a source node preserves its initialized graph bytes exactly. -/
theorem source_overlay (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (memory : ByteMemory.Memory) :
    ByteMemory.putBytes (image mode origin g memory) (nodePC mode origin g node)
      (nodeBytes mode (nodePC mode origin g node) (values mode origin g node rule).tape
        (values mode origin g node rule).back (values mode origin g node rule).forward)=image mode origin g memory :=
  Listing8NodeTable.selected_overlay mode _ _ node.val _ (lookup mode origin g node) _ (initial mode origin g memory)

theorem node_bounds (mode : Mode) (origin : Nat) (g : Graph) (index : Fin g.nodes)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8NodeBlock.Bounds mode (nodePC mode origin g index) (value mode origin g index) := by
  refine ⟨Listing8GraphLayout.node_capacity mode origin g.transitions g.nodes index.val bounds index.isLt,?_,?_⟩
  · simp only [value,Listing8GraphPointers.node_toNat mode origin g (g.tape index).back bounds,backEntry]
    exact Listing8GraphPointers.node_outside mode origin g index (g.tape index).back 10
      (by cases mode <;> decide) (by dsimp [nodeSpan];omega)
  · simp only [value,Listing8GraphPointers.node_toNat mode origin g (g.tape index).forward bounds,forwardEntry,backEntry]
    simpa only [Nat.add_assoc] using Listing8GraphPointers.node_outside mode origin g index (g.tape index).forward (10+pointerSpan mode)
      (by cases mode <;> decide) (by dsimp [nodeSpan];omega)

theorem valid_from_lookup (mode : Mode) (start : Nat) (items : List (Listing8NodeBlock.Values mode))
    (each : ∀ index value,items[index]?=some value →
      Listing8NodeBlock.Bounds mode (Listing8NodeTable.entryPC mode start index) value) :
    Listing8NodeTable.Valid mode start items := by
  induction items generalizing start with
  | nil => trivial
  | cons value items ih =>
    refine ⟨?_,?_⟩
    · simpa only [Listing8NodeTable.entryPC,Nat.zero_mul,Nat.add_zero] using each 0 value rfl
    · apply ih (start+nodeSpan mode)
      intro index item found
      have actual:=each (index+1) item (by simpa only [List.getElem?_cons_succ] using found)
      have address : Listing8NodeTable.entryPC mode start (index+1)=Listing8NodeTable.entryPC mode (start+nodeSpan mode) index := by
        dsimp [Listing8NodeTable.entryPC];rw [Nat.add_mul,Nat.one_mul];omega
      rw [address] at actual
      exact actual
theorem valid (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g) :
    Listing8NodeTable.Valid mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g) := by
  apply valid_from_lookup
  intro index item found
  have within : index<g.nodes := by
    have small:=List.getElem?_eq_some_iff.mp found |>.1
    rw [length] at small
    exact small
  have actual:=lookup mode origin g ⟨index,within⟩
  rw [found] at actual
  have same:=Option.some.inj actual
  subst item
  exact node_bounds mode origin g ⟨index,within⟩ bounds

theorem trace (mode : Mode) (origin : Nat) (g : Graph) (bounds : Listing8GraphPointers.Bounds mode origin g)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (entry : seed.principal.pc=Arithmetic.encodeNat mode (Listing8GraphLayout.input mode origin g.transitions)) :
    StringDword.Trace mode {seed with principal:={seed.principal with memory:=image mode origin g memory}}
      (Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g))
      (Listing8NodeTrace.finish mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g)
        {seed with principal:={seed.principal with memory:=image mode origin g memory}}) :=
  Listing8NodeTrace.trace mode _ _ (valid mode origin g bounds) _ entry (initial mode origin g memory)
theorem endpoint (mode : Mode) (origin : Nat) (g : Graph) :
    Listing8NodeTable.endPC mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g)=
      Listing8GraphLayout.endPC mode origin g.transitions g.nodes := by
  simp only [Listing8NodeTable.endPC,length];rfl
theorem instruction_count (mode : Mode) (origin : Nat) (g : Graph) :
    (Listing8NodeTrace.program mode (Listing8GraphLayout.input mode origin g.transitions) (declarations mode origin g)).length=9*g.nodes := by
  rw [Listing8NodeTrace.instruction_count,length]
end SmcTuring.Appendix.Listing8GraphNodeImage
