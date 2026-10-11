module
public import SmcTuring.Appendix.Listing8FullTableReset

public section
namespace SmcTuring.Appendix.Listing8FullTableResetValues
open Native Listing8CopyImage Listing8FullTableReset
abbrev Targets:=Listing8PointerCopies.Targets

theorem failure_condition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    failed mode origin l t v sentinel table memory seed=
      decide ((if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel) :=
  Listing8BootControl.failure_condition mode origin l t v sentinel r owners copies body _ seed

theorem input_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel table memory seed).principal.memory l.input.cursor=
      Arithmetic.encodeNat mode sentinel := by
  have input:=Listing8InputBounds.positions mode l t body.state.head.input.fields body.state.head.input.joined
  have second:=(Listing8Initializer.code_geometry mode l).1
  have apart : l.input.cursor+mode.wordBytes≤(Listing8StateGeometry.region mode l).cursor := by
    change l.input.cursor+mode.wordBytes≤StringCodec.sourceField mode (secondStart mode l)
    rw [input.2.2,second]
    cases mode <;> dsimp [StringCodec.sourceField,StringCodec.fieldOffset,Mode.wordBytes] <;> omega
  rw [effect mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,
    MixedFrames.word_after_word mode _ _ _ _ (Or.inr apart),MixedMemory.get_put]

theorem transition_cursor (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel table memory seed).principal.memory
      (Listing8StateGeometry.region mode l).cursor=Arithmetic.encodeNat mode (Listing8FullTableImage.start mode origin) := by
  rw [effect mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,MixedMemory.get_put]

theorem registers (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel table memory seed).principal.stack=seed.principal.stack ∧
    (finish mode origin l t v sentinel table memory seed).principal.carry=false ∧
    (finish mode origin l t v sentinel table memory seed).sourceIndex=seed.sourceIndex ∧
    (finish mode origin l t v sentinel table memory seed).destinationIndex=seed.destinationIndex ∧
    (finish mode origin l t v sentinel table memory seed).backwards=false := by
  have prior:=Listing8FullTable.result mode origin l t v sentinel table index selected located r owners copies boot body bounds.declarations
    (Listing8TableResetImage.backing mode origin l sentinel table memory) seed
  rw [effect mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed]
  exact ⟨prior.2.2.1,prior.2.2.2.1,prior.2.2.2.2.1,prior.2.2.2.2.2.1,prior.2.2.2.2.2.2⟩

theorem terminal_boundary (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (table : List (Values mode)) (index : Nat) (selected : Listing8TransitionTable.Selected mode table index v)
    (located : l.sourceTransition=Listing8TransitionTable.entryPC mode (Listing8FullTableImage.start mode origin) index)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v)
    (copies : Listing8PointerCopies.Bounds mode l t) (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (bounds : Listing8TableResetImage.Bounds mode origin l sentinel table)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (finish mode origin l t v sentinel table memory seed).principal.pc.toNat=
      origin+(if mode=.x86 then 901 else 1399)+table.length*Listing8Prototypes.transitionSpan mode := by
  rw [effect mode origin l t v sentinel table index selected located r owners copies boot body bounds memory seed,
    Arithmetic.encode_nat_toNat mode _ bounds.reset.capacity,Listing8TableResetImage.endpoint_offset]
end SmcTuring.Appendix.Listing8FullTableResetValues
