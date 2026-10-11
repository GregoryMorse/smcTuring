module
public import SmcTuring.Appendix.Listing8LoopOriginalImage
public import SmcTuring.Native.AccumulatorFinalization

public section
namespace SmcTuring.Appendix.Listing8AccumulatorEntry
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

@[expose] def initial (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  let base:=Listing8GraphBackedge.initial mode origin l t g node rule memory seed
  {base with principal:={base.principal with pc:=Arithmetic.encodeNat mode a.prologue}}
@[expose] def saved (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (a : AccumulatorLayout.Layout)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  let first:=initial mode origin l t g node rule a memory seed
  {first with principal:=AccumulatorEffects.saved mode a first.principal}

theorem state_ext (mode : Mode) (first second : StringExecution.State mode)
    (principal : first.principal=second.principal) (source : first.sourceIndex=second.sourceIndex)
    (destination : first.destinationIndex=second.destinationIndex) (direction : first.backwards=second.backwards) : first=second := by
  cases first;cases second;simp_all

/-- The actual full-width entry store reaches exactly the original Listing 8
entry image with the saved accumulator in its later code operand. -/
theorem saved_eq (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (located : AccumulatorLayout.savedPC mode a=origin)
    (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤a.save)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    saved mode origin l t g node rule a memory seed=
      Listing8GraphBackedge.initial mode origin l t g node rule (ByteMemory.putWord mode memory a.save seed.principal.accumulator) seed := by
  apply state_ext
  · rw [saved,AccumulatorEffects.save_effect mode a valid _ rfl]
    apply AccumulatorEffects.state_ext
    · change Arithmetic.encodeNat mode (AccumulatorLayout.savedPC mode a)=Arithmetic.encodeNat mode origin
      rw [located]
    · rfl
    · rfl
    · rfl
    · change ByteMemory.putWord mode (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory a.save seed.principal.accumulator=
        (Listing8GraphBackedge.initial mode origin l t g node rule (ByteMemory.putWord mode memory a.save seed.principal.accumulator) seed).principal.memory
      rw [Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx memory seed,
        Listing8LoopOriginalImage.initial_memory mode origin l t g node rule ctx _ seed,
        Listing8LoopOriginalImage.image_put_word mode origin l t g node rule ctx memory seed a.save seed.principal.accumulator after]
  · rfl
  · rfl
  · rfl

/-- This is a present prologue packet observation. Its fetched form and actual
save effect are derived before invoking any interpreter/body theorem. -/
theorem trace (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (a : AccumulatorLayout.Layout) (valid : AccumulatorLayout.Admissible mode a)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode)
    (current : ByteMemory.bytesAt (initial mode origin l t g node rule a memory seed).principal.memory a.prologue
      (Native.encode mode (AccumulatorLayout.saveForm mode a)).length=Native.encode mode (AccumulatorLayout.saveForm mode a)) :
    StringStack.Trace mode (initial mode origin l t g node rule a memory seed)
      [StringStack.native mode (AccumulatorLayout.saveForm mode a)] (saved mode origin l t g node rule a memory seed) := by
  have fits : a.prologue<2^(8*mode.wordBytes) := by
    have cap:=valid.prologueFits;unfold AccumulatorLayout.savedPC at cap;omega
  have packet:=StringStack.native_encoding mode (AccumulatorLayout.saveForm mode a)
    (initial mode origin l t g node rule a memory seed).principal.memory a.prologue current
  have fetched : StringStack.fetch mode (initial mode origin l t g node rule a memory seed).principal.memory
      (initial mode origin l t g node rule a memory seed).principal.pc.toNat=some (StringStack.native mode (AccumulatorLayout.saveForm mode a)) := by
    change StringStack.fetch mode _ (Arithmetic.encodeNat mode a.prologue).toNat=_
    rw [Arithmetic.encode_nat_toNat mode _ fits]
    exact packet
  refine .step fetched ?_
  rw [StringStack.native_execute]
  exact .nil _

end SmcTuring.Appendix.Listing8AccumulatorEntry
