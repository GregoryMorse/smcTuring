module
public import SmcTuring.Appendix.Listing8LoopOriginalInterpreterTail

public section
namespace SmcTuring.Appendix.Listing8LoopOriginalImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets

/-- The one original entry image equals the body's previously derived memory
initializer; the bootstrap overlay is commuted by its proved static bounds. -/
theorem initial_memory (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8GraphBackedge.initial mode origin l t g node rule memory seed).principal.memory=
      initialMemory mode origin l t g node rule memory :=
  (Listing8BootImage.memory_put mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) ctx.resources ctx.boot ctx.body
    (Listing8JumpImage.backing mode origin (Listing8GraphBackedge.backing mode origin l g memory))).symm

theorem patch_point (first second : ByteMemory.Memory) (address : Nat) (bytes : List LittleEndian.Byte)
    (position : Nat) (same : first position=second position) :
    ByteMemory.putBytes first address bytes position=ByteMemory.putBytes second address bytes position := by
  simp only [ByteMemory.putBytes]
  split <;> first | rfl | exact same

/-- Initial emission uses fixed byte overlays only, so every unmodified byte
comes from the same position of the supplied backing memory. -/
theorem image_point (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (first second : ByteMemory.Memory) (position : Nat) (same : first position=second position) :
    initialMemory mode origin l t g node rule first position=initialMemory mode origin l t g node rule second position := by
  simp only [initialMemory,Listing8FailureGlobalImage.memory,Listing8StateImage.memory,Listing8DirectionImage.memory,
    Listing8CopyImage.image,Listing8PointerImage.backing,Listing8DirectionImage.backing,Listing8StateImage.backing,
    Listing8FailureGlobalImage.backing,extra,Listing8GlobalBoot.extra,Listing8JumpImage.backing,Listing8FailImage.backing,
    Listing8FullTableImage.backing,Listing8TransitionTable.image,Listing8TableResetImage.backing,Listing8GraphNodeImage.image,
    Listing8NodeTable.image]
  repeat apply patch_point
  exact same

theorem point_after (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (position : Nat)
    (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤position) :
    initialMemory mode origin l t g node rule memory position=memory position := by
  have equal:=congrArg (fun bytes : List LittleEndian.Byte => bytes.head?)
    (Listing8LoopOriginalTailFrames.initial_window mode origin l t g node rule ctx memory seed position 1 after)
  change some (initialMemory mode origin l t g node rule memory position)=some (memory position) at equal
  exact Option.some.inj equal

/-- Saving the original full accumulator to a reserved later operand field
commutes with the complete original code initializer. The equality is proved
from actual fixed emission and byte frames, rather than supplied as a premise. -/
theorem image_put_word (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (field : Nat) (value : Word mode)
    (after : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤field) :
    initialMemory mode origin l t g node rule (ByteMemory.putWord mode memory field value)=
      ByteMemory.putWord mode (initialMemory mode origin l t g node rule memory) field value := by
  funext position
  by_cases inside : ByteMemory.Inside field mode.wordBytes position
  · have later : Listing8GraphLayout.endPC mode origin g.transitions g.nodes≤position := by
      unfold ByteMemory.Inside at inside;omega
    rw [point_after mode origin l t g node rule ctx _ seed position later]
    simp only [ByteMemory.putWord,ByteMemory.putBytes,LittleEndian.word_encode_length,dite_eq_left inside]
  · change initialMemory mode origin l t g node rule (ByteMemory.putBytes memory field (LittleEndian.wordEncode mode.wordBytes value)) position=
      ByteMemory.putBytes (initialMemory mode origin l t g node rule memory) field (LittleEndian.wordEncode mode.wordBytes value) position
    rw [ByteMemory.put_frame (initialMemory mode origin l t g node rule memory) field (LittleEndian.wordEncode mode.wordBytes value) position (by simpa only [LittleEndian.word_encode_length] using inside)]
    apply image_point
    exact ByteMemory.put_frame memory field (LittleEndian.wordEncode mode.wordBytes value) position (by simpa only [LittleEndian.word_encode_length] using inside)

end SmcTuring.Appendix.Listing8LoopOriginalImage
