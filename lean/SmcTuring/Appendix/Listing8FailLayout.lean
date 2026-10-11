module
public import SmcTuring.Appendix.Listing8LateFrames
public import SmcTuring.Appendix.Listing8BeginReturn
public import SmcTuring.Appendix.Listing8JumpValues

public section
namespace SmcTuring.Appendix.Listing8FailLayout
open Native Listing8CopyImage Listing8Prototypes
@[expose] def endPC (mode : Mode) (origin : Nat) := Listing8JumpLayout.failPC mode origin+Listing4TargetLayout.size mode
@[expose] def bytes (mode : Mode) (origin : Nat) := Listing4TargetLayout.bytes mode origin (Listing8JumpLayout.failPC mode origin)
structure Bounds (mode : Mode) (origin : Nat) (l : Layout) (limit : Nat) : Prop where
  continuation : endPC mode origin ≤ limit
  capacity : limit<2^(8*mode.wordBytes)
  nodeOutside : l.sourceNode+nodeSpan mode ≤ origin ∨ limit ≤ l.sourceNode
  transitionOutside : l.sourceTransition+transitionSpan mode ≤ origin ∨ limit ≤ l.sourceTransition

theorem bytes_length (mode : Mode) (origin : Nat) : (bytes mode origin).length=Listing4TargetLayout.size mode :=
  Listing4TargetLayout.bytes_length mode origin (Listing8JumpLayout.failPC mode origin)
theorem end_offset (mode : Mode) (origin : Nat) : endPC mode origin=origin+(if mode=.x86 then 837 else 1310) := by
  rw [endPC,(Listing8JumpLayout.positions mode origin).2]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> dsimp [Listing4TargetLayout.size] <;> omega
theorem origin_before (mode : Mode) (origin : Nat) : origin ≤ Listing8JumpLayout.failPC mode origin := by
  rw [(Listing8JumpLayout.positions mode origin).2];omega
theorem placement (mode : Mode) (origin : Nat) : origin+Listing4StackLayout.size mode ≤ Listing8JumpLayout.failPC mode origin := by
  rw [(Listing8JumpLayout.positions mode origin).2]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> dsimp [Listing4StackLayout.size] <;> omega
theorem ranges (mode : Mode) (origin : Nat) : Listing4TargetLayout.Ranges mode origin (Listing8JumpLayout.failPC mode origin) := by
  constructor <;> intro only <;> subst mode
  all_goals dsimp [Listing8JumpLayout.failPC,Listing8JumpLayout.callPC,Listing8JumpLayout.jumpPC,
    Listing4JumpLayout.prefixSize,Listing4TargetLayout.thirdPC,Listing4TargetLayout.fourthPC,
    Listing4TargetLayout.fifthPC,Listing4TargetLayout.endPC,Listing4TargetLayout.adjustSize,WordAddImmediate.length,
    StackMemory.size,wordPrefix,Listing4StackLayout.stptr,Listing4StackLayout.returnField]
  all_goals unfold Relocation.SignedDelta Relocation.delta;omega
theorem capacity (mode : Mode) (origin : Nat) (l : Layout) (limit : Nat) (bounds : Bounds mode origin l limit) :
    Listing8JumpLayout.failPC mode origin+Listing4TargetLayout.size mode<2^(8*mode.wordBytes) :=
  Nat.lt_of_le_of_lt bounds.continuation bounds.capacity
theorem source_windows (mode : Mode) (origin : Nat) (l : Layout) (limit : Nat) (bounds : Bounds mode origin l limit)
    (observed count : Nat) (after : Listing8JumpLayout.failPC mode origin ≤ observed) (upper : observed+count ≤ limit) :
    (l.sourceNode+nodeSpan mode ≤ observed ∨ observed+count ≤ l.sourceNode) ∧
    (l.sourceTransition+transitionSpan mode ≤ observed ∨ observed+count ≤ l.sourceTransition) := by
  have lower:=origin_before mode origin
  constructor
  · rcases bounds.nodeOutside with early | late
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases bounds.transitionOutside with early | late
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
end SmcTuring.Appendix.Listing8FailLayout
