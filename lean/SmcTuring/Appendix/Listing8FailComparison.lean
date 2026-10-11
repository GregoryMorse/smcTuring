module
public import SmcTuring.Native.ControlPackets
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

public section
namespace SmcTuring.Appendix.Listing8FailComparison
open Native
structure Layout where
  start : Nat
  cursor : Nat
  source : Nat
  mask : Nat
@[expose] def offset (mode : Mode) (index : Fin 7) :=
  let w:=WordMemoryArithmetic.size mode
  match index.val with
  | 0 => 0 | 1 => w | 2 => 2*w | 3 => 3*w | 4 => 3*w+7 | 5 => 4*w+7 | _ => 5*w+7
@[expose] def target (l : Layout) (index : Fin 7) :=
  match index.val with | 0 | 6 => l.source | 3 => l.mask | _ => l.cursor
@[expose] def operation (index : Fin 7) : ControlPackets.Operation :=
  match index.val with
  | 0 | 6 => .word .exchange | 1 => .word .subtract | 2 | 4 => .negate
  | 3 => .dword (.sbbZero 0) | _ => .word .add
@[expose] def site (mode : Mode) (l : Layout) (index : Fin 7) : ControlPackets.Site :=
  ⟨l.start+offset mode index,target l index,operation index⟩
@[expose] def sites (mode : Mode) (l : Layout) :=
  [site mode l 0,site mode l 1,site mode l 2,site mode l 3,site mode l 4,site mode l 5,site mode l 6]
@[expose] def endPC (mode : Mode) (l : Layout) := l.start+6*WordMemoryArithmetic.size mode+7
@[expose] def bytes (mode : Mode) (l : Layout) := ControlPackets.wholeBytes mode (sites mode l)
@[expose] def program (mode : Mode) (l : Layout) := ControlPackets.program mode (sites mode l)
@[expose] def finish (mode : Mode) (l : Layout) (state : StringExecution.State mode) := ControlPackets.finish mode (sites mode l) state
structure Bounds (mode : Mode) (l : Layout) : Prop where
  capacity : endPC mode l < 2^(8*mode.wordBytes)
  cursorBeforeSource : l.cursor+mode.wordBytes ≤ l.source
  sourceBefore : l.source+mode.wordBytes ≤ l.start
  cursorNear : l.start ≤ l.cursor+2048
  sourceNear : l.start ≤ l.source+2048
  maskAfter : endPC mode l ≤ l.mask
  maskFits : l.mask+4 ≤ 2^(8*mode.wordBytes)
  maskNear : l.mask ≤ l.start+2048

theorem span (mode : Mode) (l : Layout) :
    ControlPackets.span mode (sites mode l) = if mode=.x86 then 43 else 49 := by
  cases mode <;> rfl

theorem bytes_length (mode : Mode) (l : Layout) : (bytes mode l).length = if mode=.x86 then 43 else 49 := by
  cases mode <;> rfl

theorem chain (mode : Mode) (l : Layout) : ControlPackets.Contiguous mode l.start (sites mode l) := by
  cases mode <;> simp [sites,site,offset,operation,ControlPackets.Contiguous,ControlPackets.size,
    WordMemoryArithmetic.size,WordNegation.length,wordPrefix,DwordArithmetic.length,Nat.add_assoc]

theorem valid (mode : Mode) (l : Layout) (bounds : Bounds mode l) :
    ∀ reader ∈ sites mode l,ControlPackets.Valid mode reader := by
  intro reader member
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals have capacity:=bounds.capacity
  all_goals have cursorBefore:=bounds.cursorBeforeSource
  all_goals have sourceBefore:=bounds.sourceBefore
  all_goals have maskAfter:=bounds.maskAfter
  all_goals have maskFits:=bounds.maskFits
  all_goals have cursorNear:=bounds.cursorNear
  all_goals have sourceNear:=bounds.sourceNear
  all_goals have maskNear:=bounds.maskNear
  all_goals cases mode
  all_goals constructor
  all_goals simp [site,offset,target,operation,ControlPackets.size,ControlPackets.width,
    WordMemoryArithmetic.size,WordNegation.length,wordPrefix,DwordArithmetic.length,DwordArithmetic.direct,
    endPC,Mode.wordBytes,Relocation.SignedDelta,Relocation.delta] at capacity cursorBefore sourceBefore maskAfter maskFits cursorNear sourceNear maskNear ⊢
  all_goals omega

theorem code_separation (mode : Mode) (l : Layout) (bounds : Bounds mode l) :
    ControlPackets.OutsideCodes mode (sites mode l) := by
  intro writer wm reader rm
  have cb:=bounds.cursorBeforeSource
  have sb:=bounds.sourceBefore
  have ma:=bounds.maskAfter
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at wm rm
  rcases wm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases rm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases mode
  all_goals simp [site,offset,target,operation,ControlPackets.size,ControlPackets.width,
    WordMemoryArithmetic.size,WordNegation.length,wordPrefix,DwordArithmetic.length,endPC,Mode.wordBytes] at cb sb ma ⊢ <;> omega

/-- The printed USEWORD exchanges and full-width preserving COMPARE consume
only the initial complete body image. All seven current fetches are derived. -/
theorem trace (mode : Mode) (l : Layout) (bounds : Bounds mode l) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode l.start)
    (current : ByteMemory.bytesAt state.principal.memory l.start (bytes mode l).length = bytes mode l) :
    StringControl.Trace mode state (program mode l) (finish mode l state) :=
  ControlPackets.trace mode (sites mode l) l.start (chain mode l) (valid mode l bounds) (code_separation mode l bounds)
    state entry (ControlPackets.initial_packets mode (sites mode l) l.start (chain mode l) _ current)

theorem endpoint (mode : Mode) (l : Layout) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode l.start) :
    (finish mode l state).principal.pc = Arithmetic.encodeNat mode (endPC mode l) := by
  have pc:=ControlPackets.endpoint mode (sites mode l) l.start (chain mode l) state entry
  rw [span] at pc
  cases mode <;> exact pc

theorem instruction_count (mode : Mode) (l : Layout) : (program mode l).length=7 := by
  rfl

theorem registers (mode : Mode) (l : Layout) (state : StringExecution.State mode) :
    (finish mode l state).principal.stack=state.principal.stack ∧
    (finish mode l state).sourceIndex=state.sourceIndex ∧
    (finish mode l state).destinationIndex=state.destinationIndex ∧
    (finish mode l state).backwards=state.backwards := ControlPackets.registers mode (sites mode l) state

end SmcTuring.Appendix.Listing8FailComparison
