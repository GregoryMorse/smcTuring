module
public import SmcTuring.Appendix.Listing8NodeTable

public section
namespace SmcTuring.Appendix.Listing8NodeTrace
open Native Listing8NodeBlock Listing8Prototypes Listing8NodeTable
@[expose] def program (mode : Mode) : Nat → List (Values mode) → List (StringDword.Form mode)
  | _,[] => []
  | start,v::table => Listing8NodeBlock.program mode start v++program mode (start+nodeSpan mode) table
@[expose] def finish (mode : Mode) : Nat → List (Values mode) → StringExecution.State mode → StringExecution.State mode
  | _,[],state => state
  | start,v::table,state => finish mode (start+nodeSpan mode) table (Listing8NodeBlock.finish mode start v state)

theorem result (mode : Mode) (start : Nat) (table : List (Values mode)) (valid : Valid mode start table)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Initial mode start table state.principal.memory) :
    (finish mode start table state).principal.pc=Arithmetic.encodeNat mode (endPC mode start table) ∧
    (finish mode start table state).principal.memory=state.principal.memory ∧
    (finish mode start table state).principal.stack=state.principal.stack ∧
    (finish mode start table state).principal.carry=state.principal.carry ∧
    (finish mode start table state).sourceIndex=state.sourceIndex ∧
    (finish mode start table state).destinationIndex=state.destinationIndex ∧
    (finish mode start table state).backwards=state.backwards := by
  induction table generalizing start state with
  | nil => exact ⟨by simpa only [finish,endPC,List.length_nil,Nat.zero_mul,Nat.add_zero] using entry,rfl,rfl,rfl,rfl,rfl,rfl⟩
  | cons v table ih =>
    have first:=Listing8NodeBlock.result mode start v valid.1 state entry (head_current mode start v table _ initial)
    have restImage : Initial mode (start+nodeSpan mode) table (Listing8NodeBlock.finish mode start v state).principal.memory := by
      rw [first.2.1]
      exact tail_current mode start v table _ initial
    have rest:=ih (start+nodeSpan mode) valid.2 _ first.1 restImage
    have address : endPC mode (start+nodeSpan mode) table=endPC mode start (v::table) := by
      simp only [endPC,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    rw [address] at rest
    exact ⟨rest.1,rest.2.1.trans first.2.1,rest.2.2.1.trans first.2.2.1,
      rest.2.2.2.1.trans first.2.2.2.1,rest.2.2.2.2.1.trans first.2.2.2.2.1,
      rest.2.2.2.2.2.1.trans first.2.2.2.2.2.1,rest.2.2.2.2.2.2.trans first.2.2.2.2.2.2⟩

/-- The complete finite table runs from its initial bytes. Each declaration
restores whole memory before the next declaration's current-byte fetch. -/
theorem trace (mode : Mode) (start : Nat) (table : List (Values mode)) (valid : Valid mode start table)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Initial mode start table state.principal.memory) :
    StringDword.Trace mode state (program mode start table) (finish mode start table state) := by
  induction table generalizing start state with
  | nil => exact .nil _
  | cons v table ih =>
    have packet:=head_current mode start v table _ initial
    have first:=Listing8NodeBlock.trace mode start v valid.1 state entry packet
    have actual:=Listing8NodeBlock.result mode start v valid.1 state entry packet
    have restImage : Initial mode (start+nodeSpan mode) table (Listing8NodeBlock.finish mode start v state).principal.memory := by
      rw [actual.2.1]
      exact tail_current mode start v table _ initial
    exact StringDword.trace_append mode first (ih (start+nodeSpan mode) valid.2 _ actual.1 restImage)

theorem instruction_count (mode : Mode) (start : Nat) (table : List (Values mode)) :
    (program mode start table).length=9*table.length := by
  induction table generalizing start with
  | nil => rfl
  | cons v table ih =>
    rw [program,List.length_append,Listing8NodeBlock.instruction_count,ih,List.length_cons,Nat.mul_add]
    omega

theorem reusable (mode : Mode) (start : Nat) (table : List (Values mode)) (valid : Valid mode start table)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start)
    (initial : Initial mode start table state.principal.memory) :
    Initial mode start table (finish mode start table state).principal.memory := by
  rw [(result mode start table valid state entry initial).2.1]
  exact initial
end SmcTuring.Appendix.Listing8NodeTrace
