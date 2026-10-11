module
public import SmcTuring.Appendix.Listing8MainInputFrames
public import SmcTuring.Appendix.Listing8GraphMainFrames

public section
namespace SmcTuring.Appendix.Listing8MainInputMacroWindows
open Native Listing8CopyImage Listing8MainInput
@[expose] def params (mode : Mode) (l : Layout) (second : Bool) := Listing8GraphMainFrames.params mode l second

theorem header (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (second : Bool) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory (params mode l second).start (StringCodec.fieldOffset mode)=
      StringInit.leading mode (params mode l second).start := by
  have bounds:=Listing8GraphMainFrames.header_bounds mode l b.input.prefixBounds.fields.cursorLabel second
  have lower : l.start≤(params mode l second).start := by
    cases second
    · exact Nat.le_refl _
    · exact endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
  have kept:=Listing8MainInputFrames.before_patch mode l t v old b state entry forward current _ _ lower
    (Nat.le_trans bounds.1 (by omega)) bounds.2.1
  dsimp only [params] at kept ⊢
  rw [kept]
  cases second
  · exact current.prefixCurrent.copying.nodeMacro.header
  · exact current.prefixCurrent.copying.ruleMacro.header

theorem tail (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) (second : Bool) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory ((params mode l second).start+StringCodec.initialSize mode)
      (StringMacroSource.tailBytes mode (params mode l second)).length=StringMacroSource.tailBytes mode (params mode l second) := by
  have bounds:=Listing8GraphMainFrames.tail_bounds mode l b.input.prefixBounds.fields.cursorLabel second
  have lower : l.start≤(params mode l second).start+StringCodec.initialSize mode := by
    have first:=endpoint_lower mode l.start (Listing8Prototypes.nodeSpan mode)
    cases second <;> simp only [params,Listing8GraphMainFrames.params,nodeParams,transitionParams,Bool.false_eq_true,ite_false,ite_true]
    · omega
    · change l.start≤secondStart mode l+StringCodec.initialSize mode
      change l.start≤secondStart mode l at first
      omega
  have kept:=Listing8MainInputFrames.before_patch mode l t v old b state entry forward current _ _ lower
    (Nat.le_trans bounds.1 (by omega)) bounds.2.1
  dsimp only [params] at kept ⊢
  rw [kept]
  cases second
  · exact current.prefixCurrent.copying.nodeMacro.tail
  · exact current.prefixCurrent.copying.ruleMacro.tail

/-- The full current head-copy macro is recovered after the arbitrary input
phase from preserved headers/suffix and the retained actual head operand. -/
theorem node_current (mode : Mode) (l : Layout) (t : Targets) (v : Values mode) (old : OldInput) (b : Bounds mode l t v)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Current mode l t v old state.principal.memory) :
    ByteMemory.bytesAt (finish mode l t v state).principal.memory l.start
      (StringMacroLayout.bytes mode (nodeParams mode l)).length=StringMacroLayout.bytes mode (nodeParams mode l) := by
  apply StringMacroSource.current mode (nodeParams mode l)
  · exact header mode l t v old b state entry forward current false
  · exact tail mode l t v old b state entry forward current false
  · have actual:=Listing8MainInputFrames.head_cursor mode l t v old b state entry forward current
    rw [b.input.prefixBounds.fields.cursorLabel,b.input.prefixBounds.fields.headLabel] at actual
    exact actual

end SmcTuring.Appendix.Listing8MainInputMacroWindows
