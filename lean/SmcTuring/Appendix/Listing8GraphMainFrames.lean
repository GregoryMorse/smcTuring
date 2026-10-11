module
public import SmcTuring.Appendix.Listing8MainState
public import SmcTuring.Appendix.Listing8GraphCopyResources
public import SmcTuring.Native.StringMacroSource

public section
namespace SmcTuring.Appendix.Listing8GraphMainFrames
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext Listing8GraphBackedge
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def params (mode : Mode) (l : Layout) (second : Bool) :=
  if second then transitionParams mode l else nodeParams mode l

theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (before : observed+count≤patchStart mode l)
    (secondOutside : (Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor)
    (firstOutside : l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) :
    ByteMemory.bytesAt (finish mode origin l t g node rule memory seed).principal.memory observed count=
      ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) observed count := by
  have lower:=Listing8GraphCopyResources.input_before_node mode origin l t g node rule ctx node
  rw [←ctx.nodeLocated] at lower
  have main:=code_to_input mode l ctx.resources
  have patch:=(coordinates mode l).2.2
  rw [effect mode origin l t g node rule ctx memory seed]
  exact Listing8MainState.failure mode l t (values mode origin g node rule) _ _ ctx.resources
    (owners mode origin l t g node rule ctx) ctx.copies ctx.body (extra mode origin l g memory)
    (Listing8GlobalBoot.bodySeed mode origin seed) observed count (by omega) secondOutside firstOutside (Or.inr (by omega))
theorem initially_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (second : Bool) :
    ByteMemory.bytesAt (initialMemory mode origin l t g node rule memory) (params mode l second).start
      (StringMacroLayout.bytes mode (params mode l second)).length=StringMacroLayout.bytes mode (params mode l second) := by
  cases second with
  | false => exact initial_node_macro mode l (values mode origin g node rule) ctx.resources _
  | true => exact initial_transition_macro mode l (values mode origin g node rule) ctx.resources _
theorem header_bounds (mode : Mode) (l : Layout) (firstCursor : l.input.cursor=StringCodec.sourceField mode l.start) (second : Bool) :
    let observed:=(params mode l second).start
    let count:=StringCodec.fieldOffset mode
    observed+count≤patchStart mode l ∧
    ((Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor) ∧
    (l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) := by
  have positions:=Listing8Initializer.code_geometry mode l
  rw [firstCursor]
  cases mode <;> cases second <;>
    simp only [params,reduceCtorEq,Bool.false_eq_true,ite_false,ite_true,nodeParams,transitionParams,
      StringCodec.fieldOffset,StringCodec.sourceField,Listing8StateGeometry.region,Mode.wordBytes] at positions ⊢ <;>
    simp only [StringCodec.sourceField,StringCodec.fieldOffset] at * <;> omega
theorem tail_bounds (mode : Mode) (l : Layout) (firstCursor : l.input.cursor=StringCodec.sourceField mode l.start) (second : Bool) :
    let p:=params mode l second
    let observed:=p.start+StringCodec.initialSize mode
    let count:=(StringMacroSource.tailBytes mode p).length
    observed+count≤patchStart mode l ∧
    ((Listing8StateGeometry.region mode l).cursor+mode.wordBytes≤observed ∨ observed+count≤(Listing8StateGeometry.region mode l).cursor) ∧
    (l.input.cursor+mode.wordBytes≤observed ∨ observed+count≤l.input.cursor) := by
  have positions:=Listing8Initializer.code_geometry mode l
  have ending:=StringMacroSource.tail_length mode (params mode l second)
  have endPC : StringMacroLayout.endpoint mode (params mode l second)=if second then patchStart mode l else secondStart mode l := by
    cases second <;> rfl
  rw [endPC] at ending
  rw [firstCursor]
  cases mode <;> cases second <;>
    simp only [params,reduceCtorEq,Bool.false_eq_true,ite_false,ite_true,nodeParams,transitionParams,
      StringCodec.fieldOffset,StringCodec.sourceField,StringCodec.initialSize,Listing8StateGeometry.region,Mode.wordBytes] at positions ending ⊢ <;>
    simp only [StringCodec.sourceField,StringCodec.fieldOffset] at * <;> omega
theorem header (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (second : Bool) :
    ByteMemory.bytesAt (finish mode origin l t g node rule memory seed).principal.memory (params mode l second).start
      (StringCodec.fieldOffset mode)=StringInit.leading mode (params mode l second).start := by
  have bounds:=header_bounds mode l ctx.body.state.head.input.fields.cursorLabel second
  rw [window mode origin l t g node rule ctx memory seed _ _ bounds.1 bounds.2.1 bounds.2.2]
  exact (StringMacroSource.windows mode _ _ (initially_current mode origin l t g node rule ctx memory second)).1
theorem tail (mode : Mode) (origin : Nat) (l : Layout) (t : Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (memory : ByteMemory.Memory) (seed : StringExecution.State mode) (second : Bool) :
    ByteMemory.bytesAt (finish mode origin l t g node rule memory seed).principal.memory
      ((params mode l second).start+StringCodec.initialSize mode) (StringMacroSource.tailBytes mode (params mode l second)).length=
      StringMacroSource.tailBytes mode (params mode l second) := by
  have bounds:=tail_bounds mode l ctx.body.state.head.input.fields.cursorLabel second
  rw [window mode origin l t g node rule ctx memory seed _ _ bounds.1 bounds.2.1 bounds.2.2]
  exact (StringMacroSource.windows mode _ _ (initially_current mode origin l t g node rule ctx memory second)).2

end SmcTuring.Appendix.Listing8GraphMainFrames
