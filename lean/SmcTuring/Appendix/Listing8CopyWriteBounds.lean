module
public import SmcTuring.Appendix.Listing8CopyTrace
public import SmcTuring.Appendix.Listing8MacroWriteBounds

public section
namespace SmcTuring.Appendix.Listing8CopyWriteBounds
open Native Listing8CopyImage Listing8Prototypes

structure Placement (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) : Prop where
  block : codeStart≤l.start ∧ Listing8CopyImage.codeEnd mode l≤codeEnd
  node : codeStart≤l.sourceNode ∧ l.sourceNode+nodeSpan mode≤codeEnd
  transition : codeStart≤l.sourceTransition ∧ l.sourceTransition+transitionSpan mode≤codeEnd

theorem spans (mode : Mode) : mode.wordBytes≤nodeSpan mode ∧ mode.wordBytes≤transitionSpan mode := by
  cases mode <;> decide

theorem node (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (placed : Placement mode codeStart codeEnd l) :
    Listing8MacroWriteBounds.Placement mode codeStart codeEnd (nodeParams mode l) := by
  have coords:=coordinates mode l
  have dest:=destinations mode l
  have size:=(spans mode).1
  have block:=placed.block
  have source:=placed.node
  constructor
  · change codeStart≤l.start ∧ secondStart mode l≤codeEnd
    exact ⟨block.1,by omega⟩
  · change codeStart≤l.sourceNode ∧ l.sourceNode+max (nodeSpan mode) mode.wordBytes≤codeEnd
    rw [Nat.max_eq_left size];exact source
  · change codeStart≤(nodeParams mode l).destination ∧ (nodeParams mode l).destination+max (nodeSpan mode) mode.wordBytes≤codeEnd
    rw [Nat.max_eq_left size]
    exact ⟨Nat.le_trans block.1 dest.1,by omega⟩

theorem transition (mode : Mode) (codeStart codeEnd : Nat) (l : Layout) (placed : Placement mode codeStart codeEnd l) :
    Listing8MacroWriteBounds.Placement mode codeStart codeEnd (transitionParams mode l) := by
  have coords:=coordinates mode l
  have dest:=destinations mode l
  have size:=(spans mode).2
  have block:=placed.block
  have source:=placed.transition
  have lower:=endpoint_lower mode l.start (nodeSpan mode)
  change l.start≤secondStart mode l at lower
  constructor
  · change codeStart≤secondStart mode l ∧ patchStart mode l≤codeEnd
    exact ⟨Nat.le_trans block.1 lower,by omega⟩
  · change codeStart≤l.sourceTransition ∧ l.sourceTransition+max (transitionSpan mode) mode.wordBytes≤codeEnd
    rw [Nat.max_eq_left size];exact source
  · change codeStart≤(transitionParams mode l).destination ∧ (transitionParams mode l).destination+max (transitionSpan mode) mode.wordBytes≤codeEnd
    rw [Nat.max_eq_left size]
    exact ⟨by omega,by omega⟩

end SmcTuring.Appendix.Listing8CopyWriteBounds
