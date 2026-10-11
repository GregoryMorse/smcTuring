module
public import SmcTuring.Appendix.Listing8MainCatalogTransport
public import SmcTuring.Appendix.Listing8GlobalControlRegions

public section
namespace SmcTuring.Appendix.Listing8ControlStoreFields
open Native Listing8CopyImage Listing8SourceGraph
abbrev Targets:=Listing8PointerCopies.Targets

theorem slot_bound (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (address count : Nat) (slots : Listing4StackTemplates.Slots mode origin address count) : address+count≤l.start := by
  have ordering:=Listing8GlobalControlLayout.ordered mode origin
  have main:=ctx.boot.packed
  rcases slots with stack | returned
  · cases mode <;> simp only [Listing4StackLayout.stptr,Listing4StackLayout.size,Mode.wordBytes] at stack ordering <;> omega
  · cases mode <;> simp only [Listing4StackLayout.returnField,Listing4StackLayout.size,Mode.wordBytes] at returned ordering <;> omega

theorem regions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Listing8JumpReturn.Current mode origin failed state.principal.memory) :
    StringStoreRegions.Run mode (Listing8MainCatalogTransport.Allowed mode origin l)
      (Listing8JumpReturn.program mode origin failed) state :=
  BoundedStoreRegions.monotone mode (Listing4StackTemplates.Slots mode origin) _ _ state
    (fun address count slots => Or.inl (slot_bound mode origin l t g node rule ctx address count slots))
    (Listing8JumpSlotRegions.complete mode origin failed state entry capacity current)

theorem all_states (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Listing8GraphInputContext.Context mode origin l t g node rule)
    (failed : Bool) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode (Listing8JumpLayout.jumpPC mode origin))
    (capacity : Listing8JumpLayout.failPC mode origin<2^(8*mode.wordBytes))
    (current : Listing8JumpReturn.Current mode origin failed state.principal.memory)
    (initial : Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) state.principal.memory) :
    StringTemplateStates.Run mode (fun reached => Listing8InputCatalogInitial.Property mode l (values mode origin g node rule) reached.principal.memory)
      (Listing8JumpReturn.program mode origin failed) state :=
  StringStoreTemplateRuns.preserve mode _ _ _ state initial (Listing8MainCatalogTransport.store mode origin l t g node rule ctx)
    (regions mode origin l t g node rule ctx failed state entry capacity current)

end SmcTuring.Appendix.Listing8ControlStoreFields
