module
public import SmcTuring.Appendix.Listing8GraphRun
public import SmcTuring.Appendix.Listing8FullTableNodeFrames
public import SmcTuring.Appendix.Listing8LiveNodePacket

public section
namespace SmcTuring.Appendix.Listing8GraphInputContext
open Native Listing8CopyImage Listing8SourceGraph
/-- Only initial label bindings and static native placement/resources.
Current or future memory, packets, values, readiness and traces are not fields. -/
structure Context (mode : Mode) (origin : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) : Prop where
  nodeLocated : l.sourceNode=nodePC mode origin g node
  ruleLocated : l.sourceTransition=rulePC mode origin g rule
  resources : Resources mode l
  fields : Listing8GraphOwnerBounds.Fields mode l
  copies : Listing8PointerCopies.Bounds mode l t
  boot : Listing8BootImage.Bounds mode origin l
  body : Listing8FailureGeometry.Bounds mode l t (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  native : Listing8GraphPointers.Bounds mode origin g
theorem owners (mode : Mode) (origin : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8CopiedOwners.Bounds mode l (values mode origin g node rule) :=
  Listing8GraphOwnerBounds.bounds mode origin l g node rule ctx.boot.packed ctx.fields ctx.native
theorem reset_bounds (mode : Mode) (origin : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule) :
    Listing8TableResetImage.Bounds mode origin l (nodePC mode origin g g.halt) (table mode origin g) :=
  Listing8GraphTableBounds.reset_bounds mode origin g node l t _ ctx.nodeLocated ctx.boot ctx.body ctx.native
@[expose] def extra (mode : Mode) (origin : Nat) (l : Layout) (g : Graph) (memory : ByteMemory.Memory) :=
  Listing8GlobalBoot.extra mode origin (Listing8JumpImage.backing mode origin (Listing8FailImage.backing mode origin
    (Listing8FullTableImage.backing mode origin (table mode origin g)
      (Listing8TableResetImage.backing mode origin l (nodePC mode origin g g.halt) (table mode origin g)
        (Listing8GraphNodeImage.image mode origin g memory)))))
@[expose] def initialMemory (mode : Mode) (origin : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) :=
  Listing8FailureGlobalImage.memory mode l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (Listing8BootImage.beginPC mode origin) (extra mode origin l g memory)
@[expose] def bodyEnd (mode : Mode) (origin : Nat) (l : Layout) (t : Listing8PointerCopies.Targets)
    (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) (memory : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FullTableNodeFrames.bodyEnd mode origin l t (values mode origin g node rule) (nodePC mode origin g g.halt)
    (table mode origin g) (Listing8GraphNodeImage.image mode origin g memory) seed
end SmcTuring.Appendix.Listing8GraphInputContext
