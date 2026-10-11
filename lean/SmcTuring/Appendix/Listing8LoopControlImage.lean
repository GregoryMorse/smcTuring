module
public import SmcTuring.Appendix.Listing8LoopGraphFailure
public import SmcTuring.Appendix.Listing8LoopEarlyFrames
public import SmcTuring.Appendix.Listing8LoopLateFrames
public import SmcTuring.Appendix.Listing8LoopCallImage
public import SmcTuring.Appendix.Listing8GraphNextFailImage

public section
namespace SmcTuring.Appendix.Listing8LoopControlImage
open Native Listing8CopyImage Listing8SourceGraph Listing8GraphInputContext
abbrev Targets:=Listing8PointerCopies.Targets
abbrev OldInput:=Listing8MainInput.OldInput
/-- All control fragments are observed in the same present main-entry memory.
Both target packets precede selection; no future target image is a field. -/
structure Current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (old : OldInput) (machine : StringExecution.State mode) : Prop where
  body : Listing8LoopGraphFailure.Current mode origin l t g node rule old machine
  entryImage : ByteMemory.bytesAt machine.principal.memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin
  prefixImage : ByteMemory.bytesAt machine.principal.memory (Listing8JumpLayout.jumpPC mode origin)
    (Listing8JumpLayout.prefixBytes mode origin).length=Listing8JumpLayout.prefixBytes mode origin
  callImage : ByteMemory.bytesAt machine.principal.memory (Listing8JumpLayout.callPC mode origin) 5=
    Native.encode mode (Listing8JumpLayout.call mode origin false)
  failImage : ByteMemory.bytesAt machine.principal.memory (Listing8JumpLayout.failPC mode origin)
    (Listing4TargetLayout.size mode)=Listing8FailLayout.bytes mode origin

theorem entry_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory origin (Listing4EntryLayout.size mode)=Listing4EntryLayout.bytes mode origin := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have codeBefore:=Listing8GraphOwnerBounds.code_before_table mode origin l ctx.boot.packed
  have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g node
  rw [←ctx.nodeLocated] at nodeAfter
  have main:=code_length mode l
  have before : origin+Listing4EntryLayout.size mode≤l.start := by rw [ctx.boot.packed];rfl
  rw [Listing8LoopEarlyFrames.failure mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state current.body.state.head.graph.entry current.body.state.head.graph.forward image origin (Listing4EntryLayout.size mode) before (Or.inr (by omega))]
  exact current.entryImage

theorem stack_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory origin (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode origin := by
  have known:=entry_packet mode origin l t g node rule ctx old state current
  have first:=ByteWindow.packet (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory origin [] (Listing4Boot.bytes mode origin)
    (Listing4TargetLayout.bytes mode origin (Listing4JumpLayout.beginPC mode origin)) (by
      simp only [List.nil_append]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact known)
  have code : ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory origin (Listing4Boot.size mode)=Listing4Boot.bytes mode origin := by
    simpa only [List.length_nil,Nat.add_zero,Listing4Boot.bytes_length] using first
  exact Listing4Boot.stack_packet mode origin _ code

theorem begin_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (Listing8BootImage.beginPC mode origin) (Listing4TargetLayout.size mode)=
      Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
  have known:=entry_packet mode origin l t g node rule ctx old state current
  have packet:=ByteWindow.packet (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory origin
    (Listing4Boot.bytes mode origin) (Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin)) [] (by
      simp only [List.append_nil]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact known)
  have typed : ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (origin+Listing4Boot.size mode) (Listing4TargetLayout.size mode)=
      Listing4TargetLayout.bytes mode origin (Listing8BootImage.beginPC mode origin) := by
    simpa only [Listing4Boot.bytes_length,Listing4TargetLayout.bytes_length] using packet
  rw [←Listing4Boot.endpoint] at typed
  exact typed

theorem prefix_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (Listing8JumpLayout.jumpPC mode origin) (Listing8JumpLayout.prefixBytes mode origin).length=
      Listing8JumpLayout.prefixBytes mode origin := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  let region:=Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)
  have endEq:=Listing8JumpImage.end_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.endPC mode region=Listing8JumpLayout.jumpPC mode origin at endEq
  have callEq:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode region=Listing8JumpLayout.callPC mode origin at callEq
  have coords:=Listing8FailureLayout.positions mode region
  have after : region.start≤Listing8JumpLayout.jumpPC mode origin := by rw [←endEq];omega
  have upper : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤Listing8FailureLayout.callPC mode region+5 := by
    rw [callEq,Listing8JumpLayout.prefix_length];dsimp [Listing8JumpLayout.callPC];omega
  have andBefore : Listing8FailureLayout.andPC mode region+10≤Listing8JumpLayout.jumpPC mode origin := by
    rw [←endEq];simp only [Listing8FailureLayout.endPC,Listing8FailureLayout.xorPC];omega
  have maskBefore : Listing8FailureLayout.mask mode region+4≤Listing8JumpLayout.jumpPC mode origin := by
    rw [←endEq];simp only [Listing8FailureLayout.mask,Listing8FailureLayout.endPC];omega
  have callAfter : Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤Listing8FailureLayout.callPC mode region := by
    rw [callEq,Listing8JumpLayout.prefix_length];rfl
  rw [Listing8LoopFailure.window mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state current.body.state.head.graph.entry current.body.state.head.graph.forward image _ _ (Or.inl andBefore) (Or.inl maskBefore) (Or.inr (by
      change Listing8JumpLayout.jumpPC mode origin+(Listing8JumpLayout.prefixBytes mode origin).length≤Listing8FailureLayout.callPC mode region+1
      omega)),
    Listing8LoopFailurePrefix.window mode l t _ old _ _ b state current.body.state.head.graph.entry current.body.state.head.graph.forward image _ _ after upper]
  exact current.prefixImage

theorem fail_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (Listing8JumpLayout.failPC mode origin) (Listing4TargetLayout.size mode)=Listing8FailLayout.bytes mode origin := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have callEq:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at callEq
  have after : Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))+5≤Listing8JumpLayout.failPC mode origin := by rw [callEq];rfl
  have tapeOutside : l.sourceNode+10≤Listing8JumpLayout.failPC mode origin ∨
      Listing8JumpLayout.failPC mode origin+Listing4TargetLayout.size mode≤l.sourceNode+6 := by
    right
    have nodeAfter:=Listing8GraphOwnerBounds.node_after_table mode origin g node
    rw [←ctx.nodeLocated] at nodeAfter
    change Listing8FullTableImage.start mode origin≤l.sourceNode+6
    omega
  rw [Listing8LoopLateFrames.failure_window mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state current.body.state.head.graph.entry current.body.state.head.graph.forward image _ _ after tapeOutside]
  exact current.failImage

theorem call_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (g : Graph)
    (node : Fin g.nodes) (rule : Fin g.transitions) (ctx : Context mode origin l t g node rule)
    (old : OldInput) (state : StringExecution.State mode) (current : Current mode origin l t g node rule old state) :
    ByteMemory.bytesAt (Listing8LoopFailure.finish mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state).principal.memory (Listing8JumpLayout.callPC mode origin) 5=
      Native.encode mode (Listing8JumpLayout.call mode origin (Listing8LoopFailure.failed mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) state)) := by
  have b:=Listing8LoopGraphFailure.bounds mode origin l t g node rule ctx
  have image:=Listing8LoopGraphFailure.input_current mode origin l t g node rule old state ctx.nodeLocated ctx.ruleLocated current.body
  have position:=Listing8JumpImage.call_position mode origin l t (nodePC mode origin g g.halt) ctx.boot ctx.body
  change Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))=Listing8JumpLayout.callPC mode origin at position
  have original : ByteMemory.bytesAt state.principal.memory (Listing8FailureLayout.callPC mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin))) 5=
      Native.encode mode (.callRelative (Listing8FailureLayout.original mode (Listing8FailureGeometry.region mode l (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin)))) := by
    rw [Listing8FailureLayout.original,position]
    exact current.callImage
  have packet:=Listing8LoopCallImage.call_packet mode l t (values mode origin g node rule) (nodePC mode origin g g.halt) (Listing8BootImage.beginPC mode origin) old b state current.body.state.head.graph.entry current.body.state.head.graph.forward image original
  rw [Listing8FailureLayout.original,position] at packet
  exact packet

end SmcTuring.Appendix.Listing8LoopControlImage
