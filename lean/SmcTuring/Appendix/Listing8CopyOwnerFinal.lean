module
public import SmcTuring.Appendix.Listing8CopyOwnerPrefixes

public section
namespace SmcTuring.Appendix.Listing8CopyOwnerFinal
open Native Listing8CopyImage Listing8Prototypes Listing8OwnerTemplateCollection Listing8CopyOwnerPrefixes

theorem subwindow (copied source : ByteMemory.Memory) (destination origin size offset count : Nat)
    (same : ByteMemory.bytesAt copied destination size=ByteMemory.bytesAt source origin size)
    (within : offset+count≤size) :
    ByteMemory.bytesAt copied (destination+offset) count=ByteMemory.bytesAt source (origin+offset) count := by
  have small : ByteMemory.bytesAt copied destination (offset+count)=ByteMemory.bytesAt source origin (offset+count) := by
    rw [←Fetch.bytes_at_take copied destination size (offset+count) within,same,
      Fetch.bytes_at_take source origin size (offset+count) within]
  have dropped := congrArg (List.drop offset) small
  simpa only [ByteWindow.drop] using dropped

theorem template (mode : Mode) (owner : Template mode) (copied source : ByteMemory.Memory)
    (destination origin size offset : Nat) (intact : Intact mode owner source)
    (located : start mode owner=origin+offset)
    (same : ByteMemory.bytesAt copied destination size=ByteMemory.bytesAt source origin size)
    (complete : offset+Listing8CopyTemplateWindows.header mode owner≤size) :
    Intact mode (Listing8CopyTemplateWindows.relocate mode owner (destination+offset)) copied ∧
    Decodes mode (Listing8CopyTemplateWindows.relocate mode owner (destination+offset)) copied := by
  have kept : Intact mode (Listing8CopyTemplateWindows.relocate mode owner (destination+offset)) copied := by
    cases owner with
    | pointer pointerOrigin pc =>
      change PayloadTemplate.Prefix copied (destination+offset) (Listing8PointerTemplate.fixed mode pointerOrigin)
      rw [PayloadTemplate.Prefix,subwindow copied source destination origin size offset]
      · rw [←located];exact intact
      · exact same
      · simpa only [Listing8PointerTemplate.fixed_length,Listing8CopyTemplateWindows.header] using complete
    | scalar pc d =>
      change PayloadTemplate.Prefix copied (destination+offset) (Listing8ScalarTemplate.fixed d)
      rw [PayloadTemplate.Prefix,subwindow copied source destination origin size offset]
      · rw [←located];exact intact
      · exact same
      · simpa only [Listing8ScalarTemplate.fixed_length,Listing8CopyTemplateWindows.header] using complete
  exact ⟨kept,decodes mode _ _ kept⟩

@[expose] def Final (mode : Mode) (p : StringMacroLayout.Params) (templates : List (Template mode)) (memory : ByteMemory.Memory) :=
  ∀ owner∈templates,
    Intact mode (Listing8CopyTemplateWindows.relocate mode owner (p.destination+(start mode owner-p.source))) memory ∧
    Decodes mode (Listing8CopyTemplateWindows.relocate mode owner (p.destination+(start mode owner-p.source))) memory

theorem all (mode : Mode) (p : StringMacroLayout.Params) (templates : List (Template mode))
    (copied source : ByteMemory.Memory) (intact : All mode templates source) (bounded : Bounded mode p templates)
    (same : ByteMemory.bytesAt copied p.destination p.size=ByteMemory.bytesAt source p.source p.size) :
    Final mode p templates copied := by
  intro owner member
  have position := bounded owner member
  have location : start mode owner=p.source+(start mode owner-p.source) := by omega
  have complete : start mode owner-p.source+Listing8CopyTemplateWindows.header mode owner≤p.size := by
    have head := (Listing8CopyTemplateWindows.header_bounds mode owner).1
    omega
  exact template mode owner copied source _ _ _ _ (intact owner member) location same complete

/-- Complete actual paired macros, including both cursor restorations, leave
all copied node templates executable at their original static boundaries. -/
theorem node (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    Final mode (nodeParams mode l) (nodeTemplates mode l v) (Listing8MainCopies.finish mode l state).principal.memory := by
  have copied := (Listing8MainCopies.copied_packets mode l v r state entry forward current).1
  have same : ByteMemory.bytesAt (Listing8MainCopies.finish mode l state).principal.memory (nodeParams mode l).destination
      (nodeSpan mode)=ByteMemory.bytesAt state.principal.memory l.sourceNode (nodeSpan mode) := by
    rw [current.node]
    simpa only [sourceNodeBytes,node_length] using copied
  exact all mode _ _ _ state.principal.memory (node_current mode l v _ current.node) (node_bounded mode l v) same

theorem transition (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    Final mode (transitionParams mode l) (transitionTemplates mode l v) (Listing8MainCopies.finish mode l state).principal.memory := by
  have copied := (Listing8MainCopies.copied_packets mode l v r state entry forward current).2
  have same : ByteMemory.bytesAt (Listing8MainCopies.finish mode l state).principal.memory (transitionParams mode l).destination
      (transitionSpan mode)=ByteMemory.bytesAt state.principal.memory l.sourceTransition (transitionSpan mode) := by
    rw [current.rule]
    simpa only [sourceTransitionBytes,transition_length] using copied
  exact all mode _ _ _ state.principal.memory (transition_current mode l v _ current.rule) (transition_bounded mode l v) same

theorem sources (mode : Mode) (l : Layout) (v : Values mode) (r : Resources mode l)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode l.start)
    (forward : state.backwards=false) (current : Listing8MainCopyImage.Current mode l v state.principal.memory) :
    All mode (nodeTemplates mode l v) (Listing8MainCopies.finish mode l state).principal.memory ∧
    All mode (transitionTemplates mode l v) (Listing8MainCopies.finish mode l state).principal.memory := by
  have packets := Listing8MainCopies.source_packets mode l v r state entry forward current
  exact ⟨node_current mode l v _ packets.1,transition_current mode l v _ packets.2⟩

end SmcTuring.Appendix.Listing8CopyOwnerFinal
