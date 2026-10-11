module
public import SmcTuring.Appendix.Listing8EarlyState
public import SmcTuring.Appendix.Listing8GlobalBootValues

public section
namespace SmcTuring.Appendix.Listing8StackMetadata
open Native Listing8CopyImage Listing8GlobalBoot
abbrev Targets:=Listing8PointerCopies.Targets
/-- Complete bootstrap exterior frame from executed memory effects, including
all temporary pointer exchanges and the actual source-node tape write. -/
theorem window (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) (observed count : Nat)
    (lower : origin ≤ observed) (upper : observed+count ≤ l.start) :
    ByteMemory.bytesAt (finish mode origin l t v sentinel backing seed).principal.memory observed count=
      ByteMemory.bytesAt (initial mode origin l t v sentinel backing seed).principal.memory observed count := by
  have large : 10 ≤ Listing8Prototypes.nodeSpan mode := by cases mode <;> decide
  have tape : l.sourceNode+10 ≤ observed ∨ observed+count ≤ l.sourceNode+6 := by
    rcases boot.node with early | late
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have restored:=Listing8EarlyState.failure mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body
    (extra mode origin backing) (bodySeed mode origin seed) observed count upper tape
  have image:=Listing8BootImage.memory_put mode origin l t v sentinel (Listing8BootImage.beginPC mode origin) r boot body backing
  change ByteMemory.bytesAt (finish mode origin l t v sentinel backing seed).principal.memory observed count=
    ByteMemory.bytesAt (ByteMemory.putBytes
      (Listing8FailureGlobalImage.memory mode l t v sentinel (Listing8BootImage.beginPC mode origin) backing)
      origin (Listing4EntryLayout.bytes mode origin)) observed count
  rw [←image];exact restored

theorem code_current (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (finish mode origin l t v sentinel backing seed).principal.memory origin (Listing4EntryLayout.size mode)=
      Listing4EntryLayout.bytes mode origin := by
  rw [window mode origin l t v sentinel r owners copies boot body backing seed origin (Listing4EntryLayout.size mode) (Nat.le_refl _) (by rw [boot.packed];rfl)]
  exact Listing4Entry.initial_current mode origin (bootSeed mode origin l t v sentinel backing seed)

theorem stack_packet (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (finish mode origin l t v sentinel backing seed).principal.memory origin (Listing4StackLayout.size mode)=
      Listing4StackLayout.bytes mode origin := by
  have current:=code_current mode origin l t v sentinel r owners copies boot body backing seed
  have first:=ByteWindow.packet (finish mode origin l t v sentinel backing seed).principal.memory origin [] (Listing4Boot.bytes mode origin)
    (Listing4TargetLayout.bytes mode origin (Listing4JumpLayout.beginPC mode origin)) (by
      simp only [List.nil_append]
      change ByteMemory.bytesAt _ origin (Listing4EntryLayout.bytes mode origin).length=Listing4EntryLayout.bytes mode origin
      rw [Listing4EntryLayout.bytes_length];exact current)
  have code : ByteMemory.bytesAt (finish mode origin l t v sentinel backing seed).principal.memory origin (Listing4Boot.size mode)=Listing4Boot.bytes mode origin := by
    simpa only [List.length_nil,Nat.add_zero,Listing4Boot.bytes_length] using first
  exact Listing4Boot.stack_packet mode origin _ code

theorem stptr (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel backing seed).principal.memory (Listing4StackLayout.stptr mode origin)=
      Arithmetic.encodeNat mode (Listing4StackLayout.stptr mode origin) :=
  Listing4StackLayout.initial_stptr mode origin _
    (Listing4EntryLayout.stack_capacity mode origin (entry_capacity mode origin l t sentinel boot body))
    (stack_packet mode origin l t v sentinel r owners copies boot body backing seed)
theorem return_field (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (finish mode origin l t v sentinel backing seed).principal.memory (Listing4StackLayout.returnField mode origin)=
      Arithmetic.encodeNat mode (Listing4StackLayout.stptr mode origin) :=
  Listing4TargetMemory.original_return mode origin _
    (Listing4EntryLayout.stack_capacity mode origin (entry_capacity mode origin l t sentinel boot body))
    (stack_packet mode origin l t v sentinel r owners copies boot body backing seed)
end SmcTuring.Appendix.Listing8StackMetadata
