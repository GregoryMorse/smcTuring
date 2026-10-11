module
public import SmcTuring.Appendix.Listing8GlobalBoot
public import SmcTuring.Appendix.Listing8FailureGlobalValues

public section
namespace SmcTuring.Appendix.Listing8BootControl
open Native Listing8CopyImage Listing8GlobalBoot
abbrev Targets:=Listing8PointerCopies.Targets
@[expose] def region (mode : Mode) (origin : Nat) (l : Layout) (sentinel : Nat) :=
  Listing8FailureGeometry.region mode l sentinel (Listing8BootImage.beginPC mode origin)
@[expose] def failed (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :=
  Listing8FailureGlobalValues.failed mode l t v sentinel (Listing8BootImage.beginPC mode origin) (extra mode origin backing) (bodySeed mode origin seed)

theorem call_positions (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing8FailureLayout.callPC mode (region mode origin l sentinel)=origin+(if mode=.x86 then 801 else 1269) ∧
    Listing8FailureLayout.callPC mode (region mode origin l sentinel)+5=origin+(if mode=.x86 then 806 else 1274) := by
  have coords:=(Listing8FailureGeometry.positions mode l t sentinel (Listing8BootImage.beginPC mode origin) body).2.2
  change Listing8FailureLayout.callPC mode (region mode origin l sentinel)=_ at coords
  rw [boot.packed] at coords
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] at coords ⊢ <;>
    dsimp [Listing4EntryLayout.mainPC,Listing4EntryLayout.size] at coords <;> omega
theorem backedge_delta (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Relocation.delta (Listing8FailureLayout.callPC mode (region mode origin l sentinel)+5) (Listing8BootImage.beginPC mode origin)=
      (if mode=.x86 then (-785 : Int) else -1213) := by
  rw [(call_positions mode origin l t sentinel boot body).2]
  have begin:=(Listing4JumpLayout.positions mode origin).2.2
  change Listing8BootImage.beginPC mode origin=_ at begin
  rw [begin]
  cases mode <;> simp only [reduceCtorEq,ite_true,ite_false] <;> unfold Relocation.delta <;> omega
theorem backedge_reach (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Relocation.SignedDelta (Listing8FailureLayout.callPC mode (region mode origin l sentinel)+5) (Listing8BootImage.beginPC mode origin) := by
  unfold Relocation.SignedDelta
  rw [backedge_delta mode origin l t sentinel boot body]
  cases mode <;> decide
theorem begin_capacity (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (sentinel : Nat)
    (boot : Listing8BootImage.Bounds mode origin l)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin)) :
    Listing8BootImage.beginPC mode origin<2^(8*mode.wordBytes) := by
  change Listing4JumpLayout.beginPC mode origin<2^(8*mode.wordBytes)
  rw [Listing4Boot.endpoint]
  exact Listing4EntryLayout.boot_capacity mode origin (entry_capacity mode origin l t sentinel boot body)

theorem failure_condition (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    failed mode origin l t v sentinel backing seed=
      decide ((if Listing8LiteralInput.chosen v.rule v.tape then v.newState else v.next)=Arithmetic.encodeNat mode sentinel) :=
  Listing8FailureGlobalValues.failure_condition mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _
theorem call_value (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (finish mode origin l t v sentinel backing seed).principal.memory (Listing8FailureLayout.callPC mode (region mode origin l sentinel)+1)=
      if failed mode origin l t v sentinel backing seed then 0 else Listing8FailureLayout.original mode (region mode origin l sentinel) :=
  Listing8FailureGlobalValues.call_value mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _
/-- Current post-mask packet only. Actual intervening stack writes and CALL
execution remain the next composition step. -/
theorem call_fetch (mode : Mode) (origin : Nat) (l : Layout) (t : Targets) (v : Values mode) (sentinel : Nat)
    (r : Resources mode l) (owners : Listing8CopiedOwners.Bounds mode l v) (copies : Listing8PointerCopies.Bounds mode l t)
    (body : Listing8FailureGeometry.Bounds mode l t sentinel (Listing8BootImage.beginPC mode origin))
    (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    StringStack.fetch mode (finish mode origin l t v sentinel backing seed).principal.memory (Listing8FailureLayout.callPC mode (region mode origin l sentinel))=
      some (StringStack.native mode (.callRelative
        (if failed mode origin l t v sentinel backing seed then 0 else Listing8FailureLayout.original mode (region mode origin l sentinel)))) :=
  StringStack.previous_fetch mode _ _ _ (Listing8FailureGlobalValues.call_fetch mode l t v sentinel (Listing8BootImage.beginPC mode origin) r owners copies body _ _)
end SmcTuring.Appendix.Listing8BootControl
