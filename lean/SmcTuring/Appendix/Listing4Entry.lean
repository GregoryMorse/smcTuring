module
public import SmcTuring.Appendix.Listing4EntryLayout

public section
namespace SmcTuring.Appendix.Listing4Entry
open Native Listing4EntryLayout
open Listing4StackLayout (stptr returnField fields_separate)
open Listing4JumpLayout (beginPC)
@[expose] def initial (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :=
  {seed with principal := {seed.principal with
    pc := Arithmetic.encodeNat mode start
    memory := ByteMemory.putBytes seed.principal.memory start (bytes mode start)}}
/-- Reference for the restored byte image/registers. Its PC remains the
original entry; only executed stages below determine the actual future PC. -/
@[expose] def targetSeed (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :=
  let base := initial mode start seed
  {base with principal := {base.principal with
    accumulator := Listing4StackInit.accumulator mode start base
    carry := Listing4JumpEffects.flag mode start base}}
@[expose] def beforeTarget (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :=
  Listing4JumpEffects.finish mode start (initial mode start seed)
@[expose] def finish (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :=
  Listing4TargetEffects.finish mode start (beginPC mode start) (Arithmetic.encodeNat mode (beginPC mode start)) (targetSeed mode start seed)

theorem initial_current (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (initial mode start seed).principal.memory start (size mode)=bytes mode start := by
  unfold initial
  simpa only [bytes_length] using ByteMemory.bytes_at_put seed.principal.memory start (bytes mode start)
theorem boot_current (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (initial mode start seed).principal.memory start (Listing4Boot.size mode)=Listing4Boot.bytes mode start := by
  have code := initial_current mode start seed
  have packet := ByteWindow.packet (initial mode start seed).principal.memory start [] (Listing4Boot.bytes mode start)
    (Listing4TargetLayout.bytes mode start (beginPC mode start)) (by
      simp only [List.nil_append]
      change ByteMemory.bytesAt (initial mode start seed).principal.memory start (bytes mode start).length=bytes mode start
      rw [bytes_length];exact code)
  simpa only [List.length_nil,Nat.add_zero,Listing4Boot.bytes_length] using packet
theorem stack_current (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (targetSeed mode start seed).principal.memory start (Listing4StackLayout.size mode)=Listing4StackLayout.bytes mode start :=
  Listing4Boot.stack_packet mode start _ (boot_current mode start seed)
theorem target_current (mode : Mode) (start : Nat) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (targetSeed mode start seed).principal.memory (beginPC mode start) (Listing4TargetLayout.size mode)=
      Listing4TargetLayout.bytes mode start (beginPC mode start) := by
  have code := initial_current mode start seed
  have packet := ByteWindow.packet (initial mode start seed).principal.memory start (Listing4Boot.bytes mode start)
    (Listing4TargetLayout.bytes mode start (beginPC mode start)) [] (by
      simp only [List.append_nil]
      change ByteMemory.bytesAt (initial mode start seed).principal.memory start (bytes mode start).length=bytes mode start
      rw [bytes_length];exact code)
  simpa only [Listing4Boot.bytes_length,←Listing4Boot.endpoint,Listing4TargetLayout.bytes_length,targetSeed] using packet

theorem call_shape (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    beforeTarget mode start seed=Listing4TargetEffects.entry mode start (beginPC mode start)
      (Arithmetic.encodeNat mode (beginPC mode start)) (targetSeed mode start seed) := by
  have executed := Listing4JumpEffects.called_effect mode start (initial mode start seed) rfl
    (by rw [Listing4Boot.endpoint];exact boot_capacity mode start fits)
    (Listing4Boot.stack_packet mode start _ (boot_current mode start seed))
  change beforeTarget mode start seed=_ at executed
  rw [executed,Listing4TargetEffects.entry,targetSeed]
  rw [MixedFrames.words_commute mode (initial mode start seed).principal.memory (stptr mode start) (returnField mode start) _ _
    (Or.symm (fields_separate mode start))]

/-- Complete printed DEFSTACK/JUMP/JUMPTARGET entry, one initialized image and
actual CALL-derived stack/register/byte state. No PC reset bridges the stages. -/
theorem trace (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    StringStack.Trace mode (initial mode start seed) (forms mode start) (finish mode start seed) := by
  have boot := Listing4Boot.trace mode start (initial mode start seed) rfl (boot_capacity mode start fits) (boot_current mode start seed)
  have target := Listing4TargetTrace.trace mode start (beginPC mode start) (Arithmetic.encodeNat mode (beginPC mode start))
    (targetSeed mode start seed) (begin_ranges mode start) (stack_capacity mode start fits) (target_capacity mode start fits)
    (stack_current mode start seed) (target_after_stack mode start) (target_current mode start seed)
  rw [←call_shape mode start seed fits] at target
  exact StringStack.trace_append mode boot target

theorem effect (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    finish mode start seed={targetSeed mode start seed with principal := {(targetSeed mode start seed).principal with
      pc := Arithmetic.encodeNat mode (mainPC mode start)
      carry := Listing4TargetEffects.flag mode start}} := by
  have result := Listing4TargetEffects.effect mode start (beginPC mode start) (Arithmetic.encodeNat mode (beginPC mode start))
    (targetSeed mode start seed) (begin_ranges mode start) (stack_capacity mode start fits) (stack_current mode start seed)
  rw [Listing4EntryLayout.endpoint] at result
  exact result

theorem memory (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    (finish mode start seed).principal.memory=(initial mode start seed).principal.memory := by rw [effect mode start seed fits];rfl
theorem registers (mode : Mode) (start : Nat) (seed : StringExecution.State mode)
    (fits : mainPC mode start<2^(8*mode.wordBytes)) :
    (finish mode start seed).principal.stack=seed.principal.stack ∧
    (finish mode start seed).sourceIndex=seed.sourceIndex ∧
    (finish mode start seed).destinationIndex=seed.destinationIndex ∧
    (finish mode start seed).backwards=seed.backwards ∧
    (finish mode start seed).principal.accumulator=Listing4StackInit.accumulator mode start seed ∧
    (finish mode start seed).principal.carry=Listing4TargetEffects.flag mode start := by
  rw [effect mode start seed fits]
  cases mode <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
end SmcTuring.Appendix.Listing4Entry
