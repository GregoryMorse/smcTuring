module
public import SmcTuring.Native.StringPCSteps

public section
namespace SmcTuring.Native.StringPCWindows
open MemoryRegion StringPCSteps

/-- Reserve the classifier header and complete selected instruction span.
The decoder's additional request bounds are connected separately. -/
@[expose] def Envelope (mode : Mode) (region : Region) (form : StringStack.Form mode)
    (state : StringExecution.State mode) : Prop :=
  region.Contains state.principal.pc.toNat (max 3 (size mode form))

@[expose] def Run (mode : Mode) (region : Region) : List (StringStack.Form mode) → StringExecution.State mode → Prop
  | [],_ => True
  | form::rest,state => Envelope mode region form state ∧ Run mode region rest (StringStack.execute mode form state)

/-- A static suffix has enough emitted bytes for the three-byte header.
This is a property of forms and byte sizes, with no future state input. -/
@[expose] def Guard (mode : Mode) : List (StringStack.Form mode) → Prop
  | [] => True
  | form::rest => 3≤size mode form+total mode rest ∧ Guard mode rest

theorem append (mode : Mode) (region : Region) (first second : List (StringStack.Form mode))
    (state : StringExecution.State mode) :
    Run mode region (first++second) state ↔ Run mode region first state ∧ Run mode region second (StringWrites.run mode first state) := by
  induction first generalizing state with
  | nil => simp only [List.nil_append,Run,StringWrites.run,true_and]
  | cons form rest ih => simp only [List.cons_append,Run,StringWrites.run,ih,and_assoc]

theorem guard_prefix (mode : Mode) (first second : List (StringStack.Form mode))
    (guard : Guard mode second) (enough : 3≤total mode second) : Guard mode (first++second) := by
  induction first with
  | nil => exact guard
  | cons form rest ih =>
    simp only [List.cons_append,Guard,total_append]
    exact ⟨by omega,ih⟩

theorem guard_last (mode : Mode) (first : List (StringStack.Form mode)) (last : StringStack.Form mode)
    (enough : 3≤size mode last) : Guard mode (first++[last]) := by
  apply guard_prefix mode first [last]
  · simpa only [Guard,total,List.map_nil,List.sum_nil,Nat.add_zero] using And.intro enough True.intro
  · simpa only [total,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using enough

/-- Every actual PC window of a nonbranching fragment follows its initial
PC, static byte footprint and final header margin. No future PC is assumed. -/
theorem sequential (mode : Mode) (region : Region) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (pc : Nat)
    (straight : ∀ form∈forms,Sequential mode form)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc) (guard : Guard mode forms)
    (lower : region.lower≤pc) (upper : pc+total mode forms≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) : Run mode region forms state := by
  induction forms generalizing state pc with
  | nil => trivial
  | cons form rest ih =>
    have head:=straight form (List.Mem.head _)
    have tail:=fun later member => straight later (List.Mem.tail _ member)
    have totalCons : total mode (form::rest)=size mode form+total mode rest := by simp only [total,List.map_cons,List.sum_cons]
    rw [totalCons] at upper
    have margin:=guard.1
    refine ⟨?_,ih _ (pc+size mode form) tail (located_pc mode form state pc head entry) guard.2 (by omega) (by omega)⟩
    unfold Envelope
    rw [entry,Arithmetic.encode_nat_toNat mode pc (by omega)]
    refine ⟨lower,?_⟩
    have count : max 3 (size mode form)≤size mode form+total mode rest := by
      by_cases enough : 3≤size mode form
      · rw [Nat.max_eq_right enough];omega
      · rw [Nat.max_eq_left (by omega)];exact margin
    omega

theorem append_trace (mode : Mode) (region : Region) (first second : List (StringStack.Form mode))
    (state middle : StringExecution.State mode) (actual : StringStack.Trace mode state first middle)
    (leading : Run mode region first state) (trailing : Run mode region second middle) : Run mode region (first++second) state := by
  rw [append,StringWrites.trace_run_eq mode actual]
  exact ⟨leading,trailing⟩

theorem next_window (mode : Mode) (region : Region) {state finish : StringExecution.State mode}
    {forms : List (StringStack.Form mode)} (actual : StringStack.Trace mode state forms finish)
    (windows : Run mode region forms state) (before : List (StringStack.Form mode))
    (form : StringStack.Form mode) (after : List (StringStack.Form mode)) (cut : before++form::after=forms) :
    ∃ reached, StringStack.Trace mode state before reached ∧
      StringStack.fetch mode reached.principal.memory reached.principal.pc.toNat=some form ∧
      Envelope mode region form reached ∧ StringStack.Trace mode (StringStack.execute mode form reached) after finish := by
  rw [←cut] at actual windows
  obtain ⟨reached,leading,trailing⟩:=StringTraceChecks.split_trace mode before (form::after) actual
  have bounds:=(append mode region before (form::after) state).mp windows
  rw [StringWrites.trace_run_eq mode leading] at bounds
  cases trailing with
  | step current tail => exact ⟨reached,leading,current,bounds.2.1,tail⟩

end SmcTuring.Native.StringPCWindows
