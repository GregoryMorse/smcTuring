module
public import SmcTuring.Native.StringPCWindows

public section
namespace SmcTuring.Native.StringPCBranches
open MemoryRegion StringPCSteps

/-- An arbitrary final instruction, including a branching CALL, has its
fetch envelope derived from the actual preceding sequential effects. Its
post-instruction target is handled separately; no reached PC is a premise. -/
theorem last_instruction (mode : Mode) (region : Region) (before : List (StringStack.Form mode))
    (last : StringStack.Form mode) (state : StringExecution.State mode) (pc : Nat)
    (straight : ∀ form∈before,Sequential mode form)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (guard : StringPCWindows.Guard mode before) (margin : 3≤size mode last)
    (lower : region.lower≤pc) (upper : pc+total mode before+size mode last≤region.upper)
    (capacity : region.upper<2^(8*mode.wordBytes)) : StringPCWindows.Run mode region (before++[last]) state := by
  apply (StringPCWindows.append mode region before [last] state).mpr
  refine ⟨StringPCWindows.sequential mode region before state pc straight entry guard lower (by omega) capacity,?_⟩
  change StringPCWindows.Envelope mode region last (StringWrites.run mode before state) ∧ True
  refine ⟨?_,trivial⟩
  have reached : (StringWrites.run mode before state).principal.pc=Arithmetic.encodeNat mode (pc+total mode before) := by
    rw [run_pc mode before state straight,entry]
    exact BitVec.ofNat_add_ofNat _ _
  unfold StringPCWindows.Envelope
  rw [reached,Arithmetic.encode_nat_toNat mode _ (by omega),Nat.max_eq_right margin]
  exact ⟨by omega,upper⟩

end SmcTuring.Native.StringPCBranches
