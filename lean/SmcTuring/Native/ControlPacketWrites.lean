module
public import SmcTuring.Native.ControlPackets
public import SmcTuring.Native.StringMixedWrites

public section
namespace SmcTuring.Native.ControlPacketWrites

theorem length (mode : Mode) (site : ControlPackets.Site) (state : StringExecution.State mode) :
    (StringWrites.packet mode (.previous (ControlPackets.form mode site)) state).bytes.length=ControlPackets.width mode site := by
  cases site with
  | mk pc target operation =>
    cases operation with
    | word op => cases mode <;> cases op <;> exact LittleEndian.word_encode_length _ _
    | negate => cases mode <;> exact LittleEndian.word_encode_length _ _
    | dword raw => exact StringMixedWrites.length mode (.arithmetic (DwordArithmetic.located mode raw pc target)) state

theorem address (mode : Mode) (site : ControlPackets.Site) (valid : ControlPackets.Valid mode site)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode site.pc) :
    (StringWrites.packet mode (.previous (ControlPackets.form mode site)) state).address=site.target := by
  have positive : 0<ControlPackets.width mode site := by
    cases mode <;> cases h : site.operation <;> simp [ControlPackets.width,h,Mode.wordBytes]
  have fits : site.target<2^(8*mode.wordBytes) := by have bound:=valid.targetFits;omega
  cases h : site.operation with
  | word op =>
    have size : Native.instructionLength mode (.memory (WordMemoryArithmetic.opcode op) 0)=WordMemoryArithmetic.size mode := by
      cases mode <;> cases op <;> rfl
    have hit:=Relocation.instruction_memory_hits mode (WordMemoryArithmetic.opcode op) site.pc site.target state.principal entry
      (by simpa only [size,ControlPackets.size,h] using valid.range)
    change (Execution.memoryAddress mode (Execution.nextPC mode (WordMemoryArithmetic.form mode op site.pc site.target) state.principal)
      (Relocation.instructionDisp mode (WordMemoryArithmetic.opcode op) site.pc site.target))=Arithmetic.encodeNat mode site.target at hit
    have actual : (StringWrites.packet mode (.previous (ControlPackets.form mode site)) state).address=
        (Execution.memoryAddress mode (Execution.nextPC mode (WordMemoryArithmetic.form mode op site.pc site.target) state.principal)
          (Relocation.instructionDisp mode (WordMemoryArithmetic.opcode op) site.pc site.target)).toNat := by
      cases mode <;> cases op <;> simp only [ControlPackets.form,h] <;> rfl
    rw [actual,hit,Arithmetic.encode_nat_toNat mode _ fits]
  | negate =>
    have actual : (StringWrites.packet mode (.previous (ControlPackets.form mode site)) state).address=
        (WordNegation.address mode (ControlPackets.displacement mode site) state.principal).toNat := by
      cases mode <;> simp only [ControlPackets.form,h] <;> rfl
    have next : WordNegation.next mode state.principal=Arithmetic.encodeNat mode (site.pc+WordNegation.length mode) := by
      rw [WordNegation.next,entry];exact BitVec.ofNat_add_ofNat _ _
    have hit : WordNegation.address mode (ControlPackets.displacement mode site) state.principal=Arithmetic.encodeNat mode site.target := by
      rw [WordNegation.address,next]
      simp only [ControlPackets.displacement,ControlPackets.size,h]
      exact Relocation.memory_hits mode _ _ (by simpa only [ControlPackets.size,h] using valid.range)
    rw [actual,hit,Arithmetic.encode_nat_toNat mode _ fits]
  | dword raw =>
    have actual : (StringWrites.packet mode (.previous (ControlPackets.form mode site)) state).address=
        (DwordArithmetic.address mode (DwordArithmetic.located mode raw site.pc site.target) state.principal).toNat := by
      simpa only [ControlPackets.form,h,StringMixed.canonical,MixedDword.address,StringStoreWrites.liftDword] using
        StringMixedWrites.address mode (.arithmetic (DwordArithmetic.located mode raw site.pc site.target)) state
    rw [actual,DwordArithmetic.located_address mode raw site.pc site.target state.principal
      (by simpa only [h] using valid.direct) entry (by simpa only [ControlPackets.size,h] using valid.range),Arithmetic.encode_nat_toNat mode _ fits]

theorem code_write (mode : Mode) (codeStart codeEnd : Nat) (site : ControlPackets.Site) (valid : ControlPackets.Valid mode site)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode site.pc)
    (inside : codeStart≤site.target ∧ site.target+ControlPackets.width mode site≤codeEnd) :
    StringWrites.CodeWrite mode codeStart codeEnd (.previous (ControlPackets.form mode site)) state := by
  unfold StringWrites.CodeWrite
  rw [address mode site valid state entry,length]
  refine ⟨?_,inside⟩
  cases mode <;> cases h : site.operation <;> simp [ControlPackets.width,h,Mode.wordBytes]

theorem run (mode : Mode) (sites : List ControlPackets.Site) (start : Nat)
    (chain : ControlPackets.Contiguous mode start sites) (valid : ∀ site∈sites,ControlPackets.Valid mode site)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringWrites.run mode ((ControlPackets.program mode sites).map StringStack.Form.previous) state=ControlPackets.finish mode sites state := by
  induction sites generalizing start state with
  | nil => rfl
  | cons site sites ih =>
    have ready:=valid site (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have next : (ControlPackets.effect mode site state).principal.pc=Arithmetic.encodeNat mode (site.pc+ControlPackets.size mode site) := rfl
    change StringWrites.run mode _ (StringControl.execute mode (ControlPackets.form mode site) state)=_
    rw [ControlPackets.execute_effect mode site ready state location]
    exact ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member)) (ControlPackets.effect mode site state) next

theorem owned (mode : Mode) (codeStart codeEnd : Nat) (sites : List ControlPackets.Site) (start : Nat)
    (chain : ControlPackets.Contiguous mode start sites) (valid : ∀ site∈sites,ControlPackets.Valid mode site)
    (fields : ∀ site∈sites,codeStart≤site.target ∧ site.target+ControlPackets.width mode site≤codeEnd)
    (state : StringExecution.State mode) (entry : state.principal.pc=Arithmetic.encodeNat mode start) :
    StringWrites.OwnedRun mode codeStart codeEnd ((ControlPackets.program mode sites).map StringStack.Form.previous) state := by
  induction sites generalizing start state with
  | nil => trivial
  | cons site sites ih =>
    have ready:=valid site (List.Mem.head _)
    have location : state.principal.pc=Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have first:=code_write mode codeStart codeEnd site ready state location (fields site (List.Mem.head _))
    have next : (ControlPackets.effect mode site state).principal.pc=Arithmetic.encodeNat mode (site.pc+ControlPackets.size mode site) := rfl
    constructor
    · exact first
    · change StringWrites.OwnedRun mode codeStart codeEnd _ (StringControl.execute mode (ControlPackets.form mode site) state)
      rw [ControlPackets.execute_effect mode site ready state location]
      exact ih _ chain.2 (fun later member => valid later (List.Mem.tail _ member))
        (fun later member => fields later (List.Mem.tail _ member)) (ControlPackets.effect mode site state) next

end SmcTuring.Native.ControlPacketWrites
