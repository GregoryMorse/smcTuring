module
public import SmcTuring.Native.StringControl
public import SmcTuring.Native.WordMemoryArithmetic

public section
namespace SmcTuring.Native.ControlPackets
inductive Operation where
  | word (op : WordMemoryArithmetic.Op)
  | negate
  | dword (form : DwordArithmetic.Form)
structure Site where
  pc : Nat
  target : Nat
  operation : Operation
@[expose] def size (mode : Mode) (site : Site) :=
  match site.operation with
  | .word _ => WordMemoryArithmetic.size mode
  | .negate => WordNegation.length mode
  | .dword form => DwordArithmetic.length form
@[expose] def width (mode : Mode) (site : Site) :=
  match site.operation with | .dword _ => 4 | _ => mode.wordBytes
@[expose] def displacement (mode : Mode) (site : Site) := Relocation.memoryDisp mode (site.pc+size mode site) site.target
@[expose] def form (mode : Mode) (site : Site) : StringControl.Form mode :=
  match site.operation with
  | .word op => .previous (StringDwordCopy.native mode (WordMemoryArithmetic.form mode op site.pc site.target))
  | .negate => StringControl.negation mode (displacement mode site)
  | .dword raw => .previous (StringDwordArithmetic.canonical mode (DwordArithmetic.located mode raw site.pc site.target))
@[expose] def bytes (mode : Mode) (site : Site) :=
  match site.operation with
  | .word op => Native.encode mode (WordMemoryArithmetic.form mode op site.pc site.target)
  | .negate => WordNegation.encode mode (displacement mode site)
  | .dword raw => DwordArithmetic.encode (DwordArithmetic.located mode raw site.pc site.target)
structure Valid (mode : Mode) (site : Site) : Prop where
  codeFits : site.pc+size mode site < 2^(8*mode.wordBytes)
  targetFits : site.target+width mode site ≤ 2^(8*mode.wordBytes)
  range : mode = .x64 → Relocation.SignedDelta (site.pc+size mode site) site.target
  direct : match site.operation with | .dword raw => DwordArithmetic.direct raw = true | _ => True
@[expose] def memory (mode : Mode) (site : Site) (state : Execution.State mode) :=
  match site.operation with
  | .word op => ByteMemory.putWord mode state.memory site.target
      (WordMemoryArithmetic.result op (MixedMemory.getWord mode state.memory site.target) state.accumulator)
  | .negate => ByteMemory.putWord mode state.memory site.target (-MixedMemory.getWord mode state.memory site.target)
  | .dword raw => DwordCode.put state.memory site.target
      (DwordArithmetic.result raw (DwordCode.get state.memory site.target) state.carry)
@[expose] def carry (mode : Mode) (site : Site) (state : Execution.State mode) :=
  match site.operation with
  | .word op => WordMemoryArithmetic.flag op (MixedMemory.getWord mode state.memory site.target) state.accumulator state.carry
  | .negate => decide (MixedMemory.getWord mode state.memory site.target ≠ 0)
  | .dword raw => DwordArithmetic.flag raw (DwordCode.get state.memory site.target) state.carry
@[expose] def accumulator (mode : Mode) (site : Site) (state : Execution.State mode) :=
  match site.operation with
  | .word op => WordMemoryArithmetic.accumulator op (MixedMemory.getWord mode state.memory site.target) state.accumulator
  | _ => state.accumulator
@[expose] def effect (mode : Mode) (site : Site) (state : StringExecution.State mode) :=
  {state with principal := {state.principal with
    pc := Arithmetic.encodeNat mode (site.pc+size mode site)
    accumulator := accumulator mode site state.principal
    carry := carry mode site state.principal
    memory := memory mode site state.principal}}

theorem bytes_length (mode : Mode) (site : Site) : (bytes mode site).length = size mode site := by
  cases h : site.operation with
  | word op => simp only [bytes,size,h,Native.instruction_length,WordMemoryArithmetic.form_length]
  | negate => simp only [bytes,size,h,WordNegation.encode_length]
  | dword raw => simp only [bytes,size,h,DwordArithmetic.encode_length,DwordArithmetic.located,DwordArithmetic.relocate_length]

theorem fetched (mode : Mode) (site : Site) (memory : ByteMemory.Memory)
    (current : ByteMemory.bytesAt memory site.pc (bytes mode site).length = bytes mode site) :
    StringControl.fetch mode memory site.pc = some (form mode site) := by
  cases h : site.operation with
  | word op =>
    simp only [form,h]
    exact StringControl.previous_fetch mode memory site.pc _
      (StringDwordCopy.native_encoding mode _ memory site.pc (by simpa only [bytes,h] using current))
  | negate =>
    simp only [form,h]
    exact StringControl.negation_encoding mode memory site.pc _ (by simpa only [bytes,h] using current)
  | dword raw =>
    simp only [form,h]
    exact StringControl.previous_fetch mode memory site.pc _
      (StringDwordArithmetic.encoding mode _ memory site.pc (by simpa only [bytes,h] using current))

theorem execute_effect (mode : Mode) (site : Site) (valid : Valid mode site) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode site.pc) :
    StringControl.execute mode (form mode site) state = effect mode site state := by
  have positive : 0 < width mode site := by cases mode <;> cases h : site.operation <;> simp [width,h,Mode.wordBytes]
  have fits : site.target < 2^(8*mode.wordBytes) := by have bound := valid.targetFits;omega
  cases h : site.operation with
  | word op =>
    simp only [form,h]
    change {state with principal := Execution.execute mode (WordMemoryArithmetic.form mode op site.pc site.target) state.principal} = _
    rw [WordMemoryArithmetic.located_effect mode op site.pc site.target state.principal entry (by simpa only [size,h] using valid.range) fits]
    simp only [effect,size,accumulator,carry,memory,h]
  | negate =>
    rw [show form mode site = StringControl.negation mode (displacement mode site) by simp only [form,h],StringControl.negation_execute]
    have range : mode = .x64 → Relocation.SignedDelta (site.pc+WordNegation.length mode) site.target := by simpa only [size,h] using valid.range
    simp only [displacement,size,h]
    change {state with principal := WordNegation.execute mode (Relocation.memoryDisp mode (site.pc+WordNegation.length mode) site.target) state.principal} = _
    rw [WordNegation.located_effect mode site.pc site.target state.principal entry range fits]
    simp only [effect,size,accumulator,carry,memory,h]
  | dword raw =>
    rw [show form mode site = .previous (StringDwordArithmetic.canonical mode (DwordArithmetic.located mode raw site.pc site.target)) by simp only [form,h]]
    rw [StringControl.execute,StringDwordArithmetic.execute]
    rw [DwordArithmetic.located_effect mode raw site.pc site.target state.principal
      (by simpa only [h] using valid.direct) entry (by simpa only [size,h] using valid.range) fits]
    simp only [effect,size,accumulator,carry,memory,h]

@[expose] def Current (mode : Mode) (site : Site) (memory : ByteMemory.Memory) :=
  ByteMemory.bytesAt memory site.pc (bytes mode site).length = bytes mode site
@[expose] def Intact (mode : Mode) (sites : List Site) (memory : ByteMemory.Memory) :=
  ∀ site ∈ sites, Current mode site memory
@[expose] def Contiguous (mode : Mode) : Nat → List Site → Prop
  | _,[] => True
  | start,site::sites => site.pc=start ∧ Contiguous mode (site.pc+size mode site) sites
@[expose] def OutsideCodes (mode : Mode) (sites : List Site) :=
  ∀ writer ∈ sites, ∀ reader ∈ sites,
    writer.target+width mode writer ≤ reader.pc ∨ reader.pc+size mode reader ≤ writer.target
@[expose] def program (mode : Mode) (sites : List Site) := sites.map (form mode)
@[expose] def finish (mode : Mode) (sites : List Site) (state : StringExecution.State mode) :=
  sites.foldl (fun current site => effect mode site current) state
@[expose] def wholeBytes (mode : Mode) (sites : List Site) := sites.flatMap (bytes mode)

theorem effect_window (mode : Mode) (site : Site) (state : StringExecution.State mode) (start count : Nat)
    (outside : site.target+width mode site ≤ start ∨ start+count ≤ site.target) :
    ByteMemory.bytesAt (effect mode site state).principal.memory start count = ByteMemory.bytesAt state.principal.memory start count := by
  cases h : site.operation
  all_goals simp only [effect,memory,h,ByteMemory.putWord,DwordCode.put]
  all_goals apply ByteMemory.bytes_at_frame
  all_goals intro index;have bound:=index.isLt
  all_goals simp only [width,h,LittleEndian.word_encode_length,ByteMemory.Inside] at outside ⊢
  all_goals rcases outside with before | after <;> omega

/-- Initial complete packets and static separation derive every future fetch. -/
theorem trace (mode : Mode) (sites : List Site) (start : Nat)
    (chain : Contiguous mode start sites) (valid : ∀ site ∈ sites, Valid mode site)
    (outside : OutsideCodes mode sites) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start) (current : Intact mode sites state.principal.memory) :
    StringControl.Trace mode state (program mode sites) (finish mode sites state) := by
  induction sites generalizing start state with
  | nil => exact .nil _
  | cons site sites ih =>
    have firstValid := valid site (List.mem_cons_self ..)
    have location : state.principal.pc = Arithmetic.encodeNat mode site.pc := by rw [chain.1];exact entry
    have fits : site.pc < 2^(8*mode.wordBytes) := by have bound:=firstValid.codeFits;omega
    have fetched : StringControl.fetch mode state.principal.memory state.principal.pc.toNat = some (form mode site) := by
      rw [location,Arithmetic.encode_nat_toNat mode site.pc fits]
      exact ControlPackets.fetched mode site _ (current site (List.mem_cons_self ..))
    have later : Intact mode sites (effect mode site state).principal.memory := by
      intro reader member
      rw [Current,effect_window mode site state reader.pc (bytes mode reader).length (by
        rw [bytes_length];exact outside site (List.mem_cons_self ..) reader (List.mem_cons_of_mem _ member))]
      exact current reader (List.mem_cons_of_mem _ member)
    change StringControl.Trace mode state (form mode site::program mode sites) _
    refine .step fetched ?_
    rw [execute_effect mode site firstValid state location]
    exact ih _ chain.2 (fun reader member => valid reader (List.mem_cons_of_mem _ member))
      (fun writer wm reader rm => outside writer (List.mem_cons_of_mem _ wm) reader (List.mem_cons_of_mem _ rm))
      (effect mode site state) rfl later

theorem initial_packets (mode : Mode) (sites : List Site) (start : Nat)
    (chain : Contiguous mode start sites) (memory : ByteMemory.Memory)
    (whole : ByteMemory.bytesAt memory start (wholeBytes mode sites).length = wholeBytes mode sites) :
    Intact mode sites memory := by
  induction sites generalizing start with
  | nil => intro reader member;cases member
  | cons site sites ih =>
    have first := ByteWindow.packet memory start [] (bytes mode site) (wholeBytes mode sites)
      (by simpa only [wholeBytes,List.flatMap_cons,List.nil_append] using whole)
    have rest := ByteWindow.packet memory start (bytes mode site) (wholeBytes mode sites) []
      (by simpa only [wholeBytes,List.flatMap_cons,List.append_nil] using whole)
    rw [bytes_length,←chain.1] at rest
    have later := ih _ chain.2 rest
    intro reader member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [Current,List.length_nil,Nat.add_zero,chain.1] using first
    · exact later reader member

@[expose] def span (mode : Mode) (sites : List Site) := (sites.map (size mode)).sum

theorem endpoint (mode : Mode) (sites : List Site) (start : Nat)
    (chain : Contiguous mode start sites) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode start) :
    (finish mode sites state).principal.pc = Arithmetic.encodeNat mode (start+span mode sites) := by
  induction sites generalizing start state with
  | nil => simpa only [finish,List.foldl_nil,span,List.map_nil,List.sum_nil,Nat.add_zero] using entry
  | cons site sites ih =>
    have rest := ih _ chain.2 (effect mode site state) rfl
    change (finish mode sites (effect mode site state)).principal.pc = _
    rw [rest,chain.1]
    congr 1
    simp only [span,List.map_cons,List.sum_cons]
    omega

theorem window (mode : Mode) (sites : List Site) (state : StringExecution.State mode) (start count : Nat)
    (outside : ∀ site ∈ sites, site.target+width mode site ≤ start ∨ start+count ≤ site.target) :
    ByteMemory.bytesAt (finish mode sites state).principal.memory start count = ByteMemory.bytesAt state.principal.memory start count := by
  induction sites generalizing state with
  | nil => rfl
  | cons site sites ih =>
    change ByteMemory.bytesAt (finish mode sites (effect mode site state)).principal.memory start count = _
    rw [ih _ (fun reader member => outside reader (List.mem_cons_of_mem _ member)),
      effect_window mode site state start count (outside site (List.mem_cons_self ..))]

theorem registers (mode : Mode) (sites : List Site) (state : StringExecution.State mode) :
    (finish mode sites state).principal.stack = state.principal.stack ∧
    (finish mode sites state).sourceIndex = state.sourceIndex ∧
    (finish mode sites state).destinationIndex = state.destinationIndex ∧
    (finish mode sites state).backwards = state.backwards := by
  induction sites generalizing state with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons site sites ih => exact ih (effect mode site state)

end SmcTuring.Native.ControlPackets
