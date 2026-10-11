module
public import SmcTuring.Appendix.Listing8Prototypes
public import SmcTuring.Native.StringDword
public import SmcTuring.Native.StringInit

public section
namespace SmcTuring.Appendix.Listing8CopiedPointer
open Native Listing8Prototypes

/-- x86 absolute self references retain the original entry; x64's internal
RIP-relative offsets select the physical copied operand instead. -/
@[expose] def origin (mode : Mode) (source copied : Nat) := if mode = .x86 then source else copied
@[expose] def selfField (mode : Mode) (source copied : Nat) := pointerField mode (origin mode source copied)
@[expose] def label (mode : Mode) (source copied : Nat) := ReaderImage.label mode (origin mode source copied)
@[expose] def first (mode : Mode) (source copied : Nat) : Native.Form mode :=
  .memory .exchangeAcc (ReaderImage.firstDisp mode (origin mode source copied))
@[expose] def second (mode : Mode) (source copied : Nat) := Reader.storeForm mode (label mode source copied) (ReaderImage.secondDisp mode)
@[expose] def forms (mode : Mode) (source copied : Nat) (value : Word mode) : List (StringForm.Form mode) :=
  [.native (first mode source copied),.native (second mode source copied),.native .exchangeIndirect,.native (.moffs value)]
@[expose] def finish (mode : Mode) (source copied : Nat) (value : Word mode) (state : StringExecution.State mode) :=
  StringExecution.run mode (forms mode source copied value) state

theorem x64_relocates (source copied : Nat) (value : Word .x64) :
    pointerBytes .x64 source value = pointerBytes .x64 copied value := rfl

theorem encoding (mode : Mode) (source copied : Nat) (value : Word mode) :
    ((forms mode source copied value).map (StringForm.encode mode)).flatten = pointerBytes mode source value := by
  cases mode <;> simp [forms,first,second,label,origin,pointerBytes,ReaderImage.packets,ControlImage.Packet.bytes,
    ReaderImage.firstDisp,ReaderImage.secondDisp,Reader.storeForm,StringForm.encode]

theorem self_value (mode : Mode) (source copied : Nat) (value : Word mode) (memory : ByteMemory.Memory)
    (sourceFits : source+pointerSpan mode < 2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode < 2^(8*mode.wordBytes))
    (sourceCurrent : ByteMemory.bytesAt memory source (pointerBytes mode source value).length = pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt memory copied (pointerBytes mode source value).length = pointerBytes mode source value) :
    Execution.load mode memory (label mode source copied) = value := by
  have fieldFits : selfField mode source copied < 2^(8*mode.wordBytes) := by
    cases mode <;> simp [selfField,pointerField,origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes] at * <;> omega
  change Execution.load mode memory (Arithmetic.encodeNat mode (selfField mode source copied)) = value
  rw [MixedMemory.load_nat mode memory _ fieldFits]
  cases mode with
  | x86 => exact pointer_value .x86 source value memory sourceCurrent
  | x64 => exact pointer_value .x64 copied value memory (by simpa only [x64_relocates source copied value] using copiedCurrent)

theorem first_hits (mode : Mode) (source copied : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode copied) :
    Execution.memoryAddress mode (Execution.nextPC mode (first mode source copied) state)
      (ReaderImage.firstDisp mode (origin mode source copied)) = label mode source copied := by
  cases mode with
  | x86 => rfl
  | x64 => exact ReaderImage.first_hits .x64 copied state entry

theorem second_hits (mode : Mode) (source copied : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode copied) :
    Reader.storeAddress mode (Reader.swapped mode state (ReaderImage.firstDisp mode (origin mode source copied)))
      (label mode source copied) (ReaderImage.secondDisp mode) = label mode source copied := by
  cases mode with
  | x86 => rfl
  | x64 => exact ReaderImage.second_hits .x64 copied state entry

theorem swapped_pc (mode : Mode) (source copied : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode copied) :
    (Reader.swapped mode state (ReaderImage.firstDisp mode (origin mode source copied))).pc =
      Arithmetic.encodeNat mode (copied+ReaderImage.firstSize mode) := by
  have length : instructionLength mode (first mode source copied) = ReaderImage.firstSize mode := by cases mode <;> rfl
  change state.pc+Arithmetic.encodeNat mode (instructionLength mode (first mode source copied)) = _
  rw [entry,length]
  exact BitVec.ofNat_add_ofNat _ _

theorem restored_pc (mode : Mode) (source copied : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode copied) :
    (Reader.restored mode state (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)).pc =
      Arithmetic.encodeNat mode (copied+ReaderImage.firstSize mode+ReaderImage.secondSize mode) := by
  have next : (Reader.restored mode state (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)).pc =
      (Reader.swapped mode state (ReaderImage.firstDisp mode (origin mode source copied))).pc+Arithmetic.encodeNat mode (ReaderImage.secondSize mode) := by cases mode <;> rfl
  rw [next,swapped_pc mode source copied state entry]
  exact BitVec.ofNat_add_ofNat _ _

theorem dereferenced_pc (mode : Mode) (source copied : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode copied) :
    (Reader.dereferenced mode state (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)).pc =
      Arithmetic.encodeNat mode (copied+ReaderImage.prefixSize mode) := by
  change (Reader.restored mode state (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)).pc+
    Arithmetic.encodeNat mode (instructionLength mode .exchangeIndirect) = _
  rw [restored_pc mode source copied state entry]
  unfold Arithmetic.encodeNat
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  cases mode <;> simp [instructionLength,wordPrefix,ReaderImage.firstSize,ReaderImage.secondSize,ReaderImage.prefixSize,Nat.add_assoc]

theorem reader_pc (mode : Mode) (source copied : Nat) (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode copied) :
    (Reader.finish mode state (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)).pc =
      Arithmetic.encodeNat mode (copied+pointerSpan mode) := by
  change (Reader.dereferenced mode state (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)).pc+
    Arithmetic.encodeNat mode (instructionLength mode (.moffs (Execution.load mode state.memory (label mode source copied)))) = _
  rw [dereferenced_pc mode source copied state entry]
  unfold Arithmetic.encodeNat
  rw [BitVec.ofNat_add_ofNat]
  congr 1
  cases mode <;> simp [instructionLength,wordPrefix,ReaderImage.prefixSize,pointerSpan,ReaderImage.totalSize,Mode.wordBytes,Nat.add_assoc]

theorem run_reader (mode : Mode) (source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (pointer : Execution.load mode state.principal.memory (label mode source copied) = value) :
    finish mode source copied value state = { state with
      principal := Reader.finish mode state.principal (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode) } := by
  change StringExecution.run mode ([first mode source copied,second mode source copied,.exchangeIndirect,.moffs value].map StringForm.Form.native) state = _
  rw [StringInit.native_run]
  unfold Reader.finish Reader.dereferenced Reader.restored Reader.swapped
  rw [pointer]
  rfl

/-- Exact restored whole-memory effect, including arbitrary pointer aliases.
The static byte-separation conditions are needed only by the live fetch proof. -/
theorem effect (mode : Mode) (source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode copied)
    (pointer : Execution.load mode state.principal.memory (label mode source copied) = value) :
    finish mode source copied value state = { state with principal := {state.principal with
      pc := Arithmetic.encodeNat mode (copied+pointerSpan mode)
      accumulator := Execution.load mode state.principal.memory value } } := by
  have a := first_hits mode source copied state.principal entry
  have b := second_hits mode source copied state.principal entry
  have pc := reader_pc mode source copied state.principal entry
  have mem := Reader.finish_memory mode state.principal _ _ _ a b
  have ax := Reader.finish_accumulator mode state.principal _ _ _ a b
  have sp := Reader.finish_stack mode state.principal (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)
  have cf := Reader.finish_carry mode state.principal (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)
  rw [pointer] at ax
  rw [run_reader mode source copied value state pointer]
  have principal : Reader.finish mode state.principal (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode) =
      {state.principal with pc := Arithmetic.encodeNat mode (copied+pointerSpan mode),accumulator := Execution.load mode state.principal.memory value} := by
    cases finished : Reader.finish mode state.principal (label mode source copied) (ReaderImage.firstDisp mode (origin mode source copied)) (ReaderImage.secondDisp mode)
    simp only [finished] at pc mem ax sp cf
    simp only [pc,mem,ax,sp,cf]
  rw [principal]

/-- All four current-byte fetches follow from the original and copied windows,
restoration and static word/packet separation. No later fetched form is a premise. -/
theorem trace (mode : Mode) (source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode < 2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode < 2^(8*mode.wordBytes))
    (sourceOutside : source+pointerSpan mode ≤ copied ∨ copied+pointerSpan mode ≤ source)
    (targetOutside : value.toNat+mode.wordBytes ≤ copied ∨ copied+pointerSpan mode ≤ value.toNat)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length = pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length = pointerBytes mode source value) :
    StringExecution.Trace mode state (forms mode source copied value) (finish mode source copied value state) := by
  let a := Native.encode mode (first mode source copied)
  let b := Native.encode mode (second mode source copied)
  let c := Native.encode mode .exchangeIndirect
  let d := Native.encode mode (.moffs value)
  have shape : pointerBytes mode source value = a++b++c++d := by
    simpa only [forms,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,StringForm.encode,List.append_assoc] using (encoding mode source copied value).symm
  have code : ByteMemory.bytesAt state.principal.memory copied (a++b++c++d).length = a++b++c++d := by rw [←shape];exact copiedCurrent
  let swapped := StringExecution.execute mode (.native (first mode source copied)) state
  let restored := StringExecution.execute mode (.native (second mode source copied)) swapped
  let dereferenced := StringExecution.execute mode (.native .exchangeIndirect) restored
  have pointer := self_value mode source copied value state.principal.memory sourceFits copiedFits sourceCurrent copiedCurrent
  have firstHits := first_hits mode source copied state.principal entry
  have secondHits := second_hits mode source copied state.principal entry
  have fieldFits : selfField mode source copied < 2^(8*mode.wordBytes) := by
    cases mode <;> simp [selfField,pointerField,origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes] at * <;> omega
  have pc1 : swapped.principal.pc = Arithmetic.encodeNat mode (copied+ReaderImage.firstSize mode) := swapped_pc mode source copied state.principal entry
  have pc2 : restored.principal.pc = Arithmetic.encodeNat mode (copied+ReaderImage.firstSize mode+ReaderImage.secondSize mode) := restored_pc mode source copied state.principal entry
  have pc3 : dereferenced.principal.pc = Arithmetic.encodeNat mode (copied+ReaderImage.prefixSize mode) := dereferenced_pc mode source copied state.principal entry
  have mem1 : swapped.principal.memory = ByteMemory.putWord mode state.principal.memory (selfField mode source copied) state.principal.accumulator := by
    have e := congrArg Execution.State.memory (Reader.exchange_effect mode state.principal (label mode source copied) _ firstHits)
    change swapped.principal.memory = ByteMemory.putWord mode state.principal.memory (Arithmetic.encodeNat mode (selfField mode source copied)).toNat state.principal.accumulator at e
    rw [Arithmetic.encode_nat_toNat mode _ fieldFits] at e
    exact e
  have mem2 : restored.principal.memory = state.principal.memory := Reader.restored_memory mode state.principal _ _ _ firstHits secondHits
  have mem3 : dereferenced.principal.memory = ByteMemory.putWord mode state.principal.memory value.toNat value := by
    have e := Reader.dereferenced_memory mode state.principal _ _ _ firstHits secondHits
    rw [pointer] at e
    exact e
  have head : ByteMemory.bytesAt state.principal.memory copied a.length = a := by
    simpa only [List.nil_append,List.length_nil,Nat.add_zero] using ByteWindow.packet _ copied [] a (b++c++d) (by simpa only [List.append_assoc,List.nil_append] using code)
  have secondBefore : ByteMemory.bytesAt state.principal.memory (copied+ReaderImage.firstSize mode) b.length = b := by
    have p := ByteWindow.packet _ copied a b (c++d) (by simpa only [List.append_assoc] using code)
    have len : a.length = ReaderImage.firstSize mode := by cases mode <;> rfl
    simpa only [len] using p
  have thirdBefore : ByteMemory.bytesAt state.principal.memory (copied+ReaderImage.firstSize mode+ReaderImage.secondSize mode) c.length = c := by
    have p := ByteWindow.packet _ copied (a++b) c d code
    have len : (a++b).length = ReaderImage.firstSize mode+ReaderImage.secondSize mode := by cases mode <;> rfl
    simpa only [len,Nat.add_assoc] using p
  have lastBefore : ByteMemory.bytesAt state.principal.memory (copied+ReaderImage.prefixSize mode) d.length = d := by
    have p := ByteWindow.packet _ copied (a++b++c) d [] (by simpa only [List.append_nil] using code)
    have len : (a++b++c).length = ReaderImage.prefixSize mode := by cases mode <;> rfl
    simpa only [len] using p
  have fits1 : copied+ReaderImage.firstSize mode < 2^(8*mode.wordBytes) := by cases mode <;> simp [pointerSpan,ReaderImage.totalSize,ReaderImage.firstSize] at * <;> omega
  have fits2 : copied+ReaderImage.firstSize mode+ReaderImage.secondSize mode < 2^(8*mode.wordBytes) := by cases mode <;> simp [pointerSpan,ReaderImage.totalSize,ReaderImage.firstSize,ReaderImage.secondSize] at * <;> omega
  have fits3 : copied+ReaderImage.prefixSize mode < 2^(8*mode.wordBytes) := by cases mode <;> simp [pointerSpan,ReaderImage.totalSize,ReaderImage.prefixSize] at * <;> omega
  have fetched : StringForm.fetch mode state.principal.memory state.principal.pc.toNat = some (.native (first mode source copied)) := by
    rw [entry,Arithmetic.encode_nat_toNat mode _ (by omega)]
    exact StringForm.fetch_current_encoding mode _ _ _ (by trivial) head
  have nextFetched : StringForm.fetch mode swapped.principal.memory swapped.principal.pc.toNat = some (.native (second mode source copied)) := by
    rw [pc1,Arithmetic.encode_nat_toNat mode _ fits1]
    apply StringForm.fetch_current_encoding mode _ _ _ (by trivial)
    rw [mem1]
    change ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory (selfField mode source copied) state.principal.accumulator) (copied+ReaderImage.firstSize mode) b.length = b
    have outside : ∀ i : Fin b.length, ¬ByteMemory.Inside (selfField mode source copied) mode.wordBytes (copied+ReaderImage.firstSize mode+i.val) := by
      intro i
      have bound := i.isLt
      have len : b.length = ReaderImage.secondSize mode := by cases mode <;> rfl
      have smaller : i.val < ReaderImage.secondSize mode := by simpa only [len] using bound
      cases mode <;> simp [selfField,pointerField,origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,ReaderImage.firstSize,ReaderImage.secondSize,Mode.wordBytes,ByteMemory.Inside] at * <;> omega
    rw [show ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory (selfField mode source copied) state.principal.accumulator) (copied+ReaderImage.firstSize mode) b.length =
        ByteMemory.bytesAt state.principal.memory (copied+ReaderImage.firstSize mode) b.length from ByteMemory.bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)]
    exact secondBefore
  have thirdFetched : StringForm.fetch mode restored.principal.memory restored.principal.pc.toNat = some (.native .exchangeIndirect) := by
    rw [pc2,Arithmetic.encode_nat_toNat mode _ fits2,mem2]
    exact StringForm.fetch_current_encoding mode _ _ _ (by trivial) thirdBefore
  have lastFetched : StringForm.fetch mode dereferenced.principal.memory dereferenced.principal.pc.toNat = some (.native (.moffs value)) := by
    rw [pc3,Arithmetic.encode_nat_toNat mode _ fits3]
    apply StringForm.fetch_current_encoding mode _ _ _ (by trivial)
    rw [mem3]
    change ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory value.toNat value) (copied+ReaderImage.prefixSize mode) d.length = d
    have outside : ∀ i : Fin d.length, ¬ByteMemory.Inside value.toNat mode.wordBytes (copied+ReaderImage.prefixSize mode+i.val) := by
      intro i
      have bound := i.isLt
      have len : ReaderImage.prefixSize mode+d.length = pointerSpan mode := by cases mode <;> rfl
      simp only [ByteMemory.Inside]
      rcases targetOutside with before | after <;> omega
    rw [show ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory value.toNat value) (copied+ReaderImage.prefixSize mode) d.length =
        ByteMemory.bytesAt state.principal.memory (copied+ReaderImage.prefixSize mode) d.length from ByteMemory.bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)]
    exact lastBefore
  exact .step fetched (.step nextFetched (.step thirdFetched (.step lastFetched (.nil _))))

theorem unified_trace (mode : Mode) (source copied : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc = Arithmetic.encodeNat mode copied)
    (sourceFits : source+pointerSpan mode < 2^(8*mode.wordBytes))
    (copiedFits : copied+pointerSpan mode < 2^(8*mode.wordBytes))
    (sourceOutside : source+pointerSpan mode ≤ copied ∨ copied+pointerSpan mode ≤ source)
    (targetOutside : value.toNat+mode.wordBytes ≤ copied ∨ copied+pointerSpan mode ≤ value.toNat)
    (sourceCurrent : ByteMemory.bytesAt state.principal.memory source (pointerBytes mode source value).length = pointerBytes mode source value)
    (copiedCurrent : ByteMemory.bytesAt state.principal.memory copied (pointerBytes mode source value).length = pointerBytes mode source value) :
    StringDword.Trace mode state ((forms mode source copied value).map StringDword.Form.string) (finish mode source copied value state) :=
  StringDword.string_trace mode (trace mode source copied value state entry sourceFits copiedFits sourceOutside targetOutside sourceCurrent copiedCurrent)

end SmcTuring.Appendix.Listing8CopiedPointer
