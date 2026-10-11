module
public import SmcTuring.Appendix.Listing8CopiedPointer

public section
namespace SmcTuring.Appendix.Listing8OriginalPointer
open Native Listing8Prototypes Listing8CopiedPointer
/-- Original M01 DEFADDR executes directly at its own compiled entry. Its
self-field exchanges are before later fetches and restore the complete memory. -/
theorem trace (mode : Mode) (pc : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (fits : pc+pointerSpan mode<2^(8*mode.wordBytes))
    (targetOutside : value.toNat+mode.wordBytes ≤ pc ∨ pc+pointerSpan mode ≤ value.toNat)
    (current : ByteMemory.bytesAt state.principal.memory pc (pointerBytes mode pc value).length=pointerBytes mode pc value) :
    StringExecution.Trace mode state (forms mode pc pc value) (finish mode pc pc value state) := by
  have sourceFits:=fits
  have copiedFits:=fits
  have sourceCurrent:=current
  have copiedCurrent:=current
  let a := Native.encode mode (first mode pc pc)
  let b := Native.encode mode (second mode pc pc)
  let c := Native.encode mode .exchangeIndirect
  let d := Native.encode mode (.moffs value)
  have shape : pointerBytes mode pc value = a++b++c++d := by
    simpa only [forms,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,StringForm.encode,List.append_assoc] using (encoding mode pc pc value).symm
  have code : ByteMemory.bytesAt state.principal.memory pc (a++b++c++d).length = a++b++c++d := by rw [←shape];exact copiedCurrent
  let swapped := StringExecution.execute mode (.native (first mode pc pc)) state
  let restored := StringExecution.execute mode (.native (second mode pc pc)) swapped
  let dereferenced := StringExecution.execute mode (.native .exchangeIndirect) restored
  have pointer := self_value mode pc pc value state.principal.memory sourceFits copiedFits sourceCurrent copiedCurrent
  have firstHits := first_hits mode pc pc state.principal entry
  have secondHits := second_hits mode pc pc state.principal entry
  have fieldFits : selfField mode pc pc < 2^(8*mode.wordBytes) := by
    cases mode <;> simp [selfField,pointerField,origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,Mode.wordBytes] at * <;> omega
  have pc1 : swapped.principal.pc = Arithmetic.encodeNat mode (pc+ReaderImage.firstSize mode) := swapped_pc mode pc pc state.principal entry
  have pc2 : restored.principal.pc = Arithmetic.encodeNat mode (pc+ReaderImage.firstSize mode+ReaderImage.secondSize mode) := restored_pc mode pc pc state.principal entry
  have pc3 : dereferenced.principal.pc = Arithmetic.encodeNat mode (pc+ReaderImage.prefixSize mode) := dereferenced_pc mode pc pc state.principal entry
  have mem1 : swapped.principal.memory = ByteMemory.putWord mode state.principal.memory (selfField mode pc pc) state.principal.accumulator := by
    have e := congrArg Execution.State.memory (Reader.exchange_effect mode state.principal (label mode pc pc) _ firstHits)
    change swapped.principal.memory = ByteMemory.putWord mode state.principal.memory (Arithmetic.encodeNat mode (selfField mode pc pc)).toNat state.principal.accumulator at e
    rw [Arithmetic.encode_nat_toNat mode _ fieldFits] at e
    exact e
  have mem2 : restored.principal.memory = state.principal.memory := Reader.restored_memory mode state.principal _ _ _ firstHits secondHits
  have mem3 : dereferenced.principal.memory = ByteMemory.putWord mode state.principal.memory value.toNat value := by
    have e := Reader.dereferenced_memory mode state.principal _ _ _ firstHits secondHits
    rw [pointer] at e
    exact e
  have head : ByteMemory.bytesAt state.principal.memory pc a.length = a := by
    simpa only [List.nil_append,List.length_nil,Nat.add_zero] using ByteWindow.packet _ pc [] a (b++c++d) (by simpa only [List.append_assoc,List.nil_append] using code)
  have secondBefore : ByteMemory.bytesAt state.principal.memory (pc+ReaderImage.firstSize mode) b.length = b := by
    have p := ByteWindow.packet _ pc a b (c++d) (by simpa only [List.append_assoc] using code)
    have len : a.length = ReaderImage.firstSize mode := by cases mode <;> rfl
    simpa only [len] using p
  have thirdBefore : ByteMemory.bytesAt state.principal.memory (pc+ReaderImage.firstSize mode+ReaderImage.secondSize mode) c.length = c := by
    have p := ByteWindow.packet _ pc (a++b) c d code
    have len : (a++b).length = ReaderImage.firstSize mode+ReaderImage.secondSize mode := by cases mode <;> rfl
    simpa only [len,Nat.add_assoc] using p
  have lastBefore : ByteMemory.bytesAt state.principal.memory (pc+ReaderImage.prefixSize mode) d.length = d := by
    have p := ByteWindow.packet _ pc (a++b++c) d [] (by simpa only [List.append_nil] using code)
    have len : (a++b++c).length = ReaderImage.prefixSize mode := by cases mode <;> rfl
    simpa only [len] using p
  have fits1 : pc+ReaderImage.firstSize mode < 2^(8*mode.wordBytes) := by cases mode <;> simp [pointerSpan,ReaderImage.totalSize,ReaderImage.firstSize] at * <;> omega
  have fits2 : pc+ReaderImage.firstSize mode+ReaderImage.secondSize mode < 2^(8*mode.wordBytes) := by cases mode <;> simp [pointerSpan,ReaderImage.totalSize,ReaderImage.firstSize,ReaderImage.secondSize] at * <;> omega
  have fits3 : pc+ReaderImage.prefixSize mode < 2^(8*mode.wordBytes) := by cases mode <;> simp [pointerSpan,ReaderImage.totalSize,ReaderImage.prefixSize] at * <;> omega
  have fetched : StringForm.fetch mode state.principal.memory state.principal.pc.toNat = some (.native (first mode pc pc)) := by
    rw [entry,Arithmetic.encode_nat_toNat mode _ (by omega)]
    exact StringForm.fetch_current_encoding mode _ _ _ (by trivial) head
  have nextFetched : StringForm.fetch mode swapped.principal.memory swapped.principal.pc.toNat = some (.native (second mode pc pc)) := by
    rw [pc1,Arithmetic.encode_nat_toNat mode _ fits1]
    apply StringForm.fetch_current_encoding mode _ _ _ (by trivial)
    rw [mem1]
    change ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory (selfField mode pc pc) state.principal.accumulator) (pc+ReaderImage.firstSize mode) b.length = b
    have outside : ∀ i : Fin b.length, ¬ByteMemory.Inside (selfField mode pc pc) mode.wordBytes (pc+ReaderImage.firstSize mode+i.val) := by
      intro i
      have bound := i.isLt
      have len : b.length = ReaderImage.secondSize mode := by cases mode <;> rfl
      have smaller : i.val < ReaderImage.secondSize mode := by simpa only [len] using bound
      cases mode <;> simp [selfField,pointerField,origin,pointerSpan,ReaderImage.labelOffset,ReaderImage.totalSize,ReaderImage.firstSize,ReaderImage.secondSize,Mode.wordBytes,ByteMemory.Inside] at * <;> omega
    rw [show ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory (selfField mode pc pc) state.principal.accumulator) (pc+ReaderImage.firstSize mode) b.length =
        ByteMemory.bytesAt state.principal.memory (pc+ReaderImage.firstSize mode) b.length from ByteMemory.bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)]
    exact secondBefore
  have thirdFetched : StringForm.fetch mode restored.principal.memory restored.principal.pc.toNat = some (.native .exchangeIndirect) := by
    rw [pc2,Arithmetic.encode_nat_toNat mode _ fits2,mem2]
    exact StringForm.fetch_current_encoding mode _ _ _ (by trivial) thirdBefore
  have lastFetched : StringForm.fetch mode dereferenced.principal.memory dereferenced.principal.pc.toNat = some (.native (.moffs value)) := by
    rw [pc3,Arithmetic.encode_nat_toNat mode _ fits3]
    apply StringForm.fetch_current_encoding mode _ _ _ (by trivial)
    rw [mem3]
    change ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory value.toNat value) (pc+ReaderImage.prefixSize mode) d.length = d
    have outside : ∀ i : Fin d.length, ¬ByteMemory.Inside value.toNat mode.wordBytes (pc+ReaderImage.prefixSize mode+i.val) := by
      intro i
      have bound := i.isLt
      have len : ReaderImage.prefixSize mode+d.length = pointerSpan mode := by cases mode <;> rfl
      simp only [ByteMemory.Inside]
      rcases targetOutside with before | after <;> omega
    rw [show ByteMemory.bytesAt (ByteMemory.putWord mode state.principal.memory value.toNat value) (pc+ReaderImage.prefixSize mode) d.length =
        ByteMemory.bytesAt state.principal.memory (pc+ReaderImage.prefixSize mode) d.length from ByteMemory.bytes_at_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length] using outside)]
    exact lastBefore
  exact .step fetched (.step nextFetched (.step thirdFetched (.step lastFetched (.nil _))))

theorem unified_trace (mode : Mode) (pc : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (fits : pc+pointerSpan mode<2^(8*mode.wordBytes))
    (targetOutside : value.toNat+mode.wordBytes ≤ pc ∨ pc+pointerSpan mode ≤ value.toNat)
    (current : ByteMemory.bytesAt state.principal.memory pc (pointerBytes mode pc value).length=pointerBytes mode pc value) :
    StringDword.Trace mode state ((forms mode pc pc value).map StringDword.Form.string) (finish mode pc pc value state) :=
  StringDword.string_trace mode (trace mode pc value state entry fits targetOutside current)

theorem effect (mode : Mode) (pc : Nat) (value : Word mode) (state : StringExecution.State mode)
    (entry : state.principal.pc=Arithmetic.encodeNat mode pc)
    (fits : pc+pointerSpan mode<2^(8*mode.wordBytes))
    (current : ByteMemory.bytesAt state.principal.memory pc (pointerBytes mode pc value).length=pointerBytes mode pc value) :
    finish mode pc pc value state={state with principal:={state.principal with
      pc:=Arithmetic.encodeNat mode (pc+pointerSpan mode)
      accumulator:=Execution.load mode state.principal.memory value}} :=
  Listing8CopiedPointer.effect mode pc pc value state entry
    (self_value mode pc pc value state.principal.memory fits fits current current)
end SmcTuring.Appendix.Listing8OriginalPointer
