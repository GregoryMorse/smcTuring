module
public import SmcTuring.Native.StringInit

public section
namespace SmcTuring.Native.StringInitTrace
open StringExecution LittleEndian

/-- Complete initialized DEFDATA trace. The x64 reader's temporary complete
word write is outside the initializer packets; all cursor/opcode fetch safety
is derived from the original image and static region separation. -/
theorem trace (mode : Mode) (start initial : Nat) (state : State mode)
    (location : state.principal.pc = Arithmetic.encodeNat mode start)
    (codeFits : start+StringCodec.initialSize mode < 2^(8*mode.wordBytes))
    (targetFits : initial+mode.wordBytes < 2^(8*mode.wordBytes))
    (separate : initial+mode.wordBytes ≤ start ∨ start+StringCodec.initialSize mode ≤ initial)
    (current : ByteMemory.bytesAt state.principal.memory start (StringCodec.initialSize mode) = StringInit.bytes mode start initial) :
    Trace mode state (StringInit.forms mode start initial) (run mode (StringInit.forms mode start initial) state) := by
  have startFits : start < 2^(8*mode.wordBytes) := by omega
  cases mode with
  | x86 =>
    have fetched : StringForm.fetch .x86 state.principal.memory state.principal.pc.toNat =
        some (.initialize32 (BitVec.ofNat 32 (StringInit.field .x86 start)) (BitVec.ofNat 32 initial)) := by
      rw [location,Arithmetic.encode_nat_toNat .x86 start startFits]
      apply StringForm.fetch_current_encoding .x86 _ _ (.initialize32 (BitVec.ofNat 32 (StringInit.field .x86 start)) (BitVec.ofNat 32 initial)) rfl
      exact current
    exact .step fetched (.nil _)
  | x64 =>
    change start+27 < 2^64 at codeFits
    change initial+8 < 2^64 at targetFits
    change start < 2^64 at startFits
    change initial+8 ≤ start ∨ start+27 ≤ initial at separate
    let first : Native.Form .x64 := .memory .exchangeAcc 12
    let second : Native.Form .x64 := .memory .storeAcc 5
    let third : Native.Form .x64 := .exchangeIndirect
    let last : Native.Form .x64 := .moffs (Arithmetic.encodeNat .x64 initial)
    let a := Native.encode .x64 first
    let b := Native.encode .x64 second
    let c := Native.encode .x64 third
    let d := Native.encode .x64 last
    have shape : StringInit.bytes .x64 start initial = a++b++c++d := by
      have encoded := StringInit.forms_encoding .x64 start initial
      simpa only [StringInit.forms,StringInit.first_displacement,StringInit.second_displacement,List.map_cons,List.map_nil,
        List.flatten_cons,List.flatten_nil,List.append_nil,StringForm.encode,List.append_assoc] using encoded.symm
    have code : ByteMemory.bytesAt state.principal.memory start (a++b++c++d).length = a++b++c++d := by
      rw [←shape]
      change ByteMemory.bytesAt state.principal.memory start (StringCodec.initialBytes .x64 start (StringInit.field .x64 start) initial).length = _
      rw [StringCodec.initial_length]
      exact current
    let swapped := execute .x64 (.native first) state
    let restored := execute .x64 (.native second) swapped
    let dereferenced := execute .x64 (.native third) restored
    have pointer := StringInit.initialized_pointer .x64 start initial state.principal.memory codeFits current
    change Execution.load .x64 state.principal.memory (ReaderImage.label .x64 start) = Arithmetic.encodeNat .x64 initial at pointer
    have firstHits := ReaderImage.first_hits .x64 start state.principal location
    have secondHits := ReaderImage.second_hits .x64 start state.principal location
    have fieldFits : start+19 < 2^64 := by change start+27 < 2^64 at codeFits; omega
    have pc1 : swapped.principal.pc = Arithmetic.encodeNat .x64 (start+7) := ReaderImage.swapped_pc .x64 start state.principal location
    have pc2 : restored.principal.pc = Arithmetic.encodeNat .x64 (start+14) := by
      have position := ReaderImage.restored_pc .x64 start state.principal location
      change restored.principal.pc = Arithmetic.encodeNat .x64 (start+7+7) at position
      rw [show start+7+7 = start+14 by omega] at position
      exact position
    have pc3 : dereferenced.principal.pc = Arithmetic.encodeNat .x64 (start+17) := ReaderImage.dereferenced_pc .x64 start state.principal location
    have mem1 : swapped.principal.memory = ByteMemory.putWord .x64 state.principal.memory (start+19) state.principal.accumulator := by
      have effect := Reader.exchange_effect .x64 state.principal (ReaderImage.label .x64 start) 12 firstHits
      have projected := congrArg Execution.State.memory effect
      change swapped.principal.memory = ByteMemory.putWord .x64 state.principal.memory (Arithmetic.encodeNat .x64 (start+19)).toNat state.principal.accumulator at projected
      rw [Arithmetic.encode_nat_toNat .x64 _ fieldFits] at projected
      exact projected
    have mem2 : restored.principal.memory = state.principal.memory := Reader.restored_memory .x64 state.principal
      (ReaderImage.label .x64 start) 12 5 firstHits secondHits
    have mem3 : dereferenced.principal.memory = ByteMemory.putWord .x64 state.principal.memory initial (Arithmetic.encodeNat .x64 initial) := by
      have effect := Reader.dereferenced_memory .x64 state.principal (ReaderImage.label .x64 start) 12 5 firstHits secondHits
      rw [pointer,Arithmetic.encode_nat_toNat .x64 initial (by change initial < 2^64; omega)] at effect
      exact effect
    have head : ByteMemory.bytesAt state.principal.memory start a.length = a := by
      simpa only [List.nil_append,List.length_nil,Nat.add_zero] using StringWindow.packet_window state.principal.memory start [] a (b++c++d)
        (by simpa only [List.append_assoc,List.nil_append] using code)
    have secondBefore : ByteMemory.bytesAt state.principal.memory (start+7) b.length = b := by
      have exactWindow := StringWindow.packet_window state.principal.memory start a b (c++d)
        (by simpa only [List.append_assoc] using code)
      exact exactWindow
    have thirdBefore : ByteMemory.bytesAt state.principal.memory (start+14) c.length = c := by
      have exactWindow := StringWindow.packet_window state.principal.memory start (a++b) c d code
      exact exactWindow
    have lastBefore : ByteMemory.bytesAt state.principal.memory (start+17) d.length = d := by
      have exactWindow := StringWindow.packet_window state.principal.memory start (a++b++c) d []
        (by simpa only [List.append_nil] using code)
      exact exactWindow
    have fetched : StringForm.fetch .x64 state.principal.memory state.principal.pc.toNat = some (.native first) := by
      rw [location,Arithmetic.encode_nat_toNat .x64 start startFits]
      exact StringForm.fetch_current_encoding .x64 _ start (.native first) (by trivial) head
    have nextFetched : StringForm.fetch .x64 swapped.principal.memory swapped.principal.pc.toNat = some (.native second) := by
      rw [pc1,Arithmetic.encode_nat_toNat .x64 (start+7) (by change start+7 < 2^64; omega)]
      apply StringForm.fetch_current_encoding .x64 _ _ _ (by trivial)
      rw [mem1]
      change ByteMemory.bytesAt (ByteMemory.putBytes state.principal.memory (start+19) (wordEncode 8 state.principal.accumulator)) (start+7) 7 = b
      rw [ByteMemory.bytes_at_frame state.principal.memory (start+19) (wordEncode 8 state.principal.accumulator) (start+7) 7 (by
        intro index
        have small := index.isLt
        change ¬ByteMemory.Inside (start+19) 8 (start+7+index.val)
        unfold ByteMemory.Inside
        omega)]
      exact secondBefore
    have thirdFetched : StringForm.fetch .x64 restored.principal.memory restored.principal.pc.toNat = some (.native third) := by
      rw [pc2,Arithmetic.encode_nat_toNat .x64 (start+14) (by change start+14 < 2^64; omega),mem2]
      exact StringForm.fetch_current_encoding .x64 _ _ (.native third) (by trivial) thirdBefore
    have lastFetched : StringForm.fetch .x64 dereferenced.principal.memory dereferenced.principal.pc.toNat = some (.native last) := by
      rw [pc3,Arithmetic.encode_nat_toNat .x64 (start+17) (by change start+17 < 2^64; omega)]
      apply StringForm.fetch_current_encoding .x64 _ _ _ (by trivial)
      rw [mem3]
      change ByteMemory.bytesAt (ByteMemory.putBytes state.principal.memory initial (wordEncode 8 (Arithmetic.encodeNat .x64 initial))) (start+17) 10 = d
      rw [ByteMemory.bytes_at_frame state.principal.memory initial (wordEncode 8 (Arithmetic.encodeNat .x64 initial)) (start+17) 10 (by
        intro index
        have small := index.isLt
        change ¬ByteMemory.Inside initial 8 (start+17+index.val)
        unfold ByteMemory.Inside
        rcases separate with before | after <;> omega)]
      exact lastBefore
    have actualForms : StringInit.forms .x64 start initial = [.native first,.native second,.native third,.native last] := by
      simp only [StringInit.forms,StringInit.first_displacement,StringInit.second_displacement]
      rfl
    rw [actualForms]
    exact .step fetched (.step nextFetched (.step thirdFetched (.step lastFetched (.nil _))))

end SmcTuring.Native.StringInitTrace
