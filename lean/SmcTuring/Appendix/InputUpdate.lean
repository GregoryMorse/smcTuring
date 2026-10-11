module
public import SmcTuring.Appendix.CursorPatch

public section
namespace SmcTuring.Appendix.InputUpdate
open Native
abbrev Dword := BitVec 32
abbrev Layout := CursorLayout.Layout
@[expose] def body (layout : Layout) : Layout := { layout with start := layout.start+20 }
@[expose] def field (mode : Mode) (layout : Layout) : Nat := CursorPatch.field mode (body layout)
@[expose] def mask (chosen : Bool) : Dword := if chosen then BitVec.allOnes 32 else 0
@[expose] def xorForm (mode : Mode) (layout : Layout) (fresh : Dword) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.bitXor 0 fresh) layout.start (field mode layout)
@[expose] def andForm (mode : Mode) (layout : Layout) (chosen : Bool) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.bitAnd 0 (mask chosen)) (layout.start+10) (field mode layout)
@[expose] def bytes (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool) : List LittleEndian.Byte :=
  DwordArithmetic.encode (xorForm mode layout fresh) ++ DwordArithmetic.encode (andForm mode layout chosen) ++
    CursorImage.bytes mode (body layout) value
@[expose] def span (mode : Mode) : Nat := 20+CursorImage.span mode
@[expose] def image (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool)
    (backing : ByteMemory.Memory) : ByteMemory.Memory :=
  ByteMemory.putBytes backing layout.start (bytes mode layout value fresh chosen)
@[expose] def Intact (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool)
    (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory layout.start (span mode) = bytes mode layout value fresh chosen

structure Valid (mode : Mode) (layout : Layout) : Prop where
  cursor : CursorLayout.Valid mode (body layout)
  cursorOutside : layout.cursor+mode.wordBytes ≤ layout.start ∨ CursorLayout.endPC mode (body layout) ≤ layout.cursor
  tapeOutside : layout.head+10 ≤ layout.start ∨ CursorLayout.endPC mode (body layout) ≤ layout.head+6

@[expose] def xored (mode : Mode) (layout : Layout) (fresh : Dword) (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (xorForm mode layout fresh)) state
@[expose] def masked (mode : Mode) (layout : Layout) (fresh : Dword) (chosen : Bool) (state : Execution.State mode) : Execution.State mode :=
  MixedDword.execute mode (.arithmetic (andForm mode layout chosen)) (xored mode layout fresh state)
@[expose] def program (mode : Mode) (layout : Layout) (old fresh : Dword) (chosen : Bool) : List (MixedDword.Form mode) :=
  [.arithmetic (xorForm mode layout fresh),.arithmetic (andForm mode layout chosen)] ++
    CursorLayout.program mode (body layout) (CursorEffects.delta old fresh chosen)
@[expose] def finish (mode : Mode) (layout : Layout) (old fresh : Dword) (chosen : Bool) (state : Execution.State mode) : Execution.State mode :=
  CursorEffects.finish mode (body layout) (CursorEffects.delta old fresh chosen) (masked mode layout fresh chosen state)

theorem prefix_lengths (mode : Mode) (layout : Layout) (fresh : Dword) (chosen : Bool) :
    (DwordArithmetic.encode (xorForm mode layout fresh)).length = 10 ∧
    (DwordArithmetic.encode (andForm mode layout chosen)).length = 10 := by
  simp only [xorForm,andForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length,and_self]

theorem length (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool) :
    (bytes mode layout value fresh chosen).length = span mode := by
  simp only [bytes,List.length_append,(prefix_lengths mode layout fresh chosen).1,
    (prefix_lengths mode layout fresh chosen).2,CursorImage.length,span]

theorem positions (mode : Mode) (layout : Layout) :
    field mode layout = layout.start+(if mode = .x86 then 29 else 30) ∧
    CursorLayout.endPC mode (body layout) = layout.start+(if mode = .x86 then 39 else 41) := by
  cases mode <;> constructor <;> simp only [field,CursorPatch.field,body,CursorLayout.endPC,CursorLayout.lastPC,
    CursorLayout.middlePC,show CursorLayout.exchangeSize .x86=6 from rfl,
    show CursorLayout.exchangeSize .x64=7 from rfl,ite_true,ite_false,reduceCtorEq] <;> dsimp <;> omega

theorem endpoint (mode : Mode) (layout : Layout) :
    CursorLayout.endPC mode (body layout) = layout.start+span mode := by
  rw [CursorLayout.endpoint]
  dsimp only [body,span,CursorImage.span]
  omega

theorem field_bounds (mode : Mode) (layout : Layout) :
    layout.start+20 ≤ field mode layout ∧ field mode layout+4 ≤ CursorLayout.endPC mode (body layout) := by
  rw [(positions mode layout).1,(positions mode layout).2]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega

theorem field_fits (mode : Mode) (layout : Layout) (valid : Valid mode layout) :
    field mode layout < 2^(8*mode.wordBytes) := by
  have bounds := field_bounds mode layout
  have fits := valid.cursor.codeFits
  omega

theorem xor_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (layout.start+10) (field mode layout) := by
  intro wide
  subst mode
  rw [(positions .x64 layout).1]
  simp only [reduceCtorEq,ite_false]
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem and_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (layout.start+10+10) (field mode layout) := by
  intro wide
  subst mode
  rw [(positions .x64 layout).1]
  simp only [reduceCtorEq,ite_false]
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem initial_intact (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool) (backing : ByteMemory.Memory) :
    Intact mode layout value fresh chosen (image mode layout value fresh chosen backing) := by
  rw [Intact,←length mode layout value fresh chosen]
  exact ByteMemory.bytes_at_put _ _ _

theorem body_current (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value fresh chosen memory) :
    CursorImage.Intact mode (body layout) value memory := by
  have allBytes : ByteMemory.bytesAt memory layout.start (bytes mode layout value fresh chosen).length =
      bytes mode layout value fresh chosen := by simpa only [length,Intact] using intact
  have found := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (xorForm mode layout fresh) ++ DwordArithmetic.encode (andForm mode layout chosen))
    (CursorImage.bytes mode (body layout) value) [] (by simpa [bytes] using allBytes)
  simpa only [List.length_append,(prefix_lengths mode layout fresh chosen).1,
    (prefix_lengths mode layout fresh chosen).2,CursorImage.length,body,CursorImage.Intact] using found

theorem operand (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool) (memory : ByteMemory.Memory)
    (intact : Intact mode layout value fresh chosen memory) :
    DwordCode.get memory (field mode layout) = value :=
  CursorPatch.operand mode (body layout) value memory (body_current mode layout value fresh chosen memory intact)

theorem patch (mode : Mode) (layout : Layout) (old value fresh : Dword) (chosen : Bool) (memory : ByteMemory.Memory)
    (intact : Intact mode layout old fresh chosen memory) :
    Intact mode layout value fresh chosen (DwordCode.put memory (field mode layout) value) := by
  let leading := DwordArithmetic.encode (xorForm mode layout fresh) ++ DwordArithmetic.encode (andForm mode layout chosen) ++
    CursorPatch.leading mode (body layout)
  let trailing := MixedDword.encode mode (CursorLayout.last mode (body layout))
  have spelling (word : Dword) : bytes mode layout word fresh chosen =
      leading ++ LittleEndian.wordEncode 4 word ++ trailing := by
    simp only [bytes,CursorPatch.spelling,leading,trailing,List.append_assoc]
  have initialized : ByteMemory.bytesAt memory layout.start (leading ++ LittleEndian.wordEncode 4 old ++ trailing).length =
      leading ++ LittleEndian.wordEncode 4 old ++ trailing := by
    rw [←spelling,length]
    exact intact
  have patched := BytePatch.current memory layout.start leading
    (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 value) trailing (by simp) initialized
  have position : layout.start+leading.length = field mode layout := by
    simp only [leading,List.length_append,(prefix_lengths mode layout fresh chosen).1,
      (prefix_lengths mode layout fresh chosen).2,CursorPatch.leading_length,field,CursorPatch.field,
      CursorLayout.middlePC,body]
    omega
  rw [position,←spelling,length] at patched
  exact patched

theorem xored_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory) :
    xored mode layout fresh state =
      { state with
        pc := Arithmetic.encodeNat mode (layout.start+10)
        carry := false
        memory := DwordCode.put state.memory (field mode layout) (old ^^^ fresh) } := by
  have effect := DwordArithmetic.located_effect mode (.bitXor 0 fresh) layout.start (field mode layout) state
    rfl entry (xor_range mode layout) (field_fits mode layout valid)
  rw [operand mode layout old fresh chosen state.memory intact] at effect
  simpa only [xored,xorForm,MixedDword.execute,DwordArithmetic.result,DwordArithmetic.flag,DwordArithmetic.length] using effect

theorem xored_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory) :
    Intact mode layout (old ^^^ fresh) fresh chosen (xored mode layout fresh state).memory := by
  rw [xored_effect mode layout valid old fresh chosen state entry intact]
  exact patch mode layout old _ fresh chosen state.memory intact

theorem masked_effect (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory) :
    masked mode layout fresh chosen state =
      { state with
        pc := Arithmetic.encodeNat mode (body layout).start
        carry := false
        memory := DwordCode.put state.memory (field mode layout) (CursorEffects.delta old fresh chosen) } := by
  have firstEffect := xored_effect mode layout valid old fresh chosen state entry intact
  have firstPC : (xored mode layout fresh state).pc = Arithmetic.encodeNat mode (layout.start+10) := by rw [firstEffect]
  have effect := DwordArithmetic.located_effect mode (.bitAnd 0 (mask chosen)) (layout.start+10) (field mode layout)
    (xored mode layout fresh state) rfl firstPC (and_range mode layout) (field_fits mode layout valid)
  rw [operand mode layout (old ^^^ fresh) fresh chosen _ (xored_intact mode layout valid old fresh chosen state entry intact)] at effect
  change masked mode layout fresh chosen state = _ at effect
  rw [effect,firstEffect,DwordCode.put_overwrite]
  simp only [DwordArithmetic.result,DwordArithmetic.flag,DwordArithmetic.length,CursorEffects.delta,mask,body,Nat.add_assoc]

theorem masked_intact (mode : Mode) (layout : Layout) (valid : Valid mode layout) (old fresh : Dword) (chosen : Bool)
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout old fresh chosen state.memory) :
    Intact mode layout (CursorEffects.delta old fresh chosen) fresh chosen (masked mode layout fresh chosen state).memory := by
  rw [masked_effect mode layout valid old fresh chosen state entry intact]
  exact patch mode layout old _ fresh chosen state.memory intact


theorem intact_external (mode : Mode) (layout : Layout) (value fresh : Dword) (chosen : Bool)
    (memory : ByteMemory.Memory) (intact : Intact mode layout value fresh chosen memory)
    (written : Nat) (word : Dword)
    (outside : written+4 ≤ layout.start ∨ CursorLayout.endPC mode (body layout) ≤ written) :
    Intact mode layout value fresh chosen (DwordCode.put memory written word) := by
  rw [Intact,DwordCode.put,ByteMemory.bytes_at_frame]
  · exact intact
  · intro index
    have within := index.isLt
    have endPoint := endpoint mode layout
    simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
    rcases outside with before | after <;> omega

@[expose] def checks (mode : Mode) (layout : Layout) : List Bool :=
  CursorLayout.checks mode (body layout) ++
    [decide (layout.cursor+mode.wordBytes ≤ layout.start ∨ CursorLayout.endPC mode (body layout) ≤ layout.cursor),
     decide (layout.head+10 ≤ layout.start ∨ CursorLayout.endPC mode (body layout) ≤ layout.head+6)]

theorem checks_valid (mode : Mode) (layout : Layout) :
    (checks mode layout).all id = true ↔ Valid mode layout := by
  simp only [checks,List.all_append,List.all_cons,List.all_nil,id_eq,Bool.and_eq_true,and_true,
    decide_eq_true_eq,CursorLayout.checks_valid]
  constructor
  · intro ready
    exact ⟨ready.1,ready.2.1,ready.2.2⟩
  · intro valid
    exact ⟨valid.cursor,valid.cursorOutside,valid.tapeOutside⟩

end SmcTuring.Appendix.InputUpdate
