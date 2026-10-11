module
public import SmcTuring.Appendix.InputUpdateTrace
public import SmcTuring.Appendix.InputDword
public import SmcTuring.Appendix.DwordComparison
public import SmcTuring.Native.DwordOwner

public section
namespace SmcTuring.Appendix.Listing8InputPrefix
open Native
abbrev Dword := BitVec 32

/-- The literal mask-reset, M13, M14, comparison and input-update order.
The tape cursor and head are the existing full-width node fields. -/
structure Layout where
  start : Nat
  cursor : Nat
  head : Nat

@[expose] def copyStart (layout : Layout) : Nat := layout.start + 10
@[expose] def ownerPC (mode : Mode) (layout : Layout) : Nat :=
  copyStart layout + DwordLayout.span mode
@[expose] def scalarField (mode : Mode) (layout : Layout) : Nat := ownerPC mode layout + 6
@[expose] def subPC (mode : Mode) (layout : Layout) : Nat := ownerPC mode layout + 10
@[expose] def sourceField (mode : Mode) (layout : Layout) : Nat := subPC mode layout + 6
@[expose] def negPC (mode : Mode) (layout : Layout) : Nat := subPC mode layout + 10
@[expose] def sbbPC (mode : Mode) (layout : Layout) : Nat := negPC mode layout + 6
@[expose] def notPC (mode : Mode) (layout : Layout) : Nat := sbbPC mode layout + 7
/-- Contiguous extracted input fragment. The two printed mask-distribution
calls between NOT and the update are separate composition work; see
Listing8MaskCopy for their corrected sources and additional span. -/
@[expose] def updateStart (mode : Mode) (layout : Layout) : Nat := notPC mode layout + 6
@[expose] def updateLayout (mode : Mode) (layout : Layout) : InputUpdate.Layout :=
  { start := updateStart mode layout, cursor := layout.cursor, head := layout.head }
@[expose] def maskField (mode : Mode) (layout : Layout) : Nat := updateStart mode layout + 16
@[expose] def pendingField (mode : Mode) (layout : Layout) : Nat :=
  InputUpdate.field mode (updateLayout mode layout)
@[expose] def copyLayout (mode : Mode) (layout : Layout) : DwordLayout.Layout :=
  { start := copyStart layout, source := sourceField mode layout,
    destination := pendingField mode layout }
@[expose] def endPC (mode : Mode) (layout : Layout) : Nat :=
  updateStart mode layout + InputUpdate.span mode

/-- The copied source is the later SUB immediate. M13 restores that word
before SUB is fetched; its destination is the later tape-XOR immediate. -/
theorem copy_fields (mode : Mode) (layout : Layout) :
    (copyLayout mode layout).source = subPC mode layout + 6 ∧
    (copyLayout mode layout).destination = InputUpdate.field mode (updateLayout mode layout) :=
  ⟨rfl,rfl⟩

theorem owner_and_mask_fields (mode : Mode) (layout : Layout) :
    scalarField mode layout = ownerPC mode layout + 6 ∧
    maskField mode layout = updateStart mode layout + 16 := ⟨rfl,rfl⟩

theorem stage_boundaries (mode : Mode) (layout : Layout) :
    DwordLayout.endPC mode (copyLayout mode layout) = ownerPC mode layout ∧
    ownerPC mode layout + 10 = subPC mode layout ∧
    notPC mode layout + 6 = updateStart mode layout := by
  constructor
  · rw [DwordLayout.endpoint]
    rfl
  constructor <;> rfl

theorem positions (mode : Mode) (layout : Layout) :
    ownerPC mode layout = layout.start + (if mode = .x86 then 27 else 28) ∧
    scalarField mode layout = layout.start + (if mode = .x86 then 33 else 34) ∧
    subPC mode layout = layout.start + (if mode = .x86 then 37 else 38) ∧
    sourceField mode layout = layout.start + (if mode = .x86 then 43 else 44) ∧
    updateStart mode layout = layout.start + (if mode = .x86 then 66 else 67) ∧
    maskField mode layout = layout.start + (if mode = .x86 then 82 else 83) ∧
    pendingField mode layout = layout.start + (if mode = .x86 then 95 else 97) ∧
    endPC mode layout = layout.start + (if mode = .x86 then 105 else 108) := by
  cases mode <;> simp [ownerPC,scalarField,subPC,sourceField,negPC,sbbPC,notPC,
    updateStart,maskField,pendingField,updateLayout,endPC,copyStart,
    DwordLayout.span,DwordLayout.storeSize,InputUpdate.span,CursorImage.span,
    InputUpdate.field,InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,
    CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,wordPrefix] <;> omega

/-- Every M13 source/destination condition follows from the literal packed
coordinates and one complete finite-code capacity bound. -/
theorem copy_admissible (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes)) :
    DwordLayout.Admissible mode (copyLayout mode layout) := by
  cases mode <;> refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp [copyLayout,copyStart,ownerPC,scalarField,subPC,sourceField,negPC,
      sbbPC,notPC,updateStart,updateLayout,maskField,pendingField,endPC,
      DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,
      DwordLayout.span,DwordLayout.storeSize,InputUpdate.span,CursorImage.span,
      InputUpdate.field,InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,
      CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,
      MemoryOp.trailer,wordPrefix,Relocation.SignedDelta,Relocation.delta] at * <;> omega

@[expose] def resetForm (mode : Mode) (layout : Layout) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.store 0 0) layout.start (maskField mode layout)
@[expose] def ownerForm (mode : Mode) (layout : Layout) (candidate : Dword) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.store 0 candidate) (ownerPC mode layout) (scalarField mode layout)
@[expose] def subForm (mode : Mode) (layout : Layout) (ruleOld : Dword) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.subtract 0 ruleOld) (subPC mode layout) (scalarField mode layout)
@[expose] def negForm (mode : Mode) (layout : Layout) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.negate 0) (negPC mode layout) (scalarField mode layout)
@[expose] def sbbForm (mode : Mode) (layout : Layout) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.sbbZero 0) (sbbPC mode layout) (maskField mode layout)
@[expose] def notForm (mode : Mode) (layout : Layout) : DwordArithmetic.Form :=
  DwordArithmetic.located mode (.complement 0) (notPC mode layout) (maskField mode layout)

@[expose] def copyBytes (mode : Mode) (layout : Layout) : List LittleEndian.Byte :=
  DwordCode.encode mode (DwordLayout.first mode (copyLayout mode layout)) ++
  DwordCode.encode mode (DwordLayout.second mode (copyLayout mode layout)) ++
  DwordCode.encode mode (DwordLayout.third mode (copyLayout mode layout))
@[expose] def prefixBytes (mode : Mode) (layout : Layout) (candidate ruleOld : Dword) :
    List LittleEndian.Byte :=
  DwordArithmetic.encode (resetForm mode layout) ++ copyBytes mode layout ++
  DwordArithmetic.encode (ownerForm mode layout candidate) ++
  DwordArithmetic.encode (subForm mode layout ruleOld) ++
  DwordArithmetic.encode (negForm mode layout) ++
  DwordArithmetic.encode (sbbForm mode layout) ++
  DwordArithmetic.encode (notForm mode layout)
@[expose] def bytes (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword) :
    List LittleEndian.Byte :=
  prefixBytes mode layout candidate ruleOld ++
    InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false
@[expose] def image (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (backing : ByteMemory.Memory) : ByteMemory.Memory :=
  ByteMemory.putBytes backing layout.start (bytes mode layout candidate ruleOld targetOld fresh)
@[expose] def Intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory) : Prop :=
  ByteMemory.bytesAt memory layout.start (bytes mode layout candidate ruleOld targetOld fresh).length =
    bytes mode layout candidate ruleOld targetOld fresh

theorem copy_bytes_length (mode : Mode) (layout : Layout) :
    (copyBytes mode layout).length = DwordLayout.span mode := by
  simp only [copyBytes,List.length_append,DwordCode.encode_length,
    (DwordLayout.lengths mode (copyLayout mode layout)).1,
    (DwordLayout.lengths mode (copyLayout mode layout)).2.1,
    (DwordLayout.lengths mode (copyLayout mode layout)).2.2]
  cases mode <;> rfl

theorem prefix_length (mode : Mode) (layout : Layout) (candidate ruleOld : Dword) :
    layout.start + (prefixBytes mode layout candidate ruleOld).length = updateStart mode layout := by
  simp only [prefixBytes,List.length_append,copy_bytes_length,
    DwordArithmetic.encode_length,resetForm,ownerForm,subForm,negForm,sbbForm,notForm,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length]
  unfold updateStart notPC sbbPC negPC subPC ownerPC copyStart
  omega

theorem bytes_length (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword) :
    layout.start + (bytes mode layout candidate ruleOld targetOld fresh).length = endPC mode layout := by
  simp only [bytes,List.length_append,InputUpdate.length]
  have hprefix := prefix_length mode layout candidate ruleOld
  unfold endPC
  omega

theorem initial_intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (backing : ByteMemory.Memory) :
    Intact mode layout candidate ruleOld targetOld fresh
      (image mode layout candidate ruleOld targetOld fresh backing) := by
  exact ByteMemory.bytes_at_put _ _ _

theorem owner_binding (mode : Mode) (layout : Layout) (candidate : Dword) :
    DwordArithmetic.encode (ownerForm mode layout candidate) =
      DwordOwner.bytes mode (ownerPC mode layout) candidate := by
  cases mode <;> rfl

theorem reset_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory layout.start (DwordArithmetic.encode (resetForm mode layout)).length =
      DwordArithmetic.encode (resetForm mode layout) := by
  have h := ByteWindow.packet memory layout.start [] (DwordArithmetic.encode (resetForm mode layout))
    (copyBytes mode layout ++ DwordArithmetic.encode (ownerForm mode layout candidate) ++
      DwordArithmetic.encode (subForm mode layout ruleOld) ++
      DwordArithmetic.encode (negForm mode layout) ++
      DwordArithmetic.encode (sbbForm mode layout) ++
      DwordArithmetic.encode (notForm mode layout) ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa using h

theorem copy_block_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (copyStart layout) (copyBytes mode layout).length = copyBytes mode layout := by
  have h := ByteWindow.packet memory layout.start (DwordArithmetic.encode (resetForm mode layout))
    (copyBytes mode layout)
    (DwordArithmetic.encode (ownerForm mode layout candidate) ++
      DwordArithmetic.encode (subForm mode layout ruleOld) ++
      DwordArithmetic.encode (negForm mode layout) ++
      DwordArithmetic.encode (sbbForm mode layout) ++
      DwordArithmetic.encode (notForm mode layout) ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [copyStart,resetForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length] using h

theorem owner_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (ownerPC mode layout)
      (DwordArithmetic.encode (ownerForm mode layout candidate)).length =
      DwordArithmetic.encode (ownerForm mode layout candidate) := by
  have h := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (resetForm mode layout) ++ copyBytes mode layout)
    (DwordArithmetic.encode (ownerForm mode layout candidate))
    (DwordArithmetic.encode (subForm mode layout ruleOld) ++
      DwordArithmetic.encode (negForm mode layout) ++
      DwordArithmetic.encode (sbbForm mode layout) ++
      DwordArithmetic.encode (notForm mode layout) ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [ownerPC,copyStart,List.length_append,copy_bytes_length,resetForm,
    DwordArithmetic.encode_length,DwordArithmetic.located,DwordArithmetic.relocate,
    DwordArithmetic.length,Nat.add_assoc] using h

theorem sub_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (subPC mode layout)
      (DwordArithmetic.encode (subForm mode layout ruleOld)).length =
      DwordArithmetic.encode (subForm mode layout ruleOld) := by
  have h := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (resetForm mode layout) ++ copyBytes mode layout ++
      DwordArithmetic.encode (ownerForm mode layout candidate))
    (DwordArithmetic.encode (subForm mode layout ruleOld))
    (DwordArithmetic.encode (negForm mode layout) ++
      DwordArithmetic.encode (sbbForm mode layout) ++
      DwordArithmetic.encode (notForm mode layout) ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [subPC,ownerPC,copyStart,List.length_append,copy_bytes_length,resetForm,
    ownerForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length,Nat.add_assoc] using h

theorem source_value (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    DwordCode.get memory (sourceField mode layout) = ruleOld := by
  have packet := sub_current mode layout candidate ruleOld targetOld fresh memory intact
  have word := ByteWindow.packet memory (subPC mode layout)
    ([0x81,0x2d] ++ LittleEndian.wordEncode 4
      (Relocation.memoryDisp mode (subPC mode layout+10) (scalarField mode layout)))
    (LittleEndian.wordEncode 4 ruleOld) []
    (by simpa [subForm,DwordArithmetic.located,DwordArithmetic.relocate,
      DwordArithmetic.encode,DwordArithmetic.length] using packet)
  have bytesAt : ByteMemory.bytesAt memory (sourceField mode layout) 4 =
      LittleEndian.wordEncode 4 ruleOld := by
    simpa [sourceField,List.length_append,LittleEndian.word_encode_length,Nat.add_assoc]
      using word
  have decoded : ByteMemory.readWord .x86 memory (sourceField mode layout) = some ruleOld := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt memory (sourceField mode layout) 4) = some ruleOld
    rw [bytesAt,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem copy_first_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (copyStart layout)
      (DwordCode.encode mode (DwordLayout.first mode (copyLayout mode layout))).length =
      DwordCode.encode mode (DwordLayout.first mode (copyLayout mode layout)) := by
  have block := copy_block_current mode layout candidate ruleOld targetOld fresh memory intact
  have h := ByteWindow.packet memory (copyStart layout) []
    (DwordCode.encode mode (DwordLayout.first mode (copyLayout mode layout)))
    (DwordCode.encode mode (DwordLayout.second mode (copyLayout mode layout)) ++
      DwordCode.encode mode (DwordLayout.third mode (copyLayout mode layout)))
    (by simpa [copyBytes,List.append_assoc] using block)
  simpa using h

theorem copy_second_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (DwordLayout.secondPC mode (copyLayout mode layout))
      (DwordCode.encode mode (DwordLayout.second mode (copyLayout mode layout))).length =
      DwordCode.encode mode (DwordLayout.second mode (copyLayout mode layout)) := by
  have block := copy_block_current mode layout candidate ruleOld targetOld fresh memory intact
  have h := ByteWindow.packet memory (copyStart layout)
    (DwordCode.encode mode (DwordLayout.first mode (copyLayout mode layout)))
    (DwordCode.encode mode (DwordLayout.second mode (copyLayout mode layout)))
    (DwordCode.encode mode (DwordLayout.third mode (copyLayout mode layout)))
    (by simpa [copyBytes,List.append_assoc] using block)
  simp only [DwordCode.encode_length,
    (DwordLayout.lengths mode (copyLayout mode layout)).1] at h
  simpa only [DwordLayout.secondPC,copyLayout,DwordCode.encode_length] using h

theorem copy_third_current (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (DwordLayout.thirdPC mode (copyLayout mode layout))
      (DwordCode.encode mode (DwordLayout.third mode (copyLayout mode layout))).length =
      DwordCode.encode mode (DwordLayout.third mode (copyLayout mode layout)) := by
  have block := copy_block_current mode layout candidate ruleOld targetOld fresh memory intact
  have h := ByteWindow.packet memory (copyStart layout)
    (DwordCode.encode mode (DwordLayout.first mode (copyLayout mode layout)) ++
      DwordCode.encode mode (DwordLayout.second mode (copyLayout mode layout)))
    (DwordCode.encode mode (DwordLayout.third mode (copyLayout mode layout))) []
    (by simpa [copyBytes,List.append_assoc] using block)
  simp only [List.length_append,DwordCode.encode_length,
    (DwordLayout.lengths mode (copyLayout mode layout)).1,
    (DwordLayout.lengths mode (copyLayout mode layout)).2.1] at h
  simpa only [DwordLayout.thirdPC,DwordLayout.secondPC,copyLayout,
    DwordCode.encode_length,Nat.add_assoc] using h

theorem copy_intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    DwordImage.Intact mode (copyLayout mode layout) memory := by
  intro entry member
  change List.Mem entry
    [⟨(copyLayout mode layout).start,.fixed (DwordImage.firstCode mode (copyLayout mode layout))⟩,
     ⟨DwordLayout.secondPC mode (copyLayout mode layout),
       .fixed (DwordImage.secondCode mode (copyLayout mode layout))⟩,
     ⟨DwordLayout.thirdPC mode (copyLayout mode layout),
       .fixed (DwordImage.thirdCode mode (copyLayout mode layout))⟩] at member
  cases member with
  | head =>
      change ByteMemory.bytesAt memory (copyStart layout)
        (Native.encode .x86 (DwordImage.firstCode mode (copyLayout mode layout))).length =
        Native.encode .x86 (DwordImage.firstCode mode (copyLayout mode layout))
      rw [←(DwordImage.byte_bindings mode (copyLayout mode layout)).1]
      exact copy_first_current mode layout candidate ruleOld targetOld fresh memory intact
  | tail _ rest =>
      cases rest with
      | head =>
          change ByteMemory.bytesAt memory (DwordLayout.secondPC mode (copyLayout mode layout))
            (Native.encode .x86 (DwordImage.secondCode mode (copyLayout mode layout))).length =
            Native.encode .x86 (DwordImage.secondCode mode (copyLayout mode layout))
          rw [←(DwordImage.byte_bindings mode (copyLayout mode layout)).2.1]
          exact copy_second_current mode layout candidate ruleOld targetOld fresh memory intact
      | tail _ last =>
          cases last with
          | head =>
              change ByteMemory.bytesAt memory (DwordLayout.thirdPC mode (copyLayout mode layout))
                (Native.encode .x86 (DwordImage.thirdCode mode (copyLayout mode layout))).length =
                Native.encode .x86 (DwordImage.thirdCode mode (copyLayout mode layout))
              rw [←(DwordImage.byte_bindings mode (copyLayout mode layout)).2.2]
              exact copy_third_current mode layout candidate ruleOld targetOld fresh memory intact
          | tail _ empty => cases empty

theorem start_fits (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes)) :
    layout.start < 2 ^ (8 * mode.wordBytes) := by
  have ⟨_,_,_,_,_,_,_,ending⟩ := positions mode layout
  rw [ending] at capacity
  omega

theorem mask_fits (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes)) :
    maskField mode layout < 2 ^ (8 * mode.wordBytes) := by
  have ⟨_,_,_,_,_,mask,_,ending⟩ := positions mode layout
  rw [ending] at capacity
  rw [mask]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at * <;> omega

theorem reset_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (layout.start+10) (maskField mode layout) := by
  intro wide
  subst mode
  have ⟨_,_,_,_,_,mask,_,_⟩ := positions .x64 layout
  rw [mask]
  simp only [reduceCtorEq,ite_false]
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem reset_effect (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    MixedDword.execute mode (.arithmetic (resetForm mode layout)) state =
      { state with
        pc := Arithmetic.encodeNat mode (copyStart layout)
        memory := DwordCode.put state.memory (maskField mode layout) 0 } := by
  change DwordArithmetic.execute mode (resetForm mode layout) state = _
  rw [resetForm,DwordArithmetic.located_effect mode (.store 0 0) layout.start
    (maskField mode layout) state rfl entry (reset_range mode layout)
    (mask_fits mode layout capacity)]
  rfl

theorem reset_copy_intact (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordImage.Intact mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state).memory := by
  rw [reset_effect mode layout capacity state entry]
  apply DwordImage.intact_put mode (copyLayout mode layout) state.memory
    (copy_intact mode layout candidate ruleOld targetOld fresh state.memory intact)
    (maskField mode layout) 0
  right
  have close := (stage_boundaries mode layout).1
  have ⟨owner,_,_,_,_,mask,_,_⟩ := positions mode layout
  rw [close,owner,mask]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega

theorem reset_trace (mode : Mode) (layout : Layout) (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedDword.Trace mode state [.arithmetic (resetForm mode layout)]
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state) := by
  have pc : state.pc.toNat = layout.start := by
    rw [entry,Arithmetic.encode_nat_toNat mode layout.start (start_fits mode layout capacity)]
  apply MixedDword.Trace.step (by
    rw [pc]
    exact MixedDword.arithmetic_encoding mode state.memory layout.start (resetForm mode layout)
      (reset_current mode layout candidate ruleOld targetOld fresh state.memory intact))
  exact MixedDword.Trace.nil _

theorem copy_step (mode : Mode) (state : Execution.State mode) (pc : Nat)
    (form : DwordCode.Form mode)
    (location : state.pc = Arithmetic.encodeNat mode pc)
    (fits : pc < 2 ^ (8 * mode.wordBytes))
    (current : ByteMemory.bytesAt state.memory pc (DwordCode.encode mode form).length =
      DwordCode.encode mode form) :
    MixedDword.fetch mode state.memory state.pc.toNat = some (.copy form) := by
  rw [location,Arithmetic.encode_nat_toNat mode pc fits]
  exact MixedDword.copy_encoding mode state.memory pc form current

/-- M13's actual three current packets compose in the mixed decoder; its
middle write copies the pending XOR field and its last exchange restores the
SUB immediate before that later packet is fetched. -/
theorem copy_trace (mode : Mode) (layout : Layout)
    (valid : DwordLayout.Admissible mode (copyLayout mode layout))
    (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode (copyStart layout))
    (intact : DwordImage.Intact mode (copyLayout mode layout) state.memory) :
    MixedDword.Trace mode state
      ((DwordLayout.program mode (copyLayout mode layout)).map MixedDword.Form.copy)
      (DwordEffects.finish mode (copyLayout mode layout) state) := by
  let lay := copyLayout mode layout
  have firstPacket := intact ⟨lay.start,.fixed (DwordImage.firstCode mode lay)⟩ (List.Mem.head _)
  change ByteMemory.bytesAt state.memory lay.start
    (Native.encode .x86 (DwordImage.firstCode mode lay)).length =
    Native.encode .x86 (DwordImage.firstCode mode lay) at firstPacket
  rw [←(DwordImage.byte_bindings mode lay).1] at firstPacket
  have firstFits : lay.start < 2 ^ (8 * mode.wordBytes) := by
    have high : DwordLayout.endPC mode lay < 2 ^ (8 * mode.wordBytes) := valid.codeFits
    unfold DwordLayout.endPC DwordLayout.thirdPC DwordLayout.secondPC at high
    omega
  have firstFetch := copy_step mode state lay.start (DwordLayout.first mode lay)
    (by simpa only [lay,copyLayout] using entry) firstFits firstPacket
  have swappedIntact := DwordImage.swapped_intact mode lay valid state
    (by simpa only [lay,copyLayout] using entry) intact
  have secondPacket := swappedIntact
    ⟨DwordLayout.secondPC mode lay,.fixed (DwordImage.secondCode mode lay)⟩
    (List.Mem.tail _ (List.Mem.head _))
  change ByteMemory.bytesAt (DwordEffects.swapped mode lay state).memory (DwordLayout.secondPC mode lay)
    (Native.encode .x86 (DwordImage.secondCode mode lay)).length =
    Native.encode .x86 (DwordImage.secondCode mode lay) at secondPacket
  rw [←(DwordImage.byte_bindings mode lay).2.1] at secondPacket
  have secondFits : DwordLayout.secondPC mode lay < 2 ^ (8 * mode.wordBytes) := by
    have high : DwordLayout.endPC mode lay < 2 ^ (8 * mode.wordBytes) := valid.codeFits
    unfold DwordLayout.endPC DwordLayout.thirdPC at high
    omega
  have secondFetch := copy_step mode (DwordEffects.swapped mode lay state)
    (DwordLayout.secondPC mode lay) (DwordLayout.second mode lay)
    (DwordEffects.swapped_pc mode lay valid state (by simpa only [lay,copyLayout] using entry))
    secondFits secondPacket
  have storedIntact := DwordImage.stored_intact mode lay valid state
    (by simpa only [lay,copyLayout] using entry) intact
  have thirdPacket := storedIntact
    ⟨DwordLayout.thirdPC mode lay,.fixed (DwordImage.thirdCode mode lay)⟩
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  change ByteMemory.bytesAt (DwordEffects.stored mode lay state).memory (DwordLayout.thirdPC mode lay)
    (Native.encode .x86 (DwordImage.thirdCode mode lay)).length =
    Native.encode .x86 (DwordImage.thirdCode mode lay) at thirdPacket
  rw [←(DwordImage.byte_bindings mode lay).2.2] at thirdPacket
  have thirdFits : DwordLayout.thirdPC mode lay < 2 ^ (8 * mode.wordBytes) := by
    have high : DwordLayout.endPC mode lay < 2 ^ (8 * mode.wordBytes) := valid.codeFits
    unfold DwordLayout.endPC at high
    omega
  have thirdFetch := copy_step mode (DwordEffects.stored mode lay state)
    (DwordLayout.thirdPC mode lay) (DwordLayout.third mode lay)
    (DwordEffects.stored_pc mode lay valid state (by simpa only [lay,copyLayout] using entry))
    thirdFits thirdPacket
  change MixedDword.Trace mode state
    [.copy (DwordLayout.first mode lay),.copy (DwordLayout.second mode lay),
      .copy (DwordLayout.third mode lay)] (DwordEffects.finish mode lay state)
  apply MixedDword.Trace.step firstFetch
  change MixedDword.Trace mode (DwordEffects.swapped mode lay state)
    [.copy (DwordLayout.second mode lay),.copy (DwordLayout.third mode lay)] _
  apply MixedDword.Trace.step secondFetch
  change MixedDword.Trace mode (DwordEffects.stored mode lay state)
    [.copy (DwordLayout.third mode lay)] _
  apply MixedDword.Trace.step thirdFetch
  exact MixedDword.Trace.nil _

/-- The first four printed instructions are one mixed current-byte trace:
mask reset, then the three M13 packets. No future-packet premise is supplied. -/
theorem reset_copy_trace (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode)
    (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedDword.Trace mode state
      ([.arithmetic (resetForm mode layout)] ++
        (DwordLayout.program mode (copyLayout mode layout)).map MixedDword.Form.copy)
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)) := by
  let after := MixedDword.execute mode (.arithmetic (resetForm mode layout)) state
  have first := reset_trace mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have location : after.pc = Arithmetic.encodeNat mode (copyStart layout) := by
    dsimp only [after]
    rw [reset_effect mode layout capacity state entry]
  have current := reset_copy_intact mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have rest := copy_trace mode layout (copy_admissible mode layout capacity) after location current
  exact MixedDword.trace_append mode first rest

theorem source_after_reset (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    DwordCode.get (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state).memory
      (sourceField mode layout) = DwordCode.get state.memory (sourceField mode layout) := by
  rw [reset_effect mode layout capacity state entry]
  apply DwordCode.get_frame
  intro index
  have within := index.isLt
  have ⟨_,_,_,source,_,mask,_,_⟩ := positions mode layout
  unfold ByteMemory.Inside
  rw [source,mask]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega

theorem reset_copy_effect (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start) :
    DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state) =
      { state with
        pc := Arithmetic.encodeNat mode (ownerPC mode layout)
        accumulator := DwordCode.lift mode (DwordCode.low mode state.accumulator)
        memory := DwordCode.put
          (DwordCode.put state.memory (maskField mode layout) 0)
          (pendingField mode layout) (DwordCode.get state.memory (sourceField mode layout)) } := by
  have location : (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state).pc =
      Arithmetic.encodeNat mode (copyStart layout) := by
    rw [reset_effect mode layout capacity state entry]
  rw [DwordEffects.effect mode (copyLayout mode layout) (copy_admissible mode layout capacity)
    _ location]
  rw [(stage_boundaries mode layout).1]
  simp only [copyLayout]
  rw [source_after_reset mode layout capacity state entry,
    reset_effect mode layout capacity state entry]

theorem reset_copy_exact (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state) =
      { state with
        pc := Arithmetic.encodeNat mode (ownerPC mode layout)
        accumulator := DwordCode.lift mode (DwordCode.low mode state.accumulator)
        memory := DwordCode.put (DwordCode.put state.memory (maskField mode layout) 0)
          (pendingField mode layout) ruleOld } := by
  rw [reset_copy_effect mode layout capacity state entry,
    source_value mode layout candidate ruleOld targetOld fresh state.memory intact]

theorem sub_source_restored (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)).memory
      (sourceField mode layout) = ruleOld := by
  let after := MixedDword.execute mode (.arithmetic (resetForm mode layout)) state
  have location : after.pc = Arithmetic.encodeNat mode (copyStart layout) := by
    dsimp only [after]
    rw [reset_effect mode layout capacity state entry]
  have original : DwordCode.get after.memory (sourceField mode layout) = ruleOld := by
    dsimp only [after]
    rw [source_after_reset mode layout capacity state entry]
    exact source_value mode layout candidate ruleOld targetOld fresh state.memory intact
  have kept := DwordEffects.source_value mode (copyLayout mode layout)
    (copy_admissible mode layout capacity) after location
  change DwordCode.get (DwordEffects.finish mode (copyLayout mode layout) after).memory
      (sourceField mode layout) = DwordCode.get after.memory (sourceField mode layout) at kept
  exact kept.trans original

theorem owner_length (mode : Mode) (layout : Layout) (candidate : Dword) :
    (DwordArithmetic.encode (ownerForm mode layout candidate)).length = 10 := by
  simp [ownerForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length]

theorem owner_word_frame (mode : Mode) (layout : Layout) (candidate : Dword)
    (memory : ByteMemory.Memory) (field : Nat) (value : Dword)
    (later : ownerPC mode layout + 10 ≤ field) :
    ByteMemory.bytesAt (DwordCode.put memory field value) (ownerPC mode layout)
      (DwordArithmetic.encode (ownerForm mode layout candidate)).length =
    ByteMemory.bytesAt memory (ownerPC mode layout)
      (DwordArithmetic.encode (ownerForm mode layout candidate)).length := by
  change ByteMemory.bytesAt (ByteMemory.putBytes memory field (LittleEndian.wordEncode 4 value))
    (ownerPC mode layout) _ = _
  apply ByteMemory.bytes_at_frame
  intro index
  have small : index.val < 10 := by simpa only [owner_length] using index.isLt
  simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
  omega

theorem owner_current_after_copy (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    ByteMemory.bytesAt
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)).memory
      (ownerPC mode layout) (DwordArithmetic.encode (ownerForm mode layout candidate)).length =
      DwordArithmetic.encode (ownerForm mode layout candidate) := by
  have ⟨owner,_,_,_,_,mask,pending,_⟩ := positions mode layout
  have maskLater : ownerPC mode layout + 10 ≤ maskField mode layout := by
    rw [owner,mask]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega
  have pendingLater : ownerPC mode layout + 10 ≤ pendingField mode layout := by
    rw [owner,pending]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega
  rw [reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change ByteMemory.bytesAt
    (DwordCode.put (DwordCode.put state.memory (maskField mode layout) 0)
      (pendingField mode layout) ruleOld) (ownerPC mode layout) _ = _
  rw [owner_word_frame mode layout candidate _ _ _ pendingLater,
    owner_word_frame mode layout candidate _ _ _ maskLater]
  exact owner_current mode layout candidate ruleOld targetOld fresh state.memory intact

theorem owner_value_after_copy (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    DwordCode.get
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)).memory
      (scalarField mode layout) = candidate := by
  let after := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  have current : ByteMemory.bytesAt after.memory (ownerPC mode layout) 10 =
      DwordOwner.bytes mode (ownerPC mode layout) candidate := by
    rw [←owner_binding,←owner_length]
    exact owner_current_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have immediate := DwordOwner.current_immediate mode (ownerPC mode layout) candidate after.memory current
  change ByteMemory.bytesAt after.memory (scalarField mode layout) 4 =
    LittleEndian.wordEncode 4 candidate at immediate
  have decoded : ByteMemory.readWord .x86 after.memory (scalarField mode layout) = some candidate := by
    change LittleEndian.wordDecode 4 (ByteMemory.bytesAt after.memory (scalarField mode layout) 4) = some candidate
    rw [immediate,LittleEndian.word_decode_encode]
  rw [DwordCode.read_total] at decoded
  exact Option.some.inj decoded

theorem owner_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (ownerPC mode layout+10) (scalarField mode layout) := by
  intro wide
  subst mode
  simpa only [scalarField] using DwordOwner.reach (ownerPC .x64 layout)

theorem scalar_fits (mode : Mode) (layout : Layout)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes)) :
    scalarField mode layout < 2 ^ (8 * mode.wordBytes) := by
  have ⟨_,scalar,_,_,_,_,_,ending⟩ := positions mode layout
  rw [ending] at capacity
  rw [scalar]
  cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at * <;> omega

theorem owner_effect_after_copy (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)) =
      { DwordEffects.finish mode (copyLayout mode layout)
          (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state) with
        pc := Arithmetic.encodeNat mode (subPC mode layout) } := by
  let after := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  have location : after.pc = Arithmetic.encodeNat mode (ownerPC mode layout) := by
    dsimp only [after]
    rw [reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have value : DwordCode.get after.memory (scalarField mode layout) = candidate :=
    owner_value_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact
  change DwordArithmetic.execute mode (ownerForm mode layout candidate) after = _
  rw [ownerForm,DwordArithmetic.located_effect mode (.store 0 candidate)
    (ownerPC mode layout) (scalarField mode layout) after rfl location
    (owner_range mode layout) (scalar_fits mode layout capacity)]
  simp only [DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length]
  rw [show ownerPC mode layout + 10 = subPC mode layout from rfl]
  rw [←value,DwordCode.put_get_back]

theorem owner_trace_after_copy (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedDword.Trace mode
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state))
      [.arithmetic (ownerForm mode layout candidate)]
      (MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
        (DwordEffects.finish mode (copyLayout mode layout)
          (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state))) := by
  let after := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  have location : after.pc = Arithmetic.encodeNat mode (ownerPC mode layout) := by
    dsimp only [after]
    rw [reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have fits : ownerPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    have ⟨owner,_,_,_,_,_,_,ending⟩ := positions mode layout
    rw [ending] at capacity
    rw [owner]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at * <;> omega
  have pc : after.pc.toNat = ownerPC mode layout := by
    rw [location,Arithmetic.encode_nat_toNat mode _ fits]
  apply MixedDword.Trace.step (by
    rw [pc]
    exact MixedDword.arithmetic_encoding mode after.memory (ownerPC mode layout)
      (ownerForm mode layout candidate)
      (owner_current_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact))
  exact MixedDword.Trace.nil _

/-- Reset, all three M13 copy packets, and the live M14 scalar owner form an
actual five-step current-byte trace in the printed order. -/
theorem reset_copy_owner_trace (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    MixedDword.Trace mode state
      (([.arithmetic (resetForm mode layout)] ++
        (DwordLayout.program mode (copyLayout mode layout)).map MixedDword.Form.copy) ++
        [.arithmetic (ownerForm mode layout candidate)])
      (MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
        (DwordEffects.finish mode (copyLayout mode layout)
          (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state))) := by
  exact MixedDword.trace_append mode
    (reset_copy_trace mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (owner_trace_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact)

theorem sub_length (mode : Mode) (layout : Layout) (ruleOld : Dword) :
    (DwordArithmetic.encode (subForm mode layout ruleOld)).length = 10 := by
  simp [subForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length]

theorem sub_word_frame (mode : Mode) (layout : Layout) (ruleOld : Dword)
    (memory : ByteMemory.Memory) (field : Nat) (value : Dword)
    (later : subPC mode layout + 10 ≤ field) :
    ByteMemory.bytesAt (DwordCode.put memory field value) (subPC mode layout)
      (DwordArithmetic.encode (subForm mode layout ruleOld)).length =
    ByteMemory.bytesAt memory (subPC mode layout)
      (DwordArithmetic.encode (subForm mode layout ruleOld)).length := by
  change ByteMemory.bytesAt (ByteMemory.putBytes memory field (LittleEndian.wordEncode 4 value))
    (subPC mode layout) _ = _
  apply ByteMemory.bytes_at_frame
  intro index
  have small : index.val < 10 := by simpa only [sub_length] using index.isLt
  simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
  omega

theorem sub_current_after_owner (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    ByteMemory.bytesAt
      (MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
        (DwordEffects.finish mode (copyLayout mode layout)
          (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state))).memory
      (subPC mode layout) (DwordArithmetic.encode (subForm mode layout ruleOld)).length =
      DwordArithmetic.encode (subForm mode layout ruleOld) := by
  have ⟨_,_,sub,_,_,mask,pending,_⟩ := positions mode layout
  have maskLater : subPC mode layout + 10 ≤ maskField mode layout := by
    rw [sub,mask]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega
  have pendingLater : subPC mode layout + 10 ≤ pendingField mode layout := by
    rw [sub,pending]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega
  rw [owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change ByteMemory.bytesAt
    (DwordCode.put (DwordCode.put state.memory (maskField mode layout) 0)
      (pendingField mode layout) ruleOld) (subPC mode layout) _ = _
  rw [sub_word_frame mode layout ruleOld _ _ _ pendingLater,
    sub_word_frame mode layout ruleOld _ _ _ maskLater]
  exact sub_current mode layout candidate ruleOld targetOld fresh state.memory intact

theorem sub_trace_after_owner (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let after := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state))
    MixedDword.Trace mode after [.arithmetic (subForm mode layout ruleOld)]
      (MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) after) := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let after := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  have location : after.pc = Arithmetic.encodeNat mode (subPC mode layout) := by
    dsimp only [after,copied]
    rw [owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have fits : subPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    have ⟨_,_,sub,_,_,_,_,ending⟩ := positions mode layout
    rw [ending] at capacity
    rw [sub]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] at * <;> omega
  have pc : after.pc.toNat = subPC mode layout := by
    rw [location,Arithmetic.encode_nat_toNat mode _ fits]
  apply MixedDword.Trace.step (by
    rw [pc]
    exact MixedDword.arithmetic_encoding mode after.memory (subPC mode layout)
      (subForm mode layout ruleOld)
      (sub_current_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact))
  exact MixedDword.Trace.nil _

theorem reset_copy_owner_sub_trace (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let after := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state))
    MixedDword.Trace mode state
      ((([.arithmetic (resetForm mode layout)] ++
        (DwordLayout.program mode (copyLayout mode layout)).map MixedDword.Form.copy) ++
        [.arithmetic (ownerForm mode layout candidate)]) ++
        [.arithmetic (subForm mode layout ruleOld)])
      (MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) after) := by
  exact MixedDword.trace_append mode
    (reset_copy_owner_trace mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (sub_trace_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact)

theorem sub_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (subPC mode layout+10) (scalarField mode layout) := by
  intro wide
  subst mode
  have ⟨_,scalar,sub,_,_,_,_,_⟩ := positions .x64 layout
  rw [scalar,sub]
  simp only [reduceCtorEq,ite_false]
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem sub_effect_after_owner (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let after := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate))
      (DwordEffects.finish mode (copyLayout mode layout)
        (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state))
    MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) after =
      { after with
        pc := Arithmetic.encodeNat mode (negPC mode layout)
        carry := decide (candidate.toNat < ruleOld.toNat)
        memory := DwordCode.put after.memory (scalarField mode layout) (candidate-ruleOld) } := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let after := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  have location : after.pc = Arithmetic.encodeNat mode (subPC mode layout) := by
    dsimp only [after,copied]
    rw [owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have value : DwordCode.get after.memory (scalarField mode layout) = candidate := by
    dsimp only [after,copied]
    rw [owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact]
    exact owner_value_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact
  change DwordArithmetic.execute mode (subForm mode layout ruleOld) after = _
  rw [subForm,DwordArithmetic.located_effect mode (.subtract 0 ruleOld)
    (subPC mode layout) (scalarField mode layout) after rfl location
    (sub_range mode layout) (scalar_fits mode layout capacity)]
  simp only [DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length,value]
  rw [show subPC mode layout + 10 = negPC mode layout from rfl]

theorem neg_length (mode : Mode) (layout : Layout) :
    (DwordArithmetic.encode (negForm mode layout)).length = 6 := by
  simp [negForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length]

theorem packet_word_frame (memory : ByteMemory.Memory) (pc : Nat)
    (packet : List LittleEndian.Byte) (field : Nat) (value : Dword)
    (apart : field + 4 ≤ pc ∨ pc + packet.length ≤ field) :
    ByteMemory.bytesAt (DwordCode.put memory field value) pc packet.length =
      ByteMemory.bytesAt memory pc packet.length := by
  change ByteMemory.bytesAt (ByteMemory.putBytes memory field (LittleEndian.wordEncode 4 value))
    pc packet.length = _
  apply ByteMemory.bytes_at_frame
  intro index
  have bound := index.isLt
  simp only [LittleEndian.word_encode_length,ByteMemory.Inside]
  rcases apart with before | after <;> omega

theorem neg_current (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword) (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (negPC mode layout)
      (DwordArithmetic.encode (negForm mode layout)).length =
      DwordArithmetic.encode (negForm mode layout) := by
  have h := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (resetForm mode layout) ++ copyBytes mode layout ++
      DwordArithmetic.encode (ownerForm mode layout candidate) ++
      DwordArithmetic.encode (subForm mode layout ruleOld))
    (DwordArithmetic.encode (negForm mode layout))
    (DwordArithmetic.encode (sbbForm mode layout) ++
      DwordArithmetic.encode (notForm mode layout) ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [negPC,subPC,ownerPC,copyStart,List.length_append,copy_bytes_length,
    resetForm,ownerForm,subForm,DwordArithmetic.encode_length,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,
    Nat.add_assoc] using h

theorem neg_current_after_sub (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    ByteMemory.bytesAt
      (MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned).memory
      (negPC mode layout) (DwordArithmetic.encode (negForm mode layout)).length =
      DwordArithmetic.encode (negForm mode layout) := by
  have ⟨_,scalar,_,_,_,mask,pending,_⟩ := positions mode layout
  have scalarBefore : scalarField mode layout + 4 ≤ negPC mode layout := by
    rw [scalar]
    cases mode <;> simp [negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] <;> omega
  have maskLater : negPC mode layout +
      (DwordArithmetic.encode (negForm mode layout)).length ≤ maskField mode layout := by
    rw [neg_length,mask]
    cases mode <;> simp [negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] <;> omega
  have pendingLater : negPC mode layout +
      (DwordArithmetic.encode (negForm mode layout)).length ≤ pendingField mode layout := by
    rw [neg_length,pending]
    cases mode <;> simp [negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,updateStart,notPC,sbbPC,updateLayout,InputUpdate.field,
      InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,
      CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,
      MemoryOp.trailer,wordPrefix] <;> omega
  dsimp only
  rw [sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change ByteMemory.bytesAt
    (DwordCode.put (DwordCode.put (DwordCode.put state.memory (maskField mode layout) 0)
      (pendingField mode layout) ruleOld) (scalarField mode layout) (candidate-ruleOld))
      (negPC mode layout) _ = _
  rw [packet_word_frame _ _ _ _ _ (Or.inl scalarBefore),
    packet_word_frame _ _ _ _ _ (Or.inr pendingLater),
    packet_word_frame _ _ _ _ _ (Or.inr maskLater)]
  exact neg_current mode layout candidate ruleOld targetOld fresh state.memory intact

theorem neg_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (negPC mode layout+6) (scalarField mode layout) := by
  intro wide
  subst mode
  have ⟨_,scalar,sub,_,_,_,_,_⟩ := positions .x64 layout
  rw [scalar]
  rw [show negPC Mode.x64 layout = subPC Mode.x64 layout + 10 from rfl,sub]
  simp only [reduceCtorEq,ite_false]
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem neg_effect_after_sub (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed =
      { subbed with
        pc := Arithmetic.encodeNat mode (sbbPC mode layout)
        carry := decide (candidate-ruleOld ≠ 0)
        memory := DwordCode.put subbed.memory (scalarField mode layout) (-(candidate-ruleOld)) } := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
  have location : subbed.pc = Arithmetic.encodeNat mode (negPC mode layout) := by
    dsimp only [subbed,owned,copied]
    rw [sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have value : DwordCode.get subbed.memory (scalarField mode layout) = candidate-ruleOld := by
    dsimp only [subbed,owned,copied]
    rw [sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact]
    exact DwordCode.get_put _ _ _
  change DwordArithmetic.execute mode (negForm mode layout) subbed = _
  rw [negForm,DwordArithmetic.located_effect mode (.negate 0)
    (negPC mode layout) (scalarField mode layout) subbed rfl location
    (neg_range mode layout) (scalar_fits mode layout capacity)]
  simp only [DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length,value]
  rw [show negPC mode layout + 6 = sbbPC mode layout from rfl]

theorem neg_trace_after_sub (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    MixedDword.Trace mode subbed [.arithmetic (negForm mode layout)]
      (MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed) := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
  have location : subbed.pc = Arithmetic.encodeNat mode (negPC mode layout) := by
    dsimp only [subbed,owned,copied]
    rw [sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have fits : negPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    have ⟨_,_,_,_,update,_,_,ending⟩ := positions mode layout
    rw [ending] at capacity
    cases mode <;> simp [negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] at * <;> omega
  have pc : subbed.pc.toNat = negPC mode layout := by
    rw [location,Arithmetic.encode_nat_toNat mode _ fits]
  apply MixedDword.Trace.step (by
    rw [pc]
    exact MixedDword.arithmetic_encoding mode subbed.memory (negPC mode layout)
      (negForm mode layout)
      (neg_current_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact))
  exact MixedDword.Trace.nil _

theorem sbb_length (mode : Mode) (layout : Layout) :
    (DwordArithmetic.encode (sbbForm mode layout)).length = 7 := by
  simp [sbbForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length]

theorem sbb_current (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword) (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (sbbPC mode layout)
      (DwordArithmetic.encode (sbbForm mode layout)).length =
      DwordArithmetic.encode (sbbForm mode layout) := by
  have h := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (resetForm mode layout) ++ copyBytes mode layout ++
      DwordArithmetic.encode (ownerForm mode layout candidate) ++
      DwordArithmetic.encode (subForm mode layout ruleOld) ++
      DwordArithmetic.encode (negForm mode layout))
    (DwordArithmetic.encode (sbbForm mode layout))
    (DwordArithmetic.encode (notForm mode layout) ++
      InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [sbbPC,negPC,subPC,ownerPC,copyStart,List.length_append,copy_bytes_length,
    resetForm,ownerForm,subForm,negForm,DwordArithmetic.encode_length,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,
    Nat.add_assoc] using h

theorem sbb_current_after_neg (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    ByteMemory.bytesAt negated.memory (sbbPC mode layout)
      (DwordArithmetic.encode (sbbForm mode layout)).length =
      DwordArithmetic.encode (sbbForm mode layout) := by
  have ⟨_,scalar,_,_,_,mask,pending,_⟩ := positions mode layout
  have scalarBefore : scalarField mode layout + 4 ≤ sbbPC mode layout := by
    rw [scalar]
    cases mode <;> simp [sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] <;> omega
  have maskLater : sbbPC mode layout +
      (DwordArithmetic.encode (sbbForm mode layout)).length ≤ maskField mode layout := by
    rw [sbb_length,mask]
    cases mode <;> simp [sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] <;> omega
  have pendingLater : sbbPC mode layout +
      (DwordArithmetic.encode (sbbForm mode layout)).length ≤ pendingField mode layout := by
    rw [sbb_length,pending]
    cases mode <;> simp [sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,updateStart,notPC,updateLayout,InputUpdate.field,
      InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,
      CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,
      MemoryOp.trailer,wordPrefix] <;> omega
  dsimp only
  rw [neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change ByteMemory.bytesAt
    (DwordCode.put (DwordCode.put (DwordCode.put
      (DwordCode.put state.memory (maskField mode layout) 0)
      (pendingField mode layout) ruleOld) (scalarField mode layout) (candidate-ruleOld))
      (scalarField mode layout) (-(candidate-ruleOld)))
      (sbbPC mode layout) _ = _
  rw [packet_word_frame _ _ _ _ _ (Or.inl scalarBefore),
    packet_word_frame _ _ _ _ _ (Or.inl scalarBefore),
    packet_word_frame _ _ _ _ _ (Or.inr pendingLater),
    packet_word_frame _ _ _ _ _ (Or.inr maskLater)]
  exact sbb_current mode layout candidate ruleOld targetOld fresh state.memory intact

theorem word_get_frame (memory : ByteMemory.Memory) (written observed : Nat)
    (value : Dword) (apart : written + 4 ≤ observed ∨ observed + 4 ≤ written) :
    DwordCode.get (DwordCode.put memory written value) observed =
      DwordCode.get memory observed := by
  apply DwordCode.get_frame
  intro index
  have bound := index.isLt
  simp only [ByteMemory.Inside]
  rcases apart with before | after <;> omega

theorem mask_get_after_neg (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    DwordCode.get negated.memory (maskField mode layout) = 0 := by
  have ⟨_,scalar,_,_,_,mask,pending,_⟩ := positions mode layout
  have scalarBefore : scalarField mode layout + 4 ≤ maskField mode layout := by
    rw [scalar,mask]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega
  have pendingAfter : maskField mode layout + 4 ≤ pendingField mode layout := by
    rw [mask,pending]
    cases mode <;> simp only [ite_true,ite_false,reduceCtorEq] <;> omega
  dsimp only
  rw [neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change DwordCode.get
    (DwordCode.put (DwordCode.put (DwordCode.put
      (DwordCode.put state.memory (maskField mode layout) 0)
      (pendingField mode layout) ruleOld) (scalarField mode layout) (candidate-ruleOld))
      (scalarField mode layout) (-(candidate-ruleOld)))
    (maskField mode layout) = 0
  rw [word_get_frame _ _ _ _ (Or.inl scalarBefore),
    word_get_frame _ _ _ _ (Or.inl scalarBefore),
    word_get_frame _ _ _ _ (Or.inr pendingAfter),DwordCode.get_put]

theorem sbb_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (sbbPC mode layout+7) (maskField mode layout) := by
  intro wide
  subst mode
  have ⟨_,_,sub,_,_,mask,_,_⟩ := positions .x64 layout
  rw [mask]
  rw [show sbbPC Mode.x64 layout = subPC Mode.x64 layout + 16 from rfl,sub]
  simp only [reduceCtorEq,ite_false]
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem sbb_effect_after_neg (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated =
      { negated with
        pc := Arithmetic.encodeNat mode (notPC mode layout)
        carry := decide ((0#32).toNat < (if candidate-ruleOld ≠ 0 then 1 else 0 : Nat))
        memory := DwordCode.put negated.memory (maskField mode layout)
          ((0#32) - (if candidate-ruleOld ≠ 0 then 1 else 0)) } := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
  let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
  have location : negated.pc = Arithmetic.encodeNat mode (sbbPC mode layout) := by
    dsimp only [negated,subbed,owned,copied]
    rw [neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have value : DwordCode.get negated.memory (maskField mode layout) = 0 := by
    exact mask_get_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have carry : negated.carry = decide (candidate-ruleOld ≠ 0) := by
    dsimp only [negated,subbed,owned,copied]
    rw [neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change DwordArithmetic.execute mode (sbbForm mode layout) negated = _
  rw [sbbForm,DwordArithmetic.located_effect mode (.sbbZero 0)
    (sbbPC mode layout) (maskField mode layout) negated rfl location
    (sbb_range mode layout) (mask_fits mode layout capacity)]
  simp only [DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length,value,carry]
  rw [show sbbPC mode layout + 7 = notPC mode layout from rfl]
  by_cases equal : candidate-ruleOld = 0 <;> simp [equal]
  all_goals exact ⟨rfl,rfl,rfl⟩

theorem sbb_trace_after_neg (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    MixedDword.Trace mode negated [.arithmetic (sbbForm mode layout)]
      (MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated) := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
  let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
  have location : negated.pc = Arithmetic.encodeNat mode (sbbPC mode layout) := by
    dsimp only [negated,subbed,owned,copied]
    rw [neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have fits : sbbPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    have ⟨_,_,_,_,_,_,_,ending⟩ := positions mode layout
    rw [ending] at capacity
    cases mode <;> simp [sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] at * <;> omega
  have pc : negated.pc.toNat = sbbPC mode layout := by
    rw [location,Arithmetic.encode_nat_toNat mode _ fits]
  apply MixedDword.Trace.step (by
    rw [pc]
    exact MixedDword.arithmetic_encoding mode negated.memory (sbbPC mode layout)
      (sbbForm mode layout)
      (sbb_current_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact))
  exact MixedDword.Trace.nil _

theorem not_length (mode : Mode) (layout : Layout) :
    (DwordArithmetic.encode (notForm mode layout)).length = 6 := by
  simp [notForm,DwordArithmetic.encode_length,DwordArithmetic.located,
    DwordArithmetic.relocate,DwordArithmetic.length]

theorem not_current (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword) (memory : ByteMemory.Memory)
    (intact : Intact mode layout candidate ruleOld targetOld fresh memory) :
    ByteMemory.bytesAt memory (notPC mode layout)
      (DwordArithmetic.encode (notForm mode layout)).length =
      DwordArithmetic.encode (notForm mode layout) := by
  have h := ByteWindow.packet memory layout.start
    (DwordArithmetic.encode (resetForm mode layout) ++ copyBytes mode layout ++
      DwordArithmetic.encode (ownerForm mode layout candidate) ++
      DwordArithmetic.encode (subForm mode layout ruleOld) ++
      DwordArithmetic.encode (negForm mode layout) ++
      DwordArithmetic.encode (sbbForm mode layout))
    (DwordArithmetic.encode (notForm mode layout))
    (InputUpdate.bytes mode (updateLayout mode layout) targetOld fresh false)
    (by simpa [Intact,bytes,prefixBytes,List.append_assoc] using intact)
  simpa [notPC,sbbPC,negPC,subPC,ownerPC,copyStart,List.length_append,copy_bytes_length,
    resetForm,ownerForm,subForm,negForm,sbbForm,DwordArithmetic.encode_length,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,
    Nat.add_assoc] using h

theorem not_current_after_sbb (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
    ByteMemory.bytesAt borrowed.memory (notPC mode layout)
      (DwordArithmetic.encode (notForm mode layout)).length =
      DwordArithmetic.encode (notForm mode layout) := by
  have ⟨_,scalar,_,_,_,mask,pending,_⟩ := positions mode layout
  have scalarBefore : scalarField mode layout + 4 ≤ notPC mode layout := by
    rw [scalar]
    cases mode <;> simp [notPC,sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] <;> omega
  have maskLater : notPC mode layout +
      (DwordArithmetic.encode (notForm mode layout)).length ≤ maskField mode layout := by
    rw [not_length,mask]
    cases mode <;> simp [notPC,sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] <;> omega
  have pendingLater : notPC mode layout +
      (DwordArithmetic.encode (notForm mode layout)).length ≤ pendingField mode layout := by
    rw [not_length,pending]
    cases mode <;> simp [notPC,sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,updateStart,updateLayout,InputUpdate.field,
      InputUpdate.body,CursorPatch.field,CursorLayout.middlePC,
      CursorLayout.exchangeSize,instructionLength,MemoryOp.prefix,
      MemoryOp.trailer,wordPrefix] <;> omega
  dsimp only
  rw [sbb_effect_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    neg_effect_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    sub_effect_after_owner mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    owner_effect_after_copy mode layout candidate ruleOld targetOld fresh capacity state entry intact,
    reset_copy_exact mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change ByteMemory.bytesAt
    (DwordCode.put (DwordCode.put (DwordCode.put (DwordCode.put
      (DwordCode.put state.memory (maskField mode layout) 0)
      (pendingField mode layout) ruleOld) (scalarField mode layout) (candidate-ruleOld))
      (scalarField mode layout) (-(candidate-ruleOld)))
      (maskField mode layout)
      ((0#32) - (if candidate-ruleOld ≠ 0 then 1 else 0)))
      (notPC mode layout) _ = _
  rw [packet_word_frame _ _ _ _ _ (Or.inr maskLater),
    packet_word_frame _ _ _ _ _ (Or.inl scalarBefore),
    packet_word_frame _ _ _ _ _ (Or.inl scalarBefore),
    packet_word_frame _ _ _ _ _ (Or.inr pendingLater),
    packet_word_frame _ _ _ _ _ (Or.inr maskLater)]
  exact not_current mode layout candidate ruleOld targetOld fresh state.memory intact

theorem sbb_mask (condition : Bool) :
    (0#32) - (if condition then 1 else 0) = BranchAlgebra.mask condition := by
  cases condition <;> rfl

theorem sbb_mask_prop (condition : Prop) [Decidable condition] :
    (0#32) - (if condition then 1 else 0) = BranchAlgebra.mask (decide condition) := by
  by_cases h : condition <;> simp [h,BranchAlgebra.mask]

theorem sbb_carry_prop (condition : Prop) [Decidable condition] :
    decide (0 < (if condition then 1 else 0 : Nat)) = decide condition := by
  by_cases h : condition <;> simp [h]

theorem mask_get_after_sbb (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
    DwordCode.get borrowed.memory (maskField mode layout) =
      BranchAlgebra.mask (decide (candidate-ruleOld ≠ 0)) := by
  dsimp only
  rw [sbb_effect_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  simp only [DwordCode.get_put]
  exact sbb_mask_prop (candidate-ruleOld ≠ 0)

theorem sbb_carry_after_neg (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
    borrowed.carry = decide (candidate-ruleOld ≠ 0) := by
  dsimp only
  rw [sbb_effect_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  change decide (0 < (if candidate-ruleOld ≠ 0 then 1 else 0 : Nat)) =
    decide (candidate-ruleOld ≠ 0)
  exact sbb_carry_prop (candidate-ruleOld ≠ 0)

theorem not_range (mode : Mode) (layout : Layout) :
    mode = .x64 → Relocation.SignedDelta (notPC mode layout+6) (maskField mode layout) := by
  intro wide
  subst mode
  have ⟨_,_,sub,_,_,mask,_,_⟩ := positions .x64 layout
  rw [mask]
  rw [show notPC Mode.x64 layout = subPC Mode.x64 layout + 23 from rfl,sub]
  simp only [reduceCtorEq,ite_false]
  unfold Relocation.SignedDelta Relocation.delta
  omega

theorem not_effect_after_sbb (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
    MixedDword.execute mode (.arithmetic (notForm mode layout)) borrowed =
      { borrowed with
        pc := Arithmetic.encodeNat mode (updateStart mode layout)
        carry := decide (candidate-ruleOld ≠ 0)
        memory := DwordCode.put borrowed.memory (maskField mode layout)
          (BranchAlgebra.mask (!(decide (candidate-ruleOld ≠ 0)))) } := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
  let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
  let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
  have location : borrowed.pc = Arithmetic.encodeNat mode (notPC mode layout) := by
    dsimp only [borrowed,negated,subbed,owned,copied]
    rw [sbb_effect_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have value : DwordCode.get borrowed.memory (maskField mode layout) =
      BranchAlgebra.mask (decide (candidate-ruleOld ≠ 0)) :=
    mask_get_after_sbb mode layout candidate ruleOld targetOld fresh capacity state entry intact
  have carry : borrowed.carry = decide (candidate-ruleOld ≠ 0) :=
    sbb_carry_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact
  change DwordArithmetic.execute mode (notForm mode layout) borrowed = _
  rw [notForm,DwordArithmetic.located_effect mode (.complement 0)
    (notPC mode layout) (maskField mode layout) borrowed rfl location
    (not_range mode layout) (mask_fits mode layout capacity)]
  simp only [DwordArithmetic.flag,DwordArithmetic.result,DwordArithmetic.length,value,carry]
  rw [show notPC mode layout + 6 = updateStart mode layout from rfl,
    BranchAlgebra.complement_mask]

theorem not_trace_after_sbb (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
    MixedDword.Trace mode borrowed [.arithmetic (notForm mode layout)]
      (MixedDword.execute mode (.arithmetic (notForm mode layout)) borrowed) := by
  let copied := DwordEffects.finish mode (copyLayout mode layout)
    (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
  let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
  let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
  let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
  let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
  have location : borrowed.pc = Arithmetic.encodeNat mode (notPC mode layout) := by
    dsimp only [borrowed,negated,subbed,owned,copied]
    rw [sbb_effect_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact]
  have fits : notPC mode layout < 2 ^ (8 * mode.wordBytes) := by
    have ⟨_,_,_,_,_,_,_,ending⟩ := positions mode layout
    rw [ending] at capacity
    cases mode <;> simp [notPC,sbbPC,negPC,subPC,ownerPC,copyStart,DwordLayout.span,
      DwordLayout.storeSize,instructionLength,MemoryOp.prefix,MemoryOp.trailer,
      wordPrefix] at * <;> omega
  have pc : borrowed.pc.toNat = notPC mode layout := by
    rw [location,Arithmetic.encode_nat_toNat mode _ fits]
  apply MixedDword.Trace.step (by
    rw [pc]
    exact MixedDword.arithmetic_encoding mode borrowed.memory (notPC mode layout)
      (notForm mode layout)
      (not_current_after_sbb mode layout candidate ruleOld targetOld fresh capacity state entry intact))
  exact MixedDword.Trace.nil _

@[expose] def prefixProgram (mode : Mode) (layout : Layout) (candidate ruleOld : Dword) :
    List (MixedDword.Form mode) :=
  [.arithmetic (resetForm mode layout)] ++
    (DwordLayout.program mode (copyLayout mode layout)).map MixedDword.Form.copy ++
    [.arithmetic (ownerForm mode layout candidate),
     .arithmetic (subForm mode layout ruleOld),.arithmetic (negForm mode layout),
     .arithmetic (sbbForm mode layout),.arithmetic (notForm mode layout)]

/-- The exact reset, three M13 packets, M14, SUB, NEG, SBB and NOT form a
single nine-instruction current-byte trace from the initialized image. -/
theorem prefix_trace (mode : Mode) (layout : Layout)
    (candidate ruleOld targetOld fresh : Dword)
    (capacity : endPC mode layout < 2 ^ (8 * mode.wordBytes))
    (state : Execution.State mode) (entry : state.pc = Arithmetic.encodeNat mode layout.start)
    (intact : Intact mode layout candidate ruleOld targetOld fresh state.memory) :
    let copied := DwordEffects.finish mode (copyLayout mode layout)
      (MixedDword.execute mode (.arithmetic (resetForm mode layout)) state)
    let owned := MixedDword.execute mode (.arithmetic (ownerForm mode layout candidate)) copied
    let subbed := MixedDword.execute mode (.arithmetic (subForm mode layout ruleOld)) owned
    let negated := MixedDword.execute mode (.arithmetic (negForm mode layout)) subbed
    let borrowed := MixedDword.execute mode (.arithmetic (sbbForm mode layout)) negated
    MixedDword.Trace mode state (prefixProgram mode layout candidate ruleOld)
      (MixedDword.execute mode (.arithmetic (notForm mode layout)) borrowed) := by
  have throughNeg := MixedDword.trace_append mode
    (reset_copy_owner_sub_trace mode layout candidate ruleOld targetOld fresh capacity state entry intact)
    (neg_trace_after_sub mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have throughSbb := MixedDword.trace_append mode throughNeg
    (sbb_trace_after_neg mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  have throughNot := MixedDword.trace_append mode throughSbb
    (not_trace_after_sbb mode layout candidate ruleOld targetOld fresh capacity state entry intact)
  simpa only [prefixProgram,List.append_assoc,List.cons_append,List.nil_append] using throughNot

end SmcTuring.Appendix.Listing8InputPrefix
