module
public import SmcTuring.Appendix.Listing8CopiedOwners
public import SmcTuring.Appendix.Listing8CursorFields

public section
namespace SmcTuring.Appendix.Listing8OwnerInput
open Native Listing8Prototypes Listing8CopyImage Listing8LiteralInput
abbrev Dword := BitVec 32

@[expose] def beforeRule (mode : Mode) (l : Listing8LiteralInput.Layout) :=
  DwordArithmetic.encode (resetForm mode l) ++ DwordMixedImage.bytes mode (copyLayout mode l) ++
    [0xc7,0x05] ++ LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (ownerPC mode l+10) (scalarField mode l))
@[expose] def afterRule (mode : Mode) (l : Listing8LiteralInput.Layout) (tape pending fresh oldMask : Dword) :=
  DwordComparisonTail.bytes mode (tailLayout mode l) tape ++ distributionBytes mode l ++
    DwordArithmetic.encode (InputUpdate.xorForm mode (updateLayout mode l) fresh) ++ [0x81,0x25] ++
    LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (updateStart mode l+20) (pendingField mode l)) ++
    LittleEndian.wordEncode 4 oldMask ++ Listing8InputMask.trailing mode l pending
@[expose] def beforeFresh (mode : Mode) (l : Listing8LiteralInput.Layout) (rule tape : Dword) :=
  prefixBytes mode l rule tape ++ distributionBytes mode l ++ [0x81,0x35] ++
    LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (updateStart mode l+10) (pendingField mode l))
@[expose] def afterFresh (mode : Mode) (l : Listing8LiteralInput.Layout) (pending oldMask : Dword) :=
  [0x81,0x25] ++ LittleEndian.wordEncode 4 (Relocation.memoryDisp mode (updateStart mode l+20) (pendingField mode l)) ++
    LittleEndian.wordEncode 4 oldMask ++ Listing8InputMask.trailing mode l pending

theorem rule_spelling (mode : Mode) (l : Listing8LiteralInput.Layout) (rule tape pending fresh oldMask : Dword) :
    Listing8InputMask.bytes mode l rule tape pending fresh oldMask =
      beforeRule mode l ++ LittleEndian.wordEncode 4 rule ++ afterRule mode l tape pending fresh oldMask := by
  simp [Listing8InputMask.bytes,Listing8InputMask.leading,beforeRule,afterRule,prefixBytes,
    ownerForm,DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,DwordArithmetic.encode,List.append_assoc]

theorem rule_position (mode : Mode) (l : Listing8LiteralInput.Layout) :
    l.start+(beforeRule mode l).length = scalarField mode l := by
  simp only [beforeRule,List.length_append,DwordArithmetic.encode_length,resetForm,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,DwordMixedImage.bytes_length,
    List.length_cons,List.length_nil,LittleEndian.word_encode_length]
  unfold scalarField ownerPC copyStart
  omega

theorem rule_patch (mode : Mode) (l : Listing8LiteralInput.Layout) (old rule tape pending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode l old tape pending fresh oldMask memory) :
    Listing8InputMask.Intact mode l rule tape pending fresh oldMask (DwordCode.put memory (scalarField mode l) rule) := by
  have original : ByteMemory.bytesAt memory l.start (beforeRule mode l ++ LittleEndian.wordEncode 4 old ++ afterRule mode l tape pending fresh oldMask).length =
      beforeRule mode l ++ LittleEndian.wordEncode 4 old ++ afterRule mode l tape pending fresh oldMask := by rw [←rule_spelling];exact current
  have patched := BytePatch.current memory l.start (beforeRule mode l) (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 rule)
    (afterRule mode l tape pending fresh oldMask) (by simp only [LittleEndian.word_encode_length]) original
  rw [rule_position,←rule_spelling] at patched
  exact patched

theorem fresh_spelling (mode : Mode) (l : Listing8LiteralInput.Layout) (rule tape pending fresh oldMask : Dword) :
    Listing8InputMask.bytes mode l rule tape pending fresh oldMask =
      beforeFresh mode l rule tape ++ LittleEndian.wordEncode 4 fresh ++ afterFresh mode l pending oldMask := by
  simp [Listing8InputMask.bytes,Listing8InputMask.leading,beforeFresh,afterFresh,
    InputUpdate.xorForm,updateLayout,InputUpdate.field,pendingField,
    DwordArithmetic.located,DwordArithmetic.relocate,DwordArithmetic.length,DwordArithmetic.encode,List.append_assoc]

theorem fresh_position (mode : Mode) (l : Listing8LiteralInput.Layout) (rule tape : Dword) :
    l.start+(beforeFresh mode l rule tape).length = updateStart mode l+6 := by
  have prefixExtent := prefix_length mode l rule tape
  have gapLength := distribution_length mode l
  simp only [beforeFresh,List.length_append,List.length_cons,List.length_nil,LittleEndian.word_encode_length]
  unfold updateStart
  omega

theorem fresh_patch (mode : Mode) (l : Listing8LiteralInput.Layout) (rule tape pending old fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode l rule tape pending old oldMask memory) :
    Listing8InputMask.Intact mode l rule tape pending fresh oldMask (DwordCode.put memory (updateStart mode l+6) fresh) := by
  have original : ByteMemory.bytesAt memory l.start (beforeFresh mode l rule tape ++ LittleEndian.wordEncode 4 old ++ afterFresh mode l pending oldMask).length =
      beforeFresh mode l rule tape ++ LittleEndian.wordEncode 4 old ++ afterFresh mode l pending oldMask := by rw [←fresh_spelling];exact current
  have patched := BytePatch.current memory l.start (beforeFresh mode l rule tape) (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 fresh)
    (afterFresh mode l pending oldMask) (by simp only [LittleEndian.word_encode_length]) original
  rw [fresh_position,←fresh_spelling] at patched
  exact patched

/-- The actual remaining copied owners produce the entire later input image:
rule in its scalar owner, tape in SUB, fresh symbol in XOR, force-wide masks.
There is no assumed later image or host reinitialization. -/
theorem input_image (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    Listing8InputMask.Intact mode l.input v.rule v.tape force v.fresh force
      (Listing8CopiedOwners.finish mode l v backing seed).principal.memory := by
  have original := Listing8Initializer.input_after_tape mode l v r b.tapeReach backing seed
  have rule := rule_patch mode l.input 0 v.rule v.tape force force force _ original
  have fresh := fresh_patch mode l.input v.rule v.tape force force v.fresh force _ rule
  have memory := (Listing8CopiedOwners.result mode l v r b backing seed).2.1
  rw [memory]
  change ByteMemory.bytesAt (ByteMemory.putBytes _ (l.direction+6) (LittleEndian.wordEncode 4 v.direction)) l.input.start
    (Listing8InputMask.bytes mode l.input v.rule v.tape force v.fresh force).length = _
  rw [byte_frame _ _ _ _ _ (Or.inr (by
    have length := Listing8InputMask.bytes_length mode l.input v.rule v.tape force v.fresh force
    have afterInput := b.directionAfter
    omega))]
  exact fresh

theorem cursor_after_initializer (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8OwnerImage.state mode l v backing seed).principal.memory (StringCodec.sourceField mode l.start) =
      Arithmetic.encodeNat mode l.sourceNode := by
  have ending := cursor_end mode l
  have d := destinations mode l
  have nodeStart : (nodeParams mode l).destination = patchStart mode l+40 := rfl
  have source := Listing8OwnerImage.source_field_bounds mode l
  have afterInput := r.inputAfter
  have window := Listing8OwnerImage.frame mode l v r b.tapeReach backing seed (StringCodec.sourceField mode l.start) mode.wordBytes
    (by
      intro site member
      have bounds := Listing8ModeOffsets.owners_after_patches mode (patchLayout mode l) site member
      change patchStart mode l+40 ≤ site.owner ∧ _ at bounds
      right;omega)
    (Or.inr (by omega))
  unfold MixedMemory.getWord
  rw [window]
  exact Listing8CopyTrace.cursor_retained mode l v r backing seed

theorem cursor (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8CopiedOwners.finish mode l v backing seed).principal.memory (StringCodec.sourceField mode l.start) =
      Arithmetic.encodeNat mode l.sourceNode := by
  have ending := cursor_end mode l
  have d := destinations mode l
  have nodeStart : (nodeParams mode l).destination = patchStart mode l+40 := rfl
  have fields := Listing8CopiedOwners.scalar_bounds mode l
  have inputAfter := r.inputAfter
  have dirAfter := b.directionAfter
  have codeToInput := code_to_input mode l r
  have window : ∀ target ∈ [scalarField mode l.input,updateStart mode l.input+6,l.direction+6],
      ∀ i : Fin mode.wordBytes, ¬ByteMemory.Inside target 4 (StringCodec.sourceField mode l.start+i.val) := by
    intro target member i
    have small := i.isLt
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> simp only [ByteMemory.Inside] <;> omega
  rw [(Listing8CopiedOwners.result mode l v r b backing seed).2.1,
    MixedMemory.wide_after_dword mode _ (l.direction+6) _ v.direction (window _ (by simp)),
    MixedMemory.wide_after_dword mode _ (updateStart mode l.input+6) _ v.fresh (window _ (by simp)),
    MixedMemory.wide_after_dword mode _ (scalarField mode l.input) _ v.rule (window _ (by simp))]
  exact cursor_after_initializer mode l v r b backing seed

theorem bound_cursor (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode)
    (cursorBinding : l.input.cursor = StringCodec.sourceField mode l.start) (headBinding : l.input.head = l.sourceNode) :
    MixedMemory.getWord mode (Listing8CopiedOwners.finish mode l v backing seed).principal.memory l.input.cursor =
      Arithmetic.encodeNat mode l.input.head := by
  rw [cursorBinding,headBinding]
  exact cursor mode l v r b backing seed

theorem source_node (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    ByteMemory.bytesAt (Listing8CopiedOwners.finish mode l v backing seed).principal.memory l.sourceNode
      (sourceNodeBytes mode l v).length = sourceNodeBytes mode l v := by
  have fields := Listing8CopiedOwners.scalar_bounds mode l
  have before : l.start ≤ l.input.start := by have d := destinations mode l;have afterInput := r.inputAfter;omega
  have outsideInput (target : Nat) (within : l.input.start ≤ target ∧ target+4 ≤ endPC mode l.input) :
      target+4 ≤ l.sourceNode ∨ l.sourceNode+nodeSpan mode ≤ target := by
    rcases r.nodeOutside with early | late <;> omega
  have a := outsideInput (scalarField mode l.input) ⟨fields.1,fields.2.1⟩
  have c := outsideInput (updateStart mode l.input+6) ⟨fields.2.2.1,fields.2.2.2⟩
  have d := b.nodeDirection
  rw [(Listing8CopiedOwners.result mode l v r b backing seed).2.1]
  change ByteMemory.bytesAt (ByteMemory.putBytes _ (l.direction+6) (LittleEndian.wordEncode 4 v.direction)) l.sourceNode _ = _
  rw [byte_frame _ _ _ _ _ (by
    rw [LittleEndian.word_encode_length,show (sourceNodeBytes mode l v).length = nodeSpan mode from node_length mode _ _ _ _]
    rcases d with early | late <;> omega)]
  change ByteMemory.bytesAt (ByteMemory.putBytes _ (updateStart mode l.input+6) (LittleEndian.wordEncode 4 v.fresh)) l.sourceNode _ = _
  rw [byte_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length,sourceNodeBytes,node_length] using c)]
  change ByteMemory.bytesAt (ByteMemory.putBytes _ (scalarField mode l.input) (LittleEndian.wordEncode 4 v.rule)) l.sourceNode _ = _
  rw [byte_frame _ _ _ _ _ (by simpa only [LittleEndian.word_encode_length,sourceNodeBytes,node_length] using a)]
  exact Listing8OwnerImage.original_node mode l v r b.tapeReach backing seed

theorem tape_symbol (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    DwordCode.get (Listing8CopiedOwners.finish mode l v backing seed).principal.memory (l.sourceNode+6) = v.tape :=
  (node_values mode l.sourceNode v.tape v.back v.forward _ (source_node mode l v r b backing seed)).1

theorem corrected_cursor_label (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    MixedMemory.getWord mode (Listing8CopiedOwners.finish mode l v backing seed).principal.memory
      (Listing8CursorFields.field mode l.start) = Arithmetic.encodeNat mode l.sourceNode := by
  rw [Listing8CursorFields.field_is_operand]
  exact cursor mode l v r b backing seed

theorem registers (mode : Mode) (l : Listing8CopyImage.Layout) (v : Values mode) (r : Resources mode l)
    (b : Listing8CopiedOwners.Bounds mode l v) (backing : ByteMemory.Memory) (seed : StringExecution.State mode) :
    (Listing8CopiedOwners.finish mode l v backing seed).principal.stack = seed.principal.stack ∧
    (Listing8CopiedOwners.finish mode l v backing seed).principal.carry = false ∧
    (Listing8CopiedOwners.finish mode l v backing seed).sourceIndex = seed.sourceIndex ∧
    (Listing8CopiedOwners.finish mode l v backing seed).destinationIndex = seed.destinationIndex ∧
    (Listing8CopiedOwners.finish mode l v backing seed).backwards = false := by
  have copies := Listing8CopyTrace.indices mode l v r backing seed
  have indices : (Listing8OwnerImage.state mode l v backing seed).sourceIndex = seed.sourceIndex ∧
      (Listing8OwnerImage.state mode l v backing seed).destinationIndex = seed.destinationIndex ∧
      (Listing8OwnerImage.state mode l v backing seed).backwards = false := by
    rw [Listing8OwnerImage.state,Listing8Initializer.finish,Listing8Initializer.tapeForm,StringDword.store_execute]
    exact ⟨copies.1,copies.2.1,copies.2.2.1⟩
  have principal : (Listing8OwnerImage.state mode l v backing seed).principal.stack = seed.principal.stack ∧
      (Listing8OwnerImage.state mode l v backing seed).principal.carry = false := by
    rw [Listing8OwnerImage.state,Listing8Initializer.principal_effect,
      Listing8ModeOffsets.tape_owner_effect mode (patchLayout mode l) v.tape (block_capacity mode l r)
        (Listing8ModeOffsets.patch_ranges mode (patchLayout mode l)) b.tapeReach (Listing8OwnerImage.source_field_fits mode l r) _
        (Listing8CopyTrace.patch_entry mode l v r backing seed)]
    exact ⟨copies.2.2.2.1,copies.2.2.2.2⟩
  have result := (Listing8CopiedOwners.result mode l v r b backing seed).2.2
  exact ⟨result.1.trans principal.1,result.2.1.trans principal.2,result.2.2.1.trans indices.1,
    result.2.2.2.1.trans indices.2.1,result.2.2.2.2.trans indices.2.2⟩

end SmcTuring.Appendix.Listing8OwnerInput
