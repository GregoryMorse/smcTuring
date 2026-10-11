module
public import SmcTuring.Appendix.Listing8OwnerInput

public section
namespace SmcTuring.Appendix.Listing8InputReuseFields
open Native Listing8LiteralInput
abbrev Dword:=BitVec 32
@[expose] def beforePending (mode : Mode) (l : Layout) (rule tape fresh oldMask : Dword) :=
  Listing8InputMask.leading mode l rule tape fresh++LittleEndian.wordEncode 4 oldMask++
    CursorPatch.leading mode (InputUpdate.body (updateLayout mode l))

theorem mask_patch (mode : Mode) (l : Layout) (rule tape pending fresh old newMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode l rule tape pending fresh old memory) :
    Listing8InputMask.Intact mode l rule tape pending fresh newMask (DwordCode.put memory (maskField mode l) newMask) := by
  have patched:=BytePatch.current memory l.start (Listing8InputMask.leading mode l rule tape fresh)
    (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 newMask) (Listing8InputMask.trailing mode l pending)
    (by simp only [LittleEndian.word_encode_length]) current
  rw [Listing8InputMask.mask_position] at patched
  exact patched

theorem pending_spelling (mode : Mode) (l : Layout) (rule tape pending fresh oldMask : Dword) :
    Listing8InputMask.bytes mode l rule tape pending fresh oldMask=
      beforePending mode l rule tape fresh oldMask++LittleEndian.wordEncode 4 pending++
        MixedDword.encode mode (CursorLayout.last mode (InputUpdate.body (updateLayout mode l))) := by
  simp only [Listing8InputMask.bytes,Listing8InputMask.trailing,CursorPatch.spelling,beforePending,List.append_assoc]

theorem pending_position (mode : Mode) (l : Layout) (rule tape fresh oldMask : Dword) :
    l.start+(beforePending mode l rule tape fresh oldMask).length=pendingField mode l := by
  have mask:=Listing8InputMask.mask_position mode l rule tape fresh
  simp only [beforePending,List.length_append,LittleEndian.word_encode_length,CursorPatch.leading_length]
  simp only [pendingField,InputUpdate.field,CursorPatch.field,CursorLayout.middlePC,InputUpdate.body,updateLayout,maskField] at mask ⊢
  omega

theorem pending_patch (mode : Mode) (l : Layout) (rule tape old newPending fresh oldMask : Dword)
    (memory : ByteMemory.Memory) (current : Listing8InputMask.Intact mode l rule tape old fresh oldMask memory) :
    Listing8InputMask.Intact mode l rule tape newPending fresh oldMask (DwordCode.put memory (pendingField mode l) newPending) := by
  have original : ByteMemory.bytesAt memory l.start
      (beforePending mode l rule tape fresh oldMask++LittleEndian.wordEncode 4 old++
        MixedDword.encode mode (CursorLayout.last mode (InputUpdate.body (updateLayout mode l)))).length=
      beforePending mode l rule tape fresh oldMask++LittleEndian.wordEncode 4 old++
        MixedDword.encode mode (CursorLayout.last mode (InputUpdate.body (updateLayout mode l))) := by
    rw [←pending_spelling];exact current
  have patched:=BytePatch.current memory l.start (beforePending mode l rule tape fresh oldMask)
    (LittleEndian.wordEncode 4 old) (LittleEndian.wordEncode 4 newPending)
    (MixedDword.encode mode (CursorLayout.last mode (InputUpdate.body (updateLayout mode l))))
    (by simp only [LittleEndian.word_encode_length]) original
  rw [pending_position,←pending_spelling] at patched
  exact patched

theorem head_bytes (mode : Mode) (l : Layout) (head : Nat) (rule tape pending fresh oldMask : Dword) :
    Listing8InputMask.bytes mode {l with head:=head} rule tape pending fresh oldMask=
      Listing8InputMask.bytes mode l rule tape pending fresh oldMask := rfl

end SmcTuring.Appendix.Listing8InputReuseFields
