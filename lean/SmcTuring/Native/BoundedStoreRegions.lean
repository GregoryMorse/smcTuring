module
public import SmcTuring.Native.StringStoreTemplateRuns

public section
namespace SmcTuring.Native.BoundedStoreRegions

theorem native_length (mode : Mode) (form : Native.Form mode) (state : StringExecution.State mode) :
    (StringWrites.packet mode (StringStack.native mode form) state).bytes.length=mode.wordBytes :=
  LittleEndian.word_encode_length _ _

theorem packet (mode : Mode) (allowed : Nat → Nat → Prop) (field width : Nat) (form : StringStack.Form mode)
    (state : StringExecution.State mode) (inside : StringWrites.CodeWrite mode field (field+width) form state)
    (length : (StringWrites.packet mode form state).bytes.length=width) (owned : allowed field width) :
    allowed (StringWrites.packet mode form state).address (StringWrites.packet mode form state).bytes.length := by
  have address : (StringWrites.packet mode form state).address=field := by
    have lower:=inside.2.1;have upper:=inside.2.2
    rw [length] at upper
    omega
  rw [address,length]
  exact owned

theorem interval (mode : Mode) (allowed : Nat → Nat → Prop) (start stop : Nat) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode)
    (covers : ∀ address count,start≤address → address+count≤stop → allowed address count)
    (owned : StringWrites.OwnedRun mode start stop forms state) : StringStoreRegions.Run mode allowed forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨covers _ _ owned.1.2.1 owned.1.2.2,ih _ owned.2⟩

theorem monotone (mode : Mode) (first second : Nat → Nat → Prop) (forms : List (StringStack.Form mode))
    (state : StringExecution.State mode) (implies : ∀ address count,first address count → second address count)
    (regions : StringStoreRegions.Run mode first forms state) : StringStoreRegions.Run mode second forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih => exact ⟨implies _ _ regions.1,ih _ regions.2⟩

end SmcTuring.Native.BoundedStoreRegions
