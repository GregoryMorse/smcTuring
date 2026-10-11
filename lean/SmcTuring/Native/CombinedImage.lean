module
public import SmcTuring.Native.ControlPacking

public section

namespace SmcTuring.Native.CombinedImage

open ControlImage

@[expose] def image (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (values : Nat -> Word mode) : ByteMemory.Memory :=
  ControlImage.image mode (ControlPacking.place mode start packets) (GridImage.image mode gridBase values)

@[expose] def Intact (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (memory : ByteMemory.Memory) : Prop :=
  And (ControlImage.Intact mode (ControlPacking.place mode start packets) memory)
    (Protected.GridProtected mode gridBase memory)

@[expose] def Owned (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat) (address : Word mode) : Prop :=
  Or (ControlImage.Owned mode (ControlPacking.place mode start packets) address)
    (Protected.GridOwned mode gridBase address)

/-- Overlaying the finite control fragment preserves every storage-grid opcode
when the control extent ends before the first storage opcode. -/
theorem initial_grid (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode) :
    Protected.GridProtected mode gridBase (image mode packets start gridBase values) := by
  intro cell
  have original := GridImage.prefix_bytes mode gridBase cell values enough
  unfold Protected.PrefixAt
  rw [<-original]
  apply congrArg List.ofFn
  funext index
  exact ControlPacking.image_frame mode packets start _ _ (Or.inr
    (Nat.le_trans gap (GridImage.start_before mode gridBase cell index.val enough)))

theorem initially_intact (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode) :
    Intact mode packets start gridBase (image mode packets start gridBase values) :=
  And.intro (ControlPacking.initially_intact mode packets start _) (initial_grid mode packets start gridBase values enough gap)

theorem initial_word (mode : Mode) (packets : List (Packet mode)) (start gridBase cell : Nat) (values : Nat -> Word mode)
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode) :
    Protected.wordAt mode (image mode packets start gridBase values) (Layout.fieldAddress mode gridBase cell) = values cell := by
  have frame : ByteMemory.bytesAt (image mode packets start gridBase values)
      (Layout.fieldAddress mode gridBase cell) mode.wordBytes =
        ByteMemory.bytesAt (GridImage.image mode gridBase values) (Layout.fieldAddress mode gridBase cell) mode.wordBytes := by
    apply congrArg List.ofFn
    funext index
    have lower : gridBase - moffsOperandOffset mode <= Layout.fieldAddress mode gridBase cell + index.val := by
      unfold Layout.fieldAddress
      omega
    exact ControlPacking.image_frame mode packets start _ _ (Or.inr (Nat.le_trans gap lower))
  unfold Protected.wordAt
  rw [frame]
  exact GridImage.initial_word mode gridBase cell values enough

/-- A control-owned field ends inside the finite extent, so its store cannot
reach the later storage grid's opcode bytes. -/
theorem control_store_grid (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (memory : ByteMemory.Memory) (address value : Word mode)
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode)
    (intact : Protected.GridProtected mode gridBase memory)
    (owned : ControlImage.Owned mode (ControlPacking.place mode start packets) address) :
    Protected.GridProtected mode gridBase (ByteMemory.putWord mode memory address.toNat value) := by
  cases owned with
  | intro owner owns =>
    rcases owns with ⟨member, ⟨⟨initial, kind⟩, location⟩⟩
    have bound := ControlPacking.placed_upper mode packets start owner member
    rw [owned_packet_length mode owner initial kind] at bound
    intro cell
    rw [Protected.prefix_frame mode memory (Layout.templatePC mode gridBase cell) address.toNat value (by
      intro index
      have lower := GridImage.start_before mode gridBase cell index.val enough
      rw [location]
      unfold ByteMemory.Inside
      omega)]
    exact intact cell

theorem store_intact (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (memory : ByteMemory.Memory) (address value : Word mode)
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode)
    (intact : Intact mode packets start gridBase memory) (owned : Owned mode packets start gridBase address) :
    Intact mode packets start gridBase (ByteMemory.putWord mode memory address.toNat value) := by
  cases owned with
  | inl control =>
    exact And.intro (ControlImage.store_intact mode _ memory (ControlPacking.placed_separated mode packets start)
      intact.1 address value control) (control_store_grid mode packets start gridBase memory address value enough gap intact.2 control)
  | inr grid =>
    rcases grid with ⟨cell, location⟩
    have after : start + ControlPacking.size mode packets <= address.toNat := by
      rw [location]
      unfold Layout.fieldAddress
      omega
    exact And.intro (ControlImage.external_store_intact mode _ memory intact.1 address value
      (ControlPacking.above_external mode packets start address after))
      (by rw [location]; exact Protected.grid_store_protected mode gridBase cell memory value enough intact.2)

/-- Ownership names an actual currently decodable MOFFS address operand in the
constructed byte image, rather than an arbitrary memory-address predicate. -/
theorem owned_operand (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (memory : ByteMemory.Memory) (address : Word mode) (enough : moffsOperandOffset mode <= gridBase)
    (intact : Intact mode packets start gridBase memory) (owned : Owned mode packets start gridBase address) :
    exists pc, And (address.toNat = pc + moffsOperandOffset mode)
      (Fetch.fetch mode memory pc = some (.moffs (Protected.wordAt mode memory address.toNat))) := by
  cases owned with
  | inl control =>
    cases control with
    | intro entry owns =>
      rcases owns with ⟨member, ⟨⟨initial, kind⟩, location⟩⟩
      refine ⟨entry.pc, location, ?_⟩
      have prefixIntact : Protected.PrefixAt mode memory entry.pc :=
        by simpa [ControlImage.PacketIntact, kind] using intact.1 entry member
      rw [Protected.fetch_moffs mode memory entry.pc prefixIntact, location]
  | inr grid =>
    rcases grid with ⟨cell, location⟩
    refine ⟨Layout.templatePC mode gridBase cell, ?_, ?_⟩
    · rw [location, Layout.owner_field_address mode gridBase cell enough]
    · rw [Protected.grid_fetch_current mode gridBase cell memory enough intact.2, location]

theorem execute_intact (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (state : Execution.State mode) (form : Form mode) (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode)
    (intact : Intact mode packets start gridBase state.memory)
    (owned : Owned mode packets start gridBase (Writes.address mode form state)) :
    Intact mode packets start gridBase (Execution.execute mode form state).memory := by
  rw [Writes.execute_memory]
  exact store_intact mode packets start gridBase state.memory _ _ enough gap intact owned

theorem run_intact (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (state : Execution.State mode) (forms : List (Form mode)) (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode)
    (intact : Intact mode packets start gridBase state.memory)
    (owned : Writes.OwnedRun mode (Owned mode packets start gridBase) forms state) :
    Intact mode packets start gridBase (Execution.runForms mode forms state).memory := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    change And (Owned mode packets start gridBase (Writes.address mode form state))
      (Writes.OwnedRun mode (Owned mode packets start gridBase) rest (Execution.execute mode form state)) at owned
    exact ih (Execution.execute mode form state)
      (execute_intact mode packets start gridBase state form enough gap intact owned.1) owned.2

theorem trace_intact (mode : Mode) (packets : List (Packet mode)) (start gridBase : Nat)
    (state finish : Execution.State mode) (forms : List (Form mode))
    (enough : moffsOperandOffset mode <= gridBase)
    (gap : start + ControlPacking.size mode packets <= gridBase - moffsOperandOffset mode)
    (intact : Intact mode packets start gridBase state.memory)
    (owned : Writes.OwnedRun mode (Owned mode packets start gridBase) forms state)
    (trace : Fetch.Trace mode state forms finish) :
    Intact mode packets start gridBase finish.memory := by
  rw [Fetch.trace_run_eq mode trace]
  exact run_intact mode packets start gridBase state forms enough gap intact owned

end SmcTuring.Native.CombinedImage
