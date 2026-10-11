module
public import SmcTuring.Appendix.MultiplyPacking
public import SmcTuring.Appendix.ByteLinear

public section

namespace SmcTuring.Appendix.MultiplyLinear

open MultiplyByteCode MultiplyImage
abbrev State := MultiplyByteExecution.State
abbrev Word := MultiplyByteCode.Word
abbrev Memory := MultiplyImage.Memory

/-- A fixed packet whose PC falls through. CALL is deliberately excluded. -/
@[expose] def Straight : Form → Prop
  | .common (.callRelative _) => False
  | _ => True
@[expose] def span (forms : List Form) : Nat := MultiplyPacking.size (forms.map Packet.fixed)
@[expose] def entries (start : Nat) (forms : List Form) : List Entry := MultiplyPacking.place start (forms.map Packet.fixed)

theorem span_cons (form : Form) (rest : List Form) :
    span (form :: rest) = instructionLength form + span rest := by
  simp only [span, List.map_cons, MultiplyPacking.size_cons, Packet.initial, encode_length]

theorem minimum_length (form : Form) : 4 ≤ instructionLength form := by
  cases form with
  | common form => exact ByteLinear.minimum_length form
  | _ => simp [instructionLength]

theorem execute_pc (form : Form) (start : Nat) (state : State)
    (straight : Straight form) (location : state.pc = FieldRefinement.address start) :
    (MultiplyByteExecution.execute form state).pc = FieldRefinement.address (start + instructionLength form) := by
  rw [MultiplyByteExecution.execute_pc]
  have linear : MultiplyByteExecution.pc form state = MultiplyByteExecution.nextPC form state := by
    cases form with
    | common form => cases form <;> simp_all [Straight, MultiplyByteExecution.pc,
        MultiplyByteExecution.nextPC, ByteExecution.pc, ByteExecution.nextPC, instructionLength]
    | _ => rfl
  rw [linear, MultiplyByteExecution.nextPC, location]
  exact BitVec.ofNat_add_ofNat _ _

/-- Every fixed form's destination is a constant. The quantification over
states specifies static ownership; it supplies no future fetch or invariant. -/
theorem constructed_trace (whole : List Entry) (forms : List Form) (start : Nat) (state : State)
    (separate : Separated whole) (intact : Intact whole state.memory)
    (placed : ∀ entry ∈ entries start forms, entry ∈ whole)
    (straight : ∀ form ∈ forms, Straight form)
    (codeFits : start + span forms < 2 ^ 32)
    (ownership : ∀ form ∈ forms, ∀ state : State, Owned whole (MultiplyByteExecution.destination form state).toNat)
    (location : state.pc = FieldRefinement.address start) :
    MultiplyByteExecution.Trace state forms (MultiplyByteExecution.run forms state) := by
  induction forms generalizing start state with
  | nil => exact .nil state
  | cons form rest ih =>
    have member : (⟨start, .fixed form⟩ : Entry) ∈ whole := placed _ (by simp [entries, MultiplyPacking.place])
    have startFits : start + 4 ≤ 2 ^ 32 := by
      rw [span_cons] at codeFits
      have lower := minimum_length form
      omega
    have fetched : fetch state.memory state.pc.toNat = some form := by
      rw [location]
      change fetch state.memory (FieldRefinement.address start).toNat = some form
      rw [FieldRefinement.address_toNat start startFits]
      exact fetch_current _ _ (intact _ member)
    have nextIntact : Intact whole (MultiplyByteExecution.execute form state).memory :=
      execute_intact whole state form separate intact (ownership form (by simp) state)
    have tailPlaced : ∀ entry ∈ entries (start + instructionLength form) rest, entry ∈ whole := by
      intro entry inTail
      apply placed entry
      simp only [entries, List.map_cons, MultiplyPacking.place, Packet.initial, encode_length, List.mem_cons]
      exact Or.inr inTail
    have tailFits : start + instructionLength form + span rest < 2 ^ 32 := by
      simpa only [span_cons, Nat.add_assoc] using codeFits
    exact .step fetched (ih _ _ nextIntact tailPlaced (fun next member => straight next (by simp [member]))
      tailFits (fun next member => ownership next (by simp [member]))
      (execute_pc form start state (straight form (by simp)) location))

theorem image_trace (whole : List Entry) (forms : List Form) (start : Nat) (state : State) (backing : Memory)
    (separate : Separated whole) (initial : state.memory = image whole backing)
    (placed : ∀ entry ∈ entries start forms, entry ∈ whole)
    (straight : ∀ form ∈ forms, Straight form) (codeFits : start + span forms < 2 ^ 32)
    (ownership : ∀ form ∈ forms, ∀ state : State, Owned whole (MultiplyByteExecution.destination form state).toNat)
    (location : state.pc = FieldRefinement.address start) :
    MultiplyByteExecution.Trace state forms (MultiplyByteExecution.run forms state) := by
  apply constructed_trace whole forms start state separate _ placed straight codeFits ownership location
  rw [initial]
  exact initialized_intact whole backing separate

theorem run_pc (forms : List Form) (start : Nat) (state : State)
    (straight : ∀ form ∈ forms, Straight form) (location : state.pc = FieldRefinement.address start) :
    (MultiplyByteExecution.run forms state).pc = FieldRefinement.address (start + span forms) := by
  induction forms generalizing start state with
  | nil => simpa only [MultiplyByteExecution.run, span, MultiplyPacking.size, List.map_nil, List.sum_nil, Nat.add_zero] using location
  | cons form rest ih =>
    have next := ih (start + instructionLength form) _ (fun next member => straight next (by simp [member]))
      (execute_pc form start state (straight form (by simp)) location)
    simpa only [MultiplyByteExecution.run, span_cons, Nat.add_assoc] using next

theorem owned_run (owned : Word → Prop) (forms : List Form) (state : State)
    (ownership : ∀ form ∈ forms, ∀ state : State, owned (MultiplyByteExecution.destination form state)) :
    MultiplyByteExecution.OwnedRun owned forms state := by
  induction forms generalizing state with
  | nil => trivial
  | cons form rest ih =>
    exact ⟨ownership form (by simp) state, ih _ (fun next member => ownership next (by simp [member]))⟩

theorem run_intact (whole : List Entry) (forms : List Form) (state : State)
    (separate : Separated whole) (intact : Intact whole state.memory)
    (ownership : ∀ form ∈ forms, ∀ state : State, Owned whole (MultiplyByteExecution.destination form state).toNat) :
    Intact whole (MultiplyByteExecution.run forms state).memory := by
  induction forms generalizing state with
  | nil => exact intact
  | cons form rest ih =>
    exact ih _ (execute_intact whole state form separate intact (ownership form (by simp) state))
      (fun next member => ownership next (by simp [member]))

theorem run_common (forms : List ByteCode.Form) (state : State) :
    MultiplyByteExecution.run (forms.map Form.common) state = ByteExecution.run forms state := by
  induction forms generalizing state with
  | nil => rfl
  | cons form rest ih => exact ih (ByteExecution.execute form state)

end SmcTuring.Appendix.MultiplyLinear
