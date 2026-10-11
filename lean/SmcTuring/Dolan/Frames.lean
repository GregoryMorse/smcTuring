module
public import SmcTuring.Dolan.Machine

public section

namespace SmcTuring.Dolan.Mov

@[expose] def keepsRegister (r : Register) : Instruction → Prop
  | .immediate dest _ => dest ≠ r
  | .load dest _ _ => dest ≠ r
  | .store _ _ _ => True

@[expose] def readOnly : Instruction → Prop
  | .store _ _ _ => False
  | _ => True

theorem execute_register_frame (i : Instruction) (start finish : State) (r : Register)
    (h : execute i start = some finish) (keep : keepsRegister r i) :
    finish.registers r = start.registers r := by
  cases i with
  | immediate dest value =>
    simp only [execute, Option.some.injEq] at h
    subst finish
    simp [keepsRegister] at keep
    simp [write, Ne.symm keep]
  | load dest base offset =>
    cases ha : address start base offset with
    | none => simp [execute, ha] at h
    | some p =>
      simp only [execute, ha, Option.some.injEq] at h
      subst finish
      simp [keepsRegister] at keep
      simp [write, Ne.symm keep]
  | store base offset source =>
    cases ha : address start base offset with
    | none => simp [execute, ha] at h
    | some p =>
      simp only [execute, ha, Option.some.injEq] at h
      subst finish
      rfl

theorem run_register_frame (program : List Instruction) (start finish : State) (r : Register)
    (h : run program start = some finish) (keep : ∀ i ∈ program, keepsRegister r i) :
    finish.registers r = start.registers r := by
  induction program generalizing start finish with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst finish
    rfl
  | cons i rest ih =>
    cases first : execute i start with
    | none => simp [run, first] at h
    | some middle =>
      have tailRun : run rest middle = some finish := by simpa [run, first] using h
      have tailKeep : ∀ j ∈ rest, keepsRegister r j :=
        fun j hj => keep j (List.mem_cons_of_mem i hj)
      calc
        finish.registers r = middle.registers r := ih middle finish tailRun tailKeep
        _ = start.registers r := execute_register_frame i start middle r first (keep i (by simp))

theorem execute_read_only (i : Instruction) (start finish : State)
    (h : execute i start = some finish) (keep : readOnly i) : finish.memory = start.memory := by
  cases i with
  | immediate dest value =>
    simp only [execute, Option.some.injEq] at h
    subst finish
    rfl
  | load dest base offset =>
    cases ha : address start base offset with
    | none => simp [execute, ha] at h
    | some p =>
      simp only [execute, ha, Option.some.injEq] at h
      subst finish
      rfl
  | store base offset source => simp [readOnly] at keep

theorem run_read_only (program : List Instruction) (start finish : State)
    (h : run program start = some finish) (keep : ∀ i ∈ program, readOnly i) :
    finish.memory = start.memory := by
  induction program generalizing start finish with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst finish
    rfl
  | cons i rest ih =>
    cases first : execute i start with
    | none => simp [run, first] at h
    | some middle =>
      have tailRun : run rest middle = some finish := by simpa [run, first] using h
      have tailKeep : ∀ j ∈ rest, readOnly j := fun j hj => keep j (List.mem_cons_of_mem i hj)
      calc
        finish.memory = middle.memory := ih middle finish tailRun tailKeep
        _ = start.memory := execute_read_only i start middle first (keep i (by simp))

theorem immediate_noop (s : State) (r : Register) (value : Word) (h : s.registers r = value) :
    execute (.immediate r value) s = some s := by
  have same : write s.registers r value = s.registers := by
    calc
      _ = write s.registers r (s.registers r) := congrArg (write s.registers r) h.symm
      _ = s.registers := write_back s.registers r
  simp only [execute, same]

theorem run_insert_noop (first rest : List Instruction) (i : Instruction) (s : State)
    (h : ∀ middle, run first s = some middle → execute i middle = some middle) :
    run (first ++ i :: rest) s = run (first ++ rest) s := by
  calc
    _ = (run first s).bind (run (i :: rest)) := run_append first (i :: rest) s
    _ = (run first s).bind (run rest) := by
      cases completed : run first s with
      | none => rfl
      | some middle =>
        have noop := h middle completed
        simp only [Option.bind_some, run, noop]
    _ = run (first ++ rest) s := (run_append first rest s).symm

end SmcTuring.Dolan.Mov
