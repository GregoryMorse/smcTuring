module
public import SmcTuring.Appendix.Listing8NodeTrace
public import SmcTuring.Appendix.Listing8TableTrace

public section
namespace SmcTuring.Appendix.Listing8DeclarationOwnerGeometry
open Native Listing8OriginalOwners Listing8Prototypes

theorem total_append (mode : Mode) (first second : List (Owner mode)) :
    total mode (first++second)=total mode first+total mode second := by
  induction first with
  | nil => simp only [total,List.nil_append,Nat.zero_add]
  | cons owner rest ih => simp only [List.cons_append,total,ih,Nat.add_assoc]

theorem program_append (mode : Mode) (first second : List (Owner mode)) :
    program mode (first++second)=program mode first++program mode second := by
  exact List.flatMap_append

theorem contiguous_append (mode : Mode) (first second : List (Owner mode)) (start : Nat)
    (firstChain : Contiguous mode start first)
    (secondChain : Contiguous mode (start+total mode first) second) :
    Contiguous mode start (first++second) := by
  induction first generalizing start with
  | nil => simpa only [List.nil_append,total,Nat.add_zero] using secondChain
  | cons owner rest ih =>
    refine ⟨firstChain.1,ih _ firstChain.2 ?_⟩
    simpa only [total,firstChain.1,Nat.add_assoc] using secondChain

theorem nodes_total (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) :
    total mode (Listing8NodeTable.owners mode start table)=table.length*nodeSpan mode := by
  induction table generalizing start with
  | nil => simp only [Listing8NodeTable.owners,total,List.length_nil,Nat.zero_mul]
  | cons value table ih =>
    rw [Listing8NodeTable.owners,total_append,Listing8NodeBlock.total,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem nodes_chain (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) :
    Contiguous mode start (Listing8NodeTable.owners mode start table) := by
  induction table generalizing start with
  | nil => trivial
  | cons value table ih =>
    apply contiguous_append mode _ _ start (Listing8NodeBlock.contiguous mode start value)
    rw [Listing8NodeBlock.total]
    exact ih _

theorem nodes_valid (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode))
    (valid : Listing8NodeTable.Valid mode start table) :
    ∀ owner∈Listing8NodeTable.owners mode start table,Valid mode owner := by
  induction table generalizing start with
  | nil => simp only [Listing8NodeTable.owners,List.not_mem_nil];intro owner impossible;exact False.elim impossible
  | cons value table ih =>
    intro owner member
    rw [Listing8NodeTable.owners,List.mem_append] at member
    rcases member with first | later
    · exact Listing8NodeBlock.valid mode start value valid.1 owner first
    · exact ih _ valid.2 owner later

theorem nodes_current (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) (memory : ByteMemory.Memory)
    (initial : Listing8NodeTable.Initial mode start table memory) :
    Intact mode (Listing8NodeTable.owners mode start table) memory := by
  induction table generalizing start with
  | nil => intro owner member;simp only [Listing8NodeTable.owners,List.not_mem_nil] at member
  | cons value table ih =>
    intro owner member
    rw [Listing8NodeTable.owners,List.mem_append] at member
    rcases member with first | later
    · exact Listing8NodeBlock.current mode start value memory (Listing8NodeTable.head_current mode start value table memory initial) owner first
    · exact ih _ (Listing8NodeTable.tail_current mode start value table memory initial) owner later

theorem nodes_program (mode : Mode) (start : Nat) (table : List (Listing8NodeBlock.Values mode)) :
    program mode (Listing8NodeTable.owners mode start table)=Listing8NodeTrace.program mode start table := by
  induction table generalizing start with
  | nil => rfl
  | cons value table ih => rw [Listing8NodeTable.owners,program_append,ih];rfl

theorem transitions_total (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) :
    total mode (Listing8TransitionTable.owners mode start table)=table.length*transitionSpan mode := by
  induction table generalizing start with
  | nil => simp only [Listing8TransitionTable.owners,total,List.length_nil,Nat.zero_mul]
  | cons value table ih =>
    rw [Listing8TransitionTable.owners,total_append,Listing8TransitionBlock.total,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem transitions_chain (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) :
    Contiguous mode start (Listing8TransitionTable.owners mode start table) := by
  induction table generalizing start with
  | nil => trivial
  | cons value table ih =>
    apply contiguous_append mode _ _ start (Listing8TransitionBlock.contiguous mode start value)
    rw [Listing8TransitionBlock.total]
    exact ih _

theorem transitions_valid (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode))
    (valid : Listing8TransitionTable.Valid mode start table) :
    ∀ owner∈Listing8TransitionTable.owners mode start table,Valid mode owner := by
  induction table generalizing start with
  | nil => simp only [Listing8TransitionTable.owners,List.not_mem_nil];intro owner impossible;exact False.elim impossible
  | cons value table ih =>
    intro owner member
    rw [Listing8TransitionTable.owners,List.mem_append] at member
    rcases member with first | later
    · exact Listing8TransitionBlock.valid mode start value valid.1 owner first
    · exact ih _ valid.2 owner later

theorem transitions_current (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) (memory : ByteMemory.Memory)
    (initial : Listing8TransitionTable.Initial mode start table memory) :
    Intact mode (Listing8TransitionTable.owners mode start table) memory := by
  induction table generalizing start with
  | nil => intro owner member;simp only [Listing8TransitionTable.owners,List.not_mem_nil] at member
  | cons value table ih =>
    intro owner member
    rw [Listing8TransitionTable.owners,List.mem_append] at member
    rcases member with first | later
    · exact Listing8TransitionBlock.current mode start value memory (Listing8TransitionTable.head_current mode start value table memory initial) owner first
    · exact ih _ (Listing8TransitionTable.tail_current mode start value table memory initial) owner later

theorem transitions_program (mode : Mode) (start : Nat) (table : List (Listing8CopyImage.Values mode)) :
    program mode (Listing8TransitionTable.owners mode start table)=Listing8TableTrace.program mode start table := by
  induction table generalizing start with
  | nil => rfl
  | cons value table ih => rw [Listing8TransitionTable.owners,program_append,ih];rfl

end SmcTuring.Appendix.Listing8DeclarationOwnerGeometry
