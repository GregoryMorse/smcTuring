module
public import SmcTuring.Appendix.Listing8PackedResources

public section
namespace SmcTuring.Appendix.Listing8PackedPointerBounds
open Native Listing8SourceGraph Listing8Prototypes Listing8CopyImage Listing8PackedBodyLayout Listing8PackedResources

/-- The complete actual pointer-copy list, including both x64 DWORD halves,
is derived from its original encoders and copied-owner field locations. -/
theorem dword_layouts (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions) :
    Listing8PointerCopies.layouts mode (layout mode origin g node rule) (targets mode origin)=
      match mode with
      | .x86 => [⟨main mode origin+316,main mode origin+295,main mode origin+620⟩,
          ⟨main mode origin+333,main mode origin+211,main mode origin+529⟩,
          ⟨main mode origin+350,main mode origin+229,main mode origin+545⟩]
      | .x64 => [⟨main mode origin+442,main mode origin+413,main mode origin+974⟩,
          ⟨main mode origin+460,main mode origin+417,main mode origin+984⟩,
          ⟨main mode origin+478,main mode origin+302,main mode origin+790⟩,
          ⟨main mode origin+496,main mode origin+306,main mode origin+800⟩,
          ⟨main mode origin+514,main mode origin+329,main mode origin+822⟩,
          ⟨main mode origin+532,main mode origin+333,main mode origin+832⟩] := by
  have copied:=copy_positions mode origin g node rule
  have word:=word_positions mode origin g node rule
  simp only [Listing8PointerCopies.layouts,Listing8PointerCopies.dwordStart,ConversionLayout.endPC,
    ConversionLayout.thirdPC,ConversionLayout.secondPC,word.1,copied.1,copied.2.1]
  cases mode <;> simp [targets,Listing8PointerCopies.split,Listing8PointerCopies.groupSpan,Listing8PointerCopies.halfCount,
    stateEntry,directionEntry,newEntry,currentEntry,forwardEntry,backEntry,pointerField,pointerSpan,ReaderImage.totalSize,
    ReaderImage.labelOffset,ConversionLayout.exchangeSize,ConversionLayout.storeSize,instructionLength,MemoryOp.prefix,
    MemoryOp.trailer,wordPrefix,DwordLayout.span,DwordLayout.storeSize,Nat.add_assoc]

theorem word_valid (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) :
    ConversionLayout.Admissible mode (Listing8PointerCopies.word mode (layout mode origin g node rule)) := by
  have body:=body_capacity mode origin g node bounds
  have coords:=word_positions mode origin g node rule
  constructor <;> simp only [ConversionLayout.endPC,ConversionLayout.thirdPC,ConversionLayout.secondPC,coords.1,coords.2.1,coords.2.2]
  all_goals cases mode <;> simp [ConversionLayout.exchangeSize,ConversionLayout.storeSize,instructionLength,MemoryOp.prefix,
    MemoryOp.trailer,wordPrefix,Mode.wordBytes,Relocation.SignedDelta,Relocation.delta,Nat.add_assoc] at body ⊢ <;> omega

theorem dword_valid (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (bounds : Listing8GraphPointers.Bounds mode origin g) (copy : DwordLayout.Layout)
    (member : copy∈Listing8PointerCopies.layouts mode (layout mode origin g node rule) (targets mode origin)) :
    DwordLayout.Admissible mode copy := by
  have body:=body_capacity mode origin g node bounds
  rw [dword_layouts] at member
  cases mode
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals constructor
  all_goals simp [DwordLayout.endPC,DwordLayout.thirdPC,DwordLayout.secondPC,DwordLayout.storeSize,Mode.wordBytes,
    Relocation.SignedDelta,Relocation.delta,Nat.add_assoc] at body ⊢ <;> omega

theorem bounds (mode : Mode) (origin : Nat) (g : Graph) (node : Fin g.nodes) (rule : Fin g.transitions)
    (native : Listing8GraphPointers.Bounds mode origin g) :
    Listing8PointerCopies.Bounds mode (layout mode origin g node rule) (targets mode origin) := by
  refine ⟨word_valid mode origin g node rule native,dword_valid mode origin g node rule native,?_⟩
  intro pc member
  have ending:=joined mode origin g node rule
  rw [←ending]
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals cases mode <;> simp [layout,input]

end SmcTuring.Appendix.Listing8PackedPointerBounds
