module
public import SmcTuring.Appendix.Listing8TerminalReadClasses
public import SmcTuring.Native.StringPCGuards

public section
namespace SmcTuring.Appendix.Listing8OriginalOwnerPC
open Native Listing8OriginalOwners Listing8Prototypes

theorem sequential_form (mode : Mode) (owner : Owner mode) :
    ∀ form∈(forms mode owner).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  intro form member
  cases owner with
  | pointer pc value =>
    simp only [forms,List.map_map,List.mem_map] at member
    rcases member with ⟨original,packetMember,rfl⟩
    cases mode <;> simp only [Listing8CopiedPointer.forms,List.mem_cons,List.not_mem_nil,or_false] at packetMember <;>
      rcases packetMember with rfl | rfl | rfl | rfl <;>
      simp [StringStoreWrites.liftDword,StringPCSteps.Sequential,StringPCSteps.ControlSequential,
        StringPCSteps.DwordSequential,StringPCSteps.StringSequential,StringPCSteps.NativeSequential,
        Listing8CopiedPointer.first,Listing8CopiedPointer.second,Reader.storeForm]
  | scalar pc value =>
    simp only [forms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    subst form
    cases mode <;> trivial

theorem total_form (mode : Mode) (owner : Owner mode) :
    StringPCSteps.total mode ((forms mode owner).map (StringStoreWrites.liftDword mode))=span mode owner := by
  cases owner <;> cases mode <;> rfl

theorem guard_form (mode : Mode) (owner : Owner mode) :
    StringPCWindows.Guard mode ((forms mode owner).map (StringStoreWrites.liftDword mode)) := by
  cases owner with
  | pointer pc value =>
    cases mode <;> simp [forms,Listing8CopiedPointer.forms,Listing8CopiedPointer.first,
      Listing8CopiedPointer.second,Reader.storeForm,StringStoreWrites.liftDword,
      StringPCWindows.Guard,StringPCSteps.total,StringPCSteps.size,StringPCSteps.controlSize,
      StringPCSteps.dwordSize,StringPCSteps.stringSize,instructionLength,wordPrefix,
      MemoryOp.prefix,MemoryOp.trailer,Mode.wordBytes]
  | scalar pc value =>
    cases mode <;> change 3≤10 ∧ True <;> decide

theorem sequential (mode : Mode) (owners : List (Owner mode)) :
    ∀ form∈(program mode owners).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_flatMap.mp innerMember with ⟨owner,_,ownerMember⟩
  exact sequential_form mode owner _ (List.mem_map.mpr ⟨middle,ownerMember,rfl⟩)

theorem total (mode : Mode) (owners : List (Owner mode)) :
    StringPCSteps.total mode ((program mode owners).map (StringStoreWrites.liftDword mode))=Listing8OriginalOwners.total mode owners := by
  induction owners with
  | nil => rfl
  | cons owner owners ih =>
    rw [program,List.flatMap_cons,List.map_append,StringPCSteps.total_append,total_form]
    change span mode owner+StringPCSteps.total mode ((program mode owners).map (StringStoreWrites.liftDword mode))=_
    rw [ih,Listing8OriginalOwners.total]

theorem guard (mode : Mode) (owners : List (Owner mode)) :
    StringPCWindows.Guard mode ((program mode owners).map (StringStoreWrites.liftDword mode)) := by
  induction owners with
  | nil => trivial
  | cons owner owners ih =>
    rw [program,List.flatMap_cons,List.map_append]
    exact StringPCGuards.append mode _ _ (guard_form mode owner) ih

end SmcTuring.Appendix.Listing8OriginalOwnerPC
