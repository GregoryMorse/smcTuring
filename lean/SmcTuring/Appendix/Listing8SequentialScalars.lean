module
public import SmcTuring.Appendix.Listing8MainPrefix
public import SmcTuring.Native.StringSequentialFamilies

public section
namespace SmcTuring.Appendix.Listing8SequentialScalars
open Native Listing8CopyImage

theorem owners (mode : Mode) (owners : List (Listing8OwnerSequence.Owner mode)) :
    ∀ form∈(Listing8OwnerSequence.program mode owners).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  intro form member
  rcases List.mem_map.mp member with ⟨middle,innerMember,rfl⟩
  rcases List.mem_flatMap.mp innerMember with ⟨owner,_,ownerMember⟩
  cases owner with
  | pointer source pc value =>
    simp only [Listing8OwnerSequence.forms,List.mem_map] at ownerMember
    rcases ownerMember with ⟨original,packetMember,rfl⟩
    cases mode <;> simp only [Listing8CopiedPointer.forms,List.mem_cons,List.not_mem_nil,or_false] at packetMember <;>
      rcases packetMember with rfl | rfl | rfl | rfl <;>
      simp [StringStoreWrites.liftDword,StringPCSteps.Sequential,StringPCSteps.ControlSequential,StringPCSteps.DwordSequential,
        StringPCSteps.StringSequential,StringPCSteps.NativeSequential,Listing8CopiedPointer.first,Listing8CopiedPointer.second,Reader.storeForm]
  | scalar pc target value =>
    simp only [Listing8OwnerSequence.forms,List.mem_cons,List.not_mem_nil,or_false] at ownerMember
    subst middle
    cases mode <;> trivial

theorem pointers (mode : Mode) (l : Layout) (t : Listing8PointerCopies.Targets) :
    ∀ form∈(Listing8PointerCopies.program mode l t).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8PointerCopies.program,List.map_append,List.mem_append]
  intro form member
  rcases member with word | dwords
  · exact StringSequentialFamilies.word mode _ form word
  · exact StringSequentialFamilies.sequence mode _ form dwords

theorem retarget (mode : Mode) (l : Layout) (v : Values mode) :
    ∀ form∈(Listing8LiveRetarget.program mode l v).map (StringStoreWrites.liftDword mode),StringPCSteps.Sequential mode form := by
  simp only [Listing8LiveRetarget.program,List.map_append,List.map_cons,List.map_nil,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with patch | rfl
  · exact StringSequentialFamilies.retargets mode _ form patch
  · cases mode <;> trivial

end SmcTuring.Appendix.Listing8SequentialScalars
