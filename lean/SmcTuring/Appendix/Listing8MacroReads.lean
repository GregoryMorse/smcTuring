module
public import SmcTuring.Appendix.Listing8MacroWrites
public import SmcTuring.Native.StringMoveReads

public section
namespace SmcTuring.Appendix.Listing8MacroReads
open Native StringMacroLayout StringMacroEffects
abbrev Placement:=Listing8MacroWriteBounds.Placement

theorem setup_local (mode : Mode) (start source destination : Nat) :
    ∀ form∈(StringSetup.forms mode start source destination).map (StringWrites.liftString mode),StringReadWindows.Local mode form := by
  cases mode <;> simp [StringSetup.forms,StringSetup.sourceForms,StringInit.forms,StringOperands.exchange,
    StringWrites.liftString,StringReadWindows.Local,StringReadWindows.ControlLocal,StringReadWindows.DwordLocal,
    StringReadWindows.StringLocal,StringReadWindows.NativeLocal]

theorem restore_local (mode : Mode) (destination : Bool) (pc field size : Nat) :
    ∀ form∈(StringRestore.forms mode destination pc field size).map (StringWrites.liftString mode),StringReadWindows.Local mode form := by
  simp only [StringRestore.forms,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
  intro form member
  rcases member with rfl | rfl
  · trivial
  · unfold StringOperands.subtract
    split <;> trivial

theorem setup (mode : Mode) (start stop : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode start stop p) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((StringSetup.forms mode p.start p.source p.destination).map (StringWrites.liftString mode)) state :=
  StringReadRuns.local_of_owned mode start stop _ state (setup_local mode p.start p.source p.destination)
    (Listing8MacroWrites.setup mode start stop p state ready placed)

theorem moves (mode : Mode) (start stop : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode start stop p) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((StringMoves.forms mode (StringPlan.widths mode p.size)).map (StringWrites.liftString mode))
      (StringMacroEffects.setup mode p state) := by
  have total:=StringPlan.total mode p.size
  change (StringPlan.widths mode p.size).sum=p.size at total
  have source:=source_capacity mode p state ready
  have forward : (StringMacroEffects.setup mode p state).backwards=false := by rw [setup_effect mode p state ready];exact ready.forward
  have pointer : (StringMacroEffects.setup mode p state).sourceIndex.toNat=p.source := by
    rw [setup_effect mode p state ready,Arithmetic.encode_nat_toNat mode _ source.2.2]
  have fits : (StringMacroEffects.setup mode p state).sourceIndex.toNat+(StringPlan.widths mode p.size).sum<2^(8*mode.wordBytes) := by
    rw [pointer,total];exact source.1
  apply StringMoveReads.contained mode start stop _ _ forward fits
  rw [pointer,total]
  exact ⟨placed.source.1,Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) _) placed.source.2⟩

theorem restores (mode : Mode) (start stop : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode start stop p) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((StringRestore.forms mode false (sourceTail mode p) (StringCodec.sourceField mode p.start) p.size).map (StringWrites.liftString mode))
      (copied mode p state) ∧
    StringReadRuns.Run mode ⟨start,stop⟩ ((StringRestore.forms mode true (destinationTail mode p) (StringCodec.destinationField mode p.start) p.size).map (StringWrites.liftString mode))
      (sourceRestored mode p state) := by
  have owned:=Listing8MacroWrites.restores mode start stop p state ready placed
  exact ⟨StringReadRuns.local_of_owned mode start stop _ _ (restore_local mode false _ _ _) owned.1,
    StringReadRuns.local_of_owned mode start stop _ _ (restore_local mode true _ _ _) owned.2⟩

/-- Every actual read in the literal TRANSFERDATA macro follows from its
original ready image, static placement and complete store certificates.
Both SI source windows and all scalar/reader cursor windows are included. -/
theorem contained (mode : Mode) (start stop : Nat) (p : Params) (state : StringExecution.State mode)
    (ready : Ready mode p state) (placed : Placement mode start stop p) :
    StringReadRuns.Run mode ⟨start,stop⟩ ((StringProgram.forms mode p.start p.source p.destination p.size).map (StringWrites.liftString mode)) state := by
  have a:=setup mode start stop p state ready placed
  have b:=moves mode start stop p state ready placed
  have c:=restores mode start stop p state ready placed
  simp only [StringProgram.forms,List.map_append,StringReadRuns.append,StringWrites.run_append,StringWrites.run_lift_string]
  exact ⟨⟨⟨a,b⟩,c.1⟩,c.2⟩

end SmcTuring.Appendix.Listing8MacroReads
