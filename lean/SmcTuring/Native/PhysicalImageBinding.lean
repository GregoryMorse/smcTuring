module
public import SmcTuring.Native.StringFetchPermissions
public import SmcTuring.Native.Relocation

public section
namespace SmcTuring.Native.PhysicalImageBinding
open MemoryRegion MappedExecution
set_option maxHeartbeats 2000000

/-- Supported normalized COFF payloads. Relative fields use the end of the
field PLUS the remaining instruction bytes,including REL32_1's suffix. -/
inductive RelocationKind where
  | absolute32 | absolute64 | relative32 (suffix : Nat)
  deriving DecidableEq
@[expose] def payload (kind : RelocationKind) (field target : Nat) : List LittleEndian.Byte :=
  match kind with
  | .absolute32 => LittleEndian.wordEncode 4 (BitVec.ofNat 32 target)
  | .absolute64 => LittleEndian.wordEncode 8 (BitVec.ofNat 64 target)
  | .relative32 suffix => LittleEndian.wordEncode 4 (Relocation.relative32 (field+4+suffix) target)
@[expose] def fits (kind : RelocationKind) (field target : Nat) : Prop :=
  match kind with
  | .absolute32 => target<2^32
  | .absolute64 => target<2^64
  | .relative32 suffix => Relocation.SignedDelta (field+4+suffix) target
@[expose] def resolve (kind : RelocationKind) (field : Nat) (bytes : List LittleEndian.Byte) : Option Int :=
  match kind with
  | .absolute32 => (LittleEndian.wordDecode 4 bytes).map fun value => (value.toNat : Int)
  | .absolute64 => (LittleEndian.wordDecode 8 bytes).map fun value => (value.toNat : Int)
  | .relative32 suffix => (LittleEndian.wordDecode 4 bytes).map fun value => (field+4+suffix : Nat)+value.toInt

/-- Exact normalization cannot silently truncate a relative relocation or
an absolute address. The byte decoder yields the intended loaded target. -/
theorem normalized_target (kind : RelocationKind) (field target : Nat) (bounded : fits kind field target) :
    resolve kind field (payload kind field target)=some (target : Int) := by
  cases kind with
  | absolute32 =>
    simp only [resolve,payload,LittleEndian.word_decode_encode,Option.map_some,BitVec.toNat_ofNat]
    change target<2^32 at bounded
    rw [Nat.mod_eq_of_lt bounded]
  | absolute64 =>
    simp only [resolve,payload,LittleEndian.word_decode_encode,Option.map_some,BitVec.toNat_ofNat]
    change target<2^64 at bounded
    rw [Nat.mod_eq_of_lt bounded]
  | relative32 suffix =>
    simp only [resolve,payload,LittleEndian.word_decode_encode,Option.map_some]
    rw [Relocation.relative32_toInt _ _ bounded]
    unfold Relocation.delta
    congr 1
    omega

theorem normalized_bytes (kind : RelocationKind) (field target : Nat) (memory : ByteMemory.Memory) :
    ByteMemory.bytesAt (ByteMemory.putBytes memory field (payload kind field target)) field (payload kind field target).length=
      payload kind field target := by
  apply List.ext_getElem
  · exact ByteMemory.bytes_at_length _ _ _
  · intro index leftBound rightBound
    simp only [ByteMemory.bytesAt,List.getElem_ofFn]
    exact ByteMemory.put_at_index memory field _ ⟨index,rightBound⟩

/-- Loaded symbol address and signed COFF addend,including backward/self
references. Sites are static object metadata,not execution premises. -/
structure Site where
  kind : RelocationKind
  field : Nat
  symbol : Nat
  addend : Int
@[expose] def Site.target (site : Site) : Nat := Int.toNat ((site.symbol : Int)+site.addend)
@[expose] def Site.bytes (site : Site) := payload site.kind site.field site.target
@[expose] def Site.Valid (site : Site) : Prop := 0≤(site.symbol : Int)+site.addend ∧ fits site.kind site.field site.target
@[expose] def Site.Separate (left right : Site) : Prop :=
  left.field+left.bytes.length≤right.field ∨ right.field+right.bytes.length≤left.field
@[expose] def normalize : List Site → ByteMemory.Memory → ByteMemory.Memory
  | [],memory => memory
  | site::rest,memory => normalize rest (ByteMemory.putBytes memory site.field site.bytes)

theorem site_target (site : Site) (valid : site.Valid) :
    resolve site.kind site.field site.bytes=some ((site.symbol : Int)+site.addend) := by
  have nonnegative := valid.1
  have target : (site.target : Int)=(site.symbol : Int)+site.addend := by
    unfold Site.target
    omega
  rw [Site.bytes,normalized_target site.kind site.field site.target valid.2,target]

/-- The complete relocation stream leaves every disjoint opcode/header/data
window unchanged,including bytes between relocation fields. -/
theorem normalize_frame (sites : List Site) (memory : ByteMemory.Memory) (address count : Nat)
    (separate : ∀ site∈sites,site.field+site.bytes.length≤address ∨ address+count≤site.field) :
    ByteMemory.bytesAt (normalize sites memory) address count=ByteMemory.bytesAt memory address count := by
  induction sites generalizing memory with
  | nil => rfl
  | cons site rest ih =>
    rw [normalize,ih _ (fun next member => separate next (List.mem_cons_of_mem _ member)),
      ByteMemory.bytes_at_frame memory site.field site.bytes address count (by
        intro index inside
        have order := separate site List.mem_cons_self
        unfold ByteMemory.Inside at inside
        have bound := index.isLt
        rcases order with before | after <;> omega)]

/-- Every nonoverlapping field resolves its exact loaded symbol plus addend
AFTER the whole stream;later patches cannot corrupt earlier normalized sites. -/
theorem normalize_targets (sites : List Site) (memory : ByteMemory.Memory)
    (valid : ∀ site∈sites,site.Valid) (separate : sites.Pairwise Site.Separate) :
    ∀ site∈sites,resolve site.kind site.field (ByteMemory.bytesAt (normalize sites memory) site.field site.bytes.length)=
      some ((site.symbol : Int)+site.addend) := by
  induction sites generalizing memory with
  | nil => intro site member;cases member
  | cons first rest ih =>
    obtain ⟨firstSeparate,restSeparate⟩ := List.pairwise_cons.mp separate
    intro site member
    rcases List.mem_cons.mp member with same | later
    · subst site
      rw [normalize,normalize_frame rest _ first.field first.bytes.length (by
        intro next member
        exact Or.symm (firstSeparate next member))]
      rw [Site.bytes,normalized_bytes]
      exact site_target first (valid first List.mem_cons_self)
    · exact ih _ (fun next member => valid next (List.mem_cons_of_mem _ member)) restSeparate site later

/-- Initial normalized object agreement is a PRESENT finite byte comparison;
no future state,trace,decoder validity or whole interpreter is an input. -/
structure Present (mode : Mode) (region : Region) (object : Image region)
    (loaded model : StringExecution.State mode) : Prop where
  pc : loaded.principal.pc=model.principal.pc
  accumulator : loaded.principal.accumulator=model.principal.accumulator
  stack : loaded.principal.stack=model.principal.stack
  carry : loaded.principal.carry=model.principal.carry
  source : loaded.sourceIndex=model.sourceIndex
  destination : loaded.destinationIndex=model.destinationIndex
  direction : loaded.backwards=model.backwards
  loadedBytes : snapshot region loaded.principal.memory=object
  normalizedObject : object=snapshot region model.principal.memory
  backing : ∀ position,¬(region.lower≤position ∧ position<region.upper) → loaded.principal.memory position=model.principal.memory position

theorem present_eq (mode : Mode) (region : Region) (object : Image region)
    (loaded model : StringExecution.State mode) (present : Present mode region object loaded model) : loaded=model := by
  have memory : loaded.principal.memory=model.principal.memory := by
    funext position
    by_cases inside : region.lower≤position ∧ position<region.upper
    · have equality := congrFun (present.loadedBytes.trans present.normalizedObject)
        (⟨position-region.lower,by unfold Region.size;omega⟩ : Fin region.size)
      simpa only [snapshot,Nat.add_sub_of_le inside.1] using equality
    · exact present.backing position inside
  rcases loaded with ⟨⟨pc,ax,sp,cf,bytes⟩,si,di,df⟩
  rcases model with ⟨⟨pc',ax',sp',cf',bytes'⟩,si',di',df'⟩
  cases present
  simp_all

/-- Abstract physical machine projection. Its ISA/configuration conditions
are named genuine physical assumptions;this is not an entire CPU/OS model. -/
structure CPU (mode : Mode) where
  State : Type
  project : State → StringExecution.State mode
  step : State → Option State
  flatSegments : Prop
  cetDisabled : Prop
  coherentFetch : Prop
  stableMapping : Prop
  compatibleABI : Prop

/-- Only one CURRENT fetched instruction is assumed to implement the selected
ISA effect under proved access/target validity. No source simulation,full run,
future image,termination or hardware stop is assumed. -/
structure ISA (mode : Mode) (environment : Environment) (cpu : CPU mode) : Prop where
  flatSegments : cpu.flatSegments
  cetDisabled : cpu.cetDisabled
  coherentFetch : cpu.coherentFetch
  stableMapping : cpu.stableMapping
  compatibleABI : cpu.compatibleABI
  instruction : ∀ (state : cpu.State) (form : StringStack.Form mode),
    StringStack.fetch mode (cpu.project state).principal.memory (cpu.project state).principal.pc.toNat=some form →
    StringFetchPermissions.Allowed mode environment (cpu.project state) →
    StringReadPermissions.Allowed mode environment form (cpu.project state) →
    Window mode environment .write (StringWrites.packet mode form (cpu.project state)).address
      (StringWrites.packet mode form (cpu.project state)).bytes.length →
    AddressSpace.Valid mode environment.paging (StringStack.execute mode form (cpu.project state)).principal.pc.toNat →
    ∃ next,cpu.step state=some next ∧ cpu.project next=StringStack.execute mode form (cpu.project state)

inductive Trace (mode : Mode) (cpu : CPU mode) : cpu.State → List (StringStack.Form mode) → cpu.State → Prop where
  | nil (state) : Trace mode cpu state [] state
  | step {state next finish : cpu.State} {form : StringStack.Form mode} {rest : List (StringStack.Form mode)}
      (actual : cpu.step state=some next)
      (current : StringStack.fetch mode (cpu.project state).principal.memory (cpu.project state).principal.pc.toNat=some form)
      (effect : cpu.project next=StringStack.execute mode form (cpu.project state))
      (tail : Trace mode cpu next rest finish) : Trace mode cpu state (form::rest) finish

/-- Every accepted physical event projects to the exact existing byte model. -/
theorem projected (mode : Mode) (cpu : CPU mode) {start finish : cpu.State} {forms : List (StringStack.Form mode)}
    (actual : Trace mode cpu start forms finish) : StringStack.Trace mode (cpu.project start) forms (cpu.project finish) := by
  induction actual with
  | nil => exact .nil _
  | step _ current effect _ ih => exact .step current (effect ▸ ih)

/-- All current classifier requests include the first three bytes,so mapped
fetch windows positively imply a canonical current control target. -/
theorem current_pc (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) (state : StringExecution.State mode)
    (within : StringFetchWindows.Within mode region state) : AddressSpace.Valid mode environment.paging state.principal.pc.toNat := by
  have member : 3∈StringFetchRequests.requests mode state.principal.memory state.principal.pc.toNat := by
    simp only [StringFetchRequests.requests,StringFetchRequests.control,StringFetchRequests.dword,StringFetchRequests.string,
      List.mem_append,List.mem_cons]
    exact Or.inl (Or.inl (Or.inl (Or.inl True.intro)))
  have bytes := (StringFetchPermissions.of_contained mode environment region mapping state within 3 member).1
  simpa only [Nat.add_zero] using (bytes ⟨0,by decide⟩).1

/-- Static mapping,present initial projection and local ISA semantics produce
all physical steps by induction on the ALREADY PROVED native trace. The final
canonical endpoint is a static numeric address condition,not a stop premise. -/
theorem realize (mode : Mode) (environment : Environment) (region : Region)
    (mapping : Mapped mode environment region) (cpu : CPU mode) (isa : ISA mode environment cpu)
    {model finish : StringExecution.State mode} {forms : List (StringStack.Form mode)}
    (actual : StringStack.Trace mode model forms finish)
    (fetches : StringFetchWindows.Run mode region forms model)
    (reads : StringReadRuns.Run mode region forms model)
    (owned : StringWrites.OwnedRun mode region.lower region.upper forms model)
    (finalPC : AddressSpace.Valid mode environment.paging finish.principal.pc.toNat)
    (state : cpu.State) (present : cpu.project state=model) :
    ∃ physicalFinish,Trace mode cpu state forms physicalFinish ∧ cpu.project physicalFinish=finish := by
  induction actual generalizing state with
  | nil => exact ⟨state,.nil _,present⟩
  | @step model finish forms form current tail ih =>
    have nextPC : AddressSpace.Valid mode environment.paging (StringStack.execute mode form model).principal.pc.toNat := by
      cases forms with
      | nil => cases tail;exact finalPC
      | cons next rest => exact current_pc mode environment region mapping _ fetches.2.1
    have allowed := StringFetchPermissions.of_contained mode environment region mapping model fetches.1
    have read := StringReadPermissions.of_contained mode environment region mapping form model reads.1
    have write := window_of_contains mode environment region mapping .write _ _ ⟨owned.1.2.1,owned.1.2.2⟩
    obtain ⟨next,stepped,effect⟩ := isa.instruction state form (present ▸ current) (present ▸ allowed)
      (present ▸ read) (present ▸ write) (present ▸ nextPC)
    obtain ⟨last,physical,lastProjection⟩ := ih fetches.2 reads.2 owned.2 finalPC next (by rw [effect,present])
    exact ⟨last,.step stepped (present ▸ current) effect physical,lastProjection⟩

/-- Every physical prefix has the SAME reached projection as the mathematical
prefix;this transports all executable/owner,access and observation certificates. -/
theorem at_prefix (mode : Mode) (cpu : CPU mode) {state finish : cpu.State} {forms : List (StringStack.Form mode)}
    (actual : Trace mode cpu state forms finish) (before after : List (StringStack.Form mode)) (cut : forms=before++after) :
    ∃ reached,Trace mode cpu state before reached ∧ Trace mode cpu reached after finish ∧
      cpu.project reached=StringWrites.run mode before (cpu.project state) := by
  induction before generalizing state forms with
  | nil =>
    have shifted : forms=after := by simpa only [List.nil_append] using cut
    rw [shifted] at actual
    exact ⟨state,.nil _,actual,rfl⟩
  | cons form rest ih =>
    subst forms
    cases actual with
    | step stepped current effect tail =>
      obtain ⟨reached,leading,later,projection⟩ := ih tail rfl
      refine ⟨reached,.step stepped current effect leading,later,?_⟩
      change cpu.project reached=StringWrites.run mode rest (StringStack.execute mode form (cpu.project state))
      rw [←effect]
      exact projection

end SmcTuring.Native.PhysicalImageBinding
