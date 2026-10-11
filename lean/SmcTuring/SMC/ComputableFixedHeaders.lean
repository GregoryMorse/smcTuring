module
public import SmcTuring.SMC.ComputableHeader
public import SmcTuring.SMC.ConcreteImage

public section

namespace SmcTuring.SMC.Effective

open Dolan.Encoding

/-- A fixed finite cache of all reader templates. There is no header oracle. -/
@[expose] def readerHeaderCodes : List (List HeaderCode) :=
  (List.range 23).map (fun index => (Concrete.readerProgram index).map headerCode)

@[expose] def fixedControlHeaderCode (pc : Nat) : Option HeaderCode :=
  if pc < 184 then (readerHeaderCodes[pc / 8]?).bind (fun row => row[pc % 8]?)
  else if pc < 224 then ((Concrete.guardProgram false).map headerCode)[pc - 184]?
  else if pc < 264 then ((Concrete.guardProgram true).map headerCode)[pc - 224]?
  else (Concrete.kernelProgram.map headerCode)[pc - 264]?

theorem fixed_control_header_code_correct (pc : Nat) :
    fixedControlHeaderCode pc = (Concrete.controlHeader pc).map headerCode := by
  by_cases reader : pc < 184
  · have row : pc / 8 < 23 := by omega
    simp [fixedControlHeaderCode, Concrete.controlHeader, reader, readerHeaderCodes, List.getElem?_range row]
  · by_cases firstGuard : pc < 224
    · simp [fixedControlHeaderCode, Concrete.controlHeader, reader, firstGuard]
    · by_cases secondGuard : pc < 264 <;>
        simp [fixedControlHeaderCode, Concrete.controlHeader, reader, firstGuard, secondGuard]

theorem fixed_control_header_code_primrec : Primrec fixedControlHeaderCode := by
  have row := Primrec.list_getElem?.comp (Primrec.const readerHeaderCodes) (Primrec.nat_div.comp Primrec.id (Primrec.const 8))
  have reader : Primrec (fun pc : Nat => (readerHeaderCodes[pc / 8]?).bind (fun values => values[pc % 8]?)) :=
    Primrec.option_bind row (Primrec.list_getElem?.comp Primrec.snd (Primrec.nat_mod.comp Primrec.fst (Primrec.const 8))).to₂
  exact Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 184)) reader
    (Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 224))
      (Primrec.list_getElem?.comp (Primrec.const ((Concrete.guardProgram false).map headerCode)) (Primrec.nat_sub.comp Primrec.id (Primrec.const 184)))
      (Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const 264))
        (Primrec.list_getElem?.comp (Primrec.const ((Concrete.guardProgram true).map headerCode)) (Primrec.nat_sub.comp Primrec.id (Primrec.const 224)))
        (Primrec.list_getElem?.comp (Primrec.const (Concrete.kernelProgram.map headerCode)) (Primrec.nat_sub.comp Primrec.id (Primrec.const 264)))))

@[expose] def fixedStorageHeaderCode (magnitude : Nat) : Option HeaderCode :=
  if magnitude % 2 = 0 then some (1, (2, 2 * (magnitude / 2 - 1))) else
  let index := (magnitude - 1) / 2
  if And (25 <= index) (index < 38) then some (1, (2, 2 * index + 1)) else none

theorem meta_field_code (index : Nat) : zigzag (Concrete.metaField index) = 2 * index + 1 := by
  have scalar : Concrete.metaField index = Int.negSucc index := by
    simp only [Concrete.metaField, Int.negSucc_eq]
  rw [scalar]
  rfl

theorem fixed_storage_header_code_correct (pc : Int) :
    fixedStorageHeaderCode (-pc).toNat = (Concrete.storageHeader pc).map headerCode := by
  by_cases even : (-pc).toNat % 2 = 0
  · simp [fixedStorageHeaderCode, Concrete.storageHeader, even, headerCode, addressCode, zigzag]
  · by_cases active : And (25 <= ((-pc).toNat - 1) / 2) (((-pc).toNat - 1) / 2 < 38)
    · simp [fixedStorageHeaderCode, Concrete.storageHeader, even, active, headerCode, addressCode, meta_field_code]
    · simp [fixedStorageHeaderCode, Concrete.storageHeader, even, active]

theorem fixed_storage_header_code_primrec : Primrec fixedStorageHeaderCode := by
  have index : Primrec (fun magnitude : Nat => (magnitude - 1) / 2) :=
    Primrec.nat_div.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)) (Primrec.const 2)
  have dataField := Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_sub.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)) (Primrec.const 1))
  have metadataField := Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) index)
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
    (Primrec.option_some.comp (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const 2) dataField)))
    (Primrec.ite ((Primrec.nat_le.comp (Primrec.const 25) index).and (Primrec.nat_lt.comp index (Primrec.const 38)))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const 1) (Primrec.pair (Primrec.const 2) metadataField))) (Primrec.const none))

/-- Lookup of the actual constructed image, including negative-PC templates
and missing headers. The only runtime input is one canonical integer code. -/
@[expose] def fixedHeadersCode (pc : Nat) : Option (Prod HeaderCode Nat) :=
  (if pc % 2 = 0 then fixedControlHeaderCode (pc / 2) else fixedStorageHeaderCode (pc / 2 + 1)).map
    (fun header => (header, addCode pc 2))

theorem fixed_headers_code_correct (pc : Int) :
    fixedHeadersCode (zigzag pc) = (Concrete.headers pc).map (fun entry => (headerCode entry.1, zigzag entry.2)) := by
  have next := add_correct pc 1
  change addCode (zigzag pc) 2 = zigzag (pc + 1) at next
  have selected :
      (if zigzag pc % 2 = 0 then fixedControlHeaderCode (zigzag pc / 2) else fixedStorageHeaderCode (zigzag pc / 2 + 1)) =
        (if 0 <= pc then Concrete.controlHeader pc.toNat else Concrete.storageHeader pc).map headerCode := by
    cases pc with
    | ofNat number => simp [zigzag, Nat.mul_comm, fixed_control_header_code_correct]
    | negSucc number =>
      have half : (number * 2 + 1) / 2 = number := by omega
      simp [zigzag, Nat.mul_comm, half]
      simpa using fixed_storage_header_code_correct (Int.negSucc number)
  unfold fixedHeadersCode Concrete.headers
  rw [selected, next]
  simp only [Option.map_map, Function.comp_def]

theorem fixed_headers_code_primrec : Primrec fixedHeadersCode := by
  have selected : Primrec (fun pc : Nat =>
      if pc % 2 = 0 then fixedControlHeaderCode (pc / 2) else fixedStorageHeaderCode (pc / 2 + 1)) :=
    Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
      (fixed_control_header_code_primrec.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
      (fixed_storage_header_code_primrec.comp (Primrec.succ.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2))))
  exact Primrec.option_map selected (Primrec.pair Primrec.snd
    (add_primrec.comp Primrec.fst (Primrec.const 2))).to₂

end SmcTuring.SMC.Effective
