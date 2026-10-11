> Current closure (2026-10-11): all seven rounds are accepted. Complete public
> proof/native CI and Palomar full mechanical preflight pass. See
> [closure status](CLOSURE_STATUS.md) and [final acceptance](FINAL_ACCEPTANCE.json).
> Dated progress comments below are historical and do not reopen closed obligations.

# Printed x86 branch byte contract

Date: 2026-10-05. E10 supplies a normalized whole native branch fixture; E11
supplies 24 kernel-checked packet codec/current-patch declarations. E12-E14
add 68 instruction-effect, finite-field refinement and all-relation byte-state
declarations. E15-E19 now derive the complete reference predicate/patch prefix live trace
from its literal initializer. E20-E24 close the complete reference byte tail and
selected continuation; E25-E30 close ordered forward host spacing; other geometry/physical ISA remain open.

## Selected literal forms

`Appendix/ByteCode` uses 32-bit words and x86 absolute addressing. It does not
model x64 operand/address forms. The exact selected opcode/ModR/M forms are:

| Operation | Header bytes | Packet bytes | Operands |
| --- | --- | --- | --- |
| MOV [address], imm32 | C7 05 | 10 | address +2, immediate +6 |
| XOR [address], imm32 | 81 35 | 10 | address +2, immediate +6 |
| AND [address], imm32 | 81 25 | 10 | address +2, immediate +6 |
| XCHG [address], EAX | 87 05 | 6 | address +2 |
| XCHG [address], ESP | 87 25 | 6 | address +2 |
| SUB [address], EAX | 29 05 | 6 | address +2 |
| ADD [address], EAX | 01 05 | 6 | address +2 |
| NEG [address] | F7 1D | 6 | address +2 |
| NOT [address] | F7 15 | 6 | address +2 |
| SBB [address], 0 | 83 1D | 7 | address +2, fixed zero +6 |
| ADD [address], 4 | 83 05 | 7 | address +2, fixed four +6 |
| MOV [address], EAX | A3 | 5 | address +1 |
| CALL rel32 | E8 | 5 | displacement +1 |

The complete payloads are little endian. The round-trip theorem covers every
32-bit operand bit pattern. Encoding is injective. Fixed SBB/ADD trailers are
validated by the restricted decoder. Packet length is chosen only from at most
the first two bytes, independent of mutable addresses/immediates/displacements.
The 13 shapes exported by `ExportBranchEncoding.lean` are finite comparator
output from these checked definitions; evaluation is not itself a kernel theorem.

## Real current-memory patches

The packet proofs establish the following whole-byte-memory effects:

- A four-byte immediate patch at +6 preserves the operation/address and consumes
  the complete fresh immediate on subsequent opcode-derived live fetch.
- A four-byte CALL patch at +1 preserves E8 and consumes the fresh rel32.
- A four-byte address patch at +2 preserves both opcode/ModR/M and the following
  imm32. This covers the deliberate DEFSTACK CALL-return/MOV-address alias.
- The general `patch_middle` theorem preserves a following byte suffix of any
  length; `put_bytes_append` derives consecutive image placement.

The current-packet theorems start from actual current memory, rather than a
repeated image initializer or an assumed future packet. Whole-memory patch
identities and the existing byte-write frame lemma preserve every byte outside
the written four-byte field, including unchanged-value stores. They do not
supply a physical instruction-fetch coherence law. E12-E14 now connect selected
instruction effects to the finite field-word branch proof; the complete live
trace from the literal emitter is still to be constructed. `ByteCode` fetch
takes natural byte positions; `ByteExecution` uses 32-bit PC words. Full emitted
packet/PC bounds and resource validity remain explicit refinement obligations.

## Selected execution and finite field refinement

`Appendix/ByteExecution` supplies 32 checked declarations. Each of the 13 forms
has exact PC/EAX/ESP/CF and whole byte-memory effects for all input words and
initial states in the selected sequential effect model. Every instruction writes
four destination bytes. CALL's destination is the decremented ESP return slot;
its target is computed before that write. NEG sets CF for a nonzero original
operand, NOT preserves CF, SBB consumes the incoming CF, and ADD derives unsigned
overflow. The seven shared forms have identical encodings and effects to the
existing selected native model. Opcode-derived `step` fetches from current
memory; a patched immediate, rel32 or address is used by the subsequent step.
The trace and owned-run composition laws do not reinitialize the memory.

`Appendix/FieldRefinement` supplies 20 checked declarations. A finite selected
set of natural field coordinates must have complete four-byte ranges within
2^32, with every distinct pair of ranges disjoint. Agreement covers those words,
EAX and CF. Each source instruction translates to a selected byte form; dynamic
AND/XOR operands are actual loads from the current source field in byte memory.
No selected predicate, result mask or future native state is supplied. The proof
preserves agreement for one step and arbitrary finite source programs, preserves
ESP, gives outside-byte frames and establishes conditional code-word ownership.
Equal loaded words imply equal entire original byte windows, without assuming
that the initial bytes were written by an encoder.

`Appendix/BranchExecution` supplies 16 checked declarations. Initial source words
are derived from actual byte loads. All dependencies of the printed relation
program belong to its five fields. Under the physical field layout and the
printed distinct-field contract, the actual selected byte effects yield all six
signed/unsigned branch displacement results, the modular target equation,
restored EAX/ESP/input words, final CF=false and every byte outside the three
final scratch fields. In particular, x/y's temporarily changed bytes are restored.
There is also a corollary for a supplied actual current-fetch trace.

These are instruction-effect and finite-field refinements. `translate` loads a
dynamic immediate from its source field; it does not yet prove that the executing
instruction's own immediate occupies that exact field. E15-E19 now derive that identity, protected headers/constants, contiguous
nonwrapping prefix PCs, all prefix fetches and both protected continuation
images from one reference initializer. E20-E24 now compose their complete tail
and selected continuation in that SAME evolving byte image, including the
actual CALL target, deliberate return/address alias and both continuation PCs.
The older trace corollary still explicitly has a trace premise; the new
`BranchWhole.correct` constructs the whole reference trace from image/entry/extent. Physical
ISA faults, other architectural state, configuration and instruction-fetch
coherence remain realization conditions.

## Whole native regression

Run `python validation/run_branch.py`. `generate_branch.py` transcribes the
checked prefix and Listing 4's literal single-XCHG/CALL plus five-instruction
JUMPTARGET at both selected endpoints. M05 provides a separate target parameter.
DWORD types and imm32 owners are explicit; SBB zero and ADD four retain imm8.
The bracketed NEAR-code-label CALL stays E8. There are no hidden padding bytes
within a reached pure prefix/tail/continuation block. The two continuation blocks
are each 30 bytes, with the five-byte A3 accumulator store. Host observation
instructions sit after each pure continuation boundary and are excluded from
its purity claim. Unreached MOV storage owners are disclosed as in M03.

`branch.json` records 12 variants (six relations, signed and unsigned), 6,200
cases per variant and 74,400 total. Each variant has 1,200 Cartesian edge cases
and 5,000 deterministic random cases, both initial CF values, arbitrary initial
accumulator and scratch words, and both branch outcomes. The independent C++
reference uses mathematical signed/unsigned comparisons, rather than SBB masks.

Every case checks the selected endpoint, all eight general registers including
ESP/EBP, final CF=false, restored input words and DEFSTACK address/immediate,
exact delta/mask/displacement and every code byte outside the three final scratch
fields. A crash/timeout or wrong result is a fixture failure, not an intended
source-machine halt. Host setup writes and observations are outside the pure
paths. The process runs single-threaded with writable executable code, disabled
CET shadow stacks and host `FlushInstructionCache` before each entry; these
observations do not prove arbitrary physical self-modifying fetch behavior.

MASM/COFF checks cover 338 selected/storage headers, 84 real owned fields and
338 field relocations across the 12 layouts, all checked against 13 Lean codec
shapes. Each write lands in a real operand field; all seven fields in a fixture
are disjoint and avoid all selected/storage opcode and ModR/M bytes. The CALL
push-slot identity is the actual defining MOV address field. COFF addresses are
validated using both raw addends and their referenced code-section symbols;
[Microsoft's PE/COFF specification](https://learn.microsoft.com/en-us/windows/win32/debug/pe-format)
is the relocation reference. SHA256 records cover all source/proof/export files,
commands and generated assembly/header/manifest/shape/object/listing/executable
artifacts. The final evidence audit rejects stale proof/native provenance.

E02/E05 remain IN_PROGRESS: derive the general literal emitter offsets/owners,
identify the dynamic operands with their actual own instruction fields, compose
the byte-level tail/return alias, and construct the full continuous live-byte
execution and both continuation IPs,
and retain explicit physical ISA/configuration/fetch assumptions. The remaining
appendix algorithms and original full architectural-state claims are separate.

E15-E19 now construct the reference emitter's complete live-byte predicate/patch
prefix from one initial image, entry and extent bound: actual x/y words, seven
real owners, own imm32 identities, protected constants/headers, field layout,
every fetched form/next PC and all-relation register/word/CF/exterior-byte results.
The native comparator checks 158 complete prefix packets and their exact own
operand coordinates against twelve Lean emitter exports. E20-E24 close the complete reference byte-tail/return-alias/continuation
execution and PCs. General host-spacing and physical ISA/fetch remain open. See [APPENDIX_BYTE_IMAGE.md](APPENDIX_BYTE_IMAGE.md).

E25-E30 add 72 checked declarations for independently spaced, ordered forward
x86 branch blocks. One original byte image supplies all pure fetches; the actual
Taken-Fall displacement, both continuation end PCs, EAX/ESP/CF restoration,
every owned DWORD write and exact host-gap backing bytes are derived. The native
comparator now checks all 338 complete pure packets at the actual twelve COFF
layouts, including target constants, destinations/owner coordinates and end PCs.
Only absolute payloads are normalized, with separate symbol/addend/relocation
checks. The actual host gaps are 50/12/76 bytes. Other region orderings/backward
geometry and physical ISA/configuration/coherent fetch remain separate.
See [APPENDIX_BYTE_SPACING.md](APPENDIX_BYTE_SPACING.md).
