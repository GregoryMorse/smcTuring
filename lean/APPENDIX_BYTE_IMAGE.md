# Constructed printed x86 branch

Date: 2026-10-05. E15-E19 supply 64 checked declarations for the reference
emitter and prefix. E20-E24 add 56 declarations closing its complete current-byte
branch: predicate/patch prefix, XCHG ESP/CALL tail and the selected five-instruction
continuation. One initialized byte image supplies every actual fetch for all
twelve signed/unsigned relation variants. Arbitrary incoming registers/CF,
32-bit inputs and backing bytes are allowed.

## Exact reference image

`Appendix/BranchLayout` emits DEFSTACK, the normalized Listing 10 predicate/patch
prefix, a single XCHG ESP/CALL tail, both literal five-instruction JUMPTARGET
continuations, and two inactive self-writing MOV input owners. All packet lengths
come from the selected byte codec. Both continuations occupy 30 bytes. There are
no padding or observation instructions in a pure packet sequence. Input owners
are inactive storage, with the M03 static-coverage limitation retained. M05's
independent target normalization remains explicit.

Let B be the image base, P = B + 10 the prefix entry, and
L = 61 + 40*signed + 12*(relation is EQ/NE) + 6*(relation is LE/EQ/GE).
The computed layout is:

| Element | Byte coordinate | Actual owned word |
| --- | --- | --- |
| DEFSTACK MOV | B | address B+2 and immediate/pointer B+6 |
| Prefix entry | P | none |
| Final AND packet | P+L | Delta at P+L+6 |
| Final XOR packet | P+L+10 | Mask at P+L+16 |
| Stack exchange | P+L+20 | none |
| CALL | P+L+26 | Displacement at P+L+27 |
| Fall continuation | P+L+31 | none |
| Taken continuation | P+L+61 | none |
| X storage MOV | P+L+91 | X at P+L+97 |
| Y storage MOV | P+L+101 | Y at P+L+107 |
| Image end | P+L+111 | none |

The prefix has 10-17 instructions and 81-139 bytes. The target relocation is
encoded Taken minus encoded Fall. The reference continuation blocks are adjacent;
the native harness includes separate host setup/observation/capture regions.
The complete reference image is not asserted to equal the harness byte-for-byte.
The comparator below verifies each pure prefix and its own mutable operand
coordinates, with independently checked actual COFF relocations.

## What Lean constructs

`Appendix/ByteImage` has 21 declarations. Fixed packets retain all their bytes;
mutable packets own their immediate, CALL displacement, or both address and
immediate. Actual word loads from encoded current operand windows are proved.
The finite initializer supplies exact packets. Every owned four-byte write
preserves the complete protected packet invariant, including both DEFSTACK
fields, and automatic fetch reconstructs the live form from current bytes.

`Appendix/BytePacking` has 14 declarations. Adjacent placement derives complete
packet bounds and separation. Actual owner fields within a packet or different
packets have disjoint four-byte ranges. One bound on the full image extent derives
all finite field capacity/separation conditions. Exterior backing bytes are framed.

`Appendix/ByteProgram` has seven declarations. Static links identify each AND/XOR
source field with the executing instruction's own +6 immediate. Fixed constants
and addresses come from protected packets. Actual current forms equal the earlier
word-instruction translation. From an initial protected image, static placement,
ownership, links and capacity, induction constructs every opcode-derived fetch
and next PC, preserves the image after each actual write, and reaches the computed
prefix end. No future trace, future packet, repeated initializer or future Ready
predicate is an input.

`Appendix/BranchLayout` has nine declarations. For all twelve variants it derives
the exact span, own-immediate links, all seven actual owner fields, distinct branch
fields and the full physical four-byte layout from the complete image-extent
bound. Both continuation packet sequences are included in the same initializer.

`Appendix/BranchPrefix` has 13 declarations. Prefix and input-storage membership,
the actual initial x/y words, entry/end bounds and the complete live-fetch prefix
trace follow from this emitter. Arbitrary input words, incoming EAX/ESP/CF and
backing bytes are allowed. The prefix selects the signed/unsigned relation on
those input words, restores EAX/ESP/x/y, clears CF, and restores every byte outside
the final Delta/Mask/Displacement fields. Its writes preserve every packet in the
whole image. The initialized-image theorem has only the initial memory equality,
complete extent bound and entry PC as execution premises. The generic trace theorem
also applies to other initially intact images with the specified static layout.

`Appendix/ByteControl` has 16 declarations. Full four-byte loads/stores and
disjoint windows yield exact XCHG ESP/EAX, ADD DWORD 4, A3 store and CALL effects.
The CALL displacement is read after the stack exchange and its target is evaluated
before the return-slot write. The five continuation instructions restore the
ENTIRE byte memory to the pre-tail image when DEFSTACK's two fields have their
literal values and slot/address alias. The ADD clears CF under the derived
nonwrapping pointer condition; no successful CALL or future fetch is assumed.

`Appendix/ByteLinear` has eight declarations. For fixed fall-through packets,
static placement/ownership/capacity and an initial intact image construct every
current-byte fetch, next PC and protected image invariant by induction. CALL is
excluded from this helper. Its all-state ownership premise specifies fixed
constant destinations and supplies no future state, packet or execution trace.

`Appendix/BranchControl` has ten declarations. It derives the full seven-field
layout, both stack-field owners, complete byte-window separation, pointer-4
address alias and nonwrap condition from the finite extent. The literal DEFSTACK
bytes initialize both words to B+6. The actual prefix leaves these words unchanged,
proved byte by byte outside the final scratch fields.

`Appendix/BranchPaths` has five declarations. The tail and both continuations
are located at their computed PCs in the original initializer. Two actual
current-byte fetches execute the stack exchange and CALL; the latter writes the
owned address field B+2. Their writes preserve all protected packet bytes.

`Appendix/BranchWhole` has 17 declarations. It composes one continuous trace
through prefix, tail and the selected continuation, derives the actual chosen
PC from the signed/unsigned relation and CALL displacement, and proves every
reached instruction writes a nonempty DWORD entirely within an owned code field.
EAX and ESP are restored, CF is false, every protected packet remains intact and
every byte outside Delta/Mask/Displacement equals the ORIGINAL input memory.
The two DEFSTACK words, both input words and all other backing bytes are included
in that frame. Tail/continuation memory equals the prefix result exactly.
`correct` packages these results with only image, entry PC and finite extent as
execution premises; no future trace, Ready predicate or reinitializer is supplied.

For a false predicate, the continuation begins at Fall and ends at Taken; for a
true predicate it begins at Taken and ends at X storage. These are the declared
finite observation boundaries in this dense reference image. They do not assert
source halt or that the next inactive owner will never be reached under continued
hardware execution. The native harness observes the corresponding outcomes in
separate host regions.

The theorems use the selected sequential, nonfaulting PC/EAX/ESP/CF/unified
byte-memory projection. Other x86 state, physical ISA realization, permissions,
CET configuration and coherent instruction fetch remain explicit assumptions.

## Native comparison and remaining work

`ExportBranchLayout.lean` evaluates the checked emitter definitions for twelve
reference variants. This JSON export is finite comparator output, not a theorem.
`run_branch.py` compares all 158 actual MASM prefix packets in order against it:
full packet length/header/trailer/fixed constants and logical destination role.
Absolute-address payloads and the one independently checked target relocation
immediate are normalized for this comparison; other immediate bits are retained.
It also compares exact AND/XOR/CALL/Fall offsets and all three own mutable field
coordinates. The existing COFF checks validate each actual address, symbol target,
relocation expression, owner field and pure-block continuity. Source/artifact/
export/proof hashes bind these checks to the full audited Lean snapshot.

E02/E05 remain IN_PROGRESS for general host spacing/continuation placement,
physical ISA/fetch realization and the other appendix algorithms. The complete
reference branch's byte tail, literal return/address alias and both continuation
end PCs are now checked by E20-E24. Native comparisons are finite regression
evidence; they do not identify the whole dense Lean image with the harness's
spaced image or prove physical instruction-fetch coherence. Other published
listings and registry packaging remain separate obligations. No submission or
PDF edit is made.

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
