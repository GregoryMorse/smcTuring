# Listing 6 constant multiplication

The authoritative source is printed p.125 of the cached 2018 publication,
SHA256 `adf6d155c941770228d416ba16ef6dc4196420739034747e1ba57361bdda1a6e`.
Its compile-time emitter consumes the constant's low set bits. M08 therefore
changes **Leading** to **Trailing** in NLZ's description, retains the identifier
and initial shift, and adds **+1** to the two later SHL counts. The original
copy/accumulate/final-ADD structure is retained. The exact excerpt contexts are
in [edits.json](errata/edits.json) and [minimal diff](errata/morse-2018-minimal.diff).

The local contract treats constants as unsigned 32-bit patterns, with the same
low-word result for signed two's-complement multiplication. All conditionals
and logical right shifts occur at compile time; a shift by 32 consumes the
whole constant rather than using x86's masked runtime count. Zero specializes
to one MOV clearing the data word. An initial shift by zero is omitted, so an
identity constant may emit an empty trace. Data and the final ADD immediate
occupy distinct complete code-operand words. Initial scratch may be arbitrary:
the first retained partial product initializes it on every invocation.

[ConstantAlgebra.lean](SmcTuring/Appendix/ConstantAlgebra.lean) has 18 positive
results. For nonzero v, with t its trailing-zero count and r=v/2^(t+1), it proves
v=2^t(1+2r). The initial partial product and subsequent gaps preserve the intended
product modulo 2^32. Every consumed remainder decreases; the complete bounded
recurrence gives the product for every input and constant. `signed_low_product`
connects arbitrary integer operands to their low 32-bit signed product.

[ConstantWords.lean](SmcTuring/Appendix/ConstantWords.lean) has 23 positive
results for the actual emitted word sequence. Copy and scratch accumulation
expand into the printed exchange/use-accumulator/exchange triples. The final
ADD reads its current immediate field. `contract` derives the all-input result,
restored EAX, code-write purity, exterior-word frame and a 128-instruction upper
bound, with arbitrary initial scratch/backing memory. `program_legal` derives
that every emitted SHL uses a count in 1..31. The observed CF follows actual
SHL/ADD effects; a fixed incoming/outgoing flag value is not assumed.

`validation/run_constant.py` retains a small reconstructed printed coefficient
baseline, then runs the corrected finite native x86 emitter. The unchanged
original C++/ASM comparison-source baseline and its four-configuration retest
remain separately recorded. This reconstruction is not attributed to an
original MASM macro file that does not exist in the repository.

The corrected native reconstruction passes **54,366 cases across 663 constants**:
all one-bit and two-bit patterns, boundary/signed and random constants, nine
edge inputs plus random inputs, arbitrary scratch/seeds and both incoming CF
states. It verifies the product, exact scratch, every GPR/ESP/CF, exact exterior
code bytes and repeated use. Host initialization/CALL/RET/observation surround
the pure straight line. The data owner is inactive code; the scratch owner is
the actual final ADD immediate whenever emitted. No runtime arithmetic branch
or separate data-array storage is introduced.

[ExportConstant.lean](ExportConstant.lean) independently evaluates the proved
compiler. Its output matches all **11,350 complete pure instruction packets**
and **79,534 complete original-image bytes**, including D1/C1 shift selection,
absolute destination addresses, fixed constants and actual owner positions.
This comparator is execution evidence; the kernel proofs supply the all-input
word-level result. The complete variable-emitter live-byte contract is now
checked below. DEFZERO and other auxiliary Listing 6 operations remain E01;
full physical ISA/configuration/fetch remains E05.

Reproduce after the full Lean audit:

```powershell
python validation/run_lean.py
python validation/run_constant.py
python validation/audit_errata.py
python validation/audit_evidence.py
```


## Live-byte composition

E56-E62 add 99 declarations in seven modules, for 140 constant-emitter proofs.
`ConstantByteCode` adds exact C1/25 encodings with counts 1..31; D1 remains the
one-count form. The decoder deliberately restricts C1 to this selected subset.
`ConstantByteExecution` gives its full DWORD write/value/CF/PC effects and reuses
all other checked forms. `ConstantRefinement` derives actual-count equality,
current operands, complete finite word/register/CF simulation and byte frames.
No x86 write is assigned to a zero-count SHL: the proved compiler omits it.

`ConstantImage` and `ConstantPacking` construct and retain the initialized image,
its real mutable operand owners and protected header/address/count bytes.
`ConstantData.image_trace` derives every subsequent fetch from the actual memory
state and static placement/own-immediate/ownership/capacity facts. Its final
ADD reads the live immediate at its own PC+6; `run_pc` derives the exact endpoint.

`ConstantSimulation.original_image_correct` composes that trace with the all-input
word result, EAX/ESP restoration, only owned DWORD stores, reusable image and
exact ORIGINAL bytes outside the two operand windows. `compiled_agreement` and
`carry` give complete represented field/CF refinement. Arbitrary original
scratch and backing memory are allowed. No future trace, result or intermediate
state is an execution premise.

## Complete emitter geometry and original-image contract

E63-E66 add 44 kernel-checked results in four modules. The thirteen constant
modules now contain **184 audited proofs**. `ConstantShape` proves that the
emitted byte span is independent of data/scratch addresses, and that every
active remaining bit pattern terminates in the unique original ten-byte ADD.
Every preceding instruction has no own-immediate location dependency.
`ConstantRegions` constructs separated packet regions with arbitrary backing
gaps and exact initialization/frame laws.

`ConstantGeometry` computes the actual complete image from the constant:

| Quantity | Computed coordinate or extent |
| --- | --- |
| Pure byte length L | Span of the compiler with normalized operand addresses |
| Data field | start + L + 7, inside the inactive MOV after the host RET gap |
| Scratch, multi-bit constant | start + L - 4, the final ADD immediate at its PC+6 |
| Scratch, zero or single-bit constant | start + L + 17, in the inactive ADD owner |
| Complete image extent | L + 11 for an active ADD, otherwise L + 21 |

It derives complete packet placement/separation, data/scratch ownership and
nonoverlap, the final ADD's own-immediate identity, code capacity and the finite
two-field layout. There is no circular address/length premise. Zero emits a
single store; identity has an empty pure trace. The one-byte host RET gap is
arbitrary backing memory in the theorem and is unchanged by pure execution.

`ConstantCorrect.correct` assumes only original-image initialization, entry PC
and a bound on the complete image extent. It derives actual current-byte fetch
for every emitted instruction, input*constant modulo 2^32, restored EAX/ESP,
only owned code DWORD writes, the reusable whole-image invariant, exact CF
agreement with the literal word run, the endpoint PC and exact original bytes
outside data/scratch. `data_initial` proves the input from the actual emitted
owner bytes. `reusable_correct` supplies the full same execution/effect/frame
contract for arbitrary current data and scratch words using the preserved
Intact invariant and re-entry; initialization is not replayed.

The native comparator now independently exports these computed coordinates
and **every actual complete geometry packet and owner field** from Lean, then
relocates the actual operands to the native base and compares the original
image. It retains all 54,366 native cases, 663 constants, 11,350 pure packets and
79,534 initial-image bytes. This closes the variable constant-emitter layout
bridge. Auxiliary Listing 6 operations, division, remaining literal/half-field
locations, other branch geometry and physical ISA/fetch retain their separate
full-paper scope. The compact M01-M08 errata needs no additional correction.
