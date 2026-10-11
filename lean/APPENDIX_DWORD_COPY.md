# Universal DWORD exchange/store helper in x86 and x64

E148-E153 close the universal long-mode gap of M13. The existing three
instructions are retained. No new paper erratum is introduced.

| Operation | x86 bytes / address | x64 bytes / address |
| --- | --- | --- |
| XCHG EAX with source DWORD | 87/05, six bytes, absolute disp32 | 87/05, six bytes, RIP-relative disp32 |
| MOV EAX to target DWORD | A3, five bytes, absolute address32 | 89/05, six bytes, RIP-relative disp32 |
| XCHG EAX with source DWORD | 87/05, six bytes, absolute disp32 | 87/05, six bytes, RIP-relative disp32 |

There is no REX.W. All three stores write exactly four bytes. The complete
helper spans 17 x86 or 18 x64 bytes. The DWORD codec also checks the valid bare
A3 form with the mode's address width; this helper uses the listed forms.

Let s and d be complete disjoint DWORD fields, S their initial source value,
and A the entry accumulator. The first exchange stores low32(A) at s and loads
S into EAX. The middle store writes S at d. The final exchange restores s and
loads low32(A). Final memory is exactly putDWORD(M,d,S); SP and CF are unchanged.
Final EAX is the entry EAX; final long-mode RAX is its zero extension. This is
the actual effect for every entry accumulator, including nonzero upper RAX.

DwordCode proves exact encoding/decoding, opcode-derived current fetch,
strict packet lengths, natural-address DWORD loads and stores, low-register
projection/zero extension, exact byte frames and a nonempty store. Natural
addresses remain whole in long mode; DWORD data width does not truncate a
memory address above 4GiB.

DwordLayout derives the three actual PCs and absolute/RIP targets under nine
static premises: code, source and target capacities; complete source/target
separation; source and target outside the helper; and three long-mode signed
RIP ranges. Checks_valid proves equivalence between the executable nine Boolean
checks and this contract. RIP displacements use the actual six-byte ends.

DwordEffects proves the complete three-store restoration and final state for
arbitrary byte memory. DwordImage constructs a finite original control image,
derives every later fetch after preceding stores and preserves that image for
reuse. Its image carriers reuse the existing bare byte encodings, with proved
byte equality; execution uses DwordCode's actual x86 or x64 state and semantics.
Both above-4GiB addresses and four-byte write extents are retained.

InputDword.copy_correct obtains the live symbol from the complete current
COMPARE SUB packet at source-PC+6, then derives the complete seven-byte XOR
target packet with that symbol at target-PC+3. copy_pure follows all three
actual state-dependent code-field writes. source_code_frame preserves the
entire source instruction for disjoint source/target prototype packets.
The generic destination-only effect gives every exterior-byte frame.

The native fixture uses the original helper order and unchanged printed
operand forms. Each architecture passes 6,400 corrected and 6,400 typed-original
cases over forty entry words, forty DWORD symbols, both CF and two calls on
the live image. Full GPR/SP/status flags, expected RAX zero extension, source,
target, endpoint and exterior bytes are checked. All twelve loaded/object
packets, 88 x86 or 90 x64 bytes and ten relocations per mode match the actual
model encoder. All nine static checks pass; actual x64 PCs and source/target
addresses are above 4GiB.

There are 77 new positive declarations: 22 codec/load/store/register facts,
16 layout/check facts, 16 whole-memory effects, 19 initialized/live-image
facts, and four corrected input-copy facts. The prior fifteen local M13
proofs remain checked. The two-page errata now cites the stronger both-mode
InputDword.copy_correct; its 37 exact source excerpts are unchanged.

Full literal Listing 8 comparison/input update, node/state initialization,
backedge/finalization and remaining optimized field placement still require
composition. Physical ISA/configuration/fetch and registry review retain
their recorded gates.

~~~powershell
python validation/run_lean.py
python validation/run_input_operand.py
python validation/audit_errata.py
python validation/audit_evidence.py
~~~
