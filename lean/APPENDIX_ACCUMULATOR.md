# Listing 9 accumulator preservation and terminal composition

The four printed executable instructions are retained unchanged: one prologue
MOV, then XCHG/MOV/XCHG in the epilogue. Each save label denotes a complete
full-width code operand, and the pointer slot initially contains the address
of the accumulator-save slot. Data declarations are storage owners outside
the prologue and epilogue execution intervals. No new paper erratum is inferred
from this local sequence.

Let A be the entry accumulator, S the save-field address and P the pointer-field
address. The prologue stores A at S. At body exit, the reserved fields contain
M(S)=A and M(P)=S; the body may have changed AX and arbitrary other output memory.
The first exit exchange loads S and temporarily stores the body accumulator at
P. The following MOV restores P=S and the entire previous memory function. The
last exchange loads A and writes S into S. Thus the final accumulator is A and
the final memory is exactly M with S reset to its own address. SP and CF retain
the body's exit values. Every other output byte is preserved. On the next
entry the prologue stores the new accumulator, so the canonical reset is reusable.

`AccumulatorLayout` derives all current absolute/RIP targets, complete instruction
lengths and actual PC advances under word-capacity, field separation and rel32
range conditions. `AccumulatorEffects` proves the complete byte-memory effects.
`AccumulatorImage` derives the current-byte fetches after preceding writes,
code-owned purity and preserved fixed/owned packet headers; `owner_value` derives
the pointer initializer from actual emitted bytes rather than an assumed load.
`original_prologue` checks entry decoding, saved AX, initialized pointer and the
maintained image from an original byte initializer.

`AccumulatorFinalization.surround` composes an actual body trace with the printed
entry/exit sequence and corrected DOHALT. Its caller supplies the body's two
reserved-field invariants, code-owned writes, exit PC and current marker packet.
All subsequent epilogue and terminal fetches are derived. The final observation
PC is the byte immediately after the marker, AX is the entry value, SP/CF are the
body's exit values, and the exact memory change is the save-slot reset.
`surrounding_pure` covers every native instruction in this complete trace;
`TerminalMarker.pure` gives the final DWORD marker's nonempty code-owned footprint.
`output_frame` preserves any complete output window disjoint from the save slot,
and `live_reuse` preserves the helper/owner headers and live terminal encoding.

The body contract is explicit. A complete literal Listing 8 proof must still
establish it for that interpreter; the theorem does not assume that an arbitrary
body preserves reserved fields. Native field-label optimizations and x64 half-field
placement are also separate from this full-width field contract. Physical CPU,
permissions, other architectural state and SMC fetch refinement retain E05/A01.

The native fixtures use the same four-instruction order, a three-instruction
pure body that writes an independently chosen full-word output, and corrected
DOHALT. Full-width MOFFS operand owners provide the reserved/body/output storage;
this is an explicit storage realization, without silently treating an optimized
DEFDATA32 instruction-header label as an operand address. Each architecture tests
six orders of the save/pointer/body owners, with the output owner last.

Each x86/x64 run passes 38,400 executions: all pairs of forty boundary/random
entry and body words, both CF values, two consecutive calls and six layouts.
The checks cover full AX (including upper RAX bits), every GPR/SP/status flag,
body result and output preservation, actual endpoint, save/pointer reset and
every code byte outside the final save/output words. The second call uses the
live image without resetting the reserved fields or marker.

All 72 packets per architecture (48 executed control/terminal packets and
24 owned-storage packets) match the actual Lean exporter as loaded bytes and
as COFF bytes with resolved symbol/addends. The comparison covers 408 x86 or
594 x64 bytes and 54 relocations, including DIR32, RIP REL32, terminal REL32_4
and the full-width pointer initializer's x64 ADDR64. Complete owner widths,
packet separation and all nine static layout/range conditions are checked.

E139-E143 audit 49 positive declarations. Reproduce after a fresh Lean audit:

```powershell
python validation/run_accumulator.py
python validation/audit_errata.py
python validation/audit_evidence.py
```
