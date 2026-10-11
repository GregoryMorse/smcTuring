# Printed split-word exchange/copy frame

Date: 2026-10-05. `SmcTuring/X64/HalfFrame.lean` adds 28 checked positive
results for Listing 5's selected `USEWORD32`/`USEWORDOP64` forms and Listing 2's
unary `OP64(not, ...)`. It observes complete logical DWORD operand fields, the
low accumulator and CF. The full Lean axiom audit includes every result.

A single use executes exactly the printed three effects: exchange the source
word into the accumulator, apply MOV/XOR/AND/OR from the actual accumulator to
the destination word, and exchange the source back. With distinct complete
source and destination fields, `use_effect` derives the exact destination
operation, restores both source and low accumulator, and changes no other word.
MOV preserves CF; XOR/AND/OR clear it. All three operations have a nonempty
write footprint and code-write purity when both fields are instruction operands.
No supplied operation result or future state is an execution premise.

The two-half program consists of two such actual uses. Four logical fields are
pairwise distinct. `split_effect` derives its exact complete memory and register
state; `split_correct` recombines the two destination halves to the correct
64-bit MOV/XOR/AND/OR result using `HalfWords`. Both source halves and every
unrelated word are restored; `split_pure` proves all six writes are code-owned.
The two-operation NOT form separately gives the exact 64-bit complement,
preserves low accumulator and CF, frames all other words and has code-write
purity. This strengthens M04 with the literal selected exchange/copy frame,
beyond the already checked value identities.

`validation/run_half_frame.py` executes native fixtures on both architectures.
Each passes 17,290 boundary/random cases across all five operations and both
incoming CF values. Four DWORD values occupy real DEFDATA32-style immediate
fields at offset six, with ten-byte owner packets. The regression compares
both destination halves, both original source halves, low accumulator, CF and
every original code byte outside the two destination words. It also observes
upper RAX: the printed EAX exchanges clear it in long mode, while the NOT form
preserves the full incoming accumulator. Setup and flags observation are host
code outside the computational pattern; inactive storage owners are not executed.

The x64 native fixture uses the printed two-half patterns. The x86 fixture
executes two instances of each 32-bit primitive to test the same composition;
the printed x86 OP64 macro itself emits only its first half. The single-use
Lean theorem supplies that 32-bit contract directly.

The finite native results and hashes are in `validation/half-frame.json` and
are verified by `audit_evidence.py`. Logical word separation is an explicit
static premise. Literal arbitrary native byte placement, partial overlap,
all CPU flags/registers, arbitrary USEOP behavior and physical current-byte
instruction fetch remain separate obligations. No whole-word ADD/SUB without
carry/borrow propagation is added; M04's precise qualification remains.
