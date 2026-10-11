# Listing 8 scalar owner: existing DEFDATA32 and its live value

M14 replaces one published macro call:

~~~diff
- DEFDATA(0, curtinputval)
+ DEFDATA32(curtinputval, 0)
~~~

Listing 2 already defines DEFDATA32(labelname, data). The Listing 8 relocation
and COMPARE32 consumers both address curtinputval + IMMOFFS, where IMMOFFS is six.
The corrected call therefore explicitly selects the existing DWORD owner and
its declared label/value order. No new primitive or comparison algorithm is
introduced. The original generic DEFDATA call provides neither the intended
label/value order nor the explicit DWORD field layout needed by those consumers.

The owner is C7 /0 with ModR/M 05, four address/displacement bytes and a four-byte
immediate: ten bytes, without REX.W. Its destination is its own immediate at
offset six. In x86 its encoded address is absolute; in x64 the RIP displacement
is minus four, measured from the actual ten-byte instruction end. Its stored
value and both consumer windows are DWORDs in either architecture.

The intended transition-template setup patches the candidate symbol before this owner
executes. The instruction must preserve that live candidate, rather than reset
it to the initial zero. DwordOwner.initial_zero derives the initializer from
its emitted bytes. patch_value and patched_current prove that a four-byte live
operand patch creates the complete packet with the new value and the same
header/address. current_immediate derives the value from the current packet.
correct constructs the actual selected-byte fetch/store, advances PC by ten,
preserves full AX/SP/CF and leaves the entire memory function unchanged.
pure gives the nonempty architectural store wholly inside its code operand.
reusable and output_preserved retain every future encoding and output window.

These are universal selected current-byte proofs in both modes, for arbitrary
backing memory and every DWORD, under the explicit representable PC/field bounds.
The owner adds no AX clobber, including upper RAX, and no reserved-word change
to the surrounding accumulator-preservation contract. Literal Listing 8 must
still derive its initial candidate patch and compose the subsequent comparison,
conditional update, tape/state selection, backedge and finalization.

The native SMC_DEFDATA32 macro emits the existing printed one-instruction form.
Each architecture passes 6,400 executions: forty full-width entry AX values by
forty live DWORD symbols, both CF and two calls on the unchanged live image.
Full AX, all GPRs/SP/status flags, endpoint, current scalar and every byte of
the complete packet are checked. All forty live packet variants and the original
zero packet match the actual Lean exporter, 410 compared bytes per mode.
The complete COFF packet and its single DIR32 or REL32_4 relocation also match.

E146-E147 record seventeen positive declarations and both native fixtures.
The erroneous published call is retained verbatim in the exact excerpt diff.
The original C++/ASM comparison sources and their unchanged before/after
baseline remain authoritative; this ill-typed macro-call excerpt has no literal
native executable baseline. Physical ISA/configuration/fetch and full source
composition remain the ledger's explicit remaining gates.

~~~powershell
python validation/run_lean.py
python validation/run_dword_owner.py
python validation/audit_errata.py
python validation/audit_evidence.py
~~~
