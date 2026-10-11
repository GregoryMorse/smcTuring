# Listing 8 input-symbol operand correction

M13 changes one source operand in the published USEWORD32 call:

~~~diff
- USEWORD32((mov [inputupdate + REGIMMOFFS], acmltr32) , curinputval)
+ USEWORD32((mov [inputupdate + REGIMMOFFS], acmltr32) , curinputval + IMMOFFS)
~~~

The label curinputval names COMPARE32's first instruction. Its forced DWORD
SUB packet is ten bytes, with the live symbol in the four immediate bytes at
offset six. USEWORD32 reads its supplied address directly; the printed input
direction call already supplies its own + IMMOFFS. The target inputupdate
DWORD XOR packet is seven bytes, with its immediate at REGIMMOFFS = three.
No instruction or algorithm changes. No REX.W is used for these DWORD forms.

Appendix.InputOperand.copy_correct derives the source symbol from the actual
current ten bytes, composes the original exchange/store/exchange helper and
derives all seven target bytes containing that symbol. It proves the complete
selected-x86 live trace, EAX/SP/CF and exact destination-only byte change.
copy_pure accounts for all three code-field writes, including restored and
unchanged values. copy_frame and source_code_frame preserve every exterior
byte and the complete disjoint source packet. The header/address/immediate
windows and their lengths are checked rather than inferred from an opcode
alone. word_effect and word_symbol give the logical DWORD operation used
by the published USEWORD32 contract in either architecture.

The native fixtures preserve the original helper order and compare the
typed printed source operand with the corrected operand. Each architecture
passes 6,400 corrected and 6,400 typed-original executions: forty full-width
entry words by forty live DWORD symbols, both CF values and two consecutive
calls. The corrected target is the live symbol; the source instruction is
restored. All GPRs/SP/status flags, endpoint and every exterior byte are
checked. Long-mode DWORD exchanges have the expected low-AX zero extension.

All twelve loaded and COFF packets per architecture match the actual Lean
exporter: 88 x86 or 90 x64 bytes and ten address relocations, including the
long-mode REL32_4 displacement preceding an immediate. Both full source and
target packets are checked. The pure helper's source/destination fields and
the unexecuted prototype packets are separate and nonoverlapping.

E144-E145 cover fifteen positive declarations and the native fixtures.
The universal current-byte helper proof is for the selected x86 model; the
both-mode logical DWORD contract and native x64 evidence do not yet supply
a universal long-mode DWORD byte-execution theorem. Full literal Listing 8,
its storage/node initialization, optimized field placement and physical CPU
fetch/configuration remain explicit completion work.

~~~powershell
python validation/run_lean.py
python validation/run_input_operand.py
python validation/audit_errata.py
python validation/audit_evidence.py
~~~

## Both-mode execution checkpoint

E148-E153 now close the universal x64 DWORD byte-execution gap.
InputDword.copy_correct derives the actual three-instruction current-byte trace,
live target packet, correct long-mode RAX zero extension and source/code/exterior
frames. The nine static checks are proved equivalent to its admissibility
contract and pass for the actual native layouts, including x64 addresses above
4GiB. The existing M13 change is retained. The earlier x86-only description
records the prior checkpoint; see [the complete DWORD helper
contract](APPENDIX_DWORD_COPY.md) for the current both-mode result.
