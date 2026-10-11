# Printed terminal marker: positive correction contract

M12 replaces only Listing 2's `mov [$], 0` with
`mov SZW32 ptr [$+IMMOFFS], 0`, using Table II's DWORD type and immediate
offset six. Its additional sentence places termination observation immediately
after this marker; host stopping and output handling are outside the pure trace.
The computation and branch algorithms are unchanged.

The corrected C7/05 packet is ten bytes in both modes. x86 uses its absolute
four-byte operand address; x64 uses a four-byte RIP displacement of -4, with no
REX.W. Exactly the four zero immediate bytes are written back. An architectural
write counts even when it stores the present value. AX, SP and CF are unchanged,
the PC advances by ten, and the entire current memory function is preserved.
Consequently every already produced output window is unchanged and the live
marker encoding can be entered again without an initializer.

`Native.TerminalMarker.correct` starts from the actual current packet at the
entry PC and a complete nonwrapping extent bound; it proves the fetch/store and
final state. `pure` gives the nonempty code-owned footprint; `reusable` and
`output_preserved` give the maintained encoding and arbitrary output frame.
`current_image` derives the current-packet premise from an original emitted
image. No prior zero-field initializer is an extra assumption: the fetched
corrected MOV itself contains that immediate.

The proof checks both selected sequential nonfaulting x86/x64 byte models.
Physical permissions, canonical addresses, other CPU state, SMC fetch discipline
and unexpected-fault refinement retain E05/A01. MOV advances normally; the
observation boundary is the terminal outcome. E139-E143 now prove the printed full-width Listing 9 save sequence and its
body/terminal composition. Literal Listing 8 must still discharge the body's
reserved-field and current-marker contract; optimized field placement remains
S01/P07/A02. See [the accumulator contract](APPENDIX_ACCUMULATOR.md).

E136-E138 audit 27 positive declarations. The native fixtures each pass 4,128
typed-original and 4,128 corrected executions, covering both entry carry values,
boundary/random full-width accumulator words and repeated entry. They capture
all GPRs, SP and status flags, check the exact endpoint and every adjacent code
byte. Corrected reentry uses the unchanged live bytes without host reset. The
typed original baseline uses explicit DWORD width and is host-restored after
each self-header write; its normal fall-through is recorded without making a
claim that MOV stops the CPU.

The comparator checks every byte of both loaded packets against the actual
Lean exporter and every byte of both object packets against resolved COFF
symbols/addends: x86 DIR32 and x64 REL32_4 (the latter accounts for the four
trailing immediate bytes). Host setup, captures, restoration, cache flushes and
return instructions lie outside the ten-byte pure marker.

Reproduce after a fresh full Lean audit:

```powershell
python validation/run_terminal.py
python validation/audit_errata.py --write-diff
python validation/audit_evidence.py
```
