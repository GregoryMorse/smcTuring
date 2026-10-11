# Minimal proved paper errata — complete

The publishable errata for Gregory Morse's IJET 2018 paper consists of
**M01–M20**, with 60 exact published excerpts and 128 positive proof references.
The algorithm is preserved through local replacements, insertions and explicit
model/observation clarifications.

- [Two-page reviewed PDF](../../output/pdf/morse-2018-errata.pdf)
- [LaTeX source](morse-2018-errata.tex)
- [Exact minimal diff](morse-2018-minimal.diff)
- [Edit and positive-proof manifest](edits.json)
- [Errata policy](POLICY.md) and [explanatory record](../ERRATA.md)

M01 replaces DEFADDR's register-only load with an exchange and proves the same
boundary effect, including exact self-aliasing, with strict instruction-level
code writes. M02 specifies the ideal unbounded address/value model and its
separate finite x86/x64 realizations. The remaining local corrections cover
native widths, operand/layout/control details and exact observation/restoration
boundaries; their source excerpts and positive justifications are in the manifest.

The complete corrected-paper formalization and conditional native/COFF bindings
are closed. The full public cold audit checks 1,152 modules / 7,976 declarations;
21 native suites and the official Palomar full mechanical preflight pass.
See [final acceptance](../FINAL_ACCEPTANCE.json), [theorem map](../FINAL_THEOREM_MAP.md)
and [physical contract](../PHYSICAL_BINDING_CONTRACT.md). Fetch coherence and
other genuine physical conditions remain explicit hypotheses of the native
refinement. No whole CPU/OS or physical RET/stop theorem is claimed.

The earlier dated proof/PDF binding records are preserved in
[history](../history/ERRATA_README.before-public-closure-20261011.md).
The exact TeX, diff, edit manifest and PDF are unchanged by closure documentation.
The errata has not been submitted to the journal.
