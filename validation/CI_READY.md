# CI acceptance — complete

The public proof commit `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4` is validated.

- [Complete cold Linux proof audit](https://github.com/GregoryMorse/smcTuring/actions/runs/38108181056): 1,152 freshly compiled modules,
  zero reuse, 7,976 declarations, only standard axioms. The original workflow
  then failed on an errata packaging import; that later failure is retained.
- [Completed exact-source acceptance](https://github.com/GregoryMorse/smcTuring/actions/runs/38118165923): original proof report/source hashes
  verified without rebuilding finished theorems; Linux errata packaging passes;
  hash-verified Windows 210-module exporter closure from the prior fresh build,
  21 native suites, four baseline
  configurations and 30 simulator checks pass.
- [Official full Palomar mechanical preflight](https://github.com/GregoryMorse/smcTuring/actions/runs/38108849833): pass, selected mathematical
  statements verified by independent kernels, license detected as CC0-1.0.

[Final acceptance](../lean/FINAL_ACCEPTANCE.json) records report digests and the
explicit frozen-config/runtime recovery. Current master repairs the clean-build
packaging helper and alternate-cache library registrations. No Linux objects
were loaded as Windows objects. Windows native tests retain the 1.5 GB guard;
fresh exporter compilation on GitHub uses the pinned compiler with a 6 GB heap.
A complete Windows Lean audit is not claimed.

The source remains subject to [the physical contract](../lean/PHYSICAL_BINDING_CONTRACT.md).
The full mathematical objective is closed; Palomar intake/editorial registration
is the user's next action.
