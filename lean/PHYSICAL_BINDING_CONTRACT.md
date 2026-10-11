# Physical and normalized COFF binding contract

The final theorem is `SmcTuring.Appendix.Listing9PhysicalBinding.full_paper`;its bounded entry is `.complete_input`. The public inputs contain actual source-TM execution,quantitative byte/RIP bounds,original memory/seed and PRESENT `Conditions`. Every later native/physical state,trace,head boundary,packet validity and prefix catalog is positively derived.

## Present artifact and entry

`Conditions.object` is the finite normalized loaded image over the exact declared interval. `Present.loadedBytes` compares the initial physical projection to that object;`normalizedObject` compares it to the Lean emitted snapshot. Entry PC/AX/SP/CF/SI/DI/DF and exterior backing equality are explicit present comparisons. These are initial artifact/setup conditions;no whole interpreter execution or future readiness is assumed. Actual assembler/object agreement is a separate source-bound validation gate,not a theorem about arbitrary compiler output.

COFF normalization uses loaded symbol addresses plus signed addends. Absolute32/64 require representability;relative32 requires signed delta range and uses field end plus remaining instruction suffix. REL32_1 uses suffix1. `site_target` and `normalize_targets` prove exact resolved targets after all nonoverlapping fields;`normalize_frame` proves every disjoint header/opcode/data byte window is unchanged. The final object comparison includes nonrelocation bytes,metadata and exact placement.

## Genuine physical assumptions

The abstract physical CPU projects PC/AX/SP/CF/memory/SI/DI/DF. `ISA` explicitly states flat segments,CET disabled,coherent current-byte fetch,stable mapping,compatible ABI and selected local instruction effects. Its effect clause concerns ONE CURRENT fetched instruction with derived canonical fetch/read/write windows and a canonical successor;it contains no source simulation,whole run,halting assumption or future native image. It is a disclosed physical ISA contract,not an entire CPU/OS verification.

The mapping covers every actual classifier request,data read and full architectural store. The final canonical endpoint is a static numeric condition. Initial DF agrees with the constructed entry;there is no arbitrary incoming DF-restoration claim. Host/native tests must retain the existing wrapper and register/flag scopes. Registers/flags outside the projection and asynchronous interference are governed by the disclosed compatible/isolated ISA and host ABI conditions,not silently added model effects.

## Observation and stopping scope

Read the logical head at the proved structural PRE-CLEANUP physical prefix. The cleanup cursor is not the head. Complete tape output is read at the proved final physical prefix using only original geometry/blank. Full seed AX is restored at the separately proved physical epilogue boundary;x64 RAX after trailing declarations has the precise M20 self-address effect.

The theorem proves a finite execution prefix ending at the declared endpoint. It does not infer a physical RET,processor halt or OS stop. A host/supervisor must observe/stop at the stipulated boundary or use the separately validated wrapper outside the pure construction. Genuine observation/stop and unrepresented ABI behavior remain disclosed external realization conditions.

## Final source-bound acceptance

Rounds6-7 must provide ONE cold Linux complete proof/axiom replay,portable pinned CI,and actual Windows MASM/x86/x64 original-baseline and minimally corrected native/assembler results. Record exact source/toolchain/fixture/object/loaded-byte hashes,relocation kinds/positions/targets,compared expected Lean bytes,register/frame/output outcomes and failure logs. Concrete compiled objects and physical configuration must satisfy the present comparison/configuration scopes above. Historical optional Windows Lean checks retain their narrow scopes;they are neither fresh aggregate evidence nor a full Windows proof requirement. No GitHub run/public push is authorized or claimed before it actually occurs.
