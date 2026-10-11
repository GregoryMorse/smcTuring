# CI_READY_AWAITING_RUN

The selected principal Palomar statement now passes protected Comparator,
NanoDa and Lean's kernel. The current source-bound audit checks 1,152 modules
and 7,976 declarations, compiling only Solution and verifying reuse of the
1,151 unchanged core modules. The agent's OOM-terminated attempt is preserved;
the coordinator recovered and accepted the interface without claiming a new
agent checkpoint. Both pinned workflows are present. See
`lean/ACCEPTANCE_EVIDENCE.json` and `lean/CLOSURE_STATUS.md`.
Actual public-commit CI and official Palomar full preflight remain pending.

Mathematical/conditional SAME-trace native/head/COFF proof is complete. Rounds1–5 are accepted. Round6 ACCEPTED actual checkpointf828f86c78da2fab712b47ac84a23db15a9b2415;all2620 inventory/bundle hashes verified. Release/CI and overall completion remain false.

## Exact prepared evidence

- Lean4.35.0-rc3 commit470d5ce1400764999581fd26d5d72b00d990b0f4;Mathlib302343bb9a029d4edab4f736703f0736896c1b64.
- ONE cold replay:1151 freshly compiled modules,zero reuse,7975 audited declarations;only standard axioms.1196 proof/helper inputs;1298 package inputs unchanged since pre-audit freeze;22863 project/dependency companion hashes checked. Peak6594846720 bytes under unchanged parent cap.
- Report SHA256:7a69e7c85d5a054e265078ee0bee4908a431358903772f2c7a13c2dfdeac610d.
- Errata:60 exact excerpts,128 current positive references,two unchanged reviewed pages.
- Portable pinned package:syntax/YAML/action/compiler/reference pins;23 Windows exporter roots/210-module closure;185 checked native proof groups;server Linux entrypoint and fail-closed bridge pass. No Windows/GitHub run is claimed.

## Coordinator action

1. Fetch the actual immutable turn-end bundle;verify its manifest,source inventory,audit report and cold artifact evidence. No timer/manual snapshot replaces publication.
2. Restore the supplementary workflow from `validation/ci-results/portable-source-package.json`. The unchanged collector includes source/JSON/text artifacts but omits `.github/*.yml`;the package carries its exact base64 bytes and SHA256. Verify every1298 source hash before committing.
3. Review the prepared sources,commit/push to the intended repository and run **Pinned proof and native acceptance**. The remote agent has not pushed and has no authorization to do so.
4. Require both `linux-proof` and `windows-native` to pass at the SAME source commit/run. Collect the actual URL,commit/check outcomes,source/compiler/tool/fixture/object/executable/loaded-byte/failure/artifact manifests. Windows compile objects are produced on Windows;Linux proof objects are not substituted.
5. Verify Debug/Release×Win32/x64 untouched baseline outcomes and all corrected native suites. Require exact normalized object/loaded image agreement with Lean bytes:nonrelocation opcode/header/data/metadata/placement bytes;relocation kinds,widths,positions,loaded symbol targets and signed addends (including REL32_1);entry PC/AX/SP/CF/SI/DI/DF and exterior backing;register/frame/output/head/full-AX-restoration boundary observations within their stated scopes. Check physical flat-segment/CET/coherent-fetch/stable-mapping/ABI/observation conditions from `lean/PHYSICAL_BINDING_CONTRACT.md`. Full seeded AX restoration is at the proved epilogue boundary;after trailing x64 declarations RAX may hold the self-save address. No physical RET/OS stop inference.
6. Return the exact acceptance artifacts so round7/final HANDOFF can close. Failed or skipped checks remain open. Full Windows Lean/sub2GB/resource-only refactors are optional and do not replace native acceptance.

Restore command,run in the extracted project before Git review:

```python
import base64,hashlib,json
from pathlib import Path
p=json.loads(Path('validation/ci-results/portable-source-package.json').read_text())
for name,item in p['supplementary_files'].items():
    relative=Path(name)
    assert not relative.is_absolute() and '..' not in relative.parts
    data=base64.b64decode(item['base64'])
    assert hashlib.sha256(data).hexdigest()==item['sha256']
    relative.parent.mkdir(parents=True,exist_ok=True)
    relative.write_bytes(data)
for name,expected in p['sources'].items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest()==expected,name
```

Package details: `validation/ci/README.md`. Authoritative gates: `validation/remote-agent/HANDOFF.md`. The seven-round plan stays unchanged;only external verification/acceptance remains after actual round6 publication.
