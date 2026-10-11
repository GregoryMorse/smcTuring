# Palomar submission audit

Audit date: 2026-10-11. **NOT READY — REPAIRABLE.** The mathematical proof
is complete. The selected statement interface now passes protected Comparator,
NanoDa and Lean's independent kernel replay. Public-commit acceptance remains
pending. This verdict is about submission readiness.
No submission or registration performed.

The integrated passing agent checkpoint is
`08f0a594f691cb0f131a72c81dbcbd79b5667a20`. It is an immutable server checkpoint,
not the public submission commit. The current public repository is
[GregoryMorse/smcTuring](https://github.com/GregoryMorse/smcTuring); the final
public proof commit remains unresolved.

## Policy and audit inputs

The user-supplied [auditor ZIP](https://grm.web.elte.hu/supervision/palomar-submission-auditor.zip)
has SHA-256 `2e9b00186f0491583100966d7d05b98030058f011a02f0ec3357b113b1706bae`.
Its SKILL.md, four references and static preflight script were inspected before
use. Official policy, form and agent instructions were refreshed on 2026-10-11;
exact downloaded bytes and retrieval timestamps are in
`validation/palomar/policy/refresh.json` and `assets.json`.

- PalomarPolicy: `96b034cc31a72a63d4f4041911dce337a85c9a04`.
- PalomarSubmission: `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
- PalomarTemplate: `2891de4c48955af824969a263d31b25e7a9a1406`.
- Upstream metadata schema: `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.

The binding metadata rules allow one to eight arXiv codes and zero to eight
MSC codes; the overview recommends narrower lists. This package uses one
arXiv code and two relevant MSC codes. Canonical source relationships avoid
the policy's compatibility ambiguity over unfamiliar relationship wording.
The checked minimum is Lean v4.35.0-rc2; this project retains v4.35.0-rc3
and the matching pinned Mathlib revision.

## Findings and required evidence

| ID | Gate | Status | Evidence | Finding / required action |
| --- | --- | --- | --- | --- |
| P01 | Mathematical proof | PASS | Cold report SHA `7a69e7c85d5a054e265078ee0bee4908a431358903772f2c7a13c2dfdeac610d` | 1,151 production modules freshly compiled; zero reuse; 7,975 registered declarations; only standard axioms. |
| P02 | Exact corrections | PASS | `validation/audit_errata.py`, current checkpoint errata check | M01-M20; 60 exact source excerpts and 128 positive proof references; two-page minimal errata preserved. |
| P03 | Submission interface | PASS | Protected `lake comparator --config comparator.json`, exit 0 | Independent Challenge is 984 lines / 60,700 bytes; four theorem and four definition names. Only allowed Mathlib imports. Native/COFF results are supporting material by the user's scope decision. Preferred-size excess is a warning. |
| P04 | Public immutable snapshot | FAIL | Clean isolated source commit and static preflight | The reviewed source snapshot is committed locally and clean; it must still be published and anonymously fetchable from public GitHub. |
| P05 | Source module/size rules | PASS | `ACCEPTANCE_EVIDENCE.json` | 1,177 production/interface/exporter source files use `module`; largest has 9,672 lines. Ignored experiments/history must stay out of the submitted snapshot. |
| P06 | Dependency/compiler pins | PASS | Pinned toolchain, manifest and cold audit | Lean commit `470d5ce1400764999581fd26d5d72b00d990b0f4`; Mathlib `302343bb9a029d4edab4f736703f0736896c1b64`. Official verifier must independently confirm them. |
| P07 | Metadata schema/taxonomies | PASS | `validation/palomar/metadata-validation.json` | v0.4 schema passes; cs.LO, 03D10 and 68N30 are in the pinned registry taxonomies. |
| P08 | License detection | PASS | `LICENSE_AUDIT.md`; GitHub license API | GitHub independently detects CC0-1.0 from the unchanged root license blob; local text and metadata match. Final Palomar workflow also checks its own detector. Cited publisher references retain their source terms. |
| P09 | Proof-to-statement / independent kernel | PASS | Comparator log SHA `98a500a79fcee09149537c9bab421b14d8cd93be56be6e82ddf522d1703882b6` | Protected Comparator, NanoDa and Lean kernel all accept the selected declarations; exit 0 in 34.599 seconds. Final public-commit official workflow remains P10. |
| P10 | Official full preflight | UNVERIFIED | Prepared pipeline pin | Run reusable submission workflow with `mode: full`, matching `uses`/`pipeline_commit` pin, `execution_profile: palomar-standard-v1`; require actual mechanical `status: pass`. |
| P11 | Native release CI | UNVERIFIED | `.github/workflows/proof-native.yml` | Offline package passes; actual same-commit Linux and Windows baseline/corrected MASM/COFF checks remain. |
| P12 | Scope and semantic fidelity | PASS | `PALOMAR_SEMANTICS.md`, `FINAL_THEOREM_MAP.md`, `PHYSICAL_BINDING_CONTRACT.md`, exact errata | All eight selected declarations have individual semantic accounts; ideal-machine and conditional physical statements retain their explicit hypotheses and model boundaries. |
| P13 | Provenance/research audience | PASS | Published source and contextual literature below | Known source-based result, credible computability and code-verification audience. No new mathematical novelty or priority claimed. |
| P14 | Submission authorization | UNVERIFIED | User directs own paper/formalization | Proposed relationship is responsible maintainer; obtain explicit attestation to the exact intake payload before submitting. Preparation is authorized. |

## Existing theorem families and source fidelity

The Comparator manifest selects the principal mathematical result and its
four result definitions, plus three encoding/ownership theorems. The following
table also records checked native supporting families. Selection is preparation
for registration; no declaration has yet been registered.

| Family | Quantifiers and meaning | Source and qualifications |
| --- | --- | --- |
| `CorrectedPaper.Unbounded` | Every finite source machine/input has corresponding halt/divergence outcomes and each computational instruction writes code; a concrete walker witnesses unbounded distinct fetched-field changes. | Morse §§II-V and M01-M02. Integer-address/value machine; no finite x86 address-space unboundedness. Infinite repetition and unbounded distinct fields are separate conclusions. |
| `CorrectedPaper.FourMov` | One fixed four-register MOV program simulates each finite machine/input, preserving halt/divergence. | Stephen Dolan (2013), §§2-6. Three addressing forms, static body and unconditional backedge; invalid-zero mathematical model. |
| `CorrectedPaper.EffectiveInterpreter` | A finite numbered interpreter receives the finite encoded machine/input; terminal output has a positive journal/tape representation. | Effective elaboration of the published simulation using pinned Mathlib TM0. Interpreter alphabet/labels have inhabited finite encodings; these witnesses are constructed. |
| `CorrectedPaper.Observations` | At each actual finite source run boundary, one corresponding pure trace represents the logical head and every integer tape position. | Morse's TM simulation and corrected observation semantics. Prefix witnesses are conclusions, not future-state hypotheses. |
| `Listing9JointFullExecution.complete_input` | A finite halting source execution produces the full printed interpreter trace and prefix purity/owner/access certificates. | Listings 8/9 with M03-M20. Alphabet/word capacity and signed x64 relative reach are explicit. `TM.Machine` includes a blank symbol and start state, so an inhabited machine has positive alphabet/state counts; zero-count quantified cases have no machine. Empty inputs and immediate halting remain genuine cases. |
| `Listing9SameTraceBinding.complete_input` | Same actual trace has native fetch/read/store/output and structural pre-cleanup head observation. | Head is observed before cleanup; full seed AX restoration is at epilogue, with exact final x64 M20 effect afterward. |
| `Listing9PhysicalBinding.full_paper` | Present normalized object/entry agreement and local ISA effects derive physical execution and every prefix projection. | Conditional physical refinement; coherent fetch, flat segments, CET off, stable mapping, ABI and endpoint conditions. No whole CPU/OS or physical RET/stop theorem. |

## Provenance and research interest

The source is Gregory Morse's
[IJET article](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359),
published 27 April 2018. This package records an adaptation with exact proved
errata, not a newly discovered theorem. Palomar's
[submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/96b034cc31a72a63d4f4041911dce337a85c9a04/CONTRIBUTING.md)
expressly accommodates source-based formalizations; age alone is no disqualifier.

The intended audience includes computability researchers studying restricted
instruction systems and researchers verifying mutable machine code. The latter
is an established research subject: Cai, Shao and Vaynberg's
[PLDI work and Coq implementation](https://flint.cs.yale.edu/shao/papers/smc.html)
certify general self-modifying code, while Anckaert, Madou and De Bosschere's
[model](https://biblio.ugent.be/publication/750330) studies its analysis and
obfuscation. These are contextual neighbors, not proofs of the specific
instruction-level pure-SMC universality theorem formalized here.

This preparation did not establish priority or exhaustively search all prior
formalizations. The metadata identifies the pinned Mathlib dependency and the
source papers. Codex made substantial proof and tooling contributions under
Gregory Morse's direction. Mechanical checking and agent review do not imply
independent human review, journal acceptance or Palomar endorsement.

## Exact form values currently resolvable

| Field | Exact value | Evidence | Visibility / validation |
| --- | --- | --- | --- |
| Repository | `GregoryMorse/smcTuring` | Public repository and local origin | Public; fetchable source repository |
| Commit | **UNRESOLVED final public commit** | Integrated checkpoint is not public proof commit | Public; blocks READY |
| Comparator configuration | `lean/comparator.json` | Source-bound accepted four-theorem/four-definition interface | Public; local protected comparison passes |
| Project directory | `lean` | Existing pinned Lake project | Public |
| Formalization metadata | `lean/formalization.yaml` | Schema/taxonomy-validated metadata | Public |
| Existing Palomar ID | **UNRESOLVED** | Official identity and repository documents both returned HTTP403; `validation/palomar/registration-identity.json` retains the checks | Public if new version; 403 does not prove no existing ID |
| Relationship | Proposed `maintainer` | User-created/directed substantive formalization | Public; exact intake attestation pending |
| Approval evidence | Blank | No separate documentary approval required for maintainer route | Public if supplied |
| Notes | Source-based formalization of Morse (2018), with exact minimal proved errata and explicit ideal/bounded-model distinction. | Metadata and theorem map | Private submission context; no secrets |
| Preliminary override | Disabled / not used | Agent protocol | No bypass of authoritative verification |

## Remaining actions in dependency order

1. The independent Challenge/Solution/Comparator interface is checked; preserve its exact accepted inputs.
2. The clean isolated source package contains metadata and both pinned CI workflows; its exact commit and archive hash are in the local publication packet.
3. Publish the reviewed exact commit, run proof/native CI and official full
   Palomar mechanical preflight, and retain actual reports/artifact hashes.
4. Bind the completed declaration-by-declaration semantic table and all findings
   to that public commit; close only external gates that have actually passed.
5. Preserve a compact final evidence archive, then prune redundant local remote
   checkpoint copies. Do not discard the only evidence while acceptance is open.
6. If the user requests intake, show the exact payload and request the required
   authorization; registration requires a later separate decision.

Palomar readiness: NOT READY — REPAIRABLE  
Exact commit: UNRESOLVED final public commit  
Blocking findings: 1 unpublished-snapshot gate  
Unverified mandatory checks: 4 (full preflight, native CI, intake authorization and existing-ID routing)  
Submission performed: no  
Registration performed: no  
Next action: authorize publication of the reviewed candidate and the two exact-commit workflows.


## Accepted coordinator recovery

Kernel diagnostics record a memory-cgroup OOM at 2026-10-11 02:12:42 UTC
(04:12:42 Europe/Budapest), killing NanoDa and stopping the interactive agent.
The original attempted comparison was incomplete. Its sources and failure logs
were retrieved before repair; the latest published agent checkpoint stayed 08f0a59.
The principal Solution now uses the already proved mathematical components
directly, rather than projecting through the native umbrella. The statement
and all production theorem bodies are unchanged. Protected comparison and both
kernels pass in 34.599 seconds, with that recovery service peaking at
1,345,884,160 bytes. The source audit compiles only the new Solution and verifies
reuse of all 1,151 existing modules; it checks 7,976 declarations under standard
axioms. Its report SHA is
`39a231a4fceeeb55c5334261b434fe73aa01aad96e77f0ddc51cbf67e728e262`.
Errata and offline CI-package gates pass. No new correction was introduced.
See PALOMAR_SEMANTICS.md and ACCEPTANCE_EVIDENCE.json. These are local/remote
preparation results, not an official public-commit preflight or registration.
