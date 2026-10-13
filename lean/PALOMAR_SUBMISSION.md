# Palomar registration and submitted packet

Registered on 2026-10-13 as
[PALOMAR-2026-10-13-000008, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-13-000008&version=1).
The [registration receipt](acceptance/palomar-registration.json) confirms the
registered source is the exact tested commit below. These form values document
the completed intake; any future version should use the registered Palomar ID.

The explicit-initialization and reached-output revision is complete. All
selected definitions, positive proofs and descriptions agree under the
scoped [definition-level audit](SEMANTIC_ALIGNMENT.md). The
[acceptance receipt](acceptance/execution-revision.json) binds all checks to
the exact public commit below. Earlier candidates are historical.

| Form field | Value |
| --- | --- |
| Repository | `GregoryMorse/smcTuring` |
| Commit | `51198ac6ad1d1b4b2ad6e3751583e3c6d1c56b71` |
| Project directory | `lean` |
| Comparator configuration | `lean/comparator.json` |
| Formalization metadata | `lean/formalization.yaml` |
| Responsible author/maintainer | Gregory Morse |
| Authorization relationship | I am a responsible author or maintainer |
| Existing Palomar ID at this intake | Blank — first registration |
| Preliminary override | Disabled |

The selected `Unbounded` clause names the literal fixed-register,
identity-memory `activeInitial` and explicitly requires primitive-recursive
memory. Each counted changed field has its owning STORE fetched on the next
step. The selected `EffectiveInterpreter` clause requires the numbered
interpreter to reach the same halted configuration whose tape encodes the
terminal journal, starting from the exact encoded machine/input.

Four-register MOV simulation retains its positive deliberate zero-load trap
certificate and halt/divergence equivalences, following Dolan Section 5.
The complete tape and logical head observations remain on the actual source
trace. Native/COFF proofs are supporting material with explicit finite bounds
and machine-contract assumptions. The principal result is the conjunction
of these four mathematical definitions; the integer injection and two owner
declarations are also selected.

Lean remains `4.35.0-rc3`, compiler `470d5ce1400764999581fd26d5d72b00d990b0f4`.
Mathlib remains `5e043698502894993991089b2dd893867c0db5c2`; the original
acceptance used `302343bb9a029d4edab4f736703f0736896c1b64`.
All required checks passed for this candidate: full kernel/standard-axiom
and native CI, protected unmodified Palomar verification, and unmodified
Challenge rendering. The Challenge is 1,000 lines / 62,027 bytes, within
hard limits; the preferred smaller-surface warning remains disclosed.

Prepared submission notes (historical):

> Formalization of Morse's IJET 2018 pure-SMC construction with minimal
> positively proved M01–M20 errata and Dolan's credited MOV foundation.
> The unbounded distinct-field trace has an explicitly selected primitive-recursive
> initializer. The numbered interpreter's terminal journal is tied to its
> reached halted configuration on the encoded input. Conditional native/COFF
> proofs are supporting material. Codex made substantial contributions under
> the author's direction; no independent human review or registration is claimed.

The formalization license is CC0-1.0; cited papers retain their source terms.
Gregory Morse completed intake and registration. The public registry reports
trust level `high`. Private access links remain untracked.
