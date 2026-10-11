Title: Preserve Mathlib-compatible Plausible pin for source-identical Verso dependency

This is an optional compatibility improvement for existing newer Mathlib pins.
The author is independently validating a coherent official Mathlib snapshot
with the unmodified pipeline as the ordinary submission route. This PR is not
claimed as a prerequisite for submission.

The Lean 4.35.0-rc3 Verso release pins Plausible at `fb13df7…`, while Mathlib
`302343b…` pins it at `afc2695…`. Their complete tracked trees differ only in
`.github/workflows/lean_action_ci.yml`; all 28 Lean files and other build inputs
are identical. The renderer currently rejects this pair during manifest merge.
Overriding the project's pin clears that error but fails Mathlib's strict shared
dependency manifest check during cache discovery.

Keep the submitted dependency revision and permit only this exact immutable
Plausible pair, from the same canonical repository and standard package layout.
Other revisions, forks, package names, configurations and subdirectories still
fail. Cache, sandbox, accepted source and declaration checks are unchanged.

Validation: eight focused regression tests pass. The full patched renderer run
downloads all 8,998 cache archives, builds and renders the unchanged Challenge,
and passes all eight selected declarations through the final sanitized bundle:
https://github.com/GregoryMorse/smcTuring/actions/runs/38154282274

The workflow records the exact upstream base and patched source hashes and
verifies both complete upstream Git trees before applying the patch. It is an
advisory reproduction, not a registry acceptance run. It finishes in under five
minutes, without repeating the smcTuring full proof or native audit.

Patch and reproduction tools:
https://github.com/GregoryMorse/smcTuring/blob/238ce4bf97d9aee768d46b30056e000852ce659d/validation/ci/palomar-renderer-plausible.patch

This addresses the Plausible conflict described in the discussion of #131;
it does not purport to fix arbitrary conflicting SubVerso forks.
