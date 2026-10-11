# Final cleanup — 2026-10-11

The dedicated task `/home/morse/smcTuring-proof-20261006` and retired `smc`
tmux session were removed from `157.181.172.78` after all progressed source,
logs, reports and manifests were fetched and verified. Unrelated server paths,
sessions and processes were preserved.

The local `validation/remote`, remote-agent/evidence copies, temporary checkouts,
Lean/editor toolchain caches, build caches and PDF intermediates were removed.
Operational Palomar/CI files are retained in compact local archives; the three
published policy/schema tools remain in `validation/palomar`.

Final GitHub acceptance archive:

```
validation/checkpoint-archive/final-github-acceptance-20261011.zip
SHA-256: 8cb75cd0bc9c8d0063c97818c7c0acea600ef856b5cd358cce2b3ce66d72cfb1
203,076,999 bytes; 2,533 files; every member hash verified
```

The earlier agent checkpoint, coordinator recovery, server diagnostics and
workstation validation archives remain locally, with their hashes recorded in
[final acceptance](../lean/FINAL_ACCEPTANCE.json). These archives are ignored by
Git. The large Windows compiler cache remains a GitHub artifact for verified
retries. No compiled objects were added to the source repository.

The proof source, reviewed [errata PDF](../output/pdf/morse-2018-errata.pdf),
[TeX](../lean/errata/morse-2018-errata.tex),
[minimal diff](../lean/errata/morse-2018-minimal.diff) and public acceptance
receipts are retained. Local archive/check commands stayed below the existing
1.5 GB guard. No unrelated workstation/editor processes were terminated.
