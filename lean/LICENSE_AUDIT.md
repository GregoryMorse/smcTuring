# License check — 2026-10-11

**PASS: the formalization declares CC0-1.0, and GitHub independently detects
the same SPDX identifier from the repository's existing root `LICENSE.txt`.**
The detected Git blob is `0e259d42c996742e9e3cba14c677129b2c1b6311`.
Its text matches the local license modulo CRLF, and `formalization.yaml`
declares exactly `CC0-1.0`. There is one conventional root license file.
The final Palomar workflow also runs its own license detector on the public
submission commit; that mechanical result is retained with the CI reports.

Detection evidence: [GitHub license API](https://api.github.com/repos/GregoryMorse/smcTuring/license)
and [existing root license](https://github.com/GregoryMorse/smcTuring/blob/master/LICENSE.txt).
The license's meaning is documented by [Creative Commons](https://creativecommons.org/publicdomain/zero/1.0/).

This check concerns the original proof development and repository source.
Cited papers and dependencies retain their own terms and attribution. The
[journal's article page](https://ijet.ise.pw.edu.pl/index.php/ijet/article/view/10.24425-119359)
identifies the published paper as open access and displays a Creative Commons
Attribution-NonCommercial 4.0 license. The packaged publisher PDF remains
unchanged, attributed and separately licensed; the repository's CC0 declaration
does not relicense it. Palomar's policy makes the same distinction between
the submitted repository license and licenses of cited sources.
