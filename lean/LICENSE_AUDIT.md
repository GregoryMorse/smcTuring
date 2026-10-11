# License check — 2026-10-11

**PASS: the formalization declares CC0-1.0, and GitHub independently detects
the same SPDX identifier from the repository's existing root `LICENSE.txt`.**
The detected Git blob is `0e259d42c996742e9e3cba14c677129b2c1b6311`.
Its text matches the local license modulo CRLF, and `formalization.yaml`
declares exactly `CC0-1.0`. There is one conventional root license file.
The [successful official Palomar workflow](https://github.com/GregoryMorse/smcTuring/actions/runs/38108849833) independently detected
`CC0-1.0` on proof commit `1ab379c2288ef5952c6e1bbdb8d655d31e5fbbd4`, matching the declared identifier.
Its normalized license SHA-256 is
`a2010f343487d3f7618affe54f789f5487602331c0a8d03f49e9a7c547cf0499`.

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
