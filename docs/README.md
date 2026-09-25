# API documentation

[API.md](API.md) is a generated, searchable Markdown reference for the native
doc-gen4 display entries in all eight shipped modules. See the root
[mathematical overview and example](../README.md) for scope and use.

| Module | Native display entries |
| --- | ---: |
| `FiniteEtaleAlgebras.MaximalSubalgebra` | 7 |
| `FiniteEtaleAlgebras.SemilinearDescent` | 23 |
| `FiniteEtaleAlgebras.SpectrumComponents` | 2 |
| `FiniteEtaleAlgebras.SeparableClosureDescent` | 37 |
| `FiniteEtaleAlgebras.PurelyInseparableDescent` | 10 |
| `FiniteEtaleAlgebras` | 0 |
| `Examples.IdempotentSubalgebra` | 0 |
| `Examples.SeparableClosureDescent` | 0 |

The 79 entries include structure fields and two generated constructors. The
constructors have no native docstring and are explicitly labelled. Private
implementation helpers and persistent private examples are not public API.
Some generated declarations, notably `GaloisDescent.coefficientwise.eq_1`, are
not displayed by doc-gen4 either, even with its targeted source docstring.
The equation is included in the separate declaration/proof census; native
display omission is not an unproved theorem or a missing source docstring.
These docs are not a complete public/private/generated declaration census.
Proof auditing and release acceptance are separate.

All implicit binders, including typeclass hypotheses, are retained when stripping
native HTML markup. Signatures use native display notation and short names in
the source module's context; they are not independently compilable declarations
with proof bodies. Every entry links to its source lines in the same checkout.

## Exact inputs and reproduction

[native-input.json](native-input.json) binds the analyzed source revision
`fe7e68f76a3359419c4c44720f4171a421c51fad`, its eight Lean files, toolchain and
both Lake pin/configuration files. It records raw native-record SHA256 hashes,
the exact name/kind inventory, native generation receipt hash and doc-gen4
revision `97d4ecdfc8e09e7f511724c25e303d448de6a3db`.
[api-manifest.json](api-manifest.json) binds the rendered Markdown and input
manifest. These are content bindings, not signatures or attestations that a
native command actually ran. Independent review must authenticate the complete
generation evidence and bind the exact final candidate separately.

To reproduce the Markdown from the retained native `fromDb` data directory:

```sh
python3 scripts/generate_api.py --native-data /path/to/doc-data --check
python3 scripts/test_generate_api.py --native-data /path/to/doc-data
```

Omit `--check` to regenerate the two output files. Python 3.10+ and Git are
required; no third-party Python packages or Lean build are needed for rendering.
The tests also run with `python3 -O` and `python3 -OO`; refusal checks do not rely
on Python assertions.

For fresh native generation, build this project using its pinned environment,
first successfully fetching `lake exe cache get`, then `lake build --wfail`.
Build doc-gen4 at the exact revision above in a separate checkout using its own
unchanged manifest/toolchain. Its pinned toolchain matches this project's
Lean `v4.34.0-rc2`. The documentation tool is not a library dependency and no
change to this project's Lake pins is needed. Use the resulting executable
below in the project `lake env` so its import paths resolve this project's
actual artifacts. Use fresh empty output directories; run `single` sequentially
for the eight modules in the order in `native-input.json`:

```sh
mkdir native-api rendered-api
lake env /path/to/doc-gen4 single --build native-api \
  FiniteEtaleAlgebras.MaximalSubalgebra api.db \
  https://github.com/FormalFrontier/finite-etale-algebras/blob/fe7e68f76a3359419c4c44720f4171a421c51fad/FiniteEtaleAlgebras/MaximalSubalgebra.lean
# Repeat single for each remaining manifest module, with its matching .lean path.
lake env /path/to/doc-gen4 bibPrepass --build rendered-api --none
lake env /path/to/doc-gen4 fromDb --build rendered-api \
  --manifest rendered-api/manifest.json native-api/api.db
python3 scripts/generate_api.py --native-data rendered-api/doc-data --check
```

The immutable-looking source URLs are native generator input labels; these docs
do not assert that the development commit exists on GitHub. Only relative source
links are rendered. Regenerating against changed mathematical sources or pins
requires a new native run, reviewed input inventory and affected verification;
never update hashes merely to suppress a mismatch. Output directories, binaries
and the native website's CSS/JavaScript/dependency assets are not shipped here.

## Parentless release snapshots and source archives

If the analyzed commit exists in a valid Git repository, the renderer requires
its exact source/pin bytes. A present-object mismatch, a noncommit object or any
Git command/repository error is fatal; it never falls back to trusting hashes.
Only an explicit `cat-file` missing-object response permits content continuity
through the exact committed `native-input.json` and matching source/pin bytes.
This supports parentless release snapshots without importing development history.

For an explicitly supplied source archive without a Git repository, add
`--source-only`. It checks the same manifest and bytes, but cannot authenticate
that manifest's commit. Invalid `.git` metadata or an enclosing different
repository is not an archive. In either fallback, the result establishes only
content continuity, not the existence of historical Git objects or independent
native-run provenance. Final release records must identify the actual candidate
and authenticate its documentation evidence separately; this file cannot contain
its own commit ID without circularity.

## Provenance and licensing

The Python markup adapter is adapted from Anchor's original Formal Frontier
ideal-completion documentation recipe, then specialized and extended by Lattice
for this library's native inventory, structure fields/constructors, exact line
fragments and history/content-continuity checks. Both are project contributions
under Apache-2.0; prior contributor credit is retained independently of ancestry.

Documentation text is taken from this library's original docstrings, with native
display signatures produced by doc-gen4. The external tool and its contributors
retain their own credit and terms. No tool implementation, fonts, CSS, JavaScript,
external dependency documentation, source book or compiled binary is bundled in
the production documentation. This provenance statement is not final independent
rights clearance or release acceptance.
