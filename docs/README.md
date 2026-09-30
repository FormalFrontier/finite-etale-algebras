# API documentation

[API.md](API.md) is a generated, searchable Markdown reference for the native
doc-gen4 display entries in all eight shipped modules. See the root
[headline results](../README.md#headline-results) for scope and
[example](../README.md#use) for use. The
[shipped Lean modules](../FiniteEtaleAlgebras.lean) are the source of truth.

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
with proof bodies. Every entry links to its source lines in this checkout, for
example the [greatest-subalgebra theorem](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L146)
and the [component bound](../FiniteEtaleAlgebras/SpectrumComponents.lean#L68).

## Exact inputs and reproduction

[native-input.json](native-input.json) binds the analyzed source revision
`fe7e68f76a3359419c4c44720f4171a421c51fad`, its eight Lean files, toolchain and
both Lake pin/configuration files. It records raw native-record SHA256 hashes,
the exact name/kind inventory, native generation receipt hash and doc-gen4
revision `97d4ecdfc8e09e7f511724c25e303d448de6a3db`.
[api-manifest.json](api-manifest.json) binds the rendered Markdown and input
manifest, including source-line positions. The 11 source/pin input files are
byte-identical in this checkout to the manifest's recorded hashes. The
historical revision and source labels are functional generation bindings, **not
public navigation links**: the release's shipped source links above and in
[API.md](API.md) provide that navigation. These bindings are not signatures,
proof certificates, or standalone attestations of native execution or release
acceptance; those require separate evidence.

To reproduce the Markdown, first obtain the separately retained native `fromDb`
data directory (it is not included in this library's shipped tree):

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

The URL in the command is a historical native generator input label required by
the recorded manifest, **not** a claim that this development commit is available
on GitHub. Use the relative source links in this checkout for reading; do not
substitute a published commit ID for that label without regenerating and
reviewing the affected bindings. Changed mathematical sources or pins require
a new native run, reviewed input inventory and affected verification; hashes
must not be updated merely to suppress a mismatch. Output directories, binaries
and native website assets are not shipped here.

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
native-run provenance. Release records authenticate their actual candidate and
documentation evidence separately; this file cannot contain its own commit ID
without circularity.

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
the production documentation. This provenance description does not substitute
for the release's separate rights and proof-evidence records.
