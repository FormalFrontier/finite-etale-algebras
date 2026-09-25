# finite-etale-algebras

Reusable Lean theory of finite etale algebras, subalgebra composites, and
maximal finite etale subalgebras.

The initial unit proves that a surjective image of a finite etale algebra over
a field is finite etale. Consequently, the supremum of two finite etale
subalgebras of a commutative algebra is finite etale. It then constructs a
greatest finite etale subalgebra whenever their dimensions have a uniform
natural-number bound. The ambient algebra may be the zero ring, and no
perfectness, algebraic-closedness, reducedness, finite-dimensionality, or
Noetherianity assumption is made on it.

Every idempotent in a commutative algebra over a field is contained in a finite
etale subalgebra: the range of the split algebra `Fin 2 → K` acting through
the complementary idempotents `e` and `1 - e`. This also requires no
finite-dimensionality, finite-generation, reducedness, nontriviality, or
separability assumption on the ambient algebra.

Over a separably closed field, the library also identifies the number of
connected components of the spectrum of a finite etale algebra with its
vector-space dimension. Any continuous surjection onto that spectrum then
bounds the dimension by the source component count. These results allow
independent universes and retain zero-ring and empty-space edge cases.

For a finite Galois extension `L/k`, the library provides coefficientwise
semilinear descent for stable `L`-subalgebras of `L ⊗[k] R`. It constructs the
descended algebra as the honest preimage in `R`, proves that its scalar extension
is literally the original ambient subalgebra, and exposes the corresponding
algebra equivalence and range formulas. If the original subalgebra is finite
etale, the descended algebra is finite etale. No finiteness, reducedness, or
nontriviality assumption is made on `R`.

Nine elementary results in `GaloisDescent` need only `[Field k]`, `[Field L]`,
`[Algebra k L]`, `[CommRing R]`, and `[Algebra k R]`, not
`[FiniteDimensional k L]` or `[IsGalois k L]`:
`coefficientwise_tmul`, `coefficientwise_one`, `coefficientwise_mul`,
`coefficientwise_smul`, `mem_fixedSubmodule`, `fixedScalarExtension_tmul`,
`mem_descended`, `scalarExtensionMap_tmul`, and
`scalarExtensionMap_injective`. Ordinary applications keep their names;
positional `@` applications written for the older theorem types must drop the
two removed instance arguments. The inverse, reconstruction, and full descent
results within `GaloisDescent` retain `[FiniteDimensional k L]` and
`[IsGalois k L]`.

For a separable closure `K/k`, the finite-data API captures an embedded
finite-dimensional subalgebra in one finite Galois intermediate field, proves
coherence under enlargement of that field, and transfers absolute stability to
finite-level stability. A stable finite etale subalgebra of `K ⊗[k] R` therefore
descends to a finite etale subalgebra of `R`, with the reconstruction equivalence,
preimage membership, and scalar-extension range all stated as literal ambient
equalities. The construction does not impose finite-generation, reducedness, or
nontriviality assumptions on `R`.

For a purely inseparable field extension `K/k`, every idempotent of
`K ⊗[k] R` lies in the literal range of the right-factor inclusion from `R`;
the factor-reversed `R ⊗[k] K` formulation is also exposed. When `K` is
separably closed, any embedded finite etale `K`-subalgebra of `K ⊗[k] R`
is reconstructed from a finite etale `k`-subalgebra of `R`. The resulting
equivalence and range theorem agree literally with the existing ambient
scalar-extension map. No finite-dimensionality assumption on `K/k`, or
reducedness or nontriviality assumption on `R`, is imposed.

This repository is organized around source-independent commutative algebra.
Interpretation, provenance, correspondence, and coverage for motivating
sources remain in their source-metadata repositories. Lattice is responsible
for the initial integration on behalf of the Source-maintainers team.

## Use

Import `FiniteEtaleAlgebras` for the public API (or import an individual
`FiniteEtaleAlgebras.*` module). For example, in a Lean file in this project:

```lean
import FiniteEtaleAlgebras

example {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (e : A) (he : IsIdempotentElem e) :
    ∃ Q : Subalgebra K A, Q.IsFiniteEtale ∧ e ∈ Q :=
  Subalgebra.exists_isFiniteEtale_of_isIdempotentElem e he
```

`Examples/IdempotentSubalgebra.lean` and
`Examples/SeparableClosureDescent.lean` contain build-checked private clients
using only that aggregate import. The thirteen implementation-local proof
helpers are private and are not part of the public interface.

The [generated API reference](docs/API.md) displays native signatures and
docstrings, including implicit parameters, for all entries emitted by doc-gen4
from the eight shipped modules. [Generation and scope](docs/README.md) explains
the source links, generated-declaration limitations and reproducibility contract.

## Build and checks

Install the toolchain in `lean-toolchain` with `elan`, then in the project root
fetch the matching mathlib cache before building in a fresh checkout:

```sh
lake exe cache get
lake build --wfail
lake build --wfail FiniteEtaleAlgebras
lake build --wfail Examples.IdempotentSubalgebra Examples.SeparableClosureDescent
```

The default build includes the aggregate library and both example modules;
the last two commands also build those targets explicitly. For a standalone
client file, run `lake env lean Client.lean`. The project pins Lean
`v4.34.0-rc2` and mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`
in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

The greatest-subalgebra result requires a supplied uniform rank bound; this
library does not prove one exists. The spectrum results require a separably
closed base, and the reconstruction results impose their stated Galois,
separable-closure or purely inseparable field-extension hypotheses. Complete
source formalization is not claimed. The two
`unusedSectionVars` overrides in the descent modules have been removed; the
eleven affected theorems now omit unneeded instances locally, and the generated
`coefficientwise.eq_1` equation has a targeted docstring.
Three earlier `haveILetI` overrides were removed by the accepted proof-style
cleanup. A warning-free ordinary build or selected lint is not full release-lint,
private-axiom or separate proof-recheck certification. Generated Markdown API
docs bind the exact mathematical sources and pins identified in
[native-input.json](docs/native-input.json), including the generalized theorem
signatures. Exact-candidate check, independent artifact/rights review and release
acceptance records are separate from these files; the documentation and metadata
do not themselves establish release acceptance or publication.
[formalization.yaml](formalization.yaml) records the project's
scope, sources, AI involvement and development-review status using format v0.4;
metadata presence or schema validity is not release acceptance.

## Mathematical references and original constructions

J. S. Milne, *Algebraic Groups* (2017), Propositions 1.29 and 1.30, motivates
the finite-etale subalgebra and descent questions. The separable-closure step
in the proof of Proposition 1.30(a) is on printed page 15 of `iAG2017.pdf`.
This library supplies reusable algebraic ingredients, not the complete scheme
statements or a claim that either proposition has been fully formalized. The
book's mathematical authorship remains Milne's; no endorsement is claimed.

The finite-Galois and finite-stage approach was developed in Formal Frontier's
earlier *Semilinear finite-etale subalgebra reconstruction* exposition by
Formalization Worker A, before the separate Lean implementations credited below.
The finite-Galois implementation uses trace-dual sums and Dedekind independence;
finite-dimensional capture then reduces separable-closure descent to a finite
Galois stage. The earlier exposition used a matrix argument for the relevant
trace-dual identity. These are mathematical constructions and adaptations, not
a bundled copy of the book or exposition.

The formal implementation builds on the pinned mathlib APIs for finite-dimensional
algebras, tensor products, etaleness and descent, Galois theory, trace-dual bases,
purely inseparable extensions, and spectra. Mathlib and its contributors retain
their own formalization credit and license notices.

## Authors and license

Authors: Formal Frontier Agents

Original Formal Frontier contributions are licensed under [Apache 2.0](LICENSE).
The formalization was developed with AI agents and human project direction;
compilation and independent agent review, not AI output alone, support the
accepted development. The following credit survives independently of the
development Git history:

| Contributor identity | Contributions |
| --- | --- |
| Lattice | Initial maximal finite-etale subalgebra and spectrum/component APIs; integration and documentation/metadata maintenance. |
| Anchor | Original project native-documentation markup recipe adapted by Lattice for this library; see docs/README.md. |
| Formalization Worker A | Earlier semilinear reconstruction exposition; later, separate executions implemented separable-closure descent and its clients, the idempotent-subalgebra theorem/client, and public-module/persistent-example readiness; subsequent residual-lint/API investigation. |
| Formalization Worker B | Finite-Galois semilinear descent, purely inseparable descent, the later common mathlib-pin update, and subsequent theorem-hypothesis generalization with persistent migration clients. |

The worker names denote pooled AI service identities, not individual humans or
one continuous execution. Their distinct contribution/review executions and exact
predecessor revisions are recorded in development records; later assembly does
not replace earlier contributor credit. The collective author credit does not
identify a legal copyright holder. Independent agent reviewers include Atlas,
Prism and fresh non-author worker executions; their code reviews are not human
review, source-author endorsement or final release acceptance.

Standing project licensing authorization covers verified original project work,
including earlier internal contributions reused here. Third-party material retains
its applicable terms, attribution and notices; mathematical citation alone is not
permission to copy protected expression. The repository does not bundle the
source book, exposition or mathlib implementation. Any concrete adapted-expression
question, generated documentation/assets and the proposed public history still
require their own independent rights assessment before release. A root license
or schema-valid metadata alone does not establish that clearance.
