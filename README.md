# finite-etale-algebras

Reusable Lean theory of finite etale algebras, embedded subalgebra descent,
and connected components of spectra.

## Headline results

- **Finite etale subalgebras, composites and idempotents.** Over a field `k`,
  [surjective images](FiniteEtaleAlgebras/MaximalSubalgebra.lean#L44) of finite
  etale algebras are finite etale, and
  [binary suprema](FiniteEtaleAlgebras/MaximalSubalgebra.lean#L129) of finite
  etale subalgebras of a commutative `k`-algebra `R` remain finite etale. A
  *supplied* uniform natural-number bound on their dimensions yields a
  [greatest such subalgebra](FiniteEtaleAlgebras/MaximalSubalgebra.lean#L146);
  this library does not prove the existence of that bound. Every idempotent
  [lies in a finite etale subalgebra](FiniteEtaleAlgebras/MaximalSubalgebra.lean#L86),
  constructed from `Fin 2 → k` using `e` and `1 - e`.
- **Spectrum component counts.** For a finite etale algebra `S` over a
  separably closed field `k`, the
  [component-count theorem](FiniteEtaleAlgebras/SpectrumComponents.lean#L38)
  identifies `Nat.card (ConnectedComponents (PrimeSpectrum S))` with
  `Module.finrank k S`. A continuous surjection `X → PrimeSpectrum S`
  [bounds the dimension](FiniteEtaleAlgebras/SpectrumComponents.lean#L68)
  by the component count of `X` **when `[Finite (ConnectedComponents X)]`**.
  Independent universes, zero algebras and empty-space cases are retained.
- **Finite-Galois and separable-closure embedded descent.** For a finite
  Galois extension `L/k`, a subalgebra `P` of `L ⊗[k] R` stable under every
  [coefficientwise automorphism](FiniteEtaleAlgebras/SemilinearDescent.lean)
  is reconstructed from its honest preimage under `r ↦ 1 ⊗ r`. The
  [reconstruction equivalence](FiniteEtaleAlgebras/SemilinearDescent.lean#L420)
  and [range equality](FiniteEtaleAlgebras/SemilinearDescent.lean#L439)
  identify the *literal ambient* scalar extension with `P`; finite etaleness
  [descends](FiniteEtaleAlgebras/SemilinearDescent.lean#L446) if `P` is finite
  etale. For a separable closure `K/k`, the
  [finite-data layer](FiniteEtaleAlgebras/SeparableClosureDescent.lean)
  captures an embedded finite-dimensional algebra over a finite Galois
  intermediate field and is coherent under enlargement. Its
  [descent package](FiniteEtaleAlgebras/SeparableClosureDescent.lean#L479)
  reconstructs a finite etale `P` stable under *every* coefficientwise
  `k`-automorphism of `K`, including preimage membership and literal ambient
  range equality.
- **Purely inseparable idempotents and reconstruction.** For a purely
  inseparable field extension `K/k`, every idempotent of `K ⊗[k] R` belongs to
  the [range of the right-factor inclusion](FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L45)
  from `R`; [the reversed tensor orientation](FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L35)
  is also available. If `K` is additionally separably closed, the
  [reconstruction package](FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L79)
  recovers each embedded finite etale `K`-subalgebra from a finite etale
  `k`-subalgebra of `R`, with equivalence and
  [range equality](FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L237)
  agreeing with the literal ambient scalar-extension map. No
  finite-dimensionality assumption on `K/k` is imposed.

Throughout, the ambient `R` is a commutative algebra over a field; it need
not be finite-dimensional, finitely generated, reduced or nontrivial (the zero
ring is allowed). These are noncomputable mathematical interfaces, not
algorithms for extracting descended algebras. This library's `IsFiniteEtale`
predicate combines mathlib's `Module.Finite` and `Algebra.Etale`; mathlib also
supplies the tensor-product, Galois, descent and spectrum infrastructure.
This repository develops the subalgebra, component-count and literal
reconstruction interfaces described here. Full signatures appear in the
[API reference](docs/API.md); source-specific correspondence and coverage
belong in the respective source repositories, not this reusable library.

## Descent API compatibility

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

[`Examples/IdempotentSubalgebra.lean`](Examples/IdempotentSubalgebra.lean) and
[`Examples/SeparableClosureDescent.lean`](Examples/SeparableClosureDescent.lean) contain build-checked private clients
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

### Expected cost

An existing September 27, 2026 Linux native verification run in the pinned
environment measured 41.507 seconds for matching mathlib-cache retrieval,
6.338 seconds for cache verification, and 69.961 seconds for the library and
both example targets (2,591 Lake jobs). These are separate stages with cached
dependencies, not a cold end-to-end benchmark or a measurement of this
documentation revision. The separate axiom audit is not included in that build
time; no uncached mathlib source rebuild was needed or timed.

Allow several minutes for cache preparation and compilation, and additional time
for proof auditing. As a conservative planning estimate for this mathlib-based
workload, allow about 15 GiB of total memory headroom; this is **not** a measured
peak, a demonstrated minimum or a guarantee. Peak resident memory and a portable
CPU/storage baseline were not measured in these receipts. Network/cache state
and parallel compilation can materially change costs. Use the matching cache
rather than silently falling back to a mathlib source rebuild.

The [API documentation guide](docs/README.md) explains the 79 native display
entries, the signatures' historical source-byte bindings and the separate
proof-audit boundary. A successful build by itself does not establish the
transitive standard-axiom status of private declarations. The generated
documentation and [formalization metadata](formalization.yaml) describe this
library; they are not proof certificates or source-coverage decisions.

## Mathematical references and original constructions

J. S. Milne, *Algebraic Groups* (2017), Propositions 1.29 and 1.30, motivates
the finite-etale subalgebra and descent questions; its separable-closure
discussion in the proof of Proposition 1.30(a) appears on printed page 15.
This library supplies reusable algebraic ingredients, not the complete scheme
propositions or complete source coverage. No source-author endorsement is
claimed. Earlier original Formal Frontier mathematical work on semilinear
reconstruction informed the finite-Galois and finite-stage developments here.
The Lean implementation uses trace-dual sums and Dedekind independence for
finite-Galois descent, followed by finite-dimensional capture for descent over
a separable closure. The earlier project exposition instead used a matrix
argument for the trace-dual identity. The book and exposition are not bundled.

The implementation builds on pinned [mathlib](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5)
APIs for finite-dimensional algebras, tensor products, etaleness, Galois theory,
trace-dual bases, purely inseparable extensions and spectra. Its contributors
retain their own formalization credit and license notices.

## Authors and license

Authors: Formal Frontier Agents

Original Formal Frontier contributions are licensed under [Apache 2.0](LICENSE).
The formalization was developed with AI agents under human project direction
and independently reviewed by other agents; this is not a claim of human
mathematical review. Contributor credit survives independently of development
Git history:

| Contributor identity | Contributions |
| --- | --- |
| Lattice | Initial maximal finite-etale subalgebra and spectrum/component APIs; integration and documentation/metadata maintenance. |
| Anchor | Original project native-documentation markup recipe, adapted by Lattice; see [documentation provenance](docs/README.md#provenance-and-licensing). |
| Folio | Mathematical headline descriptions and checks of their hypotheses, adapted for this reader guide. |
| Other Formal Frontier AI contributors | Earlier semilinear reconstruction exposition; finite-Galois, separable-closure and purely inseparable descent; idempotent construction, public imports, examples, hypothesis generalization and migration clients. |

The collective author credit does not identify a legal copyright holder.
Third-party work retains its own applicable terms and attribution; the repository
does not bundle Milne's book, the earlier project exposition or mathlib's source.
