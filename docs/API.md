# Generated API reference

Native doc-gen4 display entries from all eight shipped Lean modules.
Import `FiniteEtaleAlgebras` for the library API; the two `Examples.*`
modules contain checked private clients. Private helpers and some generated
declarations are not displayed by doc-gen4; this is not a full proof census.

Signatures retain all implicit binders, but are native display signatures,
not complete source declarations with bodies. Short names and universe
variables have the source module's namespace/import context. Source links
refer to the same checkout. See [generation and scope](README.md) and
[content manifest](api-manifest.json).

## FiniteEtaleAlgebras.MaximalSubalgebra

### Algebra.IsFiniteEtale

```lean
def Algebra.IsFiniteEtale (K : Type u) (A : Type v) [CommRing K] [CommRing A] [Algebra K A] : Prop
```

A finite etale algebra, expressed as the conjunction of the two existing
mathlib predicates.

[Source](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L32-L36).

### Algebra.IsFiniteEtale.of_surjective

```lean
theorem Algebra.IsFiniteEtale.of_surjective {K : Type u} {A : Type v} {B : Type w} [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (hA : IsFiniteEtale K A) (f : A →ₐ[K] B) (hf : Function.Surjective ⇑f) : IsFiniteEtale K B
```

A surjective image of a finite etale algebra over a field is finite etale.

[Source](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L43-L55).

### Subalgebra.IsFiniteEtale

```lean
abbrev Subalgebra.IsFiniteEtale {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] (A : Subalgebra K R) : Prop
```

A subalgebra is finite etale when its induced algebra structure is finite
and etale.

[Source](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L65-L68).

### Subalgebra.isFiniteEtale_bot

```lean
theorem Subalgebra.isFiniteEtale_bot {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] : ⊥.IsFiniteEtale
```

The scalar subalgebra is finite etale, including when the ambient algebra
is the zero ring.

[Source](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L70-L78).

### Subalgebra.exists_isFiniteEtale_of_isIdempotentElem

```lean
theorem Subalgebra.exists_isFiniteEtale_of_isIdempotentElem {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] (e : R) (he : IsIdempotentElem e) : ∃ (Q : Subalgebra K R), Q.IsFiniteEtale ∧ e ∈ Q
```

Every idempotent of a commutative algebra over a field belongs to a finite
etale subalgebra. No finiteness, reducedness, or nontriviality assumption is
made on the ambient algebra.

The subalgebra is the range of the map from the split finite etale algebra
`Fin 2 → K` determined by the complementary idempotents `e` and `1 - e`.

[Source](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L80-L122).

### Subalgebra.IsFiniteEtale.sup

```lean
theorem Subalgebra.IsFiniteEtale.sup {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] {A B : Subalgebra K R} (hA : A.IsFiniteEtale) (hB : B.IsFiniteEtale) : (A ⊔ B).IsFiniteEtale
```

The supremum of two finite etale subalgebras is finite etale.

[Source](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L128-L140).

### Subalgebra.exists_greatest_isFiniteEtale_of_finrank_le

```lean
theorem Subalgebra.exists_greatest_isFiniteEtale_of_finrank_le {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R] (N : ℕ) (hbound : ∀ (A : Subalgebra K R), A.IsFiniteEtale → Module.finrank K ↥A ≤ N) : ∃ (A : Subalgebra K R), A.IsFiniteEtale ∧ ∀ (B : Subalgebra K R), B.IsFiniteEtale → B ≤ A
```

If the dimensions of the finite etale subalgebras of `R` are uniformly
bounded, then `R` has a greatest finite etale subalgebra.

[Source](../FiniteEtaleAlgebras/MaximalSubalgebra.lean#L144-L169).

## FiniteEtaleAlgebras.SemilinearDescent

### GaloisDescent.coefficientwise

```lean
noncomputable def GaloisDescent.coefficientwise {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (σ : Gal(L/k)) : TensorProduct k L R →ₐ[k] TensorProduct k L R
```

Coefficientwise Galois conjugation on `L ⊗[k] R`.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L41-L43).

### GaloisDescent.coefficientwise_tmul

```lean
theorem GaloisDescent.coefficientwise_tmul {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (σ : Gal(L/k)) (l : L) (r : R) : (coefficientwise σ) (l ⊗ₜ[k] r) = σ l ⊗ₜ[k] r
```

Coefficientwise conjugation sends `l ⊗ r` to `σ(l) ⊗ r`.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L49-L51).

### GaloisDescent.fixed_iff_mem_range_includeRight

```lean
theorem GaloisDescent.fixed_iff_mem_range_includeRight {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] (x : TensorProduct k L R) : (∀ (σ : Gal(L/k)), (coefficientwise σ) x = x) ↔ x ∈ Set.range ⇑Algebra.TensorProduct.includeRight
```

The fixed tensors under coefficientwise `Gal(L/k)` are exactly `1 ⊗ r`.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L111-L146).

### GaloisDescent.coefficientwise_one

```lean
theorem GaloisDescent.coefficientwise_one {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (x : TensorProduct k L R) : (coefficientwise 1) x = x
```

The identity automorphism acts identically on the tensor product.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L149-L154).

### GaloisDescent.coefficientwise_mul

```lean
theorem GaloisDescent.coefficientwise_mul {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (σ τ : Gal(L/k)) (x : TensorProduct k L R) : (coefficientwise (σ * τ)) x = (coefficientwise σ) ((coefficientwise τ) x)
```

Coefficientwise conjugation respects the Galois-group multiplication order.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L157-L163).

### GaloisDescent.coefficientwise_smul

```lean
theorem GaloisDescent.coefficientwise_smul {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (σ : Gal(L/k)) (l : L) (x : TensorProduct k L R) : (coefficientwise σ) (l • x) = σ l • (coefficientwise σ) x
```

Coefficientwise conjugation is semilinear for the `L`-module structure.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L166-L171).

### GaloisDescent.fixedSubmodule

```lean
def GaloisDescent.fixedSubmodule {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] : Submodule k (TensorProduct k L R)
```

The `k`-submodule of tensors fixed by every coefficientwise conjugation.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L194-L199).

### GaloisDescent.mem_fixedSubmodule

```lean
theorem GaloisDescent.mem_fixedSubmodule {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] {x : TensorProduct k L R} : x ∈ fixedSubmodule ↔ ∀ (σ : Gal(L/k)), (coefficientwise σ) x = x
```

Membership in the fixed submodule is pointwise Galois fixedness.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L202-L205).

### GaloisDescent.fixedScalarExtension

```lean
noncomputable def GaloisDescent.fixedScalarExtension {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] : TensorProduct k L ↥fixedSubmodule →ₗ[L] TensorProduct k L R
```

The canonical scalar-extension map from the fixed submodule.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L207-L216).

### GaloisDescent.fixedScalarExtension_tmul

```lean
theorem GaloisDescent.fixedScalarExtension_tmul {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (l : L) (w : ↥fixedSubmodule) : fixedScalarExtension (l ⊗ₜ[k] w) = l • ↑w
```

The canonical fixed-point scalar-extension map on pure tensors.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L219-L223).

### GaloisDescent.fixedScalarExtensionEquiv

```lean
noncomputable def GaloisDescent.fixedScalarExtensionEquiv {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] : TensorProduct k L ↥fixedSubmodule ≃ₗ[L] TensorProduct k L R
```

Semilinear descent for the coefficientwise action on a tensor product.

The inverse is the trace-dual averaging formula; in particular, this equivalence
does not rely on an abstract effective-descent result.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L333-L344).

### GaloisDescent.IsStable

```lean
def GaloisDescent.IsStable {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) : Prop
```

A subalgebra is stable under coefficientwise Galois conjugation.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L346-L349).

### GaloisDescent.descended

```lean
def GaloisDescent.descended {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) : Subalgebra k R
```

The honest preimage in the original algebra of a scalar-extended subalgebra.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L351-L353).

### GaloisDescent.mem_descended

```lean
theorem GaloisDescent.mem_descended {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] {P : Subalgebra L (TensorProduct k L R)} {r : R} : r ∈ descended P ↔ Algebra.TensorProduct.includeRight r ∈ P
```

An element belongs to the descended algebra exactly when its image `1 ⊗ r`
belongs to the given subalgebra.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L356-L361).

### GaloisDescent.baseChange_descended_eq

```lean
theorem GaloisDescent.baseChange_descended_eq {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) (hP : IsStable P) : Subalgebra.baseChange L (descended P) = P
```

The scalar extension of the honest preimage is literally the given stable
subalgebra inside `L ⊗[k] R`.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L363-L395).

### GaloisDescent.scalarExtensionMap

```lean
noncomputable def GaloisDescent.scalarExtensionMap {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) : TensorProduct k L ↥(descended P) →ₐ[L] TensorProduct k L R
```

Scalar extension of the inclusion of the descended subalgebra.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L397-L400).

### GaloisDescent.scalarExtensionMap_tmul

```lean
theorem GaloisDescent.scalarExtensionMap_tmul {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) (l : L) (d : ↥(descended P)) : (scalarExtensionMap P) (l ⊗ₜ[k] d) = l ⊗ₜ[k] ↑d
```

The scalar-extension inclusion sends `l ⊗ d` to the same pure tensor in the
ambient algebra.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L403-L407).

### GaloisDescent.scalarExtensionMap_injective

```lean
theorem GaloisDescent.scalarExtensionMap_injective {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) : Function.Injective ⇑(scalarExtensionMap P)
```

Scalar extension preserves the injectivity of the descended-algebra
inclusion.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L410-L416).

### GaloisDescent.reconstructionEquiv

```lean
noncomputable def GaloisDescent.reconstructionEquiv {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) (hP : IsStable P) : TensorProduct k L ↥(descended P) ≃ₐ[L] ↥P
```

The reconstructed scalar extension, in the orientation from the descended
algebra to the given stable subalgebra.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L418-L423).

### GaloisDescent.coe_reconstructionEquiv_apply

```lean
theorem GaloisDescent.coe_reconstructionEquiv_apply {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) (hP : IsStable P) (z : TensorProduct k L ↥(descended P)) : ↑((reconstructionEquiv P hP) z) = (scalarExtensionMap P) z
```

After coercion to the ambient tensor product, reconstruction is the literal
scalar-extension inclusion.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L425-L429).

### GaloisDescent.reconstructionEquiv_tmul

```lean
theorem GaloisDescent.reconstructionEquiv_tmul {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) (hP : IsStable P) (l : L) (d : ↥(descended P)) : ↑((reconstructionEquiv P hP) (l ⊗ₜ[k] d)) = l ⊗ₜ[k] ↑d
```

Reconstruction has the expected literal ambient value on pure tensors.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L431-L435).

### GaloisDescent.scalarExtensionMap_range

```lean
theorem GaloisDescent.scalarExtensionMap_range {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) (hP : IsStable P) : (scalarExtensionMap P).range = P
```

The range of the scalar-extension inclusion is literally the original stable
subalgebra.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L437-L441).

### GaloisDescent.descended_isFiniteEtale

```lean
theorem GaloisDescent.descended_isFiniteEtale {k : Type u} {L : Type v} {R : Type w} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] [CommRing R] [Algebra k R] (P : Subalgebra L (TensorProduct k L R)) (hP : IsStable P) (hEtale : P.IsFiniteEtale) : (descended P).IsFiniteEtale
```

A finite-etale stable subalgebra descends to a finite-etale subalgebra of the
original algebra.  Finiteness and etaleness are descended only after the literal
reconstruction equivalence has been established.

[Source](../FiniteEtaleAlgebras/SemilinearDescent.lean#L443-L455).

## FiniteEtaleAlgebras.SpectrumComponents

### Algebra.IsFiniteEtale.natCard_connectedComponents_primeSpectrum_eq_finrank

```lean
theorem Algebra.IsFiniteEtale.natCard_connectedComponents_primeSpectrum_eq_finrank {k : Type u} {S : Type v} [Field k] [IsSepClosed k] [CommRing S] [Algebra k S] (hS : IsFiniteEtale k S) : Nat.card (ConnectedComponents (PrimeSpectrum S)) = Module.finrank k S
```

Over a separably closed field, the number of connected components of the
spectrum of a finite etale algebra is its vector-space dimension.

[Source](../FiniteEtaleAlgebras/SpectrumComponents.lean#L36-L63).

### Algebra.IsFiniteEtale.finrank_le_natCard_connectedComponents_of_surjective

```lean
theorem Algebra.IsFiniteEtale.finrank_le_natCard_connectedComponents_of_surjective {k : Type u} {S : Type v} [Field k] [IsSepClosed k] [CommRing S] [Algebra k S] {X : Type w} [TopologicalSpace X] [Finite (ConnectedComponents X)] (hS : IsFiniteEtale k S) (f : X → PrimeSpectrum S) (hf : Continuous f) (hsurj : Function.Surjective f) : Module.finrank k S ≤ Nat.card (ConnectedComponents X)
```

A continuous surjection onto the spectrum of a finite etale algebra over a
separably closed field bounds its dimension by the number of connected
components of the source.

[Source](../FiniteEtaleAlgebras/SpectrumComponents.lean#L65-L75).

## FiniteEtaleAlgebras.SeparableClosureDescent

### SeparableClosureDescent.extensionMap

```lean
noncomputable def SeparableClosureDescent.extensionMap {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] : TensorProduct k L R →ₐ[L] TensorProduct k K R
```

The literal inclusion `L ⊗[k] R → K ⊗[k] R` in a field tower.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L35-L37).

### SeparableClosureDescent.extensionMap_tmul

```lean
theorem SeparableClosureDescent.extensionMap_tmul {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (l : L) (r : R) : extensionMap (l ⊗ₜ[k] r) = (algebraMap L K) l ⊗ₜ[k] r
```

The finite-stage inclusion has its expected value on pure tensors.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L39-L42).

### SeparableClosureDescent.extensionMap_injective

```lean
theorem SeparableClosureDescent.extensionMap_injective {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] : Function.Injective ⇑extensionMap
```

Extension of the coefficient field is injective inside the ambient tensor product.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L44-L50).

### SeparableClosureDescent.stage

```lean
noncomputable def SeparableClosureDescent.stage {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : Subalgebra L (TensorProduct k L R)
```

The literal intersection/preimage of an embedded `K`-subalgebra with
`L ⊗[k] R`.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L52-L56).

### SeparableClosureDescent.mem_stage

```lean
theorem SeparableClosureDescent.mem_stage {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} {z : TensorProduct k L R} : z ∈ stage P ↔ extensionMap z ∈ P
```

Membership in the finite stage is literal ambient membership after applying
the coefficient-field inclusion.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L58-L62).

### SeparableClosureDescent.stageInclusion

```lean
noncomputable def SeparableClosureDescent.stageInclusion {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : ↥(stage P) →ₐ[L] ↥P
```

The finite-stage algebra includes into the original algebra through the
literal ambient coefficient-field map.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L64-L75).

### SeparableClosureDescent.coe_stageInclusion_apply

```lean
theorem SeparableClosureDescent.coe_stageInclusion_apply {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) (z : ↥(stage P)) : ↑((stageInclusion P) z) = extensionMap ↑z
```

After coercion to the ambient tensor product, the stage inclusion is the
literal coefficient-field extension map.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L77-L82).

### SeparableClosureDescent.reconstructionMap

```lean
noncomputable def SeparableClosureDescent.reconstructionMap {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : TensorProduct L K ↥(stage P) →ₐ[K] ↥P
```

Scalar extension of the finite-stage inclusion, with codomain the original
embedded subalgebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L84-L90).

### SeparableClosureDescent.coe_reconstructionMap_tmul

```lean
theorem SeparableClosureDescent.coe_reconstructionMap_tmul {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) (a : K) (z : ↥(stage P)) : ↑((reconstructionMap P) (a ⊗ₜ[L] z)) = (algebraMap K (TensorProduct k K R)) a * extensionMap ↑z
```

After coercion to the ambient tensor product, reconstruction sends a pure
tensor to the scalar times the ambient finite-stage inclusion.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L92-L98).

### SeparableClosureDescent.map_stage_eq_inf

```lean
theorem SeparableClosureDescent.map_stage_eq_inf {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : Subalgebra.map extensionMap (stage P) = Subalgebra.restrictScalars L P ⊓ extensionMap.range
```

The image of the finite stage is literally the intersection of the original
subalgebra with `L ⊗[k] R` inside the ambient `K`-tensor product.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L100-L107).

### SeparableClosureDescent.ambientReconstructionMap

```lean
noncomputable def SeparableClosureDescent.ambientReconstructionMap {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : TensorProduct L K ↥(stage P) →ₐ[K] TensorProduct k K R
```

The ambient composite of finite-stage scalar extension.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L109-L114).

### SeparableClosureDescent.ambientReconstructionMap_eq

```lean
theorem SeparableClosureDescent.ambientReconstructionMap_eq {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : ambientReconstructionMap P = P.val.comp (reconstructionMap P)
```

Reconstruction followed by the subtype inclusion is the literal ambient
scalar-extension map.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L129-L139).

### SeparableClosureDescent.reconstructionMap_injective

```lean
theorem SeparableClosureDescent.reconstructionMap_injective {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : Function.Injective ⇑(reconstructionMap P)
```

The finite-stage reconstruction map is injective, independently of whether
its image already spans the original algebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L141-L155).

### SeparableClosureDescent.reconstructionMap_surjective_of_basis

```lean
theorem SeparableClosureDescent.reconstructionMap_surjective_of_basis {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] {ι : Type u_1} [Fintype ι] (P : Subalgebra K (TensorProduct k K R)) (b : Module.Basis ι K ↥P) (hb : ∀ (i : ι), ↑(b i) ∈ extensionMap.range) : Function.Surjective ⇑(reconstructionMap P)
```

A basis whose ambient vectors are already defined over `L` makes the
finite-stage reconstruction surjective.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L157-L182).

### SeparableClosureDescent.reconstructionEquivOfBasis

```lean
noncomputable def SeparableClosureDescent.reconstructionEquivOfBasis {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] {ι : Type u_1} [Fintype ι] (P : Subalgebra K (TensorProduct k K R)) (b : Module.Basis ι K ↥P) (hb : ∀ (i : ι), ↑(b i) ∈ extensionMap.range) : TensorProduct L K ↥(stage P) ≃ₐ[K] ↥P
```

Literal finite-stage reconstruction as an algebra equivalence, in the
orientation from scalar extension of the intersection to the given algebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L184-L192).

### SeparableClosureDescent.coe_reconstructionEquivOfBasis_apply

```lean
theorem SeparableClosureDescent.coe_reconstructionEquivOfBasis_apply {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] {ι : Type u_1} [Fintype ι] (P : Subalgebra K (TensorProduct k K R)) (b : Module.Basis ι K ↥P) (hb : ∀ (i : ι), ↑(b i) ∈ extensionMap.range) (z : TensorProduct L K ↥(stage P)) : ↑((reconstructionEquivOfBasis P b hb) z) = (ambientReconstructionMap P) z
```

After coercion to the ambient tensor product, finite-stage reconstruction
is the literal scalar-extension map.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L194-L204).

### SeparableClosureDescent.extensionMap_trans

```lean
theorem SeparableClosureDescent.extensionMap_trans {k : Type u} {L : Type v} {M : Type y} {K : Type w} {R : Type x} [Field k] [Field L] [Field M] [Field K] [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M] [Algebra k K] [Algebra L K] [Algebra M K] [IsScalarTower k L K] [IsScalarTower k M K] [IsScalarTower L M K] [CommRing R] [Algebra k R] (z : TensorProduct k L R) : extensionMap z = extensionMap (extensionMap z)
```

Literal coefficient-field inclusions compose in a tower.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L217-L226).

### SeparableClosureDescent.stage_tower

```lean
theorem SeparableClosureDescent.stage_tower {k : Type u} {L : Type v} {M : Type y} {K : Type w} {R : Type x} [Field k] [Field L] [Field M] [Field K] [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M] [Algebra k K] [Algebra L K] [Algebra M K] [IsScalarTower k L K] [IsScalarTower k M K] [IsScalarTower L M K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : stage P = stage (stage P)
```

Taking the literal finite-stage intersection is coherent under enlargement
of the coefficient field.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L228-L237).

### SeparableClosureDescent.reconstructionEquivTrans

```lean
noncomputable def SeparableClosureDescent.reconstructionEquivTrans {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (D : Subalgebra k R) (PL : Subalgebra L (TensorProduct k L R)) (P : Subalgebra K (TensorProduct k K R)) (eFinite : TensorProduct k L ↥D ≃ₐ[L] ↥PL) (eStage : TensorProduct L K ↥PL ≃ₐ[K] ↥P) : TensorProduct k K ↥D ≃ₐ[K] ↥P
```

Compose literal reconstruction over a finite coefficient field with the
coefficient-field tower equivalence.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L248-L255).

### SeparableClosureDescent.coe_reconstructionEquivTrans_apply

```lean
theorem SeparableClosureDescent.coe_reconstructionEquivTrans_apply {k : Type u} {L : Type v} {K : Type w} {R : Type x} [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K] [CommRing R] [Algebra k R] (D : Subalgebra k R) (PL : Subalgebra L (TensorProduct k L R)) (P : Subalgebra K (TensorProduct k K R)) (eFinite : TensorProduct k L ↥D ≃ₐ[L] ↥PL) (eStage : TensorProduct L K ↥PL ≃ₐ[K] ↥P) (hFinite : ∀ (z : TensorProduct k L ↥D), ↑(eFinite z) = (Algebra.TensorProduct.map (AlgHom.id L L) D.val) z) (hStage : ∀ (z : TensorProduct L K ↥PL), ↑(eStage z) = (Algebra.TensorProduct.cancelBaseChange k L K K R) ((Algebra.TensorProduct.map (AlgHom.id K K) PL.val) z)) (z : TensorProduct k K ↥D) : ↑((reconstructionEquivTrans D PL P eFinite eStage) z) = (Algebra.TensorProduct.map (AlgHom.id K K) D.val) z
```

The composite tower reconstruction retains the literal ambient inclusion.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L257-L286).

### SeparableClosureDescent.exists_finiteGalois_stage_basis

```lean
theorem SeparableClosureDescent.exists_finiteGalois_stage_basis {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [IsGalois k K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) [Module.Finite K ↥P] : ∃ (L : FiniteGaloisIntermediateField k K), ∀ (i : Fin (Module.finrank K ↥P)), ↑((Module.finBasis K ↥P) i) ∈ extensionMap.range
```

Finitely many basis tensors are simultaneously defined over one finite
Galois intermediate field.  This is the finite-coefficient input needed for
literal subalgebra descent.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L307-L336).

### SeparableClosureDescent.extensionMap_coefficientwise

```lean
theorem SeparableClosureDescent.extensionMap_coefficientwise {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] (L : FiniteGaloisIntermediateField k K) (sigma : Gal(K/k)) (z : TensorProduct k (↥L.toIntermediateField) R) : extensionMap ((GaloisDescent.coefficientwise ((AlgEquiv.restrictNormalHom ↥L.toIntermediateField) sigma)) z) = (GaloisDescent.coefficientwise sigma) (extensionMap z)
```

Coefficientwise conjugation commutes with the literal inclusion from a
finite normal intermediate field.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L348-L365).

### SeparableClosureDescent.stage_isStable

```lean
theorem SeparableClosureDescent.stage_isStable {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [IsGalois k K] [CommRing R] [Algebra k R] (L : FiniteGaloisIntermediateField k K) (P : Subalgebra K (TensorProduct k K R)) (hP : GaloisDescent.IsStable P) : GaloisDescent.IsStable (stage P)
```

Absolute coefficientwise stability passes to the literal finite-stage
intersection.  Surjectivity of restriction supplies a lift of each finite-level
automorphism; the result is independent of that choice because the ambient map
only sees its restriction.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L367-L378).

### SeparableClosureDescent.exists_finiteGalois_stage

```lean
theorem SeparableClosureDescent.exists_finiteGalois_stage {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [IsGalois k K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) : ∃ (L : FiniteGaloisIntermediateField k K), GaloisDescent.IsStable (stage P) ∧ (stage P).IsFiniteEtale ∧ ∃ (e : TensorProduct (↥L.toIntermediateField) K ↥(stage P) ≃ₐ[K] ↥P), ∀ (z : TensorProduct (↥L.toIntermediateField) K ↥(stage P)), ↑(e z) = (ambientReconstructionMap P) z
```

A finite-etale, absolutely stable embedded algebra is reconstructed from a
stable finite-etale algebra over one finite Galois intermediate field.  Both
equivalences and the stage itself use the literal ambient inclusions.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L388-L413).

### SeparableClosureDescent.scalarExtensionMap

```lean
noncomputable def SeparableClosureDescent.scalarExtensionMap {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] (D : Subalgebra k R) : TensorProduct k K ↥D →ₐ[K] TensorProduct k K R
```

The literal scalar-extension inclusion of a `k`-subalgebra into
`K ⊗[k] R`.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L415-L419).

### SeparableClosureDescent.scalarExtensionMap_tmul

```lean
theorem SeparableClosureDescent.scalarExtensionMap_tmul {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] (D : Subalgebra k R) (a : K) (d : ↥D) : (scalarExtensionMap D) (a ⊗ₜ[k] d) = a ⊗ₜ[k] ↑d
```

The literal scalar-extension inclusion sends `a ⊗ d` to `a ⊗ (d : R)`.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L422-L424).

### SeparableClosureDescent.scalarExtensionMap_injective

```lean
theorem SeparableClosureDescent.scalarExtensionMap_injective {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [IsGalois k K] [CommRing R] [Algebra k R] (D : Subalgebra k R) : Function.Injective ⇑(scalarExtensionMap D)
```

The literal scalar-extension inclusion is injective.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L426-L431).

### SeparableClosureDescent.Package

```lean
structure SeparableClosureDescent.Package {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : Type (max w x)
```

The complete literal output of separable-closure descent.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L441-L454).

### SeparableClosureDescent.Package.mk

```lean
constructor SeparableClosureDescent.Package.mk : {k : Type u} → {K : Type w} → {R : Type x} → [inst : Field k] → [inst_1 : Field K] → [inst_2 : Algebra k K] → [inst_3 : CommRing R] → [inst_4 : Algebra k R] → {P : Subalgebra K (TensorProduct k K R)} → (algebra : Subalgebra k R) → algebra.IsFiniteEtale → (reconstruction : TensorProduct k K ↥algebra ≃ₐ[K] ↥P) → (∀ (z : TensorProduct k K ↥algebra), ↑(reconstruction z) = (SeparableClosureDescent.scalarExtensionMap algebra) z) → (∀ (r : R), r ∈ algebra ↔ Algebra.TensorProduct.includeRight r ∈ P) → SeparableClosureDescent.Package P
```

Generated structure constructor; see the parent structure and its fields.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L441-L454).

### SeparableClosureDescent.Package.algebra

```lean
abbrev SeparableClosureDescent.Package.algebra {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) : Subalgebra k R
```

The reconstructed algebra in the original ambient algebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L444-L444).

### SeparableClosureDescent.Package.isFiniteEtale

```lean
theorem SeparableClosureDescent.Package.isFiniteEtale {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) : self.algebra.IsFiniteEtale
```

The reconstructed subalgebra is finite etale over `k`.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L446-L446).

### SeparableClosureDescent.Package.reconstruction

```lean
abbrev SeparableClosureDescent.Package.reconstruction {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) : TensorProduct k K ↥self.algebra ≃ₐ[K] ↥P
```

Canonical orientation from scalar extension to the given subalgebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L448-L448).

### SeparableClosureDescent.Package.coe_reconstruction

```lean
theorem SeparableClosureDescent.Package.coe_reconstruction {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) (z : TensorProduct k K ↥self.algebra) : ↑(self.reconstruction z) = (scalarExtensionMap self.algebra) z
```

Reconstruction is the literal ambient scalar-extension inclusion.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L450-L450).

### SeparableClosureDescent.Package.mem_algebra

```lean
theorem SeparableClosureDescent.Package.mem_algebra {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) (r : R) : r ∈ self.algebra ↔ Algebra.TensorProduct.includeRight r ∈ P
```

The descended algebra is the honest preimage in `R`.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L453-L453).

### SeparableClosureDescent.scalarExtensionMap_range_of_equiv

```lean
theorem SeparableClosureDescent.scalarExtensionMap_range_of_equiv {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) (D : Subalgebra k R) (e : TensorProduct k K ↥D ≃ₐ[K] ↥P) (he : ∀ (z : TensorProduct k K ↥D), ↑(e z) = (scalarExtensionMap D) z) : (scalarExtensionMap D).range = P
```

An ambient-compatible reconstruction equivalence identifies the literal
range of scalar extension with the given subalgebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L457-L474).

### SeparableClosureDescent.package

```lean
noncomputable def SeparableClosureDescent.package {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [IsSepClosure k K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) : Package P
```

A finite-etale subalgebra embedded after extension to a separable closure,
and stable under every coefficientwise absolute-Galois automorphism, descends
to an honest finite-etale subalgebra of the original ambient algebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L476-L511).

### SeparableClosureDescent.package_range

```lean
theorem SeparableClosureDescent.package_range {k : Type u} {K : Type w} {R : Type x} [Field k] [Field K] [Algebra k K] [IsSepClosure k K] [CommRing R] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) : (scalarExtensionMap (package P hP hEtale).algebra).range = P
```

The separable-closure reconstruction has literal ambient range equal to the
original stable subalgebra.

[Source](../FiniteEtaleAlgebras/SeparableClosureDescent.lean#L513-L519).

## FiniteEtaleAlgebras.PurelyInseparableDescent

### PurelyInseparableDescent.idempotent_mem_range_algebraMap

```lean
theorem PurelyInseparableDescent.idempotent_mem_range_algebraMap (k : Type u) (K : Type v) (R : Type w) [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] [IsPurelyInseparable k K] {e : TensorProduct k R K} (he : IsIdempotentElem e) : e ∈ (algebraMap R (TensorProduct k R K)).range
```

An idempotent of `R ⊗[k] K` belongs to the range of the canonical
`R`-algebra map.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L33-L40).

### PurelyInseparableDescent.idempotent_mem_range_includeRight

```lean
theorem PurelyInseparableDescent.idempotent_mem_range_includeRight (k : Type u) (K : Type v) (R : Type w) [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] [IsPurelyInseparable k K] {e : TensorProduct k K R} (he : IsIdempotentElem e) : e ∈ Set.range ⇑Algebra.TensorProduct.includeRight
```

An idempotent of `K ⊗[k] R` belongs to the range of the canonical
right-factor inclusion of `R`.  This is the factor-reversed form of
`idempotent_mem_range_algebraMap`.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L42-L52).

### PurelyInseparableDescent.Package

```lean
structure PurelyInseparableDescent.Package {k : Type u} {K : Type v} {R : Type w} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] (P : Subalgebra K (TensorProduct k K R)) : Type (max v w)
```

The output of purely inseparable descent for an embedded finite etale
algebra.  The equivalence is oriented from scalar extension to the given
subalgebra, and its underlying ambient map is the literal tensor-product
inclusion.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L59-L73).

### PurelyInseparableDescent.Package.mk

```lean
constructor PurelyInseparableDescent.Package.mk : {k : Type u} → {K : Type v} → {R : Type w} → [inst : Field k] → [inst_1 : Field K] → [inst_2 : CommRing R] → [inst_3 : Algebra k K] → [inst_4 : Algebra k R] → {P : Subalgebra K (TensorProduct k K R)} → (algebra : Subalgebra k R) → algebra.IsFiniteEtale → (reconstruction : TensorProduct k K ↥algebra ≃ₐ[K] ↥P) → (∀ (z : TensorProduct k K ↥algebra), ↑(reconstruction z) = (SeparableClosureDescent.scalarExtensionMap algebra) z) → PurelyInseparableDescent.Package P
```

Generated structure constructor; see the parent structure and its fields.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L59-L73).

### PurelyInseparableDescent.Package.algebra

```lean
abbrev PurelyInseparableDescent.Package.algebra {k : Type u} {K : Type v} {R : Type w} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) : Subalgebra k R
```

The descended finite etale subalgebra of the original ambient algebra.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L65-L65).

### PurelyInseparableDescent.Package.isFiniteEtale

```lean
theorem PurelyInseparableDescent.Package.isFiniteEtale {k : Type u} {K : Type v} {R : Type w} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) : self.algebra.IsFiniteEtale
```

The descended algebra is finite etale over the smaller field.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L67-L67).

### PurelyInseparableDescent.Package.reconstruction

```lean
abbrev PurelyInseparableDescent.Package.reconstruction {k : Type u} {K : Type v} {R : Type w} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) : TensorProduct k K ↥self.algebra ≃ₐ[K] ↥P
```

Reconstruction after extending scalars to the larger field.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L69-L69).

### PurelyInseparableDescent.Package.coe_reconstruction

```lean
theorem PurelyInseparableDescent.Package.coe_reconstruction {k : Type u} {K : Type v} {R : Type w} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] {P : Subalgebra K (TensorProduct k K R)} (self : Package P) (z : TensorProduct k K ↥self.algebra) : ↑(self.reconstruction z) = (SeparableClosureDescent.scalarExtensionMap self.algebra) z
```

Reconstruction is the literal ambient scalar-extension map.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L71-L71).

### PurelyInseparableDescent.package

```lean
noncomputable def PurelyInseparableDescent.package {k : Type u} {K : Type v} {R : Type w} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] [IsPurelyInseparable k K] [IsSepClosed K] (P : Subalgebra K (TensorProduct k K R)) (hP : P.IsFiniteEtale) : Package P
```

A finite etale subalgebra embedded after purely inseparable scalar
extension descends to a finite etale subalgebra of the original ambient
algebra.  Separably closedness of the larger field is used only to split the
finite etale algebra into its complete family of coordinate idempotents.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L75-L233).

### PurelyInseparableDescent.package_range

```lean
theorem PurelyInseparableDescent.package_range {k : Type u} {K : Type v} {R : Type w} [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] [IsPurelyInseparable k K] [IsSepClosed K] (P : Subalgebra K (TensorProduct k K R)) (hP : P.IsFiniteEtale) : (SeparableClosureDescent.scalarExtensionMap (package P hP).algebra).range = P
```

The literal ambient range of the reconstructed scalar extension is the
original embedded subalgebra.

[Source](../FiniteEtaleAlgebras/PurelyInseparableDescent.lean#L235-L240).

## FiniteEtaleAlgebras

No native display entries (aggregate import or private examples).

## Examples.IdempotentSubalgebra

No native display entries (aggregate import or private examples).

## Examples.SeparableClosureDescent

No native display entries (aggregate import or private examples).
