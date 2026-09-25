/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FiniteEtaleAlgebras.MaximalSubalgebra
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# Finite-Galois semilinear descent

This file reconstructs a subalgebra of `R` from an `L`-subalgebra of
`L ⊗[k] R` stable under coefficientwise `Gal(L/k)`.  The reconstruction is
the honest preimage under `r ↦ 1 ⊗ r`; its scalar extension is identified
literally with the given ambient subalgebra.

The proof formalizes the trace-dual inverse for semilinear descent, including
both inverse identities.  Finiteness and etaleness are descended only after
the included algebra has been reconstructed.  No nontriviality, connectedness,
reducedness, or finiteness hypothesis is imposed on the ambient algebra `R`.
-/

public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- Coefficientwise Galois conjugation on `L ⊗[k] R`. -/
@[expose] noncomputable def coefficientwise (σ : L ≃ₐ[k] L) : L ⊗[k] R →ₐ[k] L ⊗[k] R :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k R)

/-- Unfolds coefficientwise conjugation into the tensor map of `σ` and identity on `R`. -/
add_decl_doc coefficientwise.eq_1

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Coefficientwise conjugation sends `l ⊗ r` to `σ(l) ⊗ r`. -/
@[simp] theorem coefficientwise_tmul (σ : L ≃ₐ[k] L) (l : L) (r : R) :
    coefficientwise (R := R) σ (l ⊗ₜ[k] r) = σ l ⊗ₜ[k] r := rfl

private theorem traceDual_orthogonality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k L) (σ : L ≃ₐ[k] L) :
    (σ = 1 → (∑ i, b i * σ (b.traceDual i)) = 1) ∧
      (σ ≠ 1 → (∑ i, b i * σ (b.traceDual i)) = 0) := by
  classical
  let c : (L ≃ₐ[k] L) → L := fun τ => ∑ i, b i * τ (b.traceDual i)
  have hrepr (x : L) (i : ι) :
      b.repr x i = Algebra.trace k L (b.traceDual i * x) := by
    calc
      b.repr x i = b.traceDual.traceDual.repr x i := by rw [b.traceDual_traceDual]
      _ = Algebra.trace k L (b.traceDual i * x) := by
        simp only [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, mul_comm]
  have hexpand (x : L) : ∑ τ, c τ * τ x = x := by
    simp only [c]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      ∑ i : ι, ∑ τ : L ≃ₐ[k] L, b i * τ (b.traceDual i) * τ x =
          ∑ i : ι, b i * ∑ τ : L ≃ₐ[k] L, τ (b.traceDual i * x) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro τ _
            simp only [map_mul, mul_assoc]
      _ = ∑ i : ι, b i * algebraMap k L (Algebra.trace k L (b.traceDual i * x)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [trace_eq_sum_automorphisms]
      _ = ∑ i : ι, b.repr x i • b i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hrepr]
            simp [Algebra.smul_def, mul_comm]
      _ = x := b.sum_repr x
  let d : (L ≃ₐ[k] L) → L := fun τ => c τ - if τ = 1 then 1 else 0
  let q : (L ≃ₐ[k] L) →₀ L := Finsupp.equivFunOnFinite.symm d
  have hzero (x : L) : ∑ τ, d τ * τ x = 0 := by
    simp only [d, sub_mul, Finset.sum_sub_distrib]
    rw [hexpand]
    simp
  have hli : LinearIndependent L (fun τ : L ≃ₐ[k] L => (τ : L → L)) :=
    LinearIndependent.comp (ι' := L ≃ₐ[k] L)
      (linearIndependent_monoidHom L L) (fun τ => τ)
      (fun x y h => by ext z; exact DFunLike.ext_iff.1 h z)
  have hq : Finsupp.linearCombination L (fun τ : L ≃ₐ[k] L => (τ : L → L)) q = 0 := by
    ext x
    simpa [q, Finsupp.linearCombination, Finsupp.sum_fintype] using hzero x
  have hq0 : q = 0 := (linearIndependent_iff.mp hli) q hq
  have hd : d σ = 0 := by
    have := congrArg (fun z : (L ≃ₐ[k] L) →₀ L => z σ) hq0
    simpa [q] using this
  constructor
  · intro hσ
    simpa [d, hσ, c] using (sub_eq_zero.mp hd)
  · intro hσ
    simpa [d, hσ, c] using (sub_eq_zero.mp hd)

/-- The fixed tensors under coefficientwise `Gal(L/k)` are exactly `1 ⊗ r`. -/
theorem fixed_iff_mem_range_includeRight (x : L ⊗[k] R) :
    (∀ σ : L ≃ₐ[k] L, coefficientwise (R := R) σ x = x) ↔
      x ∈ Set.range (Algebra.TensorProduct.includeRight : R →ₐ[k] L ⊗[k] R) := by
  classical
  let b := Module.Free.chooseBasis k R
  let B := b.baseChange L
  have hcoord (σ : L ≃ₐ[k] L) (z : L ⊗[k] R) (i) :
      B.repr (coefficientwise (R := R) σ z) i = σ (B.repr z i) := by
    induction z with
    | tmul l r =>
        simp only [coefficientwise_tmul, B, Module.Basis.baseChange_repr_tmul]
        simp [Algebra.smul_def]
    | add z₁ z₂ h₁ h₂ => simp_all
  constructor
  · intro hx
    have ha (i) : B.repr x i ∈ Set.range (algebraMap k L) :=
      (IsGalois.mem_range_algebraMap_iff_fixed (B.repr x i)).2 fun σ => by
        rw [← hcoord σ x i, hx]
    let a : Module.Free.ChooseBasisIndex k R → k := fun i => Classical.choose (ha i)
    have ha_spec (i) : algebraMap k L (a i) = B.repr x i := Classical.choose_spec (ha i)
    have ha_zero_out (i) (hi : i ∉ (B.repr x).support) : a i = 0 := by
      apply (algebraMap k L).injective
      rw [ha_spec, Finsupp.notMem_support_iff.mp hi, map_zero]
    let y : Module.Free.ChooseBasisIndex k R →₀ k :=
      Finsupp.onFinset (B.repr x).support a fun i hai => by
        by_contra hi
        exact hai (ha_zero_out i hi)
    let r : R := b.repr.symm y
    refine ⟨r, B.repr.injective ?_⟩
    ext i
    rw [Algebra.TensorProduct.includeRight_apply,
      Module.Basis.baseChange_repr_tmul]
    simpa [r, y, Algebra.smul_def] using ha_spec i
  · rintro ⟨r, rfl⟩ σ
    simp [coefficientwise]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The identity automorphism acts identically on the tensor product. -/
@[simp] theorem coefficientwise_one (x : L ⊗[k] R) :
    coefficientwise (R := R) 1 x = x := by
  induction x with
  | tmul l r => simp [coefficientwise_tmul]
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Coefficientwise conjugation respects the Galois-group multiplication order. -/
theorem coefficientwise_mul (σ τ : L ≃ₐ[k] L) (x : L ⊗[k] R) :
    coefficientwise (R := R) (σ * τ) x =
      coefficientwise (R := R) σ (coefficientwise (R := R) τ x) := by
  induction x with
  | tmul l r => simp [coefficientwise_tmul, AlgEquiv.mul_apply]
  | add x y hx hy => simp [hx, hy]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Coefficientwise conjugation is semilinear for the `L`-module structure. -/
theorem coefficientwise_smul (σ : L ≃ₐ[k] L) (l : L) (x : L ⊗[k] R) :
    coefficientwise (R := R) σ (l • x) =
      σ l • coefficientwise (R := R) σ x := by
  rw [Algebra.smul_def, Algebra.smul_def]
  simp [coefficientwise, Algebra.TensorProduct.algebraMap_apply]

private noncomputable def traceAverage (a : L) (x : L ⊗[k] R) : L ⊗[k] R :=
  ∑ σ : L ≃ₐ[k] L, σ a • coefficientwise (R := R) σ x

omit [IsGalois k L] in
private theorem coefficientwise_traceAverage (τ : L ≃ₐ[k] L) (a : L)
    (x : L ⊗[k] R) :
    coefficientwise (R := R) τ (traceAverage (R := R) a x) =
      traceAverage (R := R) a x := by
  classical
  simp only [traceAverage, map_sum, coefficientwise_smul, ← AlgEquiv.mul_apply,
    ← coefficientwise_mul]
  exact Fintype.sum_bijective (fun σ : L ≃ₐ[k] L => τ * σ)
    (Group.mulLeft_bijective τ) _ _ (fun _ => rfl)

omit [IsGalois k L] in
private theorem traceAverage_add (a : L) (x y : L ⊗[k] R) :
    traceAverage (R := R) a (x + y) =
      traceAverage (R := R) a x + traceAverage (R := R) a y := by
  classical
  simp [traceAverage, smul_add, Finset.sum_add_distrib]

/-- The `k`-submodule of tensors fixed by every coefficientwise conjugation. -/
def fixedSubmodule : Submodule k (L ⊗[k] R) where
  carrier := {x | ∀ σ : L ≃ₐ[k] L, coefficientwise (R := R) σ x = x}
  zero_mem' := by simp
  add_mem' hx hy := by intro σ; simp [hx σ, hy σ]
  smul_mem' a x hx := by intro σ; simpa using congrArg (a • ·) (hx σ)

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Membership in the fixed submodule is pointwise Galois fixedness. -/
@[simp] theorem mem_fixedSubmodule {x : L ⊗[k] R} :
    x ∈ fixedSubmodule (k := k) (L := L) (R := R) ↔
      ∀ σ : L ≃ₐ[k] L, coefficientwise (R := R) σ x = x := Iff.rfl

/-- The canonical scalar-extension map from the fixed submodule. -/
@[expose] noncomputable def fixedScalarExtension :
    L ⊗[k] fixedSubmodule (k := k) (L := L) (R := R) →ₗ[L] L ⊗[k] R :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun l =>
        { toFun := fun w => l • (w : L ⊗[k] R)
          map_add' := fun x y => by simp
          map_smul' := fun a x => smul_comm l a (x : L ⊗[k] R) }
      map_add' := fun x y => by ext; simp [add_smul]
      map_smul' := fun a x => by ext; simp [mul_smul] }

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The canonical fixed-point scalar-extension map on pure tensors. -/
@[simp] theorem fixedScalarExtension_tmul (l : L)
    (w : fixedSubmodule (k := k) (L := L) (R := R)) :
    fixedScalarExtension (k := k) (L := L) (R := R) (l ⊗ₜ[k] w) = l • (w : L ⊗[k] R) :=
  rfl

private noncomputable def traceDualInverse (x : L ⊗[k] R) :
    L ⊗[k] fixedSubmodule (k := k) (L := L) (R := R) :=
  let b := Module.finBasis k L
  ∑ i, b i ⊗ₜ[k] ⟨traceAverage (R := R) (b.traceDual i) x,
    fun τ => coefficientwise_traceAverage τ _ _⟩

private theorem traceAverage_smul_fixed (a l : L)
    (w : fixedSubmodule (k := k) (L := L) (R := R)) :
    traceAverage (R := R) a (l • (w : L ⊗[k] R)) =
      algebraMap k L (Algebra.trace k L (a * l)) • (w : L ⊗[k] R) := by
  classical
  simp only [traceAverage, coefficientwise_smul]
  simp only [smul_smul, ← map_mul]
  calc
    ∑ σ : L ≃ₐ[k] L,
        σ (a * l) • coefficientwise (R := R) σ (w : L ⊗[k] R) =
        ∑ σ : L ≃ₐ[k] L, σ (a * l) • (w : L ⊗[k] R) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [w.property σ]
    _ = algebraMap k L (Algebra.trace k L (a * l)) • (w : L ⊗[k] R) := by
      rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms]

private theorem sum_smul_traceAverage_traceDual {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    (b : Module.Basis ι k L) (x : L ⊗[k] R) :
    ∑ i, b i • traceAverage (R := R) (b.traceDual i) x = x := by
  classical
  simp only [traceAverage]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ σ : L ≃ₐ[k] L, ∑ i : ι,
        b i • (σ (b.traceDual i) • coefficientwise (R := R) σ x) =
        ∑ σ : L ≃ₐ[k] L, (∑ i : ι, b i * σ (b.traceDual i)) •
          coefficientwise (R := R) σ x := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.sum_smul]
          apply Finset.sum_congr rfl
          intro i _
          simp [smul_smul]
    _ = x := by
      rw [Finset.sum_eq_single (1 : L ≃ₐ[k] L)]
      · rw [(traceDual_orthogonality b 1).1 rfl]
        simp
      · intro σ _ hσ
        rw [(traceDual_orthogonality b σ).2 hσ]
        simp
      · simp

private theorem fixedScalarExtension_traceDualInverse (x : L ⊗[k] R) :
    fixedScalarExtension (k := k) (L := L) (R := R)
      (traceDualInverse (k := k) (L := L) (R := R) x) = x := by
  classical
  simp [traceDualInverse, sum_smul_traceAverage_traceDual]

private theorem traceDualInverse_fixedScalarExtension_tmul (l : L)
    (w : fixedSubmodule (k := k) (L := L) (R := R)) :
    traceDualInverse (k := k) (L := L) (R := R)
      (fixedScalarExtension (k := k) (L := L) (R := R) (l ⊗ₜ[k] w)) = l ⊗ₜ[k] w := by
  classical
  let b := Module.finBasis k L
  have hrepr (i) : b.repr l i = Algebra.trace k L (b.traceDual i * l) := by
    calc
      b.repr l i = b.traceDual.traceDual.repr l i := by rw [b.traceDual_traceDual]
      _ = Algebra.trace k L (b.traceDual i * l) := by
        simp only [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, mul_comm]
  have hexpand : ∑ i, Algebra.trace k L (b.traceDual i * l) • b i = l := by
    simpa only [← hrepr] using b.sum_repr l
  simp only [fixedScalarExtension_tmul, traceDualInverse]
  calc
    _ = ∑ i, b i ⊗ₜ[k] (Algebra.trace k L (b.traceDual i * l) • w) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply Subtype.ext
      simpa [Algebra.smul_def] using
        traceAverage_smul_fixed (R := R) (b.traceDual i) l w
    _ = l ⊗ₜ[k] w := by
      simp_rw [TensorProduct.tmul_smul]
      change (∑ i, (Algebra.trace k L (b.traceDual i * l) • b i) ⊗ₜ[k] w) =
        l ⊗ₜ[k] w
      rw [← TensorProduct.sum_tmul Finset.univ
        (fun i => Algebra.trace k L (b.traceDual i * l) • b i) w, hexpand]

private theorem traceDualInverse_add (x y : L ⊗[k] R) :
    traceDualInverse (k := k) (L := L) (R := R) (x + y) =
      traceDualInverse (k := k) (L := L) (R := R) x +
        traceDualInverse (k := k) (L := L) (R := R) y := by
  classical
  simp only [traceDualInverse]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← TensorProduct.tmul_add]
  congr 1
  apply Subtype.ext
  exact traceAverage_add _ _ _

private theorem traceDualInverse_fixedScalarExtension
    (z : L ⊗[k] fixedSubmodule (k := k) (L := L) (R := R)) :
    traceDualInverse (k := k) (L := L) (R := R)
      (fixedScalarExtension (k := k) (L := L) (R := R) z) = z := by
  induction z with
  | tmul l w => exact traceDualInverse_fixedScalarExtension_tmul l w
  | add x y hx hy => rw [map_add, traceDualInverse_add, hx, hy]

/-- Semilinear descent for the coefficientwise action on a tensor product.

The inverse is the trace-dual averaging formula; in particular, this equivalence
does not rely on an abstract effective-descent result. -/
noncomputable def fixedScalarExtensionEquiv :
    L ⊗[k] fixedSubmodule (k := k) (L := L) (R := R) ≃ₗ[L] L ⊗[k] R :=
  LinearEquiv.ofBijective (fixedScalarExtension (k := k) (L := L) (R := R))
    ⟨fun x y h => by
        simpa only [traceDualInverse_fixedScalarExtension] using congrArg
          (traceDualInverse (k := k) (L := L) (R := R)) h,
      fun x => ⟨traceDualInverse (k := k) (L := L) (R := R) x,
        fixedScalarExtension_traceDualInverse x⟩⟩

/-- A subalgebra is stable under coefficientwise Galois conjugation. -/
@[expose] def IsStable (P : Subalgebra L (L ⊗[k] R)) : Prop :=
  ∀ (σ : L ≃ₐ[k] L) ⦃x : L ⊗[k] R⦄,
    x ∈ P → coefficientwise (R := R) σ x ∈ P

/-- The honest preimage in the original algebra of a scalar-extended subalgebra. -/
def descended (P : Subalgebra L (L ⊗[k] R)) : Subalgebra k R :=
  (P.restrictScalars k).comap Algebra.TensorProduct.includeRight

omit [FiniteDimensional k L] [IsGalois k L] in
/-- An element belongs to the descended algebra exactly when its image `1 ⊗ r`
belongs to the given subalgebra. -/
@[simp] theorem mem_descended {P : Subalgebra L (L ⊗[k] R)} {r : R} :
    r ∈ descended P ↔
      (Algebra.TensorProduct.includeRight r : L ⊗[k] R) ∈ P := by
  simp [descended]

/-- The scalar extension of the honest preimage is literally the given stable
subalgebra inside `L ⊗[k] R`. -/
theorem baseChange_descended_eq (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) : (descended P).baseChange L = P := by
  classical
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    induction z with
    | tmul l d =>
        change l ⊗ₜ[k] (d : R) ∈ P
        simpa [Algebra.smul_def] using P.smul_mem d.property l
    | add x y hx hy => simpa only [map_add] using P.add_mem hx hy
  · intro x hx
    let b := Module.finBasis k L
    rw [← sum_smul_traceAverage_traceDual (R := R) b x]
    apply Subalgebra.sum_mem
    intro i _
    refine ((descended P).baseChange L).smul_mem ?_ (b i)
    have hTP : traceAverage (R := R) (b.traceDual i) x ∈ P := by
      apply Subalgebra.sum_mem
      intro σ _
      exact P.smul_mem (hP σ hx) _
    have hfixed : ∀ τ : L ≃ₐ[k] L,
        coefficientwise (R := R) τ (traceAverage (R := R) (b.traceDual i) x) =
          traceAverage (R := R) (b.traceDual i) x := fun τ =>
      coefficientwise_traceAverage τ _ _
    obtain ⟨r, hr⟩ := (fixed_iff_mem_range_includeRight
      (R := R) (traceAverage (R := R) (b.traceDual i) x)).mp hfixed
    have hrD : r ∈ descended P := by
      rw [mem_descended, hr]
      exact hTP
    rw [← hr]
    exact Subalgebra.tmul_mem_baseChange hrD 1

/-- Scalar extension of the inclusion of the descended subalgebra. -/
@[expose] noncomputable def scalarExtensionMap (P : Subalgebra L (L ⊗[k] R)) :
    L ⊗[k] descended P →ₐ[L] L ⊗[k] R :=
  Algebra.TensorProduct.map (AlgHom.id L L) (descended P).val

omit [FiniteDimensional k L] [IsGalois k L] in
/-- The scalar-extension inclusion sends `l ⊗ d` to the same pure tensor in the
ambient algebra. -/
@[simp] theorem scalarExtensionMap_tmul (P : Subalgebra L (L ⊗[k] R))
    (l : L) (d : descended P) :
    scalarExtensionMap P (l ⊗ₜ[k] d) = l ⊗ₜ[k] (d : R) := rfl

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Scalar extension preserves the injectivity of the descended-algebra
inclusion. -/
theorem scalarExtensionMap_injective (P : Subalgebra L (L ⊗[k] R)) :
    Function.Injective (scalarExtensionMap P) := by
  change Function.Injective ((descended P).val.toLinearMap.baseChange L)
  exact Module.Flat.lTensor_preserves_injective_linearMap
    (descended P).val.toLinearMap Subtype.val_injective

/-- The reconstructed scalar extension, in the orientation from the descended
algebra to the given stable subalgebra. -/
@[expose] noncomputable def reconstructionEquiv (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) : L ⊗[k] descended P ≃ₐ[L] P :=
  (AlgEquiv.ofInjective (scalarExtensionMap P) (scalarExtensionMap_injective P)).trans
    (Subalgebra.equivOfEq _ _ (baseChange_descended_eq P hP))

/-- After coercion to the ambient tensor product, reconstruction is the literal
scalar-extension inclusion. -/
@[simp] theorem coe_reconstructionEquiv_apply (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) (z : L ⊗[k] descended P) :
    ((reconstructionEquiv P hP z : P) : L ⊗[k] R) = scalarExtensionMap P z := rfl

/-- Reconstruction has the expected literal ambient value on pure tensors. -/
@[simp] theorem reconstructionEquiv_tmul (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) (l : L) (d : descended P) :
    ((reconstructionEquiv P hP (l ⊗ₜ[k] d) : P) : L ⊗[k] R) =
      l ⊗ₜ[k] (d : R) := rfl

/-- The range of the scalar-extension inclusion is literally the original stable
subalgebra. -/
theorem scalarExtensionMap_range (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) : (scalarExtensionMap P).range = P :=
  baseChange_descended_eq P hP

/-- A finite-etale stable subalgebra descends to a finite-etale subalgebra of the
original algebra.  Finiteness and etaleness are descended only after the literal
reconstruction equivalence has been established. -/
theorem descended_isFiniteEtale (P : Subalgebra L (L ⊗[k] R))
    (hP : IsStable P) (hEtale : P.IsFiniteEtale) : (descended P).IsFiniteEtale := by
  let e := reconstructionEquiv P hP
  let : Module.Finite L P := hEtale.1
  let : Algebra.Etale L P := hEtale.2
  let : Module.Finite L (L ⊗[k] descended P) :=
    (Module.Finite.equiv_iff e.toLinearEquiv).2 inferInstance
  let : Algebra.Etale L (L ⊗[k] descended P) := Algebra.Etale.of_equiv e.symm
  exact ⟨Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L,
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L⟩

end GaloisDescent
