/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FiniteEtaleAlgebras.SeparableClosureDescent
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Idempotents

/-!
# Purely inseparable descent for embedded finite etale algebras

This file proves that scalar extension along a purely inseparable field
extension creates no new idempotents. Both tensor-factor orientations are
provided, with membership stated in the range of the corresponding literal
ambient map. Over a separably closed extension field, these idempotents give a
literal reconstruction of every embedded finite etale subalgebra.
-/

public section

open scoped TensorProduct

universe u v w

namespace PurelyInseparableDescent

variable (k : Type u) (K : Type v) (R : Type w)
variable [Field k] [Field K] [CommRing R]
variable [Algebra k K] [Algebra k R] [IsPurelyInseparable k K]

/-- An idempotent of `R ⊗[k] K` belongs to the range of the canonical
`R`-algebra map. -/
theorem idempotent_mem_range_algebraMap {e : R ⊗[k] K}
    (he : IsIdempotentElem e) :
    e ∈ (algebraMap R (R ⊗[k] K)).range := by
  obtain ⟨n, hn, hmem⟩ :=
    IsPurelyInseparable.exists_pow_mem_range_tensorProduct (k := k) e
  rwa [he.pow_eq hn.ne'] at hmem

/-- An idempotent of `K ⊗[k] R` belongs to the range of the canonical
right-factor inclusion of `R`.  This is the factor-reversed form of
`idempotent_mem_range_algebraMap`. -/
theorem idempotent_mem_range_includeRight {e : K ⊗[k] R}
    (he : IsIdempotentElem e) :
    e ∈ Set.range (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) := by
  let swap : K ⊗[k] R ≃ₐ[k] R ⊗[k] K := Algebra.TensorProduct.comm k K R
  have hswap : IsIdempotentElem (swap e) := he.map swap
  obtain ⟨r, hr⟩ := idempotent_mem_range_algebraMap k K R hswap
  refine ⟨r, swap.injective ?_⟩
  simpa [swap, Algebra.TensorProduct.includeRight_apply] using hr

section Reconstruction

variable {k K R}
variable [IsSepClosed K]

/-- The output of purely inseparable descent for an embedded finite etale
algebra.  The equivalence is oriented from scalar extension to the given
subalgebra, and its underlying ambient map is the literal tensor-product
inclusion. -/
structure Package (P : Subalgebra K (K ⊗[k] R)) where
  /-- The descended finite etale subalgebra of the original ambient algebra. -/
  algebra : Subalgebra k R
  /-- The descended algebra is finite etale over the smaller field. -/
  isFiniteEtale : algebra.IsFiniteEtale
  /-- Reconstruction after extending scalars to the larger field. -/
  reconstruction : K ⊗[k] algebra ≃ₐ[K] P
  /-- Reconstruction is the literal ambient scalar-extension map. -/
  coe_reconstruction (z : K ⊗[k] algebra) :
    ((reconstruction z : P) : K ⊗[k] R) =
      SeparableClosureDescent.scalarExtensionMap algebra z

/-- A finite etale subalgebra embedded after purely inseparable scalar
extension descends to a finite etale subalgebra of the original ambient
algebra.  Separably closedness of the larger field is used only to split the
finite etale algebra into its complete family of coordinate idempotents. -/
noncomputable def package (P : Subalgebra K (K ⊗[k] R))
    (hP : P.IsFiniteEtale) : Package P := by
  classical
  letI : Module.Finite K P := hP.1
  letI : Algebra.Etale K P := hP.2
  letI : IsArtinianRing P := isArtinian_of_tower K inferInstance
  letI : Fintype (PrimeSpectrum P) := Fintype.ofFinite _
  let split : P ≃ₐ[K] PrimeSpectrum P → K :=
    Algebra.FormallyEtale.equivPiOfIsSepClosed K P
  let idem (i : PrimeSpectrum P) : P := split.symm (Pi.single i 1)
  have hidem : CompleteOrthogonalIdempotents idem := by
    change CompleteOrthogonalIdempotents
      (split.symm ∘ fun i : PrimeSpectrum P ↦ Pi.single i 1)
    exact (CompleteOrthogonalIdempotents.single
      (fun _ : PrimeSpectrum P ↦ K)).map split.symm.toRingHom
  have hdesc (i : PrimeSpectrum P) :
      ∃ r : R, Algebra.TensorProduct.includeRight r =
        ((idem i : P) : K ⊗[k] R) := by
    exact idempotent_mem_range_includeRight k K R
      ((hidem.idem i).map P.val)
  choose r hr using hdesc
  let extendCoefficients : (PrimeSpectrum P → k) →ₐ[k] (PrimeSpectrum P → K) :=
    AlgHom.pi fun i ↦
      (Algebra.ofId k K).comp
        (Pi.evalAlgHom k (fun _ : PrimeSpectrum P ↦ k) i)
  let splitBase : (PrimeSpectrum P → k) →ₐ[k] P :=
    (split.symm.toAlgHom.restrictScalars k).comp extendCoefficients
  let linearCombination : (PrimeSpectrum P → k) →ₗ[k] R :=
    Fintype.linearCombination k r
  have hlinearCombination (x : PrimeSpectrum P → k) :
      Algebra.TensorProduct.includeRight (linearCombination x) =
        ((splitBase x : P) : K ⊗[k] R) := by
    calc
      Algebra.TensorProduct.includeRight (linearCombination x) =
          ∑ i, x i • ((idem i : P) : K ⊗[k] R) := by
            simp [linearCombination, Fintype.linearCombination_apply, hr]
      _ = ((∑ i, x i • idem i : P) : K ⊗[k] R) := by simp
      _ = ((splitBase x : P) : K ⊗[k] R) := by
        apply congrArg Subtype.val
        apply split.injective
        ext j
        rw [map_sum, Finset.sum_apply, Fintype.sum_eq_single j]
        · rw [← IsScalarTower.algebraMap_smul K, map_smul]
          simp [splitBase, extendCoefficients, idem]
        · intro i hij
          rw [← IsScalarTower.algebraMap_smul K, map_smul]
          simp [idem, hij]
  have hlinearCombination_one : linearCombination 1 = 1 := by
    apply Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
    rw [hlinearCombination]
    simp only [map_one, Subalgebra.coe_one]
  have hlinearCombination_mul (x y : PrimeSpectrum P → k) :
      linearCombination (x * y) = linearCombination x * linearCombination y := by
    apply Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
    calc
      Algebra.TensorProduct.includeRight (linearCombination (x * y)) =
          ((splitBase (x * y) : P) : K ⊗[k] R) := hlinearCombination (x * y)
      _ = ((splitBase x * splitBase y : P) : K ⊗[k] R) := by rw [map_mul]
      _ = Algebra.TensorProduct.includeRight (linearCombination x) *
          Algebra.TensorProduct.includeRight (linearCombination y) := by
            change ((splitBase x : P) : K ⊗[k] R) *
              ((splitBase y : P) : K ⊗[k] R) = _
            rw [hlinearCombination, hlinearCombination]
      _ = Algebra.TensorProduct.includeRight
          (linearCombination x * linearCombination y) := by rw [map_mul]
  let coefficients : (PrimeSpectrum P → k) →ₐ[k] R :=
    AlgHom.ofLinearMap linearCombination hlinearCombination_one hlinearCombination_mul
  have hcoefficients (x : PrimeSpectrum P → k) :
      Algebra.TensorProduct.includeRight (coefficients x) =
        ((splitBase x : P) : K ⊗[k] R) :=
    hlinearCombination x
  have hcoefficients_injective : Function.Injective coefficients := by
    intro x y hxy
    have hambient := congrArg
      (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R) hxy
    rw [hcoefficients, hcoefficients] at hambient
    have hbase : splitBase x = splitBase y := Subtype.ext hambient
    have hextend : extendCoefficients x = extendCoefficients y := by
      exact split.symm.injective hbase
    ext i
    exact (algebraMap k K).injective (congrFun hextend i)
  let D : Subalgebra k R := coefficients.range
  let coefficientEquiv : (PrimeSpectrum P → k) ≃ₐ[k] D :=
    AlgEquiv.ofInjective coefficients hcoefficients_injective
  have hD : D.IsFiniteEtale := by
    apply Algebra.IsFiniteEtale.of_surjective
      (A := PrimeSpectrum P → k) (B := D) ⟨inferInstance, inferInstance⟩
      coefficientEquiv.toAlgHom coefficientEquiv.surjective
  have hD_mem (d : D) :
      (Algebra.TensorProduct.includeRight (d : R) : K ⊗[k] R) ∈ P := by
    obtain ⟨x, hx⟩ := d.property
    change coefficients x = (d : R) at hx
    rw [← hx, hcoefficients]
    exact (splitBase x).property
  let baseMap : D →ₐ[k] P :=
    (Algebra.TensorProduct.includeRight.comp D.val).codRestrict
      (P.restrictScalars k) hD_mem
  let reconstructionHom : K ⊗[k] D →ₐ[K] P :=
    Algebra.TensorProduct.lift (Algebra.ofId K P) baseMap
      fun _ _ ↦ Commute.all _ _
  have hcoe (z : K ⊗[k] D) :
      ((reconstructionHom z : P) : K ⊗[k] R) =
        SeparableClosureDescent.scalarExtensionMap D z := by
    induction z using TensorProduct.inductionOn with
    | tmul a d =>
      rw [SeparableClosureDescent.scalarExtensionMap_tmul]
      dsimp only [reconstructionHom]
      rw [Algebra.TensorProduct.lift_tmul]
      change (algebraMap K (K ⊗[k] R) a) *
        Algebra.TensorProduct.includeRight (d : R) = a ⊗ₜ[k] (d : R)
      rw [Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      simp
    | add x y hx hy =>
      simpa only [map_add, Subalgebra.coe_add] using congrArg₂ (.+.) hx hy
  have hreconstruction_injective : Function.Injective reconstructionHom := by
    have hscalarExtensionMap_injective :
        Function.Injective (SeparableClosureDescent.scalarExtensionMap (K := K) D) := by
      change Function.Injective (D.val.toLinearMap.baseChange K)
      exact Module.Flat.lTensor_preserves_injective_linearMap D.val.toLinearMap
        Subtype.val_injective
    intro x y hxy
    apply hscalarExtensionMap_injective
    rw [← hcoe, ← hcoe, hxy]
  have hbaseMap_idem (i : PrimeSpectrum P) :
      baseMap (coefficientEquiv (Pi.single i 1)) = idem i := by
    apply Subtype.ext
    change Algebra.TensorProduct.includeRight
        (coefficients (Pi.single i 1)) = ((idem i : P) : K ⊗[k] R)
    rw [hcoefficients]
    apply congrArg Subtype.val
    apply split.injective
    ext j
    by_cases hij : i = j
    · subst j
      simp [splitBase, extendCoefficients, idem]
    · simp [splitBase, extendCoefficients, idem, hij]
  have hreconstruction_surjective : Function.Surjective reconstructionHom := by
    intro p
    let x : PrimeSpectrum P → K := split p
    refine ⟨∑ i, x i ⊗ₜ[k] coefficientEquiv (Pi.single i 1), ?_⟩
    apply split.injective
    ext j
    simpa [reconstructionHom, hbaseMap_idem, idem, x] using
      (congrFun (pi_eq_sum_univ' (split p)) j).symm
  let reconstruction : K ⊗[k] D ≃ₐ[K] P :=
    AlgEquiv.ofBijective reconstructionHom
      ⟨hreconstruction_injective, hreconstruction_surjective⟩
  refine
    { algebra := D
      isFiniteEtale := hD
      reconstruction := reconstruction
      coe_reconstruction := fun z ↦ ?_ }
  exact hcoe z

/-- The literal ambient range of the reconstructed scalar extension is the
original embedded subalgebra. -/
theorem package_range (P : Subalgebra K (K ⊗[k] R)) (hP : P.IsFiniteEtale) :
    (SeparableClosureDescent.scalarExtensionMap (package P hP).algebra).range = P :=
  SeparableClosureDescent.scalarExtensionMap_range_of_equiv P _
    (package P hP).reconstruction (package P hP).coe_reconstruction

end Reconstruction

end PurelyInseparableDescent
