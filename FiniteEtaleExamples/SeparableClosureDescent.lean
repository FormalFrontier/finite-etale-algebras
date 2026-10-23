/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FiniteEtaleAlgebras
import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descent of the scalar line in the dual numbers

The bottom subalgebra of the scalar extension of `TrivSqZeroExt k k` is stable
under coefficientwise Galois conjugation. The selected separable-closure descent
package reconstructs exactly the bottom subalgebra, even though the ambient dual
numbers have the nonzero square-zero element `TrivSqZeroExt.inr 1`.

The scalar-line identification uses the standard augmentation and tensor-product
maps from Mathlib, together with injectivity of the finite-stage base-change map.
-/

public section

open scoped TensorProduct

namespace SeparableClosureDescentExample

universe u w

/-- The selected descent package for the scalar line in the dual numbers has
bottom algebra, the ambient reconstruction map, preimage membership, and the
expected scalar-extension range. No stability hypothesis is supplied by the caller. -/
theorem standard_dual_bot_package
    {k : Type u} {K : Type w} [Field k] [Field K]
    [Algebra k K] [IsSepClosure k K] :
    let R := TrivSqZeroExt k k
    let P : Subalgebra K (K ⊗[k] R) := ⊥
    ∃ hP : GaloisDescent.IsStable P,
      let S := SeparableClosureDescent.package P hP
        (Subalgebra.isFiniteEtale_bot (K := K) (R := K ⊗[k] R))
      S.algebra = (⊥ : Subalgebra k R) ∧
      (∀ z : K ⊗[k] S.algebra,
        ((S.reconstruction z : P) : K ⊗[k] R) =
          SeparableClosureDescent.scalarExtensionMap S.algebra z) ∧
      (∀ r : R, r ∈ S.algebra ↔
        (Algebra.TensorProduct.includeRight r : K ⊗[k] R) ∈ P) ∧
      (SeparableClosureDescent.scalarExtensionMap S.algebra).range = P := by
  let R := TrivSqZeroExt k k
  let P : Subalgebra K (K ⊗[k] R) := ⊥
  have hP : GaloisDescent.IsStable P := by
    intro σ x hx
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hx
    rw [Algebra.algebraMap_eq_smul_one, GaloisDescent.coefficientwise_smul,
      map_one, ← Algebra.algebraMap_eq_smul_one]
    exact P.algebraMap_mem (σ c)
  refine ⟨hP, ?_⟩
  let S := SeparableClosureDescent.package P hP
    (Subalgebra.isFiniteEtale_bot (K := K) (R := K ⊗[k] R))
  refine ⟨?_, S.coe_reconstruction, S.mem_algebra,
    SeparableClosureDescent.package_range P hP _⟩
  apply le_antisymm ?_ bot_le
  intro r hr
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp ((S.mem_algebra r).mp hr)
  let π : R →ₐ[k] k := TrivSqZeroExt.fstHom k k k
  let aug : K ⊗[k] R →ₐ[K] K :=
    (Algebra.TensorProduct.rid k K K).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id K K) π)
  have hcoeff : c = algebraMap k K (π r) := by
    calc
      c = aug (algebraMap K (K ⊗[k] R) c) := by
        simpa using (aug.commutes c).symm
      _ = aug (Algebra.TensorProduct.includeRight r) := congrArg aug hc
      _ = algebraMap k K (π r) := by simp [aug, Algebra.smul_def]
  have hscalar : (Algebra.TensorProduct.includeRight r : K ⊗[k] R) =
      Algebra.TensorProduct.includeRight (algebraMap k R (π r)) := by
    calc
      _ = algebraMap K (K ⊗[k] R) c := hc.symm
      _ = algebraMap K (K ⊗[k] R) (algebraMap k K (π r)) := congrArg _ hcoeff
      _ = algebraMap k (K ⊗[k] R) (π r) :=
        (IsScalarTower.algebraMap_apply k K (K ⊗[k] R) (π r)).symm
      _ = _ := (Algebra.TensorProduct.includeRight : R →ₐ[k] K ⊗[k] R).commutes _ |>.symm
  have hbase : (1 ⊗ₜ[k] r : k ⊗[k] R) =
      1 ⊗ₜ[k] (algebraMap k R (π r)) := by
    apply SeparableClosureDescent.extensionMap_injective (k := k) (L := k) (K := K)
    simpa only [SeparableClosureDescent.extensionMap_tmul, map_one,
      Algebra.TensorProduct.includeRight_apply] using hscalar
  have hrScalar : r = algebraMap k R (π r) := by
    simpa only [Algebra.TensorProduct.lid_tmul, one_smul] using
      congrArg (Algebra.TensorProduct.lid k R) hbase
  exact Algebra.mem_bot.mpr ⟨π r, hrScalar.symm⟩

example {k : Type u} [Field k] :
    let P : Subalgebra k (k ⊗[k] Polynomial k) := ⊤
    ∃ e : k ⊗[k] SeparableClosureDescent.stage (k := k) (L := k) P ≃ₐ[k] P,
      ∀ z : k ⊗[k] SeparableClosureDescent.stage (k := k) (L := k) P,
        ((e z : P) : k ⊗[k] Polynomial k) =
          SeparableClosureDescent.ambientReconstructionMap (k := k) (L := k) P z := by
  let P : Subalgebra k (k ⊗[k] Polynomial k) := ⊤
  let b : Module.Basis ℕ k P :=
    (Polynomial.basisMonomials k).map
      ((Algebra.TensorProduct.lid k (Polynomial k)).symm.toLinearEquiv.trans
        (Subalgebra.topEquiv : P ≃ₐ[k] k ⊗[k] Polynomial k).symm.toLinearEquiv)
  have hb (n : ℕ) :
      (b n : k ⊗[k] Polynomial k) ∈
        (SeparableClosureDescent.extensionMap
          (k := k) (L := k) (K := k) (R := Polynomial k)).range := by
    refine ⟨(1 : k) ⊗ₜ[k] (Polynomial.basisMonomials k) n, ?_⟩
    change _ = (Algebra.TensorProduct.lid k (Polynomial k)).symm
      ((Polynomial.basisMonomials k) n)
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_one,
      Algebra.TensorProduct.lid_symm_apply] using
      (SeparableClosureDescent.extensionMap_tmul
        (k := k) (L := k) (K := k) (R := Polynomial k)
        (1 : k) ((Polynomial.basisMonomials k) n))
  exact ⟨SeparableClosureDescent.reconstructionEquivOfBasis P b hb,
    SeparableClosureDescent.coe_reconstructionEquivOfBasis_apply P b hb⟩

end SeparableClosureDescentExample
