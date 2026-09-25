/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import FiniteEtaleAlgebras

/-! A downstream check of the public separable-closure descent orientation. -/

open scoped TensorProduct

namespace SeparableClosureDescentExample

universe u v w x

section GenericTensorAction

variable {k : Type u} {L : Type v} {R : Type x}
  [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R]

private theorem generic_coefficientwise_tmul (σ : L ≃ₐ[k] L) (l : L) (r : R) :
    GaloisDescent.coefficientwise (R := R) σ (l ⊗ₜ[k] r) = σ l ⊗ₜ[k] r :=
  GaloisDescent.coefficientwise_tmul σ l r

private theorem generic_coefficientwise_one (x : L ⊗[k] R) :
    GaloisDescent.coefficientwise (R := R) 1 x = x :=
  GaloisDescent.coefficientwise_one x

private theorem generic_coefficientwise_mul (σ τ : L ≃ₐ[k] L) (x : L ⊗[k] R) :
    GaloisDescent.coefficientwise (R := R) (σ * τ) x =
      GaloisDescent.coefficientwise (R := R) σ
        (GaloisDescent.coefficientwise (R := R) τ x) :=
  GaloisDescent.coefficientwise_mul σ τ x

private theorem generic_coefficientwise_smul (σ : L ≃ₐ[k] L) (l : L) (x : L ⊗[k] R) :
    GaloisDescent.coefficientwise (R := R) σ (l • x) =
      σ l • GaloisDescent.coefficientwise (R := R) σ x :=
  GaloisDescent.coefficientwise_smul σ l x

private theorem generic_mem_fixedSubmodule (x : L ⊗[k] R) :
    x ∈ GaloisDescent.fixedSubmodule (k := k) (L := L) (R := R) ↔
      ∀ σ : L ≃ₐ[k] L, GaloisDescent.coefficientwise (R := R) σ x = x :=
  GaloisDescent.mem_fixedSubmodule

private theorem generic_fixedScalarExtension_tmul (l : L)
    (w : GaloisDescent.fixedSubmodule (k := k) (L := L) (R := R)) :
    GaloisDescent.fixedScalarExtension (k := k) (L := L) (R := R) (l ⊗ₜ[k] w) =
      l • (w : L ⊗[k] R) :=
  GaloisDescent.fixedScalarExtension_tmul l w

private theorem generic_mem_descended (P : Subalgebra L (L ⊗[k] R)) (r : R) :
    r ∈ GaloisDescent.descended P ↔
      (Algebra.TensorProduct.includeRight r : L ⊗[k] R) ∈ P :=
  GaloisDescent.mem_descended

private theorem generic_scalarExtensionMap_tmul (P : Subalgebra L (L ⊗[k] R))
    (l : L) (d : GaloisDescent.descended P) :
    GaloisDescent.scalarExtensionMap P (l ⊗ₜ[k] d) = l ⊗ₜ[k] (d : R) :=
  GaloisDescent.scalarExtensionMap_tmul P l d

private theorem generic_scalarExtensionMap_injective (P : Subalgebra L (L ⊗[k] R)) :
    Function.Injective (GaloisDescent.scalarExtensionMap P) :=
  GaloisDescent.scalarExtensionMap_injective P

private theorem explicit_coefficientwise_tmul (σ : L ≃ₐ[k] L) (l : L) (r : R) :
    GaloisDescent.coefficientwise (R := R) σ (l ⊗ₜ[k] r) = σ l ⊗ₜ[k] r :=
  @GaloisDescent.coefficientwise_tmul k L R
    (inferInstance : Field k) (inferInstance : Field L) (inferInstance : Algebra k L)
    (inferInstance : CommRing R) (inferInstance : Algebra k R) σ l r

private theorem explicit_scalarExtensionMap_injective (P : Subalgebra L (L ⊗[k] R)) :
    Function.Injective (GaloisDescent.scalarExtensionMap P) :=
  @GaloisDescent.scalarExtensionMap_injective k L R
    (inferInstance : Field k) (inferInstance : Field L) (inferInstance : Algebra k L)
    (inferInstance : CommRing R) (inferInstance : Algebra k R) P

end GenericTensorAction

section General

variable {k : Type u} {K : Type w} {R : Type x}
  [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
  [CommRing R] [Algebra k R]

private noncomputable def general_reconstruction (P : Subalgebra K (K ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    K ⊗[k] (SeparableClosureDescent.package P hP hEtale).algebra ≃ₐ[K] P :=
  (SeparableClosureDescent.package P hP hEtale).reconstruction

private theorem general_membership (P : Subalgebra K (K ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) (r : R) :
    r ∈ (SeparableClosureDescent.package P hP hEtale).algebra ↔
      (Algebra.TensorProduct.includeRight r : K ⊗[k] R) ∈ P :=
  (SeparableClosureDescent.package P hP hEtale).mem_algebra r

private theorem general_range (P : Subalgebra K (K ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    (SeparableClosureDescent.scalarExtensionMap
      (SeparableClosureDescent.package P hP hEtale).algebra).range = P :=
  SeparableClosureDescent.package_range P hP hEtale

end General

section IdentityExtension

variable {k : Type u} [Field k] [IsSepClosed k]
  {R : Type x} [CommRing R] [Algebra k R]

private theorem identity_isSepClosure : IsSepClosure k k := inferInstance

private noncomputable def identity_reconstruction (P : Subalgebra k (k ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    k ⊗[k] (SeparableClosureDescent.package P hP hEtale).algebra ≃ₐ[k] P :=
  (SeparableClosureDescent.package P hP hEtale).reconstruction

end IdentityExtension

section AmbientEdgeCases

variable {k : Type u} {K : Type w}
  [Field k] [Field K] [Algebra k K] [IsSepClosure k K]

abbrev ZeroAlgebra := k ⧸ (⊤ : Ideal k)

private theorem zero_algebra_subsingleton : Subsingleton (ZeroAlgebra (k := k)) :=
  inferInstance

private noncomputable def top_zero_algebra_package :
    SeparableClosureDescent.Package
      (⊤ : Subalgebra K (K ⊗[k] ZeroAlgebra (k := k))) := by
  apply SeparableClosureDescent.package ⊤
  · intro σ z hz
    simp
  · exact ⟨inferInstance, inferInstance⟩

private noncomputable def zero_algebra_package
    (P : Subalgebra K (K ⊗[k] ZeroAlgebra (k := k)))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    SeparableClosureDescent.Package P :=
  SeparableClosureDescent.package P hP hEtale

private noncomputable def product_algebra_package
    (P : Subalgebra K (K ⊗[k] (k × k)))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    SeparableClosureDescent.Package P :=
  SeparableClosureDescent.package P hP hEtale

private noncomputable def nonreduced_ambient_package
    {R : Type x} [CommRing R] [Algebra k R]
    (ε : R) (_ : ε ≠ 0) (_ : ε ^ 2 = 0)
    (P : Subalgebra K (K ⊗[k] R))
    (hP : GaloisDescent.IsStable P) (hEtale : P.IsFiniteEtale) :
    SeparableClosureDescent.Package P :=
  SeparableClosureDescent.package P hP hEtale

end AmbientEdgeCases

end SeparableClosureDescentExample
