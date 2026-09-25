/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Maximal finite etale subalgebras

This file proves that finite etale subalgebras of a commutative algebra over a
field are closed under binary suprema. As an application, any uniform bound on
their dimensions yields a greatest finite etale subalgebra.

The ambient algebra is not assumed finite-dimensional, reduced, or nontrivial.
In particular, the statements include the zero algebra.
-/

public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- A finite etale algebra, expressed as the conjunction of the two existing
mathlib predicates. -/
@[expose] def IsFiniteEtale (K : Type u) (A : Type v) [CommRing K] [CommRing A]
    [Algebra K A] : Prop :=
  Module.Finite K A ∧ Algebra.Etale K A

namespace IsFiniteEtale

variable {K : Type u} {A : Type v} {B : Type w} [Field K]
  [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- A surjective image of a finite etale algebra over a field is finite etale. -/
theorem of_surjective (hA : IsFiniteEtale K A) (f : A →ₐ[K] B)
    (hf : Function.Surjective f) : IsFiniteEtale K B := by
  let : Module.Finite K A := hA.1
  let : Algebra.Etale K A := hA.2
  let : Module.Finite K B := Module.Finite.of_surjective f.toLinearMap hf
  let : Algebra.FormallyUnramified K B :=
    Algebra.FormallyUnramified.of_surjective f hf
  let : Algebra.FormallyEtale K B :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field K B
  let : Algebra.Etale K B :=
    { finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  exact ⟨inferInstance, inferInstance⟩

end IsFiniteEtale

end Algebra

namespace Subalgebra

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]

/-- A subalgebra is finite etale when its induced algebra structure is finite
and etale. -/
abbrev IsFiniteEtale (A : Subalgebra K R) : Prop :=
  Algebra.IsFiniteEtale K A

/-- The scalar subalgebra is finite etale, including when the ambient algebra
is the zero ring. -/
theorem isFiniteEtale_bot : IsFiniteEtale (⊥ : Subalgebra K R) := by
  apply Algebra.IsFiniteEtale.of_surjective
    (A := K) (B := ↥(⊥ : Subalgebra K R)) ⟨inferInstance, inferInstance⟩
    (Algebra.ofId K (⊥ : Subalgebra K R))
  rintro ⟨x, hx⟩
  obtain ⟨y, hy⟩ := Algebra.mem_bot.mp hx
  exact ⟨y, Subtype.ext hy⟩

/-- Every idempotent of a commutative algebra over a field belongs to a finite
etale subalgebra. No finiteness, reducedness, or nontriviality assumption is
made on the ambient algebra.

The subalgebra is the range of the map from the split finite etale algebra
`Fin 2 → K` determined by the complementary idempotents `e` and `1 - e`. -/
theorem exists_isFiniteEtale_of_isIdempotentElem (e : R)
    (he : IsIdempotentElem e) :
    ∃ Q : Subalgebra K R, Q.IsFiniteEtale ∧ e ∈ Q := by
  let f : (Fin 2 → K) →ₐ[K] R :=
    { toFun := fun x ↦ algebraMap K R (x 0) * e +
          algebraMap K R (x 1) * (1 - e)
      map_one' := by
        change algebraMap K R 1 * e + algebraMap K R 1 * (1 - e) = 1
        simp
      map_mul' := fun x y ↦ by
        change algebraMap K R (x 0 * y 0) * e +
            algebraMap K R (x 1 * y 1) * (1 - e) =
          (algebraMap K R (x 0) * e + algebraMap K R (x 1) * (1 - e)) *
            (algebraMap K R (y 0) * e + algebraMap K R (y 1) * (1 - e))
        simp only [map_mul]
        linear_combination
          -((algebraMap K R (x 0) - algebraMap K R (x 1)) *
            (algebraMap K R (y 0) - algebraMap K R (y 1))) * he.eq
      map_zero' := by simp
      map_add' := fun x y ↦ by
        change algebraMap K R (x 0 + y 0) * e +
            algebraMap K R (x 1 + y 1) * (1 - e) = _
        simp only [map_add, add_mul]
        abel
      commutes' := fun a ↦ by
        change algebraMap K R a * e + algebraMap K R a * (1 - e) =
          algebraMap K R a
        rw [← mul_add, add_sub_cancel, mul_one] }
  let Q := f.range
  have hQ : Q.IsFiniteEtale :=
    Algebra.IsFiniteEtale.of_surjective (A := Fin 2 → K) (B := Q)
      ⟨inferInstance, inferInstance⟩ f.rangeRestrict
      (AlgHom.rangeRestrict_surjective f)
  refine ⟨Q, hQ, ?_⟩
  refine ⟨Pi.single 0 1, ?_⟩
  change algebraMap K R 1 * e + algebraMap K R 0 * (1 - e) = e
  simp

namespace IsFiniteEtale

variable {A B : Subalgebra K R}

/-- The supremum of two finite etale subalgebras is finite etale. -/
theorem sup (hA : A.IsFiniteEtale) (hB : B.IsFiniteEtale) :
    (A ⊔ B).IsFiniteEtale := by
  let : Module.Finite K A := hA.1
  let : Algebra.Etale K A := hA.2
  let : Module.Finite K B := hB.1
  let : Algebra.Etale K B := hB.2
  have : Algebra.Etale A (A ⊗[K] B) := inferInstance
  have : Algebra.Etale K (A ⊗[K] B) :=
    Algebra.Etale.comp K A (A ⊗[K] B)
  apply Algebra.IsFiniteEtale.of_surjective
    (A := A ⊗[K] B) (B := ↥(A ⊔ B)) ⟨inferInstance, inferInstance⟩
    (Subalgebra.mulMap' A B) (Subalgebra.mulMap'_surjective A B)

end IsFiniteEtale

/-- If the dimensions of the finite etale subalgebras of `R` are uniformly
bounded, then `R` has a greatest finite etale subalgebra. -/
theorem exists_greatest_isFiniteEtale_of_finrank_le (N : ℕ)
    (hbound : ∀ A : Subalgebra K R, A.IsFiniteEtale → Module.finrank K A ≤ N) :
    ∃ A : Subalgebra K R, A.IsFiniteEtale ∧
      ∀ B : Subalgebra K R, B.IsFiniteEtale → B ≤ A := by
  let ranks : Set ℕ :=
    {n | ∃ A : Subalgebra K R, A.IsFiniteEtale ∧ Module.finrank K A = n}
  have hranks_nonempty : ranks.Nonempty := by
    exact ⟨Module.finrank K (⊥ : Subalgebra K R), ⊥, isFiniteEtale_bot, rfl⟩
  have hranks_bdd : BddAbove ranks := by
    refine ⟨N, ?_⟩
    rintro n ⟨A, hA, rfl⟩
    exact hbound A hA
  obtain ⟨n, hn_mem, hn_max⟩ :=
    hranks_bdd.exists_isGreatest_of_nonempty hranks_nonempty
  obtain ⟨A, hA, rfl⟩ := hn_mem
  refine ⟨A, hA, fun B hB ↦ ?_⟩
  have hsup : (A ⊔ B).IsFiniteEtale := hA.sup hB
  let : Module.Finite K ↥(A ⊔ B) := hsup.1
  have hfinrank : Module.finrank K ↥(A ⊔ B) ≤ Module.finrank K A :=
    hn_max ⟨(A ⊔ B : Subalgebra K R), hsup, rfl⟩
  have hA_sup : A = (A ⊔ B : Subalgebra K R) :=
    Subalgebra.eq_of_le_of_finrank_le le_sup_left hfinrank
  rw [hA_sup]
  exact le_sup_right

end Subalgebra
