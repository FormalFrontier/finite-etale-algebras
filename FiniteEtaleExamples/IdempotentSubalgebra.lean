/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FiniteEtaleAlgebras.MaximalSubalgebra
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# An idempotent in a nonreduced algebra

The product of the standard trivial square-zero extension of a field with the
field itself has both a nonzero square-zero element and a nontrivial idempotent.
The idempotent belongs to a finite etale subalgebra by
`Subalgebra.exists_isFiniteEtale_of_isIdempotentElem`, despite the nonreduced
ambient algebra. The finite etale subalgebra is not required to contain the
nilpotent element. The ambient model and its square-zero identities use
mathlib's `TrivSqZeroExt` API.
-/

@[expose] public section

namespace IdempotentSubalgebraExample

universe u

/-- Over every field, the product of the trivial square-zero extension with the
field is genuinely nonreduced, and its idempotent `(1, 0)` is neither zero nor
one. This idempotent belongs to a finite etale subalgebra. The square-zero
witness is `(TrivSqZeroExt.inr 1, 0)`, with no hypothesis on the characteristic
of the field. -/
theorem standard_nonreduced_idempotent {k : Type u} [Field k] :
    let B := TrivSqZeroExt k k × k
    let η : B := (TrivSqZeroExt.inr (1 : k), 0)
    let e : B := (1, 0)
    η ≠ 0 ∧ η ^ 2 = 0 ∧ ¬ IsReduced B ∧
      IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 ∧
      ∃ Q : Subalgebra k B, Q.IsFiniteEtale ∧ e ∈ Q := by
  let B := TrivSqZeroExt k k × k
  let η : B := (TrivSqZeroExt.inr (1 : k), 0)
  let e : B := (1, 0)
  have hη : η ≠ 0 := by
    intro h
    have h10 : (1 : k) = 0 := by
      simpa [η] using congrArg (fun z : B ↦ z.1.snd) h
    exact one_ne_zero h10
  have hηsq : η ^ 2 = 0 := by
    rw [pow_two]
    apply Prod.ext
    · change (TrivSqZeroExt.inr (1 : k) : TrivSqZeroExt k k) *
        TrivSqZeroExt.inr (1 : k) = 0
      exact TrivSqZeroExt.inr_mul_inr k (1 : k) 1
    · change (0 : k) * 0 = 0
      exact mul_zero _
  have hB : ¬ IsReduced B := by
    intro h
    let : IsReduced B := h
    exact hη (IsReduced.eq_zero η ⟨2, hηsq⟩)
  have he : IsIdempotentElem e := by
    change e * e = e
    apply Prod.ext
    · change (1 : TrivSqZeroExt k k) * 1 = 1
      exact one_mul _
    · change (0 : k) * 0 = 0
      exact mul_zero _
  have he0 : e ≠ 0 := by
    intro h
    have h10 : (1 : TrivSqZeroExt k k) = 0 :=
      congrArg (fun z : B ↦ z.1) h
    exact one_ne_zero h10
  have he1 : e ≠ 1 := by
    intro h
    have h01 : (0 : k) = 1 := congrArg (fun z : B ↦ z.2) h
    exact zero_ne_one h01
  exact ⟨hη, hηsq, hB, he, he0, he1,
    Subalgebra.exists_isFiniteEtale_of_isIdempotentElem e he⟩

end IdempotentSubalgebraExample
