/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import FiniteEtaleAlgebras

/-!
# Finite etale subalgebras containing idempotents

Downstream checks of `Subalgebra.exists_isFiniteEtale_of_isIdempotentElem`,
including ordinary, nonreduced, and zero-algebra ambient rings.
-/

namespace IdempotentSubalgebraExample

universe u v

section General

variable {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]

private theorem general_idempotent (e : A) (he : IsIdempotentElem e) :
    ∃ Q : Subalgebra K A, Q.IsFiniteEtale ∧ e ∈ Q :=
  Subalgebra.exists_isFiniteEtale_of_isIdempotentElem e he

end General

section Ordinary

variable {K : Type u} [Field K]

private theorem product_idempotent :
    ∃ Q : Subalgebra K (K × K), Q.IsFiniteEtale ∧ (1, 0) ∈ Q :=
  Subalgebra.exists_isFiniteEtale_of_isIdempotentElem (1, 0) (by
    simp [IsIdempotentElem])

end Ordinary

section NonreducedAmbient

variable {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]

private theorem nonreduced_ambient (ε : A) (_ : ε ≠ 0) (_ : ε ^ 2 = 0) :
    ∃ Q : Subalgebra K A, Q.IsFiniteEtale ∧ (1 : A) ∈ Q :=
  Subalgebra.exists_isFiniteEtale_of_isIdempotentElem 1 .one

end NonreducedAmbient

section ZeroAlgebra

variable {K : Type u} [Field K]

abbrev ZeroAlgebra := K ⧸ (⊤ : Ideal K)

private theorem zero_algebra_subsingleton : Subsingleton (ZeroAlgebra (K := K)) :=
  inferInstance

private theorem zero_algebra_idempotent : ∃ Q : Subalgebra K (ZeroAlgebra (K := K)),
    Q.IsFiniteEtale ∧ (0 : ZeroAlgebra (K := K)) ∈ Q :=
  Subalgebra.exists_isFiniteEtale_of_isIdempotentElem 0 .zero

end ZeroAlgebra

end IdempotentSubalgebraExample
