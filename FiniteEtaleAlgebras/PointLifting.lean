/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib

/-!
# Lifting a point from an idempotent component

`Algebra.exists_lift_of_lifted_idempotent` lifts a specified residue point of a flat
localization of a finite algebra, conditional on a chosen lifted eigenidempotent.

The proof applies Nakayama's lemma to the finite cokernel of the scalar map onto the
selected component, before using flatness. The original-action linear section is
`σ(p(a)) = β(ε) * β(a)`; it is not a unital ring homomorphism. Flatness of the component
then gives `J ⊓ P = J * P` separately for each principal ideal `P` contained in the
scalar kernel `J`. A second application of Nakayama proves that kernel is zero.

## References

The proof uses Mathlib's quotient-kernel algebra equivalence, flat-retract theorem,
tensor-injectivity criterion for ideal products, and submodule form of Nakayama's lemma.
-/

@[expose] public section

open Polynomial
open scoped BigOperators TensorProduct

universe u v w t

private theorem scalar_surjective_of_eigenidempotent
    {R : Type u} {U : Type v} [CommRing R] [CommRing U] [Algebra R U]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    [Module.Finite R U]
    (τ : U →ₐ[R] R ⧸ I)
    (ebar : U ⧸ I.map (algebraMap R U))
    (heigen : ∀ (a : U) (r : R),
      Ideal.Quotient.mk I r = τ a →
      ebar * (Ideal.Quotient.mk (I.map (algebraMap R U)) a -
        Ideal.Quotient.mk (I.map (algebraMap R U)) (algebraMap R U r)) = 0)
    (ε : U) (hεbar : Ideal.Quotient.mk (I.map (algebraMap R U)) ε = ebar) :
    Function.Surjective
      (algebraMap R (U ⧸ Ideal.span ({1 - ε} : Set U))) := by
  classical
  let K : Ideal U := Ideal.span ({1 - ε} : Set U)
  let V := U ⧸ K
  let p : U →ₐ[R] V := Ideal.Quotient.mkₐ R K
  let κ : R →ₗ[R] V := (Algebra.ofId R V).toLinearMap
  have hκapply (r : R) : κ r = algebraMap R V r :=
    congrArg (fun f : R →+* V => f r)
      (Algebra.toRingHom_ofId (R := R) (A := V))
  have hpSurj : Function.Surjective p := Ideal.Quotient.mkₐ_surjective (R₁ := R) K
  let : Module.Finite R V :=
    Module.Finite.of_surjective (R := R) (S := R) (σ := RingHom.id R)
      p.toLinearMap hpSurj
  have hpε : p ε = 1 := by
    have h : p (1 - ε) = 0 := by
      change Ideal.Quotient.mk K (1 - ε) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by rfl))
    rw [map_sub, map_one] at h
    exact (sub_eq_zero.mp h).symm
  have hpα (r : R) : p (algebraMap R U r) = κ r :=
    (p.commutes r).trans (hκapply r).symm
  let L : Submodule R V := LinearMap.range κ
  let C := V ⧸ L
  let m : V →ₗ[R] C := L.mkQ
  have hCfinite : Module.Finite R C :=
    Module.Finite.of_surjective (R := R) (S := R) (σ := RingHom.id R)
      m L.mkQ_surjective
  have hCtop : (⊤ : Submodule R C).FG :=
    (Module.finite_def (R := R) (M := C)).mp hCfinite
  have hmκ (r : R) : m (κ r) = 0 := by
    change (Submodule.Quotient.mk (κ r) : C) = 0
    exact (Submodule.Quotient.mk_eq_zero (p := L)).mpr ⟨r, rfl⟩
  have hmap : ∀ x ∈ I.map (algebraMap R U), ∀ a : U,
      m (p (x * a)) ∈ I • (⊤ : Submodule R C) := by
    intro x hx
    change x ∈ Submodule.span U ((algebraMap R U) '' (I : Set R)) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        rcases hx with ⟨r, hr, rfl⟩
        intro a
        rw [← Algebra.smul_def, map_smul, map_smul]
        exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    | zero =>
        intro a
        simp only [zero_mul, map_zero, Submodule.zero_mem]
    | add x y hx hy ihx ihy =>
        intro a
        simpa only [add_mul, map_add] using
          (I • (⊤ : Submodule R C)).add_mem (ihx a) (ihy a)
    | smul a x hx ih =>
        intro b
        simpa only [smul_eq_mul, mul_assoc, mul_left_comm] using ih (a * b)
  have hCgen : (⊤ : Submodule R C) ≤ I • (⊤ : Submodule R C) := by
    intro c _hc
    obtain ⟨v, rfl⟩ := L.mkQ_surjective c
    obtain ⟨a, rfl⟩ := hpSurj v
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (τ a)
    have hx : ε * (a - algebraMap R U r) ∈ I.map (algebraMap R U) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_mul, map_sub, hεbar] using heigen a r hr
    have h := hmap _ hx 1
    simpa only [mul_one, map_mul, map_sub, hpε, one_mul, hpα, hmκ, sub_zero] using h
  have hCzero : (⊤ : Submodule R C) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      I (⊤ : Submodule R C) hCtop hCgen hI
  intro v
  have hc : m v = 0 := by
    have h : m v ∈ (⊤ : Submodule R C) := Submodule.mem_top
    rw [hCzero] at h
    exact h
  change (Submodule.Quotient.mk v : C) = 0 at hc
  have hv : v ∈ L := (Submodule.Quotient.mk_eq_zero (p := L)).mp hc
  obtain ⟨r, hr⟩ := hv
  exact ⟨r, (hκapply r).symm.trans hr⟩

private def componentSection
    {R : Type u} {U : Type v} {B : Type w}
    [CommRing R] [CommRing U] [CommRing B] [Algebra R U] [Algebra R B]
    (β : U →ₐ[R] B) (ε : U) (hε : IsIdempotentElem ε) :
    (U ⧸ Ideal.span ({1 - ε} : Set U)) →ₗ[R] B := by
  let K : Ideal U := Ideal.span ({1 - ε} : Set U)
  let f : U →ₗ[R] B :=
    { toFun := fun a => β ε * β a
      map_add' := by
        intro a b
        rw [map_add, mul_add]
      map_smul' := by
        intro r a
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [map_mul, β.commutes]
        ring }
  have hf : K.restrictScalars R ≤ LinearMap.ker f := by
    intro a ha
    change f a = 0
    change a ∈ Ideal.span ({1 - ε} : Set U) at ha
    rcases Ideal.mem_span_singleton.mp ha with ⟨b, rfl⟩
    change β ε * β ((1 - ε) * b) = 0
    have he : β ε * β ε = β ε := by
      rw [← map_mul]
      exact congrArg β hε
    rw [map_mul, map_sub, map_one, ← mul_assoc, mul_sub, mul_one, he, sub_self, zero_mul]
  let e : (U ⧸ K.restrictScalars R) ≃ₗ[R] U ⧸ K :=
    Submodule.Quotient.restrictScalarsEquiv R (K : Submodule U U)
  exact ((K.restrictScalars R).liftQ (τ₁₂ := RingHom.id R) f hf).comp e.symm.toLinearMap

private theorem componentSection_mk
    {R : Type u} {U : Type v} {B : Type w}
    [CommRing R] [CommRing U] [CommRing B] [Algebra R U] [Algebra R B]
    (β : U →ₐ[R] B) (ε : U) (hε : IsIdempotentElem ε) (a : U) :
    componentSection β ε hε
      (Ideal.Quotient.mk (Ideal.span ({1 - ε} : Set U)) a) = β ε * β a := by
  dsimp only [componentSection, LinearMap.comp_apply]
  rw [← Ideal.Quotient.mk_eq_mk]
  change
    ((Ideal.span ({1 - ε} : Set U)).restrictScalars R).liftQ
      (τ₁₂ := RingHom.id R) _ _
      ((Submodule.Quotient.restrictScalarsEquiv R
        (Ideal.span ({1 - ε} : Set U) : Submodule U U)).symm
          (Submodule.Quotient.mk a)) = β ε * β a
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply]
  rfl

private theorem component_scalar_injective
    {R : Type u} {U : Type v} [CommRing R] [CommRing U] [Algebra R U]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (ε : U)
    (hκsurj : Function.Surjective
      (algebraMap R (U ⧸ Ideal.span ({1 - ε} : Set U))))
    (hJI : RingHom.ker (algebraMap R (U ⧸ Ideal.span ({1 - ε} : Set U))) ≤ I)
    (hFlatV : Module.Flat R (U ⧸ Ideal.span ({1 - ε} : Set U))) :
    Function.Injective (algebraMap R (U ⧸ Ideal.span ({1 - ε} : Set U))) := by
  let V := U ⧸ Ideal.span ({1 - ε} : Set U)
  let κ : R →+* V := algebraMap R V
  let J : Ideal R := RingHom.ker κ
  have hJzero : J = ⊥ := by
    classical
    let : Module.Flat R V := hFlatV
    let φκ : R →ₐ[R] V := Algebra.ofId R V
    have hφκ : φκ.toRingHom = κ := by
      change (Algebra.ofId R V).toRingHom = algebraMap R V
      exact Algebra.toRingHom_ofId (R := R) (A := V)
    have hφκsurj : Function.Surjective φκ := by
      change Function.Surjective φκ.toRingHom
      rw [hφκ]
      exact hκsurj
    have hφκker : RingHom.ker φκ.toRingHom = J := by
      change RingHom.ker φκ.toRingHom = RingHom.ker κ
      exact congrArg (fun f : R →+* V => RingHom.ker f) hφκ
    let eκ : (R ⧸ RingHom.ker φκ.toRingHom) ≃ₐ[R] V :=
      Ideal.quotientKerAlgEquivOfSurjective (f := φκ) hφκsurj
    have hFlatKer : Module.Flat R (R ⧸ RingHom.ker φκ.toRingHom) :=
      Module.Flat.of_linearEquiv (R := R) (M := V) eκ.toLinearEquiv
    have hFlatQuot : Module.Flat R (R ⧸ J) :=
      Eq.mp
        (congrArg (fun L : Ideal R => Module.Flat R (R ⧸ L)) hφκker)
        hFlatKer
    let : Module.Flat R (R ⧸ J) := hFlatQuot
    have hJJac : J ≤ Ideal.jacobson (⊥ : Ideal R) := le_trans hJI hI
    apply le_antisymm
    · intro j hj
      let P : Ideal R := Ideal.span ({j} : Set R)
      have hjP : j ∈ P := by
        change j ∈ Ideal.span ({j} : Set R)
        exact Ideal.subset_span (by rfl)
      have hPJ : P ≤ J := by
        change Ideal.span ({j} : Set R) ≤ J
        apply Ideal.span_le.mpr
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact hj
      have hPFG : (P : Submodule R R).FG := by
        change (Submodule.span R ({j} : Set R)).FG
        exact ⟨{j}, by simp only [Finset.coe_singleton]⟩
      have hTensor : Function.Injective (P.subtype.lTensor (R ⧸ J)) :=
        Module.Flat.lTensor_preserves_injective_linearMap
          (R := R) (M := R ⧸ J) P.subtype
          (Submodule.injective_subtype (P : Submodule R R))
      have hInf : J ⊓ P = J * P :=
        (injective_lTensor_quotient_iff_inf_eq_mul J P).mp hTensor
      have hPmul : P = J * P := by
        calc
          P = J ⊓ P := (inf_eq_right.mpr hPJ).symm
          _ = J * P := hInf
      have hPsmul : (P : Submodule R R) ≤ J • (P : Submodule R R) := by
        rw [Ideal.smul_eq_mul J P, ← hPmul]
      have hPzero : (P : Submodule R R) = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          J (P : Submodule R R) hPFG hPsmul hJJac
      exact hPzero ▸ hjP
    · exact bot_le
  intro a b hab
  have h : a - b ∈ J := by
    change κ (a - b) = 0
    rw [map_sub, hab, sub_self]
  rw [hJzero] at h
  exact sub_eq_zero.mp h

private theorem componentSection_split
    {R : Type u} {U : Type v} {B : Type w}
    [CommRing R] [CommRing U] [CommRing B] [Algebra R U] [Algebra R B]
    (β : U →ₐ[R] B) (ε : U)
    (ρ : B →ₐ[R] U ⧸ Ideal.span ({1 - ε} : Set U))
    (σ : (U ⧸ Ideal.span ({1 - ε} : Set U)) →ₗ[R] B)
    (hσ : ∀ a : U,
      σ (Ideal.Quotient.mk (Ideal.span ({1 - ε} : Set U)) a) = β ε * β a)
    (hρ : ∀ a : U, ρ (β a) = Ideal.Quotient.mk (Ideal.span ({1 - ε} : Set U)) a) :
    ρ.toLinearMap.comp σ = LinearMap.id := by
  let K : Ideal U := Ideal.span ({1 - ε} : Set U)
  have hpε : Ideal.Quotient.mk K ε = 1 := by
    have h : Ideal.Quotient.mk K (1 - ε) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by rfl))
    rw [map_sub, map_one] at h
    exact (sub_eq_zero.mp h).symm
  apply LinearMap.ext
  intro v
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  calc
    ρ.toLinearMap (σ (Ideal.Quotient.mk K a)) = ρ (β ε * β a) :=
      congrArg ρ (hσ a)
    _ = ρ (β ε) * ρ (β a) := ρ.map_mul _ _
    _ = Ideal.Quotient.mk K ε * Ideal.Quotient.mk K a :=
      congrArg₂ (fun x y => x * y) (hρ ε) (hρ a)
    _ = Ideal.Quotient.mk K a := by rw [hpε, one_mul]

/-- A point of a flat localization of a finite algebra lifts if its residue eigencomponent
has an idempotent lift on which the given point is one.

The point being lifted is the specified `z`. No finite-presentation hypothesis on the
localization is required. The proof first makes the scalar map onto the selected component
surjective by Nakayama, then obtains flatness of that component from a linear retract.
Flatness is used separately on each principal ideal in the scalar kernel. The residue
idempotence also follows from `hε` and `hεbar`. -/
theorem Algebra.exists_lift_of_lifted_idempotent
    {R : Type u} {U : Type v} {B : Type w}
    [CommRing R] [CommRing U] [CommRing B]
    [Algebra R U] [Algebra U B] [Algebra R B]
    [IsScalarTower R U B]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    [Module.Finite R U]
    (S : Submonoid U) [IsLocalization S B] [Module.Flat R B]
    (z : B →ₐ[R] R ⧸ I)
    (ebar : U ⧸ I.map (algebraMap R U))
    (heigen : ∀ (u : U) (r : R),
      Ideal.Quotient.mk I r = z (algebraMap U B u) →
      ebar * (Ideal.Quotient.mk (I.map (algebraMap R U)) u -
        Ideal.Quotient.mk (I.map (algebraMap R U))
          (algebraMap R U r)) = 0)
    (ε : U) (hε : IsIdempotentElem ε)
    (hεbar : Ideal.Quotient.mk (I.map (algebraMap R U)) ε = ebar)
    (hεpoint : z (algebraMap U B ε) = 1) :
    ∃ s : B →ₐ[R] R, (Ideal.Quotient.mkₐ R I).comp s = z := by
  classical
  let β : U →ₐ[R] B := IsScalarTower.toAlgHom R U B
  let τ : U →ₐ[R] R ⧸ I := z.comp β
  let K : Ideal U := Ideal.span ({1 - ε} : Set U)
  let V := U ⧸ K
  let p : U →ₐ[R] V := Ideal.Quotient.mkₐ R K
  let κ : R →+* V := algebraMap R V
  have hκsurj : Function.Surjective κ :=
    scalar_surjective_of_eigenidempotent I hI τ ebar heigen ε hεbar
  have hKτ : K ≤ RingHom.ker τ.toRingHom := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    change τ (1 - ε) = 0
    rw [map_sub, map_one, show τ ε = 1 from hεpoint, sub_self]
  let ν : V →ₐ[R] R ⧸ I :=
    Ideal.Quotient.liftₐ (R₁ := R) K τ (fun a ha => hKτ ha)
  have hνp (a : U) : ν (p a) = τ a := by
    calc
      ν (p a) = ν (Ideal.Quotient.mk K a) :=
        congrArg ν (congrFun (Ideal.Quotient.mkₐ_eq_mk (R₁ := R) K) a)
      _ = Ideal.Quotient.lift K τ.toRingHom (fun b hb => hKτ hb)
            (Ideal.Quotient.mk K a) :=
        Ideal.Quotient.liftₐ_apply K τ (fun b hb => hKτ hb) _
      _ = τ a := Ideal.Quotient.lift_mk K τ.toRingHom (fun b hb => hKτ hb)
  have hνκ (r : R) : ν (κ r) = Ideal.Quotient.mk I r := by
    simpa only [κ, Ideal.Quotient.algebraMap_eq] using ν.commutes r
  have hJI : RingHom.ker κ ≤ I := by
    intro r hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    calc
      Ideal.Quotient.mk I r = ν (κ r) := (hνκ r).symm
      _ = 0 := by rw [show κ r = 0 from hr, map_zero]
  -- Surjectivity is established before denominator units, the retract, or flatness of V.
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I hI
  have hpunits : ∀ a : S, IsUnit (p a) := by
    intro a
    have hτunit : IsUnit (τ a) :=
      (IsLocalization.map_units B a).map z.toMonoidHom
    obtain ⟨r, hr⟩ := hκsurj (p a)
    have hqr : IsUnit (Ideal.Quotient.mk I r) := by
      rw [← hνκ, hr, hνp]
      exact hτunit
    have hrunit : IsUnit r := IsUnit.of_map (Ideal.Quotient.mk I) r hqr
    rw [← hr]
    exact hrunit.map κ.toMonoidHom
  let ρ₀ : B →+* V :=
    IsLocalization.lift (R := U) (M := S) (S := B) (g := p.toRingHom) hpunits
  have hρp (a : U) : ρ₀ (algebraMap U B a) = p a :=
    IsLocalization.lift_eq (R := U) (M := S) (S := B) (g := p.toRingHom) hpunits a
  let ρ : B →ₐ[R] V :=
    { toRingHom := ρ₀
      commutes' := by
        intro r
        change ρ₀ (algebraMap R B r) = algebraMap R V r
        rw [IsScalarTower.algebraMap_eq R U B]
        exact (hρp (algebraMap R U r)).trans (p.commutes r) }
  let σ : V →ₗ[R] B := componentSection β ε hε
  have hsplit : ρ.toLinearMap.comp σ = LinearMap.id := by
    apply componentSection_split β ε ρ σ
    · intro a
      exact componentSection_mk β ε hε a
    · intro a
      exact hρp a
  have hFlatV : Module.Flat R V := Module.Flat.of_retract σ ρ.toLinearMap hsplit
  have hκinj : Function.Injective κ :=
    component_scalar_injective I hI ε hκsurj hJI hFlatV
  let e : R ≃ₐ[R] V := AlgEquiv.ofBijective (Algebra.ofId R V) ⟨hκinj, hκsurj⟩
  have heκ (r : R) : e r = κ r :=
    congrArg (fun f : R →+* V => f r)
      (Algebra.toRingHom_ofId (R := R) (A := V))
  have hqinv : (Ideal.Quotient.mkₐ R I).comp e.symm.toAlgHom = ν := by
    ext v
    obtain ⟨r, rfl⟩ := hκsurj v
    change Ideal.Quotient.mk I (e.symm (κ r)) = ν (κ r)
    calc
      Ideal.Quotient.mk I (e.symm (κ r)) = Ideal.Quotient.mk I r := by
        rw [← heκ r, e.symm_apply_apply]
      _ = ν (κ r) := (hνκ r).symm
  have hνρ : ν.comp ρ = z := by
    have h : (ν.comp ρ).toRingHom = z.toRingHom := by
      apply IsLocalization.ringHom_ext (R := U) (M := S) (S := B)
      ext a
      change ν (ρ₀ (algebraMap U B a)) = z (algebraMap U B a)
      rw [hρp, hνp]
      rfl
    ext b
    exact congrArg (fun f : B →+* R ⧸ I => f b) h
  refine ⟨e.symm.toAlgHom.comp ρ, ?_⟩
  calc
    (Ideal.Quotient.mkₐ R I).comp (e.symm.toAlgHom.comp ρ) =
        ((Ideal.Quotient.mkₐ R I).comp e.symm.toAlgHom).comp ρ := rfl
    _ = ν.comp ρ := congrArg (fun f : V →ₐ[R] R ⧸ I => f.comp ρ) hqinv
    _ = z := hνρ
