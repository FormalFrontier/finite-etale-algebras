/-
Authors: Formal Frontier Agents
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FiniteEtaleAlgebras.MaximalSubalgebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Connected components of finite etale spectra

This file identifies the number of connected components of the spectrum of a
finite etale algebra over a separably closed field with its vector-space
dimension. It then bounds that dimension using any continuous surjection onto
the spectrum.

The statements allow independent universes and include zero rings, empty
spectra, empty source spaces, and zero component counts.
-/

public section

open Function Topology

universe u v w

namespace Algebra.IsFiniteEtale

noncomputable section

variable {k : Type u} {S : Type v} [Field k] [IsSepClosed k]
  [CommRing S] [Algebra k S]

/-- Over a separably closed field, the number of connected components of the
spectrum of a finite etale algebra is its vector-space dimension. -/
theorem natCard_connectedComponents_primeSpectrum_eq_finrank
    (hS : Algebra.IsFiniteEtale k S) :
    Nat.card (ConnectedComponents (PrimeSpectrum S)) = Module.finrank k S := by
  let _ : Module.Finite k S := hS.1
  let _ : Algebra.Etale k S := hS.2
  let _ : IsArtinianRing S := isArtinian_of_tower k inferInstance
  let _ : DiscreteTopology (PrimeSpectrum S) :=
    DiscreteTopology.of_finite_of_isClosed_singleton fun p =>
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr inferInstance
  let _ : Fintype (PrimeSpectrum S) := Fintype.ofFinite _
  let pointsEquivComponents :
      PrimeSpectrum S ≃ ConnectedComponents (PrimeSpectrum S) :=
    Equiv.ofBijective ConnectedComponents.mk ⟨by
      intro x y hxy
      apply Set.singleton_injective
      simpa only [ConnectedComponents.coe_eq_coe,
        connectedComponent_eq_singleton] using hxy,
      ConnectedComponents.surjective_coe⟩
  calc
    Nat.card (ConnectedComponents (PrimeSpectrum S)) =
        Nat.card (PrimeSpectrum S) := (Nat.card_congr pointsEquivComponents).symm
    _ = Fintype.card (PrimeSpectrum S) := Nat.card_eq_fintype_card
    _ = Module.finrank k S := by
      rw [← Module.finrank_fintype_fun_eq_card k]
      exact
        (Algebra.FormallyEtale.equivPiOfIsSepClosed k S).toLinearEquiv.finrank_eq.symm

/-- A continuous surjection onto the spectrum of a finite etale algebra over a
separably closed field bounds its dimension by the number of connected
components of the source. -/
theorem finrank_le_natCard_connectedComponents_of_surjective
    {X : Type w} [TopologicalSpace X] [Finite (ConnectedComponents X)]
    (hS : Algebra.IsFiniteEtale k S) (f : X → PrimeSpectrum S)
    (hf : Continuous f) (hsurj : Surjective f) :
    Module.finrank k S ≤ Nat.card (ConnectedComponents X) := by
  rw [← natCard_connectedComponents_primeSpectrum_eq_finrank hS]
  exact Nat.card_le_card_of_surjective hf.connectedComponentsMap
    (hf.connectedComponentsMap_surjective hsurj)

end

end Algebra.IsFiniteEtale
