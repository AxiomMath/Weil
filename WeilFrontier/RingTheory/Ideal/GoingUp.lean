module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Weil.Attr

/-!
# Localizing a finite algebra over a local ring at a maximal ideal

Let `A` be a local ring and `f : A →+* B` an integral (for instance finite) ring homomorphism.
For every maximal ideal `𝔫` of `B`, the composite `A → B → B_𝔫` is a local homomorphism:
the preimage of `𝔫` in `A` is maximal by going-up (lying over a maximal ideal under an integral
extension), hence equals the maximal ideal of `A`.

## Main results

* `isLocalHom_algebraMap_localization_comp_of_isIntegral`: the integral case.
* `isLocalHom_algebraMap_localization_comp_of_finite`: the finite case.

## Implementation notes

The noetherian hypothesis on `A` in the source is not needed, and the finite case is deduced
from the integral one.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
-/

@[expose] public section

open IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]

/-- For an integral ring homomorphism `f : A →+* B` out of a local ring and a maximal ideal `𝔫`
of `B`, the composite `A → B → B_𝔫` is a local homomorphism. -/
theorem isLocalHom_algebraMap_localization_comp_of_isIntegral (f : A →+* B) (hf : f.IsIntegral)
    (n : Ideal B) [n.IsMaximal] :
    IsLocalHom ((algebraMap B (Localization.AtPrime n)).comp f) := by
  let := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hf⟩
  have hc : n.comap f = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) n)
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ n.comap f := hc ▸ (mem_maximalIdeal a).mpr h
  have : algebraMap B (Localization.AtPrime n) (f a) ∈ maximalIdeal (Localization.AtPrime n) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hm
  exact (mem_maximalIdeal _).mp this ha

/-- For a finite ring homomorphism `f : A →+* B` out of a local ring and a maximal ideal `𝔫` of
`B`, the composite `A → B → B_𝔫` is a local homomorphism. -/
@[weil "lem_fk103_finite_over_henselian_factor_map_local"]
theorem isLocalHom_algebraMap_localization_comp_of_finite (f : A →+* B) (hf : f.Finite)
    (n : Ideal B) [n.IsMaximal] :
    IsLocalHom ((algebraMap B (Localization.AtPrime n)).comp f) :=
  isLocalHom_algebraMap_localization_comp_of_isIntegral f hf.to_isIntegral n

end
