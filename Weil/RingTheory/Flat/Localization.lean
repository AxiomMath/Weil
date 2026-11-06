module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Weil.Attr

/-!
# Flatness from flatness of localizations over the base

Let `A → C` be a ring homomorphism and `M` a `C`-module. If for every maximal ideal `P` of `C`
the localization `M_P` is flat over the local ring `A_q`, where `q = P ∩ A`, then `M` is flat
over `A`.

## Main results

* `Module.flat_of_flat_localization_comap_maximal`: the statement above, for any choice of
  localizations `A_q` of `A` and `M_P` of `M`.

## Implementation notes

The localizations are arbitrary: `Aₚ P` is any `A`-algebra that is a localization of `A` at
`P.comap (algebraMap A C)`, and `Mₚ P` is any module receiving a map `M →ₗ[C] Mₚ P` that is a
localization at `P`, with compatible `A`-, `C`- and `Aₚ P`-module structures. The proof reduces
to `Module.flat_of_isLocalized_maximal`: since `A_q` is flat over `A`, a flat `A_q`-module is
flat over `A` (`Module.Flat.trans`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

namespace Module

variable {A C M : Type*} [CommRing A] [CommRing C] [Algebra A C]
  [AddCommGroup M] [Module A M] [Module C M] [IsScalarTower A C M]

/-- Let `A → C` be a ring homomorphism and `M` a `C`-module such that for every maximal ideal
`P` of `C`, the localization `M_P` is flat over `A_q` with `q = P ∩ A`. Then `M` is flat
over `A`. -/
@[weil "lem_fk101_flat_of_flat_at_primes"]
theorem flat_of_flat_localization_comap_maximal
    (Aₚ : ∀ (P : Ideal C) [P.IsMaximal], Type*)
    [∀ (P : Ideal C) [P.IsMaximal], CommRing (Aₚ P)]
    [∀ (P : Ideal C) [P.IsMaximal], Algebra A (Aₚ P)]
    [∀ (P : Ideal C) [P.IsMaximal], IsLocalization.AtPrime (Aₚ P) (P.comap (algebraMap A C))]
    (Mₚ : ∀ (P : Ideal C) [P.IsMaximal], Type*)
    [∀ (P : Ideal C) [P.IsMaximal], AddCommGroup (Mₚ P)]
    [∀ (P : Ideal C) [P.IsMaximal], Module A (Mₚ P)]
    [∀ (P : Ideal C) [P.IsMaximal], Module C (Mₚ P)]
    [∀ (P : Ideal C) [P.IsMaximal], Module (Aₚ P) (Mₚ P)]
    [∀ (P : Ideal C) [P.IsMaximal], IsScalarTower A C (Mₚ P)]
    [∀ (P : Ideal C) [P.IsMaximal], IsScalarTower A (Aₚ P) (Mₚ P)]
    (f : ∀ (P : Ideal C) [P.IsMaximal], M →ₗ[C] Mₚ P)
    [∀ (P : Ideal C) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]
    (H : ∀ (P : Ideal C) [P.IsMaximal], Module.Flat (Aₚ P) (Mₚ P)) :
    Module.Flat A M := by
  refine Module.flat_of_isLocalized_maximal C M Mₚ f fun P _ ↦ ?_
  have : Module.Flat A (Aₚ P) :=
    IsLocalization.flat (Aₚ P) (P.comap (algebraMap A C)).primeCompl
  exact Module.Flat.trans A (Aₚ P) (Mₚ P)

end Module
