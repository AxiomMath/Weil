module

public import Weil.Attr
public import StacksFrontier.RingTheory.Henselian.TFAE

/-!
# Hensel's lemma for a local ring

A local ring `(A, 𝔪)` *satisfies Hensel's lemma* if every factorization `P̄ = Q̄ R̄` of the
reduction of a monic polynomial `P ∈ A[X]` into relatively prime monic polynomials over the
residue field `A/𝔪` lifts to a factorization `P = Q R` into monic polynomials over `A` whose
reductions are `Q̄` and `R̄`.

For every local ring this is equivalent to Mathlib's `HenselianLocalRing` (the root-lifting
form); no noetherian hypothesis is needed.

## Main definitions

* `IsLocalRing.SatisfiesHenselLemma A`: the monic coprime-factorization lifting property.

## Main results

* `IsLocalRing.satisfiesHenselLemma_iff_henselianLocalRing`: a local ring satisfies Hensel's
  lemma if and only if it is henselian.
* `HenselianLocalRing.satisfiesHenselLemma`: a henselian local ring satisfies Hensel's lemma.

## Implementation notes

The equivalence is extracted from items (1), (3) and (4) of
`HenselianLocalRing.TFAE_factorization_etale_quasiFinite` (Stacks, Tag 04GG). Item (4) lifts
a coprime factorization of the reduction of a monic polynomial with `deg g = deg g₀`; the
leading coefficient of `g` is then a unit reducing to `1`, and dividing by it gives the monic
lifts. Conversely, a factorization `f̄ = g₀ h₀` of a monic polynomial into coprime factors is
normalized to monic factors by the leading coefficient of `g₀`, which is a unit.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

open Polynomial IsLocalRing

universe u

namespace IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- A local ring `A` *satisfies Hensel's lemma* if for every monic `P ∈ A[X]` whose reduction
`P̄ ∈ (A/𝔪)[X]` is a product `P̄ = Q̄ R̄` of relatively prime monic polynomials, there are monic
`Q R ∈ A[X]` with `P = Q R` reducing to `Q̄` and `R̄`. -/
@[weil "def_fk101_hensel_lemma_property"]
def SatisfiesHenselLemma : Prop :=
  ∀ P : A[X], P.Monic → ∀ Q₀ R₀ : (ResidueField A)[X], Q₀.Monic → R₀.Monic →
    IsCoprime Q₀ R₀ → P.map (residue A) = Q₀ * R₀ →
    ∃ Q R : A[X], Q.Monic ∧ R.Monic ∧ P = Q * R ∧
      Q.map (residue A) = Q₀ ∧ R.map (residue A) = R₀

variable {A}

/-- Item (4) of Tag 04GG gives monic lifts of a monic coprime factorization. -/
private lemma satisfiesHenselLemma_of_item4
    (h4 : ∀ f : A[X], f.Monic → ∀ g₀ h₀ : (ResidueField A)[X], f.map (residue A) = g₀ * h₀ →
      IsCoprime g₀ h₀ →
      ∃ g h : A[X], f = g * h ∧ g.map (residue A) = g₀ ∧ h.map (residue A) = h₀ ∧
        g.degree = g₀.degree) :
    SatisfiesHenselLemma A := by
  intro P hP Q₀ R₀ hQ₀ _hR₀ hcop hPQR
  obtain ⟨g, h, rfl, hg, hh, hdeg⟩ := h4 P hP Q₀ R₀ hPQR hcop
  -- the leading coefficient of `g` reduces to `1`
  have hnat : g.natDegree = Q₀.natDegree := by
    rw [natDegree_eq_of_degree_eq hdeg]
  have hlc : residue A g.leadingCoeff = 1 := by
    have := congrArg (fun p => p.coeff Q₀.natDegree) hg
    simp only [coeff_map] at this
    rw [leadingCoeff, hnat, this]
    exact hQ₀
  have hu : IsUnit g.leadingCoeff := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hlc]
    exact one_ne_zero
  obtain ⟨u, hu'⟩ := hu
  have hres : residue A (↑u⁻¹ : A) = 1 := by
    have h1 : residue A (↑u : A) * residue A (↑u⁻¹ : A) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rwa [hu', hlc, one_mul] at h1
  have hQm : (g * C (↑u⁻¹ : A)).Monic := by
    rw [Monic, leadingCoeff_mul_C_of_isUnit (Units.isUnit _), ← hu', Units.mul_inv]
  have hprod : g * h = g * C (↑u⁻¹ : A) * (C (↑u : A) * h) := by
    rw [mul_assoc, ← mul_assoc (C _), ← C_mul, Units.inv_mul, C_1, one_mul]
  refine ⟨g * C (↑u⁻¹ : A), C (↑u : A) * h, hQm, ?_, hprod, ?_, ?_⟩
  · rw [hprod] at hP
    exact hQm.of_mul_monic_left hP
  · rw [Polynomial.map_mul, map_C, hg, hres, C_1, mul_one]
  · have hres' : residue A (↑u : A) = 1 := by rw [hu', hlc]
    rw [Polynomial.map_mul, map_C, hh, hres', C_1, one_mul]

/-- Monic lifts of monic coprime factorizations give item (3) of Tag 04GG. -/
private lemma item3_of_satisfiesHenselLemma (hA : SatisfiesHenselLemma A) :
    ∀ f : A[X], f.Monic → ∀ g₀ h₀ : (ResidueField A)[X], f.map (residue A) = g₀ * h₀ →
      IsCoprime g₀ h₀ →
      ∃ g h : A[X], f = g * h ∧ g.map (residue A) = g₀ ∧ h.map (residue A) = h₀ := by
  intro f hf g₀ h₀ hfgh hcop
  have hm : (g₀ * h₀).Monic := hfgh ▸ hf.map (residue A)
  have hlc : g₀.leadingCoeff * h₀.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul]; exact hm
  set c := g₀.leadingCoeff with hc
  set d := h₀.leadingCoeff with hd
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hlc
  have hdc : d = c⁻¹ := eq_inv_of_mul_eq_one_right hlc
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c
  have hau : IsUnit a := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ha]; exact hc0
  obtain ⟨u, rfl⟩ := hau
  have hgm : (g₀ * C c⁻¹).Monic := by
    rw [Monic, leadingCoeff_mul_C_of_isUnit (isUnit_iff_ne_zero.mpr (inv_ne_zero hc0)),
      ← hc, mul_inv_cancel₀ hc0]
  have hhm : (h₀ * C c).Monic := by
    rw [Monic, leadingCoeff_mul_C_of_isUnit (isUnit_iff_ne_zero.mpr hc0), ← hd, hdc,
      inv_mul_cancel₀ hc0]
  have hcop' : IsCoprime (g₀ * C c⁻¹) (h₀ * C c) :=
    (isCoprime_mul_units_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hc0)))
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)) _ _).mpr hcop
  have hfac : f.map (residue A) = g₀ * C c⁻¹ * (h₀ * C c) := by
    rw [hfgh, mul_mul_mul_comm, ← C_mul, inv_mul_cancel₀ hc0, C_1, mul_one]
  obtain ⟨Q, R, -, -, rfl, hQ, hR⟩ := hA f hf _ _ hgm hhm hcop' hfac
  have hinv : residue A (↑u⁻¹ : A) = c⁻¹ := by
    rw [← ha, map_units_inv]
  refine ⟨Q * C (↑u : A), R * C (↑u⁻¹ : A), ?_, ?_, ?_⟩
  · rw [mul_mul_mul_comm, ← C_mul, Units.mul_inv, C_1, mul_one]
  · rw [Polynomial.map_mul, map_C, hQ, ha, mul_assoc, ← C_mul, inv_mul_cancel₀ hc0, C_1,
      mul_one]
  · rw [Polynomial.map_mul, map_C, hR, hinv, mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1,
      mul_one]

/-- A local ring satisfies Hensel's lemma (monic coprime factorizations of reductions of
monic polynomials lift) if and only if it is henselian. -/
theorem satisfiesHenselLemma_iff_henselianLocalRing :
    SatisfiesHenselLemma A ↔ HenselianLocalRing A := by
  have h := HenselianLocalRing.TFAE_factorization_etale_quasiFinite A
  constructor
  · intro hA
    exact (h.out 1 3).mpr (item3_of_satisfiesHenselLemma hA)
  · intro hA
    exact satisfiesHenselLemma_of_item4 ((h.out 1 4).mp hA)

end IsLocalRing

/-- A henselian local ring satisfies Hensel's lemma. -/
theorem HenselianLocalRing.satisfiesHenselLemma (A : Type u) [CommRing A]
    [HenselianLocalRing A] : IsLocalRing.SatisfiesHenselLemma A :=
  IsLocalRing.satisfiesHenselLemma_iff_henselianLocalRing.mpr ‹_›

end
