module

public import Weil.Attr
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The singularity ideal

Let `P` be a commutative ring and `𝔟` an ideal of `P`. The *singularity ideal* `𝔰(P, 𝔟)` of
`P ⧸ 𝔟` in `P` is the intersection of all primes `𝔭 ⊇ 𝔟` of `P` such that the localization of
`P ⧸ 𝔟` at the image of `𝔭` is not a regular local ring; it is `P` when there is no such prime.
Its zero locus in `Spec P` is the closure of the singular locus of `Spec (P ⧸ 𝔟)`.

## Main definitions

* `Ideal.singularLocus 𝔟`: the set of primes `𝔭 ⊇ 𝔟` of `P` at which `P ⧸ 𝔟` is not regular.
* `Ideal.singularityIdeal 𝔟`: the singularity ideal, the vanishing ideal of
  `Ideal.singularLocus 𝔟`.

## Main results

* `Ideal.mem_singularityIdeal_iff`: `f ∈ 𝔰(P, 𝔟)` iff `f` lies in every prime of the singular
  locus.
* `Ideal.le_singularityIdeal`: `𝔟 ≤ 𝔰(P, 𝔟)`.
* `Ideal.singularityIdeal_eq_top_iff`: `𝔰(P, 𝔟) = ⊤` iff `P ⧸ 𝔟` is regular at every prime
  containing `𝔟`.
* `Ideal.isRegularLocalRing_of_not_le_singularityIdeal`: at a prime `𝔭 ⊇ 𝔟` not containing
  `𝔰(P, 𝔟)`, the ring `P ⧸ 𝔟` is regular.

## Implementation notes

The localization of `P ⧸ 𝔟` at the image of `𝔭` is formed as the localization at the image of
the submonoid `P \ 𝔭`, which needs no primality proof for the image ideal. No noetherian
hypothesis is imposed on the definition; it is needed only by results about it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I, §1.
-/

@[expose] public section

namespace Ideal

variable {P : Type*} [CommRing P] (b : Ideal P)

/-- The localization of `P ⧸ 𝔟` at the image of the prime `𝔭` of `P`, i.e. at the image of
the submonoid `P \ 𝔭`. When `𝔟 ≤ 𝔭` this is the local ring of `Spec (P ⧸ 𝔟)` at `𝔭`. -/
abbrev quotientLocalizationAt (p : PrimeSpectrum P) : Type _ :=
  Localization (p.asIdeal.primeCompl.map (Ideal.Quotient.mk b))

/-- The singular locus of `P ⧸ 𝔟`, as a set of primes of `P`: the primes `𝔭 ⊇ 𝔟` such that
the localization of `P ⧸ 𝔟` at the image of `𝔭` is not a regular local ring. -/
def singularLocus : Set (PrimeSpectrum P) :=
  {p | b ≤ p.asIdeal ∧ ¬ IsRegularLocalRing (b.quotientLocalizationAt p)}

/-- The singularity ideal `𝔰(P, 𝔟)` of `P ⧸ 𝔟` in `P`: the intersection of the primes `𝔭 ⊇ 𝔟`
of `P` at which `P ⧸ 𝔟` is not regular, and `P` itself when there is no such prime. -/
@[weil "def_fk101_singularity_ideal"]
noncomputable def singularityIdeal : Ideal P :=
  PrimeSpectrum.vanishingIdeal b.singularLocus

variable {b}

theorem mem_singularLocus_iff {p : PrimeSpectrum P} :
    p ∈ b.singularLocus ↔
      b ≤ p.asIdeal ∧ ¬ IsRegularLocalRing (b.quotientLocalizationAt p) :=
  Iff.rfl

theorem mem_singularityIdeal_iff {f : P} :
    f ∈ b.singularityIdeal ↔ ∀ p ∈ b.singularLocus, f ∈ p.asIdeal :=
  PrimeSpectrum.mem_vanishingIdeal _ _

theorem singularityIdeal_le_of_mem_singularLocus {p : PrimeSpectrum P}
    (hp : p ∈ b.singularLocus) : b.singularityIdeal ≤ p.asIdeal :=
  fun _ hf => mem_singularityIdeal_iff.1 hf p hp

theorem singularityIdeal_le {p : PrimeSpectrum P} (hb : b ≤ p.asIdeal)
    (hreg : ¬ IsRegularLocalRing (b.quotientLocalizationAt p)) :
    b.singularityIdeal ≤ p.asIdeal :=
  singularityIdeal_le_of_mem_singularLocus ⟨hb, hreg⟩

theorem isRegularLocalRing_of_not_le_singularityIdeal {p : PrimeSpectrum P}
    (hb : b ≤ p.asIdeal) (hp : ¬ b.singularityIdeal ≤ p.asIdeal) :
    IsRegularLocalRing (b.quotientLocalizationAt p) := by
  by_contra h
  exact hp (singularityIdeal_le hb h)

variable (b)

theorem le_singularityIdeal : b ≤ b.singularityIdeal :=
  fun _ hf => mem_singularityIdeal_iff.2 fun _ hp => hp.1 hf

theorem singularityIdeal_eq_top_of_singularLocus_eq_empty (h : b.singularLocus = ∅) :
    b.singularityIdeal = ⊤ := by
  rw [singularityIdeal, h, PrimeSpectrum.vanishingIdeal_empty]

theorem singularLocus_eq_empty_of_singularityIdeal_eq_top (h : b.singularityIdeal = ⊤) :
    b.singularLocus = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  exact p.isPrime.ne_top (top_le_iff.1 (h ▸ singularityIdeal_le_of_mem_singularLocus hp))

theorem singularityIdeal_eq_top_iff_singularLocus_eq_empty :
    b.singularityIdeal = ⊤ ↔ b.singularLocus = ∅ :=
  ⟨singularLocus_eq_empty_of_singularityIdeal_eq_top b,
    singularityIdeal_eq_top_of_singularLocus_eq_empty b⟩

/-- `𝔰(P, 𝔟) = P` iff `P ⧸ 𝔟` is regular at every prime of `P` containing `𝔟`. -/
theorem singularityIdeal_eq_top_iff :
    b.singularityIdeal = ⊤ ↔
      ∀ p : PrimeSpectrum P, b ≤ p.asIdeal → IsRegularLocalRing (b.quotientLocalizationAt p) := by
  rw [singularityIdeal_eq_top_iff_singularLocus_eq_empty, Set.eq_empty_iff_forall_notMem]
  refine forall_congr' fun p => ?_
  rw [mem_singularLocus_iff, not_and, not_not]

theorem isRadical_singularityIdeal : b.singularityIdeal.IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- The zero locus of `𝔰(P, 𝔟)` is the closure of the singular locus. -/
theorem zeroLocus_singularityIdeal :
    PrimeSpectrum.zeroLocus (b.singularityIdeal : Set P) = closure b.singularLocus :=
  PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _

end Ideal
