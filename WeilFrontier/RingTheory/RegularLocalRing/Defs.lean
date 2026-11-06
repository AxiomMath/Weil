module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Weil.Attr

/-!
# Localizations of a normal noetherian domain at primes of height at most one are regular

Let `A` be a noetherian integrally closed domain and `𝔭 ⊂ A` a prime ideal of height `≤ 1`.
Then the localization `A_𝔭` is a regular local ring. Indeed `A_𝔭` is again a noetherian
integrally closed domain, and its Krull dimension is the height of `𝔭`, so at most one; hence
`A_𝔭` is a Dedekind domain. A local Dedekind domain is a field (height `0`) or a discrete
valuation ring (height `1`), and in either case it is regular.

In particular, for an excellent normal Henselian local domain `A`, every prime of `A` of height
at most one lies in the regular locus of `Spec A`; this is the statement used in the comparison
of `Spec A` with `Spec A{t}` in [FK, I.7].

## Main results

* `Ring.DimensionLEOne.of_ringKrullDim_le_one`: a domain of Krull dimension `≤ 1` has
  dimension `≤ 1` in the sense of `Ring.DimensionLEOne`.
* `IsIntegrallyClosed.isRegularLocalRing_localization_atPrime_of_height_le_one`: the
  localization of a noetherian integrally closed domain at a prime of height `≤ 1` is a regular
  local ring.

## Implementation notes

The statement is proved for an arbitrary noetherian integrally closed domain: the hypotheses
"excellent" and "Henselian" of the source are not needed. Membership of `𝔭` in the regular
locus is stated as `IsRegularLocalRing (Localization.AtPrime 𝔭)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl]
-/

@[expose] public section

/-- A domain of Krull dimension at most one has dimension `≤ 1` in the sense of
`Ring.DimensionLEOne`: every nonzero prime ideal is maximal. -/
theorem Ring.DimensionLEOne.of_ringKrullDim_le_one {R : Type*} [CommRing R] [IsDomain R]
    (h : ringKrullDim R ≤ 1) : Ring.DimensionLEOne R :=
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr h
  ⟨fun hp hP => hP.isMaximal_of_ne_bot hp⟩

/-- The localization of a noetherian integrally closed domain `A` at a prime ideal `𝔭` of
height at most one is a regular local ring; that is, `𝔭` lies in the regular locus of
`Spec A`. -/
@[weil "lem_fk107_henselian_line_regular_locus_complement_codim"]
theorem IsIntegrallyClosed.isRegularLocalRing_localization_atPrime_of_height_le_one
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (𝔭 : Ideal A) [𝔭.IsPrime] (h𝔭 : 𝔭.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime 𝔭) := by
  have hdim : ringKrullDim (Localization.AtPrime 𝔭) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭]
    exact_mod_cast h𝔭
  have : IsIntegrallyClosed (Localization.AtPrime 𝔭) :=
    isIntegrallyClosed_of_isLocalization _ 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  have : Ring.DimensionLEOne (Localization.AtPrime 𝔭) :=
    Ring.DimensionLEOne.of_ringKrullDim_le_one hdim
  have : IsDedekindDomain (Localization.AtPrime 𝔭) := {}
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

end
