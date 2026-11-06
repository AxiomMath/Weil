module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Sections of the structure sheaf over the regular locus of a normal domain

Let `A` be a Noetherian integrally closed domain. A prime `𝔭` of `A` of height at most one has
regular local ring `A_𝔭`: it is a field when `𝔭 = 0`, and a Noetherian integrally closed local
domain of dimension one, hence a discrete valuation ring, when `𝔭` has height one. So every open
subset `W ⊆ Spec A` containing the primes of height `≤ 1` contains the generic point, and the
algebraic Hartogs lemma applies: a section `s ∈ Γ(W, 𝒪)` has germ at the generic point an
element `z` of the fraction field `K` of `A` with `z ∈ A_𝔭` for every `𝔭 ∈ W`, in particular for
every prime of height one, and `A = ⋂_{ht 𝔭 = 1} A_𝔭` inside `K` (Stacks 031T). Hence the
restriction map `A = Γ(Spec A, 𝒪) → Γ(W, 𝒪)` is an isomorphism.

When `A` is moreover excellent, the regular locus `V` of `Spec A` is open (excellent rings are
J-2, hence J-1), and it contains every prime of height `≤ 1`; therefore `A → Γ(V, 𝒪_V)` is an
isomorphism.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_localization_of_height_le_one`: a normal Noetherian
  domain is regular at every prime of height at most one.
* `AlgebraicGeometry.isIso_presheaf_map_of_height_le_one`: the algebraic Hartogs lemma, the
  restriction `Γ(Spec A, ⊤) → Γ(Spec A, W)` is an isomorphism when `W` contains every prime of
  height at most one.
* `AlgebraicGeometry.isOpen_regularLocus_of_isExcellent`: the regular locus of the spectrum of
  an excellent ring is open.
* `AlgebraicGeometry.isIso_presheaf_map_regularLocus`: for an excellent normal domain `A` the
  restriction from `Spec A` to its regular locus is an isomorphism on sections.

## Implementation notes

The statement is proved for every excellent integrally closed domain `A`; the local and
Henselian hypotheses of the source, which only fix the setting of the Henselian affine line
over `A`, are not needed. The regular locus is StacksFrontier's `AlgebraicGeometry.regularLocus`,
regarded as an open subscheme of `Spec A` through its openness.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T)
-/

/- `isIso_presheaf_map_of_height_le_one` is also FK's statement on sections of a normal domain
outside codimension two, and `isRegularLocalRing_localization_of_height_le_one` is FK's statement
that the complement of the regular locus has codimension at least two. -/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- A Noetherian integrally closed domain is regular at every prime of height at most one. -/
theorem isRegularLocalRing_localization_of_height_le_one {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (p : Ideal R) [p.IsPrime] (hp : p.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  set L := Localization.AtPrime p
  have hdim : (IsLocalRing.maximalIdeal L).height ≤ 1 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := L)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p L] at h
    exact (WithBot.coe_le_coe.mp h.le).trans hp
  have : Ring.DimensionLEOne L := ⟨fun {Q} hQ hQp => by
    by_contra hmax
    have hlt : Q < IsLocalRing.maximalIdeal L :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) fun h => hmax (h ▸ inferInstance)
    have hQ0 : Q.height ≠ 0 := by
      intro h0
      rw [Ideal.height_eq_zero_iff] at h0
      exact hQ (le_bot_iff.mp (h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le))
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : (1 : ℕ∞) + 1 ≤ Q.height + 1 := by
      gcongr; exact Order.one_le_iff_ne_zero.mpr hQ0
    have := (h2.trans h1).trans hdim
    exact absurd this (by decide)⟩
  have : IsIntegrallyClosed L :=
    isIntegrallyClosed_of_isLocalization L p.primeCompl (Ideal.primeCompl_le_nonZeroDivisors p)
  have : IsDedekindDomain L := { }
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing L

/-- **Algebraic Hartogs lemma.** For a Noetherian integrally closed domain `R` and an open
`W ⊆ Spec R` containing every prime of height at most one, the restriction map
`Γ(Spec R, ⊤) → Γ(Spec R, W)` is an isomorphism. -/
theorem isIso_presheaf_map_of_height_le_one {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Spec (.of R)).Opens)
    (hW : ∀ p : PrimeSpectrum R, p.asIdeal.height ≤ 1 → p ∈ W) :
    IsIso ((Spec (.of R)).presheaf.map (homOfLE le_top : W ⟶ ⊤).op) := by
  let η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ∈ W := hW η (by simp [η])
  have : Nonempty W := ⟨⟨η, hη⟩⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨map_injective_of_isIntegral _ _, fun s => ?_⟩
  let F := Spec.structureSheaf R
  -- Every `p ∈ W` writes the germ of `s` at the generic point as `a / b` with `b ∉ p`.
  have key : ∀ (p : PrimeSpectrum R) (hp : p ∈ W), ∃ a b : R, b ∉ p.asIdeal ∧
      F.presheaf.germ W η hη s * algebraMap R (F.presheaf.stalk η) b =
        algebraMap R (F.presheaf.stalk η) a := by
    intro p hp
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl
      (F.presheaf.germ W p hp s)
    have hsp : η ⤳ p := (PrimeSpectrum.le_iff_specializes η p).1 bot_le
    have h1 := congrArg (F.presheaf.stalkSpecializes hsp).hom
      (IsLocalization.mk'_spec (F.presheaf.stalk p) a b)
    change IsLocalization.mk' _ a b = _ at hab
    rw [map_mul, hab] at h1
    refine ⟨a, b, b.2, ?_⟩
    have e1 := TopCat.Presheaf.germ_stalkSpecializes_apply F.presheaf hp hsp s
    have e2 : ∀ r : R, (F.presheaf.stalkSpecializes hsp).hom
        (algebraMap R (F.presheaf.stalk p) r) = algebraMap R (F.presheaf.stalk η) r :=
      fun r => StructureSheaf.toStalk_stalkSpecializes_apply hsp r
    rw [e2, e2] at h1
    convert h1 using 2
    exact e1.symm
  set S := F.presheaf.stalk η
  set g := F.presheaf.germ W η hη s
  have : IsLocalization.AtPrime S η.asIdeal := StructureSheaf.IsLocalization.to_stalk R η
  have inj : Function.Injective (algebraMap R S) :=
    IsLocalization.injective (M := η.asIdeal.primeCompl) S
      (Ideal.primeCompl_le_nonZeroDivisors _)
  obtain ⟨a₀, b₀, hb₀, h₀⟩ := key η hη
  have hb₀' : b₀ ≠ 0 := fun h => hb₀ (h ▸ Submodule.zero_mem _)
  let K := FractionRing R
  have hb₀K : algebraMap R K b₀ ≠ 0 := by simpa using hb₀'
  set z : K := algebraMap R K a₀ / algebraMap R K b₀
  have hz : z ∈ ⨅ p : PrimeSpectrum R, ⨅ _ : p.asIdeal.height = 1,
      Localization.subalgebra.ofField K _ p.asIdeal.primeCompl_le_nonZeroDivisors := by
    refine Algebra.mem_iInf.mpr fun p => Algebra.mem_iInf.mpr fun hp => ?_
    obtain ⟨a, b, hb, h⟩ := key p (hW p hp.le)
    have hb' : b ≠ 0 := fun h => hb (h ▸ Submodule.zero_mem _)
    have hbK : algebraMap R K b ≠ 0 := by simpa using hb'
    have hab : a₀ * b = a * b₀ := inj (by
      rw [map_mul, map_mul, ← h₀, ← h]; ring)
    refine ⟨a, b, hb, ?_⟩
    rw [eq_mul_inv_iff_mul_eq₀ hbK, div_mul_eq_mul_div, div_eq_iff hb₀K, ← map_mul,
      ← map_mul, hab]
  rw [(associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot K).2.1] at hz
  obtain ⟨d, hd⟩ := Algebra.mem_bot.mp hz
  have had : a₀ = d * b₀ := IsFractionRing.injective R K (by
    rw [map_mul, hd, div_mul_cancel₀ _ hb₀K])
  refine ⟨algebraMap R ((Spec.structureSheaf R).presheaf.obj (op ⊤)) d, ?_⟩
  apply germ_injective_of_isIntegral (Spec (.of R)) η hη
  have hgd : g = algebraMap R S d :=
    (IsLocalization.map_units S (⟨b₀, hb₀⟩ : η.asIdeal.primeCompl)).mul_left_inj.mp
      (by rw [h₀, had, map_mul])
  have e := StructureSheaf.algebraMap_germ_apply (R := R) ⊤ η trivial d
  have e0 := TopCat.Presheaf.germ_res_apply (Spec (.of R)).presheaf
    (homOfLE le_top : W ⟶ ⊤) η hη
    (algebraMap R ((Spec.structureSheaf R).presheaf.obj (op ⊤)) d)
  exact e0.trans (e.trans hgd.symm)

/-- The regular locus of the spectrum of an excellent ring is open. -/
theorem isOpen_regularLocus_of_isExcellent {A : Type u} [CommRing A] (hA : IsExcellent A) :
    IsOpen (regularLocus (Spec (.of A))) :=
  (Scheme.isOpen_regularLocus_spec_iff A).mpr (hA.1.2.2 A)

/-- A normal Noetherian domain is regular at every point of `Spec A` whose prime has height at
most one. -/
theorem mem_regularLocus_of_height_le_one {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] (p : PrimeSpectrum A) (hp : p.asIdeal.height ≤ 1) :
    p ∈ regularLocus (Spec (.of A)) := by
  have := isRegularLocalRing_localization_of_height_le_one p.asIdeal hp
  change IsRegularLocalRing ((Spec (.of A)).presheaf.stalk p)
  exact IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of A) p).commRingCatIsoToRingEquiv.symm

/-- Let `A` be an excellent integrally closed domain and `V` the regular locus of `Spec A`, an
open subscheme. Then the restriction map `A = Γ(Spec A, 𝒪) → Γ(V, 𝒪_V)` is an isomorphism. -/
@[weil "lem_fk107_henselian_line_sections_base_regular_locus"]
theorem isIso_presheaf_map_regularLocus {A : Type u} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (hA : IsExcellent A) :
    IsIso ((Spec (.of A)).presheaf.map
      (homOfLE le_top :
        (⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩ :
          (Spec (.of A)).Opens) ⟶ ⊤).op) :=
  have : IsNoetherianRing A := hA.1.1
  isIso_presheaf_map_of_height_le_one _ fun p hp => mem_regularLocus_of_height_le_one p hp

end AlgebraicGeometry
