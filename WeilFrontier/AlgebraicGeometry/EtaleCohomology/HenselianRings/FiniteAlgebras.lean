module

public import Mathlib.RingTheory.Spectrum.Maximal.Localization
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteAlgebras
public import Weil.Attr

/-!
# A finite algebra over a henselian local ring is the product of its localizations

Let `A` be a henselian local ring and `B` a finite `A`-algebra. Then `B` has only finitely many
maximal ideals `𝔫₁, …, 𝔫ᵣ`, and the canonical ring homomorphism `B → ∏ᵢ B_{𝔫ᵢ}` is an
isomorphism.

The proof goes through the decomposition of `B` as a finite product of local rings
(`exists_algEquiv_pi_henselianLocalRing_of_module_finite`), together with the fact that a finite
product of local rings is canonically the product of its localizations at its maximal ideals.

## Main results

* `MaximalSpectrum.toPiLocalization_pi_bijective_of_isLocalRing`: for a finite family of local
  rings `Lᵢ`, the canonical map from `∏ᵢ Lᵢ` to the product of its localizations at its maximal
  ideals is bijective.
* `finite_maximalSpectrum_of_henselianLocalRing`: a finite algebra over a henselian local ring
  has finitely many maximal ideals.
* `bijective_toPiLocalization_of_henselianLocalRing`: for such an algebra `B`, the canonical map
  `B → ∏_{𝔫} B_𝔫` is bijective.
* `toPiLocalizationEquivOfHenselianLocalRing`: the resulting algebra isomorphism.

## Implementation notes

The base ring is not assumed noetherian: Mathlib's `HenselianLocalRing` is used, and the
statement holds in that generality. The product over the maximal ideals is
`MaximalSpectrum.PiLocalization B`, and the canonical map is `MaximalSpectrum.toPiLocalization B`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I, §3][FK]
* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
-/

@[expose] public section

universe u v

namespace MaximalSpectrum

variable {ι : Type*} [Finite ι] (L : ι → Type*) [∀ i, CommRing (L i)] [∀ i, IsLocalRing (L i)]

/-- For a local ring, the canonical map to its localization at the maximal ideal is
surjective (all elements of the complement are units). -/
theorem algebraMap_localization_atPrime_maximalIdeal_surjective (R : Type*) [CommRing R]
    [IsLocalRing R] :
    Function.Surjective
      (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R))) := by
  intro z
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (IsLocalRing.maximalIdeal R).primeCompl z
  have hs : IsUnit (s : R) := by
    by_contra h
    exact s.2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  refine ⟨x * hs.unit⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

/-- A finite product of local rings is canonically isomorphic to the product of its
localizations at its maximal ideals: the canonical map is surjective. -/
theorem toPiLocalization_pi_surjective_of_isLocalRing :
    Function.Surjective (toPiLocalization (Π i, L i)) := by
  intro x
  let I : ι → MaximalSpectrum (Π i, L i) := fun i =>
    ⟨(IsLocalRing.maximalIdeal (L i)).comap (Pi.evalRingHom L i),
      Ideal.IsMaximal.comap_piEvalRingHom (IsLocalRing.maximalIdeal.isMaximal _)⟩
  have hy : ∀ i, ∃ y : L i, algebraMap (L i) _ y =
      Localization.AtPrime.mapPiEvalRingHom (IsLocalRing.maximalIdeal (L i)) (x (I i)) :=
    fun i => algebraMap_localization_atPrime_maximalIdeal_surjective (L i) _
  choose y hy using hy
  refine ⟨y, funext fun J => ?_⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq (R := L) ⟨J.1, J.2.isPrime⟩
  have hq' : q.asIdeal.comap (Pi.evalRingHom L i) = J.asIdeal := congrArg PrimeSpectrum.asIdeal hq
  have hqm : q.asIdeal = IsLocalRing.maximalIdeal (L i) := by
    have hle : q.asIdeal ≤ IsLocalRing.maximalIdeal (L i) :=
      IsLocalRing.le_maximalIdeal q.2.ne_top
    have hmax : (q.asIdeal.comap (Pi.evalRingHom L i)).IsMaximal := hq' ▸ J.2
    have hJ : q.asIdeal.comap (Pi.evalRingHom L i) =
        (IsLocalRing.maximalIdeal (L i)).comap (Pi.evalRingHom L i) :=
      hmax.eq_of_le (Ideal.IsMaximal.comap_piEvalRingHom
        (IsLocalRing.maximalIdeal.isMaximal _)).ne_top (Ideal.comap_mono hle)
    exact Ideal.comap_injective_of_surjective _ RingHomSurjective.is_surjective hJ
  obtain rfl : J = I i := by
    ext1
    rw [← hq', hqm]
  apply (Localization.AtPrime.mapPiEvalRingHom_bijective
    (IsLocalRing.maximalIdeal (L i))).1
  rw [toPiLocalization_apply_apply, Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply]
  exact hy i

/-- A finite product of local rings: the canonical map to the product of its localizations at
its maximal ideals is bijective. -/
theorem toPiLocalization_pi_bijective_of_isLocalRing :
    Function.Bijective (toPiLocalization (Π i, L i)) :=
  ⟨toPiLocalization_injective _, toPiLocalization_pi_surjective_of_isLocalRing L⟩

/-- Surjectivity of the canonical map `R → ∏_{𝔪} R_𝔪` is invariant under ring isomorphisms. -/
theorem toPiLocalization_surjective_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : Function.Surjective (toPiLocalization S)) :
    Function.Surjective (toPiLocalization R) := by
  intro x
  let f : R →+* S := e
  have hf : Function.Bijective f := e.bijective
  obtain ⟨r, hr⟩ := h (mapPiLocalization f hf x)
  refine ⟨e.symm r, (mapPiLocalization_bijective f hf).1 ?_⟩
  have := congrArg (fun g => g (e.symm r)) (mapPiLocalization_naturality f hf)
  have hfr : f (e.symm r) = r := e.apply_symm_apply r
  simp only [RingHom.coe_comp, Function.comp_apply, hfr] at this
  exact this.trans hr

end MaximalSpectrum

section Henselian

variable (A : Type u) [CommRing A] [HenselianLocalRing A]
  (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]

include A

/-- For a finite algebra `B` over a henselian local ring, the canonical map
`B → ∏_{𝔫} B_𝔫` (over the maximal ideals `𝔫` of `B`) is surjective. -/
theorem surjective_toPiLocalization_of_henselianLocalRing :
    Function.Surjective (MaximalSpectrum.toPiLocalization B) := by
  obtain ⟨ι, _, L, _, _, hL, -, ⟨e⟩⟩ :=
    exists_algEquiv_pi_henselianLocalRing_of_module_finite A B
  exact MaximalSpectrum.toPiLocalization_surjective_of_ringEquiv e.toRingEquiv
    (MaximalSpectrum.toPiLocalization_pi_surjective_of_isLocalRing L)

/-- A finite algebra over a henselian local ring has only finitely many maximal ideals. -/
@[weil "lem_fk103_finite_over_henselian_product_of_localizations"]
theorem finite_maximalSpectrum_of_henselianLocalRing : Finite (MaximalSpectrum B) :=
  MaximalSpectrum.finite_of_toPiLocalization_surjective
    (surjective_toPiLocalization_of_henselianLocalRing A B)

/-- For a finite algebra `B` over a henselian local ring, the canonical map
`B → ∏_{𝔫} B_𝔫` (over the finitely many maximal ideals `𝔫` of `B`) is bijective. -/
@[weil "lem_fk103_finite_over_henselian_product_of_localizations"]
theorem bijective_toPiLocalization_of_henselianLocalRing :
    Function.Bijective (MaximalSpectrum.toPiLocalization B) :=
  ⟨MaximalSpectrum.toPiLocalization_injective B,
    surjective_toPiLocalization_of_henselianLocalRing A B⟩

/-- The canonical isomorphism `B ≃ ∏_{𝔫} B_𝔫` for a finite algebra `B` over a henselian local
ring. -/
noncomputable def toPiLocalizationEquivOfHenselianLocalRing :
    B ≃ₐ[B] MaximalSpectrum.PiLocalization B :=
  AlgEquiv.ofBijective (MaximalSpectrum.toPiLocalization B)
    (bijective_toPiLocalization_of_henselianLocalRing A B)

@[simp]
theorem toPiLocalizationEquivOfHenselianLocalRing_apply (b : B) :
    toPiLocalizationEquivOfHenselianLocalRing A B b = MaximalSpectrum.toPiLocalization B b :=
  rfl

end Henselian

end
