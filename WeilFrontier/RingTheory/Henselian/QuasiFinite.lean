module

public import Weil.Attr
public import StacksFrontier.RingTheory.Henselian.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.RingTheory.Flat.FlatteningHenselianReduction
public import WeilFrontier.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import WeilFrontier.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian

/-!
# Localizations of finite algebras over a henselian local ring are finite

Let `A` be a henselian local ring, `B` a finite `A`-algebra and `𝔫` a maximal ideal of `B`.
Then the localization `B_𝔫` is again finite over `A`.

Since `B` is integral over `A`, the contraction of `𝔫` to `A` is maximal, so `𝔫` lies over the
maximal ideal of `A`. A finite algebra is of finite type and quasi-finite, so the statement is the
fourth item of Stacks 04GH
(`HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt`).

## Main results

* `HenselianLocalRing.module_finite_of_isLocalization_atPrime_of_isMaximal`: `B_𝔫` is a finite
  `A`-module, for any localization `B_𝔫` of `B` at `𝔫`.

## Implementation notes

The source assumes `A` noetherian (its definition of a henselian ring is the Zariski main
theorem-style condition for noetherian local rings); the result holds for any henselian local
ring in Mathlib's sense, and is stated so. The localization is any `IsLocalization.AtPrime`
model in a scalar tower over `A`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
* [Stacks] Tag 04GH.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace HenselianLocalRing

/-- Let `A` be a henselian local ring, `B` a finite `A`-algebra and `𝔫` a maximal ideal of `B`.
Then every localization `B_𝔫` of `B` at `𝔫` is a finite `A`-module. -/
@[weil "lem_fk103_localization_of_finite_over_henselian_is_finite"]
theorem module_finite_of_isLocalization_atPrime_of_isMaximal
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Module.Finite A B]
    (𝔫 : Ideal B) [𝔫.IsMaximal]
    (Bn : Type w) [CommRing Bn] [Algebra A Bn] [Algebra B Bn] [IsScalarTower A B Bn]
    [IsLocalization.AtPrime Bn 𝔫] :
    Module.Finite A Bn := by
  have : (𝔫.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
  have : 𝔫.LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal this).symm⟩
  exact ((henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt A).2.2.2 B
    inferInstance inferInstance 𝔫 Bn).2

end HenselianLocalRing

end

/-! ### Localizations of finite algebras over a henselian local ring are henselian -/

/-!
# Localizations of finite algebras over a henselian local ring are henselian

Let `R` be a henselian local ring and `S` a finite `R`-algebra. For every maximal ideal `𝔫` of
`S`, the localization `S_𝔫` is a henselian local ring.

Since `S` is integral over `R`, the contraction of `𝔫` to `R` is maximal, hence is the maximal
ideal of `R`; a finite algebra is of finite type and quasi-finite, so the claim is a special case
of the structure theorem for quasi-finite algebras over a henselian local ring (Stacks 04GH (4)).

## Main results

* `HenselianLocalRing.of_isLocalization_atPrime_of_finite`: `S_𝔫` is henselian, for any
  localization `S_𝔫` of a finite `R`-algebra `S` at a maximal ideal `𝔫`.

## Implementation notes

The localization is any `IsLocalization.AtPrime Sn 𝔫` in a scalar tower over `R`, rather than
the specific `Localization.AtPrime 𝔫`. Henselian is Mathlib's `HenselianLocalRing`; no
noetherian hypothesis is needed.

## References

* [FK] Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
* [Stacks 04GH](https://stacks.math.columbia.edu/tag/04GH)
-/

@[expose] public section

universe u v w

open IsLocalRing

/-- If `R` is a henselian local ring, `S` a finite `R`-algebra and `𝔫` a maximal ideal of `S`,
then the localization `S_𝔫` is a henselian local ring. -/
@[weil "lem_fk103_finite_over_henselian_factors_henselian"]
theorem HenselianLocalRing.of_isLocalization_atPrime_of_finite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    (𝔫 : Ideal S) [𝔫.IsMaximal]
    (Sn : Type w) [CommRing Sn] [Algebra R Sn] [Algebra S Sn] [IsScalarTower R S Sn]
    [IsLocalization.AtPrime Sn 𝔫] :
    HenselianLocalRing Sn := by
  have hmax : (𝔫.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔫
  have : 𝔫.LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
  exact ((HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt R).2.2.2
    S inferInstance inferInstance 𝔫 Sn).1

end

/-! ### Local-étale homomorphisms out of a strictly henselian local ring -/

/-!
# Local-étale homomorphisms out of a strictly henselian local ring

Let `A` be a strictly henselian local ring and `A → B` a local homomorphism to a local ring `B`
which is flat, formally unramified and essentially of finite type. Then `A → B` is bijective.

The proof: `B` is quasi-finite over `A` (being formally unramified and essentially of finite
type), so `B` is the localization of a finite type `A`-algebra at a prime over `𝔪(A)` at which it
is quasi-finite, and henselianity of `A` makes `B` finite over `A` (Stacks 04GH). Unramifiedness
gives `𝔪(A) B = 𝔪(B)` and a separable residue field extension, which is trivial since the residue
field of `A` is separably closed; hence `B = A · 1 + 𝔪(A) B`, and Nakayama's lemma makes
`A → B` surjective. A flat local homomorphism of local rings is faithfully flat, hence injective.

## Main results

* `HenselianLocalRing.module_finite_of_essFiniteType_of_quasiFinite`: a local, quasi-finite,
  essentially finite type algebra over a henselian local ring is finite.
* `Algebra.bijective_algebraMap_of_flat_of_formallyUnramified`: the statement for a henselian
  local ring with separably closed residue field and a flat, formally unramified, essentially
  finite type local algebra; no noetherian hypothesis is needed.
* `RingHom.bijective_algebraMap_of_isEtaleLocalHom`: a local-étale homomorphism
  (`RingHom.IsEtaleLocalHom`) out of a strictly henselian noetherian local ring is bijective.

## Implementation notes

"Isomorphism" is stated as bijectivity of the algebra map; `RingEquiv.ofBijective` turns it into
a ring isomorphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
* [Stacks Project, Tag 04GH](https://stacks.math.columbia.edu/tag/04GH)
-/

@[expose] public section

open IsLocalRing

universe u v

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

open Algebra in
/-- A local algebra which is quasi-finite and essentially of finite type over a henselian local
ring is finite. -/
theorem HenselianLocalRing.module_finite_of_essFiniteType_of_quasiFinite [HenselianLocalRing A]
    [IsLocalHom (algebraMap A B)] [EssFiniteType A B] [QuasiFinite A B] :
    Module.Finite A B := by
  obtain ⟨C, _, _, _, _, _, hloc⟩ := EssFiniteType.exists_finiteType_isLocalization_atPrime A B
  set q : Ideal C := (maximalIdeal B).comap (algebraMap C B)
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : IsLocalization.AtPrime B q := hloc
  have : q.LiesOver (maximalIdeal A) := by
    constructor
    rw [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsLocalRing.maximalIdeal_comap]
  have hqf : QuasiFiniteAt A q := by
    let e : Localization.AtPrime q ≃ₐ[C] B := IsLocalization.algEquiv q.primeCompl _ B
    exact (QuasiFinite.iff_of_algEquiv (e.restrictScalars A)).mpr inferInstance
  exact ((HenselianLocalRing.henselianLocalRing_and_finite_of_finite_of_quasiFiniteAt A).2.2.1
    C inferInstance q hqf B).2

namespace Algebra

/-- Let `A` be a henselian local ring with separably closed residue field, and `B` a local ring
which is a flat, formally unramified, essentially finite type local `A`-algebra. Then the
algebra map `A → B` is bijective. -/
theorem bijective_algebraMap_of_flat_of_formallyUnramified [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] [IsLocalHom (algebraMap A B)] [EssFiniteType A B]
    [Module.Flat A B] [FormallyUnramified A B] :
    Function.Bijective (algebraMap A B) := by
  have : Module.Finite A B :=
    HenselianLocalRing.module_finite_of_essFiniteType_of_quasiFinite A B
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨FaithfulSMul.algebraMap_injective A B, ?_⟩
  -- every element of `B` is congruent to an element of `A` modulo `𝔪(B) = 𝔪(A) B`
  have hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)) :=
    IsSepClosed.algebraMap_surjective _ _
  let N : Submodule A B := LinearMap.range (Algebra.linearMap A B)
  have hle : (⊤ : Submodule A B) ≤ N ⊔ maximalIdeal A • (⊤ : Submodule A B) := by
    intro b _
    obtain ⟨x, hx⟩ := hres (residue B b)
    obtain ⟨a, rfl⟩ := residue_surjective x
    have hmem : b - algebraMap A B a ∈ maximalIdeal B := by
      rw [← residue_eq_zero_iff, map_sub, ← hx, ResidueField.algebraMap_residue,
        sub_self]
    rw [← FormallyUnramified.map_maximalIdeal (R := A)] at hmem
    have hmem' : b - algebraMap A B a ∈ maximalIdeal A • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]
      exact hmem
    have hN : algebraMap A B a ∈ N := ⟨a, rfl⟩
    simpa using Submodule.add_mem_sup hN hmem'
  have := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (maximalIdeal_le_jacobson _) hle
  intro b
  obtain ⟨a, ha⟩ := this (Submodule.mem_top (x := b))
  exact ⟨a, ha⟩

end Algebra

namespace RingHom

/-- Let `A` be a strictly henselian noetherian local ring. Every local-étale homomorphism
`A → B` of noetherian local rings is bijective, hence an isomorphism. -/
@[weil "lem_fk101_strictly_henselian_local_etale_is_iso"]
theorem bijective_algebraMap_of_isEtaleLocalHom {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing B] [StrictlyHenselianLocalRing A] [IsLocalHom (algebraMap A B)]
    (h : (algebraMap A B).IsEtaleLocalHom) :
    Function.Bijective (algebraMap A B) := by
  obtain ⟨hf, hu, he⟩ := h
  have : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hf
  have : Algebra.FormallyUnramified A B := RingHom.formallyUnramified_algebraMap.mp hu
  have : Algebra.EssFiniteType A B := RingHom.essFiniteType_algebraMap.mp he
  exact Algebra.bijective_algebraMap_of_flat_of_formallyUnramified A B

end RingHom

end
