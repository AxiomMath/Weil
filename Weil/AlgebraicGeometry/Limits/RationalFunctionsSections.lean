module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.Topology.Sober.Generization
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic

/-!
# The generic fibre of an étale morphism

Let `φ : U ⟶ X` be an étale morphism of schemes and let `η_X = ∐_η Spec κ(η)` be the scheme of
generic points of `X`, with its canonical morphism `j_X : η_X ⟶ X`. Then a point `u` of `U` is a
generic point of an irreducible component of `U` if and only if `φ u` is a generic point of an
irreducible component of `X`, and the canonical morphism `j_U : η_U ⟶ U` factors through the
projection `U ×_X η_X ⟶ U` by an isomorphism `η_U ≅ U ×_X η_X`. In words: the generic fibre of
an étale morphism is the disjoint union of the spectra of the residue fields at the generic points
of the source.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.genericPointsSchemeMap`: for `φ` flat, the morphism
  `η_U ⟶ η_X` induced on schemes of generic points.
- `AlgebraicGeometry.Scheme.Hom.genericPointsSchemeToPullback`: the morphism
  `η_U ⟶ U ×_X η_X` whose composite with the projection to `U` is `j_U`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.mem_genericPoints_iff_of_etale`: for `φ` étale, `φ u` is a
  generic point of `X` if and only if `u` is a generic point of `U`.
- `AlgebraicGeometry.Scheme.Hom.isIso_genericPointsSchemeToPullback`: for `φ` étale, the morphism
  `η_U ⟶ U ×_X η_X` is an isomorphism.
- `AlgebraicGeometry.Scheme.Hom.genericPointsSchemeToPullback_fst`: its composite with the
  projection `U ×_X η_X ⟶ U` is `j_U`.

## Implementation notes

The statement is proved for an arbitrary étale morphism `φ : U ⟶ X` of schemes. The source states
it for `X` a smooth curve over a field, where `U` is again a smooth curve; neither the base field,
smoothness of `X`, nor finiteness of the set of irreducible components is used. The proof shows that
each summand `Spec κ(ξ) ⟶ U ×_X η_X` is étale (being a morphism between étale `η_X`-schemes,
since `κ(ξ)` is a finite separable extension of `κ(φ ξ)`) and a monomorphism (its composite with
the projection to `U` is `U.fromSpecResidueField ξ`), hence an open immersion; these open
immersions have pairwise disjoint images, and they cover `U ×_X η_X` because `j_X` is universally
injective and every point of `U` over a generic point of `X` is a generic point of `U`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (φ : U ⟶ X)

/-- A morphism with discrete fibres (for instance a locally quasi-finite one) reflects generic
points of irreducible components. -/
theorem mem_genericPoints_of_locallyQuasiFinite [LocallyQuasiFinite φ] {u : U}
    (hu : φ u ∈ genericPoints X) : u ∈ genericPoints U := by
  rw [TopologicalSpace.mem_genericPoints_iff_forall_specializes_eq] at hu ⊢
  intro y hy
  have hφ : φ y = φ u := hu _ (hy.map φ.continuous)
  have := (φ.isDiscrete_preimage_singleton (φ u)).to_subtype
  have hsub : (⟨y, hφ⟩ : ↥(φ ⁻¹' {φ u})) ⤳ ⟨u, rfl⟩ := by
    rwa [← Topology.IsInducing.subtypeVal.specializes_iff]
  exact congrArg Subtype.val hsub.eq

/-- **Étale morphisms preserve and reflect generic points**: for `φ : U ⟶ X` étale, `φ u` is the
generic point of an irreducible component of `X` if and only if `u` is the generic point of an
irreducible component of `U`. -/
theorem mem_genericPoints_iff_of_etale [Etale φ] (u : U) :
    φ u ∈ genericPoints X ↔ u ∈ genericPoints U :=
  have : LocallyQuasiFinite φ := (locallyQuasiFinite_of_etale φ).2
  ⟨φ.mem_genericPoints_of_locallyQuasiFinite, φ.mem_genericPoints_of_flat⟩

/-- For `φ : U ⟶ X` étale and `x : U`, the morphism `Spec κ(x) ⟶ Spec κ(φ x)` induced by the
residue field extension is étale: `κ(x)` is a finite separable extension of `κ(φ x)`. -/
instance etale_SpecMap_residueFieldMap [Etale φ] (x : U) :
    Etale (Spec.map (φ.residueFieldMap x)) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  algebraize [(φ.residueFieldMap x).hom]
  have : Algebra.EssFiniteType (X.residueField (φ x)) (U.residueField x) := by
    rw [← RingHom.essFiniteType_algebraMap]
    exact RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap φ x)
  have : Algebra.FormallyUnramified (X.residueField (φ x)) (U.residueField x) :=
    Algebra.FormallyUnramified.of_isSeparable _ _
  have : Algebra.FormallyEtale (X.residueField (φ x)) (U.residueField x) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Module.Finite (X.residueField (φ x)) (U.residueField x) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.FinitePresentation (X.residueField (φ x)) (U.residueField x) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩

/-- For `φ` flat, the morphism `η_U ⟶ η_X` of schemes of generic points: on the summand
`Spec κ(ξ)` it is `Spec κ(ξ) ⟶ Spec κ(φ ξ)` followed by the inclusion of that summand. -/
noncomputable def genericPointsSchemeMap [Flat φ] :
    U.genericPointsScheme ⟶ X.genericPointsScheme :=
  Sigma.desc fun ξ : genericPoints U => Spec.map (φ.residueFieldMap ξ) ≫
    X.genericPointsSchemeι ⟨φ ξ, φ.mem_genericPoints_of_flat ξ.2⟩

@[reassoc (attr := simp)]
theorem genericPointsSchemeι_genericPointsSchemeMap [Flat φ] (ξ : genericPoints U) :
    U.genericPointsSchemeι ξ ≫ φ.genericPointsSchemeMap =
      Spec.map (φ.residueFieldMap ξ) ≫
        X.genericPointsSchemeι ⟨φ ξ, φ.mem_genericPoints_of_flat ξ.2⟩ :=
  Sigma.ι_desc _ _

@[reassoc]
theorem genericPointsSchemeMap_genericPointsMorphism [Flat φ] :
    φ.genericPointsSchemeMap ≫ X.genericPointsMorphism = U.genericPointsMorphism ≫ φ :=
  Scheme.genericPointsScheme_hom_ext _ fun ξ => by
    simp [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]

/-- For `φ` flat, the morphism `η_U ⟶ U ×_X η_X` whose components are `j_U` and the induced
morphism `η_U ⟶ η_X`. -/
noncomputable def genericPointsSchemeToPullback [Flat φ] :
    U.genericPointsScheme ⟶ pullback φ X.genericPointsMorphism :=
  pullback.lift U.genericPointsMorphism φ.genericPointsSchemeMap
    (φ.genericPointsSchemeMap_genericPointsMorphism).symm

/-- **The canonical morphism `η_U ⟶ U` factors through the projection `U ×_X η_X ⟶ U`.** -/
@[reassoc (attr := simp), weil "lem_fk105_rational_functions_sections"]
theorem genericPointsSchemeToPullback_fst [Flat φ] :
    φ.genericPointsSchemeToPullback ≫ pullback.fst φ X.genericPointsMorphism =
      U.genericPointsMorphism :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem genericPointsSchemeToPullback_snd [Flat φ] :
    φ.genericPointsSchemeToPullback ≫ pullback.snd φ X.genericPointsMorphism =
      φ.genericPointsSchemeMap :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The canonical morphism `j_X : η_X ⟶ X` is universally injective: a morphism from the
spectrum of a field to `η_X` lands in one summand `Spec κ(η)`, and `Spec κ(η) ⟶ X` is a
monomorphism. -/
instance universallyInjective_genericPointsMorphism :
    UniversallyInjective X.genericPointsMorphism := by
  refine ((tfae_universallyInjective X.genericPointsMorphism).out 1 2).mpr ?_
  intro K _ g₁ g₂ hg
  dsimp only at hg
  obtain ⟨pt⟩ : Nonempty (Spec (.of K)) := ⟨IsLocalRing.closedPoint K⟩
  have hpt (y : Spec (.of K)) : y = pt :=
    Subsingleton.elim (α := PrimeSpectrum K) _ _
  obtain ⟨η, a, ha⟩ := X.exists_genericPointsSchemeι_eq (g₁ pt)
  obtain ⟨η', b, hb⟩ := X.exists_genericPointsSchemeι_eq (g₂ pt)
  have hj (η : genericPoints X) (a : Spec (X.residueField η)) :
      X.genericPointsMorphism (X.genericPointsSchemeι η a) = η := by
    rw [← Scheme.Hom.comp_apply, ι_genericPointsMorphism, fromSpecResidueField_apply]
  have hηη' : η = η' := by
    apply Subtype.ext
    rw [← hj η a, ← hj η' b, ha, hb, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]
  subst hηη'
  have : IsOpenImmersion (X.genericPointsSchemeι η) :=
    inferInstanceAs (IsOpenImmersion (Sigma.ι _ _))
  have h₁ : Set.range g₁ ⊆ Set.range (X.genericPointsSchemeι η) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨a, by rw [ha, hpt y]⟩
  have h₂ : Set.range g₂ ⊆ Set.range (X.genericPointsSchemeι η) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨b, by rw [hb, hpt y]⟩
  rw [← IsOpenImmersion.lift_fac _ g₁ h₁, ← IsOpenImmersion.lift_fac _ g₂ h₂]
  congr 1
  rw [← cancel_mono (X.fromSpecResidueField η), ← ι_genericPointsMorphism,
    ← Category.assoc, ← Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, hg]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (φ : U ⟶ X)

/-- **The generic fibre of an étale morphism is the disjoint union of the spectra of the residue
fields at the generic points of the source**: for `φ : U ⟶ X` étale, the canonical morphism
`η_U ⟶ U ×_X η_X` is an isomorphism. -/
@[weil "lem_fk105_rational_functions_sections"]
theorem isIso_genericPointsSchemeToPullback [Etale φ] :
    IsIso φ.genericPointsSchemeToPullback := by
  set f := φ.genericPointsSchemeToPullback
  let s : ∀ ξ : genericPoints U, Spec (U.residueField ξ) ⟶ pullback φ X.genericPointsMorphism :=
    fun ξ => U.genericPointsSchemeι ξ ≫ f
  have hf : f = Sigma.desc s := Sigma.hom_ext _ _ fun ξ => (Sigma.ι_desc s ξ).symm
  have hs_fst (ξ : genericPoints U) :
      s ξ ≫ pullback.fst φ X.genericPointsMorphism = U.fromSpecResidueField ξ := by
    simp [s, f]
  have hs_snd (ξ : genericPoints U) :
      s ξ ≫ pullback.snd φ X.genericPointsMorphism = Spec.map (φ.residueFieldMap ξ) ≫
        X.genericPointsSchemeι ⟨φ ξ, φ.mem_genericPoints_of_flat ξ.2⟩ := by
    simp [s, f]
  have hs_open (ξ : genericPoints U) : IsOpenImmersion (s ξ) := by
    have : Mono (s ξ) := mono_of_mono_fac (hs_fst ξ)
    have : IsOpenImmersion (X.genericPointsSchemeι ⟨φ ξ, φ.mem_genericPoints_of_flat ξ.2⟩) :=
      inferInstanceAs (IsOpenImmersion (Sigma.ι _ _))
    have : Etale (s ξ ≫ pullback.snd φ X.genericPointsMorphism) := by
      rw [hs_snd]; infer_instance
    have : Etale (s ξ) := Etale.of_comp _ (pullback.snd φ X.genericPointsMorphism)
    exact IsOpenImmersion.of_flat_of_mono _
  have hs_range (ξ : genericPoints U) (y : Spec (U.residueField ξ)) :
      pullback.fst φ X.genericPointsMorphism (s ξ y) = ξ := by
    rw [← Scheme.Hom.comp_apply, hs_fst, fromSpecResidueField_apply]
  have hopen : IsOpenImmersion f := by
    rw [hf]
    refine isOpenImmersion_sigmaDesc _ _ fun ξ ξ' hξ => ?_
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, rfl⟩ ⟨y', hy'⟩
    apply hξ
    apply Subtype.ext
    rw [← hs_range ξ y, ← hs_range ξ' y', hy']
  have hsurj : Surjective f := by
    refine ⟨fun p => ?_⟩
    obtain ⟨η, a, ha⟩ := X.exists_genericPointsSchemeι_eq (pullback.snd φ X.genericPointsMorphism p)
    have h1 : φ (pullback.fst φ X.genericPointsMorphism p) = η := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← ha,
        ← Scheme.Hom.comp_apply, ι_genericPointsMorphism, fromSpecResidueField_apply]
    let ξ : genericPoints U := ⟨pullback.fst φ X.genericPointsMorphism p,
      (φ.mem_genericPoints_iff_of_etale _).1 (h1 ▸ η.2)⟩
    obtain ⟨pt⟩ : Nonempty (Spec (U.residueField ξ)) := ⟨IsLocalRing.closedPoint _⟩
    refine ⟨U.genericPointsSchemeι ξ pt, ?_⟩
    have : UniversallyInjective (pullback.fst φ X.genericPointsMorphism) :=
      MorphismProperty.of_isPullback (P := @UniversallyInjective)
        (IsPullback.of_hasPullback φ X.genericPointsMorphism).flip inferInstance
    apply (pullback.fst φ X.genericPointsMorphism).injective
    change pullback.fst φ X.genericPointsMorphism (s ξ _) = _
    rw [hs_range]
  exact (isIso_iff_isOpenImmersion_and_surjective f).mpr ⟨hopen, hsurj⟩

end AlgebraicGeometry.Scheme.Hom
