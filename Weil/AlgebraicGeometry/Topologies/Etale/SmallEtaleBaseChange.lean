module

public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleFiniteLimits
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import Mathlib.CategoryTheory.Sites.PreservesLimits

/-!
# Base change of equivalence relations in the small étale site

Let `u, v : R ⟶ Y` be an equivalence relation in the small étale category of a scheme `S`, and
let `f : T ⟶ S` be a morphism. Then the base change `R ×_S T ⇉ Y ×_S T` is an equivalence
relation in the small étale category of `T`.

This is an instance of a general fact: a functor between categories with binary products which
preserves binary products and fibre products carries internal equivalence relations to internal
equivalence relations (`CategoryTheory.isEquivalenceRelation_map`). Indeed, a pair
`p₁, p₂ : R ⟶ A` is jointly monic exactly when `(p₁, p₂) : R ⟶ A × A` is a monomorphism; a
functor preserving fibre products preserves monomorphisms, and one preserving binary products
identifies the image of `(p₁, p₂)` with `(F p₁, F p₂)` up to the comparison isomorphism.
Reflexivity, symmetry and transitivity are transported along the functor. Small étale base
change preserves finite limits (`AlgebraicGeometry.preservesFiniteLimits_smallEtaleBaseChange`).

## Main results

* `AlgebraicGeometry.isEquivalenceRelation_smallEtaleBaseChange`: base change of an equivalence
  relation in the small étale category of `S` along `f : T ⟶ S` is an equivalence relation in
  the small étale category of `T`.

## Implementation notes

An equivalence relation in the étale category is Mathlib's internal equivalence relation
`CategoryTheory.IsEquivalenceRelation` in the small étale category `AlgebraicGeometry.SmallEtale`
of a big étale site; since the étale topology is subcanonical and the Yoneda embedding is fully
faithful and preserves limits, this is the same as asking that the representable sheaves form an
equivalence relation of sheaves. The base change is `AlgebraicGeometry.smallEtaleBaseChange`,
whose objects are the fibre products `R ×_S T`. The proof goes through the categorical
characterisation instead of testing on points with values in `T`-schemes and the open immersion
`R ⟶ Y ×_S Y`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Base change of an étale equivalence relation** (FK I.4). Let `u, v : R ⟶ Y` be an
equivalence relation in the small étale category of `S`, and `f : T ⟶ S` a morphism of the big
étale site. Then the base change `R ×_S T ⇉ Y ×_S T` is an equivalence relation in the small
étale category of `T`. -/
@[weil "lem_fk104_etale_equivalence_relation_base_change"]
theorem isEquivalenceRelation_smallEtaleBaseChange (B : BigEtaleSite.{u}) {S T : B.Scheme}
    (f : T ⟶ S) {R Y : SmallEtale B S.obj S.property} (u v : R ⟶ Y)
    [h : IsEquivalenceRelation u v] :
    IsEquivalenceRelation ((smallEtaleBaseChange B f).map u) ((smallEtaleBaseChange B f).map v) :=
  isEquivalenceRelation_map (smallEtaleBaseChange B f) u v h

end AlgebraicGeometry

end

/-! ### Base change of representable equivalence relations on the small étale site -/

/-!
# Base change of representable equivalence relations on the small étale site

Let `f : T ⟶ S` be a morphism of schemes and `r₁ r₂ : R ⟶ H` morphisms of étale `S`-schemes
such that the pair of morphisms of represented sheaves `R̃ ⇉ H̃` is an equivalence relation in
the category of étale sheaves of sets on `S`. Then the base-changed pair
`r₁ ×_S T, r₂ ×_S T : R ×_S T ⇉ H ×_S T` of étale `T`-schemes again represents an equivalence
relation of étale sheaves on `T`.

Since the étale topology is subcanonical, the Yoneda embedding of the small étale site into its
topos is fully faithful and preserves limits, so `R̃ ⇉ H̃` is an equivalence relation of sheaves
if and only if `R ⇉ H` is an internal equivalence relation of étale `S`-schemes (a jointly monic
pair with reflexivity, symmetry and transitivity morphisms). Base change preserves finite limits,
hence carries internal equivalence relations to internal equivalence relations.

## Main results

* `AlgebraicGeometry.isEquivalenceRelation_smallEtaleYoneda_map_iff`: `R̃ ⇉ H̃` is an
  equivalence relation of étale sheaves if and only if `R ⇉ H` is an internal equivalence
  relation in the small étale category.
* `AlgebraicGeometry.isEquivalenceRelation_smallEtaleYoneda_map_smallEtaleBaseChange`: base
  change along `f : T ⟶ S` preserves representable equivalence relations of étale sheaves.

## Implementation notes

The statement is on the small étale site of all étale schemes over `S` (rather than only the
noetherian separated ones), with the base and target schemes in a big étale site; no
noetherian or separatedness hypothesis is needed. The fibre product `R ×_S T` with its morphism
to `T` is `AlgebraicGeometry.smallEtaleBaseChange`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §4.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}}

/-- A pair `r₁ r₂ : R ⟶ H` of morphisms of étale `S`-schemes represents an equivalence relation
of étale sheaves (the pair `R̃ ⇉ H̃` is an equivalence relation in the étale topos) if and only
if it is an internal equivalence relation in the small étale category of `S`. -/
theorem isEquivalenceRelation_smallEtaleYoneda_map_iff {S : Scheme.{u}} {hS : B.Contains S}
    {R H : SmallEtale B S hS} (r₁ r₂ : R ⟶ H) :
    IsEquivalenceRelation ((smallEtaleYoneda B S hS).map r₁) ((smallEtaleYoneda B S hS).map r₂) ↔
      IsEquivalenceRelation r₁ r₂ := by
  refine ⟨fun h => isEquivalenceRelation_of_map (smallEtaleYoneda B S hS) r₁ r₂ h,
    fun h => ?_⟩
  have : PreservesLimitsOfShape (Discrete WalkingPair) (smallEtaleYoneda B S hS) :=
    inferInstanceAs (PreservesLimitsOfShape _ (SmallEtale.topology B S hS).yoneda)
  have : PreservesLimitsOfShape WalkingCospan (smallEtaleYoneda B S hS) :=
    inferInstanceAs (PreservesLimitsOfShape _ (SmallEtale.topology B S hS).yoneda)
  exact isEquivalenceRelation_map (smallEtaleYoneda B S hS) r₁ r₂ h

/-- **Base change of representable equivalence relations.** Let `f : T ⟶ S` be a morphism of
schemes and `r₁ r₂ : R ⟶ H` morphisms of étale `S`-schemes such that `R̃ ⇉ H̃` is an equivalence
relation of étale sheaves of sets on `S`. Then for `R' = R ×_S T`, `H' = H ×_S T` and
`rᵢ' = rᵢ ×_S T`, the pair `R̃' ⇉ H̃'` is an equivalence relation of étale sheaves of sets
on `T`. -/
@[weil "lem_fk104_equivalence_relation_base_change"]
theorem isEquivalenceRelation_smallEtaleYoneda_map_smallEtaleBaseChange {S T : B.Scheme}
    (f : T ⟶ S) {R H : SmallEtale B S.obj S.property} (r₁ r₂ : R ⟶ H)
    (h : IsEquivalenceRelation ((smallEtaleYoneda B S.obj S.property).map r₁)
      ((smallEtaleYoneda B S.obj S.property).map r₂)) :
    IsEquivalenceRelation
      ((smallEtaleYoneda B T.obj T.property).map ((smallEtaleBaseChange B f).map r₁))
      ((smallEtaleYoneda B T.obj T.property).map ((smallEtaleBaseChange B f).map r₂)) := by
  rw [isEquivalenceRelation_smallEtaleYoneda_map_iff] at h ⊢
  exact isEquivalenceRelation_map (smallEtaleBaseChange B f) r₁ r₂ h

end AlgebraicGeometry
