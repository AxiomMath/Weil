module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleFiniteLimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.Attr

/-!
# Equivalence relations in the étale category

Let `S` be a scheme. An *equivalence relation in the étale category of `S`* is a pair of
morphisms `u, v : R ⟶ Y` of étale `S`-schemes such that the induced pair of representable
sheaves `R̃ ⇉ Ỹ` represents an equivalence relation of sheaves of sets: for every étale
`S`-scheme `T`, the map `R̃(T) → Ỹ(T) × Ỹ(T)` is injective and its image is an equivalence
relation on `Ỹ(T)`.

This is the internal equivalence relation `CategoryTheory.IsEquivalenceRelation u v` in the
small étale category: a jointly monic pair which is reflexive, symmetric and transitive. We
prove the two identifications this needs.

* In any category with fibre products, `p₁, p₂ : R ⟶ X` is an internal equivalence relation if
  and only if, for every object `T`, the map `Hom(T, R) → Hom(T, X) × Hom(T, X)` is injective and
  its image is an equivalence relation on `Hom(T, X)`
  (`CategoryTheory.isEquivalenceRelation_iff_forall_injective_and_equivalence`).
* Since the small étale topology is subcanonical, the Yoneda embedding into étale sheaves is
  fully faithful and preserves limits, so `u, v` is an equivalence relation exactly when the
  representable sheaves form one (`AlgebraicGeometry.SmallEtale.isEquivalenceRelation_iff_yoneda`).

## Main results

* `AlgebraicGeometry.SmallEtale.isEquivalenceRelation_iff_forall_injective_and_equivalence`:
  the sectionwise description of an equivalence relation in the small étale category.
* `AlgebraicGeometry.SmallEtale.isEquivalenceRelation_iff_yoneda`: `u, v` is an equivalence
  relation if and only if the pair of representable sheaves is.

## Implementation notes

No new definition is introduced: an equivalence relation in the étale category is Mathlib's
`CategoryTheory.IsEquivalenceRelation` in the small étale category
`AlgebraicGeometry.SmallEtale B S hS` of a big étale site, and the representable sheaf of `X` is
`AlgebraicGeometry.smallEtaleYoneda B S hS`. The objects range over all étale `S`-schemes in
the big étale site rather than the noetherian separated ones only.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- **Sectionwise description of internal equivalence relations.** In a category where the
pullback of `p₂` and `p₁` exists, the pair `p₁, p₂ : R ⟶ X` is an internal equivalence relation
if and only if, for every object `T`, the map `Hom(T, R) → Hom(T, X) × Hom(T, X)`,
`r ↦ (r ≫ p₁, r ≫ p₂)` is injective and its image is an equivalence relation on `Hom(T, X)`. -/
theorem isEquivalenceRelation_iff_forall_injective_and_equivalence {R X : C} (p₁ p₂ : R ⟶ X)
    [HasPullback p₂ p₁] :
    IsEquivalenceRelation p₁ p₂ ↔ ∀ T : C,
      Function.Injective (fun r : T ⟶ R ↦ (r ≫ p₁, r ≫ p₂)) ∧
        _root_.Equivalence (fun a b : T ⟶ X ↦ ∃ r : T ⟶ R, r ≫ p₁ = a ∧ r ≫ p₂ = b) := by
  constructor
  · rintro ⟨⟨e⟩⟩ T
    refine ⟨fun f g h ↦ e.right_cancellation f g (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2,
      ⟨fun a ↦ ⟨a ≫ e.r, by simp, by simp⟩, ?_, ?_⟩⟩
    · rintro a b ⟨r, rfl, rfl⟩
      exact ⟨r ≫ e.s, by rw [Category.assoc, e.symmetry₁], by rw [Category.assoc, e.symmetry₂]⟩
    · rintro a b c ⟨r, rfl, rfl⟩ ⟨r', hr', rfl⟩
      refine ⟨PullbackCone.IsLimit.lift e.isLimit r r' hr'.symm ≫ e.t, ?_, ?_⟩
      · rw [Category.assoc, e.transitivity₁, ← Category.assoc,
          PullbackCone.IsLimit.lift_fst]
      · rw [Category.assoc, e.transitivity₂, ← Category.assoc,
          PullbackCone.IsLimit.lift_snd]
  · intro h
    have hr := (h X).2.refl (𝟙 X)
    have hs := (h R).2.symm (x := p₁) (y := p₂) ⟨𝟙 R, Category.id_comp _, Category.id_comp _⟩
    have ht := (h (pullback p₂ p₁)).2.trans (x := pullback.fst p₂ p₁ ≫ p₁)
      (y := pullback.fst p₂ p₁ ≫ p₂) (z := pullback.snd p₂ p₁ ≫ p₂)
      ⟨pullback.fst p₂ p₁, rfl, rfl⟩ ⟨pullback.snd p₂ p₁, pullback.condition.symm, rfl⟩
    exact EquivalenceRelation.isEquivalenceRelation
      { right_cancellation := fun T f g h₁ h₂ ↦ (h T).1 (Prod.ext h₁ h₂)
        r := hr.choose
        reflexivity₁ := hr.choose_spec.1
        reflexivity₂ := hr.choose_spec.2
        s := hs.choose
        symmetry₁ := hs.choose_spec.1
        symmetry₂ := hs.choose_spec.2
        c := pullback.cone p₂ p₁
        isLimit := pullback.isLimit p₂ p₁
        t := ht.choose
        transitivity₁ := ht.choose_spec.1
        transitivity₂ := ht.choose_spec.2 }

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Equivalence relations in the étale category, sectionwise** (FK I.4). A pair
`u, v : R ⟶ Y` of morphisms of étale `S`-schemes is an equivalence relation in the small étale
category if and only if, for every étale `S`-scheme `T`, the map
`R̃(T) → Ỹ(T) × Ỹ(T)` of sections of the representable sheaves is injective and its image is an
equivalence relation on `Ỹ(T)`; that is, `R̃ ⇉ Ỹ` represents an equivalence relation of sheaves
of sets. -/
@[weil "def_fk104_etale_equivalence_relation"]
theorem isEquivalenceRelation_iff_forall_injective_and_equivalence {R Y : SmallEtale B S hS}
    (u v : R ⟶ Y) :
    IsEquivalenceRelation u v ↔ ∀ T : SmallEtale B S hS,
      Function.Injective (fun r : T ⟶ R ↦ (r ≫ u, r ≫ v)) ∧
        _root_.Equivalence (fun a b : T ⟶ Y ↦ ∃ r : T ⟶ R, r ≫ u = a ∧ r ≫ v = b) :=
  CategoryTheory.isEquivalenceRelation_iff_forall_injective_and_equivalence u v

/-- **Equivalence relations in the étale category are those of representable sheaves**
(FK I.4). A pair `u, v : R ⟶ Y` of morphisms of étale `S`-schemes is an equivalence relation in
the small étale category if and only if the induced pair `R̃ ⇉ Ỹ` of representable sheaves is an
equivalence relation in the category of étale sheaves of sets. -/
@[weil "def_fk104_etale_equivalence_relation"]
theorem isEquivalenceRelation_iff_yoneda {R Y : SmallEtale B S hS} (u v : R ⟶ Y) :
    IsEquivalenceRelation u v ↔
      IsEquivalenceRelation ((smallEtaleYoneda B S hS).map u) ((smallEtaleYoneda B S hS).map v) :=
  have : PreservesLimitsOfShape (Discrete WalkingPair) (smallEtaleYoneda B S hS) :=
    inferInstanceAs (PreservesLimitsOfShape _ (SmallEtale.topology B S hS).yoneda)
  have : PreservesLimitsOfShape WalkingCospan (smallEtaleYoneda B S hS) :=
    inferInstanceAs (PreservesLimitsOfShape _ (SmallEtale.topology B S hS).yoneda)
  ⟨isEquivalenceRelation_map (smallEtaleYoneda B S hS) u v,
    isEquivalenceRelation_of_map (smallEtaleYoneda B S hS) u v⟩

end AlgebraicGeometry.SmallEtale

end
