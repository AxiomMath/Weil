module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Weil.Defs.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringIsomorphism
public import Weil.Defs.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringSpace
public import Weil.Attr

/-!
# Base change of Galois covering spaces

Let `F` be a finite group, `Y → X` an `F`-Galois covering space and `h : X' → X` a morphism of
schemes. Then `Y ×_X X' → X'`, with `F` acting by `σ × id_{X'}`, is an `F`-Galois covering space
of `X'`: étale and surjective morphisms are stable under base change, and the morphism
`∐_{σ ∈ F} (Y ×_X X') → (Y ×_X X') ×_{X'} (Y ×_X X')` is the base change of the isomorphism
`∐_{σ ∈ F} Y → Y ×_X Y`, since pullbacks commute with finite coproducts of schemes.
Base change is functorial, so an isomorphism of `F`-Galois covering spaces `Y → Z` over `X`
induces one `Y ×_X X' → Z ×_X X'` over `X'`.

## Main definitions

* `AlgebraicGeometry.GaloisCovering.pullback h` — the base change functor
  `GaloisCovering X F ⥤ GaloisCovering X' F` along `h : X' ⟶ X`.

## Main results

* `AlgebraicGeometry.IsGaloisCovering.pullback` — the base change of an `F`-Galois covering
  space, with the induced action, is an `F`-Galois covering space.
* `AlgebraicGeometry.GaloisCovering.isoOver_pullback_mapIso` — the isomorphism of base changes
  induced by an isomorphism `e` of `F`-Galois covering spaces is the base change of `e`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {X X' : Scheme.{u}} {F : Type u} [Group F]

namespace IsGaloisCovering

variable {W V T S : Scheme.{u}} {p : W ⟶ V} {q : W ⟶ T} {f : V ⟶ S} {g : T ⟶ S}

/-- In a cartesian square `W = V ×_S T`, the self-product `W ×_T W` is the base change of
`V ×_S V` along the second projection. -/
lemma isPullback_snd_pullbackMap (H : IsPullback p q f g) :
    IsPullback (pullback.snd q q) (pullback.map q q f f p p g H.w.symm H.w.symm) p
      (pullback.snd f f) := by
  have hrf : pullback.map q q f f p p g H.w.symm H.w.symm ≫ pullback.fst f f =
      pullback.fst q q ≫ p := pullback.lift_fst _ _ _
  have hrs : pullback.map q q f f p p g H.w.symm H.w.symm ≫ pullback.snd f f =
      pullback.snd q q ≫ p := pullback.lift_snd _ _ _
  have ho : IsPullback (pullback.map q q f f p p g H.w.symm H.w.symm ≫ pullback.fst f f)
      (pullback.snd q q) f (p ≫ f) := by
    rw [hrf, H.w]
    exact (IsPullback.of_hasPullback q q).paste_horiz H
  exact (ho.of_right hrs (IsPullback.of_hasPullback f f)).flip

/-- In a cartesian square `W = V ×_S T` whose top map intertwines an endomorphism `b` of `W`
over `T` with an endomorphism `a` of `V` over `S`, the graph `(b, id)` of `b` is the base change
of the graph `(a, id)` of `a`. -/
lemma isPullback_lift_lift_id (H : IsPullback p q f g) (a : V ⟶ V) (ha : a ≫ f = f)
    (b : W ⟶ W) (hb : b ≫ q = q) (hab : b ≫ p = p ≫ a) :
    IsPullback (pullback.lift b (𝟙 W) (by rw [Category.id_comp, hb])) p
      (pullback.map q q f f p p g H.w.symm H.w.symm)
      (pullback.lift a (𝟙 V) (by rw [Category.id_comp, ha])) := by
  have hw : pullback.lift b (𝟙 W) (by rw [Category.id_comp, hb]) ≫
      pullback.map q q f f p p g H.w.symm H.w.symm =
      p ≫ pullback.lift a (𝟙 V) (by rw [Category.id_comp, ha]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      simp only [hab]
      exact congrArg (p ≫ ·) (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      simp only [Category.id_comp]
      exact (Category.comp_id p).symm.trans (congrArg (p ≫ ·) (pullback.lift_snd _ _ _).symm)
  have ho : IsPullback
      (pullback.lift b (𝟙 W) (by rw [Category.id_comp, hb]) ≫ pullback.snd q q) p p
      (pullback.lift a (𝟙 V) (by rw [Category.id_comp, ha]) ≫ pullback.snd f f) := by
    rw [pullback.lift_snd, pullback.lift_snd]
    exact IsPullback.id_horiz p
  exact ho.of_right hw (isPullback_snd_pullbackMap H)

variable [Finite F]

/-- The morphism `∐_{σ ∈ F} (Y ×_X X') → (Y ×_X X') ×_{X'} (Y ×_X X')` of the base change is
the base change of the morphism `∐_{σ ∈ F} Y → Y ×_X Y`. -/
lemma isPullback_galoisCoveringMap_pullback (h : X' ⟶ X) (Y : Over X) (ρ : F →* Aut Y) :
    IsPullback (galoisCoveringMap ((Over.pullback h).obj Y)
        (((Over.pullback h).mapAut Y).comp ρ))
      (Sigma.desc fun σ : F ↦ pullback.fst Y.hom h ≫ Sigma.ι (fun _ : F ↦ Y.left) σ)
      (pullback.map _ _ Y.hom Y.hom (pullback.fst Y.hom h) (pullback.fst Y.hom h) h
        (IsPullback.of_hasPullback Y.hom h).w.symm (IsPullback.of_hasPullback Y.hom h).w.symm)
      (galoisCoveringMap Y ρ) := by
  have H := IsPullback.of_hasPullback Y.hom h
  have hu : IsUniversalColimit (Cofan.mk _ (Sigma.ι fun _ : F ↦ Y.left)) :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _)
  exact hu.isPullback_of_isColimit_left
    (fun σ ↦ pullback.lift (ρ σ).hom.left (𝟙 Y.left) (by simp))
    (galoisCoveringMap Y ρ)
    (pullback.map _ _ Y.hom Y.hom (pullback.fst Y.hom h) (pullback.fst Y.hom h) h H.w.symm H.w.symm)
    (fun σ ↦ pullback.lift ((((Over.pullback h).mapAut Y).comp ρ) σ).hom.left (𝟙 _) (by
      rw [Category.id_comp]; exact Over.w ((((Over.pullback h).mapAut Y).comp ρ) σ).hom))
    (fun _ ↦ pullback.fst Y.hom h)
    (fun σ ↦ isPullback_lift_lift_id H _ (Over.w (ρ σ).hom) _
      (Over.w ((((Over.pullback h).mapAut Y).comp ρ) σ).hom) (pullback.lift_fst _ _ _))
    (coproductIsCoproduct _) (fun σ ↦ by
      change Sigma.ι _ σ ≫ galoisCoveringMap Y ρ = _
      exact Sigma.ι_desc _ σ)

/-- **Base change of Galois covering spaces.** If `Y → X` is an `F`-Galois covering space for a
finite group `F` and `h : X' ⟶ X` is a morphism, then `Y ×_X X' → X'`, with `F` acting by
`σ × id_{X'}`, is an `F`-Galois covering space of `X'`. -/
@[weil "lem_fk106_galois_covering_base_change"]
theorem pullback {Y : Over X} {ρ : F →* Aut Y} (hY : IsGaloisCovering Y ρ) (h : X' ⟶ X) :
    IsGaloisCovering ((Over.pullback h).obj Y) (((Over.pullback h).mapAut Y).comp ρ) where
  etale := by
    have := hY.etale
    change Etale (pullback.snd Y.hom h)
    infer_instance
  surjective := by
    have := hY.surjective
    change Surjective (pullback.snd Y.hom h)
    infer_instance
  isIso_galoisCoveringMap := by
    have := hY.isIso_galoisCoveringMap
    exact (isPullback_galoisCoveringMap_pullback h Y ρ).isIso_fst_of_isIso

end IsGaloisCovering

namespace GaloisCovering

lemma ρAut_mapAction_obj (h : X' ⟶ X) (A : Action (Over X) F) :
    ((Over.pullback h).mapAction F |>.obj A).ρAut = ((Over.pullback h).mapAut A.V).comp A.ρAut := by
  ext σ : 2
  rfl

variable (F) [Finite F] in
/-- The base change `Y ↦ Y ×_X X'` of `F`-Galois covering spaces along `h : X' ⟶ X`, with `F`
acting by `σ × id_{X'}`; as a functor, it sends an isomorphism of `F`-Galois covering spaces
`Y → Z` over `X` to an isomorphism `Y ×_X X' → Z ×_X X'` over `X'`. -/
@[weil "lem_fk106_galois_covering_base_change"]
def pullback (h : X' ⟶ X) : GaloisCovering X F ⥤ GaloisCovering X' F :=
  ObjectProperty.lift _ ((isGaloisCoveringProperty X F).ι ⋙ (Over.pullback h).mapAction F)
    fun Y ↦ by
      change IsGaloisCovering ((Over.pullback h).obj Y.obj.V)
        ((Over.pullback h).mapAction F |>.obj Y.obj).ρAut
      rw [ρAut_mapAction_obj]
      exact Y.isGaloisCovering.pullback h

variable [Finite F]

@[simp]
lemma pullback_obj_over (h : X' ⟶ X) (Y : GaloisCovering X F) :
    ((pullback F h).obj Y).over = (Over.pullback h).obj Y.over :=
  rfl

lemma pullback_obj_act (h : X' ⟶ X) (Y : GaloisCovering X F) :
    ((pullback F h).obj Y).act = ((Over.pullback h).mapAut Y.over).comp Y.act :=
  ρAut_mapAction_obj h Y.obj

/-- The isomorphism `Y ×_X X' ≅ Z ×_X X'` of `F`-Galois covering spaces induced by an
isomorphism `e : Y ≅ Z` of `F`-Galois covering spaces is the base change of `e`. -/
@[simp]
lemma isoOver_pullback_mapIso (h : X' ⟶ X) {Y Z : GaloisCovering X F} (e : Y ≅ Z) :
    isoOver ((pullback F h).mapIso e) = (Over.pullback h).mapIso (isoOver e) := by
  ext : 1
  rfl

end GaloisCovering

end AlgebraicGeometry
