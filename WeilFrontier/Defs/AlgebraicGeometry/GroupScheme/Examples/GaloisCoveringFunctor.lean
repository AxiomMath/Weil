module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Skeletal
public import WeilFrontier.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringBaseChange
public import Weil.Attr

/-!
# The functor of Galois covering spaces of a base change

Let `R` be a ring, `X` an `R`-scheme and `n ≥ 1`. For an `R`-algebra `B` let `F(B)` be the set of
isomorphism classes of `ℤ/nℤ`-Galois covering spaces of `X ⊗_R B = X ×_{Spec R} Spec B`; a
homomorphism of `R`-algebras `B → B'` induces `F(B) → F(B')`,
`[Y] ↦ [Y ×_{X ⊗_R B} (X ⊗_R B')]`. Restricted to noetherian `R`-algebras this is the functor
`F_{X,n}` of [FK], I.6, used there for `X` projective over `Spec R`.

That the map is well defined rests on the fact that the base change of an `F`-Galois covering
space `Y → X` along any morphism `X' → X` is an `F`-Galois covering space of `X'` for a finite
group `F` (`AlgebraicGeometry.IsGaloisCovering.pullback`): étale surjective morphisms are
stable under base change, and the isomorphism `∐_{σ ∈ F} Y ≅ Y ×_X Y` stays one after base
change because finite coproducts of schemes are universal.

## Main definitions

* `AlgebraicGeometry.GaloisCovering.pullbackIdIso`,
  `AlgebraicGeometry.GaloisCovering.pullbackCompIso` — base change of Galois covering spaces
  along the identity and along a composite, up to isomorphism.
* `AlgebraicGeometry.baseChangeAlg X` — the base change `B ↦ X ⊗_R B`, as a functor.
* `AlgebraicGeometry.galoisCoveringClasses X F` — the functor of isomorphism classes of
  `F`-Galois covering spaces of `X ⊗_R B` on all `R`-algebras `B`.
* `AlgebraicGeometry.galoisCoveringFunctor X n` — the functor `F_{X,n}` on noetherian
  `R`-algebras.

## Main results

* `AlgebraicGeometry.galoisCoveringFunctor_map_toSkeleton` — the map induced by `B → B'` is
  `[Y] ↦ [Y ×_{X ⊗_R B} (X ⊗_R B')]`.

## Implementation notes

The set of isomorphism classes of a category `C` is `CategoryTheory.Skeleton C`, and the class
of `Y` is `CategoryTheory.toSkeleton Y`. The group `ℤ/nℤ` is taken multiplicatively,
`Multiplicative (ZMod n)`, lifted to the universe of the schemes; `n ≥ 1` is `NeZero n`, which
makes it finite. The functor is defined for every `R`-scheme `X`; projectivity of `X` over
`Spec R` is a hypothesis of the results about it. Noetherian `R`-algebras form the full
subcategory of `CommAlgCat R` on the algebras with `IsNoetherianRing`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

variable {X X' : Scheme.{u}} (f : X' ⟶ X) {F : Type u} [Group F]

namespace GaloisCovering

variable [Finite F]

/-- The base change of an `F`-Galois covering space along the identity is isomorphic to it. -/
def pullbackIdIso (Y : GaloisCovering X F) : (pullback F (𝟙 X)).obj Y ≅ Y :=
  ObjectProperty.isoMk _ <|
    (Functor.mapActionCongr F Over.pullbackId).app Y.obj ≪≫ Action.mkIso (Iso.refl _)
      (by intro g; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)

/-- Base change of `F`-Galois covering spaces along a composite is the composite of the base
changes, up to isomorphism. -/
def pullbackCompIso {X'' : Scheme.{u}} (g : X'' ⟶ X') (Y : GaloisCovering X F) :
    (pullback F (g ≫ f)).obj Y ≅ (pullback F g).obj ((pullback F f).obj Y) :=
  ObjectProperty.isoMk _ <|
    (Functor.mapActionCongr F (Over.pullbackComp g f)).app Y.obj ≪≫
      (Functor.mapActionComp F (Over.pullback f) (Over.pullback g)).app Y.obj

lemma toSkeleton_pullback_id (Y : GaloisCovering X F) :
    toSkeleton ((pullback F (𝟙 X)).obj Y) = toSkeleton Y :=
  congr_toSkeleton_of_iso (pullbackIdIso Y)

lemma toSkeleton_pullback_comp {X'' : Scheme.{u}} (g : X'' ⟶ X') (Y : GaloisCovering X F) :
    toSkeleton ((pullback F (g ≫ f)).obj Y) =
      toSkeleton ((pullback F g).obj ((pullback F f).obj Y)) :=
  congr_toSkeleton_of_iso (pullbackCompIso f g Y)

end GaloisCovering

section Functor

variable {R : CommRingCat.{u}} (X : Over (Spec R))

/-- The base change `X ⊗_R B = X ×_{Spec R} Spec B` of an `R`-scheme `X`, as a functor of the
`R`-algebra `B`. -/
def baseChangeAlg : (CommAlgCat.{u} R)ᵒᵖ ⥤ Scheme.{u} :=
  algSpec R ⋙ tensorLeft X ⋙ Over.forget _

lemma baseChangeAlg_obj (B : (CommAlgCat.{u} R)ᵒᵖ) :
    (baseChangeAlg X).obj B =
      Limits.pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap R B.unop))) :=
  rfl

variable (F : Type u) [Group F] [Finite F]

/-- The functor on `R`-algebras sending `B` to the set of isomorphism classes of `F`-Galois
covering spaces of `X ⊗_R B`, and a homomorphism `B → B'` to the base change
`[Y] ↦ [Y ×_{X ⊗_R B} (X ⊗_R B')]`. -/
def galoisCoveringClasses : CommAlgCat.{u} R ⥤ Type (u + 1) where
  obj B := Skeleton (GaloisCovering ((baseChangeAlg X).obj (.op B)) F)
  map φ := TypeCat.ofHom (GaloisCovering.pullback F ((baseChangeAlg X).map φ.op)).mapSkeleton.obj
  map_id B := by
    refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
    rw [← toSkeleton_fromSkeleton_obj y, TypeCat.ofHom_apply, Functor.mapSkeleton_obj_toSkeleton,
      types_id_apply, op_id, CategoryTheory.Functor.map_id]
    exact GaloisCovering.toSkeleton_pullback_id _
  map_comp φ ψ := by
    refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
    rw [← toSkeleton_fromSkeleton_obj y]
    simp only [types_comp_apply, TypeCat.ofHom_apply, Functor.mapSkeleton_obj_toSkeleton]
    rw [op_comp, CategoryTheory.Functor.map_comp]
    exact GaloisCovering.toSkeleton_pullback_comp _ _ _

variable {X F}

lemma galoisCoveringClasses_map_toSkeleton {B B' : CommAlgCat.{u} R} (φ : B ⟶ B')
    (Y : GaloisCovering ((baseChangeAlg X).obj (.op B)) F) :
    (galoisCoveringClasses X F).map φ (toSkeleton Y) =
      toSkeleton ((GaloisCovering.pullback F ((baseChangeAlg X).map φ.op)).obj Y) :=
  Functor.mapSkeleton_obj_toSkeleton _ _

variable (X)

/-- The functor `F_{X,n}` on the category of noetherian `R`-algebras: it sends `B` to the set
of isomorphism classes of `ℤ/nℤ`-Galois covering spaces of `X ⊗_R B`, and a homomorphism of
`R`-algebras `B → B'` to `[Y] ↦ [Y ×_{X ⊗_R B} (X ⊗_R B')]`. -/
@[weil "def_fk106_galois_covering_functor"]
def galoisCoveringFunctor (n : ℕ) [NeZero n] :
    ObjectProperty.FullSubcategory (fun B : CommAlgCat.{u} R ↦ IsNoetherianRing B) ⥤
      Type (u + 1) :=
  ObjectProperty.ι _ ⋙ galoisCoveringClasses X (ULift.{u} (Multiplicative (ZMod n)))

variable {X}

/-- The value of `galoisCoveringFunctor X n` on a homomorphism of noetherian `R`-algebras
`B → B'` is the base change `[Y] ↦ [Y ×_{X ⊗_R B} (X ⊗_R B')]`. -/
@[weil "def_fk106_galois_covering_functor"]
lemma galoisCoveringFunctor_map_toSkeleton (n : ℕ) [NeZero n]
    {B B' : ObjectProperty.FullSubcategory (fun B : CommAlgCat.{u} R ↦ IsNoetherianRing B)}
    (φ : B ⟶ B')
    (Y : GaloisCovering ((baseChangeAlg X).obj (.op B.obj)) (ULift.{u} (Multiplicative (ZMod n)))) :
    (galoisCoveringFunctor X n).map φ (toSkeleton Y) =
      toSkeleton ((GaloisCovering.pullback _ ((baseChangeAlg X).map φ.hom.op)).obj Y) :=
  galoisCoveringClasses_map_toSkeleton _ _

end Functor

end AlgebraicGeometry
