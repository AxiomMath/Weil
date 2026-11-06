module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Weil.Defs.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringSpace
public import Weil.Attr

/-!
# The category of Galois covering spaces

Let `X` be a scheme and `F` a group. A morphism of `F`-Galois covering spaces `X'/X → X''/X` is
an `X`-morphism `X' → X''` compatible with the actions of `F`, and an *isomorphism* of
`F`-Galois covering spaces is an `X`-isomorphism `X' → X''` compatible with the actions of `F`.
We organise the `F`-Galois covering spaces of `X` into a category, the full subcategory of the
category `Action (Over X) F` of `X`-schemes with an action of `F` by `X`-morphisms on the objects
which are Galois covering spaces; its isomorphisms are then exactly the isomorphisms of
`F`-Galois covering spaces, and isomorphism classes are `CategoryTheory.IsIsomorphic`-classes.

## Main definitions

* `AlgebraicGeometry.GaloisCovering X F` — the category of `F`-Galois covering spaces of `X`.
* `AlgebraicGeometry.GaloisCovering.of Y ρ h` — the `F`-Galois covering space given by an
  `X`-scheme `Y`, an action `ρ : F →* Aut Y` and a proof `h : IsGaloisCovering Y ρ`.
* `AlgebraicGeometry.GaloisCovering.isoMk` — the isomorphism of `F`-Galois covering spaces given
  by an `F`-equivariant `X`-isomorphism.

## Main results

* `AlgebraicGeometry.GaloisCovering.isoEquiv` — isomorphisms of `F`-Galois covering spaces
  are the same as `X`-isomorphisms of the underlying `X`-schemes compatible with the actions of
  `F`.
* `AlgebraicGeometry.GaloisCovering.isIsomorphic_of_iff` — two `F`-Galois covering spaces given
  by actions `ρ`, `ρ'` are isomorphic if and only if there is an `X`-isomorphism `e` with
  `ρ σ ≪≫ e = e ≪≫ ρ' σ` for every `σ ∈ F`.

## Implementation notes

The action on an object of `Action (Over X) F` is a monoid homomorphism `F →* End Y`; for a
group `F` it is the same as a homomorphism `F →* Aut Y` (`Action.ρAut`), which is the form in
which `AlgebraicGeometry.IsGaloisCovering` is stated.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (F : Type u) [Group F]

/-- The `X`-schemes with an action of `F` by `X`-automorphisms which are `F`-Galois covering
spaces of `X`. -/
def isGaloisCoveringProperty : ObjectProperty (Action (Over X) F) :=
  fun A ↦ IsGaloisCovering A.V A.ρAut

/-- The category of `F`-Galois covering spaces of `X`: its objects are the `F`-Galois covering
spaces, its morphisms the `F`-equivariant `X`-morphisms. -/
@[weil "def_fk102_galois_covering_isomorphism"]
abbrev GaloisCovering : Type (u + 1) :=
  (isGaloisCoveringProperty X F).FullSubcategory

variable {X F}

namespace GaloisCovering

/-- The underlying `X`-scheme of an `F`-Galois covering space. -/
abbrev over (Y : GaloisCovering X F) : Over X := Y.obj.V

/-- The action of `F` on an `F`-Galois covering space, by `X`-automorphisms. -/
abbrev act (Y : GaloisCovering X F) : F →* Aut Y.over := Y.obj.ρAut

lemma isGaloisCovering (Y : GaloisCovering X F) : IsGaloisCovering Y.over Y.act := Y.property

/-- The `F`-Galois covering space given by an `X`-scheme `Y` with an action `ρ` of `F` by
`X`-automorphisms which makes it a Galois covering space. -/
def of (Y : Over X) (ρ : F →* Aut Y) (h : IsGaloisCovering Y ρ) : GaloisCovering X F where
  obj := ⟨Y, (Aut.toEnd Y).comp ρ⟩
  property := by
    have : (⟨Y, (Aut.toEnd Y).comp ρ⟩ : Action (Over X) F).ρAut = ρ := by
      ext σ : 2
      rfl
    simpa [isGaloisCoveringProperty, this] using h

@[simp]
lemma of_over (Y : Over X) (ρ : F →* Aut Y) (h : IsGaloisCovering Y ρ) : (of Y ρ h).over = Y :=
  rfl

@[simp]
lemma of_act (Y : Over X) (ρ : F →* Aut Y) (h : IsGaloisCovering Y ρ) : (of Y ρ h).act = ρ := by
  ext σ : 2
  rfl

/-- An `X`-isomorphism of `F`-Galois covering spaces compatible with the actions of `F` is an
isomorphism of `F`-Galois covering spaces. -/
def isoMk {Y Y' : GaloisCovering X F} (e : Y.over ≅ Y'.over)
    (comm : ∀ σ : F, Y.act σ ≪≫ e = e ≪≫ Y'.act σ) : Y ≅ Y' :=
  ObjectProperty.isoMk _ <| Action.mkIso e fun σ ↦ congrArg Iso.hom (comm σ)

@[simp]
lemma isoMk_hom_hom_hom {Y Y' : GaloisCovering X F} (e : Y.over ≅ Y'.over)
    (comm : ∀ σ : F, Y.act σ ≪≫ e = e ≪≫ Y'.act σ) : (isoMk e comm).hom.hom.hom = e.hom :=
  rfl

/-- The `X`-isomorphism of underlying `X`-schemes of an isomorphism of `F`-Galois covering
spaces. -/
def isoOver {Y Y' : GaloisCovering X F} (e : Y ≅ Y') : Y.over ≅ Y'.over :=
  (Action.forget (Over X) F).mapIso ((isGaloisCoveringProperty X F).ι.mapIso e)

@[simp]
lemma isoOver_hom {Y Y' : GaloisCovering X F} (e : Y ≅ Y') : (isoOver e).hom = e.hom.hom.hom :=
  rfl

lemma act_trans_isoOver {Y Y' : GaloisCovering X F} (e : Y ≅ Y') (σ : F) :
    Y.act σ ≪≫ isoOver e = isoOver e ≪≫ Y'.act σ := by
  ext : 1
  exact e.hom.hom.comm σ

/-- An isomorphism of `F`-Galois covering spaces `Y → Y'` is the same as an `X`-isomorphism
`e` of the underlying `X`-schemes compatible with the actions of `F`, that is, with
`σ ≫ e = e ≫ σ` for every `σ ∈ F`. -/
@[weil "def_fk102_galois_covering_isomorphism"]
def isoEquiv (Y Y' : GaloisCovering X F) :
    (Y ≅ Y') ≃ {e : Y.over ≅ Y'.over // ∀ σ : F, Y.act σ ≪≫ e = e ≪≫ Y'.act σ} where
  toFun e := ⟨isoOver e, act_trans_isoOver e⟩
  invFun e := isoMk e.1 e.2
  left_inv e := by
    ext : 3
    rfl
  right_inv e := by
    ext : 2
    rfl

/-- Two `F`-Galois covering spaces given by actions `ρ` and `ρ'` are isomorphic if and only if
there is an `X`-isomorphism between them compatible with the actions of `F`. -/
lemma isIsomorphic_of_iff {Y Y' : Over X} {ρ : F →* Aut Y} {ρ' : F →* Aut Y'}
    (h : IsGaloisCovering Y ρ) (h' : IsGaloisCovering Y' ρ') :
    IsIsomorphic (of Y ρ h) (of Y' ρ' h') ↔
      ∃ e : Y ≅ Y', ∀ σ : F, ρ σ ≪≫ e = e ≪≫ ρ' σ := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨e, he⟩ := isoEquiv _ _ e
    exact ⟨e, fun σ ↦ Iso.ext (congrArg Iso.hom (he σ) :)⟩
  · rintro ⟨e, he⟩
    exact ⟨(isoEquiv (of Y ρ h) (of Y' ρ' h')).symm
      ⟨e, fun σ ↦ Iso.ext (congrArg Iso.hom (he σ) :)⟩⟩

end GaloisCovering

end AlgebraicGeometry
