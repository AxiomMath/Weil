module

public import Mathlib.CategoryTheory.Elements
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import Weil.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# Pointed covering spaces

Let `s : Spec Ω ⟶ X` be a geometric point of a scheme `X`. A *pointed covering space* of
`(X, s)` is a pair `(Y, α)` of a covering space `Y` of `X` (a finite étale `X`-scheme) and a
geometric point `α ∈ Y(s)` of `Y` over `s`, i.e. a morphism `α : Spec Ω ⟶ Y` with `α ≫ p = s`.
A morphism of pointed covering spaces `(Y₁, α₁) ⟶ (Y₂, α₂)` is a morphism of covering spaces
`f : Y₁ ⟶ Y₂` with `α₁ ≫ f = α₂`.

Pointed covering spaces are exactly the objects of the category of elements of the geometric
fibre functor `Y ↦ Y(s)` on `Cov(X)`, and that is how they are defined here.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace s` — the category of pointed covering
  spaces of `(X, s)`, the category of elements of `finiteEtaleFiberFunctor s`.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.mk` — the pointed covering space
  `(Y, α)`.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.cover` — the underlying covering space.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.point` — the base point `α ∈ Y(s)`.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.forget` — the functor to `Cov(X)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.homEquiv` — a morphism
  `(Y₁, α₁) ⟶ (Y₂, α₂)` is the same as a morphism of schemes `f : Y₁ ⟶ Y₂` over `X` with
  `α₁ ≫ f = α₂`.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.hom_ext` — morphisms are determined by
  their underlying morphism of schemes.

## Implementation notes

Geometric points take values in algebraically closed fields (`AlgebraicGeometry.GeometricPoint`),
following the convention of the Stacks project; the source allows separably closed fields.
The pointed Galois covering spaces are Mathlib's
`CategoryTheory.PreGaloisCategory.PointedGaloisObject` for the fibre functor.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} (s : GeometricPoint X)

/-- **Pointed covering spaces.** A pointed covering space of `(X, s)` is a pair `(Y, α)` of a
covering space `Y` of `X` and a geometric point `α ∈ Y(s)` of `Y` over `s`. They form the
category of elements of the geometric fibre functor `Y ↦ Y(s)` on `Cov(X)`: a morphism
`(Y₁, α₁) ⟶ (Y₂, α₂)` is a morphism of covering spaces carrying `α₁` to `α₂`. -/
@[weil "def_fka1_pointed_covering_space"]
abbrev PointedCoveringSpace : Type (u + 1) :=
  (finiteEtaleFiberFunctor s : X.CoveringSpace ⥤ Type u).Elements

namespace PointedCoveringSpace

variable {s}

/-- The pointed covering space `(Y, α)`, for a covering space `Y` and a geometric point
`α : Spec Ω ⟶ Y` of `Y` over `s`. -/
abbrev mk (Y : X.CoveringSpace) (α : s.source ⟶ Y.left) (hα : α ≫ Y.hom = s.hom) :
    s.PointedCoveringSpace :=
  ⟨Y, ⟨α, hα⟩⟩

/-- The underlying covering space `Y` of a pointed covering space `(Y, α)`. -/
abbrev cover (P : s.PointedCoveringSpace) : X.CoveringSpace := P.1

/-- The base point `α : Spec Ω ⟶ Y` of a pointed covering space `(Y, α)`. -/
abbrev point (P : s.PointedCoveringSpace) : s.source ⟶ P.cover.left := P.2.1

@[reassoc (attr := simp)]
lemma point_comp_hom (P : s.PointedCoveringSpace) : P.point ≫ P.cover.hom = s.hom :=
  P.2.2

@[simp]
lemma cover_mk (Y : X.CoveringSpace) (α : s.source ⟶ Y.left) (hα : α ≫ Y.hom = s.hom) :
    (mk Y α hα).cover = Y :=
  rfl

@[simp]
lemma point_mk (Y : X.CoveringSpace) (α : s.source ⟶ Y.left) (hα : α ≫ Y.hom = s.hom) :
    (mk Y α hα).point = α :=
  rfl

/-- The forgetful functor `(Y, α) ↦ Y` from pointed covering spaces to covering spaces. -/
abbrev forget : s.PointedCoveringSpace ⥤ X.CoveringSpace :=
  CategoryOfElements.π _

/-- The underlying morphism of covering spaces carries the base point to the base point. -/
@[reassoc (attr := simp)]
lemma point_comp_left {P Q : s.PointedCoveringSpace} (f : P ⟶ Q) :
    P.point ≫ f.1.left = Q.point :=
  congrArg Subtype.val f.2

/-- Morphisms of pointed covering spaces are determined by their underlying morphism of
schemes. -/
@[ext]
lemma hom_ext {P Q : s.PointedCoveringSpace} {f g : P ⟶ Q} (h : f.1.left = g.1.left) :
    f = g :=
  CategoryOfElements.ext _ _ _ (MorphismProperty.Over.Hom.ext h)

/-- A morphism of schemes `f : Y₁ ⟶ Y₂` over `X` with `α₁ ≫ f = α₂` as a morphism of pointed
covering spaces `(Y₁, α₁) ⟶ (Y₂, α₂)`. -/
def homMk {P Q : s.PointedCoveringSpace} (f : P.cover.left ⟶ Q.cover.left)
    (hf : f ≫ Q.cover.hom = P.cover.hom) (hα : P.point ≫ f = Q.point) : P ⟶ Q :=
  ⟨MorphismProperty.Over.homMk f hf, Subtype.ext hα⟩

@[simp]
lemma homMk_left {P Q : s.PointedCoveringSpace} (f : P.cover.left ⟶ Q.cover.left)
    (hf : f ≫ Q.cover.hom = P.cover.hom) (hα : P.point ≫ f = Q.point) :
    (homMk f hf hα).1.left = f :=
  rfl

/-- **Morphisms of pointed covering spaces.** A morphism `(Y₁, α₁) ⟶ (Y₂, α₂)` is the same as a
morphism of schemes `f : Y₁ ⟶ Y₂` over `X` with `α₁ ≫ f = α₂`. -/
def homEquiv (P Q : s.PointedCoveringSpace) :
    (P ⟶ Q) ≃ {f : P.cover.left ⟶ Q.cover.left //
      f ≫ Q.cover.hom = P.cover.hom ∧ P.point ≫ f = Q.point} where
  toFun f := ⟨f.1.left, MorphismProperty.Over.w f.1, point_comp_left f⟩
  invFun f := homMk f.1 f.2.1 f.2.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma homEquiv_apply_coe {P Q : s.PointedCoveringSpace} (f : P ⟶ Q) :
    (homEquiv P Q f : P.cover.left ⟶ Q.cover.left) = f.1.left :=
  rfl

@[simp]
lemma id_left (P : s.PointedCoveringSpace) : (𝟙 P : P ⟶ P).1.left = 𝟙 P.cover.left :=
  rfl

@[simp, reassoc]
lemma comp_left {P Q R : s.PointedCoveringSpace} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).1.left = f.1.left ≫ g.1.left :=
  rfl

end PointedCoveringSpace

end GeometricPoint

end AlgebraicGeometry

end
