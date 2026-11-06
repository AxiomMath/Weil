module

public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import Weil.Attr

/-!
# Morphisms of pointed covering spaces

Let `s` be a geometric point of a scheme `X`, and let `(Y₁, α₁)`, `(Y₂, α₂)` be pointed covering
spaces of `(X, s)`. A *mapping of pointed covering spaces* `(Y₁, α₁) → (Y₂, α₂)` is an
`X`-morphism `f : Y₁ ⟶ Y₂` with `α₁ ≫ f = α₂`. These maps contain the identities and are closed
under composition of morphisms of schemes, so they form a category, the category of pointed
covering spaces of `(X, s)`.

The category `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace s` is the category of
elements of the geometric fibre functor; this file identifies its morphisms with the mappings
above, as morphisms of schemes.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.IsHom P Q f` — the morphism of schemes
  `f` is a mapping of pointed covering spaces `P ⟶ Q`.

## Main results

* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.isHom_iff_exists_hom` — the mappings of
  pointed covering spaces are exactly the underlying morphisms of schemes of the morphisms of
  the category `PointedCoveringSpace s`.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.isHom_id`,
  `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.isHom_comp` — identities are mappings
  and mappings are closed under composition of morphisms of schemes.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.homEquivIsHom` — the morphisms
  `P ⟶ Q` of the category are in bijection with the mappings, compatibly with identities and
  composition.

## Implementation notes

Geometric points take values in algebraically closed fields (`AlgebraicGeometry.GeometricPoint`),
following the convention of the Stacks project; the source allows separably closed fields.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

namespace PointedCoveringSpace

variable {X : Scheme.{u}} {s : GeometricPoint X}

/-- **Mappings of pointed covering spaces.** A morphism of schemes `f : Y₁ ⟶ Y₂` is a mapping of
pointed covering spaces `(Y₁, α₁) → (Y₂, α₂)` if it is a morphism over `X` and `α₁ ≫ f = α₂`. -/
@[weil "def_fka1_pointed_covering_morphism"]
def IsHom (P Q : s.PointedCoveringSpace) (f : P.cover.left ⟶ Q.cover.left) : Prop :=
  f ≫ Q.cover.hom = P.cover.hom ∧ P.point ≫ f = Q.point

lemma isHom_iff {P Q : s.PointedCoveringSpace} {f : P.cover.left ⟶ Q.cover.left} :
    IsHom P Q f ↔ f ≫ Q.cover.hom = P.cover.hom ∧ P.point ≫ f = Q.point :=
  Iff.rfl

/-- The underlying morphism of schemes of a morphism of pointed covering spaces is a mapping of
pointed covering spaces. -/
lemma isHom_left {P Q : s.PointedCoveringSpace} (g : P ⟶ Q) : IsHom P Q g.1.left :=
  ⟨MorphismProperty.Over.w g.1, point_comp_left g⟩

/-- The mappings of pointed covering spaces `P → Q` are exactly the underlying morphisms of
schemes of the morphisms `P ⟶ Q` of the category of pointed covering spaces. -/
@[weil "def_fka1_pointed_covering_morphism"]
theorem isHom_iff_exists_hom {P Q : s.PointedCoveringSpace} (f : P.cover.left ⟶ Q.cover.left) :
    IsHom P Q f ↔ ∃ g : P ⟶ Q, g.1.left = f :=
  ⟨fun h => ⟨homMk f h.1 h.2, rfl⟩, fun ⟨g, hg⟩ => hg ▸ isHom_left g⟩

/-- The identity is a mapping of pointed covering spaces. -/
@[weil "def_fka1_pointed_covering_morphism"]
theorem isHom_id (P : s.PointedCoveringSpace) : IsHom P P (𝟙 P.cover.left) :=
  ⟨Category.id_comp _, Category.comp_id _⟩

/-- Mappings of pointed covering spaces are closed under composition of morphisms of schemes. -/
@[weil "def_fka1_pointed_covering_morphism"]
theorem isHom_comp {P Q R : s.PointedCoveringSpace} {f : P.cover.left ⟶ Q.cover.left}
    {g : Q.cover.left ⟶ R.cover.left} (hf : IsHom P Q f) (hg : IsHom Q R g) :
    IsHom P R (f ≫ g) :=
  ⟨by rw [Category.assoc, hg.1, hf.1], by rw [← Category.assoc, hf.2, hg.2]⟩

/-- The morphisms `P ⟶ Q` of the category of pointed covering spaces are in bijection with the
mappings of pointed covering spaces `P → Q`, by taking the underlying morphism of schemes. -/
def homEquivIsHom (P Q : s.PointedCoveringSpace) :
    (P ⟶ Q) ≃ {f : P.cover.left ⟶ Q.cover.left // IsHom P Q f} :=
  homEquiv P Q

@[simp]
lemma homEquivIsHom_apply_coe {P Q : s.PointedCoveringSpace} (g : P ⟶ Q) :
    (homEquivIsHom P Q g : P.cover.left ⟶ Q.cover.left) = g.1.left :=
  rfl

@[simp]
lemma homEquivIsHom_symm_apply_left {P Q : s.PointedCoveringSpace}
    (f : {f : P.cover.left ⟶ Q.cover.left // IsHom P Q f}) :
    ((homEquivIsHom P Q).symm f).1.left = f.1 :=
  rfl

/-- The bijection `homEquivIsHom` sends identities to identities. -/
lemma homEquivIsHom_id (P : s.PointedCoveringSpace) :
    homEquivIsHom P P (𝟙 P) = ⟨𝟙 P.cover.left, isHom_id P⟩ :=
  rfl

/-- The bijection `homEquivIsHom` sends composition in the category of pointed covering spaces
to composition of morphisms of schemes. -/
lemma homEquivIsHom_comp {P Q R : s.PointedCoveringSpace} (f : P ⟶ Q) (g : Q ⟶ R) :
    homEquivIsHom P R (f ≫ g) =
      ⟨(homEquivIsHom P Q f).1 ≫ (homEquivIsHom Q R g).1,
        isHom_comp (homEquivIsHom P Q f).2 (homEquivIsHom Q R g).2⟩ :=
  rfl

end PointedCoveringSpace

end GeometricPoint

end AlgebraicGeometry

end
