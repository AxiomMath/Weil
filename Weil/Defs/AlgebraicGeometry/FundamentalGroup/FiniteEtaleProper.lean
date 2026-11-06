module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ContainsFiniteEtale
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Covering spaces

A *covering space* of a scheme `X` is a finite étale morphism `p : Y ⟶ X`, and the covering
spaces of `X` form the category `Cov(X)` whose morphisms `(Y₁, p₁) ⟶ (Y₂, p₂)` are the
`X`-morphisms, i.e. the morphisms of schemes `f : Y₁ ⟶ Y₂` with `f ≫ p₂ = p₁`. This is the
category of finite étale `X`-schemes, `AlgebraicGeometry.FiniteEtaleOver X`.

When `X` is noetherian and separated, every covering space `Y` of `X` is a noetherian separated
scheme étale over `X`, hence an object of the étale category `Et(X)`, and `Cov(X)` is the full
subcategory of `Et(X)` on the objects whose structure morphism is finite.

## Main definitions

* `AlgebraicGeometry.Scheme.CoveringSpace X` — the category `Cov(X)` of covering spaces of `X`.
* `AlgebraicGeometry.Scheme.CoveringSpace.toNoetherianSeparatedEtale` — for `X` noetherian and
  separated, the functor `Cov(X) ⥤ Et(X)`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.homEquiv` — morphisms of covering spaces are exactly
  the `X`-morphisms.
* `AlgebraicGeometry.Scheme.CoveringSpace.fullyFaithfulToNoetherianSeparatedEtale` — the functor
  `Cov(X) ⥤ Et(X)` is fully faithful.
* `AlgebraicGeometry.Scheme.CoveringSpace.isFinite_structureMorphism_iff` — its essential image
  consists of the objects of `Et(X)` whose structure morphism is finite.

## Implementation notes

The category `Cov(X)` is defined for every scheme `X`, as the category of finite étale
`X`-schemes, without asking the source to be noetherian and separated. For `X` noetherian and
separated, which is the setting of the source, the two conditions hold automatically for the
source of a finite morphism, so nothing is lost; for general `X` this is the standard category
`FÉt_X`. The objects of `Et(X)` live in a big étale site `B` containing `X`; every finite étale
`X`-scheme lies in `B` (`AlgebraicGeometry.BigEtaleSite.contains_left_of_finiteEtaleOver`), so
the functor to `Et(X)` needs no choice of a representative.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 0BL7](https://stacks.math.columbia.edu/tag/0BL7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The category `Cov(X)` of covering spaces of `X`.** A covering space of `X` is a finite
étale morphism `p : Y ⟶ X`; a morphism of covering spaces `(Y₁, p₁) ⟶ (Y₂, p₂)` is a morphism of
schemes `f : Y₁ ⟶ Y₂` with `f ≫ p₂ = p₁`. -/
@[weil "def_fka1_covering_space"]
abbrev Scheme.CoveringSpace (X : Scheme.{u}) : Type (u + 1) := FiniteEtaleOver X

namespace Scheme.CoveringSpace

section Basic

variable {X : Scheme.{u}}

instance isFinite_hom (Y : X.CoveringSpace) : IsFinite Y.hom := Y.prop.1

instance etale_hom (Y : X.CoveringSpace) : Etale Y.hom := Y.prop.2

/-- The covering space given by a finite étale morphism `p : Y ⟶ X`. -/
abbrev mk {Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] [Etale p] : X.CoveringSpace :=
  MorphismProperty.Over.mk ⊤ p ⟨‹IsFinite p›, ‹Etale p›⟩

@[reassoc (attr := simp)]
lemma left_comp_hom {Y₁ Y₂ : X.CoveringSpace} (f : Y₁ ⟶ Y₂) : f.left ≫ Y₂.hom = Y₁.hom :=
  MorphismProperty.Over.w f

/-- **Morphisms of covering spaces.** A morphism `(Y₁, p₁) ⟶ (Y₂, p₂)` of covering spaces of `X`
is the same as an `X`-morphism, a morphism of schemes `f : Y₁ ⟶ Y₂` with `f ≫ p₂ = p₁`. -/
@[weil "def_fka1_covering_space"]
def homEquiv (Y₁ Y₂ : X.CoveringSpace) :
    (Y₁ ⟶ Y₂) ≃ {f : Y₁.left ⟶ Y₂.left // f ≫ Y₂.hom = Y₁.hom} where
  toFun f := ⟨f.left, left_comp_hom f⟩
  invFun f := MorphismProperty.Over.homMk f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma homEquiv_apply_coe {Y₁ Y₂ : X.CoveringSpace} (f : Y₁ ⟶ Y₂) :
    (homEquiv Y₁ Y₂ f : Y₁.left ⟶ Y₂.left) = f.left :=
  rfl

/-- The source of a covering space of a noetherian scheme is noetherian. -/
instance isNoetherian_left [IsNoetherian X] (Y : X.CoveringSpace) : IsNoetherian Y.left := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := Y.left) (Y := X) Y.hom
  have : CompactSpace Y.left :=
    QuasiCompact.compactSpace_of_compactSpace (X := Y.left) (Y := X) Y.hom
  exact ⟨⟩

/-- The source of a covering space of a separated scheme is separated. -/
instance isSeparated_left [X.IsSeparated] (Y : X.CoveringSpace) : Y.left.IsSeparated := by
  have h₁ : IsSeparated (Y.hom : Y.left ⟶ X) := IsSeparated.of_isAffineHom _
  have h₂ := MorphismProperty.comp_mem @IsSeparated _ _ h₁
    (Scheme.IsSeparated.isSeparated_terminal_from (X := X))
  exact ⟨Subsingleton.elim ((Y.hom : Y.left ⟶ X) ≫ Limits.terminal.from X)
    (Limits.terminal.from Y.left) ▸ h₂⟩

end Basic

section NoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) [IsNoetherian X]
  [X.IsSeparated]

/-- **A covering space is an object of `Et(X)`.** For `X` noetherian and separated, the functor
`Cov(X) ⥤ Et(X)` sending a covering space `p : Y ⟶ X` to the étale morphism `p` from the
noetherian separated scheme `Y`. -/
@[weil "def_fka1_covering_space"]
noncomputable def toNoetherianSeparatedEtale :
    X.CoveringSpace ⥤ SmallNoetherianSeparatedEtale B X hX where
  obj Y := SmallNoetherianSeparatedEtale.mk Y.left (B.contains_left_of_finiteEtaleOver Y hX) Y.hom
  map f := (SmallNoetherianSeparatedEtale.homEquiv _ _).symm ⟨f.left, left_comp_hom f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {B X hX}

@[simp]
lemma toScheme_obj_toNoetherianSeparatedEtale_obj (Y : X.CoveringSpace) :
    (SmallNoetherianSeparatedEtale.toScheme B X hX).obj
      ((toNoetherianSeparatedEtale B X hX).obj Y) = Y.left :=
  rfl

@[simp]
lemma structureMorphism_toNoetherianSeparatedEtale_obj (Y : X.CoveringSpace) :
    SmallNoetherianSeparatedEtale.structureMorphism ((toNoetherianSeparatedEtale B X hX).obj Y) =
      Y.hom :=
  rfl

@[simp]
lemma toScheme_map_toNoetherianSeparatedEtale_map {Y₁ Y₂ : X.CoveringSpace} (f : Y₁ ⟶ Y₂) :
    (SmallNoetherianSeparatedEtale.toScheme B X hX).map
      ((toNoetherianSeparatedEtale B X hX).map f) = f.left :=
  rfl

variable (B X hX)

/-- **`Cov(X)` is a full subcategory of `Et(X)`.** -/
@[weil "def_fka1_covering_space"]
noncomputable def fullyFaithfulToNoetherianSeparatedEtale :
    (toNoetherianSeparatedEtale B X hX).FullyFaithful where
  preimage g := MorphismProperty.Over.homMk
    ((SmallNoetherianSeparatedEtale.toScheme B X hX).map g)
    (SmallNoetherianSeparatedEtale.toScheme_map_comp_structureMorphism g)
  map_preimage _ := rfl
  preimage_map _ := rfl

instance : (toNoetherianSeparatedEtale B X hX).Full :=
  (fullyFaithfulToNoetherianSeparatedEtale B X hX).full

instance : (toNoetherianSeparatedEtale B X hX).Faithful :=
  (fullyFaithfulToNoetherianSeparatedEtale B X hX).faithful

variable {B X hX}

/-- **The essential image of `Cov(X)` in `Et(X)`.** An object `u : U ⟶ X` of `Et(X)` is
isomorphic to a covering space if and only if `u` is finite. -/
@[weil "def_fka1_covering_space"]
theorem isFinite_structureMorphism_iff (U : SmallNoetherianSeparatedEtale B X hX) :
    IsFinite (SmallNoetherianSeparatedEtale.structureMorphism U) ↔
      ∃ Y : X.CoveringSpace, Nonempty ((toNoetherianSeparatedEtale B X hX).obj Y ≅ U) := by
  constructor
  · intro _
    refine ⟨mk (SmallNoetherianSeparatedEtale.structureMorphism U), ⟨?_⟩⟩
    exact
      { hom := (SmallNoetherianSeparatedEtale.homEquiv _ _).symm ⟨𝟙 _, Category.id_comp _⟩
        inv := (SmallNoetherianSeparatedEtale.homEquiv _ _).symm ⟨𝟙 _, Category.id_comp _⟩
        hom_inv_id := SmallNoetherianSeparatedEtale.hom_ext (by
          rw [Functor.map_comp, CategoryTheory.Functor.map_id]; exact Category.id_comp _)
        inv_hom_id := SmallNoetherianSeparatedEtale.hom_ext (by
          rw [Functor.map_comp, CategoryTheory.Functor.map_id]; exact Category.id_comp _) }
  · rintro ⟨Y, ⟨e⟩⟩
    rw [← SmallNoetherianSeparatedEtale.toScheme_map_comp_structureMorphism e.inv]
    have : IsFinite (Y.hom : Y.left ⟶ X) := Y.prop.1
    have : IsFinite ((SmallNoetherianSeparatedEtale.toScheme B X hX).map e.inv) := inferInstance
    exact MorphismProperty.comp_mem @IsFinite _ (Y.hom : Y.left ⟶ X) this ‹_›

end NoetherianSeparatedEtale

end Scheme.CoveringSpace

end AlgebraicGeometry

end
