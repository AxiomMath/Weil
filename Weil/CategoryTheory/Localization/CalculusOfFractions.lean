module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Weil.Attr

/-!
# Composition of roofs in the derived category

Let `W` be a multiplicative class of morphisms in a category `C`. A right fraction (a roof)
`φ : X ← X' → Y` is a pair `(φ.s, φ.f)` with `φ.s ∈ W`. Given roofs `φ : X ← X' → Y` and
`ψ : Y ← Y' → Z`, a square `ρ : X' ← P → Y'` with `ρ.s ∈ W` and `ρ.s ≫ φ.f = ρ.f ≫ ψ.s`
gives the composite roof `X ← P → Z`, namely `(ρ.s ≫ φ.s, ρ.f ≫ ψ.f)`.

When `W` admits a calculus of right fractions, such a square always exists, and the class of
the composite roof (for the equivalence relation `RightFractionRel`) depends neither on the
square chosen nor on the representatives of the classes of `φ` and `ψ`. The induced
composition on classes is unital, with identities the classes of `(𝟙, 𝟙)`, and associative;
under any localization functor `L` it is the composition of `L.obj X ⟶ L.obj Y` and
`L.obj Y ⟶ L.obj Z`.

For the derived category `D(A)` of an abelian category, with `W` the quasi-isomorphisms of
the homotopy category `K(A)` and `L = DerivedCategory.Qh`, this is Verdier's description of
composition in `D(A)`.

## Main definitions

* `CategoryTheory.MorphismProperty.RightFraction.comp₀`: the composite roof attached to a
  square.

## Main results

* `CategoryTheory.MorphismProperty.RightFraction.map_comp_map_eq_map`: a localization functor
  sends the composite roof to the composite of the images.
* `CategoryTheory.MorphismProperty.RightFraction.rightFractionRel_comp₀`: independence of the
  square and of the representatives.
* `DerivedCategory.exists_rightFraction_comp_square`,
  `DerivedCategory.rightFractionRel_comp₀`, `DerivedCategory.rightFraction_map_comp_map`,
  `DerivedCategory.rightFractionRel_ofHom_id_comp₀`,
  `DerivedCategory.rightFractionRel_comp₀_ofHom_id`, `DerivedCategory.rightFractionRel_comp₀_assoc`:
  the statements for `D(A)`.

## Implementation notes

Mathlib constructs `DerivedCategory C` as a localization of `HomotopyCategory C (up ℤ)` at the
quasi-isomorphisms, so that it is a category by construction. The roof description of its
morphisms (`Localization.exists_rightFraction`, `RightFraction.map_eq_iff`) identifies the
roof composition with the composition of `DerivedCategory C`; the statements here are about
roofs and their classes, and their images under `DerivedCategory.Qh`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II.
-/

@[expose] public section

namespace CategoryTheory

open Category

namespace MorphismProperty

namespace RightFraction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {W : MorphismProperty C}

/-- The composite of right fractions `φ : X ← X' → Y` and `ψ : Y ← Y' → Z` attached to a
right fraction `ρ : X' ← P → Y'` (meant to satisfy `ρ.s ≫ φ.f = ρ.f ≫ ψ.s`): the roof
`X ← P → Z` with denominator `ρ.s ≫ φ.s` and numerator `ρ.f ≫ ψ.f`. -/
@[simps]
def comp₀ [W.IsStableUnderComposition] {X Y Z : C} (φ : W.RightFraction X Y)
    (ψ : W.RightFraction Y Z) (ρ : W.RightFraction φ.X' ψ.X') : W.RightFraction X Z where
  X' := ρ.X'
  s := ρ.s ≫ φ.s
  hs := W.comp_mem _ _ ρ.hs φ.hs
  f := ρ.f ≫ ψ.f

/-- A functor inverting `W` sends the composite roof to the composite of the images. -/
lemma map_comp_map_eq_map [W.IsStableUnderComposition] {X Y Z : C} (φ : W.RightFraction X Y)
    (ψ : W.RightFraction Y Z) (ρ : W.RightFraction φ.X' ψ.X') (h : ρ.s ≫ φ.f = ρ.f ≫ ψ.s)
    (L : C ⥤ D) (hL : W.IsInvertedBy L) :
    φ.map L hL ≫ ψ.map L hL = (φ.comp₀ ψ ρ).map L hL := by
  have := hL _ φ.hs
  have := hL _ ρ.hs
  have : IsIso (L.map (ρ.s ≫ φ.s)) := hL _ (W.comp_mem _ _ ρ.hs φ.hs)
  rw [← cancel_epi (L.map (ρ.s ≫ φ.s))]
  have key : L.map (ρ.s ≫ φ.s) ≫ (φ.comp₀ ψ ρ).map L hL = L.map (ρ.f ≫ ψ.f) :=
    map_s_comp_map (φ.comp₀ ψ ρ) L hL
  rw [key, L.map_comp, assoc, map_s_comp_map_assoc, ← L.map_comp_assoc, h, L.map_comp, assoc,
    map_s_comp_map, L.map_comp]

/-- Under a calculus of right fractions, a square completing a roof composition exists. -/
lemma exists_comp_square [W.HasRightCalculusOfFractions] {X Y Z : C} (φ : W.RightFraction X Y)
    (ψ : W.RightFraction Y Z) :
    ∃ ρ : W.RightFraction φ.X' ψ.X', ρ.s ≫ φ.f = ρ.f ≫ ψ.s :=
  HasRightCalculusOfFractions.exists_rightFraction (LeftFraction.mk φ.f ψ.s ψ.hs)

/-- Under a calculus of right fractions, the class of the composite roof does not depend on the
square chosen nor on the representatives of the two roofs. -/
lemma rightFractionRel_comp₀ [W.HasRightCalculusOfFractions] {X Y Z : C}
    {φ₁ φ₂ : W.RightFraction X Y} {ψ₁ ψ₂ : W.RightFraction Y Z}
    (hφ : RightFractionRel φ₁ φ₂) (hψ : RightFractionRel ψ₁ ψ₂)
    (ρ₁ : W.RightFraction φ₁.X' ψ₁.X') (h₁ : ρ₁.s ≫ φ₁.f = ρ₁.f ≫ ψ₁.s)
    (ρ₂ : W.RightFraction φ₂.X' ψ₂.X') (h₂ : ρ₂.s ≫ φ₂.f = ρ₂.f ≫ ψ₂.s) :
    RightFractionRel (φ₁.comp₀ ψ₁ ρ₁) (φ₂.comp₀ ψ₂ ρ₂) := by
  rw [← map_eq_iff W.Q W] at hφ hψ ⊢
  rw [← map_comp_map_eq_map _ _ _ h₁, ← map_comp_map_eq_map _ _ _ h₂, hφ, hψ]

/-- The roof `(𝟙, 𝟙)` is a left unit for the roof composition, up to `RightFractionRel`. -/
lemma rightFractionRel_ofHom_id_comp₀ [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) (ρ : W.RightFraction (ofHom W (𝟙 X)).X' φ.X')
    (h : ρ.s ≫ (ofHom W (𝟙 X)).f = ρ.f ≫ φ.s) :
    RightFractionRel ((ofHom W (𝟙 X)).comp₀ φ ρ) φ := by
  rw [← map_eq_iff W.Q W, ← map_comp_map_eq_map _ _ _ h, map_ofHom, Functor.map_id, id_comp]

/-- The roof `(𝟙, 𝟙)` is a right unit for the roof composition, up to `RightFractionRel`. -/
lemma rightFractionRel_comp₀_ofHom_id [W.HasRightCalculusOfFractions] {X Y : C}
    (φ : W.RightFraction X Y) (ρ : W.RightFraction φ.X' (ofHom W (𝟙 Y)).X')
    (h : ρ.s ≫ φ.f = ρ.f ≫ (ofHom W (𝟙 Y)).s) :
    RightFractionRel (φ.comp₀ (ofHom W (𝟙 Y)) ρ) φ := by
  rw [← map_eq_iff W.Q W, ← map_comp_map_eq_map _ _ _ h, map_ofHom, Functor.map_id, comp_id]

/-- The roof composition is associative, up to `RightFractionRel`. -/
lemma rightFractionRel_comp₀_assoc [W.HasRightCalculusOfFractions] {X Y Z T : C}
    (φ : W.RightFraction X Y) (ψ : W.RightFraction Y Z) (χ : W.RightFraction Z T)
    (ρ₁ : W.RightFraction φ.X' ψ.X') (h₁ : ρ₁.s ≫ φ.f = ρ₁.f ≫ ψ.s)
    (ρ₂ : W.RightFraction (φ.comp₀ ψ ρ₁).X' χ.X')
    (h₂ : ρ₂.s ≫ (φ.comp₀ ψ ρ₁).f = ρ₂.f ≫ χ.s)
    (ρ₃ : W.RightFraction ψ.X' χ.X') (h₃ : ρ₃.s ≫ ψ.f = ρ₃.f ≫ χ.s)
    (ρ₄ : W.RightFraction φ.X' (ψ.comp₀ χ ρ₃).X')
    (h₄ : ρ₄.s ≫ φ.f = ρ₄.f ≫ (ψ.comp₀ χ ρ₃).s) :
    RightFractionRel ((φ.comp₀ ψ ρ₁).comp₀ χ ρ₂) (φ.comp₀ (ψ.comp₀ χ ρ₃) ρ₄) := by
  rw [← map_eq_iff W.Q W, ← map_comp_map_eq_map _ _ _ h₂, ← map_comp_map_eq_map _ _ _ h₄,
    ← map_comp_map_eq_map _ _ _ h₁, ← map_comp_map_eq_map _ _ _ h₃, assoc]

end RightFraction

end MorphismProperty

end CategoryTheory

namespace DerivedCategory

open CategoryTheory MorphismProperty

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "K" => HomotopyCategory C (ComplexShape.up ℤ)
local notation "S" => HomotopyCategory.quasiIso C (ComplexShape.up ℤ)

/-- Roofs in `K(A)` (with quasi-isomorphisms as denominators) can be composed: a square
completing the composition exists. -/
@[weil "lem_fka2_derived_category_composition_well_defined"]
lemma exists_rightFraction_comp_square {X Y Z : K} (φ : RightFraction S X Y)
    (ψ : RightFraction S Y Z) :
    ∃ ρ : RightFraction S φ.X' ψ.X', ρ.s ≫ φ.f = ρ.f ≫ ψ.s :=
  RightFraction.exists_comp_square φ ψ

/-- The class of the composite of two roofs in `K(A)` is independent of the representatives
and of the square chosen. -/
@[weil "lem_fka2_derived_category_composition_well_defined"]
lemma rightFractionRel_comp₀ {X Y Z : K}
    {φ₁ φ₂ : RightFraction S X Y} {ψ₁ ψ₂ : RightFraction S Y Z}
    (hφ : RightFractionRel φ₁ φ₂) (hψ : RightFractionRel ψ₁ ψ₂)
    (ρ₁ : RightFraction S φ₁.X' ψ₁.X') (h₁ : ρ₁.s ≫ φ₁.f = ρ₁.f ≫ ψ₁.s)
    (ρ₂ : RightFraction S φ₂.X' ψ₂.X') (h₂ : ρ₂.s ≫ φ₂.f = ρ₂.f ≫ ψ₂.s) :
    RightFractionRel (φ₁.comp₀ ψ₁ ρ₁) (φ₂.comp₀ ψ₂ ρ₂) :=
  RightFraction.rightFractionRel_comp₀ hφ hψ ρ₁ h₁ ρ₂ h₂

/-- The identity roof `id/id` is a left unit for the roof composition. -/
@[weil "lem_fka2_derived_category_composition_well_defined"]
lemma rightFractionRel_ofHom_id_comp₀ {X Y : K} (φ : RightFraction S X Y)
    (ρ : RightFraction S (RightFraction.ofHom S (𝟙 X)).X' φ.X')
    (h : ρ.s ≫ (RightFraction.ofHom S (𝟙 X)).f = ρ.f ≫ φ.s) :
    RightFractionRel ((RightFraction.ofHom S (𝟙 X)).comp₀ φ ρ) φ :=
  RightFraction.rightFractionRel_ofHom_id_comp₀ φ ρ h

/-- The identity roof `id/id` is a right unit for the roof composition. -/
@[weil "lem_fka2_derived_category_composition_well_defined"]
lemma rightFractionRel_comp₀_ofHom_id {X Y : K} (φ : RightFraction S X Y)
    (ρ : RightFraction S φ.X' (RightFraction.ofHom S (𝟙 Y)).X')
    (h : ρ.s ≫ φ.f = ρ.f ≫ (RightFraction.ofHom S (𝟙 Y)).s) :
    RightFractionRel (φ.comp₀ (RightFraction.ofHom S (𝟙 Y)) ρ) φ :=
  RightFraction.rightFractionRel_comp₀_ofHom_id φ ρ h

/-- The roof composition in `K(A)` is associative up to equivalence of roofs. -/
@[weil "lem_fka2_derived_category_composition_well_defined"]
lemma rightFractionRel_comp₀_assoc {X Y Z T : K}
    (φ : RightFraction S X Y) (ψ : RightFraction S Y Z) (χ : RightFraction S Z T)
    (ρ₁ : RightFraction S φ.X' ψ.X') (h₁ : ρ₁.s ≫ φ.f = ρ₁.f ≫ ψ.s)
    (ρ₂ : RightFraction S (φ.comp₀ ψ ρ₁).X' χ.X')
    (h₂ : ρ₂.s ≫ (φ.comp₀ ψ ρ₁).f = ρ₂.f ≫ χ.s)
    (ρ₃ : RightFraction S ψ.X' χ.X') (h₃ : ρ₃.s ≫ ψ.f = ρ₃.f ≫ χ.s)
    (ρ₄ : RightFraction S φ.X' (ψ.comp₀ χ ρ₃).X')
    (h₄ : ρ₄.s ≫ φ.f = ρ₄.f ≫ (ψ.comp₀ χ ρ₃).s) :
    RightFractionRel ((φ.comp₀ ψ ρ₁).comp₀ χ ρ₂) (φ.comp₀ (ψ.comp₀ χ ρ₃) ρ₄) :=
  RightFraction.rightFractionRel_comp₀_assoc φ ψ χ ρ₁ h₁ ρ₂ h₂ ρ₃ h₃ ρ₄ h₄

variable [HasDerivedCategory.{w} C]

/-- In `D(A)`, the composition of the morphisms given by two roofs is the morphism given by
their composite roof. -/
@[weil "lem_fka2_derived_category_composition_well_defined"]
lemma rightFraction_map_comp_map {X Y Z : K} (φ : RightFraction S X Y)
    (ψ : RightFraction S Y Z) (ρ : RightFraction S φ.X' ψ.X') (h : ρ.s ≫ φ.f = ρ.f ≫ ψ.s) :
    φ.map Qh (Localization.inverts _ _) ≫ ψ.map Qh (Localization.inverts _ _) =
      (φ.comp₀ ψ ρ).map Qh (Localization.inverts _ _) :=
  RightFraction.map_comp_map_eq_map φ ψ ρ h _ _

/-- In `D(A)`, the morphism given by the roof `id/id` is the identity. -/
@[weil "lem_fka2_derived_category_composition_well_defined"]
lemma rightFraction_map_ofHom_id (X : K) :
    (RightFraction.ofHom S (𝟙 X)).map Qh (Localization.inverts _ _) = 𝟙 (Qh.obj X) := by
  simp

end DerivedCategory

end
