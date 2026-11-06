module

public import Weil.Attr
public import Weil.CategoryTheory.Sites.Plus
public import Weil.CategoryTheory.Sites.PlusPresheafExistsUnique
public import Weil.Defs.AlgebraicGeometry.Sites.CoveringPullback
public import Weil.Defs.CategoryTheory.Sites.PlusFunctorialMap
public import Weil.Defs.CategoryTheory.Sites.PlusPresheaf

/-!
# Naturality of the map induced on plus presheaves

Let `A` be a commutative ring and `α : F₁ ⟶ F₂` a morphism of presheaves on the étale category
`Et(A)`. The maps `α̃_B : F̃₁(B) → F̃₂(B)`, `[𝔅, s] ↦ [𝔅, α_𝔅(s)]`, form a morphism of
presheaves `α̃ : F̃₁ ⟶ F̃₂` between the plus presheaves. Indeed, for `f : B ⟶ B'` and a class
`[𝔅, s] ∈ F̃₁(B)`, choose a morphism of coverings `φ : 𝔅 ⟶ 𝔅'` over `f`; since
`α_{𝔅'} ∘ φ_* = φ_* ∘ α_𝔅`,
`F̃₂(f)(α̃_B [𝔅, s]) = [𝔅', φ_* α_𝔅(s)] = [𝔅', α_{𝔅'} φ_* s] = α̃_{B'}(F̃₁(f)[𝔅, s])`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.homOfHom P₁ P₂ α`: the morphism of presheaves
  of sets `α̃ : F̃₁ ⟶ F̃₂`.
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.homOfHom P₁ P₂ α`: the morphism of presheaves
  of abelian groups `α̃ : F̃₁ ⟶ F̃₂`.

## Main results

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.map_plusConstructionMap`,
  `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.map_comp_addPlusConstructionMap`:
  `F̃₂(f) ∘ α̃_B = α̃_{B'} ∘ F̃₁(f)`.

## Implementation notes

The plus presheaf of a presheaf is unique (`PlusPresheaf.instUnique`), so the statements are
made for arbitrary plus presheaves `P₁` of `F₁` and `P₂` of `F₂`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

open Covering

namespace PlusPresheaf

variable {F₁ F₂ F₃ : Presheaf A (Type v)}

/-- `F̃₂(f)(α̃_B t) = α̃_{B'}(F̃₁(f) t)` for a morphism of presheaves of sets `α : F₁ ⟶ F₂`,
a morphism `f : B ⟶ B'` and plus presheaves `P₁` of `F₁` and `P₂` of `F₂`. -/
@[weil "lem_fk101_plus_functorial_map_natural"]
theorem map_plusConstructionMap (P₁ : PlusPresheaf.{w} F₁) (P₂ : PlusPresheaf.{w} F₂)
    (α : F₁ ⟶ F₂) {B B' : EtaleCategory A} (f : B ⟶ B') (t : plusConstruction.{w} F₁ B) :
    P₂.map f (plusConstruction.map α t) = plusConstruction.map α (P₁.map f t) := by
  obtain ⟨𝔅, s, rfl⟩ := plusConstruction.exists_mk t
  obtain ⟨𝔅', ⟨φ⟩⟩ := exists_homOver f 𝔅
  rw [plusConstruction.map_mk, P₂.map_mk f 𝔅 𝔅' φ, P₁.map_mk f 𝔅 𝔅' φ,
    plusConstruction.map_mk, HomOver.sectionsMap_coveringSectionsMap]

/-- The morphism of presheaves of sets `α̃ : F̃₁ ⟶ F̃₂`, `α̃_B [𝔅, s] = [𝔅, α_𝔅(s)]`, induced
on plus presheaves by a morphism of presheaves `α : F₁ ⟶ F₂`. -/
@[weil "lem_fk101_plus_functorial_map_natural", simps]
def homOfHom (P₁ : PlusPresheaf.{w} F₁) (P₂ : PlusPresheaf.{w} F₂) (α : F₁ ⟶ F₂) :
    P₁.toPresheaf ⟶ P₂.toPresheaf where
  app B := ↾(plusConstruction.map α)
  naturality _ _ f := by
    ext t
    exact (map_plusConstructionMap P₁ P₂ α f t).symm

@[simp]
lemma homOfHom_id (P : PlusPresheaf.{w} F₁) : homOfHom P P (𝟙 F₁) = 𝟙 P.toPresheaf := by
  ext B t
  exact congrFun (plusConstruction.map_id (B := B)) t

lemma homOfHom_comp (P₁ : PlusPresheaf.{w} F₁) (P₂ : PlusPresheaf.{w} F₂)
    (P₃ : PlusPresheaf.{w} F₃) (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) :
    homOfHom P₁ P₃ (α ≫ β) = homOfHom P₁ P₂ α ≫ homOfHom P₂ P₃ β := by
  ext B t
  exact congrFun (plusConstruction.map_comp (B := B) α β) t

end PlusPresheaf

namespace AddPlusPresheaf

variable {F₁ F₂ F₃ : Presheaf A AddCommGrpCat.{v}}

/-- `F̃₂(f) ∘ α̃_B = α̃_{B'} ∘ F̃₁(f)` for a morphism of presheaves of abelian groups
`α : F₁ ⟶ F₂`, a morphism `f : B ⟶ B'` and plus presheaves `P₁` of `F₁` and `P₂` of `F₂`. -/
@[weil "lem_fk101_plus_functorial_map_natural"]
theorem map_comp_addPlusConstructionMap (P₁ : AddPlusPresheaf.{w} F₁)
    (P₂ : AddPlusPresheaf.{w} F₂) (α : F₁ ⟶ F₂) {B B' : EtaleCategory A} (f : B ⟶ B') :
    addPlusConstruction.map α ≫ P₂.map f = P₁.map f ≫ addPlusConstruction.map α := by
  ext1
  refine addPlusConstruction.hom_ext fun 𝔅 s ↦ ?_
  obtain ⟨𝔅', ⟨φ⟩⟩ := exists_homOver f 𝔅
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [addPlusConstruction.map_mk, P₂.map_mk f 𝔅 𝔅' φ, P₁.map_mk f 𝔅 𝔅' φ,
    addPlusConstruction.map_mk]
  exact congrArg (addPlusConstruction.mk 𝔅') (DFunLike.congr_fun
    (HomOver.sectionsAddMonoidHom_comp_coveringSectionsAddMonoidHom φ α) s)

/-- The morphism of presheaves of abelian groups `α̃ : F̃₁ ⟶ F̃₂`,
`α̃_B [𝔅, s] = [𝔅, α_𝔅(s)]`, induced on plus presheaves by a morphism of presheaves
`α : F₁ ⟶ F₂`. -/
@[weil "lem_fk101_plus_functorial_map_natural", simps]
def homOfHom (P₁ : AddPlusPresheaf.{w} F₁) (P₂ : AddPlusPresheaf.{w} F₂) (α : F₁ ⟶ F₂) :
    P₁.toPresheaf ⟶ P₂.toPresheaf where
  app _ := addPlusConstruction.map α
  naturality _ _ f := (map_comp_addPlusConstructionMap P₁ P₂ α f).symm

@[simp]
lemma homOfHom_id (P : AddPlusPresheaf.{w} F₁) : homOfHom P P (𝟙 F₁) = 𝟙 P.toPresheaf := by
  ext : 2
  exact addPlusConstruction.map_id

lemma homOfHom_comp (P₁ : AddPlusPresheaf.{w} F₁) (P₂ : AddPlusPresheaf.{w} F₂)
    (P₃ : AddPlusPresheaf.{w} F₃) (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) :
    homOfHom P₁ P₃ (α ≫ β) = homOfHom P₁ P₂ α ≫ homOfHom P₂ P₃ β := by
  ext : 2
  exact addPlusConstruction.map_comp α β

end AddPlusPresheaf

end EtaleCategory

end AlgebraicGeometry
