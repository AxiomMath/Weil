module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringMorphism
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringSectionsMap
public import WeilFrontier.Defs.CategoryTheory.Sites.PlusPresheaf
public import WeilFrontier.Defs.CategoryTheory.Sites.PlusUnit

/-!
# Restricting a class of the plus construction to a member of its covering

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)`, `F̃` a plus
presheaf of `F`, `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` a covering of `B` and `s = (sᵢ)ᵢ ∈ F(𝔅)`. Then
`F̃(gᵢ)([𝔅, s]) = ι_{F,Bᵢ}(sᵢ)` for every index `i`.

Indeed, `(∗ ↦ i, (id_{Bᵢ}))` is a morphism from `𝔅` to the covering `(id_{Bᵢ})` of `Bᵢ` over
`gᵢ`, and it sends `s` to `sᵢ`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.Covering.toSelf 𝔅 i`: the morphism of coverings from `𝔅` to
  `(id_{Bᵢ})` over `gᵢ`.

## Main results

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.toPresheaf_map_mk_eq_toPlusConstruction`:
  `F̃(gᵢ)([𝔅, s]) = ι_{F,Bᵢ}(sᵢ)` for a presheaf of sets.
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.toPresheaf_map_mk_eq_toAddPlusConstruction`:
  the same for a presheaf of abelian groups.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

namespace Covering

variable {B : EtaleCategory A}

/-- The morphism `(∗ ↦ i, (id_{Bᵢ}))` of coverings from `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` to the covering
`(id_{Bᵢ})` of `Bᵢ`, over `gᵢ`. -/
@[simps]
def toSelf (𝔅 : Covering.{w} B) (i : 𝔅.ι) : HomOver (𝔅.map i) 𝔅 (self.{w} (𝔅.obj i)) where
  σ _ := i
  h _ := 𝟙 _
  comm _ := by simp

/-- The morphism `𝔅 ⟶ (id_{Bᵢ})` over `gᵢ` sends a section `s` of a presheaf of sets over `𝔅` to
its component `sᵢ`. -/
lemma toSelf_sectionsMap (F : EtaleCategory A ⥤ Type v) (𝔅 : Covering.{w} B) (i : 𝔅.ι)
    (s : coveringSections F 𝔅.map) :
    (𝔅.toSelf i).sectionsMap F s = (coveringSectionsSelfEquiv.{w} F (𝔅.obj i)).symm (s.1 i) :=
  Subtype.ext <| funext fun _ ↦ F.map_id_apply _ _

/-- The morphism `𝔅 ⟶ (id_{Bᵢ})` over `gᵢ` sends a section `s` of a presheaf of abelian groups
over `𝔅` to its component `sᵢ`. -/
lemma toSelf_sectionsAddMonoidHom (F : EtaleCategory A ⥤ AddCommGrpCat.{v})
    (𝔅 : Covering.{w} B) (i : 𝔅.ι) (s : coveringSectionsAddSubgroup F 𝔅.map) :
    HomOver.sectionsAddMonoidHom F (𝔅.toSelf i) s =
      (coveringSectionsAddSubgroupSelfEquiv.{w} F (𝔅.obj i)).symm (s.1 i) :=
  Subtype.ext <| funext fun _ ↦ by
    change (F.map (𝟙 _)) (s.1 i) = s.1 i
    simp

end Covering

open Covering

namespace PlusPresheaf

variable {F : Presheaf A (Type v)} (P : PlusPresheaf.{w} F)

/-- For a covering `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` and `s ∈ F(𝔅)`, `F̃(gᵢ)([𝔅, s]) = ι_{F,Bᵢ}(sᵢ)`. -/
@[weil "lem_fk101_plus_restriction_of_class"]
theorem toPresheaf_map_mk_eq_toPlusConstruction {B : EtaleCategory A} (𝔅 : Covering.{w} B)
    (s : coveringSections F 𝔅.map) (i : 𝔅.ι) :
    P.toPresheaf.map (𝔅.map i) (plusConstruction.mk 𝔅 s) =
      toPlusConstruction.{w} F (𝔅.obj i) (s.1 i) := by
  rw [P.toPresheaf_map_mk (𝔅.map i) 𝔅 (self.{w} (𝔅.obj i)) (𝔅.toSelf i) s,
    toSelf_sectionsMap, toPlusConstruction_apply]

end PlusPresheaf

namespace AddPlusPresheaf

variable {F : Presheaf A AddCommGrpCat.{v}} (P : AddPlusPresheaf.{w} F)

/-- For a covering `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` and `s ∈ F(𝔅)`, `F̃(gᵢ)([𝔅, s]) = ι_{F,Bᵢ}(sᵢ)`, for a
presheaf of abelian groups. -/
@[weil "lem_fk101_plus_restriction_of_class"]
theorem toPresheaf_map_mk_eq_toAddPlusConstruction {B : EtaleCategory A} (𝔅 : Covering.{w} B)
    (s : coveringSectionsAddSubgroup F 𝔅.map) (i : 𝔅.ι) :
    P.toPresheaf.map (𝔅.map i) (addPlusConstruction.mk 𝔅 s) =
      toAddPlusConstruction.{w} F (𝔅.obj i) (s.1 i) := by
  rw [P.toPresheaf_map_mk (𝔅.map i) 𝔅 (self.{w} (𝔅.obj i)) (𝔅.toSelf i) s,
    toSelf_sectionsAddMonoidHom, toAddPlusConstruction_apply]

end AddPlusPresheaf

end EtaleCategory

end AlgebraicGeometry
