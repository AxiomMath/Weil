module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Sites.ConcreteSheafification
public import WeilFrontier.Defs.CategoryTheory.Sites.CoveringRestriction
public import WeilFrontier.Defs.CategoryTheory.Sites.PlusUnit

/-!
# Equality of images under the unit of the plus construction

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)`, `B` an object of
`Et(A)` and `s, t ∈ F(B)`. Then `ι_{F,B}(s) = ι_{F,B}(t)` in `F̃(B)` if and only if there is a
covering `(c_l : B ⟶ C_l)_l` of `B` with `F(c_l)(s) = F(c_l)(t)` for all `l`.

There is exactly one morphism of coverings `(id_B) ⟶ 𝔆` for every covering `𝔆 = (c_l)_l` of
`B`: its components are forced to be the `c_l`. It sends `s ∈ F(B) = F((id_B))` to the
restriction `ρ_𝔆(s) = (F(c_l)(s))_l`. The claim then follows from the criterion for equality of
classes in the plus construction.

## Main results

- `AlgebraicGeometry.EtaleCategory.toPlusConstruction_eq_iff_exists`: the criterion for a
  presheaf of sets.
- `AlgebraicGeometry.EtaleCategory.toAddPlusConstruction_eq_iff_exists`: the criterion for a
  presheaf of abelian groups.

## Implementation notes

Mathlib's `CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk` together with
`CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists` is the analogous statement for the
plus construction indexed by covering sieves; here the colimit runs over the category of covering
families of `B`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}} {B : EtaleCategory A}

open Covering

namespace Covering

/-- The components of a morphism of coverings `(id_B) ⟶ 𝔆` are the maps of `𝔆`. -/
lemma Hom.h_self (𝔆 : Covering.{w} B) (φ : self.{w} B ⟶ 𝔆) (l : 𝔆.ι) :
    HomOver.h φ l = 𝔆.map l := by
  exact (Category.id_comp _).symm.trans (Hom.comm φ l)

/-- The morphism of coverings `(id_B) ⟶ 𝔆`, with components the maps `c_l` of `𝔆`. -/
def toSelfHom (𝔆 : Covering.{w} B) : self.{w} B ⟶ 𝔆 :=
  HomOver.toHom
    { σ := fun _ ↦ PUnit.unit
      h := 𝔆.map
      comm := fun _ ↦ (Category.id_comp _).trans (Category.id_comp _).symm }

end Covering

/-- The map induced by a morphism of coverings `(id_B) ⟶ 𝔆` sends `s ∈ F(B) = F((id_B))` to the
restriction `ρ_𝔆(s) = (F(c_l)(s))_l`. -/
lemma sectionsMap_coveringSectionsSelfEquiv_symm (F : EtaleCategory A ⥤ Type v)
    (𝔆 : Covering.{w} B) (φ : self.{w} B ⟶ 𝔆) (s : F.obj B) :
    HomOver.sectionsMap F φ ((coveringSectionsSelfEquiv.{w} F B).symm s) =
      coveringRestriction F 𝔆.map s :=
  Subtype.ext <| funext fun l ↦ by
    rw [HomOver.sectionsMap_apply, coveringSectionsSelfEquiv_symm_apply_coe,
      coveringRestriction_apply, Hom.h_self]
    rfl

/-- **Equality under the unit of the plus construction** (presheaves of sets).
`ι_{F,B}(s) = ι_{F,B}(t)` if and only if there is a covering `(c_l : B ⟶ C_l)_l` of `B` with
`F(c_l)(s) = F(c_l)(t)` for all `l`. -/
@[weil "lem_fk101_plus_unit_equal_iff"]
theorem toPlusConstruction_eq_iff_exists (F : EtaleCategory A ⥤ Type v) (s t : F.obj B) :
    toPlusConstruction.{w} F B s = toPlusConstruction.{w} F B t ↔
      ∃ 𝔆 : Covering.{w} B, ∀ l, F.map (𝔆.map l) s = F.map (𝔆.map l) t := by
  rw [toPlusConstruction_apply, toPlusConstruction_apply, plusConstruction.mk_eq_mk_iff_exists]
  constructor
  · rintro ⟨𝔆, φ₁, φ₂, e⟩
    refine ⟨𝔆, fun l ↦ ?_⟩
    rw [sectionsMap_coveringSectionsSelfEquiv_symm, sectionsMap_coveringSectionsSelfEquiv_symm]
      at e
    simpa using congrFun (congrArg Subtype.val e) l
  · rintro ⟨𝔆, h⟩
    refine ⟨𝔆, toSelfHom 𝔆, toSelfHom 𝔆, ?_⟩
    rw [sectionsMap_coveringSectionsSelfEquiv_symm, sectionsMap_coveringSectionsSelfEquiv_symm]
    exact Subtype.ext (funext h)

/-- The homomorphism induced by a morphism of coverings `(id_B) ⟶ 𝔆` sends
`s ∈ F(B) = F((id_B))` to the family `(F(c_l)(s))_l`. -/
lemma sectionsAddMonoidHom_coveringSectionsAddSubgroupSelfEquiv_symm_coe
    (F : EtaleCategory A ⥤ AddCommGrpCat.{v}) (𝔆 : Covering.{w} B) (φ : self.{w} B ⟶ 𝔆)
    (s : F.obj B) (l : 𝔆.ι) :
    (HomOver.sectionsAddMonoidHom F φ
      ((coveringSectionsAddSubgroupSelfEquiv.{w} F B).symm s)).1 l = F.map (𝔆.map l) s := by
  change F.map (HomOver.h φ l) s = _
  rw [Hom.h_self]
  rfl

/-- **Equality under the unit of the plus construction** (presheaves of abelian groups).
`ι_{F,B}(s) = ι_{F,B}(t)` if and only if there is a covering `(c_l : B ⟶ C_l)_l` of `B` with
`F(c_l)(s) = F(c_l)(t)` for all `l`. -/
@[weil "lem_fk101_plus_unit_equal_iff"]
theorem toAddPlusConstruction_eq_iff_exists (F : EtaleCategory A ⥤ AddCommGrpCat.{v})
    (s t : F.obj B) :
    toAddPlusConstruction.{w} F B s = toAddPlusConstruction.{w} F B t ↔
      ∃ 𝔆 : Covering.{w} B, ∀ l, F.map (𝔆.map l) s = F.map (𝔆.map l) t := by
  rw [toAddPlusConstruction_apply, toAddPlusConstruction_apply,
    addPlusConstruction.mk_eq_mk_iff_exists]
  constructor
  · rintro ⟨𝔆, φ₁, φ₂, e⟩
    refine ⟨𝔆, fun l ↦ ?_⟩
    have := congrFun (congrArg Subtype.val e) l
    rwa [sectionsAddMonoidHom_coveringSectionsAddSubgroupSelfEquiv_symm_coe,
      sectionsAddMonoidHom_coveringSectionsAddSubgroupSelfEquiv_symm_coe] at this
  · rintro ⟨𝔆, h⟩
    refine ⟨𝔆, toSelfHom 𝔆, toSelfHom 𝔆, Subtype.ext (funext fun l ↦ ?_)⟩
    rw [sectionsAddMonoidHom_coveringSectionsAddSubgroupSelfEquiv_symm_coe,
      sectionsAddMonoidHom_coveringSectionsAddSubgroupSelfEquiv_symm_coe]
    exact h l

end EtaleCategory

end AlgebraicGeometry
