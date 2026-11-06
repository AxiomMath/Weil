module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.CoveringMorphism
public import Weil.Defs.CategoryTheory.Sites.Plus

/-!
# Elements of the plus construction are single classes

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)` and `B` an object of
`Et(A)`. Every element of the plus construction `F̃(B) = colim_{𝔅 ∈ Cov(B)} F(𝔅)` is a single
class `[𝔅, s]`, for one covering `𝔅` of `B` and one `s ∈ F(𝔅)`.

For a presheaf of sets this is the description of the colimit in `Type`
(`AlgebraicGeometry.EtaleCategory.plusConstruction.exists_mk`). For a presheaf of abelian groups an
element of `F̃(B)` is a finite sum `∑ₗ [𝔅ₗ, sₗ]`; since the coverings of `B` are directed
(`AlgebraicGeometry.EtaleCategory.Covering.cocone_objs`), the classes can be moved to a common
covering `𝔅` and added there.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.Covering.single B`: the covering `(𝟙 : B ⟶ B)` of `B`.

## Main results

- `AlgebraicGeometry.EtaleCategory.addPlusConstruction.exists_mk`: every element of `F̃(B)`, for a
  presheaf of abelian groups `F`, is a class `[𝔅, s]`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

namespace Covering

/-- The covering `(𝟙 : B ⟶ B)` of `B`, indexed by a point. -/
def single (B : EtaleCategory A) : Covering.{w} B where
  ι := PUnit
  obj _ := B
  map _ := 𝟙 B
  isCovering :=
    ⟨inferInstance, fun p ↦ ⟨PUnit.unit, p, PrimeSpectrum.ext (Ideal.ext fun _ ↦ Iff.rfl)⟩⟩

end Covering

open Covering

namespace addPlusConstruction

variable {F : EtaleCategory A ⥤ AddCommGrpCat.{v}} {B : EtaleCategory A}

/-- Every element of the plus construction `F̃(B)` of a presheaf of abelian groups is a single
class `[𝔅, s]`, for one covering `𝔅` of `B` and one `s ∈ F(𝔅)`. -/
@[weil "lem_fk101_plus_construction_element_representative"]
theorem exists_mk (t : addPlusConstruction.{w} F B) :
    ∃ (𝔅 : Covering.{w} B) (s : coveringSectionsAddSubgroup F 𝔅.map), mk 𝔅 s = t := by
  classical
  -- The single classes form an additive subgroup of `F̃(B)` containing every class.
  let S : AddSubgroup (addPlusConstruction.{w} F B) :=
    { carrier := {t | ∃ (𝔅 : Covering.{w} B) (s : coveringSectionsAddSubgroup F 𝔅.map),
        mk 𝔅 s = t}
      zero_mem' := ⟨single B, 0, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨𝔅₁, s₁, rfl⟩ ⟨𝔅₂, s₂, rfl⟩
        obtain ⟨𝔅, φ₁, φ₂, -⟩ := cocone_objs 𝔅₁ 𝔅₂
        refine ⟨𝔅, HomOver.sectionsAddMonoidHom F φ₁ s₁ + HomOver.sectionsAddMonoidHom F φ₂ s₂, ?_⟩
        rw [map_add, mk_sectionsAddMonoidHom, mk_sectionsAddMonoidHom]
      neg_mem' := by
        rintro _ ⟨𝔅, s, rfl⟩
        exact ⟨𝔅, -s, map_neg _ _⟩ }
  -- The corestriction of `F̃(B)` to `S`, followed by the inclusion, is the identity.
  let f : addPlusConstruction.{w} F B →+ S :=
    lift (fun 𝔅 ↦ (mk 𝔅).codRestrict S fun s ↦ ⟨𝔅, s, rfl⟩) fun φ ↦ by
      ext s
      simp
  have h : S.subtype.comp f = AddMonoidHom.id _ := hom_ext fun 𝔅 s ↦ by simp [f]
  have := DFunLike.congr_fun h t
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply] at this
  rw [← this]
  exact (f t).2

end addPlusConstruction

end EtaleCategory

end AlgebraicGeometry
