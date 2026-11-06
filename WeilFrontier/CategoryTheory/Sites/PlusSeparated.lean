module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.CoveringMorphism
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleCoveringFk101
public import WeilFrontier.CategoryTheory.Sites.Plus
public import WeilFrontier.CategoryTheory.Sites.PlusPresheafExistsUnique
public import WeilFrontier.CategoryTheory.Sites.PlusUnitEqualIff
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringMorphism
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringSectionsMap
public import WeilFrontier.Defs.CategoryTheory.Sites.CoveringRestriction
public import WeilFrontier.Defs.CategoryTheory.Sites.Plus
public import WeilFrontier.Defs.CategoryTheory.Sites.PlusPresheaf

/-!
# The plus presheaf is separated

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)` and `F̃` its plus
presheaf. For every object `B` of `Et(A)` and every covering `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` of `B`, the
restriction map `ρ_𝔅 : F̃(B) → F̃(𝔅)` is injective.

The restriction of a class `[𝔅, s]` along a member `gᵢ` of `𝔅` is the image `ι_{F,Bᵢ}(sᵢ)` of
its component under the unit of the plus construction. Given `x, y ∈ F̃(B)` with the same
restrictions to `𝔅`, write `x = [𝔄, a]` and `y = [𝔄, b]` over a common covering `𝔄` admitting a
morphism of coverings `(σ, h) : 𝔅 ⟶ 𝔄`. Then `ι(aₖ) = ι(bₖ)` for every member `aₖ : B ⟶ Aₖ`
of `𝔄`, so `aₖ` and `bₖ` agree on a covering `(c_{kl})_l` of `Aₖ`; on the composite covering
`(c_{kl} ∘ aₖ)_{(k,l)}` of `B` the two families become equal, hence `x = y`.

## Main results

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.injective_coveringRestriction`: the plus
  presheaf of a presheaf of sets is separated.
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.injective_coveringRestriction`: the plus
  presheaf of a presheaf of abelian groups is separated.

## Implementation notes

Mathlib's `CategoryTheory.GrothendieckTopology.Plus.sep` is the analogous statement for the plus
construction indexed by covering sieves; here the plus construction is the colimit over the
category of covering families of `B`.

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

/-- The morphism of coverings over the member `gᵢ : B ⟶ Bᵢ` of a covering `𝔅` of `B`, from `𝔅`
to the covering `(id_{Bᵢ})` of `Bᵢ`: it picks the index `i`, with component `id_{Bᵢ}`. -/
private def homOverSelf (𝔅 : Covering.{w} B) (i : 𝔅.ι) :
    HomOver (𝔅.map i) 𝔅 (self.{w} (𝔅.obj i)) where
  σ _ := i
  h _ := 𝟙 _
  comm _ := rfl

/-- The composite covering `(c_{kl} ∘ aₖ)_{(k,l)}` of `B`, for a covering `𝔄 = (aₖ)ₖ` of `B` and
coverings `𝔆ₖ = (c_{kl})_l` of its members `Aₖ`. -/
private def bind (𝔄 : Covering.{w} B) (𝔆 : ∀ k, Covering.{w} (𝔄.obj k)) : Covering.{w} B where
  ι := Σ k, (𝔆 k).ι
  obj kl := (𝔆 kl.1).obj kl.2
  map kl := 𝔄.map kl.1 ≫ (𝔆 kl.1).map kl.2
  isCovering := 𝔄.isCovering.comp fun k ↦ (𝔆 k).isCovering

/-- The morphism of coverings `𝔄 ⟶ (c_{kl} ∘ aₖ)_{(k,l)}`, `(k, l) ↦ k`, with components
`c_{kl}`. -/
private def toBind (𝔄 : Covering.{w} B) (𝔆 : ∀ k, Covering.{w} (𝔄.obj k)) : 𝔄 ⟶ 𝔄.bind 𝔆 :=
  HomOver.toHom
    { σ := Sigma.fst
      h kl := (𝔆 kl.1).map kl.2
      comm _ := (Category.id_comp _).symm }

end Covering

namespace PlusPresheaf

variable {F : Presheaf A (Type v)} (P : PlusPresheaf.{w} F)

/-- The restriction of a class `[𝔅, s]` along a member `gᵢ` of `𝔅` is `ι_{F,Bᵢ}(sᵢ)`. -/
private lemma map_mk_map (𝔅 : Covering.{w} B) (s : coveringSections F 𝔅.map) (i : 𝔅.ι) :
    P.map (𝔅.map i) (plusConstruction.mk 𝔅 s) = toPlusConstruction.{w} F (𝔅.obj i) (s.1 i) := by
  rw [P.map_mk _ 𝔅 _ (homOverSelf 𝔅 i), toPlusConstruction_apply]
  congr 1
  exact Subtype.ext <| funext fun _ ↦ show F.map (𝟙 _) (s.1 i) = s.1 i by simp

/-- If two classes over the same covering `𝔄` of `B` have the same restrictions along all the
members of `𝔄`, they are equal. -/
private lemma mk_eq_mk_of_map_eq (𝔄 : Covering.{w} B) (a b : coveringSections F 𝔄.map)
    (h : ∀ k, P.map (𝔄.map k) (plusConstruction.mk 𝔄 a) =
      P.map (𝔄.map k) (plusConstruction.mk 𝔄 b)) :
    plusConstruction.mk 𝔄 a = plusConstruction.mk 𝔄 b := by
  have hk : ∀ k, ∃ 𝔆 : Covering.{w} (𝔄.obj k), ∀ l,
      F.map ((𝔆.map l)) (a.1 k) = F.map (𝔆.map l) (b.1 k) := fun k ↦ by
    rw [← toPlusConstruction_eq_iff_exists, ← map_mk_map, ← map_mk_map]
    exact h k
  choose 𝔆 h𝔆 using hk
  rw [← plusConstruction.mk_sectionsMap (toBind 𝔄 𝔆) a,
    ← plusConstruction.mk_sectionsMap (toBind 𝔄 𝔆) b]
  congr 1
  exact Subtype.ext <| funext fun kl ↦ h𝔆 kl.1 kl.2

/-- **The plus presheaf is separated** (presheaves of sets). For every covering `𝔅` of `B` the
restriction map `ρ_𝔅 : F̃(B) → F̃(𝔅)` is injective. -/
@[weil "lem_fk101_plus_separated"]
theorem injective_coveringRestriction (𝔅 : Covering.{w} B) :
    Function.Injective (coveringRestriction P.toPresheaf 𝔅.map) := by
  intro x y hxy
  have h : ∀ i, P.map (𝔅.map i) x = P.map (𝔅.map i) y := fun i ↦
    congrFun (congrArg Subtype.val hxy) i
  obtain ⟨𝔄₁, a, rfl⟩ := plusConstruction.exists_mk x
  obtain ⟨𝔄₂, b, rfl⟩ := plusConstruction.exists_mk y
  obtain ⟨𝔄₁₂, φ₁, φ₂, -⟩ := cocone_objs 𝔄₁ 𝔄₂
  obtain ⟨𝔄, ψ, χ, -⟩ := cocone_objs 𝔄₁₂ 𝔅
  rw [← plusConstruction.mk_sectionsMap (φ₁ ≫ ψ) a,
    ← plusConstruction.mk_sectionsMap (φ₂ ≫ ψ) b] at h ⊢
  refine P.mk_eq_mk_of_map_eq 𝔄 _ _ fun k ↦ ?_
  rw [← Hom.comm χ k, P.map_comp, P.map_comp, h]

end PlusPresheaf

namespace AddPlusPresheaf

variable {F : Presheaf A AddCommGrpCat.{v}} (P : AddPlusPresheaf.{w} F)

/-- The restriction of a class `[𝔅, s]` along a member `gᵢ` of `𝔅` is `ι_{F,Bᵢ}(sᵢ)`. -/
private lemma map_mk_map (𝔅 : Covering.{w} B) (s : coveringSectionsAddSubgroup F 𝔅.map)
    (i : 𝔅.ι) :
    P.map (𝔅.map i) (addPlusConstruction.mk 𝔅 s) =
      toAddPlusConstruction.{w} F (𝔅.obj i) (s.1 i) := by
  rw [P.map_mk _ 𝔅 _ (homOverSelf 𝔅 i), toAddPlusConstruction_apply]
  congr 1
  exact Subtype.ext <| funext fun _ ↦ show F.map (𝟙 _) (s.1 i) = s.1 i by simp

/-- If two classes over the same covering `𝔄` of `B` have the same restrictions along all the
members of `𝔄`, they are equal. -/
private lemma mk_eq_mk_of_map_eq (𝔄 : Covering.{w} B)
    (a b : coveringSectionsAddSubgroup F 𝔄.map)
    (h : ∀ k, P.map (𝔄.map k) (addPlusConstruction.mk 𝔄 a) =
      P.map (𝔄.map k) (addPlusConstruction.mk 𝔄 b)) :
    addPlusConstruction.mk 𝔄 a = addPlusConstruction.mk 𝔄 b := by
  have hk : ∀ k, ∃ 𝔆 : Covering.{w} (𝔄.obj k), ∀ l,
      F.map ((𝔆.map l)) (a.1 k) = F.map (𝔆.map l) (b.1 k) := fun k ↦ by
    rw [← toAddPlusConstruction_eq_iff_exists, ← map_mk_map, ← map_mk_map]
    exact h k
  choose 𝔆 h𝔆 using hk
  rw [← addPlusConstruction.mk_sectionsAddMonoidHom (toBind 𝔄 𝔆) a,
    ← addPlusConstruction.mk_sectionsAddMonoidHom (toBind 𝔄 𝔆) b]
  congr 1
  exact Subtype.ext <| funext fun kl ↦ h𝔆 kl.1 kl.2

/-- **The plus presheaf is separated** (presheaves of abelian groups). For every covering `𝔅` of
`B` the restriction homomorphism `ρ_𝔅 : F̃(B) → F̃(𝔅)` is injective. -/
@[weil "lem_fk101_plus_separated"]
theorem injective_coveringRestriction (𝔅 : Covering.{w} B) :
    Function.Injective (coveringRestrictionAddMonoidHom P.toPresheaf 𝔅.map) := by
  intro x y hxy
  have h : ∀ i, P.map (𝔅.map i) x = P.map (𝔅.map i) y := fun i ↦
    congrFun (congrArg Subtype.val hxy) i
  obtain ⟨𝔄₁, a, rfl⟩ := addPlusConstruction.exists_mk x
  obtain ⟨𝔄₂, b, rfl⟩ := addPlusConstruction.exists_mk y
  obtain ⟨𝔄₁₂, φ₁, φ₂, -⟩ := cocone_objs 𝔄₁ 𝔄₂
  obtain ⟨𝔄, ψ, χ, -⟩ := cocone_objs 𝔄₁₂ 𝔅
  rw [← addPlusConstruction.mk_sectionsAddMonoidHom (φ₁ ≫ ψ) a,
    ← addPlusConstruction.mk_sectionsAddMonoidHom (φ₂ ≫ ψ) b] at h ⊢
  refine P.mk_eq_mk_of_map_eq 𝔄 _ _ fun k ↦ ?_
  rw [← Hom.comm χ k, P.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h]

end AddPlusPresheaf

end EtaleCategory

end AlgebraicGeometry
