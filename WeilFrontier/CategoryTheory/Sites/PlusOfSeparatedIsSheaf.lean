module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.CoveringMorphism
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleCoveringFk101
public import WeilFrontier.AlgebraicGeometry.Sites.SheafIffCoveringConditionFk101
public import WeilFrontier.CategoryTheory.Sites.PlusUnitEqualIff
public import WeilFrontier.Defs.CategoryTheory.Sites.PlusPresheaf

/-!
# The plus presheaf of a separated presheaf is a sheaf

Let `A` be a commutative ring and `F` a presheaf of sets on the étale category `Et(A)` such that
for every object `B` and every covering `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` of `B` the restriction map
`ρ_𝔅 : F(B) → F(𝔅)` is injective. Then the plus presheaf `F̃` is a sheaf.

By the sheaf criterion via coverings it suffices to show that every `ρ_𝔅 : F̃(B) → F̃(𝔅)` is
bijective. Injectivity holds for every presheaf `F`: two classes can be represented on a common
covering refining `𝔅`, and their members agree after restriction to a covering of each member.
For surjectivity, a compatible family `(xᵢ)ᵢ`, `xᵢ = [𝔄ᵢ, aᵢ]`, glues to the class of the family
`(a_{ik})_{(i, k)}` on the composite covering `(c_{ik} ∘ gᵢ)_{(i, k)}`; the family is compatible
because `F` is separated.

## Main results

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.isSheaf_toPresheaf_of_injective`,
  `AlgebraicGeometry.EtaleCategory.PlusPresheaf.isSheafAxioms_toPresheaf_of_injective`: if the
  restriction maps of `F` to its sections over coverings are injective, the plus presheaf of `F`
  is a sheaf.

## Implementation notes

The coverings in the hypothesis and in the plus construction are indexed in the same universe
`w`; the coverings of `Et(A)` are finite families, so this is no restriction.

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

variable {B B' : EtaleCategory A}

/-- The composite covering `(gᵢ ≫ c_{ik})_{(i, k)}` of `B`, for a covering `𝔅 = (gᵢ)ᵢ` of `B`
and coverings `𝔄ᵢ = (c_{ik})ₖ` of its members. -/
private def bind (𝔅 : Covering.{w} B) (𝔄 : ∀ i, Covering.{w} (𝔅.obj i)) : Covering.{w} B where
  ι := Σ i, (𝔄 i).ι
  obj ik := (𝔄 ik.1).obj ik.2
  map ik := 𝔅.map ik.1 ≫ (𝔄 ik.1).map ik.2
  isCovering := 𝔅.isCovering.comp fun i ↦ (𝔄 i).isCovering

/-- The morphism of coverings `𝔅.bind 𝔄 ⟶ 𝔄ᵢ` over `gᵢ`, given by `k ↦ (i, k)` and identities. -/
private def bindHomOver (𝔅 : Covering.{w} B) (𝔄 : ∀ i, Covering.{w} (𝔅.obj i)) (i : 𝔅.ι) :
    HomOver (𝔅.map i) (𝔅.bind 𝔄) (𝔄 i) where
  σ k := ⟨i, k⟩
  h _ := 𝟙 _
  comm _ := Category.comp_id _

/-- The morphism of coverings `𝔅 ⟶ 𝔅.bind 𝔄` of `B`, given by `(i, k) ↦ i` and the maps
`c_{ik}`. -/
private def toBind (𝔅 : Covering.{w} B) (𝔄 : ∀ i, Covering.{w} (𝔅.obj i)) : 𝔅 ⟶ 𝔅.bind 𝔄 :=
  HomOver.toHom
    { σ := Sigma.fst
      h ik := (𝔄 ik.1).map ik.2
      comm _ := (Category.id_comp _).symm }

/-- The morphism of coverings `𝔅 ⟶ (id_{Bᵢ})` over a member `gᵢ` of `𝔅`. -/
private def toSelfOfMember (𝔅 : Covering.{w} B) (i : 𝔅.ι) :
    HomOver (𝔅.map i) 𝔅 (self.{w} (𝔅.obj i)) where
  σ _ := i
  h _ := 𝟙 _
  comm _ := rfl

/-- The morphism of coverings `(id_B) ⟶ (id_{B'})` over a morphism `f : B ⟶ B'`. -/
private def selfHomOver (f : B ⟶ B') : HomOver f (self.{w} B) (self.{w} B') where
  σ _ := PUnit.unit
  h _ := f
  comm _ := (Category.id_comp f).trans (Category.comp_id f).symm

end Covering

open EtaleCategory.Covering

namespace plusConstruction

variable {F : EtaleCategory A ⥤ Type v}

/-- Two classes `[𝔈, s]`, `[𝔈, t]` on the same covering `𝔈` agree if `ι(sⱼ) = ι(tⱼ)` for every
member `Eⱼ` of `𝔈`. -/
private lemma mk_eq_mk_of_toPlusConstruction_eq {B : EtaleCategory A} (𝔈 : Covering.{w} B)
    (s t : coveringSections F 𝔈.map)
    (h : ∀ j, toPlusConstruction.{w} F (𝔈.obj j) (s.1 j) =
      toPlusConstruction.{w} F (𝔈.obj j) (t.1 j)) :
    mk 𝔈 s = mk 𝔈 t := by
  choose 𝔉 h𝔉 using fun j ↦ (toPlusConstruction_eq_iff_exists F (s.1 j) (t.1 j)).1 (h j)
  rw [← mk_sectionsMap (toBind 𝔈 𝔉) s, ← mk_sectionsMap (toBind 𝔈 𝔉) t]
  congr 1
  exact Subtype.ext (funext fun ik ↦ h𝔉 ik.1 ik.2)

end plusConstruction

namespace PlusPresheaf

variable {F : Presheaf A (Type v)} (P : PlusPresheaf.{w} F)

/-- The restriction of a class `[𝔅, s]` to a member `Bᵢ` of `𝔅` is `ι(sᵢ)`. -/
private lemma map_map_mk {B : EtaleCategory A} (𝔅 : Covering.{w} B) (s : coveringSections F 𝔅.map)
    (i : 𝔅.ι) :
    P.map (𝔅.map i) (plusConstruction.mk 𝔅 s) = toPlusConstruction.{w} F (𝔅.obj i) (s.1 i) := by
  rw [P.map_mk _ 𝔅 _ (toSelfOfMember 𝔅 i), toPlusConstruction_apply]
  congr 1
  exact Subtype.ext (funext fun _ ↦ Presheaf.map_id_apply F _ _)

/-- The maps `ι : F(B) → F̃(B)` commute with restriction. -/
private lemma map_toPlusConstruction {B B' : EtaleCategory A} (f : B ⟶ B') (s : F.obj B) :
    P.map f (toPlusConstruction.{w} F B s) = toPlusConstruction.{w} F B' (F.map f s) := by
  rw [toPlusConstruction_apply, P.map_mk f _ _ (selfHomOver f), toPlusConstruction_apply]
  rfl

/-- The restriction maps `ρ_𝔅 : F̃(B) → F̃(𝔅)` of a plus presheaf to its sections over a
covering are injective. -/
private theorem injective_coveringRestriction {B : EtaleCategory A} {ι : Type w}
    {C : ι → EtaleCategory A} {g : ∀ i, B ⟶ C i} (hg : IsCovering g) :
    Function.Injective (coveringRestriction P.toPresheaf g) := by
  intro x y hxy
  have hxy' : ∀ i, P.map (g i) x = P.map (g i) y := fun i ↦
    congrFun (congrArg Subtype.val hxy) i
  let 𝔊 : Covering.{w} B := ⟨ι, C, g, hg⟩
  obtain ⟨𝔄, a, rfl⟩ := plusConstruction.exists_mk x
  obtain ⟨𝔄', b, rfl⟩ := plusConstruction.exists_mk y
  let 𝔈 := (𝔄.inf 𝔄').inf 𝔊
  let φ : 𝔄 ⟶ 𝔈 := toInfLeft 𝔄 𝔄' ≫ toInfLeft _ 𝔊
  let φ' : 𝔄' ⟶ 𝔈 := toInfRight 𝔄 𝔄' ≫ toInfLeft _ 𝔊
  let ψ : 𝔊 ⟶ 𝔈 := toInfRight _ 𝔊
  rw [← plusConstruction.mk_sectionsMap φ a, ← plusConstruction.mk_sectionsMap φ' b] at hxy' ⊢
  refine plusConstruction.mk_eq_mk_of_toPlusConstruction_eq 𝔈 _ _ fun j ↦ ?_
  rw [← P.map_map_mk, ← P.map_map_mk, ← Hom.comm ψ j, P.map_comp, P.map_comp]
  exact congrArg (P.map _) (hxy' _)

/-- If the restriction maps `ρ_𝔅 : F(B) → F(𝔅)` of `F` are injective, the restriction maps
`ρ_𝔅 : F̃(B) → F̃(𝔅)` of a plus presheaf of `F` to its sections over a covering are
surjective. -/
private theorem surjective_coveringRestriction
    (hF : ∀ (B : EtaleCategory A) (ι : Type w) (C : ι → EtaleCategory A) (g : ∀ i, B ⟶ C i),
      IsCovering g → Function.Injective (coveringRestriction F g))
    {B : EtaleCategory A} {ι : Type w} {C : ι → EtaleCategory A} {g : ∀ i, B ⟶ C i}
    (hg : IsCovering g) :
    Function.Surjective (coveringRestriction P.toPresheaf g) := by
  rintro ⟨x, hx⟩
  let 𝔊 : Covering.{w} B := ⟨ι, C, g, hg⟩
  choose 𝔄 a ha using fun i ↦ plusConstruction.exists_mk (x i)
  have key : ∀ (i j : ι) (k : (𝔄 i).ι) (l : (𝔄 j).ι) (D : EtaleCategory A)
      (u : (𝔄 i).obj k ⟶ D) (v : (𝔄 j).obj l ⟶ D),
      (g i ≫ (𝔄 i).map k) ≫ u = (g j ≫ (𝔄 j).map l) ≫ v →
        F.map u ((a i).1 k) = F.map v ((a j).1 l) := by
    intro i j k l D u v huv
    obtain ⟨𝔈, h𝔈⟩ := (toPlusConstruction_eq_iff_exists F (F.map u ((a i).1 k))
      (F.map v ((a j).1 l))).1 (by
        rw [← P.map_toPlusConstruction, ← P.map_toPlusConstruction, ← P.map_map_mk,
          ← P.map_map_mk, ← P.map_comp, ← P.map_comp, ha, ha]
        have := (mem_coveringSections_iff _ g x).1 hx i j D ((𝔄 i).map k ≫ u)
          ((𝔄 j).map l ≫ v) (by simpa only [Category.assoc] using huv)
        exact this)
    exact hF _ _ _ _ 𝔈.isCovering (Subtype.ext (funext h𝔈))
  have hc : (fun ik : (𝔊.bind 𝔄).ι ↦ (a ik.1).1 ik.2) ∈ coveringSections F (𝔊.bind 𝔄).map := by
    refine (mem_coveringSections_iff F (𝔊.bind 𝔄).map _).2 ?_
    rintro ⟨i, k⟩ ⟨j, l⟩ D u v huv
    exact key i j k l D u v huv
  refine ⟨plusConstruction.mk (𝔊.bind 𝔄) ⟨_, hc⟩, Subtype.ext (funext fun i ↦ ?_)⟩
  change P.map (g i) _ = x i
  rw [P.map_mk _ (𝔊.bind 𝔄) (𝔄 i) (bindHomOver 𝔊 𝔄 i), ← ha i]
  congr 1
  exact Subtype.ext (funext fun _ ↦ Presheaf.map_id_apply F _ _)

/-- **The plus presheaf of a separated presheaf is a sheaf** [FK, I.1]. If for every object `B`
of `Et(A)` and every covering `𝔅` of `B` the restriction map `ρ_𝔅 : F(B) → F(𝔅)` is injective,
then the plus presheaf `F̃` of `F` is a sheaf for the étale topology. -/
@[weil "lem_fk101_plus_of_separated_is_sheaf"]
theorem isSheaf_toPresheaf_of_injective
    (hF : ∀ (B : EtaleCategory A) (ι : Type w) (C : ι → EtaleCategory A) (g : ∀ i, B ⟶ C i),
      IsCovering g → Function.Injective (coveringRestriction F g)) :
    Presheaf.IsSheaf (Scheme.AffineEtale.topology (Spec A)) P.toPresheaf :=
  (isSheaf_iff_forall_bijective_coveringRestriction.{u, max (u + 1) (w + 1) v, w}
    P.toPresheaf).2 fun _ _ _ _ hg ↦
      ⟨P.injective_coveringRestriction hg, P.surjective_coveringRestriction hF hg⟩

/-- **The plus presheaf of a separated presheaf is a sheaf** [FK, I.1], in the form of the sheaf
axioms: if every restriction map `ρ_𝔅 : F(B) → F(𝔅)` to the sections over a covering is
injective, the plus presheaf `F̃` of `F` satisfies the sheaf axioms. -/
@[weil "lem_fk101_plus_of_separated_is_sheaf"]
theorem isSheafAxioms_toPresheaf_of_injective
    (hF : ∀ (B : EtaleCategory A) (ι : Type w) (C : ι → EtaleCategory A) (g : ∀ i, B ⟶ C i),
      IsCovering g → Function.Injective (coveringRestriction F g)) :
    IsSheafAxioms P.toPresheaf :=
  (isSheaf_iff_isSheafAxioms _).1 (P.isSheaf_toPresheaf_of_injective hF)

end PlusPresheaf

end EtaleCategory

end AlgebraicGeometry
