module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.CoveringMorphism
public import WeilFrontier.AlgebraicGeometry.Sites.CoveringSectionsMap
public import WeilFrontier.CategoryTheory.Sites.Plus
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.CoveringPullback
public import WeilFrontier.Defs.CategoryTheory.Sites.PlusPresheaf

/-!
# Existence and uniqueness of the plus presheaf

Let `A` be a commutative ring and `F` a presheaf on the étale category `Et(A)`. There is exactly
one plus presheaf of `F`: exactly one family of maps `P(f) : F̃(B) → F̃(B')`, functorial in
`f : B ⟶ B'`, with `P(f)([𝔅, s]) = [𝔅', φ_* s]` for every morphism of coverings `φ : 𝔅 ⟶ 𝔅'`
over `f`.

Uniqueness holds because every element of `F̃(B)` is a class `[𝔅, s]` and every covering `𝔅` of
`B` admits a morphism of coverings over `f` to some covering of `B'`. For existence, `P(f)` sends
`[𝔅, s]` to `[f_* 𝔅, ι_* s]`, where `ι : 𝔅 ⟶ f_* 𝔅` is the morphism over `f` to the pulled back
covering; the class `[𝔅', φ_* s]` does not depend on the morphism `φ` over `f` and the covering
`𝔅'` (`plusConstruction.mk_sectionsMap_eq_mk_sectionsMap`), which gives well-definedness, the
defining identity and functoriality.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.plusConstruction.restrict f`: the map `F̃(B) → F̃(B')`
  induced by `f : B ⟶ B'`, for a presheaf of sets.
- `AlgebraicGeometry.EtaleCategory.addPlusConstruction.restrict f`: the homomorphism
  `F̃(B) ⟶ F̃(B')` induced by `f`, for a presheaf of abelian groups.

## Main results

- `AlgebraicGeometry.EtaleCategory.PlusPresheaf.instUnique`: a presheaf of sets on `Et(A)` has
  exactly one plus presheaf.
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.instUnique`: a presheaf of abelian groups on
  `Et(A)` has exactly one plus presheaf.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}} {B B' B'' : EtaleCategory A}

open Covering

namespace plusConstruction

variable {F : EtaleCategory A ⥤ Type v}

/-- The class `[𝔅', φ_* s] ∈ F̃(B')` does not depend on the covering `𝔅'` of `B'` and the
morphism of coverings `φ : 𝔅 ⟶ 𝔅'` over `f`. -/
lemma mk_sectionsMap_eq_mk_sectionsMap {f : B ⟶ B'} {𝔅 : Covering.{w} B}
    {𝔅₁ 𝔅₂ : Covering.{w} B'} (φ₁ : HomOver f 𝔅 𝔅₁) (φ₂ : HomOver f 𝔅 𝔅₂)
    (s : coveringSections F 𝔅.map) :
    mk 𝔅₁ (φ₁.sectionsMap F s) = mk 𝔅₂ (φ₂.sectionsMap F s) := by
  obtain ⟨𝔅₃, χ₁, χ₂, -⟩ := cocone_objs 𝔅₁ 𝔅₂
  rw [← mk_sectionsMap χ₁, ← mk_sectionsMap χ₂]
  congr 1
  have h₁ := HomOver.sectionsMap_comp F φ₁ χ₁ s
  have h₂ := HomOver.sectionsMap_comp F φ₂ χ₂ s
  rw [← HomOver.sectionsMap_congrBase F (Category.comp_id f)] at h₁ h₂
  exact h₁.symm.trans ((congrFun (HomOver.sectionsMap_eq F _ _) s).trans h₂)

/-- The map `F̃(B) → F̃(B')`, `[𝔅, s] ↦ [f_* 𝔅, ι_* s]`, induced by a morphism `f : B ⟶ B'`, where
`ι : 𝔅 ⟶ f_* 𝔅` is the morphism of coverings over `f` to the pulled back covering. -/
def restrict (f : B ⟶ B') : plusConstruction.{w} F B → plusConstruction.{w} F B' :=
  (sectionsFunctor.{w} F B).descColimitType
    { pt := plusConstruction.{w} F B'
      ι 𝔅 s := mk (pullback f 𝔅) ((toPullback f 𝔅).sectionsMap F s)
      ι_naturality {𝔅 𝔅₁} φ := funext fun (s : coveringSections F 𝔅.map) ↦
        (congrArg (mk _) (HomOver.sectionsMap_comp F φ (toPullback f 𝔅₁) s).symm).trans
          (mk_sectionsMap_eq_mk_sectionsMap
            ((HomOver.comp φ (toPullback f 𝔅₁)).congrBase (Category.id_comp f))
            (toPullback f 𝔅) s) }

/-- `restrict f ([𝔅, s]) = [𝔅', φ_* s]` for every morphism of coverings `φ : 𝔅 ⟶ 𝔅'` over `f`. -/
lemma restrict_mk (f : B ⟶ B') (𝔅 : Covering.{w} B) (𝔅' : Covering.{w} B') (φ : HomOver f 𝔅 𝔅')
    (s : coveringSections F 𝔅.map) :
    restrict f (mk 𝔅 s) = mk 𝔅' (φ.sectionsMap F s) :=
  mk_sectionsMap_eq_mk_sectionsMap _ _ s

lemma restrict_id (t : plusConstruction.{w} F B) : restrict (𝟙 B) t = t := by
  obtain ⟨𝔅, s, rfl⟩ := exists_mk t
  rw [restrict_mk (𝟙 B) 𝔅 𝔅 (HomOver.id 𝔅), HomOver.sectionsMap_id]

lemma restrict_comp (f : B ⟶ B') (g : B' ⟶ B'') (t : plusConstruction.{w} F B) :
    restrict (f ≫ g) t = restrict g (restrict f t) := by
  obtain ⟨𝔅, s, rfl⟩ := exists_mk t
  rw [restrict_mk f 𝔅 _ (toPullback f 𝔅), restrict_mk g _ _ (toPullback g (pullback f 𝔅)),
    restrict_mk (f ≫ g) 𝔅 _ ((toPullback f 𝔅).comp (toPullback g (pullback f 𝔅))),
    HomOver.sectionsMap_comp]

end plusConstruction

namespace PlusPresheaf

variable (F : Presheaf A (Type v))

/-- **Existence and uniqueness of the plus presheaf** (presheaves of sets). A presheaf of sets on
`Et(A)` has exactly one plus presheaf. -/
@[weil "lem_fk101_plus_presheaf_exists_unique"]
instance instUnique : Unique (PlusPresheaf.{w} F) where
  default :=
    { map := plusConstruction.restrict
      map_id _ := plusConstruction.restrict_id
      map_comp := plusConstruction.restrict_comp
      map_mk := plusConstruction.restrict_mk }
  uniq P := by
    obtain ⟨map, map_id, map_comp, map_mk⟩ := P
    congr
    funext B B' f t
    obtain ⟨𝔅, s, rfl⟩ := plusConstruction.exists_mk t
    obtain ⟨𝔅', ⟨φ⟩⟩ := exists_homOver f 𝔅
    rw [map_mk f 𝔅 𝔅' φ s, plusConstruction.restrict_mk f 𝔅 𝔅' φ s]

end PlusPresheaf

namespace addPlusConstruction

variable {F : EtaleCategory A ⥤ AddCommGrpCat.{v}}

lemma sectionsAddMonoidHom_comp {f : B ⟶ B'} {f' : B' ⟶ B''} {𝔅 : Covering.{w} B}
    {𝔅' : Covering.{w} B'} {𝔅'' : Covering.{w} B''} (φ : HomOver f 𝔅 𝔅')
    (ψ : HomOver f' 𝔅' 𝔅'') (s : coveringSectionsAddSubgroup F 𝔅.map) :
    (φ.comp ψ).sectionsAddMonoidHom F s =
      ψ.sectionsAddMonoidHom F (φ.sectionsAddMonoidHom F s) :=
  Subtype.ext <| funext fun _ ↦ by
    dsimp only [HomOver.sectionsAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    change F.map (φ.h _ ≫ ψ.h _) _ = _
    rw [Functor.map_comp]
    rfl

lemma sectionsAddMonoidHom_id (𝔅 : Covering.{w} B) (s : coveringSectionsAddSubgroup F 𝔅.map) :
    (HomOver.id 𝔅).sectionsAddMonoidHom F s = s :=
  Subtype.ext <| funext fun _ ↦ by
    dsimp only [HomOver.sectionsAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    change F.map (𝟙 (𝔅.obj _)) (s.1 _) = s.1 _
    rw [CategoryTheory.Functor.map_id]
    rfl

lemma sectionsAddMonoidHom_congrBase {f₁ f₂ : B ⟶ B'} {𝔅 : Covering.{w} B}
    {𝔅' : Covering.{w} B'} (e : f₁ = f₂) (φ : HomOver f₁ 𝔅 𝔅') :
    (φ.congrBase e).sectionsAddMonoidHom F = φ.sectionsAddMonoidHom F :=
  rfl

/-- The class `[𝔅', φ_* s] ∈ F̃(B')` does not depend on the covering `𝔅'` of `B'` and the
morphism of coverings `φ : 𝔅 ⟶ 𝔅'` over `f`. -/
lemma mk_sectionsAddMonoidHom_eq_mk_sectionsAddMonoidHom {f : B ⟶ B'} {𝔅 : Covering.{w} B}
    {𝔅₁ 𝔅₂ : Covering.{w} B'} (φ₁ : HomOver f 𝔅 𝔅₁) (φ₂ : HomOver f 𝔅 𝔅₂)
    (s : coveringSectionsAddSubgroup F 𝔅.map) :
    mk 𝔅₁ (φ₁.sectionsAddMonoidHom F s) = mk 𝔅₂ (φ₂.sectionsAddMonoidHom F s) := by
  obtain ⟨𝔅₃, χ₁, χ₂, -⟩ := cocone_objs 𝔅₁ 𝔅₂
  rw [← mk_sectionsAddMonoidHom χ₁, ← mk_sectionsAddMonoidHom χ₂]
  congr 1
  have h₁ := sectionsAddMonoidHom_comp φ₁ χ₁ s
  have h₂ := sectionsAddMonoidHom_comp φ₂ χ₂ s
  rw [← sectionsAddMonoidHom_congrBase (Category.comp_id f)] at h₁ h₂
  exact h₁.symm.trans ((DFunLike.congr_fun (HomOver.sectionsAddMonoidHom_eq F _ _) s).trans h₂)

/-- The homomorphism `F̃(B) → F̃(B')`, `[𝔅, s] ↦ [f_* 𝔅, ι_* s]`, underlying `restrict f`. -/
def restrictAddMonoidHom (f : B ⟶ B') :
    addPlusConstruction.{w} F B →+ addPlusConstruction.{w} F B' :=
  lift (fun 𝔅 ↦ (mk (pullback f 𝔅)).comp ((toPullback f 𝔅).sectionsAddMonoidHom F))
    fun {𝔅 𝔅₁} φ ↦ by
      ext s
      change mk _ ((toPullback f 𝔅₁).sectionsAddMonoidHom F
        (HomOver.sectionsAddMonoidHom F φ s)) = mk _ ((toPullback f 𝔅).sectionsAddMonoidHom F s)
      exact (congrArg (mk _) (sectionsAddMonoidHom_comp φ (toPullback f 𝔅₁) s).symm).trans
        (mk_sectionsAddMonoidHom_eq_mk_sectionsAddMonoidHom
          ((HomOver.comp φ (toPullback f 𝔅₁)).congrBase (Category.id_comp f))
          (toPullback f 𝔅) s)

/-- The homomorphism `F̃(B) ⟶ F̃(B')`, `[𝔅, s] ↦ [f_* 𝔅, ι_* s]`, induced by a morphism
`f : B ⟶ B'`, where `ι : 𝔅 ⟶ f_* 𝔅` is the morphism of coverings over `f` to the pulled back
covering. -/
def restrict (f : B ⟶ B') : addPlusConstruction.{w} F B ⟶ addPlusConstruction.{w} F B' :=
  AddCommGrpCat.ofHom (restrictAddMonoidHom f)

/-- `restrict f ([𝔅, s]) = [𝔅', φ_* s]` for every morphism of coverings `φ : 𝔅 ⟶ 𝔅'` over `f`. -/
lemma restrict_mk (f : B ⟶ B') (𝔅 : Covering.{w} B) (𝔅' : Covering.{w} B') (φ : HomOver f 𝔅 𝔅')
    (s : coveringSectionsAddSubgroup F 𝔅.map) :
    restrict f (mk 𝔅 s) = mk 𝔅' (φ.sectionsAddMonoidHom F s) := by
  change restrictAddMonoidHom f (mk 𝔅 s) = _
  rw [restrictAddMonoidHom, lift_mk, AddMonoidHom.comp_apply]
  exact mk_sectionsAddMonoidHom_eq_mk_sectionsAddMonoidHom _ _ s

lemma restrict_id (B : EtaleCategory A) : restrict (F := F) (𝟙 B) = 𝟙 _ := by
  ext : 1
  refine hom_ext fun 𝔅 s ↦ ?_
  rw [restrict_mk (𝟙 B) 𝔅 𝔅 (HomOver.id 𝔅), sectionsAddMonoidHom_id]
  rfl

lemma restrict_comp (f : B ⟶ B') (g : B' ⟶ B'') :
    restrict (F := F) (f ≫ g) = restrict f ≫ restrict g := by
  ext : 1
  refine hom_ext fun 𝔅 s ↦ ?_
  rw [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, restrict_mk f 𝔅 _ (toPullback f 𝔅),
    restrict_mk g _ _ (toPullback g (pullback f 𝔅)),
    restrict_mk (f ≫ g) 𝔅 _ ((toPullback f 𝔅).comp (toPullback g (pullback f 𝔅))),
    sectionsAddMonoidHom_comp]

end addPlusConstruction

namespace AddPlusPresheaf

variable (F : Presheaf A AddCommGrpCat.{v})

/-- **Existence and uniqueness of the plus presheaf** (presheaves of abelian groups). A presheaf
of abelian groups on `Et(A)` has exactly one plus presheaf. -/
@[weil "lem_fk101_plus_presheaf_exists_unique"]
instance instUnique : Unique (AddPlusPresheaf.{w} F) where
  default :=
    { map := addPlusConstruction.restrict
      map_id := addPlusConstruction.restrict_id
      map_comp := addPlusConstruction.restrict_comp
      map_mk := addPlusConstruction.restrict_mk }
  uniq P := by
    obtain ⟨map, map_id, map_comp, map_mk⟩ := P
    congr
    funext B B' f
    ext : 1
    refine addPlusConstruction.hom_ext fun 𝔅 s ↦ ?_
    obtain ⟨𝔅', ⟨φ⟩⟩ := exists_homOver f 𝔅
    rw [map_mk f 𝔅 𝔅' φ s, addPlusConstruction.restrict_mk f 𝔅 𝔅' φ s]

end AddPlusPresheaf

end EtaleCategory

end AlgebraicGeometry
