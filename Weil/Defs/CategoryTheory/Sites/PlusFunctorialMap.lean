module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.Plus

/-!
# The map induced on the plus construction by a morphism of presheaves

Let `A` be a commutative ring, `α : F₁ ⟶ F₂` a morphism of presheaves on the étale category
`Et(A)` and `B` an object of `Et(A)`. For a family `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` the map
`α_𝔅 : F₁(𝔅) → F₂(𝔅)`, `(sᵢ)ᵢ ↦ (α_{Bᵢ}(sᵢ))ᵢ`, sends compatible families to compatible
families, because `α` is natural: `F₂(u)(α_{Bᵢ}(sᵢ)) = α_D(F₁(u)(sᵢ))`. By naturality again,
`α_{𝔅'} ∘ (σ, h)_* = (σ, h)_* ∘ α_𝔅` for every morphism of coverings `(σ, h) : 𝔅 ⟶ 𝔅'`, so the
maps `α_𝔅` form a natural transformation of the functors `𝔅 ↦ F₁(𝔅)` and `𝔅 ↦ F₂(𝔅)` on the
category `Cov(B)` of coverings of `B`. The map `α̃_B : F̃₁(B) → F̃₂(B)` is the map it induces on
colimits, `[𝔅, s] ↦ [𝔅, α_𝔅(s)]`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.coveringSectionsMap α g`: the map `α_𝔅 : F₁(𝔅) → F₂(𝔅)`, for
  presheaves of sets.
- `AlgebraicGeometry.EtaleCategory.coveringSectionsAddMonoidHom α g`: the same map, as a
  homomorphism of the subgroups `F₁(𝔅) → F₂(𝔅)`, for presheaves of abelian groups.
- `AlgebraicGeometry.EtaleCategory.Covering.sectionsFunctorMap α B`,
  `AlgebraicGeometry.EtaleCategory.Covering.sectionsAddFunctorMap α B`: the natural
  transformations `𝔅 ↦ α_𝔅` on `Cov(B)`.
- `AlgebraicGeometry.EtaleCategory.plusConstruction.map α`: the map `α̃_B : F̃₁(B) → F̃₂(B)`, for
  presheaves of sets.
- `AlgebraicGeometry.EtaleCategory.addPlusConstruction.map α`: the homomorphism
  `α̃_B : F̃₁(B) ⟶ F̃₂(B)`, for presheaves of abelian groups.

## Main results

- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.sectionsMap_coveringSectionsMap`:
  `(σ, h)_* ∘ α_𝔅 = α_{𝔅'} ∘ (σ, h)_*`.
- `AlgebraicGeometry.EtaleCategory.plusConstruction.map_mk`,
  `AlgebraicGeometry.EtaleCategory.addPlusConstruction.map_mk`: `α̃_B [𝔅, s] = [𝔅, α_𝔅(s)]`.
- `map_id`, `map_comp`: the construction `α ↦ α̃_B` is functorial.

## Implementation notes

The plus construction here is the colimit over the category of coverings (families) of `B`, as
in the source, not Mathlib's colimit `GrothendieckTopology.plusObj` over covering sieves; so
`α̃_B` is the map induced on these colimits rather than Mathlib's `GrothendieckTopology.plusMap`.
The two agree under the comparison of the two colimits along the cofinal functor from coverings
to covering sieves.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}} {B : EtaleCategory A} {ι : Type w} {C : ι → EtaleCategory A}

section Types

variable {F₁ F₂ F₃ : EtaleCategory A ⥤ Type v}

/-- The map `α_𝔅 : F₁(𝔅) → F₂(𝔅)`, `(sᵢ)ᵢ ↦ (α_{Bᵢ}(sᵢ))ᵢ`, induced on the sections over a
family `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` by a morphism of presheaves of sets `α : F₁ ⟶ F₂`. -/
@[weil "def_fk101_plus_functorial_map"]
def coveringSectionsMap (α : F₁ ⟶ F₂) (g : ∀ i, B ⟶ C i) :
    coveringSections F₁ g → coveringSections F₂ g :=
  fun s ↦ ⟨fun i ↦ α.app (C i) (s.1 i), by
    rw [mem_coveringSections_iff]
    intro i j D u v huv
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
      map_eq_map_of_mem_coveringSections F₁ g s.2 u v huv]⟩

@[simp]
lemma coveringSectionsMap_apply (α : F₁ ⟶ F₂) (g : ∀ i, B ⟶ C i) (s : coveringSections F₁ g)
    (i : ι) : (coveringSectionsMap α g s).1 i = α.app (C i) (s.1 i) :=
  rfl

@[simp]
lemma coveringSectionsMap_id (g : ∀ i, B ⟶ C i) (s : coveringSections F₁ g) :
    coveringSectionsMap (𝟙 F₁) g s = s :=
  rfl

lemma coveringSectionsMap_comp (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) (g : ∀ i, B ⟶ C i)
    (s : coveringSections F₁ g) :
    coveringSectionsMap (α ≫ β) g s = coveringSectionsMap β g (coveringSectionsMap α g s) :=
  rfl

/-- `(σ, h)_* ∘ α_𝔅 = α_{𝔅'} ∘ (σ, h)_*` for a morphism of coverings `(σ, h) : 𝔅 ⟶ 𝔅'` over
`f : B ⟶ B'` and a morphism of presheaves `α`. -/
lemma Covering.HomOver.sectionsMap_coveringSectionsMap {B B' : EtaleCategory A} {f : B ⟶ B'}
    {𝔅 : Covering.{w} B} {𝔅' : Covering.{w} B'} (φ : Covering.HomOver f 𝔅 𝔅') (α : F₁ ⟶ F₂)
    (s : coveringSections F₁ 𝔅.map) :
    φ.sectionsMap F₂ (coveringSectionsMap α 𝔅.map s) =
      coveringSectionsMap α 𝔅'.map (φ.sectionsMap F₁ s) :=
  Subtype.ext <| funext fun _ ↦ (NatTrans.naturality_apply α _ _).symm

/-- The natural transformation `𝔅 ↦ α_𝔅` from `𝔅 ↦ F₁(𝔅)` to `𝔅 ↦ F₂(𝔅)` on the category
`Cov(B)` of coverings of `B`. -/
@[simps]
def Covering.sectionsFunctorMap (α : F₁ ⟶ F₂) (B : EtaleCategory A) :
    Covering.sectionsFunctor.{w} F₁ B ⟶ Covering.sectionsFunctor.{w} F₂ B where
  app 𝔅 := TypeCat.ofHom (coveringSectionsMap α 𝔅.map)
  naturality _ _ φ := by
    ext s
    exact (Covering.HomOver.sectionsMap_coveringSectionsMap φ α s).symm

namespace plusConstruction

/-- The map `α̃_B : F̃₁(B) → F̃₂(B)`, `[𝔅, s] ↦ [𝔅, α_𝔅(s)]`, induced on the plus
constructions by a morphism of presheaves of sets `α : F₁ ⟶ F₂`: the map induced on colimits
by the natural transformation `𝔅 ↦ α_𝔅`. -/
@[weil "def_fk101_plus_functorial_map"]
def map (α : F₁ ⟶ F₂) : plusConstruction.{w} F₁ B → plusConstruction.{w} F₂ B :=
  (Covering.sectionsFunctor.{w} F₁ B).descColimitType
    ((Covering.sectionsFunctor.{w} F₂ B).coconeTypes.precompose
      (fun 𝔅 ↦ coveringSectionsMap α 𝔅.map)
      (fun φ ↦ funext fun s ↦ (Covering.HomOver.sectionsMap_coveringSectionsMap φ α s).symm))

/-- `α̃_B [𝔅, s] = [𝔅, α_𝔅(s)]`. -/
@[simp]
lemma map_mk (α : F₁ ⟶ F₂) (𝔅 : Covering.{w} B) (s : coveringSections F₁ 𝔅.map) :
    map α (mk 𝔅 s) = mk 𝔅 (coveringSectionsMap α 𝔅.map s) :=
  rfl

@[simp]
lemma map_id : map (B := B) (𝟙 F₁) = id :=
  hom_ext fun _ _ ↦ rfl

lemma map_comp (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) :
    map (B := B) (α ≫ β) = map β ∘ map α :=
  hom_ext fun _ _ ↦ rfl

end plusConstruction

end Types

section AddCommGrp

variable {F₁ F₂ F₃ : EtaleCategory A ⥤ AddCommGrpCat.{v}}

/-- The homomorphism `α_𝔅 : F₁(𝔅) → F₂(𝔅)`, `(sᵢ)ᵢ ↦ (α_{Bᵢ}(sᵢ))ᵢ`, induced on the sections
over a family `𝔅 = (gᵢ : B ⟶ Bᵢ)ᵢ` by a morphism of presheaves of abelian groups
`α : F₁ ⟶ F₂`. -/
@[weil "def_fk101_plus_functorial_map"]
def coveringSectionsAddMonoidHom (α : F₁ ⟶ F₂) (g : ∀ i, B ⟶ C i) :
    coveringSectionsAddSubgroup F₁ g →+ coveringSectionsAddSubgroup F₂ g where
  toFun s := ⟨fun i ↦ α.app (C i) (s.1 i),
    (coveringSectionsMap (Functor.whiskerRight α (forget AddCommGrpCat)) g ⟨s.1, s.2⟩).2⟩
  map_zero' := Subtype.ext <| funext fun i ↦ map_zero (α.app (C i)).hom
  map_add' _ _ := Subtype.ext <| funext fun i ↦ map_add (α.app (C i)).hom _ _

@[simp]
lemma coveringSectionsAddMonoidHom_apply (α : F₁ ⟶ F₂) (g : ∀ i, B ⟶ C i)
    (s : coveringSectionsAddSubgroup F₁ g) (i : ι) :
    (coveringSectionsAddMonoidHom α g s).1 i = α.app (C i) (s.1 i) :=
  rfl

/-- `(σ, h)_* ∘ α_𝔅 = α_{𝔅'} ∘ (σ, h)_*` for a morphism of coverings `(σ, h) : 𝔅 ⟶ 𝔅'` over
`f : B ⟶ B'` and a morphism of presheaves of abelian groups `α`. -/
lemma Covering.HomOver.sectionsAddMonoidHom_comp_coveringSectionsAddMonoidHom
    {B B' : EtaleCategory A} {f : B ⟶ B'} {𝔅 : Covering.{w} B} {𝔅' : Covering.{w} B'}
    (φ : Covering.HomOver f 𝔅 𝔅') (α : F₁ ⟶ F₂) :
    (φ.sectionsAddMonoidHom F₂).comp (coveringSectionsAddMonoidHom α 𝔅.map) =
      (coveringSectionsAddMonoidHom α 𝔅'.map).comp (φ.sectionsAddMonoidHom F₁) := by
  ext s j
  exact (NatTrans.naturality_apply α (φ.h j) (s.1 (φ.σ j))).symm

/-- The natural transformation `𝔅 ↦ α_𝔅` from `𝔅 ↦ F₁(𝔅)` to `𝔅 ↦ F₂(𝔅)` on the category
`Cov(B)` of coverings of `B`, for presheaves of abelian groups. -/
@[simps]
def Covering.sectionsAddFunctorMap (α : F₁ ⟶ F₂) (B : EtaleCategory A) :
    Covering.sectionsAddFunctor.{w} F₁ B ⟶ Covering.sectionsAddFunctor.{w} F₂ B where
  app 𝔅 := AddCommGrpCat.ofHom (coveringSectionsAddMonoidHom α 𝔅.map)
  naturality _ _ φ := by
    ext1
    exact (Covering.HomOver.sectionsAddMonoidHom_comp_coveringSectionsAddMonoidHom φ α).symm

namespace addPlusConstruction

/-- The homomorphisms `s ↦ [𝔅, α_𝔅(s)]` are compatible with the maps `(σ, h)_*`. -/
lemma mk_comp_coveringSectionsAddMonoidHom_comp (α : F₁ ⟶ F₂) {𝔅 𝔅' : Covering.{w} B}
    (φ : 𝔅 ⟶ 𝔅') :
    ((mk 𝔅').comp (coveringSectionsAddMonoidHom α 𝔅'.map)).comp
        (Covering.HomOver.sectionsAddMonoidHom F₁ φ) =
      (mk 𝔅).comp (coveringSectionsAddMonoidHom α 𝔅.map) := by
  ext s
  have h : φ.sectionsAddMonoidHom F₂ (coveringSectionsAddMonoidHom α 𝔅.map s) =
      coveringSectionsAddMonoidHom α 𝔅'.map (φ.sectionsAddMonoidHom F₁ s) :=
    DFunLike.congr_fun
      (Covering.HomOver.sectionsAddMonoidHom_comp_coveringSectionsAddMonoidHom φ α) s
  change mk 𝔅' (coveringSectionsAddMonoidHom α 𝔅'.map (φ.sectionsAddMonoidHom F₁ s)) =
    mk 𝔅 (coveringSectionsAddMonoidHom α 𝔅.map s)
  rw [← h, mk_sectionsAddMonoidHom]

/-- The homomorphism `α̃_B : F̃₁(B) ⟶ F̃₂(B)`, `[𝔅, s] ↦ [𝔅, α_𝔅(s)]`, induced on the plus
constructions by a morphism of presheaves of abelian groups `α : F₁ ⟶ F₂`: the map induced on
colimits by the natural transformation `𝔅 ↦ α_𝔅`. -/
@[weil "def_fk101_plus_functorial_map"]
def map (α : F₁ ⟶ F₂) : addPlusConstruction.{w} F₁ B ⟶ addPlusConstruction.{w} F₂ B :=
  AddCommGrpCat.ofHom <| lift (fun 𝔅 ↦ (mk 𝔅).comp (coveringSectionsAddMonoidHom α 𝔅.map))
    (mk_comp_coveringSectionsAddMonoidHom_comp α)

/-- `α̃_B [𝔅, s] = [𝔅, α_𝔅(s)]`. -/
@[simp]
lemma map_mk (α : F₁ ⟶ F₂) (𝔅 : Covering.{w} B) (s : coveringSectionsAddSubgroup F₁ 𝔅.map) :
    map α (mk 𝔅 s) = mk 𝔅 (coveringSectionsAddMonoidHom α 𝔅.map s) :=
  lift_mk _ (mk_comp_coveringSectionsAddMonoidHom_comp α) 𝔅 s

@[simp]
lemma map_id : map (B := B) (𝟙 F₁) = 𝟙 _ := by
  ext1
  refine hom_ext fun 𝔅 s ↦ ?_
  rw [map_mk]
  rfl

lemma map_comp (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) :
    map (B := B) (α ≫ β) = map α ≫ map β := by
  ext1
  refine hom_ext fun 𝔅 s ↦ ?_
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, map_mk]
  rfl

end addPlusConstruction

end AddCommGrp

end EtaleCategory

end AlgebraicGeometry
