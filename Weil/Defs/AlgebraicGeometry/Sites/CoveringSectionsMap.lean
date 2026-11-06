module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.CoveringMorphism
public import Weil.Defs.CategoryTheory.Sites.IsSheafFor

/-!
# The map on sections induced by a morphism of coverings

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)`, and
`(σ, h) : 𝔅 ⟶ 𝔅'` a morphism over `f : B ⟶ B'` of coverings `𝔅 = (gᵢ : B ⟶ Bᵢ)_{i ∈ I}` and
`𝔅' = (g'ⱼ : B' ⟶ B'ⱼ)_{j ∈ J}`. The induced map `(σ, h)_* : F(𝔅) → F(𝔅')` sends a compatible
family `(sᵢ)ᵢ` to `(F(hⱼ)(s_{σ j}))ⱼ`. The image is again compatible: if `u : B'ⱼ ⟶ D` and
`v : B'ⱼ' ⟶ D` satisfy `u g'ⱼ = v g'ⱼ'`, then `(u hⱼ) g_{σ j} = u g'ⱼ f = v g'ⱼ' f =
(v hⱼ') g_{σ j'}`. By functoriality of `F` the construction is compatible with composition of
morphisms of coverings and sends identities to identities.

For morphisms of coverings of a fixed object `B` (over `𝟙 B`), the map `(σ, h)_*` is Mathlib's
refinement map `Meq.refine` of matching families along the inclusion of the generated covering
sieves.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.sectionsMap F φ`: the map
  `F(𝔅) → F(𝔅')` induced by a morphism `φ = (σ, h) : 𝔅 ⟶ 𝔅'` over `f`, for a presheaf of sets.
- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.sectionsAddMonoidHom F φ`: the same map, as
  a homomorphism of the subgroups `F(𝔅) → F(𝔅')`, for a presheaf of abelian groups.

## Main results

- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.sectionsMap_comp`:
  `((σ', h') ∘ (σ, h))_* = (σ', h')_* ∘ (σ, h)_*`.
- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.sectionsMap_id`: the identity morphism
  induces the identity.
- `AlgebraicGeometry.EtaleCategory.Covering.HomOver.coveringSectionsEquivMeq_sectionsMap`: for
  a morphism of coverings of `B`, the induced map is `Meq.refine` along the inclusion of sieves
  `HomOver.sieve_le`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

namespace Covering

namespace HomOver

variable {A : CommRingCat.{u}} {B B' B'' : EtaleCategory A} {f : B ⟶ B'} {f' : B' ⟶ B''}
  {𝔅 : Covering.{w} B} {𝔅' : Covering.{w} B'} {𝔅'' : Covering.{w} B''}

/-- The family `(F(hⱼ)(s_{σ j}))ⱼ` of a compatible family `s` over `𝔅` along a morphism
`(σ, h) : 𝔅 ⟶ 𝔅'` of coverings is compatible over `𝔅'`. -/
lemma map_mem_coveringSections (F : EtaleCategory A ⥤ Type v) (φ : HomOver f 𝔅 𝔅')
    {s : ∀ i, F.obj (𝔅.obj i)} (hs : s ∈ coveringSections F 𝔅.map) :
    (fun j ↦ F.map (φ.h j) (s (φ.σ j))) ∈ coveringSections F 𝔅'.map := by
  rw [mem_coveringSections_iff]
  intro j j' D u v huv
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  refine map_eq_map_of_mem_coveringSections F 𝔅.map hs _ _ ?_
  rw [φ.comm_assoc, φ.comm_assoc, huv]

/-- The map `(σ, h)_* : F(𝔅) → F(𝔅')`, `(sᵢ)ᵢ ↦ (F(hⱼ)(s_{σ j}))ⱼ`, induced on the sections of a
presheaf of sets `F` by a morphism `(σ, h) : 𝔅 ⟶ 𝔅'` of coverings over `f : B ⟶ B'`. -/
@[weil "def_fk101_covering_sections_map"]
def sectionsMap (F : EtaleCategory A ⥤ Type v) (φ : HomOver f 𝔅 𝔅') :
    coveringSections F 𝔅.map → coveringSections F 𝔅'.map :=
  fun s ↦ ⟨fun j ↦ F.map (φ.h j) (s.1 (φ.σ j)), φ.map_mem_coveringSections F s.2⟩

variable (F : EtaleCategory A ⥤ Type v)

@[simp]
lemma sectionsMap_apply (φ : HomOver f 𝔅 𝔅') (s : coveringSections F 𝔅.map) (j : 𝔅'.ι) :
    (φ.sectionsMap F s).1 j = F.map (φ.h j) (s.1 (φ.σ j)) :=
  rfl

/-- The identity morphism of a covering induces the identity on its sections. -/
@[simp]
lemma sectionsMap_id (𝔅 : Covering.{w} B) (s : coveringSections F 𝔅.map) :
    (HomOver.id 𝔅).sectionsMap F s = s :=
  Subtype.ext <| funext fun _ ↦ F.map_id_apply _ _

/-- The map induced by a composite of morphisms of coverings is the composite of the induced
maps: `((σ', h') ∘ (σ, h))_* = (σ', h')_* ∘ (σ, h)_*`. -/
@[weil "def_fk101_covering_sections_map"]
lemma sectionsMap_comp (φ : HomOver f 𝔅 𝔅') (ψ : HomOver f' 𝔅' 𝔅'')
    (s : coveringSections F 𝔅.map) :
    (φ.comp ψ).sectionsMap F s = ψ.sectionsMap F (φ.sectionsMap F s) :=
  Subtype.ext <| funext fun _ ↦ F.map_comp_apply _ _ _

/-- Transporting a morphism of coverings along an equality of the underlying morphisms does not
change the induced map. -/
@[simp]
lemma sectionsMap_congrBase {f₁ f₂ : B ⟶ B'} (e : f₁ = f₂) (φ : HomOver f₁ 𝔅 𝔅') :
    (φ.congrBase e).sectionsMap F = φ.sectionsMap F :=
  rfl

end HomOver

variable {A : CommRingCat.{u}} {B : EtaleCategory A} {𝔅 𝔅' 𝔅'' : Covering.{w} B}
  (F : EtaleCategory A ⥤ Type v)

/-- In the category `Cov(B)` of coverings of `B`, the identity induces the identity on
sections. -/
@[simp]
lemma sectionsMap_id' (s : coveringSections F 𝔅.map) :
    HomOver.sectionsMap F (𝟙 𝔅 : 𝔅 ⟶ 𝔅) s = s :=
  HomOver.sectionsMap_id F 𝔅 s

/-- In the category `Cov(B)` of coverings of `B`, the map induced by a composite is the
composite of the induced maps. -/
lemma sectionsMap_comp' (φ : 𝔅 ⟶ 𝔅') (ψ : 𝔅' ⟶ 𝔅'') (s : coveringSections F 𝔅.map) :
    HomOver.sectionsMap F (φ ≫ ψ) s =
      HomOver.sectionsMap F ψ (HomOver.sectionsMap F φ s) :=
  HomOver.sectionsMap_comp F φ ψ s

/-- For a morphism `φ : 𝔅 ⟶ 𝔅'` of coverings of `B`, the induced map on sections is, under the
identification `coveringSectionsEquivMeq` of sections with matching families on the generated
covering sieves, Mathlib's refinement map `Meq.refine` along the inclusion of sieves
`HomOver.sieve_le φ`. -/
lemma HomOver.coveringSectionsEquivMeq_sectionsMap (φ : 𝔅 ⟶ 𝔅')
    (s : coveringSections F 𝔅.map) :
    coveringSectionsEquivMeq F 𝔅'.isCovering (HomOver.sectionsMap F φ s) =
      (coveringSectionsEquivMeq F 𝔅.isCovering s).refine
        (homOfLE (HomOver.sieve_le φ) : toCoverObj 𝔅' ⟶ toCoverObj 𝔅) := by
  have key : ∀ {𝔆 : Covering.{w} B} (m : Meq F (toCoverObj 𝔆)) (i : 𝔆.ι) {Y}
      (c : Y ⟶ (𝔆.obj i).unop) (hc),
      m ⟨Y, c ≫ (𝔆.map i).unop, hc⟩ =
        F.map c.op (m ⟨_, (𝔆.map i).unop, Sieve.ofArrows_mk _ _ i⟩) := by
    intro 𝔆 m i Y c hc
    have := m.condition (GrothendieckTopology.Cover.Relation.mk'
      (GrothendieckTopology.Cover.Arrow.precompRelation
        ⟨_, (𝔆.map i).unop, Sieve.ofArrows_mk _ _ i⟩ c))
    exact (F.map_id_apply (op Y) _).symm.trans this
  refine Meq.ext _ _ fun ⟨Y, a, ha⟩ ↦ ?_
  obtain ⟨j, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ha
  have e : b ≫ (𝔅'.map j).unop =
      (b ≫ (HomOver.h φ j).unop) ≫ (𝔅.map (HomOver.σ φ j)).unop := by
    rw [Category.assoc, ← unop_comp, Hom.comm φ j]
  refine (key (coveringSectionsEquivMeq F 𝔅'.isCovering (HomOver.sectionsMap F φ s)) j b
    ha).trans ((?_ : _ = _).trans
      ((Meq.congr_apply (coveringSectionsEquivMeq F 𝔅.isCovering s) e _).trans
        (key _ _ _ _)).symm)
  have h₁ := coveringSectionsEquivMeq_apply F 𝔅'.isCovering (HomOver.sectionsMap F φ s) j
  have h₂ := coveringSectionsEquivMeq_apply F 𝔅.isCovering s (HomOver.σ φ j)
  rw [sectionsMap_apply] at h₁
  rw [op_comp, Quiver.Hom.op_unop, F.map_comp_apply]
  exact congrArg (F.map b.op) (h₁.trans (congrArg (F.map (HomOver.h φ j)) h₂.symm))

/-- The map `(σ, h)_* : F(𝔅) → F(𝔅')` induced on the sections of a presheaf of abelian groups
`F` by a morphism `(σ, h) : 𝔅 ⟶ 𝔅'` of coverings over `f`, as a homomorphism of the subgroups
`F(𝔅) ⊆ ∏ᵢ F(Bᵢ)` and `F(𝔅') ⊆ ∏ⱼ F(B'ⱼ)`. -/
@[weil "def_fk101_covering_sections_map"]
def HomOver.sectionsAddMonoidHom {B B' : EtaleCategory A} {f : B ⟶ B'} {𝔅 : Covering.{w} B}
    {𝔅' : Covering.{w} B'} (F : EtaleCategory A ⥤ AddCommGrpCat.{v}) (φ : HomOver f 𝔅 𝔅') :
    coveringSectionsAddSubgroup F 𝔅.map →+ coveringSectionsAddSubgroup F 𝔅'.map where
  toFun s := ⟨fun j ↦ F.map (φ.h j) (s.1 (φ.σ j)),
    φ.map_mem_coveringSections (F ⋙ forget AddCommGrpCat) s.2⟩
  map_zero' := Subtype.ext <| funext fun j ↦ map_zero (F.map (φ.h j)).hom
  map_add' _ _ := Subtype.ext <| funext fun j ↦ map_add (F.map (φ.h j)).hom _ _

end Covering

end EtaleCategory

end AlgebraicGeometry
