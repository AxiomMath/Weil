module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# The inverse image of an abelian sheaf and its underlying sheaf of sets

Let `f : T ⟶ S` be a morphism of schemes of a big étale site and `𝒜` an abelian sheaf on the
small étale site of `S`, with underlying sheaf of sets `𝒜°` and addition `m : 𝒜° × 𝒜° ⟶ 𝒜°`.
There are two inverse images, `f^*_Ab` of abelian sheaves and `f^*_Set` of sheaves of sets. The
canonical map `c : f^*_Set 𝒜° ⟶ (f^*_Ab 𝒜)°` is the mate, along the two adjunctions
`f^* ⊣ f_*`, of the identity `f_* (ℱ°) = (f_* ℱ)°` (direct images of abelian sheaves and of
sheaves of sets have the same sections). It is an isomorphism, and through `c` and the comparison
`f^*_Set (𝒜° × 𝒜°) ⟶ f^*_Set 𝒜° × f^*_Set 𝒜°` the addition of `f^*_Ab 𝒜` is `f^*_Set (m)`.

## Main definitions

* `CategoryTheory.Sheaf.addHom` — the addition `𝒜° × 𝒜° ⟶ 𝒜°` of an abelian sheaf, as a
  morphism of sheaves of sets.
* `CategoryTheory.sheafPullbackForgetComparison` — for a continuous functor of sites and
  left adjoints `L₁`, `L₂` of the direct images of abelian sheaves and of sheaves of sets, the
  comparison `L₂ (𝒜°) ⟶ (L₁ 𝒜)°`, the mate of the identity of direct images.
* `AlgebraicGeometry.smallEtaleInverseImageForgetComparison` — the canonical map
  `f^*_Set 𝒜° ⟶ (f^*_Ab 𝒜)°` on the small étale sites.

## Main results

* `CategoryTheory.map_addHom_comp_sheafPullbackForgetComparison` — the comparison carries
  `L₂ (m)` to the addition of `L₁ 𝒜`.
* `AlgebraicGeometry.isIso_smallEtaleInverseImageForgetComparison` — the canonical map is an
  isomorphism.
* `AlgebraicGeometry.smallEtaleInverseImage_map_addHom_comp_forgetComparison` — through it, the
  addition of `f^*_Ab 𝒜` is `f^*_Set (m)`.

## Implementation notes

The source deduces both statements from stalks. Here invertibility is the Stacks project's
`Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare`, which proves that the same mate,
taken along the explicit construction of inverse images by left Kan extension and
sheafification, is invertible, because the forgetful functor preserves the filtered colimits
computing the Kan extension and commutes with sheafification; the mate along the chosen left
adjoints is identified with it by uniqueness of left adjoints. The addition statement is formal:
it holds for any comparison which is natural, and uses only that `f^*_Ab` is additive, being a
left adjoint of an additive functor. The source's hypothesis that the schemes are noetherian and
separated is not needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

universe w v₁ v₂ u₁ u₂ u

namespace CategoryTheory

/-- Postcomposition of sheaves with a functor preserving limits of a shape `K` preserves limits
of shape `K`: limits of sheaves are computed on sections. -/
instance sheafCompose_preservesLimitsOfShape {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    [J.HasSheafCompose F] (K : Type*) [Category* K] [HasLimitsOfShape K A]
    [HasLimitsOfShape K B] [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) := by
    change PreservesLimitsOfShape K (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J B)

namespace Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasBinaryProducts (Sheaf J (Type w))]
  [HasBinaryProducts (Sheaf J AddCommGrpCat.{w})]
  [PreservesLimitsOfShape (Discrete WalkingPair) (sheafCompose J (forget AddCommGrpCat.{w}))]

/-- **The addition of an abelian sheaf** `𝒜`, as a morphism `𝒜° × 𝒜° ⟶ 𝒜°` of its underlying
sheaf of sets: the sum `pr₁ + pr₂ : 𝒜 × 𝒜 ⟶ 𝒜` of the two projections, on underlying sheaves of
sets, through the identification `(𝒜 × 𝒜)° ≅ 𝒜° × 𝒜°`. On sections it is `(a, b) ↦ a + b`. -/
def addHom (G : Sheaf J AddCommGrpCat.{w}) :
    (sheafCompose J (forget AddCommGrpCat.{w})).obj G ⨯
        (sheafCompose J (forget AddCommGrpCat.{w})).obj G ⟶
      (sheafCompose J (forget AddCommGrpCat.{w})).obj G :=
  inv (prodComparison (sheafCompose J (forget AddCommGrpCat.{w})) G G) ≫
    (sheafCompose J (forget AddCommGrpCat.{w})).map (prod.fst + prod.snd)

end Sheaf

section Comparison

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (uf : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [uf.IsContinuous J K]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  {L₁ : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}}
  {L₂ : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
  (adj₁ : L₁ ⊣ uf.sheafPushforwardContinuous AddCommGrpCat.{w} J K)
  (adj₂ : L₂ ⊣ uf.sheafPushforwardContinuous (Type w) J K)

/-- **The comparison of inverse images with the underlying sheaf of sets.** For left adjoints
`L₁`, `L₂` of the direct images of abelian sheaves and of sheaves of sets along a continuous
functor of sites, the natural map `L₂ (𝒜°) ⟶ (L₁ 𝒜)°`: the mate of the identity
`(f_* ℱ)° = f_* (ℱ°)` of direct images. -/
def sheafPullbackForgetComparison :
    TwoSquare (sheafCompose J (forget AddCommGrpCat.{w})) L₁ L₂
      (sheafCompose K (forget AddCommGrpCat.{w})) :=
  (mateEquiv adj₁ adj₂).symm (TwoSquare.mk _ _ _ _ (𝟙 _))

variable [HasBinaryProducts (Sheaf J AddCommGrpCat.{w})]
  [HasBinaryProducts (Sheaf K (Type w))] [HasBinaryProducts (Sheaf K AddCommGrpCat.{w})]
  [PreservesLimitsOfShape (Discrete WalkingPair) (sheafCompose J (forget AddCommGrpCat.{w}))]
  [PreservesLimitsOfShape (Discrete WalkingPair) (sheafCompose K (forget AddCommGrpCat.{w}))]

/-- **The comparison carries `L₂ (m)` to the addition of `L₁ 𝒜`.** Through the comparison
`c : L₂ (𝒜°) ⟶ (L₁ 𝒜)°` and the comparison `L₂ (𝒜° × 𝒜°) ⟶ L₂ 𝒜° × L₂ 𝒜°` of `L₂` with
products, the image `L₂ (m)` of the addition `m` of `𝒜` is the addition of `L₁ 𝒜`. -/
theorem map_addHom_comp_sheafPullbackForgetComparison (G : Sheaf J AddCommGrpCat.{w}) :
    L₂.map (Sheaf.addHom G) ≫ (sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.app G =
      prodComparison L₂ _ _ ≫
        prod.map ((sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.app G)
          ((sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.app G) ≫
        Sheaf.addHom (L₁.obj G) := by
  have : (uf.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have := adj₁.left_adjoint_additive
  have h1 := (sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.naturality
    (prod.fst + prod.snd : G ⨯ G ⟶ G)
  have h2 : L₁.map (prod.fst + prod.snd : G ⨯ G ⟶ G) =
      prodComparison L₁ G G ≫ (prod.fst + prod.snd) := by
    rw [L₁.map_add, Preadditive.comp_add, prodComparison_fst, prodComparison_snd]
  have h3 : (sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.app (G ⨯ G) ≫
      (sheafCompose K (forget AddCommGrpCat.{w})).map (prodComparison L₁ G G) ≫
        prodComparison (sheafCompose K (forget AddCommGrpCat.{w})) (L₁.obj G) (L₁.obj G) =
      L₂.map (prodComparison (sheafCompose J (forget AddCommGrpCat.{w})) G G) ≫
        prodComparison L₂ _ _ ≫
        prod.map ((sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.app G)
          ((sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.app G) := by
    apply prod.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]
      erw [prod.map_fst]
      rw [prodComparison_fst]
      simp only [← Functor.map_comp, prodComparison_fst]
      rw [prodComparison_fst_assoc, ← Functor.map_comp_assoc, prodComparison_fst]
      exact ((sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.naturality
        (prod.fst : G ⨯ G ⟶ G)).symm
    · rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc]
      erw [prod.map_snd]
      rw [prodComparison_snd]
      simp only [← Functor.map_comp, prodComparison_snd]
      rw [prodComparison_snd_assoc, ← Functor.map_comp_assoc, prodComparison_snd]
      exact ((sheafPullbackForgetComparison uf J K adj₁ adj₂).natTrans.naturality
        (prod.snd : G ⨯ G ⟶ G)).symm
  rw [← cancel_epi (L₂.map (prodComparison (sheafCompose J (forget AddCommGrpCat.{w})) G G))]
  simp only [Sheaf.addHom, ← L₂.map_comp_assoc, IsIso.hom_inv_id_assoc]
  refine h1.trans ?_
  simp only [Functor.comp_map, h2, Functor.map_comp]
  rw [← reassoc_of% h3, IsIso.hom_inv_id_assoc]

end Comparison

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The forgetful functor of abelian groups preserves left Kan extensions along the opposite of
base change of étale schemes: base change is representably flat, so the categories indexing the
pointwise Kan extension are filtered, and the forgetful functor preserves filtered colimits. -/
instance preservesLeftKanExtensions_forget_smallEtaleBaseChange :
    (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions (smallEtaleBaseChange B f).op := by
  intro P
  have hfil : ∀ V : (SmallEtale B T.obj T.property)ᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange B f).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange B f) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  infer_instance

/-- **The canonical map `f^*_Set 𝒜° ⟶ (f^*_Ab 𝒜)°`** from the inverse image of the underlying
sheaf of sets of an abelian sheaf `𝒜` on the small étale site of `S` to the underlying sheaf of
sets of its abelian inverse image: the mate, along the adjunctions `f^* ⊣ f_*` for abelian
sheaves and for sheaves of sets, of the identity of direct images. -/
@[weil "lem_fk104_inverse_image_abelian_underlying_sets"]
abbrev smallEtaleInverseImageForgetComparison :
    TwoSquare (sheafCompose (SmallEtale.topology B S.obj S.property) (forget AddCommGrpCat.{u + 1}))
      (smallEtaleInverseImage B f AddCommGrpCat.{u + 1})
      (smallEtaleInverseImage B f (Type (u + 1)))
      (sheafCompose (SmallEtale.topology B T.obj T.property) (forget AddCommGrpCat.{u + 1})) :=
  sheafPullbackForgetComparison.{u + 1} (smallEtaleBaseChange B f)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (smallEtaleInverseImageAdjunction B f AddCommGrpCat.{u + 1})
    (smallEtaleInverseImageAdjunction B f (Type (u + 1)))

/-- **The canonical map `f^*_Set 𝒜° ⟶ (f^*_Ab 𝒜)°` is an isomorphism**, naturally in `𝒜`. -/
@[weil "lem_fk104_inverse_image_abelian_underlying_sets"]
instance isIso_smallEtaleInverseImageForgetComparison :
    IsIso (smallEtaleInverseImageForgetComparison B f).natTrans :=
  Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq _
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _) _
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _) _
    (Stacks.EtaleCohomology.isIso_coefficientPullbackTwoSquare (smallEtaleBaseChange B f)
      (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
      (forget AddCommGrpCat.{u + 1}))

/-- **The addition of `f^*_Ab 𝒜` is `f^*_Set (m)`.** Through the canonical isomorphism
`c : f^*_Set 𝒜° ≅ (f^*_Ab 𝒜)°` and the comparison
`f^*_Set (𝒜° × 𝒜°) ⟶ f^*_Set 𝒜° × f^*_Set 𝒜°` of the inverse image with products, the inverse
image `f^*_Set (m)` of the addition `m` of `𝒜` is the addition of `f^*_Ab 𝒜`. -/
@[weil "lem_fk104_inverse_image_abelian_underlying_sets"]
theorem smallEtaleInverseImage_map_addHom_comp_forgetComparison
    (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}) :
    (smallEtaleInverseImage B f (Type (u + 1))).map (Sheaf.addHom G) ≫
        (smallEtaleInverseImageForgetComparison B f).natTrans.app G =
      prodComparison (smallEtaleInverseImage B f (Type (u + 1))) _ _ ≫
        prod.map ((smallEtaleInverseImageForgetComparison B f).natTrans.app G)
          ((smallEtaleInverseImageForgetComparison B f).natTrans.app G) ≫
        Sheaf.addHom ((smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).obj G) :=
  map_addHom_comp_sheafPullbackForgetComparison.{u + 1} _ _ _ _ _ G

end AlgebraicGeometry
