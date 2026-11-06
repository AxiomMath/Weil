module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurvePicardBaseCase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeNormal
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal

/-!
# The normalization of a curve in a finite étale cover of an open subscheme

Let `k` be a perfect field, `X` a smooth proper curve over `k`, `U ⊆ X` an open subscheme and
`g : V ⟶ U` a finite étale morphism with `V` connected. Write `f : V ⟶ X` for the composite of
`g` with the inclusion of `U`, and `X̄_V := f.normalization` for the relative normalization of `X`
in `V`, with its integral morphism `h̄ : X̄_V ⟶ X` and the dominant morphism `V ⟶ X̄_V`.

Then:

* `h̄` is finite, `X` being of finite type over a field, hence Nagata;
* `X̄_V` is integral and normal, since `V` is (a connected scheme smooth over a field);
* `V ⟶ X̄_V` is an open immersion with image exactly `h̄⁻¹(U)`: it is an open immersion as `f` is
  separated and quasi-finite, and its image is closed in `h̄⁻¹(U)` because `g` is universally
  closed and `h̄⁻¹(U) ⟶ U` is separated, and dense because `V ⟶ X̄_V` is dominant;
* `h̄` is surjective, so `X̄_V` has dimension one, and `X̄_V` is a smooth projective curve over
  `k`: proper normal of dimension one over a perfect field.

This is the compactification of a finite étale cover of an open of a curve used in the dévissage
of constructible sheaves on the projective line: the direct image along `h̄⁻¹(U) ⟶ X̄_V` of a
constant sheaf is constant (Stacks 09Z5), which applies because `X̄_V` is integral and normal.

## Main results

* `AlgebraicGeometry.isFinite_fromNormalization_comp_ι`: `h̄` is finite.
* `AlgebraicGeometry.isIntegral_normalization_comp_ι`,
  `AlgebraicGeometry.isNormal_normalization_comp_ι`: `X̄_V` is integral and normal.
* `AlgebraicGeometry.range_toNormalization_comp_ι`: the image of `V` in `X̄_V` is `h̄⁻¹(U)`.
* `AlgebraicGeometry.normalizationCompιPreimageIso`: the isomorphism `V ≅ h̄⁻¹(U)` over `U`.
* `AlgebraicGeometry.surjective_fromNormalization_comp_ι`: `h̄` is surjective.
* `AlgebraicGeometry.isCurve_smooth_isProjectiveVariety_normalization_comp_ι`: `X̄_V` is a smooth
  projective curve over `k`.
* `AlgebraicGeometry.isIso_unit_app_constantSheaf_normalization_comp_ι`: along the inclusion `j` of
  `h̄⁻¹(U)` the unit `M ⟶ j_* j^* M` at a constant abelian sheaf is an isomorphism.

## References

* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
* [Stacks Project, Tag 03GR](https://stacks.math.columbia.edu/tag/03GR)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 09Z5](https://stacks.math.columbia.edu/tag/09Z5)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k))
  {U : X.Opens}
  {V : Scheme.{u}} (g : V ⟶ U.toScheme) [IsFinite g]

/-- The normalization of a scheme locally of finite type over a field in a reduced scheme finite
over an open subscheme is finite. -/
theorem isFinite_fromNormalization_comp_ι [LocallyOfFiniteType p] [IsReduced V] :
    IsFinite (g ≫ U.ι).fromNormalization :=
  isFinite_fromNormalization_of_locallyOfFiniteType (g ≫ U.ι)
    (isNagataScheme_of_locallyOfFiniteType_over_field k p)

/-- The preimage of `U` in the normalization of `X` in `V` contains the image of `V`. -/
theorem range_toNormalization_comp_ι_subset :
    Set.range (g ≫ U.ι).toNormalization ⊆ ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U : Set _) := by
  rintro _ ⟨v, rfl⟩
  change ((g ≫ U.ι).toNormalization ≫ (g ≫ U.ι).fromNormalization) v ∈ U
  rw [Scheme.Hom.toNormalization_fromNormalization]
  exact (g v).2

/-- The morphism from `V` to the preimage of `U` in the normalization of `X` in `V`. -/
def toNormalizationPreimage :
    V ⟶ ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι) (g ≫ U.ι).toNormalization
    (by rw [Scheme.Opens.range_ι]; exact range_toNormalization_comp_ι_subset g)

@[reassoc (attr := simp)]
theorem toNormalizationPreimage_ι :
    toNormalizationPreimage g ≫ ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι =
      (g ≫ U.ι).toNormalization :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem toNormalizationPreimage_morphismRestrict :
    toNormalizationPreimage g ≫ ((g ≫ U.ι).fromNormalization ∣_ U) = g := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, toNormalizationPreimage_ι_assoc,
    Scheme.Hom.toNormalization_fromNormalization]

/-- The image of `V` in the normalization of `X` in `V` is closed in the preimage of `U`: the
morphism to that preimage is universally closed, `g` being finite and the preimage separated over
`U`. -/
theorem isClosed_range_toNormalizationPreimage :
    IsClosed (Set.range (toNormalizationPreimage g)) := by
  have : UniversallyClosed (toNormalizationPreimage g ≫ ((g ≫ U.ι).fromNormalization ∣_ U)) := by
    rw [toNormalizationPreimage_morphismRestrict]; infer_instance
  have := UniversallyClosed.of_comp_of_isSeparated (toNormalizationPreimage g)
    ((g ≫ U.ι).fromNormalization ∣_ U)
  exact (toNormalizationPreimage g).isClosedMap.isClosed_range

/-- The image of `V` in the normalization of `X` in `V` is dense in the preimage of `U`. -/
theorem dense_range_toNormalizationPreimage :
    Dense (Set.range (toNormalizationPreimage g)) := by
  have h : Set.range (toNormalizationPreimage g) =
      ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι ⁻¹' Set.range (g ≫ U.ι).toNormalization := by
    rw [← toNormalizationPreimage_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι.isOpenEmbedding.injective.preimage_image]
  rw [h]
  exact (g ≫ U.ι).toNormalization.denseRange.preimage
    ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap

theorem range_toNormalizationPreimage :
    Set.range (toNormalizationPreimage g) = Set.univ := by
  rw [← (isClosed_range_toNormalizationPreimage g).closure_eq]
  exact (dense_range_toNormalizationPreimage g).closure_eq

instance : IsOpenImmersion (toNormalizationPreimage g) := by
  have : IsOpenImmersion (toNormalizationPreimage g ≫ ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι) := by
    rw [toNormalizationPreimage_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι

instance : IsIso (toNormalizationPreimage g) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ <| by
    ext x; simp [Scheme.Hom.opensRange, range_toNormalizationPreimage g]

/-- **The image of `V` in the normalization of `X` in `V` is the preimage of `U`.** -/
theorem range_toNormalization_comp_ι :
    Set.range (g ≫ U.ι).toNormalization = ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U : Set _) := by
  rw [← toNormalizationPreimage_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    range_toNormalizationPreimage, Set.image_univ, Scheme.Opens.range_ι]

/-- The isomorphism of `V` with the preimage of `U` in the normalization of `X` in `V`; it lies
over `U` (`normalizationCompιPreimageIso_hom_morphismRestrict`). -/
def normalizationCompιPreimageIso :
    V ≅ ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).toScheme :=
  asIso (toNormalizationPreimage g)

@[reassoc (attr := simp)]
theorem normalizationCompιPreimageIso_hom_morphismRestrict :
    (normalizationCompιPreimageIso g).hom ≫ ((g ≫ U.ι).fromNormalization ∣_ U) = g :=
  toNormalizationPreimage_morphismRestrict g

@[reassoc (attr := simp)]
theorem normalizationCompιPreimageIso_hom_ι :
    (normalizationCompιPreimageIso g).hom ≫ ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι =
      (g ≫ U.ι).toNormalization :=
  toNormalizationPreimage_ι g

/-! ### A finite étale cover of an open of a smooth proper curve -/

section Curve

variable [Smooth p] [Etale g] [ConnectedSpace V]

omit [IsLocallyNoetherian X] [IsFinite g] in
include p g in
/-- A connected scheme `V` étale over an open of a smooth curve is integral. -/
theorem isIntegral_of_etale_comp_ι : IsIntegral V :=
  Stacks.Chow.isIntegral_of_connectedSpace_of_smooth ((g ≫ U.ι) ≫ p)

omit [IsLocallyNoetherian X] [IsFinite g] [ConnectedSpace V] in
include p g in
/-- A finite étale cover `V` of an open of a smooth curve is normal. -/
theorem isNormal_of_etale_comp_ι : IsNormal V :=
  isNormal_of_isRegular V (isRegular_of_smooth_over_field ((g ≫ U.ι) ≫ p))

include p g in
/-- **The normalization of `X` in `V` is integral.** -/
theorem isIntegral_normalization_comp_ι : IsIntegral (g ≫ U.ι).normalization := by
  have := isIntegral_of_etale_comp_ι p g
  infer_instance

include p g in
/-- **The normalization of `X` in `V` is normal.** -/
theorem isNormal_normalization_comp_ι : IsNormal (g ≫ U.ι).normalization := by
  have := isIntegral_of_etale_comp_ι p g
  have := isNormal_of_etale_comp_ι p g
  exact isNormal_normalization (g ≫ U.ι)
    (Stacks.EtaleCohomology.finiteIrreducibleComponents_of_isIntegral V)

include g in
/-- **The normalization of `X` in `V` maps onto `X`**: its image is closed, the morphism being
integral, and contains the image of `V`, a nonempty open of the irreducible scheme `X`. -/
theorem surjective_fromNormalization_comp_ι [IrreducibleSpace X] :
    Surjective (g ≫ U.ι).fromNormalization := by
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  have hopen : IsOpen (Set.range (g ≫ U.ι)) := (g ≫ U.ι).isOpenMap.isOpen_range
  have : Nonempty V := ConnectedSpace.toNonempty
  have hne : (Set.range (g ≫ U.ι)).Nonempty := Set.range_nonempty _
  have hsub : Set.range (g ≫ U.ι) ⊆ Set.range (g ≫ U.ι).fromNormalization := by
    rintro _ ⟨v, rfl⟩
    exact ⟨(g ≫ U.ι).toNormalization v, by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]⟩
  have hcl : IsClosed (Set.range (g ≫ U.ι).fromNormalization) :=
    (g ≫ U.ι).fromNormalization.isClosedMap.isClosed_range
  have hd : Dense (Set.range (g ≫ U.ι).fromNormalization) :=
    (hopen.dense hne).mono hsub
  have : Set.range (g ≫ U.ι).fromNormalization = Set.univ := by
    rw [← hcl.closure_eq]; exact hd.closure_eq
  exact ⟨Set.range_eq_univ.mp this⟩

include p g in
/-- **The normalization of a smooth proper curve in a connected finite étale cover of an open is
a smooth projective curve.** Let `X` be a smooth proper curve over a perfect field `k`, `U ⊆ X`
open and `g : V ⟶ U` finite étale with `V` connected. Then the normalization of `X` in `V` is a
smooth projective curve over `k`: it is integral and normal, and of dimension one since it is
finite over `X` and maps onto `X`. -/
theorem isCurve_smooth_isProjectiveVariety_normalization_comp_ι [PerfectField k] [IsCurve k p]
    [IsProper p] :
    IsCurve k ((g ≫ U.ι).fromNormalization ≫ p) ∧ Smooth ((g ≫ U.ι).fromNormalization ≫ p) ∧
      IsProjectiveVariety k ((g ≫ U.ι).fromNormalization ≫ p) := by
  have := isIntegral_of_etale_comp_ι p g
  have := isIntegral_normalization_comp_ι p g
  have := isNormal_normalization_comp_ι p g
  have := surjective_fromNormalization_comp_ι g
  have := isFinite_fromNormalization_comp_ι p g
  have hdim : topologicalKrullDim (g ≫ U.ι).normalization = 1 := by
    rw [topologicalKrullDim_eq_of_isIntegralHom_of_surjective (g ≫ U.ι).fromNormalization]
    exact IsCurve.topologicalKrullDim_eq_one (k := k) (f := p)
  exact isCurve_smooth_isProjectiveVariety_of_isNormal k _ hdim

/-- The preimage of `U` in the normalization of `X` in `V` is nonempty. -/
theorem nonempty_preimage_fromNormalization_comp_ι :
    (((g ≫ U.ι).fromNormalization ⁻¹ᵁ U : (g ≫ U.ι).normalization.Opens) :
      Set (g ≫ U.ι).normalization).Nonempty := by
  have : Nonempty V := ConnectedSpace.toNonempty
  obtain ⟨v⟩ := this
  exact ⟨_, range_toNormalization_comp_ι_subset g ⟨v, rfl⟩⟩

include p in
/-- **The direct image of a constant sheaf from `V` to the normalization is constant.** Along the
inclusion `j` of the preimage of `U` (which is `V`, `normalizationCompιPreimageIso`) into the
normalization of `X` in `V`, the unit `M ⟶ j_* j^* M` at the constant sheaf `M` is an isomorphism
of abelian sheaves on the small étale site, the normalization being integral and normal. -/
theorem isIso_unit_app_constantSheaf_normalization_comp_ι
    (M : AddCommGrpCat.{max (u + 1) v}) :
    IsIso (((Stacks.EtaleCohomology.smallEtaleBaseChange
      ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).ι).sheafAdjunctionContinuous
      AddCommGrpCat.{max (u + 1) v} (g ≫ U.ι).normalization.smallEtaleTopology
      ((g ≫ U.ι).fromNormalization ⁻¹ᵁ U).toScheme.smallEtaleTopology).unit.app
        ((constantSheaf (g ≫ U.ι).normalization.smallEtaleTopology _).obj M)) := by
  have := isIntegral_normalization_comp_ι p g
  have := isNormal_normalization_comp_ι p g
  exact Scheme.isIso_unit_app_constantSheaf_opensι_addCommGrpCat _
    (nonempty_preimage_fromNormalization_comp_ι g) M

end Curve

end AlgebraicGeometry
