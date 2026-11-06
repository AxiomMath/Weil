/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonColimits
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonCurve
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonFinite
public import WeilFrontier.CategoryTheory.Abelian.EffaceableComparisonDegreeZero
public import WeilFrontier.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.Main
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianConstructibleImages
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CurvePicardBaseCase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierProperCurves.AbelianAssembly
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic

/-!
# The comparison theorem for the projective line

Let `X` be a scheme proper over `ℂ` of dimension at most one, with `X(ℂ)` compact (for instance a
projective curve, or the projective line `ℙ¹_ℂ`). For every torsion abelian sheaf `F` on the small
étale site of `X` and every `n`, the comparison map
`c^n(X, F) : H^n_et(X, F) → H^n(X(ℂ), F_an)` is bijective.

The proof is a dévissage. By the commutation of both sides with filtered colimits it suffices to
treat constructible `F`, and constructible sheaves are stable under quotients. By the
effaceability criterion it then suffices to embed every constructible `F` into a constructible
sheaf on which `c` is bijective in every degree. Such an embedding is
`F ↪ ⨁ⱼ fⱼ_* M̲ⱼ ↪ ⨁ⱼ (fⱼ ∘ νⱼ)_* M̲ⱼ`, where `fⱼ : Yⱼ ⟶ X` is finite with `Yⱼ` integral and
`Mⱼ` a finite abelian group (Stacks 09Z6), and `νⱼ : Ỹⱼ ⟶ Yⱼ` is the normalization, a finite
surjective morphism, so that `M̲ ⟶ νⱼ_* M̲` is injective. On a direct image along a finite
morphism the comparison map is that of the source, and the source `Ỹⱼ` is normal, integral,
proper over `ℂ` and of dimension at most one: either a point, where the comparison map is
bijective for all sheaves, or a smooth projective curve, where it is bijective on finite constant
sheaves by the Kummer sequences and GAGA.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.pc_of_topologicalKrullDim_le_one`: `PC(X)` for `X`
  proper over `ℂ` of dimension at most one with `X(ℂ)` compact.
* `AlgebraicGeometry.Scheme.ComplexPoints.pc_line`: `PC(ℙ¹_ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_pushforward_constantSheaf_bijective`:
  the comparison map is bijective on the direct image of a finite constant sheaf along a finite
  morphism from a normal integral scheme, over such an `X`.

## Implementation notes

The constructible sheaves are those of
`Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf`, by transport to the small étale
site of `AlgebraicGeometry.BigEtaleSite.containing X`, where they form a weak Serre class.
The dévissage uses the embedding of Stacks 09Z6 into direct images from integral schemes rather
than the generic structure of a constructible sheaf on a curve (a dense open over which it is
finite locally constant): the integral schemes `Yⱼ` may be singular, and normalizing them is
what brings the smooth curves into play.

## References

* [Stacks Project, Tag 09Z6](https://stacks.math.columbia.edu/tag/09Z6)
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace ZeroObject

attribute [local instance 3000] Abelian.hasFiniteBiproducts

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [Abelian C] (P : ObjectProperty C)

/-- A property of objects of an abelian category containing a zero object and closed under
isomorphisms and extensions is closed under finite products: a binary product is a binary
biproduct, an extension of one factor by the other. -/
theorem isClosedUnderFiniteProducts_of_isClosedUnderExtensions [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions] :
    P.IsClosedUnderFiniteProducts := by
  have : P.IsClosedUnderBinaryProducts := by
    refine IsClosedUnderLimitsOfShape.mk' ?_
    rintro _ ⟨K, hK⟩
    exact P.prop_of_iso ((Limits.biprod.isoProd _ _) ≪≫
      (Limits.HasLimit.isoOfNatIso (Limits.diagramIsoPair K)).symm)
      (P.prop_biprod (hK ⟨.left⟩) (hK ⟨.right⟩))
  exact IsClosedUnderFiniteProducts.mk'

/-- Under the hypotheses of `isClosedUnderFiniteProducts_of_isClosedUnderExtensions`, a finite
biproduct of objects satisfying `P` satisfies `P`. -/
theorem prop_biproduct_of_isClosedUnderExtensions [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions] {J : Type} [Finite J]
    (f : J → C) (hf : ∀ j, P (f j)) : P (⨁ f) := by
  have := P.isClosedUnderFiniteProducts_of_isClosedUnderExtensions
  have := Fintype.ofFinite J
  exact P.prop_of_iso (biproduct.isoProduct f).symm (P.prop_product hf)

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Scheme.ComplexPoints

open Stacks.EtaleCohomology

/-! ### Sheaves on which the comparison map is bijective -/

section Bijective

variable {X : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType x]

/-- The étale sheaves on which the comparison map is bijective in every degree. -/
def comparisonBijective : ObjectProperty (EtSheaf X) :=
  fun F => ∀ n, Function.Bijective (comparisonMap x F n)

instance : (comparisonBijective x).IsClosedUnderIsomorphisms where
  of_iso e h n := bijective_comparisonMap_of_iso x e n (h n)

instance : (comparisonBijective x).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := bijective_comparisonMap_of_shortExact x hS h₁ h₃

instance : (comparisonBijective x).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun n => by
    have h₀ : IsZero ((analyticInverseImage x).obj 0) :=
      (analyticInverseImage x).map_isZero (isZero_zero _)
    have : Subsingleton (Sheaf.H.{1} (0 : EtSheaf X) n) :=
      Abelian.Ext.subsingleton_of_isZero_right _ (isZero_zero _) n
    have : Subsingleton (Sheaf.H.{1} ((analyticInverseImage x).obj 0) n) :=
      Abelian.Ext.subsingleton_of_isZero_right _ h₀ n
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩

/-- The sheaves on which the comparison map is bijective in every degree are closed under finite
biproducts. -/
theorem comparisonBijective_biproduct {J : Type} [Finite J] (f : J → EtSheaf X)
    (hf : ∀ j n, Function.Bijective (comparisonMap x (f j) n)) (n : ℕ) :
    Function.Bijective (comparisonMap x (⨁ f) n) :=
  (comparisonBijective x).prop_biproduct_of_isClosedUnderExtensions f hf n

end Bijective

/-! ### Constructible sheaves on Mathlib's small étale site -/

section Constructible

variable {X : Scheme.{0}}

/-- **Constructible sheaves are stable under quotients**: in a short exact sequence of abelian
sheaves on `X_étale` whose first two terms are constructible, so is the third (Stacks 03RZ). -/
theorem isConstructibleSmallEtaleAbelianSheaf_X₃ {S : ShortComplex (EtSheaf X)}
    (hS : S.ShortExact) (h₁ : IsConstructibleSmallEtaleAbelianSheaf.{0, 0} S.X₁)
    (h₂ : IsConstructibleSmallEtaleAbelianSheaf.{0, 0} S.X₂) :
    IsConstructibleSmallEtaleAbelianSheaf.{0, 0} S.X₃ := by
  let E := (SmallEtale.sheafEquiv (BigEtaleSite.containing X) X
    (BigEtaleSite.contains_containing X) AddCommGrpCat.{1}).inverse
  have hS' := hS.map_of_exact E
  let B := BigEtaleSite.containing X
  let XB := B.obj X (BigEtaleSite.contains_containing X)
  let P : ObjectProperty (Sheaf (SmallEtale.topology B XB.obj XB.property) AddCommGrpCat.{1}) :=
    fun F => IsConstructibleAbelianSheaf B XB F
  have : P.IsWeakSerreClass := constructibleAbelianSheaf_isWeakSerreClass B XB
  exact P.prop_of_isColimit_cokernelCofork hS'.gIsCokernel h₁ h₂

/-- **A finite direct sum of constructible sheaves is constructible.** -/
theorem isConstructibleSmallEtaleAbelianSheaf_biproduct {J : Type} [Finite J]
    (f : J → EtSheaf X) (hf : ∀ j, IsConstructibleSmallEtaleAbelianSheaf.{0, 0} (f j)) :
    IsConstructibleSmallEtaleAbelianSheaf.{0, 0} (⨁ f) := by
  let E := (SmallEtale.sheafEquiv (BigEtaleSite.containing X) X
    (BigEtaleSite.contains_containing X) AddCommGrpCat.{1}).inverse
  let B := BigEtaleSite.containing X
  let XB := B.obj X (BigEtaleSite.contains_containing X)
  let P : ObjectProperty (Sheaf (SmallEtale.topology B XB.obj XB.property) AddCommGrpCat.{1}) :=
    fun F => IsConstructibleAbelianSheaf B XB F
  have : P.IsWeakSerreClass := constructibleAbelianSheaf_isWeakSerreClass B XB
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  exact P.prop_of_iso (E.mapBiproduct f).symm
    (P.prop_biproduct_of_isClosedUnderExtensions _ hf)

end Constructible

/-! ### Direct images from normal schemes finite over a curve -/

section Normal

/-- An irreducible space of dimension at most zero with a closed point is that point. -/
theorem _root_.subsingleton_of_topologicalKrullDim_nonpos {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] (h : topologicalKrullDim T ≤ 0) {z : T} (hz : IsClosed {z}) :
    Subsingleton T := by
  let a : IrreducibleCloseds T := ⟨{z}, isIrreducible_singleton, hz⟩
  let b : IrreducibleCloseds T := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  have hab : a ≤ b := fun _ _ => Set.mem_univ _
  have hba : b ≤ a := (Order.krullDim_nonpos_iff_forall_isMin.1 h b) hab
  refine ⟨fun w w' => ?_⟩
  have hw : w ∈ (a : Set T) := hba (Set.mem_univ w)
  have hw' : w' ∈ (a : Set T) := hba (Set.mem_univ w')
  exact hw.trans hw'.symm

variable {X : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) [IsProper x]

/-- **The comparison map on direct images from a normal scheme finite over a curve.** Let `X` be
proper over `ℂ` of dimension at most one and `h : Z ⟶ X` finite with `Z` normal and integral.
For every finite abelian group `M` and every `n`, the comparison map is bijective on
`h_* M̲`. It is the comparison map of `Z` on `M̲`, and `Z`, of dimension at most one, is either a
point, where the comparison map is bijective on every sheaf, or a smooth projective curve. -/
theorem comparisonMap_pushforward_constantSheaf_bijective (hX : topologicalKrullDim X ≤ 1)
    {Z : Scheme.{0}} [IsIntegral Z] [IsNormal Z] (h : Z ⟶ X) [IsFinite h]
    (M : AddCommGrpCat.{1}) [Finite M] (n : ℕ) :
    Function.Bijective (comparisonMap x ((smallEtalePushforwardAb h).obj
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).obj M)) n) := by
  rw [comparisonMap_pushforward_bijective_iff x (h ≫ x) h rfl]
  have hZ : topologicalKrullDim Z ≤ 1 := (topologicalKrullDim_le_of_isIntegralHom h).trans hX
  by_cases h1 : topologicalKrullDim Z = 1
  · obtain ⟨_, _, _⟩ := isCurve_smooth_isProjectiveVariety_of_isNormal ℂ (h ≫ x) h1
    exact comparisonMap_constant_finite_bijective_of_curve (h ≫ x) M n
  · have h0 : topologicalKrullDim Z ≤ 0 :=
      Order.le_of_lt_succ (lt_of_le_of_ne hZ h1)
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (h ≫ x)
    obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
    have := subsingleton_of_topologicalKrullDim_nonpos h0 hz
    let p : ComplexPoints (h ≫ x) := (pointEquivClosedPoint (h ≫ x)).symm ⟨z, hz⟩
    have : IsClosedImmersion p.hom := isClosedImmersion_hom (h ≫ x) p
    have : Surjective p.hom := ⟨fun w => ⟨IsLocalRing.closedPoint ℂ, Subsingleton.elim _ _⟩⟩
    have : IsIso p.hom := isIso_of_isClosedImmersion_of_surjective p.hom
    have hpc : PC (h ≫ x) := (pc_iff_of_iso (h ≫ x) (𝟙 _) (asIso p.hom) p.2).2
      (fun F _ m => comparisonBijectiveOn_spec F trivial m)
    exact hpc _ (torsionSheafProperty_of_isConstructibleEtaleAbelianSheaf _
      (isConstructibleEtaleAbelianSheaf_constantSheaf Z M)) n

end Normal

/-! ### Normalization -/

section Normalization

variable {X : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType x] [IsSeparated x]
  [QuasiCompact x]

/-- A dominant morphism with closed image is surjective. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.surjective_of_isDominant_of_isClosedMap
    {Y Z : Scheme.{0}} (g : Y ⟶ Z) [IsDominant g] (hg : IsClosedMap g) : Surjective g :=
  ⟨Set.range_eq_univ.mp (by
    rw [← hg.isClosed_range.closure_eq]; exact g.denseRange.closure_eq)⟩

include x in
/-- **A finite constant sheaf on an integral scheme embeds into the direct image of the constant
sheaf on its normalization.** Let `f : Y ⟶ X` be finite, `Y` integral and `X` separated of
finite type over `ℂ`. Then the direct image `f_* M̲` embeds into `(f ∘ ν)_* M̲` for the
normalization `ν : Ỹ ⟶ Y`, a finite surjective morphism from a normal integral scheme; the
composite `f ∘ ν` is finite. -/
theorem exists_mono_etaleAbelianDirectImage_constantSheaf_of_isNormal {Y : Scheme.{0}}
    [IsIntegral Y] (f : Y ⟶ X) [IsFinite f] (M : AddCommGrpCat.{1}) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (_ : IsNormal Z) (h : Z ⟶ X) (_ : IsFinite h)
      (u : (etaleAbelianDirectImage.{0, 0} f).obj
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj M) ⟶
        (etaleAbelianDirectImage.{0, 0} h).obj
          ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{1}).obj M)), Mono u := by
  let y := f ≫ x
  have : IsVariety ℂ y := {}
  let ν := normalizationOverField ℂ y
  have := isFinite_normalizationOverField ℂ y
  have := isDominant_normalizationOverField ℂ y
  have hV : IsVariety ℂ (ν ≫ y) := inferInstance
  have : IsIntegral (normalizationSchemeOverField ℂ y) := hV.toIsIntegral
  have : IsNormal (normalizationSchemeOverField ℂ y) :=
    Scheme.isNormal_normalizationScheme Y _
  have : Surjective ν := ν.surjective_of_isDominant_of_isClosedMap ν.isClosedMap
  let u₀ : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj M ⟶
      (etaleAbelianDirectImage.{0, 0} ν).obj
        ((constantSheaf (normalizationSchemeOverField ℂ y).smallEtaleTopology
          AddCommGrpCat.{1}).obj M) :=
    (etaleAbelianInverseImageDirectImageAdj.{0, 0} ν).unit.app _ ≫
      ((etaleAbelianDirectImage.{0, 0} ν).mapIso
        ((etaleAbelianInverseImageConstantIso.{0, 0} ν).app M)).hom
  have : Mono u₀ := @mono_comp _ _ _ _ _ _ (mono_etaleAbelianUnit_of_surjective ν
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj M)) _ inferInstance
  have :=
    Functor.preservesMonomorphisms_of_adjunction (etaleAbelianInverseImageDirectImageAdj.{0, 0} f)
  have : Mono ((etaleAbelianDirectImage.{0, 0} f).map u₀) := Functor.map_mono _ _
  exact ⟨_, inferInstance, inferInstance, ν ≫ f, inferInstance,
    (etaleAbelianDirectImage.{0, 0} f).map u₀ ≫
      ((etaleAbelianDirectImageCompIso.{0, 0} ν f).app _).hom,
    @mono_comp _ _ _ _ _ _ this _ (@IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _))⟩

end Normalization

/-! ### The comparison theorem in dimension at most one -/

section Main

variable {X : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) [IsProper x]

/-- **Every constructible sheaf embeds into a constructible sheaf with bijective comparison
maps**, on a scheme proper over `ℂ` of dimension at most one. The embedding is
`F ↪ ⨁ⱼ fⱼ_* M̲ⱼ ↪ ⨁ⱼ (fⱼ ∘ νⱼ)_* M̲ⱼ` of Stacks 09Z6 followed by the normalizations `νⱼ` of the
integral schemes `Yⱼ`. -/
theorem exists_mono_comparisonBijective_of_isConstructible (hX : topologicalKrullDim X ≤ 1)
    (F : EtSheaf X) (hF : IsConstructibleSmallEtaleAbelianSheaf.{0, 0} F) :
    ∃ (G : EtSheaf X) (i : F ⟶ G), Mono i ∧ IsConstructibleSmallEtaleAbelianSheaf.{0, 0} G ∧
      ∀ n, Function.Bijective (comparisonMap x G n) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian x
  have : IsNoetherian X := {}
  obtain ⟨J, hJ, Y, f, hf, -, M, hM, m, hm, hgen⟩ :=
    exists_mono_biproduct_etaleAbelianDirectImage_constantSheaf_isGenericallyFiniteEtale F hF
  choose Z hZi hZn h hh u hu using fun j =>
    have := (hgen j).1
    exists_mono_etaleAbelianDirectImage_constantSheaf_of_isNormal x (f j) (M j)
  have : Mono (biproduct.map u) := biproduct.map_mono u
  refine ⟨⨁ fun j => (etaleAbelianDirectImage.{0, 0} (h j)).obj
    ((constantSheaf (Z j).smallEtaleTopology AddCommGrpCat.{1}).obj (M j)),
    m ≫ biproduct.map u, mono_comp _ _, ?_, ?_⟩
  · refine isConstructibleSmallEtaleAbelianSheaf_biproduct _ fun j => ?_
    have := hh j
    exact isConstructibleEtaleAbelianSheaf_etaleAbelianDirectImage_of_isFinite (h j)
      ⟨inferInstance, inferInstance, inferInstance⟩ _
      (isConstructibleEtaleAbelianSheaf_constantSheaf _ _)
  · refine comparisonBijective_biproduct x _ fun j n => ?_
    have := hZi j
    have := hZn j
    have := hh j
    exact comparisonMap_pushforward_constantSheaf_bijective x hX (h j) (M j) n

/-- **The comparison theorem for schemes of dimension at most one.** Let `X` be proper over `ℂ`
of dimension at most one, with `X(ℂ)` compact. Then for every torsion abelian sheaf `F` on
`X_étale` and every `n` the comparison map `H^n_et(X, F) → H^n(X(ℂ), F_an)` is bijective. -/
theorem pc_of_topologicalKrullDim_le_one [CompactSpace (ComplexPoints x)]
    (hX : topologicalKrullDim X ≤ 1) : PC x :=
  pc_of_constructible x fun F hF n =>
    (analyticInverseImage x).mapExtOfIso_bijective_of_effaceable'
      ((constantSheafIso x).app (AddCommGrpCat.of (ULift ℤ)))
      (fun F => IsConstructibleSmallEtaleAbelianSheaf.{0, 0} F)
      (fun _ hS h₁ h₂ => isConstructibleSmallEtaleAbelianSheaf_X₃ hS h₁ h₂)
      (fun F hF => exists_mono_comparisonBijective_of_isConstructible x hX F hF) n F hF

end Main

/-- The projective line over a field is proper. -/
instance _root_.AlgebraicGeometry.SymmetricProduct.isProper_lineOver_hom (k : Type) [Field k] :
    IsProper (SymmetricProduct.lineOver k).hom :=
  Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1

/-- **The comparison theorem for the projective line.** For every torsion abelian sheaf `F` on
the small étale site of `ℙ¹_ℂ` and every `n`, the comparison map
`H^n_et(ℙ¹_ℂ, F) → H^n(ℙ¹(ℂ), F_an)` is bijective. -/
theorem pc_line : PC (SymmetricProduct.lineOver ℂ).hom := by
  have : CompactSpace (ComplexPoints (SymmetricProduct.lineOver ℂ).hom) := compactSpace_proj 1
  refine pc_of_topologicalKrullDim_le_one _ ?_
  rw [show topologicalKrullDim (SymmetricProduct.lineOver ℂ).left = _ from
    Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin ℂ (r := 2) (by norm_num)]
  norm_num

end AlgebraicGeometry.Scheme.ComplexPoints
