module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.SmoothCurveCohomologyConstantVanishQGt2
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem

/-!
# Vanishing of `H^q(X, (𝐙/n𝐙)_X)` for `q > 1` on an affine curve

Let `k` be an algebraically closed field and `X` an affine scheme of finite type over `k` of
dimension at most one (for instance an affine smooth curve over `k`). For every abelian sheaf `F`
on the small étale site of `X` killed by some integer `n ≥ 1`, and in particular for the constant
sheaf `(𝐙/n𝐙)_X`, the étale cohomology `H^q(X, F)` vanishes for every `q > 1`.

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_of_nsmul_id_eq_zero_of_isAffine`:
  `H^q(X, F) = 0` for `q ≥ 2`, `X` affine, and `F` an abelian sheaf on `SmallEtale B X hX` with
  `n • 𝟙 F = 0`, `n ≥ 1`.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_constantSheaf_zmod_of_isAffine_of_one_lt`:
  `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 1`, the constant sheaf being the sheafification of the
  constant presheaf.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_locallyConstantSheafAb_zmod_of_isAffine`:
  the same for the constant sheaf as the sheaf of locally constant `𝐙/n𝐙`-valued functions.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_constantSheaf_zmod_of_isCurve_of_isAffine`:
  the same on an affine curve in the sense of `AlgebraicGeometry.IsCurve`.

## Implementation notes

The proof is that of [Stacks, Tag 0A54]: `(𝐙/n𝐙)_X` is a torsion sheaf, and every torsion sheaf
on an affine scheme of finite type and of dimension at most one over an algebraically closed
field has vanishing cohomology in degrees `≥ 2`. Freitag–Kiehl instead decompose `X` into its
connected components, identify `(𝐙/n𝐙)_X` with `μ_n` and use the vanishing of `H^2(X_j, μ_n)`
on an affine smooth connected curve; the route through torsion sheaves needs neither smoothness
nor that `n` be prime to the characteristic of `k`, so these hypotheses are dropped. An affine
smooth curve over `k` is affine, of finite type and of dimension one, hence satisfies the
hypotheses used here.

The vanishing theorem is stated on Mathlib's small étale site with coefficients in the universe
`u + 1`; it is read on `SmallEtale B X hX` through the sheaf equivalence of the two sites and the
comparison of cohomology across a change of coefficient universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 0A54](https://stacks.math.columbia.edu/tag/0A54)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallEtale

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- **Stacks Project, Tag 0A54, for sheaves killed by an integer.** Let `X` be an affine scheme of
finite type and of dimension at most one over an algebraically closed field `k`, and let `F` be
an abelian sheaf on the small étale site `SmallEtale B X hX` with `n • 𝟙 F = 0` for some `n ≥ 1`.
Then `H^q(X, F) = 0` for every `q ≥ 2`. -/
theorem subsingleton_sheafH_of_nsmul_id_eq_zero_of_isAffine [AlgebraicGeometry.IsAffine X]
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u}) {n : ℕ} (hn : 0 < n) (hF : n • 𝟙 F = 0)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (F.H q) := by
  let E := sheafEquiv B X hX AddCommGrpCat.{u}
  let G := E.functor.obj F
  have i1 : HasBinaryProducts (Sheaf (topology B X hX) AddCommGrpCat.{u}) := inferInstance
  have i2 : PreservesLimitsOfShape (Discrete WalkingPair) E.functor := inferInstance
  have i3 : E.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint E.functor
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  have hG : n • 𝟙 G = 0 := by
    rw [← E.functor.map_id, ← Functor.map_nsmul, hF, Functor.map_zero]
  have hu : HasExt.{u} (Sheaf (topology B X hX) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasExt _
  have : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  have hX' : HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.hasExt _
  have : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  have : HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasExt _
  have : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    etaleSheaves_hasSheafify_of_univLE.{u, u + 1} X
  have : X.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} :=
    (etaleUlift_properties.{u, u, u + 1} X).1
  have : (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesInjectiveObjects :=
    (etaleUlift_properties.{u, u, u + 1} X).2
  have : QuasiCompact f := inferInstance
  let S : Stacks.EtaleCohomology.TorsionSheafSituation.{u, u} :=
    { k := k
      X := X
      structureMorphism := f
      dimension_le_one := hdim
      F := (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj G
      isTorsion := torsionSheafProperty_sheafCompose_ulift_of_nsmul_id_eq_zero G hn hG }
  have hlift : Subsingleton (Sheaf.H.{u + 1}
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj G) q) :=
    S.isAffineVanishingAboveDegreeOne.{u + 1}
      (show _root_.AlgebraicGeometry.IsAffine X from inferInstance) q hq
  have hGq : Subsingleton (Sheaf.H.{u} G q) :=
    Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift.{u, u, u + 1, u + 1}
      X.smallEtaleTopology G q hlift
  have hFq : Subsingleton (Sheaf.H.{u} F q) :=
    (cohomologyAddEquivOfSmallEtale.{u} B X hX F q).toEquiv.subsingleton_congr.mpr hGq
  exact (Abelian.Ext.chgUniv.{u} : Sheaf.H.{w} F q ≃ Sheaf.H.{u} F q).subsingleton

/-- **Freitag–Kiehl, I.5: `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 1` on an affine curve.** Let `k` be an
algebraically closed field, `n ≥ 1` an integer and `X` an affine scheme of finite type and of
dimension at most one over `k` (for instance an affine smooth curve over `k`). Then the étale
cohomology of the constant sheaf `(𝐙/n𝐙)_X` on `SmallEtale B X hX` vanishes in every degree
`q > 1`. -/
@[weil "prop_fk105_affine_smooth_curve_cohomology_constant_vanish_q_gt_1"]
theorem subsingleton_sheafH_constantSheaf_zmod_of_isAffine_of_one_lt [AlgebraicGeometry.IsAffine X]
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})] {n : ℕ} (hn : 0 < n)
    (q : ℕ) (hq : 1 < q) :
    Subsingleton (((constantSheaf (topology B X hX) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod n)))).H q) :=
  subsingleton_sheafH_of_nsmul_id_eq_zero_of_isAffine f B hX hdim _ hn
    (nsmul_id_constantSheaf_zmod B hX n) q hq

/-- **Freitag–Kiehl, I.5: `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 1` on an affine curve**, for the
constant sheaf as the sheaf of locally constant `𝐙/n𝐙`-valued functions. -/
@[weil "prop_fk105_affine_smooth_curve_cohomology_constant_vanish_q_gt_1"]
theorem subsingleton_sheafH_locallyConstantSheafAb_zmod_of_isAffine
    [AlgebraicGeometry.IsAffine X]
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})] {n : ℕ} (hn : 0 < n)
    (q : ℕ) (hq : 1 < q) :
    Subsingleton
      ((SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B X hX (ZMod n)).H q) :=
  subsingleton_sheafH_of_nsmul_id_eq_zero_of_isAffine f B hX hdim _ hn
    (nsmul_id_locallyConstantSheafAbSmallEtale_zmod B hX n) q hq

/-- `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 1` on an affine curve `X` over an algebraically closed field
(`AlgebraicGeometry.IsCurve`, no smoothness needed). -/
theorem subsingleton_sheafH_constantSheaf_zmod_of_isCurve_of_isAffine [IsCurve k f]
    [AlgebraicGeometry.IsAffine X]
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})] {n : ℕ} (hn : 0 < n)
    (q : ℕ) (hq : 1 < q) :
    Subsingleton (((constantSheaf (topology B X hX) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod n)))).H q) :=
  subsingleton_sheafH_constantSheaf_zmod_of_isAffine_of_one_lt f B hX
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le hn q hq

end AlgebraicGeometry.SmallEtale
