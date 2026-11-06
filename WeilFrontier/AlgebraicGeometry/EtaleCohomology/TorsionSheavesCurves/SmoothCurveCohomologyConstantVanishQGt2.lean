module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NonseparatedCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-!
# Vanishing of `H^q(X, (𝐙/n𝐙)_X)` for `q > 2` on a curve

Let `k` be an algebraically closed field and `X` a scheme of finite type over `k` of dimension
at most one (for instance a smooth curve over `k`). For every abelian sheaf `F` on the small
étale site of `X` killed by some integer `n ≥ 1`, and in particular for the constant sheaf
`(𝐙/n𝐙)_X`, the étale cohomology `H^q(X, F)` vanishes for every `q > 2`.

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_of_nsmul_id_eq_zero`: `H^q(X, F) = 0` for
  `q ≥ 3` and `F` an abelian sheaf on `SmallEtale B X hX` with `n • 𝟙 F = 0`, `n ≥ 1`.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_constantSheaf_zmod_of_two_lt`:
  `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 2`, the constant sheaf being the sheafification of the
  constant presheaf.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_locallyConstantSheafAb_zmod_of_two_lt`:
  the same for the constant sheaf as the sheaf of locally constant `𝐙/n𝐙`-valued functions.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_constantSheaf_zmod_of_isCurve`: the same on
  a curve in the sense of `AlgebraicGeometry.IsCurve`.

## Implementation notes

The proof is that of [Stacks, Tag 03RT]: `(𝐙/n𝐙)_X` is a torsion sheaf, and every torsion sheaf
on a scheme of finite type and of dimension at most one over an algebraically closed field has
vanishing cohomology in degrees `≥ 3`. Freitag–Kiehl instead identify `(𝐙/n𝐙)_X` with `μ_n`
(`AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot`) and use the Kummer
sequence; the route through torsion sheaves needs neither smoothness nor that `n` be prime to
the characteristic of `k`, so these hypotheses are dropped. A smooth curve over `k` is of finite
type and of dimension one, hence satisfies the hypotheses used here
(`AlgebraicGeometry.SmallEtale.subsingleton_sheafH_constantSheaf_zmod_of_isCurve`).

The vanishing theorem is stated on Mathlib's small étale site with coefficients in the object
universe; it is read on `SmallEtale B X hX` through the sheaf equivalence of the two sites and
the comparison of cohomology across a change of coefficient universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RT](https://stacks.math.columbia.edu/tag/03RT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace CategoryTheory.Sheaf

/-- Every section of an abelian sheaf killed by `n` is killed by `n`. -/
theorem nsmul_eq_zero_of_nsmul_id_eq_zero {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {G : Sheaf J AddCommGrpCat.{w}} {n : ℕ} (hG : n • 𝟙 G = 0)
    (U : Cᵒᵖ) (y : G.obj.obj U) :
    n • y = 0 := by
  have h := congrArg (fun φ : G ⟶ G => φ.hom.app U y) hG
  have e : (n • 𝟙 G).hom = n • 𝟙 G.obj := (sheafToPresheaf J AddCommGrpCat.{w}).map_nsmul
  simp only at h
  rw [e, NatTrans.app_nsmul] at h
  change (n • 𝟙 (G.obj.obj U)).hom y = (0 : G.obj.obj U ⟶ G.obj.obj U).hom y at h
  simpa using h

/-- An abelian sheaf all of whose sections are killed by `n` is killed by `n`. -/
theorem nsmul_id_eq_zero_of_forall_nsmul_eq_zero {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {G : Sheaf J AddCommGrpCat.{w}} {n : ℕ}
    (hG : ∀ (U : Cᵒᵖ) (y : G.obj.obj U), n • y = 0) : n • 𝟙 G = 0 := by
  apply Sheaf.hom_ext
  ext U y
  have e : (n • 𝟙 G).hom = n • 𝟙 G.obj := (sheafToPresheaf J AddCommGrpCat.{w}).map_nsmul
  rw [e, NatTrans.app_nsmul]
  change (n • 𝟙 (G.obj.obj U)).hom y = (0 : G.obj.obj U ⟶ G.obj.obj U).hom y
  simpa using hG U y

end CategoryTheory.Sheaf

namespace AddCommGrpCat

/-- The abelian group `𝐙/n𝐙` is killed by `n`. -/
theorem nsmul_id_of_ulift_zmod (n : ℕ) :
    n • 𝟙 (AddCommGrpCat.of (ULift.{u} (ZMod n))) = 0 := by
  ext x
  simp

end AddCommGrpCat

namespace AlgebraicGeometry.SmallEtale

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (B : BigEtaleSite.{u}) (hX : B.Contains X)

/-- The coefficient-universe lift of a sheaf on Mathlib's small étale site killed by `n ≥ 1` is
a torsion sheaf. -/
theorem torsionSheafProperty_sheafCompose_ulift_of_nsmul_id_eq_zero
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {n : ℕ} (hn : 0 < n)
    (hG : n • 𝟙 G = 0) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj G) := by
  intro U x
  refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ => ⟨n, hn, ?_⟩⟩
  apply ULift.ext
  exact Sheaf.nsmul_eq_zero_of_nsmul_id_eq_zero hG (op V) _

/-- **Stacks Project, Tag 03RT, for sheaves killed by an integer.** Let `X` be a scheme of finite
type and of dimension at most one over an algebraically closed field `k`, and let `F` be an
abelian sheaf on the small étale site `SmallEtale B X hX` with `n • 𝟙 F = 0` for some `n ≥ 1`.
Then `H^q(X, F) = 0` for every `q ≥ 3`. -/
theorem subsingleton_sheafH_of_nsmul_id_eq_zero [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{u}) {n : ℕ} (hn : 0 < n) (hF : n • 𝟙 F = 0)
    (q : ℕ) (hq : 3 ≤ q) : Subsingleton (F.H q) := by
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
  have hlift : Subsingleton (Sheaf.H.{u + 1}
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj G) q) :=
    Stacks.EtaleCohomology.subsingleton_sheafH_of_three_le.{u + 1, u, u} f hdim _
      (torsionSheafProperty_sheafCompose_ulift_of_nsmul_id_eq_zero G hn hG) q hq
  have hGq : Subsingleton (Sheaf.H.{u} G q) :=
    Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift.{u, u, u + 1, u + 1}
      X.smallEtaleTopology G q hlift
  have hFq : Subsingleton (Sheaf.H.{u} F q) :=
    (cohomologyAddEquivOfSmallEtale.{u} B X hX F q).toEquiv.subsingleton_congr.mpr hGq
  exact (Abelian.Ext.chgUniv.{u} : Sheaf.H.{w} F q ≃ Sheaf.H.{u} F q).subsingleton

/-- The constant sheaf `(𝐙/n𝐙)_X` is killed by `n`. -/
theorem nsmul_id_constantSheaf_zmod (n : ℕ) :
    n • 𝟙 ((constantSheaf (topology B X hX) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod n)))) = 0 := by
  rw [← (constantSheaf (topology B X hX) AddCommGrpCat.{u}).map_id, ← Functor.map_nsmul,
    AddCommGrpCat.nsmul_id_of_ulift_zmod, Functor.map_zero]

/-- The sheaf of locally constant `𝐙/n𝐙`-valued functions is killed by `n`. -/
theorem nsmul_id_locallyConstantSheafAbSmallEtale_zmod (n : ℕ) :
    n • 𝟙 (SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B X hX (ZMod n)) =
      0 := by
  refine Sheaf.nsmul_id_eq_zero_of_forall_nsmul_eq_zero fun U y => ?_
  let y' : LocallyConstant ((SmallEtale.toScheme B X hX).obj U.unop) (ZMod n) := y
  change n • y' = 0
  ext z
  have h := congrFun (map_nsmul LocallyConstant.coeFnAddMonoidHom n y') z
  simp only [LocallyConstant.coeFnAddMonoidHom_apply, Pi.smul_apply] at h
  rw [h]
  simp

/-- **Freitag–Kiehl, I.5: `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 2` on a curve.** Let `k` be an
algebraically closed field, `n ≥ 1` an integer and `X` a scheme of finite type and of dimension
at most one over `k` (for instance a smooth curve over `k`). Then the étale cohomology of the
constant sheaf `(𝐙/n𝐙)_X` on `SmallEtale B X hX` vanishes in every degree `q > 2`. -/
@[weil "prop_fk105_smooth_curve_cohomology_constant_vanish_q_gt_2"]
theorem subsingleton_sheafH_constantSheaf_zmod_of_two_lt [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})] {n : ℕ} (hn : 0 < n)
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (((constantSheaf (topology B X hX) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod n)))).H q) :=
  subsingleton_sheafH_of_nsmul_id_eq_zero f B hX hdim _ hn (nsmul_id_constantSheaf_zmod B hX n)
    q hq

/-- **Freitag–Kiehl, I.5: `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 2` on a curve**, for the constant
sheaf as the sheaf of locally constant `𝐙/n𝐙`-valued functions. -/
@[weil "prop_fk105_smooth_curve_cohomology_constant_vanish_q_gt_2"]
theorem subsingleton_sheafH_locallyConstantSheafAb_zmod_of_two_lt [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})] {n : ℕ} (hn : 0 < n)
    (q : ℕ) (hq : 2 < q) :
    Subsingleton
      ((SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B X hX (ZMod n)).H q) :=
  subsingleton_sheafH_of_nsmul_id_eq_zero f B hX hdim _ hn
    (nsmul_id_locallyConstantSheafAbSmallEtale_zmod B hX n) q hq

/-- `H^q(X, (𝐙/n𝐙)_X) = 0` for `q > 2` on a curve `X` over an algebraically closed field
(`AlgebraicGeometry.IsCurve`, no smoothness needed). -/
theorem subsingleton_sheafH_constantSheaf_zmod_of_isCurve [IsCurve k f]
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})] {n : ℕ} (hn : 0 < n)
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (((constantSheaf (topology B X hX) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod n)))).H q) :=
  subsingleton_sheafH_constantSheaf_zmod_of_two_lt f B hX
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le hn q hq

end AlgebraicGeometry.SmallEtale
