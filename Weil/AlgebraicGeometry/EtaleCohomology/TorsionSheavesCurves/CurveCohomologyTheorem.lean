module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.HasExtSmallEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import Weil.AlgebraicGeometry.EtaleCohomology.ClopenDecomposition
public import Weil.AlgebraicGeometry.Sites.Bridges.ConstantSheaf

/-!
# Vanishing of `H^q(X, A_X)` for `q > 1` on affine curves

Let `k` be an algebraically closed field, `X` an affine scheme of finite type over `k` of
dimension at most one, and `A` a finite abelian group. Then the étale cohomology
`H^q(X, A_X)` of the constant sheaf `A_X` vanishes for every `q > 1`.

This is the case of a constant sheaf of statement (2) of [Stacks, Tag 0A52] (Tag 0A54), which
holds for every torsion abelian sheaf on Mathlib's small étale site of `X`. The constant sheaf
`A_X` on the small étale site `SmallEtale B X hX` is transported to Mathlib's small étale site
(with coefficients raised to `AddCommGrpCat.{u + 1}`) without changing its cohomology, and it
stays torsion there: every section is killed by `|A|`.

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_H_locallyConstantSheafAbSmallEtale_of_isAffine`:
  `H^q(X, A_X) = 0` for `q > 1`.
* `AlgebraicGeometry.SmallEtale.torsionSheafProperty_sheafEquiv_functor_obj_ulift`: a sheaf on
  the small étale site whose sections are torsion gives a torsion sheaf on Mathlib's small étale
  site.

## Implementation notes

The source assumes moreover `X` smooth over `k` and `char k ∤ |A|`; neither is needed. The
source's proof reduces to `X` connected and to cyclic `A` and uses the computation of the
cohomology of `𝐙/n𝐙` on a smooth affine curve; here the general vanishing theorem for torsion
sheaves (Tag 0A54, which in the source rests on the same computation) is applied directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 0A54](https://stacks.math.columbia.edu/tag/0A54)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.SmallEtale

/-- An abelian sheaf `F` on the small étale site all of whose sections are torsion becomes, after
raising the coefficients to `AddCommGrpCat.{u + 1}`, a torsion sheaf on Mathlib's small étale
site. -/
theorem torsionSheafProperty_sheafEquiv_functor_obj_ulift (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (F : Sheaf (topology B X hX) AddCommGrpCat.{u})
    (hF : ∀ (V : SmallEtale B X hX) (x : F.obj.obj (op V)), ∃ n : ℕ, 0 < n ∧ n • x = 0) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((sheafEquiv B X hX AddCommGrpCat.{u + 1}).functor.obj
        ((sheafCompose (topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F)) := by
  let E := sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let L := sheafCompose (topology B X hX) AddCommGrpCat.uliftFunctor.{u + 1, u}
  refine Stacks.Torsion.isLocallyTorsion_of_isCoverDense X.smallEtaleTopology
    (toEtaleSite B X hX) _ fun V y => ?_
  have e : (E.functor.obj (L.obj F)).obj.obj (op ((toEtaleSite B X hX).obj V)) ≅
      (L.obj F).obj.obj (op V) :=
    ((sheafToPresheaf _ _).mapIso (E.unitIso.app (L.obj F))).symm.app (op V)
  refine Stacks.Torsion.exists_nsmul_eq_zero_of_iso e.symm (fun x => ?_) y
  obtain ⟨n, hn, hx⟩ := hF V x.down
  exact ⟨n, hn, ULift.ext _ _ hx⟩

/-- Let `k` be an algebraically closed field, `X` an affine scheme of finite type over `k` with
`dim X ≤ 1`, and `A` a finite abelian group. Then `H^q(X, A_X) = 0` for every `q > 1`. -/
@[weil "lem_fk105_affine_smooth_curve_finite_constant_sheaf_vanish_q_gt_1"]
theorem subsingleton_H_locallyConstantSheafAbSmallEtale_of_isAffine
    {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    [_root_.AlgebraicGeometry.IsAffine X] (hdim : topologicalKrullDim X ≤ 1)
    (A : Type u) [AddCommGroup A] [Finite A]
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{u})] (q : ℕ) (hq : 1 < q) :
    Subsingleton
      ((SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B X hX A).H q) := by
  let F := SmallNoetherianSeparatedEtale.locallyConstantSheafAbSmallEtale B X hX A
  have := AlgebraicGeometry.hasExt_sheaf_smallEtale_max.{0} X
  have hT := torsionSheafProperty_sheafEquiv_functor_obj_ulift B X hX F fun V x =>
    ⟨Nat.card A, Nat.card_pos, (LocallyConstant.ext fun _ => card_nsmul_eq_zero' :
      Nat.card A • (x : LocallyConstant ((SmallEtale.toScheme B X hX).obj V) A) = 0)⟩
  let S : Stacks.EtaleCohomology.TorsionSheafSituation.{u, 0} :=
    { k := k, X := X, structureMorphism := π, dimension_le_one := hdim, F := _, isTorsion := hT }
  exact (cohomologyAddEquivUlift F q).subsingleton_congr.mpr
    (Stacks.EtaleCohomology.TorsionSheafSituation.isAffineVanishingAboveDegreeOne.{u + 1, 0, u} S
      inferInstance q hq)

end AlgebraicGeometry.SmallEtale
