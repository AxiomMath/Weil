module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.HasExtSmallEtale
public import Weil.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericDirectImageCohomologyVanishGe3
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.NonseparatedCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.AlgebraicGeometry.FunctionField
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Torsion cohomology of curves above degree two, and the generic direct image

Let `k` be an algebraically closed field and `X` a scheme of finite type over `k` of dimension
at most one. For every torsion abelian sheaf `F` on the small étale site of `X`,
`H^q(X, F) = 0` for every `q ≥ 3` (Stacks, Tag 03RT). We state this on the bounded small étale
site `AlgebraicGeometry.SmallEtale` of a big étale site, transporting the Stacks result, which
is stated on Mathlib's small étale site, along the comparison of the two sites.

Freitag and Kiehl reduce this vanishing, for an integral curve `X` with generic point
`η : Spec K ⟶ X`, to the vanishing of `H^q(X, η_* η^* F)` for `q ≥ 3`: the kernel and cokernel of
the unit `F ⟶ η_* η^* F` are torsion sheaves with zero generic stalk, hence acyclic, so
`H^q(X, F) ≅ H^q(X, η_* η^* F)` for `q ≥ 3`. We record that implication; with Tag 03RT its
conclusion holds without the hypothesis.

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_three_le`: for a torsion
  sheaf `F` on the small étale site of a scheme of finite type and dimension at most one over an
  algebraically closed field, `H^q(X, F) = 0` for `q ≥ 3`.
* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_of_subsingleton_sheafH_genericPoint`: if
  `H^q(X, η_* η^* F) = 0` for every `q ≥ 3`, then `H^q(X, F) = 0` for every `q ≥ 3`.

## Implementation notes

The hypotheses on `X` are those of Tag 03RT: `X ⟶ Spec k` locally of finite type and
quasi-compact, and `topologicalKrullDim X ≤ 1`; an integral curve over `k` satisfies them.
The coefficients are `AddCommGrpCat.{max (u + 1) v}`, the universe in which the inverse image
`AlgebraicGeometry.smallEtaleInverseImage` exists, and the `Ext` universe `w` is arbitrary.
Both `Spec K` and `X` must lie in the big étale site for `η_*` and `η^*` to be formed there.

The proof does not follow the reduction: the conclusion is Tag 03RT, which holds for every
torsion sheaf, so the hypothesis on `η_* η^* F` is not used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RT](https://stacks.math.columbia.edu/tag/03RT)
-/

@[expose] public section

open CategoryTheory Stacks.EtaleCohomology

universe w v u

namespace AlgebraicGeometry

namespace SmallEtale

variable {k : Type u} [Field k] [IsAlgClosed k] (B : BigEtaleSite.{u}) {X : Scheme.{u}}
  (hX : B.Contains X)

/-- **Tag 03RT on the bounded small étale site.** Let `k` be an algebraically closed field and
`X` a scheme locally of finite type and quasi-compact over `k`, of dimension at most one. For
every torsion abelian sheaf `F` on the small étale site of `X`, `H^q(X, F) = 0` for `q ≥ 3`. -/
theorem subsingleton_sheafH_of_isTorsionSheaf_of_three_le (π : X ⟶ Spec (.of k))
    [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v})
    (hF : IsTorsionSheaf B X hX F) (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (F.H q) := by
  let E := sheafEquiv B X hX AddCommGrpCat.{max (u + 1) v}
  have : IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
  let _ : HasExt.{max (u + 1) v} (Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v}) :=
    IsGrothendieckAbelian.hasExt _
  let _ : HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    AlgebraicGeometry.hasExt_sheaf_smallEtale_max.{v} X
  have hFM : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology (E.functor.obj F) :=
    (torsionSheafProperty_toEtaleSite_iff B X hX _).mp
      ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso (E.unitIso.app F) hF)
  have h1 : Subsingleton (Sheaf.H.{max (u + 1) v} (E.functor.obj F) q) :=
    subsingleton_sheafH_of_three_le.{max (u + 1) v, v} π hdim _ hFM q hq
  have h2 : Subsingleton (Sheaf.H.{max (u + 1) v} (E.inverse.obj (E.functor.obj F)) q) :=
    (Stacks.Cohomology.DenseSubsite.hAddEquiv.{max (u + 1) v} (topology B X hX)
      X.smallEtaleTopology (toEtaleSite B X hX) (E.functor.obj F) q).symm.toEquiv.subsingleton
  have h3 : Subsingleton (Sheaf.H.{max (u + 1) v} F q) :=
    @Equiv.subsingleton _ _ ((Sheaf.functorH.{max (u + 1) v, max (u + 1) v} (topology B X hX)
      q).mapIso (E.unitIso.app F)).addCommGroupIsoToAddEquiv.toEquiv h2
  exact @Equiv.subsingleton (Sheaf.H.{w} F q) _ Abelian.Ext.chgUniv h3

/-- **Reduction of the vanishing to the generic direct image.** Let `k` be an algebraically
closed field, `X` an integral scheme of finite type over `k` of dimension at most one (for
instance an integral curve), `η : Spec K ⟶ X` its generic point, and `F` a torsion sheaf on the
small étale site of `X`. If `H^q(X, η_* η^* F) = 0` for every `q ≥ 3`, then `H^q(X, F) = 0` for
every `q ≥ 3`. -/
@[weil "lem_fk105_reduce_vanishing_to_generic_direct_image"]
theorem subsingleton_sheafH_of_subsingleton_sheafH_genericPoint [IsIntegral X]
    (hK : B.Contains (Spec X.functionField)) (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π]
    [QuasiCompact π] (hdim : topologicalKrullDim X ≤ 1)
    [HasExt.{w} (Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf (topology B X hX) AddCommGrpCat.{max (u + 1) v})
    (hF : IsTorsionSheaf B X hX F)
    (_hη : ∀ q, 3 ≤ q → Subsingleton (Sheaf.H.{w}
      ((B.smallPushforward (BigEtaleSite.genericPointHom X B hX hK)
          AddCommGrpCat.{max (u + 1) v}).obj
        ((smallEtaleInverseImage B (BigEtaleSite.genericPointHom X B hX hK)
          AddCommGrpCat.{max (u + 1) v}).obj F)) q))
    (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (F.H q) :=
  subsingleton_sheafH_of_isTorsionSheaf_of_three_le B hX π hdim F hF q hq

end SmallEtale

end AlgebraicGeometry
