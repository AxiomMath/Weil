module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion

/-!
# Étale cohomology of constructible sheaves on affine curves vanishes in degrees at least two

Let `k` be a separably closed field, `X` an affine `k`-scheme of finite type with `dim X ≤ 1` and
`𝓕` a constructible abelian sheaf on `X_ét`. Then `H^q(X, 𝓕) = 0` for every `q ≥ 2`.

A constructible sheaf is a torsion sheaf, and an affine scheme of finite type and dimension at
most one over a separably closed field has étale cohomological dimension at most one
([Stacks, Tag 03SC], [Stacks, Tag 0F0S]): the cohomology of every torsion sheaf vanishes above
degree one.

## Main results

* `AlgebraicGeometry.IsConstructibleAbelianSheaf.subsingleton_sheafH_of_two_le_of_isAffine`:
  `H^q(X, 𝓕) = 0` for `q ≥ 2`, `X` affine, of finite type and of dimension at most one over a
  separably closed field, and `𝓕` constructible.

## Implementation notes

Sheaves live on the small étale site `SmallEtale B X hX` of a big étale site `B`, with
coefficients `AddCommGrpCat.{u + 1}`, the coefficients of constructible abelian sheaves. The
cohomological dimension is defined on Mathlib's small étale site `X.smallEtaleTopology`, and
cohomology is moved across the dense subsite inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite`.

Freitag and Kiehl assume in addition that the orders of the sections of `𝓕` are prime to the
characteristic of `k`, and argue by reduction to a smooth curve over an algebraically closed
field; neither the hypothesis nor the reduction is needed here. Finite type is weakened to
locally of finite type, which is the same for an affine scheme.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0F0S](https://stacks.math.columbia.edu/tag/0F0S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- The étale cohomological dimension bounds the cohomology of a torsion sheaf on the small étale
site `SmallEtale B X hX`. -/
private theorem SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_etaleCohomologicalDimension_lt
    (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (hF : SmallEtale.IsTorsionSheaf B X hX F) (b : ℕ)
    (hb : Scheme.etaleCohomologicalDimension X < b) :
    Subsingleton (Sheaf.H.{w} F b) := by
  have h1 : HasExt.{u + 1} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
    inferInstance
  refine @Equiv.subsingleton _ _ (Abelian.Ext.chgUniv.{u + 1} :
    Sheaf.H.{w} F b ≃ Sheaf.H.{u + 1} F b) ?_
  let E := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let e₁ : Sheaf.H.{u + 1} F b ≃+ Sheaf.H.{u + 1} (E.inverse.obj (E.functor.obj F)) b :=
    ((Sheaf.functorH.{u + 1, u + 1} (SmallEtale.topology B X hX) b).mapIso
      (E.unitIso.app F)).addCommGroupIsoToAddEquiv
  let e₂ : Sheaf.H.{u + 1} (E.functor.obj F) b ≃+
      Sheaf.H.{u + 1} (E.inverse.obj (E.functor.obj F)) b :=
    Stacks.Cohomology.DenseSubsite.hAddEquiv (SmallEtale.topology B X hX) X.smallEtaleTopology
      (SmallEtale.toEtaleSite B X hX) (E.functor.obj F) b
  let e : Sheaf.H.{u + 1} F b ≃+ Sheaf.H.{u + 1} (E.functor.obj F) b := e₁.trans e₂.symm
  refine @Equiv.subsingleton _ _ e.toEquiv ?_
  have hFM : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology (E.functor.obj F) :=
    Stacks.EtaleCohomology.torsionSheafProperty_of_pushforward _ _ (SmallEtale.toEtaleSite B X hX)
      _ ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso (E.unitIso.app F) hF)
  exact Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension X _ hFM b hb

section Constructible

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Freitag–Kiehl I.5.** Let `k` be a separably closed field, `X` an affine `k`-scheme of finite
type with `dim X ≤ 1`, and `𝓕` a constructible abelian sheaf on `X_ét`. Then `H^q(X, 𝓕) = 0` for
every `q ≥ 2`. -/
@[weil "prop_fk105_affine_curve_constructible_h_ge_2_vanish"]
theorem IsConstructibleAbelianSheaf.subsingleton_sheafH_of_two_le_of_isAffine
    {k : Type u} [Field k] [IsSepClosed k] (X : B.Scheme) [IsAffine X.obj]
    (π : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType π] (hdim : topologicalKrullDim X.obj ≤ 1)
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} F q) := by
  refine SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_etaleCohomologicalDimension_lt B
    X.property F (isTorsionSheaf_of_isConstructibleAbelianSheaf B X F hF) q ?_
  refine (Scheme.etaleCohomologicalDimension_le_one_of_isSepClosed π hdim).trans_lt ?_
  exact_mod_cast hq

end Constructible

end AlgebraicGeometry
