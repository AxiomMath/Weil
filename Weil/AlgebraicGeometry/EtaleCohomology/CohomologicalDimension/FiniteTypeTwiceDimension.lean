module

public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteTypeTwiceDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionStalkCriterion

/-!
# Étale cohomology of constructible sheaves on curves vanishes in degrees at least three

Let `k` be a separably closed field, `X` a `k`-scheme of finite type with `dim X ≤ 1` and `𝓕` a
constructible abelian sheaf on `X_ét`. Then `H^q(X, 𝓕) = 0` for every `q ≥ 3`.

A constructible sheaf is a torsion sheaf, and for a torsion sheaf `𝓕` on a quasi-compact scheme
`X` locally of finite type over a field `K` with `dim X ≤ n` the groups `H^b(X, 𝓕)` vanish for
`b > 2n + cd(K)` ([Stacks, Tag 0F0W]); a separably closed field has cohomological dimension
zero.

## Main results

* `AlgebraicGeometry.SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_topologicalKrullDim_le`:
  `H^b(X, 𝓕) = 0` for a torsion sheaf `𝓕` on the small étale site of `X` and
  `b > 2 dim X + cd(K)`.
* `AlgebraicGeometry.IsConstructibleAbelianSheaf.subsingleton_sheafH_of_three_le`:
  `H^q(X, 𝓕) = 0` for `q ≥ 3`, `X` of finite type and of dimension at most one over a separably
  closed field and `𝓕` constructible.

## Implementation notes

Sheaves live on the small étale site `SmallEtale B X hX` of a big étale site `B`, with
coefficients `AddCommGrpCat.{u + 1}`, the coefficients of constructible abelian sheaves. The
vanishing bound is proved on Mathlib's small étale site `X.smallEtaleTopology`, and cohomology is
moved across the dense subsite inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite`.

Freitag and Kiehl assume in addition that the orders of the sections of `𝓕` are prime to the
characteristic of `k`, and argue by reduction to a smooth curve over an algebraically closed
field and the direct image from the generic point; neither the hypothesis nor the reduction is
needed here. No separatedness of `X` is assumed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
* [Stacks Project, Tag 03RT](https://stacks.math.columbia.edu/tag/03RT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **Étale cohomology of a torsion sheaf vanishes above twice the dimension.** Let `X` be a
quasi-compact scheme locally of finite type over a field `K`, with `dim X ≤ n`, and `𝓕` a torsion
abelian sheaf on the small étale site of `X`. Then `H^b(X, 𝓕) = 0` for every `b > 2n + cd(K)`. -/
theorem SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_topologicalKrullDim_le
    (K : Type u) [Field K] (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] [QuasiCompact π] (n : ℕ)
    (hdim : topologicalKrullDim X ≤ n)
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})
    (hF : SmallEtale.IsTorsionSheaf B X hX F) (b : ℕ)
    (hb : ((2 * n : ℕ) : ℕ∞) + Scheme.etaleCohomologicalDimension (Spec (.of K)) < b) :
    Subsingleton (Sheaf.H.{w} F b) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
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
  exact subsingleton_H_of_topologicalKrullDim_le K n X π hdim _ hFM b hb

section Constructible

variable (B : BigEtaleSite.{u})
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Freitag–Kiehl I.5.** Let `k` be a separably closed field, `X` a `k`-scheme of finite type
with `dim X ≤ 1`, and `𝓕` a constructible abelian sheaf on `X_ét`. Then `H^q(X, 𝓕) = 0` for every
`q ≥ 3`. -/
@[weil "prop_fk105_curve_constructible_cohomology_vanish_ge_3"]
theorem IsConstructibleAbelianSheaf.subsingleton_sheafH_of_three_le
    {k : Type u} [Field k] [IsSepClosed k] (X : B.Scheme) (π : X.obj ⟶ Spec (.of k))
    [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim X.obj ≤ 1)
    [HasExt.{w} (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) (q : ℕ) (hq : 3 ≤ q) :
    Subsingleton (Sheaf.H.{w} F q) := by
  refine SmallEtale.subsingleton_sheafH_of_isTorsionSheaf_of_topologicalKrullDim_le k B
    X.property π 1 (by exact_mod_cast hdim) F
    (isTorsionSheaf_of_isConstructibleAbelianSheaf B X F hF) q ?_
  have h0 := Scheme.etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k
  rw [nonpos_iff_eq_zero.mp h0, add_zero]
  exact_mod_cast hq

end Constructible

end AlgebraicGeometry
