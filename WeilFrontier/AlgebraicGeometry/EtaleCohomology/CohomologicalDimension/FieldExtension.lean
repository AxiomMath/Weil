module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SeparablyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionSiteTransfer
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Function fields in one variable have cohomological dimension at most one

Let `k` be a separably closed field and `K` an extension field of `k` of transcendence degree at
most one, for instance a function field in one variable over an algebraically closed field. Then
`H^q(Spec K, 𝓖) = 0` for every torsion abelian sheaf `𝓖` on the small étale site of `Spec K` and
every `q ≥ 2`.

The proof is Stacks 0F0T: `cd(K) ≤ cd(k) + trdeg_k K ≤ 0 + 1`, the cohomological dimension of a
separably closed field being zero.

## Main results

* `AlgebraicGeometry.Scheme.subsingleton_H_spec_of_trdeg_le_one`: the statement on Mathlib's
  small étale site `(Spec K).smallEtaleTopology`.
* `AlgebraicGeometry.SmallEtale.subsingleton_H_spec_of_trdeg_le_one`: the statement on the
  bounded small étale site `AlgebraicGeometry.SmallEtale.topology`, for the torsion sheaves
  `AlgebraicGeometry.SmallEtale.IsTorsionSheaf`.

## Implementation notes

The source proves the statement through Tsen's theorem (`H²(L, 𝔾ₘ) = 0` for every finite
separable extension `L` of `K`) and the criterion "`H²(L, 𝔾ₘ) = 0` for all finite separable `L`
implies `cd(K) ≤ 1`". We instead use the bound `cd(L) ≤ cd(K) + trdeg_K(L)` for a field extension
`L/K`, which gives the same conclusion directly. The hypotheses are weaker than the source's: `k`
need only be separably closed, and `K` need not be finitely generated over `k`, only of
transcendence degree at most one.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], Lemma I.5
* [Stacks Project, Tag 0F0T](https://stacks.math.columbia.edu/tag/0F0T)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The étale cohomological dimension of an extension of transcendence degree at most one of a
separably closed field is at most one. -/
theorem etaleCohomologicalDimension_spec_le_one_of_trdeg_le_one (k K : Type u) [Field k]
    [IsSepClosed k] [Field K] [Algebra k K] (h : Algebra.trdeg k K ≤ 1) :
    etaleCohomologicalDimension (Spec (.of K)) ≤ 1 := by
  have h1 := etaleCohomologicalDimension_spec_le_add_trdeg k K
  have h0 := etaleCohomologicalDimension_spec_le_zero_of_isSepClosed k
  have ht : (Algebra.trdeg k K).toENat ≤ 1 := by
    simpa using Cardinal.toENat.monotone' h
  exact h1.trans (by simpa using add_le_add h0 ht)

/-- **Function fields in one variable have cohomological dimension at most one.** Let `k` be a
separably closed field and `K` an extension of `k` of transcendence degree at most one. Then
`H^q(Spec K, 𝓖) = 0` for every torsion abelian sheaf `𝓖` on the small étale site of `Spec K` and
every `q ≥ 2`. -/
@[weil "lem_fk105_function_field_cd_le_1_torsion"]
theorem subsingleton_H_spec_of_trdeg_le_one (k K : Type u) [Field k] [IsSepClosed k] [Field K]
    [Algebra k K] (h : Algebra.trdeg k K ≤ 1)
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) :=
  (etaleCohomologicalDimension_le_iff _ 1).1
    (etaleCohomologicalDimension_spec_le_one_of_trdeg_le_one k K h) F hF q
    (by exact_mod_cast hq)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SmallEtale

/-- **Function fields in one variable have cohomological dimension at most one**, on the bounded
small étale site. Let `k` be a separably closed field and `K` an extension of `k` of
transcendence degree at most one. Then `H^q(Spec K, 𝓖) = 0` for every torsion abelian sheaf `𝓖`
on the small étale site of `Spec K` and every `q ≥ 2`. -/
@[weil "lem_fk105_function_field_cd_le_1_torsion"]
theorem subsingleton_H_spec_of_trdeg_le_one (B : BigEtaleSite.{u}) (k K : Type u) [Field k]
    [IsSepClosed k] [Field K] [Algebra k K] (h : Algebra.trdeg k K ≤ 1)
    (hS : B.Contains (Spec (.of K)))
    [HasExt.{u + 1} (Sheaf (topology B (Spec (.of K)) hS) AddCommGrpCat.{u + 1})]
    (F : Sheaf (topology B (Spec (.of K)) hS) AddCommGrpCat.{u + 1})
    (hF : IsTorsionSheaf B (Spec (.of K)) hS F) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F q) := by
  let E := sheafEquiv B (Spec (.of K)) hS AddCommGrpCat.{u + 1}
  let G := E.functor.obj F
  have hG : Stacks.Torsion.torsionSheafProperty _ G :=
    (torsionSheafProperty_toEtaleSite_iff B (Spec (.of K)) hS G).1
      ((Stacks.Torsion.torsionSheafProperty _).prop_of_iso (E.unitIso.app F) hF)
  have := Scheme.subsingleton_H_spec_of_trdeg_le_one k K h G hG q hq
  let e₁ := Stacks.Cohomology.DenseSubsite.hAddEquiv (topology B (Spec (.of K)) hS)
    (Spec (.of K)).smallEtaleTopology (toEtaleSite B (Spec (.of K)) hS) G q
  let e₂ := ((Sheaf.functorH.{u + 1, u + 1} (topology B (Spec (.of K)) hS) q).mapIso
    (E.unitIso.app F)).addCommGroupIsoToAddEquiv
  exact (e₂.trans e₁.symm).toEquiv.subsingleton

end AlgebraicGeometry.SmallEtale
