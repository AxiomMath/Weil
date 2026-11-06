module

public import Weil.Attr
public import WeilFrontier.Defs.FieldTheory.AlgebraicClosure
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupTranscendenceDegreeOneVanishing

/-!
# Vanishing of the étale cohomology of `𝐆_m` over a function field in one variable

Let `K` be a function field in one variable over an algebraically closed constant field `k`.
Then the étale cohomology `H^q(K, 𝐆_m)` vanishes for every `q > 0`. This is Tsen's theorem read
through Galois cohomology: every finite extension of `K` is a `C₁` field, so has trivial Brauer
group, and this forces the vanishing in every positive degree.

## Main results

* `IsFunctionFieldOneVariable.subsingleton_sheafH_multiplicativeSheaf_spec`: the vanishing on
  the small étale site `(Spec K).Etale`.
* `IsFunctionFieldOneVariable.subsingleton_sheafH_multiplicativeSheaf_spec_smallEtale`: the
  same vanishing on the small étale site `SmallEtale B (Spec K) hK` of a big étale site `B`.

## Implementation notes

Only the transcendence degree of `K` over `k` is used: the result holds for every extension
`K / k` of transcendence degree one, finitely generated or not, whatever its constants
(`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one`). The
field `k` and `K` are taken in one universe `u`, and abelian sheaves on the small étale site of
`Spec K` have coefficients in `AddCommGrpCat.{u + 1}`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace IsFunctionFieldOneVariable

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **`H^q(K, 𝐆_m) = 0` for a function field in one variable over an algebraically closed
field.** Let `K` be a function field in one variable over an algebraically closed field `k`.
Then the étale cohomology of `Spec K` with coefficients in `𝐆_m` vanishes in every degree
`q > 0`. -/
@[weil "prop_ext_fk101_function_field_gm_cohomology_vanishes"]
theorem subsingleton_sheafH_multiplicativeSheaf_spec (k : Type u) [Field k] [IsAlgClosed k]
    (K : Type u) [Field K] [Algebra k K] [IsFunctionFieldOneVariable k K] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q) :=
  Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_spec_of_trdeg_eq_one k K
    (trdeg_eq_one (k := k) (K := K)) q hq

/-- **`H^q(K, 𝐆_m) = 0` for a function field in one variable over an algebraically closed
field**, on the small étale site `SmallEtale B (Spec K) hK` of a big étale site `B` containing
`Spec K`: the restriction of `𝐆_m` to it has vanishing cohomology in every degree `q > 0`. -/
@[weil "prop_ext_fk101_function_field_gm_cohomology_vanishes"]
theorem subsingleton_sheafH_multiplicativeSheaf_spec_smallEtale (k : Type u) [Field k]
    [IsAlgClosed k] (K : Type u) [Field K] [Algebra k K] [IsFunctionFieldOneVariable k K]
    (B : BigEtaleSite.{u}) (hK : B.Contains (Spec (.of K)))
    [HasExt.{u + 1} (Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1}
      ((SmallEtale.sheafEquiv B (Spec (.of K)) hK AddCommGrpCat.{u + 1}).inverse.obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K)))) q) := by
  have := subsingleton_sheafH_multiplicativeSheaf_spec k K q hq
  have : EnoughInjectives (Sheaf (SmallEtale.topology B (Spec (.of K)) hK)
      AddCommGrpCat.{u + 1}) :=
    (SmallEtale.sheafEquiv B (Spec (.of K)) hK AddCommGrpCat.{u + 1}).enoughInjectives_iff.2
      inferInstance
  exact (Stacks.Cohomology.DenseSubsite.hAddEquiv.{u + 1, u + 1}
    (SmallEtale.topology B (Spec (.of K)) hK) (Spec (.of K)).smallEtaleTopology
    (SmallEtale.toEtaleSite B (Spec (.of K)) hK)
    (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} (Spec (.of K))) q).symm.injective.subsingleton

end IsFunctionFieldOneVariable
