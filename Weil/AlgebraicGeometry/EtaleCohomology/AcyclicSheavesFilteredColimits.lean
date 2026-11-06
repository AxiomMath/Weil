module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AcyclicSheavesFilteredColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# Filtered colimits of injective abelian étale sheaves are acyclic

Let `X` be a quasi-compact and quasi-separated scheme (for instance a noetherian separated
scheme) and `(𝒥_ν)` a filtered system of injective abelian sheaves on the small étale site of
`X`, with colimit `𝒥`. Then `Hⁱ(X, 𝒥) = 0` for every `i > 0`, where `Hⁱ(X, -)` is the `i`-th
right derived functor of the global sections functor `Γ(X, -)`.

An injective object is acyclic for `Γ(X, -)`, and a filtered colimit of `Γ(X, -)`-acyclic
sheaves is `Γ(X, -)`-acyclic because étale cohomology of a quasi-compact quasi-separated scheme
commutes with filtered colimits (Stacks 03Q5).

## Main results

* `AlgebraicGeometry.isZero_rightDerived_Γ_colimit_of_injective`: `Hⁱ(X, colim 𝒥_ν) = 0` for
  `i > 0` when every `𝒥_ν` is injective.

## Implementation notes

The statement is on Mathlib's small étale site `X.smallEtaleTopology`, with coefficients in
`AddCommGrpCat.{max (u + 1) v}` and index categories in `Type (max (u + 1) v)`, the setting of
Stacks 03Q5 as used here. The hypothesis "noetherian separated" is generalized to quasi-compact
and quasi-separated. The proof does not pass through Čech cohomology and Cartan's lemma: it
uses that higher cohomology commutes with filtered colimits on a quasi-compact quasi-separated
scheme.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FK88]
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Scheme.SmallEtaleColimits

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

universe v u

namespace AlgebraicGeometry

/-- **A filtered colimit of injective abelian étale sheaves is acyclic.** On a quasi-compact
quasi-separated scheme `X`, if `𝒥 : I ⥤ Sh(X_ét, Ab)` is a filtered diagram of injective
sheaves, then `Hⁱ(X, colim 𝒥) = 0` for every `i > 0`. -/
@[weil "lem_fk104_filtered_colimit_injectives_acyclic"]
theorem isZero_rightDerived_Γ_colimit_of_injective (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (𝒥 : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    [∀ i, Injective (𝒥.obj i)] (n : ℕ) (hn : 0 < n) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived n).obj
      (colimit 𝒥)) :=
  (CategoryTheory.rightAcyclic_iff_isZero_rightDerived _ _).1
    (Stacks.EtaleCohomology.rightAcyclic_Γ_colimit_smallEtale.{v} X 𝒥
      fun _ ↦ Functor.rightAcyclic_of_injective _ _) n hn

end AlgebraicGeometry
