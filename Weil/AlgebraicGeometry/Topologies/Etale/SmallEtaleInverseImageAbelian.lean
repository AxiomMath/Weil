module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# The inverse image of abelian étale sheaves is exact

Let `f : T ⟶ S` be a morphism of schemes of a big étale site `B`. The inverse image
`f^* : Sh(S_ét, Ab) ⥤ Sh(T_ét, Ab)` is exact: it preserves finite limits and finite colimits.
Consequently it sends an exact sequence `G' ⟶ G ⟶ G''` of abelian sheaves on the small étale site
of `S` to an exact sequence of abelian sheaves on the small étale site of `T`.

Right exactness holds because `f^*` is a left adjoint (of the direct image). Left exactness holds
because `f^*` is the sheafification of the left Kan extension along the opposite of base change:
sheafification is exact, and the colimits computing the Kan extension are indexed by categories in
which every span is completed by a commutative square and every parallel pair is coequalized (the
small étale site of `S` has fibre products and equalizers, which base change preserves), so they
are exact in abelian groups.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_preservesFiniteLimits`,
  `AlgebraicGeometry.smallEtaleInverseImage_preservesFiniteColimits` — the two halves.
* `AlgebraicGeometry.smallEtaleInverseImage_exact` — `f^*` on abelian sheaves is exact.
* `CategoryTheory.ShortComplex.Exact.map_smallEtaleInverseImage` — `f^*` sends an exact
  sequence of abelian sheaves to an exact sequence.

## Implementation notes

The proof is the Kan-extension argument rather than the stalkwise one: exactness of the colimits
over the comma categories is the stalkwise argument carried out on sections. The coefficients are
`AddCommGrpCat.{u + 1}` for the scheme universe `u`: this is what makes the coefficient
category receive the colimits computing the Kan extension.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The inverse image of abelian sheaves on the small étale sites preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}) := by
  have : HasFiniteLimits (SmallEtale B S.obj S.property) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange B f)
        AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)) :=
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits _ _ _
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange B f)
      AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).symm

/-- The inverse image of abelian sheaves on the small étale sites preserves finite colimits,
being left adjoint to the direct image. -/
instance smallEtaleInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}) :=
  have := (smallEtaleInverseImageAdjunction B f AddCommGrpCat.{u + 1}).isLeftAdjoint
  inferInstance

/-- **The inverse image is exact.** For a morphism `f : T ⟶ S` of schemes of a big étale site,
the inverse image `f^*` from abelian sheaves on the small étale site of `S` to abelian sheaves on
the small étale site of `T` preserves finite limits and finite colimits. -/
@[weil "lem_fk102_inverse_image_exact"]
theorem smallEtaleInverseImage_exact :
    exactFunctor _ _ (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}) :=
  (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- **The inverse image preserves exact sequences.** If `G' ⟶ G ⟶ G''` is an exact sequence of
abelian sheaves on the small étale site of `S`, then `f^* G' ⟶ f^* G ⟶ f^* G''` is exact. -/
@[weil "lem_fk102_inverse_image_exact"]
theorem _root_.CategoryTheory.ShortComplex.Exact.map_smallEtaleInverseImage
    {X : ShortComplex (Sheaf (SmallEtale.topology B S.obj S.property)
      AddCommGrpCat.{u + 1})} (hX : X.Exact) :
    (X.map (smallEtaleInverseImage B f AddCommGrpCat.{u + 1})).Exact :=
  hX.map _

end AlgebraicGeometry

end
