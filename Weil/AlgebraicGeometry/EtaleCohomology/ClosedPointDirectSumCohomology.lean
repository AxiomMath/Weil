module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheaf
public import Weil.AlgebraicGeometry.Sites.EtaleComparison

/-!
# Étale cohomology of a skyscraper sheaf at a closed point

Let `X` be a scheme locally of finite type over an algebraically closed field `k`, let `x` be a
closed point of `X`, regarded as the `k`-point `x : Spec k ⟶ X`
(`AlgebraicGeometry.pointOfClosedPoint`), and let `𝒢` be an abelian sheaf on the small étale
site of `Spec k`. Then `H^i(X, x_* 𝒢) = 0` for every `i > 0`.

More generally, for an integral morphism `y : Spec K ⟶ X` with `K` separably closed, the direct
image `y_*` does not change étale cohomology, and every abelian sheaf on `Spec K` is acyclic,
`K` being a strictly henselian local ring. The `k`-point attached to a closed point is the
composite of an isomorphism `Spec k ≅ Spec κ(x)` with the closed immersion
`Spec κ(x) ⟶ X`, hence finite, hence integral.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_pushforward_of_isSepClosed` — positive-degree
  cohomology of `y_* 𝒢` vanishes for `y : Spec K ⟶ X` integral and `K` separably closed.
* `Stacks.EtaleCohomology.subsingleton_sheafH_pushforward_pointOfClosedPoint` — the statement
  above for a closed point of a scheme locally of finite type over an algebraically closed
  field.

## Implementation notes

The statements are on Mathlib's small étale site `Scheme.smallEtaleTopology`, with direct image
`Stacks.EtaleCohomology.smallEtalePushforwardAb`, because the integral-pushforward cohomology
comparison `Stacks.EtaleCohomology.sheafHSmallEtalePushforwardAddEquiv` is stated there.
Finite type is weakened to locally of finite type, and the sheaf may live on any separably
closed field in the general form.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I §5][FK]
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`, which makes
`CategoryTheory.Sheaf.H` elaborate. -/
local instance isGrothendieckAbelian_sheaf_smallEtaleTopology_skyscraper (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  letI : EssentiallySmall.{u + 1} X.Etale := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology X) Ab.{u + 1}

/-- **Direct image from a separably closed point along an integral morphism is acyclic.** For
`K` a separably closed field, `y : Spec K ⟶ X` an integral morphism and `𝒢` an abelian sheaf
on the small étale site of `Spec K`, the étale cohomology of `y_* 𝒢` vanishes in every positive
degree. -/
public theorem subsingleton_sheafH_pushforward_of_isSepClosed {K : Type u} [Field K]
    [IsSepClosed K] {X : Scheme.{u}} (y : Spec (.of K) ⟶ X) [IsIntegralHom y]
    (𝒢 : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}) (q : ℕ) (hq : 1 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePushforwardAb y).obj 𝒢) q) := by
  have : StrictlyHenselianLocalRing K := StrictlyHenselianLocalRing.of_isSepClosed K
  have : Subsingleton (Sheaf.H.{u + 1, u + 1} 𝒢 q) :=
    Stacks.StrictlyHenselian.subsingleton_etaleCohomology_smallEtaleTopology K 𝒢 q hq
  exact Equiv.subsingleton (sheafHSmallEtalePushforwardAddEquiv y 𝒢 q).symm.toEquiv

/-- The `k`-point `Spec k ⟶ X` attached to a closed point of a scheme locally of finite type
over an algebraically closed field `k` is finite. -/
public instance isFinite_pointOfClosedPoint {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (x : X)
    (hx : IsClosed {x}) : IsFinite (pointOfClosedPoint g x hx) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  unfold pointOfClosedPoint
  infer_instance

/-- **Skyscraper sheaves at closed points are acyclic.** Let `X` be a scheme locally of finite
type over an algebraically closed field `k`, `x` a closed point of `X` regarded as the
geometric point `x : Spec k ⟶ X`, and `𝒢` an abelian sheaf on the small étale site of
`Spec k`. Then `H^q(X, x_* 𝒢) = 0` for every `q ≥ 1`. -/
@[weil "lem_fk105_skyscraper_acyclic_alg_closed_point"]
public theorem subsingleton_sheafH_pushforward_pointOfClosedPoint {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (x : X)
    (hx : IsClosed {x}) (𝒢 : Sheaf (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}) (q : ℕ)
    (hq : 1 ≤ q) :
    Subsingleton
      (Sheaf.H.{u + 1, u + 1} ((smallEtalePushforwardAb (pointOfClosedPoint g x hx)).obj 𝒢) q) :=
  subsingleton_sheafH_pushforward_of_isSepClosed _ 𝒢 q hq

end Stacks.EtaleCohomology

end

/-! ### The sheaf of divisors on a curve is acyclic -/

/-!
# The sheaf of divisors on a curve is acyclic

Let `X` be a scheme locally of finite type over an algebraically closed field `k`, quasi-compact
and quasi-separated (for instance a smooth curve over `k`), and let
`𝒟_X = ⨁_{x ∈ X₀} (i_x)_* ℤ` be the sheaf of divisors on its small étale site, the direct sum over
the closed points of the skyscraper sheaves (`Stacks.EtaleCohomology.closedPointDivisorSheaf`).
Then `H^q(X, 𝒟_X) = 0` for every `q > 0`.

Étale cohomology commutes with the direct sum, and each summand is acyclic: the inclusion of a
closed point is a closed immersion, so direct image along it does not change cohomology, and the
residue field at a closed point is algebraically closed, so every abelian sheaf on its spectrum is
acyclic.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_closedPointDivisorSheaf`: the vanishing on Mathlib's
  small étale site `X.smallEtaleTopology`.
* `AlgebraicGeometry.subsingleton_sheafH_closedPointDivisorSheaf_smallEtale`: the vanishing on the
  small étale site `SmallEtale B X hX` of a big étale site `B` containing `X`, for the restriction
  of the sheaf of divisors to it.

## Implementation notes

The hypotheses are those of the Stacks project statement, more general than a smooth curve: `X`
quasi-compact, quasi-separated and locally of finite type over `k`. Coefficients are
`AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`, the universe in which the sheaf of divisors is
formed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RL](https://stacks.math.columbia.edu/tag/03RL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`, which makes
`CategoryTheory.Sheaf.H` elaborate. -/
local instance isGrothendieckAbelian_sheaf_smallEtaleTopology_divisors (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  letI : EssentiallySmall.{u + 1} X.Etale := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology X) Ab.{u + 1}

/-- **The sheaf of divisors is acyclic**, on Mathlib's small étale site: for `X` quasi-compact,
quasi-separated and locally of finite type over an algebraically closed field `k`, the cohomology
of `⨁_{x ∈ X₀} (i_x)_* ℤ` vanishes in every positive degree. -/
theorem subsingleton_sheafH_closedPointDivisorSheaf {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] [CompactSpace X]
    [QuasiSeparatedSpace X] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} (closedPointDivisorSheaf.{u, 0} X) q) :=
  subsingleton_sheafH_sigma_closedPointPushforward_smallEtale g q hq

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`. -/
local instance isGrothendieckAbelian_sheaf_smallEtaleTopology_divisorSheaf (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  letI : EssentiallySmall.{u + 1} X.Etale := inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology X)
    AddCommGrpCat.{u + 1}

/-- **The sheaf of divisors is acyclic.** Let `X` be quasi-compact, quasi-separated and locally of
finite type over an algebraically closed field `k` (for instance a smooth curve over `k`), and `B`
a big étale site containing `X`. The restriction of the sheaf of divisors
`𝒟_X = ⨁_{x ∈ X₀} (i_x)_* ℤ` to the small étale site `SmallEtale B X hX` has vanishing cohomology
in every positive degree. -/
@[weil "lem_fk105_divisors_acyclic"]
theorem subsingleton_sheafH_closedPointDivisorSheaf_smallEtale {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g]
    [CompactSpace X] [QuasiSeparatedSpace X] (B : BigEtaleSite.{u}) (hX : B.Contains X)
    [HasExt.{u + 1} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.obj
      (Stacks.EtaleCohomology.closedPointDivisorSheaf.{u, 0} X)) q) := by
  have := Stacks.EtaleCohomology.subsingleton_sheafH_closedPointDivisorSheaf g q hq
  have : EnoughInjectives (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
    (SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).enoughInjectives_iff.2 inferInstance
  exact (Stacks.Cohomology.DenseSubsite.hAddEquiv.{u + 1, u + 1} (SmallEtale.topology B X hX)
    X.smallEtaleTopology (SmallEtale.toEtaleSite B X hX)
    (Stacks.EtaleCohomology.closedPointDivisorSheaf.{u, 0} X) q).symm.injective.subsingleton

end AlgebraicGeometry

end
