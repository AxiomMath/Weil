/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import Weil.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import Weil.Attr

/-!
# The strict local ring at a geometric point is strictly Henselian

Let `x` be a geometric point of a scheme `X`. The strict local ring `𝒪̃_{X,x}` is isomorphic
to the strict Henselization of the Zariski local ring `𝒪_{X,x₀}` at the image `x₀` of `x`;
hence it is a strictly Henselian local ring: a Henselian local ring whose residue field is
separably closed.

## Main results

* `AlgebraicGeometry.strictLocalRing_strictlyHenselian`: the strict local ring of `X` at a
  geometric point is strictly Henselian.
* `AlgebraicGeometry.henselianLocalRing_strictLocalRing_and_isSepClosed`: equivalently, it is
  Henselian and its residue field is separably closed.

## Implementation notes

Geometric points take values in algebraically closed fields
(`AlgebraicGeometry.GeometricPoint`), and the result is
`AlgebraicGeometry.etaleLocalRing_strictHenselian`, which identifies the étale local ring with
the strict Henselization of the Zariski local ring.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.2
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- For every geometric point `x` of `X`, the strict local ring `𝒪̃_{X,x}` is a strictly
Henselian local ring. -/
@[weil "lem_fk102_strict_local_ring_strictly_henselian"]
theorem strictLocalRing_strictlyHenselian :
    StrictlyHenselianLocalRing (strictLocalRing B X hX x) :=
  etaleLocalRing_strictHenselian B X hX x

/-- The strict local ring `𝒪̃_{X,x}` is a Henselian local ring with separably closed residue
field. -/
theorem henselianLocalRing_strictLocalRing_and_isSepClosed :
    HenselianLocalRing (strictLocalRing B X hX x) ∧
      IsSepClosed (IsLocalRing.ResidueField (strictLocalRing B X hX x)) :=
  (strictlyHenselianLocalRing_iff _).1 (strictLocalRing_strictlyHenselian B X hX x)

end AlgebraicGeometry
