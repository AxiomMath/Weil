/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import Weil.Attr

/-!
# The strict local ring at a geometric point

Let `x` be a geometric point of a scheme `X`. The *strict local ring* `𝒪̃_{X,x}` of `X` at `x`
is the colimit, in the category of rings, of the rings of global functions `Γ(U, 𝒪_U)` over the
étale neighbourhoods `(U, u)` of `x`, the transition map along a morphism of neighbourhoods
`h : (U, u) ⟶ (V, v)` being the pullback `h^* : Γ(V, 𝒪_V) ⟶ Γ(U, 𝒪_U)`.

This ring is the étale local ring `AlgebraicGeometry.etaleLocalRing` (the stalk at `x` of the
structure sheaf of the small étale site), which is commutative, local, strictly Henselian and
an algebra over the Zariski local ring at the image of `x`. Here it is recorded as an object of
`CommRingCat`, together with the diagram of the rings of functions on the étale neighbourhoods
and the fact that it is the colimit of that diagram in `CommRingCat`.

## Main definitions

* `AlgebraicGeometry.strictLocalRing`: the strict local ring of `X` at `x`, as a commutative
  ring.
* `AlgebraicGeometry.strictLocalRingDiagram`: the functor `(U, u) ↦ Γ(U, 𝒪_U)` on the opposite
  of the category of étale neighbourhoods of `x`.
* `AlgebraicGeometry.strictLocalRingCocone`: the cocone of germ maps `Γ(U, 𝒪_U) ⟶ 𝒪̃_{X,x}`.

## Main results

* `AlgebraicGeometry.isColimitStrictLocalRingCocone`: the strict local ring is the colimit of
  `strictLocalRingDiagram` in the category of commutative rings.
* `AlgebraicGeometry.strictLocalRing_eq_colimit`: as a ring, it is by definition the colimit
  of the same diagram in the category of rings.

## Implementation notes

Geometric points are those of `AlgebraicGeometry.GeometricPoint`, with values in an
algebraically closed field, and étale neighbourhoods are taken in the small étale site of a big
étale site `B` containing `X`; the size cutoff of that site is why `B` and `hX` appear.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.2
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- The strict local ring of `X` at a geometric point `x`: the étale local ring at `x`, as a
commutative ring. -/
@[weil "def_fk102_strict_local_ring"]
abbrev strictLocalRing : CommRingCat.{u} :=
  CommRingCat.of (etaleLocalRing B X hX x)

/-- The rings of global functions on the étale neighbourhoods of a geometric point `x`, as a
functor on the opposite of the category of étale neighbourhoods: `(U, u) ↦ Γ(U, 𝒪_U)`, with
transition maps the pullbacks of functions. -/
abbrev strictLocalRingDiagram :
    (geometricPointFiber B X hX x).Elementsᵒᵖ ⥤ CommRingCat.{u} :=
  (CategoryOfElements.π (geometricPointFiber B X hX x)).op ⋙
    (SmallEtale.toScheme B X hX).op ⋙ Scheme.Γ

/-- The étale local ring at `x` is, by definition, the colimit in the category of rings of the
rings of global functions on the étale neighbourhoods of `x`. -/
theorem strictLocalRing_eq_colimit :
    etaleLocalRing B X hX x =
      colimit (strictLocalRingDiagram B X hX x ⋙ forget₂ CommRingCat RingCat) :=
  rfl

/-- The germ maps `Γ(U, 𝒪_U) ⟶ 𝒪̃_{X,x}` from the rings of functions on the étale
neighbourhoods of `x` to the strict local ring. -/
def strictLocalRingCocone : Cocone (strictLocalRingDiagram B X hX x) where
  pt := strictLocalRing B X hX x
  ι :=
    { app := fun U => CommRingCat.ofHom
        (colimit.ι (strictLocalRingDiagram B X hX x ⋙ forget₂ CommRingCat RingCat) U).hom
      naturality := fun U V f => by
        ext a
        exact congrArg (fun g => g.hom a)
          (colimit.w (strictLocalRingDiagram B X hX x ⋙ forget₂ CommRingCat RingCat) f) }

/-- **The strict local ring is a colimit.** The strict local ring of `X` at `x` is the colimit,
in the category of commutative rings, of the rings of global functions `Γ(U, 𝒪_U)` over the
étale neighbourhoods `(U, u)` of `x`, with transition maps the pullbacks of functions. -/
@[weil "def_fk102_strict_local_ring"]
def isColimitStrictLocalRingCocone : IsColimit (strictLocalRingCocone B X hX x) :=
  isColimitOfReflects (forget₂ CommRingCat RingCat)
    ((colimit.isColimit
      (strictLocalRingDiagram B X hX x ⋙ forget₂ CommRingCat RingCat)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (fun _ => rfl)))

end AlgebraicGeometry
