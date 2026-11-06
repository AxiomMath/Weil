module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import WeilFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# The degree of a covering space

Let `p : Y ⟶ X` be a covering space (a finite étale morphism) and `n` a natural number. The
covering space `Y` *has degree `n`* if the set `Y(s)` of geometric points of `Y` over `s` has
exactly `n` elements for every geometric point `s` of `X` with `Y(s)` nonempty.

Over a connected base this is the rank of `p` as a finite locally free morphism: if `p` is finite
locally free of rank `n` then every geometric fibre has `n` elements, and conversely if `Y` has
degree `n` and some geometric fibre is nonempty, then `p` is finite locally free of rank `n`.

## Main definitions

* `AlgebraicGeometry.Scheme.CoveringSpace.HasDegree Y n` — the covering space `Y` has degree `n`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.hasDegree_iff_fiberFunctor` — the definition in terms
  of the functor of geometric points `AlgebraicGeometry.GeometricPoint.fiberFunctor`.
* `AlgebraicGeometry.Scheme.CoveringSpace.HasDegree.eq` — the degree is unique as soon as one
  geometric fibre is nonempty.
* `AlgebraicGeometry.Scheme.CoveringSpace.hasDegree_of_isEmpty` — the empty covering space has
  every degree.
* `AlgebraicGeometry.Scheme.CoveringSpace.natCard_eq_of_isFiniteLocallyFreeOfRank`,
  `AlgebraicGeometry.Scheme.CoveringSpace.hasDegree_of_isFiniteLocallyFreeOfRank` — over a
  connected base, a covering space of rank `n` has every geometric fibre of size `n`.
* `AlgebraicGeometry.Scheme.CoveringSpace.HasDegree.isFiniteLocallyFreeOfRank` — over a connected
  base, a covering space of degree `n` with a nonempty geometric fibre has rank `n`.
* `AlgebraicGeometry.Scheme.CoveringSpace.hasDegree_natCard` — over a connected base, a covering
  space has degree the size of any of its geometric fibres.

## Implementation notes

Geometric points take values in algebraically closed fields
(`AlgebraicGeometry.GeometricPoint`), following the Stacks project; the source allows separably
closed fields. The size of a geometric fibre does not depend on this choice, since a finite étale
algebra over a separably closed field already splits completely.

The fibre `Y(s)` is the geometric fibre `AlgebraicGeometry.finiteEtaleFiberFunctor s` of the
Stacks project, which is the restriction to covering spaces of
`AlgebraicGeometry.GeometricPoint.fiberFunctor s` on the nose.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.CoveringSpace

variable {X : Scheme.{u}}

/-- **The degree of a covering space.** A covering space `Y` of `X` *has degree `n`* if the
geometric fibre `Y(s)` has exactly `n` elements for every geometric point `s` of `X` with `Y(s)`
nonempty. -/
@[weil "def_fka1_covering_degree"]
def HasDegree (Y : X.CoveringSpace) (n : ℕ) : Prop :=
  ∀ s : GeometricPoint X, Nonempty ((finiteEtaleFiberFunctor s).obj Y) →
    Nat.card ((finiteEtaleFiberFunctor s).obj Y) = n

/-- The degree in terms of the functor of geometric points over `s`, `Y ↦ Y(s)`. -/
theorem hasDegree_iff_fiberFunctor (Y : X.CoveringSpace) (n : ℕ) :
    HasDegree Y n ↔ ∀ s : GeometricPoint X,
      Nonempty ((s.fiberFunctor).obj ((MorphismProperty.Over.forget _ _ X).obj Y)) →
        Nat.card ((s.fiberFunctor).obj ((MorphismProperty.Over.forget _ _ X).obj Y)) = n :=
  Iff.rfl

theorem HasDegree.natCard_eq {Y : X.CoveringSpace} {n : ℕ} (h : HasDegree Y n)
    (s : GeometricPoint X) (hs : Nonempty ((finiteEtaleFiberFunctor s).obj Y)) :
    Nat.card ((finiteEtaleFiberFunctor s).obj Y) = n :=
  h s hs

/-- The degree of a covering space is unique once one of its geometric fibres is nonempty. -/
theorem HasDegree.eq {Y : X.CoveringSpace} {m n : ℕ} (hm : HasDegree Y m) (hn : HasDegree Y n)
    (s : GeometricPoint X) (hs : Nonempty ((finiteEtaleFiberFunctor s).obj Y)) : m = n :=
  (hm s hs).symm.trans (hn s hs)

/-- A covering space with empty source has every degree. -/
theorem hasDegree_of_isEmpty (Y : X.CoveringSpace) [IsEmpty Y.left] (n : ℕ) : HasDegree Y n :=
  fun _ ⟨α⟩ ↦ (IsEmpty.false (α.1 default)).elim

/-- A finite locally free morphism of rank `m` and of rank `n` to a nonempty scheme has `m = n`. -/
private theorem eq_of_isFiniteLocallyFreeOfRank {Y S : Scheme.{u}} (f : Y ⟶ S) [IsFinite f]
    [Flat f] (x : S) {m n : ℕ} (hm : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f m)
    (hn : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f n) : m = n := by
  rw [Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq] at hm hn
  exact (hm x).symm.trans (hn x)

/-- Over a connected base, every geometric fibre of a covering space of rank `n` has `n`
elements. -/
theorem natCard_eq_of_isFiniteLocallyFreeOfRank [ConnectedSpace X] {Y : X.CoveringSpace} {n : ℕ}
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank Y.hom n) (s : GeometricPoint X) :
    Nat.card ((finiteEtaleFiberFunctor s).obj Y) = n :=
  eq_of_isFiniteLocallyFreeOfRank Y.hom (s.hom default)
    (isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s Y) h

/-- Over a connected base, a covering space of rank `n` has degree `n`. -/
theorem hasDegree_of_isFiniteLocallyFreeOfRank [ConnectedSpace X] {Y : X.CoveringSpace} {n : ℕ}
    (h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank Y.hom n) : HasDegree Y n :=
  fun s _ ↦ natCard_eq_of_isFiniteLocallyFreeOfRank h s

/-- Over a connected base, a covering space has degree the number of elements of any of its
geometric fibres. -/
theorem hasDegree_natCard [ConnectedSpace X] (Y : X.CoveringSpace) (s : GeometricPoint X) :
    HasDegree Y (Nat.card ((finiteEtaleFiberFunctor s).obj Y)) :=
  hasDegree_of_isFiniteLocallyFreeOfRank (isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s Y)

/-- Over a connected base, a covering space of degree `n` with a nonempty geometric fibre is
finite locally free of rank `n`. -/
theorem HasDegree.isFiniteLocallyFreeOfRank [ConnectedSpace X] {Y : X.CoveringSpace} {n : ℕ}
    (h : HasDegree Y n) (s : GeometricPoint X)
    (hs : Nonempty ((finiteEtaleFiberFunctor s).obj Y)) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank Y.hom n :=
  h s hs ▸ isFiniteLocallyFreeOfRank_natCard_finiteEtaleFiber s Y

/-- Over a connected base, a covering space with a nonempty geometric fibre has degree `n` if and
only if it is finite locally free of rank `n`. -/
theorem hasDegree_iff_isFiniteLocallyFreeOfRank [ConnectedSpace X] (Y : X.CoveringSpace)
    (s : GeometricPoint X) (hs : Nonempty ((finiteEtaleFiberFunctor s).obj Y)) (n : ℕ) :
    HasDegree Y n ↔ Stacks.Morphisms.IsFiniteLocallyFreeOfRank Y.hom n :=
  ⟨fun h ↦ h.isFiniteLocallyFreeOfRank s hs, hasDegree_of_isFiniteLocallyFreeOfRank⟩

end Scheme.CoveringSpace

end AlgebraicGeometry

end
