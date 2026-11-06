module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Attr

/-!
# Geometric fibres of covering spaces of a connected scheme are nonempty

Let `X` be a connected scheme and `p : Y ⟶ X` a covering space (a finite étale morphism) with
`Y` nonempty. Since `p` is étale its image is open, and since `p` is finite its image is closed;
being nonempty, the image is all of `X`. Hence for every geometric point `s : Spec Ω ⟶ X`
there is a point of `Y` over the underlying point of `s`, and since `p` is étale and `Ω` is
(separably) closed, it lifts to a geometric point `α : Spec Ω ⟶ Y` with `α ≫ p = s`.
So the geometric fibre `Y(s)` is nonempty.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.surjective_hom_of_nonempty` — a covering space of a
  connected scheme with nonempty source is surjective.
* `AlgebraicGeometry.Scheme.CoveringSpace.nonempty_fiberFunctor_obj` — its geometric fibre over
  every geometric point is nonempty.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.CoveringSpace

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- A covering space `p : Y ⟶ X` of a connected scheme with `Y` nonempty is surjective: its
image is open (`p` is étale) and closed (`p` is finite). -/
theorem surjective_hom_of_nonempty (Y : X.CoveringSpace) [Nonempty Y.left] :
    Function.Surjective (Y.hom : Y.left ⟶ X) := by
  let p : Y.left ⟶ X := Y.hom
  have hopen : IsOpen (Set.range p) := p.isOpenMap.isOpen_range
  have hclosed : IsClosed (Set.range p) := p.isClosedMap.isClosed_range
  obtain ⟨y⟩ := ‹Nonempty Y.left›
  have hne : (Set.range p).Nonempty := ⟨p y, y, rfl⟩
  have hclopen : IsClopen (Set.range p) := ⟨hclosed, hopen⟩
  exact Set.range_eq_univ.mp ((isClopen_iff (α := X)).mp hclopen |>.resolve_left hne.ne_empty)

/-- **Geometric fibres of a covering space of a connected scheme are nonempty.** Let `X` be a
connected scheme, `p : Y ⟶ X` a covering space with `Y` nonempty and `s` a geometric point of
`X`. Then `Y(s)` is nonempty: there is a geometric point `α : Spec Ω ⟶ Y` with `α ≫ p = s`. -/
@[weil "lem_fka1_covering_fiber_nonempty_connected_base"]
theorem nonempty_fiberFunctor_obj (Y : X.CoveringSpace) [Nonempty Y.left]
    (s : GeometricPoint X) :
    Nonempty
      ((GeometricPoint.fiberFunctor s).obj ((MorphismProperty.Over.forget _ _ X).obj Y)) := by
  obtain ⟨y, hy⟩ := surjective_hom_of_nonempty Y (s.hom default)
  obtain ⟨α, hα, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (Y.hom : Y.left ⟶ X) s.hom y hy
  exact ⟨⟨α, hα⟩⟩

end Scheme.CoveringSpace

end AlgebraicGeometry

end
