module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.PointedCoveringMorphism
public import Weil.Attr

/-!
# Uniqueness of mappings of pointed covering spaces

Let `s` be a geometric point of a scheme `X` and let `(Y₁, α₁)`, `(Y₂, α₂)` be pointed covering
spaces of `(X, s)` with `Y₁` connected. Then there is at most one mapping of pointed covering
spaces `(Y₁, α₁) → (Y₂, α₂)`.

A pointed covering space `(Y, α)` is an étale neighbourhood of `s`, and a mapping of pointed
covering spaces is a morphism of étale neighbourhoods; since the structure morphism of a
covering space is finite, hence separated, the uniqueness of morphisms of étale neighbourhoods
out of a connected one applies.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.toEtaleNeighborhood` — the étale
  neighbourhood of `s` underlying a pointed covering space.

## Main results

* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.IsHom.eq_of_connectedSpace` — two
  mappings of pointed covering spaces out of a connected one are equal.
* `AlgebraicGeometry.GeometricPoint.PointedCoveringSpace.subsingleton_hom_of_connectedSpace` —
  there is at most one morphism of pointed covering spaces out of a connected one.

## Implementation notes

No hypothesis on `X` is needed: the separatedness used is that of the finite structure morphism
of the target covering space.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

namespace PointedCoveringSpace

variable {X : Scheme.{u}} {s : GeometricPoint X}

/-- The étale neighbourhood `(Y, α)` of `s` underlying a pointed covering space `(Y, α)`. -/
def toEtaleNeighborhood (P : s.PointedCoveringSpace) : EtaleNeighborhood s where
  scheme := P.cover.left
  toBase := P.cover.hom
  point := P.point
  point_comp := P.point_comp_hom

@[simp]
lemma toEtaleNeighborhood_scheme (P : s.PointedCoveringSpace) :
    P.toEtaleNeighborhood.scheme = P.cover.left :=
  rfl

@[simp]
lemma toEtaleNeighborhood_toBase (P : s.PointedCoveringSpace) :
    P.toEtaleNeighborhood.toBase = P.cover.hom :=
  rfl

/-- A mapping of pointed covering spaces as a morphism of the underlying étale
neighbourhoods. -/
def IsHom.toEtaleNeighborhoodHom {P Q : s.PointedCoveringSpace}
    {f : P.cover.left ⟶ Q.cover.left} (hf : IsHom P Q f) :
    P.toEtaleNeighborhood ⟶ Q.toEtaleNeighborhood :=
  EtaleNeighborhood.homMk (U := P.toEtaleNeighborhood) (V := Q.toEtaleNeighborhood) f hf.1 hf.2

/-- **Mappings of pointed covering spaces are unique.** Two mappings of pointed covering spaces
`(Y₁, α₁) → (Y₂, α₂)` with `Y₁` connected are equal. -/
@[weil "lem_fka1_pointed_morphism_unique"]
theorem IsHom.eq_of_connectedSpace {P Q : s.PointedCoveringSpace} [ConnectedSpace P.cover.left]
    {f g : P.cover.left ⟶ Q.cover.left} (hf : IsHom P Q f) (hg : IsHom P Q g) : f = g := by
  have : ConnectedSpace P.toEtaleNeighborhood.scheme := ‹ConnectedSpace P.cover.left›
  have : IsSeparated Q.toEtaleNeighborhood.toBase :=
    IsSeparated.of_isAffineHom (Q.cover.hom : Q.cover.left ⟶ X)
  exact congrArg EtaleNeighborhood.Hom.hom
    (EtaleNeighborhood.hom_ext_of_connectedSpace hf.toEtaleNeighborhoodHom
      hg.toEtaleNeighborhoodHom)

/-- **Mappings of pointed covering spaces are unique.** There is at most one morphism of pointed
covering spaces `(Y₁, α₁) ⟶ (Y₂, α₂)` when `Y₁` is connected. -/
@[weil "lem_fka1_pointed_morphism_unique"]
instance subsingleton_hom_of_connectedSpace {P Q : s.PointedCoveringSpace}
    [ConnectedSpace P.cover.left] : Subsingleton (P ⟶ Q) :=
  ⟨fun f g => hom_ext ((isHom_left f).eq_of_connectedSpace (isHom_left g))⟩

end PointedCoveringSpace

end GeometricPoint

end AlgebraicGeometry

end
