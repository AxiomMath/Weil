module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# The opposite of the category of étale neighbourhoods is filtered

Let `s` be a geometric point of a scheme `S` and `N(s)` the category of étale neighbourhoods
of `s` (`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood`). Then `N(s)ᵒᵖ` is filtered:
`N(s)` is nonempty, any two étale neighbourhoods are dominated by a third, and any two parallel
morphisms `f g : (U, u) ⟶ (V, v)` are equalised by some morphism `e : (W, w) ⟶ (U, u)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.isFiltered_op`: `N(s)ᵒᵖ` is filtered.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.cofiltered_conditions`: the three
  conditions spelled out.

## Implementation notes

`N(s)` is identified with the category of elements of the fibre functor of the point
`AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site, which Mathlib proves to be
cofiltered; the cofilteredness of `N(s)` is transported along that equivalence, and the
filteredness of `N(s)ᵒᵖ` follows.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
* [Stacks Project, Tag 03PQ](https://stacks.math.columbia.edu/tag/03PQ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

namespace EtaleNeighborhood

variable {S : Scheme.{u}} (s : GeometricPoint S)

/-- The opposite of the category of étale neighbourhoods of a geometric point is filtered. -/
@[weil "lem_fk102_etale_neighborhoods_filtered"]
instance isFiltered_op : IsFiltered (EtaleNeighborhood s)ᵒᵖ :=
  isFiltered_op_of_isCofiltered _

/-- The category of étale neighbourhoods of a geometric point `s` is nonempty, any two étale
neighbourhoods of `s` receive morphisms from a common one, and any two parallel morphisms of
étale neighbourhoods are equalised by a morphism into their source. -/
@[weil "lem_fk102_etale_neighborhoods_filtered"]
theorem cofiltered_conditions :
    Nonempty (EtaleNeighborhood s) ∧
      (∀ U V : EtaleNeighborhood s, ∃ (W : EtaleNeighborhood s) (_ : W ⟶ U), Nonempty (W ⟶ V)) ∧
      ∀ {U V : EtaleNeighborhood s} (f g : U ⟶ V),
        ∃ (W : EtaleNeighborhood s) (e : W ⟶ U), e ≫ f = e ≫ g :=
  ⟨IsCofiltered.nonempty, fun U V => ⟨IsCofiltered.min U V, IsCofiltered.minToLeft U V,
      ⟨IsCofiltered.minToRight U V⟩⟩,
    fun f g => ⟨IsCofiltered.eq f g, IsCofiltered.eqHom f g, IsCofiltered.eq_condition f g⟩⟩

end EtaleNeighborhood

end GeometricPoint

end AlgebraicGeometry

end
