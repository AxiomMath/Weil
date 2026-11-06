module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal

/-!
# Closed points under an étale morphism of schemes over a field

Let `k` be a field, `U` a scheme locally of finite type over `k` and `ψ : V ⟶ U` an étale
morphism. A point `v` of `V` is closed if and only if its image `ψ v` is closed in `U`.

If `ψ v` is closed, `v` is isolated in its fibre (an étale morphism is quasi-finite) and the fibre
over a closed point is closed in `V`. Conversely `V` is locally of finite type over `k`, so a
closed point of `V` has residue field finite over `k`, hence so does `ψ v`, and `ψ v` is closed
because `U` is a Jacobson space.

## Main results

* `AlgebraicGeometry.isClosed_singleton_iff_of_etale_of_locallyOfFiniteType`: a point of the
  source of an étale morphism of schemes locally of finite type over a field is closed exactly
  when its image is.

## Implementation notes

The statement is more general than the one in the reference: `V` need not be of finite type
over `k` (it is automatically locally of finite type, being étale over `U`), only `U` has to be
locally of finite type over `k`, and `ψ` need not be a morphism over `k`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FK]
* [Stacks Project, Tag 0C57](https://stacks.math.columbia.edu/tag/0C57)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Let `U` be a scheme locally of finite type over a field `k` and `ψ : V ⟶ U` étale. Then a
point `v` of `V` is closed if and only if `ψ v` is closed in `U`. -/
@[weil "lem_fk105_etale_closed_points_iff"]
theorem isClosed_singleton_iff_of_etale_of_locallyOfFiniteType
    {k : Type u} [Field k] {U V : Scheme.{u}}
    (f : U ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (ψ : V ⟶ U) [Etale ψ] (v : V) :
    IsClosed ({v} : Set V) ↔ IsClosed ({ψ v} : Set U) :=
  (Stacks.Curves.isClosed_singleton_iff_of_etale f ψ v).symm

end AlgebraicGeometry
