module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.AffineEtale

/-!
# The étale category of a ring is essentially small

For a commutative ring `A`, the isomorphism classes of objects of the étale category `Et(A)`
form a set: every étale `A`-algebra is of finite type, hence a quotient of a polynomial ring in
finitely many variables over `A`.

## Main results

- `AlgebraicGeometry.EtaleCategory.essentiallySmall`: `EtaleCategory A` is essentially small.
- `AlgebraicGeometry.EtaleCategory.essentiallySmall_isEtaleAlgebra`: the full subcategory of
  étale `A`-algebras is essentially small.

## Implementation notes

The essential smallness of the affine étale site `Scheme.AffineEtale (Spec A)` is Mathlib's;
it is transported along the opposite category and the equivalence
`AlgebraicGeometry.EtaleCategory.algebraEquiv`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable (A : CommRingCat.{u})

/-- The isomorphism classes of objects of the étale category of `A` form a set. -/
@[weil "lem_fk101_etale_category_essentially_small"]
instance essentiallySmall : EssentiallySmall.{u} (EtaleCategory A) :=
  inferInstanceAs (EssentiallySmall.{u} (Scheme.AffineEtale (Spec A))ᵒᵖ)

/-- The isomorphism classes of étale `A`-algebras form a set. -/
@[weil "lem_fk101_etale_category_essentially_small"]
instance essentiallySmall_isEtaleAlgebra :
    EssentiallySmall.{u} (IsEtaleAlgebra A).FullSubcategory :=
  (essentiallySmall_congr (algebraEquiv A)).mpr inferInstance

end EtaleCategory

end AlgebraicGeometry
