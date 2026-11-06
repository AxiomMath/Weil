module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.RingTheory.Etale.Pi

/-!
# Finite products of étale algebras

A finite product `∏ k, B k` of étale `A`-algebras is an étale `A`-algebra; for the empty
family the product is the zero ring. Consequently a finite family of objects of the étale
category `Et(A)` has a product algebra which is again an object of `Et(A)`.

## Main results

- `AlgebraicGeometry.EtaleCategory.algebra_etale_pi`: `∏ k, B k` is étale over `A` for a
  finite family of étale `A`-algebras.
- `AlgebraicGeometry.EtaleCategory.isEtaleAlgebra_pi`: the product `A`-algebra of a finite
  family of étale `A`-algebras satisfies `IsEtaleAlgebra A`.
- `AlgebraicGeometry.EtaleCategory.piAlgebra`: the product, as an object of the full
  subcategory of étale `A`-algebras.
- `AlgebraicGeometry.EtaleCategory.subsingleton_pi_of_isEmpty`: for the empty family the
  product is the zero ring.

## Implementation notes

The étaleness of the product is Mathlib's instance `Algebra.Etale` on finite products
(`Mathlib.RingTheory.Etale.Pi`); no noetherian hypothesis is needed. The index type and the
factors live in independent universes. For the categorical statements the base ring lives in
`Type (max u w)` when the index type lives in `Type w`, so that the product lands in the same
universe; this covers both an index type in `Type` over a base ring in any universe and an
index type in the universe of the base ring.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

/-- A finite product of étale `A`-algebras is an étale `A`-algebra. -/
@[weil "lem_fk101_etale_finite_product"]
theorem algebra_etale_pi (A : Type u) [CommRing A] {K : Type w} [Finite K]
    (B : K → Type v) [∀ k, CommRing (B k)] [∀ k, Algebra A (B k)]
    [∀ k, Algebra.Etale A (B k)] : Algebra.Etale A (∀ k, B k) :=
  inferInstance

/-- For the empty family, the product algebra is the zero ring. -/
@[weil "lem_fk101_etale_finite_product"]
theorem subsingleton_pi_of_isEmpty {K : Type w} [IsEmpty K] (B : K → Type v) :
    Subsingleton (∀ k, B k) :=
  inferInstance

variable {A : CommRingCat.{max u w}}

/-- The product `A`-algebra of a finite family of étale `A`-algebras is étale. -/
@[weil "lem_fk101_etale_finite_product"]
theorem isEtaleAlgebra_pi {K : Type w} [Finite K] (B : K → (IsEtaleAlgebra A).FullSubcategory) :
    IsEtaleAlgebra A (CommAlgCat.of A (∀ k, (B k).obj)) :=
  haveI : ∀ k, Algebra.Etale A (B k).obj := fun k ↦ (B k).property
  algebra_etale_pi A (fun k ↦ (B k).obj)

/-- The product of a finite family of étale `A`-algebras, as an étale `A`-algebra. -/
noncomputable abbrev piAlgebra {K : Type w} [Finite K]
    (B : K → (IsEtaleAlgebra A).FullSubcategory) : (IsEtaleAlgebra A).FullSubcategory :=
  ⟨CommAlgCat.of A (∀ k, (B k).obj), isEtaleAlgebra_pi B⟩

/-- The product of a finite family of étale `A`-algebras, as an object of `Et(A)`. -/
noncomputable abbrev piObj {K : Type w} [Finite K]
    (B : K → (IsEtaleAlgebra A).FullSubcategory) : EtaleCategory A :=
  ofAlgebra A (piAlgebra B)

end EtaleCategory

end AlgebraicGeometry
