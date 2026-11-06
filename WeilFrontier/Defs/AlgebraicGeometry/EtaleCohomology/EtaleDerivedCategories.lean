module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# The derived category of étale sheaves of modules

Let `X` be a scheme and `Λ` a ring. The étale sheaves of `Λ`-modules on `X` form an abelian
category `Sh(X, Λ)`, and `D(X, Λ)` is its derived category `D(Sh(X, Λ))`: the localization of
the homotopy category of complexes of étale sheaves of `Λ`-modules at the quasi-isomorphisms.
It is a triangulated category, with shift, distinguished triangles and localization functor
`Q` from complexes coming from the general theory of derived categories of abelian categories.
Its bounded below and bounded above parts `D⁺(X, Λ)` and `D⁻(X, Λ)` are
`DerivedCategory.Plus` and `DerivedCategory.Minus` of the same abelian category.

## Main definitions

* `Stacks.EtaleCohomology.EtaleDerivedCategory Λ X`: the derived category `D(X, Λ)` of the
  abelian category `Stacks.EtaleCohomology.EtaleModules Λ X` of étale sheaves of `Λ`-modules
  on `X`.

## Implementation notes

The abelian category is `Stacks.EtaleCohomology.EtaleModules Λ X`, sheaves on Mathlib's small
étale site `X.smallEtaleTopology` with coefficients `ModuleCat.{max (u + 1) r} Λ`; this is the
category on which the direct image, restriction, extension by zero and global sections functors
and their right derived functors `Stacks.EtaleCohomology.etaleModuleDerivedDirectImage` and
`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSections` are defined, so that they are functors
between the categories defined here. The derived category is Mathlib's `DerivedCategory` for the
instance `CategoryTheory.HasDerivedCategory.standard`, made a local instance as in that
development; the definition fixes this instance, so that `D(X, Λ)` is one type rather than one
for each choice of instance.

The ring `Λ` is only assumed to be a ring; the source takes it commutative.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II][FK]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

/-- The derived category `D(X, Λ)` of étale sheaves of `Λ`-modules on a scheme `X`: the derived
category `D(Sh(X, Λ))` of the abelian category `EtaleModules Λ X` of sheaves of `Λ`-modules on
the small étale site of `X`. -/
@[weil "def_fka2_etale_derived_categories"]
abbrev EtaleDerivedCategory :=
  DerivedCategory (EtaleModules.{u, r} Λ X)

end Stacks.EtaleCohomology
