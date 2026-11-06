module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# Derived global sections of étale sheaves of modules

Let `X` be a scheme and `Λ` a ring. Global sections `Γ(X, -) : G ↦ G(X)` is a left exact
functor from sheaves of `Λ`-modules on the small étale site of `X` to `Λ`-modules, and the
source has enough injectives. Its right derived functor on the bounded below derived category
is `RΓ(X, -) : D⁺(X, Λ) ⥤ D(Λ)`, computed by applying `Γ(X, -)` degreewise to a bounded below
complex of injectives. This file records it with values in the unbounded derived category of
`Λ`-modules, the bounded below derived category of `Λ`-modules being a full subcategory of it.
For `Λ = ℤ` it is derived global sections of abelian étale sheaves.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsι`: `RΓ(X, -) : D⁺(X, Λ) ⥤ D(Λ)`,
  the bounded below right derived functor
  `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSections` of `Γ(X, -)` followed by the
  inclusion `DerivedCategory.Plus.ι` of `D⁺(Λ)` into `D(Λ)`.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsιUnit`: the comparison morphism
  from `Γ(X, -)` applied degreewise to `RΓ(X, -)`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedGlobalSectionsιUnit_app`: on a bounded below
  complex of injective sheaves the comparison morphism is an isomorphism, i.e. `RΓ(X, -)` is
  computed by injective resolutions.
* `Stacks.EtaleCohomology.etaleModuleDerivedGlobalSections_isRightDerivedFunctor`: the bounded
  below functor is a right derived functor of `Γ(X, -)` with respect to quasi-isomorphisms.

## Implementation notes

The sheaf category is `Stacks.EtaleCohomology.EtaleModules Λ X`, sheaves on Mathlib's small
étale site `X.smallEtaleTopology` with coefficients `ModuleCat.{max (u + 1) r} Λ`; its enough
injectives is `Stacks.EtaleCohomology.etaleModules_enoughInjectives`. The derived categories are
those of `CategoryTheory.HasDerivedCategory.standard`, as in the reused development.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A II][FK]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

/-- Derived global sections `RΓ(X, -) : D⁺(X, Λ) ⥤ D(Λ)` of sheaves of `Λ`-modules on the
small étale site of `X`: the bounded below right derived functor of `Γ(X, -)`, with values in
the unbounded derived category of `Λ`-modules. -/
@[weil "not_fka2_derived_global_sections"]
abbrev etaleModuleDerivedGlobalSectionsι :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (ModuleCat.{max (u + 1) r} Λ) :=
  etaleModuleDerivedGlobalSections.{u, r} Λ X ⋙ DerivedCategory.Plus.ι

/-- The comparison morphism from `Γ(X, -)` applied degreewise to bounded below complexes to
`RΓ(X, -)`. -/
abbrev etaleModuleDerivedGlobalSectionsιUnit :
    (etaleModuleGlobalSections.{u, r} Λ X).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Qh ⋙ etaleModuleDerivedGlobalSectionsι.{u, r} Λ X :=
  Functor.whiskerRight (etaleModuleGlobalSections.{u, r} Λ X).rightDerivedFunctorPlusUnit
    DerivedCategory.Plus.ι

/-- The bounded below derived global sections are a right derived functor of `Γ(X, -)` with
respect to quasi-isomorphisms. -/
theorem etaleModuleDerivedGlobalSections_isRightDerivedFunctor :
    (etaleModuleDerivedGlobalSections.{u, r} Λ X).IsRightDerivedFunctor
      (etaleModuleGlobalSections.{u, r} Λ X).rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso (EtaleModules.{u, r} Λ X)) :=
  inferInstance

/-- `RΓ(X, -)` is computed by injective resolutions: on a bounded below complex of injective
sheaves the comparison morphism is an isomorphism. -/
theorem isIso_etaleModuleDerivedGlobalSectionsιUnit_app
    (K : HomotopyCategory.Plus (InjectiveObject (EtaleModules.{u, r} Λ X))) :
    IsIso ((etaleModuleDerivedGlobalSectionsιUnit.{u, r} Λ X).app
      ((InjectiveObject.ι _).mapHomotopyCategoryPlus.obj K)) := by
  dsimp only [etaleModuleDerivedGlobalSectionsιUnit, Functor.whiskerRight_app]
  infer_instance

end Stacks.EtaleCohomology
