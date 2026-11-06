module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import Weil.Attr

/-!
# Extension by zero along a composite of étale morphisms

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be étale morphisms of schemes and `Λ` a ring. Extension by zero
of sheaves of `Λ`-modules on the small étale sites satisfies `(g ∘ f)_! ≅ g_! ∘ f_!`. Both sides
are left adjoint to restriction along `g ∘ f`, since restriction along `g ∘ f` is restriction
along `g` followed by restriction along `f`; the isomorphism is the one induced, by the Yoneda
lemma, by the composite bijection
`Hom(g_! f_! F, G) ≃ Hom(f_! F, G|_Y) ≃ Hom(F, (G|_Y)|_X) ≃ Hom(F, G|_X) ≃ Hom((g ∘ f)_! F, G)`.

The isomorphism itself is the Stacks Project's
`Stacks.EtaleCohomology.etaleModuleExtensionByZeroCompIso`. This file records that it is the
isomorphism induced by the composite of the adjunction bijections, which is the form in which
it is used.

## Main results

* `AlgebraicGeometry.etaleModuleExtensionByZeroAdj_homEquiv_compIso_hom_app_comp`: under the
  adjunction bijections, precomposition with `(g ∘ f)_! F ≅ g_! f_! F` is the composite of the
  bijections for `g`, then for `f`, then the identification `(G|_Y)|_X ≅ G|_X`.
* `AlgebraicGeometry.etaleModuleExtensionByZeroAdj_unit_app_comp_map_compIso_hom_app`: the
  same statement for the units of the adjunctions.

## Implementation notes

The construction lives on Mathlib's small étale site `X.Etale` with the topology
`X.smallEtaleTopology`, where the Stacks Project's extension by zero
`Stacks.EtaleCohomology.etaleModuleExtensionByZero` is defined, with coefficients in
`ModuleCat.{max (u + 1) r} Λ`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public section

open CategoryTheory Stacks.EtaleCohomology

universe r u

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

namespace AlgebraicGeometry

variable (Λ : Type r) [Ring Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Etale f] [Etale g]

/-- The unit of the extension-by-zero adjunction for `g ∘ f`, followed by the restriction of the
isomorphism `(g ∘ f)_! F ≅ g_! f_! F`, is the unit for `f`, then the restriction to `X` of the
unit for `g`, then the identification `(G|_Y)|_X ≅ G|_X`. -/
@[weil "lem_fk108_extension_by_zero_comp"]
theorem etaleModuleExtensionByZeroAdj_unit_app_comp_map_compIso_hom_app
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (f ≫ g)).unit.app F ≫
        (etaleModuleRestriction.{u, r} Λ (f ≫ g)).map
          ((etaleModuleExtensionByZeroCompIso.{u, r} Λ f g).hom.app F) =
      (etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F ≫
        (etaleModuleRestriction.{u, r} Λ f).map
          ((etaleModuleExtensionByZeroAdj.{u, r} Λ g).unit.app
            ((etaleModuleExtensionByZero.{u, r} Λ f).obj F)) ≫
        (etaleModuleRestrictionCompIso.{u, r} Λ f g).hom.app _ := by
  simp [etaleModuleExtensionByZeroCompIso]

/-- **Extension by zero composes** ([FK], I.8): for étale `f : X ⟶ Y` and `g : Y ⟶ Z`, the
isomorphism `(g ∘ f)_! F ≅ g_! f_! F` is the one induced by the composite bijection
`Hom(g_! f_! F, G) ≃ Hom(f_! F, G|_Y) ≃ Hom(F, (G|_Y)|_X) ≃ Hom(F, G|_X) ≃ Hom((g ∘ f)_! F, G)`:
precomposing `ψ : g_! f_! F ⟶ G` with it and taking the adjoint for `g ∘ f` gives the adjoint of
`ψ` for `g`, then for `f`, followed by `(G|_Y)|_X ≅ G|_X`. -/
@[weil "lem_fk108_extension_by_zero_comp"]
theorem etaleModuleExtensionByZeroAdj_homEquiv_compIso_hom_app_comp
    (F : EtaleModules.{u, r} Λ X) (G : EtaleModules.{u, r} Λ Z)
    (ψ : (etaleModuleExtensionByZero.{u, r} Λ g).obj
      ((etaleModuleExtensionByZero.{u, r} Λ f).obj F) ⟶ G) :
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (f ≫ g)).homEquiv F G
        ((etaleModuleExtensionByZeroCompIso.{u, r} Λ f g).hom.app F ≫ ψ) =
      (etaleModuleExtensionByZeroAdj.{u, r} Λ f).homEquiv F _
          ((etaleModuleExtensionByZeroAdj.{u, r} Λ g).homEquiv _ G ψ) ≫
        (etaleModuleRestrictionCompIso.{u, r} Λ f g).hom.app G := by
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [etaleModuleExtensionByZeroAdj_unit_app_comp_map_compIso_hom_app, Category.assoc,
    Functor.map_comp]
  have h := (etaleModuleRestrictionCompIso.{u, r} Λ f g).hom.naturality ψ
  simp only [Functor.comp_map] at h
  rw [← h]

end AlgebraicGeometry
