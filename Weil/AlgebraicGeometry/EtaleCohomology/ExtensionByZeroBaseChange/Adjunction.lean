module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ExtensionByZeroEtale
public import Weil.Attr

/-!
# Extension by zero is left adjoint to restriction

Let `f : X ⟶ Y` be an étale morphism of schemes and `Λ` a ring. For a sheaf `F` of `Λ`-modules
on the small étale site of `X`, let `η_F : F ⟶ (f_! F)|_X` be the unit of extension by zero.
For every sheaf `G` of `Λ`-modules on the small étale site of `Y`, the map
`Hom(f_! F, G) → Hom(F, G|_X)`, `ψ ↦ ψ|_X ∘ η_F`, is bijective: extension by zero `f_!` is left
adjoint to restriction `G ↦ G|_X`, with unit `η`.

## Main results

* `AlgebraicGeometry.bijective_etaleModuleExtensionByZero_unit_comp_map`: the bijection on
  Mathlib's small étale site `X.Etale`, where the extension by zero
  `Stacks.EtaleCohomology.etaleModuleExtensionByZero` is defined.
* `AlgebraicGeometry.bijective_moduleExtensionByZero_unit_comp_map`: the same bijection on the
  small étale sites `SmallEtale B X hX` of a big étale site, for the étale morphism underlying an
  object `U` of the small étale site of `X`.

## Implementation notes

Both statements are the hom-set bijection of the adjunction `f_! ⊣ (-)|_X`; the map
`ψ ↦ η_F ≫ ψ|_X` is the adjunction's `homEquiv` (`CategoryTheory.Adjunction.homEquiv_unit`).
Restriction is precomposition with the functor "an étale scheme over the source is an étale
scheme over the target", so that `(G|_X)(V ⟶ X) = G(V ⟶ X ⟶ Y)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.EtaleCohomology

universe v r u

namespace AlgebraicGeometry

section MathlibSite

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- **Extension by zero is left adjoint to restriction**, on Mathlib's small étale site: for
sheaves of `Λ`-modules `F` on `X` and `G` on `Y`, the map `ψ ↦ η_F ≫ ψ|_X` from
`Hom(f_! F, G)` to `Hom(F, G|_X)` is bijective, `η` being the unit of extension by zero. -/
@[weil "lem_fk108_extension_by_zero_left_adjoint"]
theorem bijective_etaleModuleExtensionByZero_unit_comp_map (F : EtaleModules.{u, r} Λ X)
    (G : EtaleModules.{u, r} Λ Y) :
    Function.Bijective fun ψ : (etaleModuleExtensionByZero.{u, r} Λ f).obj F ⟶ G =>
      (etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F ≫
        (etaleModuleRestriction.{u, r} Λ f).map ψ := by
  convert ((etaleModuleExtensionByZeroAdj.{u, r} Λ f).homEquiv F G).bijective using 1
  funext ψ
  exact ((etaleModuleExtensionByZeroAdj.{u, r} Λ f).homEquiv_unit F G ψ).symm

end MathlibSite

section SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (Λ : Type v) [Ring Λ]

/-- **Extension by zero is left adjoint to restriction**, on the small étale sites of a big
étale site: for the étale morphism `U ⟶ X` underlying an object `U` of the small étale site of
`X`, and sheaves of `Λ`-modules `F` on `U` and `G` on `X`, the map `ψ ↦ η_F ≫ ψ|_U` from
`Hom(f_! F, G)` to `Hom(F, G|_U)` is bijective, `η` being the unit of extension by zero. -/
@[weil "lem_fk108_extension_by_zero_left_adjoint"]
theorem bijective_moduleExtensionByZero_unit_comp_map
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ))
    (G : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) :
    Function.Bijective fun ψ : (moduleExtensionByZero B X hX U Λ).obj F ⟶ G =>
      (moduleExtensionByZeroAdjunction B X hX U Λ).unit.app F ≫
        (moduleRestriction B X hX U Λ).map ψ := by
  convert ((moduleExtensionByZeroAdjunction B X hX U Λ).homEquiv F G).bijective using 1
  funext ψ
  exact ((moduleExtensionByZeroAdjunction B X hX U Λ).homEquiv_unit F G ψ).symm

end SmallEtale

end AlgebraicGeometry

end
