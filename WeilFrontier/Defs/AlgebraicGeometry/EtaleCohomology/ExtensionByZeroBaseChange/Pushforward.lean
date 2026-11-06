module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import WeilFrontier.AlgebraicGeometry.Sites.EtalePoint
public import Weil.Attr

/-!
# Canonical homomorphisms from extension by zero to a direct image

Let `X ⟶ Z ⟶ Y` be morphisms of schemes, `j : X ⟶ Z` an open immersion and `f = j ≫ g`
étale, and let `F` be a sheaf of `Λ`-modules on the small étale site of `X`. For an étale
`φ : U ⟶ X`, the scheme `U` is étale over `Y` through `f ∘ φ` and over `Z` through `j ∘ φ`, and
the fibre product `U ×_Y Z` is étale over `Z` through its second projection; the sections of
the direct image `g_* (j_! F)` over `U` are the sections of `j_! F` over `U ×_Y Z`. The graph
`γ_φ = (id_U, j ∘ φ) : U ⟶ U ×_Y Z` is a morphism of étale `Z`-schemes.

A morphism `c : f_! F ⟶ g_* (j_! F)` is a *canonical homomorphism* if for every étale
`φ : U ⟶ X`, every section `s` of `F` over `U`, and every decomposition `U ×_Y Z = W ⊔ W'` into
open subschemes such that `γ_φ` is an isomorphism of `U` onto `W`, the section
`σ = c([φ, s])` of `j_! F` over `U ×_Y Z` vanishes on `W'` and restricts along `γ_φ` to the
section `[φ, s]` of `j_! F` over `U`.

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.graphToBaseChange`: the graph `γ_φ : U ⟶ U ×_Y Z` as a
  morphism of the small étale site of `Z`.
* `AlgebraicGeometry.IsCanonicalExtensionByZeroToPushforward`: the predicate that a morphism
  `f_! F ⟶ g_* (j_! F)` is a canonical homomorphism.

## Main results

* `AlgebraicGeometry.IsCanonicalExtensionByZeroToPushforward.map_compl_eq_zero` and
  `AlgebraicGeometry.IsCanonicalExtensionByZeroToPushforward.map_graph_eq`: the two halves of
  the defining condition.

## Implementation notes

The statement lives on Mathlib's small étale site `X.Etale`, where the extension by zero
`Stacks.EtaleCohomology.etaleModuleExtensionByZero` and the direct image
`Stacks.EtaleCohomology.etaleModuleDirectImage` of sheaves of `Λ`-modules are defined; abelian
sheaves are the case `Λ = ℤ`.

The section `[φ, s]` of `f_! F` over `U →^{f φ} Y`, the image of `s` placed in the summand of
`P_f F` indexed by `φ`, is the image of `s` under the unit `F ⟶ f^{-1} f_! F` of the adjunction
`f_! ⊣ f^{-1}` (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj`), evaluated at `U`: the
unit of the sheafified left Kan extension is the inclusion of that summand followed by
sheafification. The same holds for `[φ, s]` as a section of `j_! F` over `U →^{j φ} Z`.

The condition that `σ|_W` corresponds to `[φ, s]` under the isomorphism `γ_φ : U ≅ W` is stated
as the equality of the restriction of `σ` along `γ_φ` with `[φ, s]`; for an isomorphism
`e : U ≅ W` with `e ≫ ι_W = γ_φ` the two conditions are equivalent, the restriction along `γ_φ`
being the restriction to `W` followed by the transport along `e`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8, p. 85.
* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.EtaleCohomology

universe r u

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {X Z Y : Scheme.{u}} (j : X ⟶ Z) (g : Z ⟶ Y) (f : X ⟶ Y) [Etale j] [Etale f]

/-- The graph `γ_φ = (id_U, j ∘ φ) : U ⟶ U ×_Y Z` of an étale `φ : U ⟶ X`, where `f = j ≫ g`,
as a morphism of the small étale site of `Z` from `U →^{j φ} Z` to the base change of
`U →^{f φ} Y` along `g`. -/
def graphToBaseChange (fac : j ≫ g = f) (U : X.Etale) :
    (smallEtaleCompose j).obj U ⟶ (smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 U.left) (U.hom ≫ j) (by simp [← fac]))
    (pullback.lift_snd _ _ _) trivial

@[simp]
theorem graphToBaseChange_left (fac : j ≫ g = f) (U : X.Etale) :
    (graphToBaseChange j g f fac U).left =
      pullback.lift (𝟙 U.left) (U.hom ≫ j) (by simp [← fac]) :=
  rfl

end Scheme.Etale

open Scheme.Etale

variable (Λ : Type r) [Ring Λ] {X Z Y : Scheme.{u}} (j : X ⟶ Z) (g : Z ⟶ Y) (f : X ⟶ Y)
  [IsOpenImmersion j] [Etale f]

/-- A morphism `c : f_! F ⟶ g_* (j_! F)`, for an open immersion `j : X ⟶ Z` and `f = j ≫ g`
étale, is a *canonical homomorphism* for `(j, g, F)` if for every étale `φ : U ⟶ X`, every
section `s` of `F` over `U`, and every decomposition `U ×_Y Z = W ⊔ W'` into open subschemes
such that the graph `γ_φ : U ⟶ U ×_Y Z` is an isomorphism of `U` onto `W`, the section
`σ = c([φ, s])` of `j_! F` over `U ×_Y Z` restricts to zero on `W'` and restricts along `γ_φ`
to the section `[φ, s]` of `j_! F` over `U →^{j φ} Z`. -/
@[weil "def_fk108_extension_by_zero_to_pushforward_map"]
def IsCanonicalExtensionByZeroToPushforward (fac : j ≫ g = f) (F : EtaleModules.{u, r} Λ X)
    (c : (etaleModuleExtensionByZero.{u, r} Λ f).obj F ⟶
      (etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F)) :
    Prop :=
  ∀ (U : X.Etale) (s : F.obj.obj (op U))
    (W W' : ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U)).left.Opens),
    IsCompl W W' →
    (∃ e : U.left ≅ W.toScheme, e.hom ≫ W.ι = (graphToBaseChange j g f fac U).left) →
    ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map (ofOpensι _ W').op
        ((c.hom.app (op ((smallEtaleCompose f).obj U))).hom
          (((etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F).hom.app (op U) s)) = 0 ∧
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map
          (graphToBaseChange j g f fac U).op
        ((c.hom.app (op ((smallEtaleCompose f).obj U))).hom
          (((etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F).hom.app (op U) s)) =
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F).hom.app (op U) s

namespace IsCanonicalExtensionByZeroToPushforward

variable {Λ j g f} {fac : j ≫ g = f} {F : EtaleModules.{u, r} Λ X}
  {c : (etaleModuleExtensionByZero.{u, r} Λ f).obj F ⟶
    (etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F)}

/-- For a canonical homomorphism `c`, the section `c([φ, s])` vanishes on the complement `W'` of
the image `W` of the graph of `φ`. -/
theorem map_compl_eq_zero (hc : IsCanonicalExtensionByZeroToPushforward Λ j g f fac F c)
    (U : X.Etale) (s : F.obj.obj (op U))
    (W W' : ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U)).left.Opens)
    (hWW' : IsCompl W W') (e : U.left ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (graphToBaseChange j g f fac U).left) :
    ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map (ofOpensι _ W').op
        ((c.hom.app (op ((smallEtaleCompose f).obj U))).hom
          (((etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F).hom.app (op U) s)) = 0 :=
  (hc U s W W' hWW' ⟨e, he⟩).1

/-- For a canonical homomorphism `c`, the section `c([φ, s])` restricts along the graph of `φ`
to `[φ, s]`, provided the image of the graph is open with open complement. -/
theorem map_graph_eq (hc : IsCanonicalExtensionByZeroToPushforward Λ j g f fac F c)
    (U : X.Etale) (s : F.obj.obj (op U))
    (W W' : ((smallEtaleBaseChange g).obj ((smallEtaleCompose f).obj U)).left.Opens)
    (hWW' : IsCompl W W') (e : U.left ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (graphToBaseChange j g f fac U).left) :
    ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map
          (graphToBaseChange j g f fac U).op
        ((c.hom.app (op ((smallEtaleCompose f).obj U))).hom
          (((etaleModuleExtensionByZeroAdj.{u, r} Λ f).unit.app F).hom.app (op U) s)) =
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app F).hom.app (op U) s :=
  (hc U s W W' hWW' ⟨e, he⟩).2

end IsCanonicalExtensionByZeroToPushforward

end AlgebraicGeometry
