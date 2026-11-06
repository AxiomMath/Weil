module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import Weil.Attr

/-!
# Extension by zero on derived categories of étale sheaves

Let `f : X ⟶ Y` be an étale morphism of schemes. Extension by zero `f_!` from sheaves of abelian
groups on the small étale site of `X` to those on `Y` is an exact additive functor. Applied
termwise it sends a complex `K` to the complex with terms `f_! (K n)` and differentials `f_! (d n)`,
and a morphism of complexes to the termwise morphism; this is
`CategoryTheory.Functor.mapHomologicalComplex`. Being exact, it sends quasi-isomorphisms to
quasi-isomorphisms, so it induces a functor `f_! = R f_! : D(X) ⥤ D(Y)` on derived categories,
`CategoryTheory.Functor.mapDerivedCategory`, characterised by the isomorphism
`Q ⋙ f_! ≅ f_!^{termwise} ⋙ Q` with the localization functors `Q`.

## Main definitions

* `AlgebraicGeometry.etaleDerivedExtensionByZero`: `f_! : D(X) ⥤ D(Y)` for abelian sheaves on
  the small étale sites, the functor induced by the termwise extension by zero.
* `AlgebraicGeometry.etaleDerivedExtensionByZeroFactors`: the functor induced by the termwise
  extension by zero on complexes, composed with the localization, is the localization composed
  with `f_!`.
* `AlgebraicGeometry.etaleModuleDerivedExtensionByZeroUnboundedFactors`: the same for sheaves of
  `Λ`-modules, with the derived extension by zero
  `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnbounded`.
* `AlgebraicGeometry.smallEtaleDerivedExtensionByZero`: `f_!` on derived categories of abelian
  sheaves on the bounded small étale sites `SmallEtale`, for `f` the structure morphism of an
  object of `SmallEtale B X hX`.

## Implementation notes

The termwise functor on complexes is Mathlib's
`(Stacks.EtaleCohomology.extensionByZero f).mapHomologicalComplex (ComplexShape.up ℤ)`; its
terms and differentials are given by `CategoryTheory.Functor.mapHomologicalComplex_obj_X` and
`CategoryTheory.Functor.mapHomologicalComplex_obj_d`, so no new functor on complexes is
introduced.

For sheaves of `Λ`-modules the Stacks Project defines the derived extension by zero as a total
right derived functor; `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedIso`
identifies it with the functor induced by the termwise extension by zero, and the factorisation
through the localization is transported along that isomorphism.

The coefficient categories are those of `Stacks.EtaleCohomology.extensionByZero`:
`AddCommGrpCat.{max (u + 1) v}` on Mathlib's small étale site, and `AddCommGrpCat.{u + 1}` on the
bounded small étale site.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

universe v r u

namespace AlgebraicGeometry

section Abelian

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Extension by zero `f_! : D(X) ⥤ D(Y)` along an étale morphism `f`, on the derived categories
of abelian sheaves on the small étale sites: the functor induced by extension by zero applied
termwise to complexes, which is exact. -/
@[weil "def_fk108_extension_by_zero_derived"]
abbrev etaleDerivedExtensionByZero :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (extensionByZero.{u, v} f).mapDerivedCategory

/-- The derived extension by zero is induced by the termwise extension by zero: the localization
of the complex `(f_! K n, f_! d n)` is `f_!` of the localization of `K`, naturally in `K`. -/
@[weil "def_fk108_extension_by_zero_derived"]
def etaleDerivedExtensionByZeroFactors :
    DerivedCategory.Q ⋙ etaleDerivedExtensionByZero.{v} f ≅
      (extensionByZero.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (extensionByZero.{u, v} f).mapDerivedCategoryFactors

end Abelian

section Modules

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- For sheaves of `Λ`-modules, the derived extension by zero
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnbounded` is induced by the termwise
extension by zero: the localization of the complex `(f_! K n, f_! d n)` is `f_!` of the
localization of `K`, naturally in `K`. -/
@[weil "def_fk108_extension_by_zero_derived"]
def etaleModuleDerivedExtensionByZeroUnboundedFactors :
    DerivedCategory.Q ⋙ etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ f ≅
      (etaleModuleExtensionByZero.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ f) ≪≫
    (etaleModuleExtensionByZero.{u, r} Λ f).mapDerivedCategoryFactors

end Modules

section SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  [HasDerivedCategory (Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})]

/-- Extension by zero `f_! : D(U) ⥤ D(X)` on the derived categories of abelian sheaves on the
bounded small étale sites, for `f : U ⟶ X` the structure morphism of an object `U` of the small
étale site of `X`: the functor induced by the termwise extension by zero. -/
@[weil "def_fk108_extension_by_zero_derived"]
abbrev smallEtaleDerivedExtensionByZero :
    DerivedCategory (Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
  (abelianExtensionByZero B X hX U).mapDerivedCategory

/-- The derived extension by zero on the bounded small étale sites is induced by the termwise
extension by zero. -/
@[weil "def_fk108_extension_by_zero_derived"]
def smallEtaleDerivedExtensionByZeroFactors :
    DerivedCategory.Q ⋙ smallEtaleDerivedExtensionByZero B X hX U ≅
      (abelianExtensionByZero B X hX U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (abelianExtensionByZero B X hX U).mapDerivedCategoryFactors

end SmallEtale

end AlgebraicGeometry
