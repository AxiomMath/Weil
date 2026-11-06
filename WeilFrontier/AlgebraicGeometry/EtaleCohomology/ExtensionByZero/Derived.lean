module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Derived
public import Weil.Attr

/-!
# Termwise extension by zero preserves quasi-isomorphisms

Let `f : X ⟶ Y` be an étale morphism of schemes. Extension by zero `f_!` from abelian sheaves on
the small étale site of `X` to those on `Y` is additive and exact. Applied termwise to complexes
it is `CategoryTheory.Functor.mapHomologicalComplex`, and, being exact, it preserves homology; so
it sends quasi-isomorphisms of complexes to quasi-isomorphisms. Consequently the composite of
the termwise functor with the localization `Q` to the derived category inverts
quasi-isomorphisms, and the functor `f_! : D(X) ⥤ D(Y)` it induces
(`AlgebraicGeometry.etaleDerivedExtensionByZero`) is well defined.

## Main results

* `AlgebraicGeometry.quasiIso_map_mapHomologicalComplex_extensionByZero`: on Mathlib's small
  étale site, the termwise extension by zero along an étale `f` sends a quasi-isomorphism to a
  quasi-isomorphism.
* `AlgebraicGeometry.isInvertedBy_quasiIso_mapHomologicalComplex_extensionByZero`: the termwise
  extension by zero followed by the localization inverts quasi-isomorphisms.
* `AlgebraicGeometry.SmallEtale.quasiIso_map_mapHomologicalComplex_abelianExtensionByZero`,
  `AlgebraicGeometry.SmallEtale.isInvertedBy_quasiIso_mapHomologicalComplex_abelianExtensionByZero`:
  the same on the bounded small étale sites `SmallEtale`, for the structure morphism of an object
  of `SmallEtale B X hX`.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

universe v u

namespace AlgebraicGeometry

section Abelian

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- For an étale morphism `f`, the termwise extension by zero `f_!` on complexes of abelian
sheaves on the small étale sites sends quasi-isomorphisms to quasi-isomorphisms. -/
@[weil "lem_fk108_extension_by_zero_derived_well_defined"]
theorem quasiIso_map_mapHomologicalComplex_extensionByZero {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (((extensionByZero.{u, v} f).mapHomologicalComplex c).map φ) :=
  inferInstance

/-- For an étale morphism `f`, the termwise extension by zero followed by the localization to
the derived category of `Y` inverts quasi-isomorphisms; hence it induces the functor
`f_! : D(X) ⥤ D(Y)` (`AlgebraicGeometry.etaleDerivedExtensionByZero`). -/
@[weil "lem_fk108_extension_by_zero_derived_well_defined"]
theorem isInvertedBy_quasiIso_mapHomologicalComplex_extensionByZero
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (ComplexShape.up ℤ)).IsInvertedBy
      ((extensionByZero.{u, v} f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) := by
  intro K L φ hφ
  have : QuasiIso φ := hφ
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance

end Abelian

section SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

/-- On the bounded small étale sites, for the structure morphism `f : U ⟶ X` of an object `U` of
the small étale site of `X`, the termwise extension by zero `f_!` sends quasi-isomorphisms of
complexes of abelian sheaves to quasi-isomorphisms. -/
@[weil "lem_fk108_extension_by_zero_derived_well_defined"]
theorem SmallEtale.quasiIso_map_mapHomologicalComplex_abelianExtensionByZero {ι : Type*}
    {c : ComplexShape ι}
    {K L : HomologicalComplex
      (Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) c}
    (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso (((abelianExtensionByZero B X hX U).mapHomologicalComplex c).map φ) :=
  inferInstance

/-- On the bounded small étale sites, the termwise extension by zero followed by the
localization inverts quasi-isomorphisms; hence it induces `f_! : D(U) ⥤ D(X)`
(`AlgebraicGeometry.smallEtaleDerivedExtensionByZero`). -/
@[weil "lem_fk108_extension_by_zero_derived_well_defined"]
theorem SmallEtale.isInvertedBy_quasiIso_mapHomologicalComplex_abelianExtensionByZero
    [HasDerivedCategory (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})] :
    (HomologicalComplex.quasiIso
        (Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ)).IsInvertedBy
      ((abelianExtensionByZero B X hX U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) := by
  intro K L φ hφ
  have : QuasiIso φ := hφ
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr inferInstance

end SmallEtale

end AlgebraicGeometry
