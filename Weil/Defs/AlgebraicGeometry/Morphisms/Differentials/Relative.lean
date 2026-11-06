module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative

/-!
# The sheaf of relative differentials as sheafified Kähler differentials

For a morphism of schemes `f : X ⟶ Y`, the sheaf of relative differential forms `Ω_{X/Y}` is
the sheaf of `𝒪_X`-modules associated with the presheaf `U ↦ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}` of
Kähler differential modules, where `f⁻¹𝒪_Y` is the topological inverse image of `𝒪_Y`, a sheaf
of rings on `X` with the structural ring map `f⁻¹𝒪_Y ⟶ 𝒪_X`.

The sheaf itself is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, defined as the
sheaf of modules representing derivations of `𝒪_X` relative to `f⁻¹𝒪_Y`. This file identifies
it with the sheafification of the sectionwise Kähler differentials, compatibly with the
universal derivation, which is the description of `Ω_{X/Y}` as a sheaf associated with a
presheaf.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsIsoSheafifiedKaehler`: the sheaf of
  relative differentials of `f` is the sheafification of `U ↦ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`.
* `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation_postcomp_iso`: the isomorphism
  carries the universal relative derivation to the sheafified sectionwise differential.
* `AlgebraicGeometry.Scheme.Hom.relativeKaehlerPresheaf_obj`: the sections of the presheaf
  over an open `U` are the Kähler differentials of `𝒪_X(U)` over `(f⁻¹𝒪_Y)(U)`.

## Implementation notes

The structural map `f⁻¹𝒪_Y ⟶ 𝒪_X` is `AlgebraicGeometry.inverseImageStructureMap f`, the
adjunct of `f^♯` under the inverse image–direct image adjunction of sheaves of rings.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.2
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Grothendieck, *EGA IV*, 16.3][EGA4]
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The sections over an open `U` of the presheaf of relative Kähler differentials of
`f⁻¹𝒪_Y ⟶ 𝒪_X` are the Kähler differentials `Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`. -/
theorem relativeKaehlerPresheaf_obj (U : (Opens X)ᵒᵖ) :
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
        (inverseImageStructureMap f).hom).obj U =
      CommRingCat.KaehlerDifferential ((inverseImageStructureMap f).hom.app U) :=
  rfl

/-- **The sheaf of relative differentials is sheafified Kähler differentials.** For a morphism
of schemes `f : X ⟶ Y`, the sheaf of relative differentials `Ω_{X/Y}` is the sheaf of
`𝒪_X`-modules associated with the presheaf `U ↦ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`. -/
@[weil "def_fk102_relative_differentials"]
noncomputable def relativeDifferentialsIsoSheafifiedKaehler :
    f.relativeDifferentials ≅
      SheafOfModules.sectionwiseDifferentialsSheaf (inverseImageStructureMap f) :=
  SheafOfModules.moduleOfDifferentialsIsoSectionwise (inverseImageStructureMap f)

/-- The isomorphism `relativeDifferentialsIsoSheafifiedKaehler` carries the universal relative
derivation to the sectionwise differential followed by the unit of sheafification. -/
theorem universalRelativeDerivation_postcomp_iso :
    (universalRelativeDerivation f).postcomp
        (relativeDifferentialsIsoSheafifiedKaehler f).hom.val =
      SheafOfModules.sectionwiseDerivation (inverseImageStructureMap f) :=
  SheafOfModules.moduleOfDifferentialsIsoSectionwise_compatible (inverseImageStructureMap f)

end AlgebraicGeometry.Scheme.Hom
