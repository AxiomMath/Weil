module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.HomologySequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDerived
public import Weil.Attr

/-!
# The direct image with proper support of a sheaf

Let `f : X ⟶ S` be a morphism of schemes with a compactification `c = (X̄, j, f̄)`, and `Λ` a
ring. For a sheaf `F` of `Λ`-modules on the small étale site of `X`, the *direct image with
proper support* of `F` is the sheaf `f_!^c F = R⁰f_! F = H⁰(Rf_!(F[0]))` on the small étale site
of `S`, the degree-zero cohomology sheaf of the derived direct image with proper support
`Rf_! = R f̄_* ∘ j_!` of `F` placed in degree `0`.

On Mathlib's small étale sites this sheaf is `Stacks.EtaleCohomology.lowerShriekHomology Λ f c 0`.
Here it is given on the size-bounded small étale sites `AlgebraicGeometry.SmallEtale` of a big
étale site `B`, by transport along the equivalences
`AlgebraicGeometry.SmallEtale.moduleSheafEquivEtaleModules` of the categories of sheaves of
modules, and identified with `H⁰` of the derived functor
`AlgebraicGeometry.SmallEtale.derivedLowerShriek` of these sites.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properDirectImage`: the functor `F ↦ f_!^c F = R⁰f_! F` from
  sheaves of `Λ`-modules on `SmallEtale B X` to sheaves of `Λ`-modules on `SmallEtale B S`.

## Main results

* `AlgebraicGeometry.SmallEtale.properDirectImage_obj`: `f_!^c F` is `R⁰f_!` of Mathlib's small
  étale sites, applied to `F` and read back on `SmallEtale B S`.
* `AlgebraicGeometry.SmallEtale.properDirectImageIsoHomologyDerivedLowerShriek`:
  `f_!^c ≅ H⁰(Rf_!(-[0]))`, for `Rf_!` the derived direct image with proper support on the small
  étale sites of `B`.

## Implementation notes

The source defines `f_!^c F` for torsion abelian sheaves. The formula uses no torsion
hypothesis, so the functor here is defined on all sheaves of `Λ`-modules, for any ring `Λ`; the
source's functor is its value on torsion sheaves for `Λ = ℤ`. The compactification is an
explicit argument, as for `AlgebraicGeometry.SmallEtale.derivedLowerShriek`. The source writes
`f_!` for this sheaf; the superscript `c` of the prose distinguishes it from the extension by zero
along an étale morphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X S : B.Scheme} (f : X.obj ⟶ S.obj) (c : f.Compactification)
  (Λ : Type) [Ring Λ]

/-- Sheafification of presheaves of `Λ`-modules in the universe `u + 1`, for `Λ : Type`: the
instance `AlgebraicGeometry.SmallEtale.hasSheafify_moduleSheaf` at the universes `v = r = 0`,
which instance search cannot read off `ModuleCat.{u + 1} Λ`. -/
instance (priority := high) hasSheafify_moduleSheaf_zero (T : B.Scheme) :
    HasSheafify (SmallEtale.topology B T.obj T.property) (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleSheaf.{u, 0, 0} B T Λ

/-- **The direct image with proper support** `f_!^c F = R⁰f_! F` of a sheaf `F` of `Λ`-modules on
the small étale site of `X`, for a morphism `f : X ⟶ S` with compactification `c`: the sheaf
`Stacks.EtaleCohomology.lowerShriekHomology Λ f c 0` of Mathlib's small étale sites, transported
to the small étale sites of `B`. -/
@[weil "def_fk108_proper_direct_image_sheaf"]
def properDirectImage : ModuleSheaf.{u, 0, 0} B X Λ ⥤ ModuleSheaf.{u, 0, 0} B S Λ :=
  (moduleSheafEquivEtaleModules B Λ X).functor ⋙
    Stacks.EtaleCohomology.lowerShriekHomology Λ f c 0 ⋙
    (moduleSheafEquivEtaleModules B Λ S).inverse

/-- `f_!^c F` is `R⁰f_!` of Mathlib's small étale sites, applied to `F`, read back on
`SmallEtale B S`. -/
theorem properDirectImage_obj (F : ModuleSheaf.{u, 0, 0} B X Λ) :
    (properDirectImage f c Λ).obj F =
      (moduleSheafEquivEtaleModules B Λ S).inverse.obj
        ((Stacks.EtaleCohomology.lowerShriekHomology Λ f c 0).obj
          ((moduleSheafEquivEtaleModules B Λ X).functor.obj F)) :=
  rfl

/-- The functor induced on bounded below derived categories by an exact functor `F` commutes with
the cohomology functors: `Hⁿ(F(K)) ≅ F(Hⁿ(K))`. -/
def _root_.CategoryTheory.Functor.mapDerivedCategoryPlusHomologyFunctorIso {A C : Type*}
    [Category* A] [Category* C] [Abelian A] [Abelian C] [HasDerivedCategory A]
    [HasDerivedCategory C] (F : A ⥤ C) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (n : ℤ) :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      DerivedCategory.Plus.homologyFunctor A n ⋙ F :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι (F.mapDerivedCategoryHomologyFunctorIso n)

/-- **`f_!^c = R⁰f_!`**: the direct image with proper support is the degree-zero cohomology
sheaf `H⁰(Rf_!(F[0]))` of the derived direct image with proper support
`AlgebraicGeometry.SmallEtale.derivedLowerShriek` of the small étale sites of `B`, applied to
`F` placed in degree `0`. -/
@[weil "def_fk108_proper_direct_image_sheaf"]
def properDirectImageIsoHomologyDerivedLowerShriek :
    properDirectImage f c Λ ≅
      Stacks.EtaleCohomology.singlePlus (ModuleSheaf.{u, 0, 0} B X Λ) ⋙
        DerivedCategory.Plus.Q ⋙ derivedLowerShriek.{u, 0} Λ f c ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleSheaf.{u, 0, 0} B S Λ) 0 :=
  Functor.isoWhiskerLeft
      ((moduleSheafEquivEtaleModules B Λ X).functor ⋙
        Stacks.EtaleCohomology.singlePlus _ ⋙ DerivedCategory.Plus.Q ⋙
          Stacks.EtaleCohomology.derivedLowerShriek.{u, 0} f c Λ)
      ((moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlusHomologyFunctorIso
        0).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (Stacks.EtaleCohomology.singlePlus _)
          (moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlusQIso ≪≫
        Functor.isoWhiskerRight
          (Stacks.EtaleCohomology.singlePlusMapIso (moduleSheafEquivEtaleModules B Λ X).functor)
          DerivedCategory.Plus.Q).symm
      (Stacks.EtaleCohomology.derivedLowerShriek.{u, 0} f c Λ ⋙
        (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleSheaf.{u, 0, 0} B S Λ) 0)

end AlgebraicGeometry.SmallEtale
