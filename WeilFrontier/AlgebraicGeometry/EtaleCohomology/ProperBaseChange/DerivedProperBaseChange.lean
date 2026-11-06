module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.DerivedProperBaseChange
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDerivedDirectImage
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Derived

/-!
# Proper base change for bounded below complexes with torsion cohomology

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` proper, and let `K` be an object of `D_{+,tor}(X)`: a
complex of abelian sheaves on the small étale site of `X` which is cohomologically bounded below
and whose cohomology sheaves are torsion sheaves. Then the base change morphism
`g^*(Rf_* K) ⟶ Rf'_*(g'^* K)` is an isomorphism in the derived category of `Y'`.

Computed by a choice of resolutions `ι : F ⟶ I`, `q : g'^* I ⟶ J` (quasi-isomorphisms onto
K-injective complexes, for instance bounded below complexes of injectives), the base change
morphism is the image of the morphism of complexes `γ_{(ι,q)} = f'_*(q) ∘ β_I : g^* f_* I ⟶ f'_* J`;
so the statement says that `γ_{(ι,q)}` is a quasi-isomorphism.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_of_torsionPlus`: the base
  change morphism is an isomorphism at every object of `D_{+,tor}(X)`.
* `Stacks.EtaleCohomology.quasiIso_etaleAbelianResolutionBaseChange_of_isProper`: for every
  choice of resolutions of a complex `F` whose image lies in `D_{+,tor}(X)`, the base change
  morphism of complexes `γ_{(ι,q)}` is a quasi-isomorphism.

## Implementation notes

The proof is the Stacks Project's
(`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isProper`, Tag 0DDE): the
proper base change theorem for single torsion sheaves passed to bounded below complexes by a
dévissage on the truncations, which is the argument of Freitag and Kiehl.
Sheaves are abelian sheaves on Mathlib's small étale site `X.smallEtaleTopology` with values in
`AddCommGrpCat.{u + 1}`, the setting of the base change morphism
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **Proper base change for complexes.** Let `f : X ⟶ Y` be proper and `X' = Y' ×_Y X`, given as
a cartesian square with projections `f'` and `g'`. For every object `K` of `D_{+,tor}(X)` the base
change morphism `g^*(Rf_* K) ⟶ Rf'_*(g'^* K)` is an isomorphism. -/
@[weil "lem_fk108_proper_base_change_complexes"]
theorem isIso_etaleAbelianDerivedBaseChange_app_of_torsionPlus {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : Stacks.Torsion.torsionPlusCohomologyProperty X.smallEtaleTopology K) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' sq.w).app K) := by
  obtain ⟨hT, n, hn⟩ := hK
  exact isIso_etaleAbelianDerivedBaseChange_of_isProper f sq K n hn hT

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

/-- **Proper base change for complexes, through a choice of resolutions.** Let `f : X ⟶ Y` be
proper and `X' = Y' ×_Y X`. Let `F` be a complex of abelian sheaves on `X` whose image in the
derived category lies in `D_{+,tor}(X)`, and `ι : F ⟶ I`, `q : g'^* I ⟶ J` quasi-isomorphisms onto
K-injective complexes. Then the base change morphism of complexes
`γ_{(ι,q)} = f'_*(q) ∘ β_I : g^* f_* I ⟶ f'_* J` is a quasi-isomorphism. -/
@[weil "lem_fk108_proper_base_change_complexes"]
theorem quasiIso_etaleAbelianResolutionBaseChange_of_isProper {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g)
    {F I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ)}
    {J : HomologicalComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ)}
    (ι : F ⟶ I) [QuasiIso ι]
    (q : ((etaleAbelianInverseImage.{u, 0} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      J) [QuasiIso q]
    (hI : CochainComplex.IsKInjective I) (hJ : CochainComplex.IsKInjective J)
    (hF : Stacks.Torsion.torsionPlusCohomologyProperty X.smallEtaleTopology
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F))) :
    QuasiIso (etaleAbelianResolutionBaseChange.{u, 0} f g g' f' sq.w I q) := by
  have h := isIso_etaleAbelianDerivedBaseChange_app_of_torsionPlus f sq _ hF
  rw [etaleAbelianDerivedBaseChange_app_eq.{u, 0} f g g' f' sq.w ι q hI hJ] at h
  have h' : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (etaleAbelianResolutionBaseChange.{u, 0} f g g' f' sq.w I q))) := by
    set e₁ := etaleAbelianResolutionBaseChangeSourceIso.{u, 0} f g ι hI
    set e₂ := etaleAbelianResolutionBaseChangeTargetIso.{u, 0} g' f' ι q hJ
    set x := DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (etaleAbelianResolutionBaseChange.{u, 0} f g g' f' sq.w I q))
    have hx : x = e₁.hom ≫ (e₁.inv ≫ x ≫ e₂.hom) ≫ e₂.inv := by simp
    rw [hx]
    infer_instance
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff] at h'
  exact h'

end Stacks.EtaleCohomology

end

/-! ### Proper direct images of extensions by zero vanish off the image -/

/-!
# Proper direct images of extensions by zero vanish off the image

Let `f : X ⟶ Y` be a proper morphism of schemes, `i : U ⟶ X` an open immersion and `F` a
bounded below complex of abelian sheaves on `X_étale` with torsion cohomology sheaves, that is,
an object of `D_{+,tor}(U)`. Then the cohomology sheaves `R^v f_* (i_! F)` vanish at every
geometric point of `Y` lying over a point outside `f(i(U))`.

More generally, for every morphism `g : T ⟶ Y` whose image misses `f(i(U))`, the inverse image
`g⁻¹ R^v f_* (i_! F)` is zero. Indeed, form the cartesian square with `g' : X_T ⟶ X` and
`f' : X_T ⟶ T`. The complex `i_! F` is bounded below with torsion cohomology sheaves
`H^m(i_! F) = i_! H^m(F)`, so the proper base change theorem for complexes gives
`g⁻¹ Rf_* (i_! F) ≅ Rf'_* (g'⁻¹ i_! F)`; and the image of `g'` misses `i(U)`, so the cohomology
sheaves `g'⁻¹ i_! H^m(F)` of `g'⁻¹ i_! F` vanish. Taking for `g` a geometric point
`y : Spec Ω ⟶ Y` gives the statement on stalks, the stalk of a sheaf at `y` being the stalk of
its inverse image to `Spec Ω` at the canonical point.

## Main results

* `AlgebraicGeometry.isZero_etaleAbelianInverseImage_homology_derivedDirectImage_extensionByZero`:
  `g⁻¹ R^v f_* (i_! F) = 0` when the image of `g` misses `f(i(U))`.
* `AlgebraicGeometry.isZero_sheafFiber_homology_derivedDirectImage_extensionByZero`:
  `(R^v f_* (i_! F))_y = 0` for a geometric point `y` over a point outside `f(i(U))`.

## Implementation notes

The sheaves live on Mathlib's small étale site `U.smallEtaleTopology` with coefficients in
`AddCommGrpCat.{u + 1}`, the setting of the proper base change theorem for complexes,
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isProper` (Stacks, Tag 0DDE).
`Rf_*` is the derived direct image `Stacks.EtaleCohomology.etaleAbelianDerivedDirectImage` and
`R^v f_*` its `v`-th cohomology sheaf; `i_!` is `AlgebraicGeometry.etaleDerivedExtensionByZero`.
Geometric points are morphisms `Spec Ω ⟶ Y` with `Ω` separably closed, as in the source, and
the stalk is the fibre functor of `AlgebraicGeometry.Scheme.pointSmallEtale`.

The source argues by dévissage to single torsion sheaves and the proper base change theorem for
sheaves, then computes stalks of `g'⁻¹ i_! H` one geometric point at a time. Here the proper base
change theorem for bounded below complexes with torsion cohomology is applied to `i_! F`
directly, and `g'⁻¹ i_! H = 0` is the adjunction argument
`Stacks.EtaleCohomology.isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl], I.8.
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {U X Y : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : X ⟶ Y)

/-- An object of the derived category of abelian sheaves on the small étale site all of whose
cohomology sheaves vanish is zero. -/
private lemma isZero_of_forall_isZero_homology {S : Scheme.{u}}
    (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor _ n).obj K)) : IsZero K := by
  open ZeroObject in
  have : IsIso (0 : K ⟶ 0) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    exact ⟨0, (hK n).eq_of_src _ _,
      (((DerivedCategory.homologyFunctor _ n).map_isZero (isZero_zero _))).eq_of_src _ _⟩
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

/-- The cohomology sheaves of `i_! F` are the extensions by zero of those of `F`. -/
def homologyEtaleDerivedExtensionByZeroIso
    (F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).obj ((etaleDerivedExtensionByZero.{0} i).obj F) ≅
      (extensionByZero.{u, 0} i).obj ((DerivedCategory.homologyFunctor _ n).obj F) :=
  ((extensionByZero.{u, 0} i).mapDerivedCategoryHomologyIso n).app F

/-- Extension by zero along an open immersion preserves `D_{+,tor}`. -/
lemma torsionPlusCohomologyProperty_etaleDerivedExtensionByZero_obj
    {F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hF : Stacks.Torsion.torsionPlusCohomologyProperty U.smallEtaleTopology F) :
    Stacks.Torsion.torsionPlusCohomologyProperty X.smallEtaleTopology
      ((etaleDerivedExtensionByZero.{0} i).obj F) := by
  rw [Stacks.Torsion.torsionPlusCohomologyProperty_iff] at hF ⊢
  obtain ⟨hT, n₀, hn₀⟩ := hF
  refine ⟨fun n => ?_, n₀, fun n hn => ?_⟩
  · exact (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      (homologyEtaleDerivedExtensionByZeroIso i F n).symm
      (torsionSheafProperty_extensionByZero.{u, 0} i _ (hT n))
  · exact ((extensionByZero.{u, 0} i).map_isZero (hn₀ n hn)).of_iso
      (homologyEtaleDerivedExtensionByZeroIso i F n)

variable [IsProper f]

/-- **Proper direct images of extensions by zero vanish off the image.** Let `f : X ⟶ Y` be
proper, `i : U ⟶ X` an open immersion and `F ∈ D_{+,tor}(U)`. For every morphism `g : T ⟶ Y`
whose image misses `f(i(U))`, the inverse image `g⁻¹ R^v f_* (i_! F)` is zero for all `v`. -/
@[weil "lem_fk108_extension_by_zero_proper_direct_image_vanishes_off_image"]
theorem isZero_etaleAbelianInverseImage_homology_derivedDirectImage_extensionByZero
    (F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hF : Stacks.Torsion.torsionPlusCohomologyProperty U.smallEtaleTopology F)
    {T : Scheme.{u}} (g : T ⟶ Y) (hg : Disjoint (Set.range g.base) (Set.range (i ≫ f).base))
    (v : ℤ) :
    IsZero ((etaleAbelianInverseImage.{u, 0} g).obj
      ((DerivedCategory.homologyFunctor _ v).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
          ((etaleDerivedExtensionByZero.{0} i).obj F)))) := by
  set E := (etaleDerivedExtensionByZero.{0} i).obj F
  have hE := torsionPlusCohomologyProperty_etaleDerivedExtensionByZero_obj i hF
  obtain ⟨n₀, hn₀⟩ := hE.2
  have hGE : E.IsGE n₀ := hn₀
  have sq := IsPullback.of_hasPullback f g
  have hiso := isIso_etaleAbelianDerivedBaseChange_of_isProper f sq E n₀ hGE hE.1
  -- the inverse image of `i_! F` to `X_T` vanishes
  have hdisj : Disjoint (Set.range (pullback.fst f g).base) (Set.range i.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, rfl⟩ ⟨x, hx⟩
    refine Set.disjoint_left.1 hg ⟨(pullback.snd f g).base p, rfl⟩ ⟨x, ?_⟩
    rw [Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, pullback.condition,
      Scheme.Hom.comp_apply]
  have hZ : IsZero ((etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f g)).obj E) := by
    refine isZero_of_forall_isZero_homology _ fun n => ?_
    refine IsZero.of_iso ?_ (((etaleAbelianInverseImage.{u, 0}
      (pullback.fst f g)).mapDerivedCategoryHomologyIso n).app E)
    refine IsZero.of_iso ?_ ((etaleAbelianInverseImage.{u, 0} (pullback.fst f g)).mapIso
      (homologyEtaleDerivedExtensionByZeroIso i F n))
    exact isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, 0} _ i hdisj _
  refine IsZero.of_iso ?_ (((etaleAbelianInverseImage.{u, 0} g).mapDerivedCategoryHomologyIso
    v).app _).symm
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ v).mapIso
    (asIso ((etaleAbelianDerivedBaseChange.{u, 0} f g _ _ sq.w).app E)))
  exact (DerivedCategory.homologyFunctor _ v).map_isZero
    ((etaleAbelianDerivedDirectImage.{u, 0} (pullback.snd f g)).map_isZero hZ)

/-- **Proper direct images of extensions by zero vanish off the image, on stalks.** Let
`f : X ⟶ Y` be proper, `i : U ⟶ X` an open immersion, `F ∈ D_{+,tor}(U)` and
`y : Spec Ω ⟶ Y` a geometric point, `Ω` separably closed, over a point not in `f(i(U))`.
Then the stalk `(R^v f_* (i_! F))_y` is zero for all `v`. -/
@[weil "lem_fk108_extension_by_zero_proper_direct_image_vanishes_off_image"]
theorem isZero_sheafFiber_homology_derivedDirectImage_extensionByZero
    (F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hF : Stacks.Torsion.torsionPlusCohomologyProperty U.smallEtaleTopology F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (hy : Disjoint (Set.range y.base) (Set.range (i ≫ f).base)) (v : ℤ) :
    IsZero ((Scheme.pointSmallEtale y).sheafFiber.obj
      ((DerivedCategory.homologyFunctor _ v).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
          ((etaleDerivedExtensionByZero.{0} i).obj F)))) := by
  have e := smallEtalePullbackStalkAbIso y (𝟙 (Spec (.of Ω)))
  rw [Category.id_comp] at e
  refine IsZero.of_iso ?_ (e.symm.app _)
  refine (smallEtaleStalkAb (𝟙 (Spec (.of Ω)))).map_isZero ?_
  exact (isZero_etaleAbelianInverseImage_homology_derivedDirectImage_extensionByZero
    i f F hF y hy v).of_iso ((smallEtalePullbackAbIsoInverseImage y).app _)

/-- **Proper direct images of extensions by zero vanish off the image, for the classical derived
functors.** The same statement with `R^v f_*` the `v`-th classical right derived functor
`CategoryTheory.Functor.rightDerivedFunctorPlusHomology` of the direct image on the bounded below
derived category, applied to `i_! F ∈ D⁺(X)`. -/
@[weil "lem_fk108_extension_by_zero_proper_direct_image_vanishes_off_image"]
theorem isZero_sheafFiber_rightDerivedFunctorPlusHomology_extensionByZero
    (F : DerivedCategory (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hF : Stacks.Torsion.torsionPlusCohomologyProperty U.smallEtaleTopology F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (hy : Disjoint (Set.range y.base) (Set.range (i ≫ f).base)) (v : ℤ) :
    IsZero ((Scheme.pointSmallEtale y).sheafFiber.obj
      (((etaleAbelianDirectImage.{u, 0} f).rightDerivedFunctorPlusHomology v).obj
        ⟨(etaleDerivedExtensionByZero.{0} i).obj F,
          (torsionPlusCohomologyProperty_etaleDerivedExtensionByZero_obj i hF).2⟩)) := by
  have : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale.{u, 0} X
  obtain ⟨n₀, hn₀⟩ := (torsionPlusCohomologyProperty_etaleDerivedExtensionByZero_obj i hF).2
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f)
    (etaleAbelianDerivedDirectImageUnit.{u, 0} f)
    (Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective _ _ _
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective)
    ⟨(etaleDerivedExtensionByZero.{0} i).obj F,
      (torsionPlusCohomologyProperty_etaleDerivedExtensionByZero_obj i hF).2⟩ n₀ hn₀
  exact (isZero_sheafFiber_homology_derivedDirectImage_extensionByZero i f F hF y hy v).of_iso
    ((Scheme.pointSmallEtale y).sheafFiber.mapIso
      ((DerivedCategory.homologyFunctor _ v).mapIso e.symm))

end AlgebraicGeometry

end
