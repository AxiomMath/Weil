module

public import Mathlib.Algebra.Homology.Functor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleHigherDirectImageStalk
public import Weil.Attr

/-!
# The cohomology presheaves of a direct image of an injective resolution

Let `f : X ⟶ Y` be a morphism of schemes, `F` an abelian sheaf on the small étale site of `X`
and `F → J^•` an injective resolution. Applying the direct image `f_*` and forgetting the sheaf
condition gives a complex of abelian presheaves `f_* J^•` on the small étale site of `Y`; its
`i`-th cohomology presheaf `P^i_J` is `U ↦ H^i((f_* J^•)(U))`, the `i`-th cohomology of the
complex of abelian groups of sections over `U`.

Up to canonical isomorphism, `P^i_J` does not depend on `J`: it is the `i`-th right derived
functor of `F ↦ f_* F` (viewed as a presheaf) evaluated at `F`, which is
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageCohomologyPresheaf`.

## Main definitions

* `Stacks.EtaleCohomology.directImageCohomologyPresheaf`: the presheaf `P^i_J`,
  `U ↦ H^i((f_* J^•)(U))`.
* `HomologicalComplex.asFunctorCompHomologyFunctorIso`: for a complex `K` in a functor category
  `T ⥤ V` (with `V` abelian), the pointwise homology `t ↦ H^i(K(t))` is the homology `H^i(K)`
  computed in `T ⥤ V`.

## Main results

* `Stacks.EtaleCohomology.directImageCohomologyPresheafIso`: `P^i_J` is isomorphic to
  `Stacks.EtaleCohomology.smallEtaleHigherDirectImageCohomologyPresheaf f F i`, the `i`-th right
  derived functor of the underlying presheaf of the direct image evaluated at `F`.
* `Stacks.EtaleCohomology.directImageCohomologyPresheafIsoOfInjectiveResolutions`: the
  presheaves attached to two injective resolutions of `F` are canonically isomorphic.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale` with the topology
`AlgebraicGeometry.Scheme.smallEtaleTopology`, and coefficients are `AddCommGrpCat.{u + 1}` for
`X Y : Scheme.{u}`: this is the model and the universe of the direct image
`Stacks.EtaleCohomology.etaleAbelianDirectImage` and of the resolution-free presheaf
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageCohomologyPresheaf` it is compared with.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitagkiehl1988], I.2
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace HomologicalComplex

variable {T V : Type*} [Category* T] [Category* V] [Abelian V]
  {ι : Type*} {c : ComplexShape ι}

/-- For a complex `K` in the functor category `T ⥤ V`, the pointwise homology
`t ↦ H^i(K(t))` is isomorphic to the homology `H^i(K)` computed in `T ⥤ V`. -/
def asFunctorCompHomologyFunctorIso (K : HomologicalComplex (T ⥤ V) c) (i : ι) :
    K.asFunctor ⋙ homologyFunctor V c i ≅ K.homology i :=
  NatIso.ofComponents (fun t => (K.sc i).mapHomologyIso ((evaluation T V).obj t)) (by
    intro t t' g
    have h := ShortComplex.homologyMap_mapNatTrans (K.sc i) ((evaluation T V).map g)
    rw [← Category.assoc] at h
    exact (Iso.eq_comp_inv _).mp h)

@[simp]
lemma asFunctorCompHomologyFunctorIso_hom_app (K : HomologicalComplex (T ⥤ V) c) (i : ι)
    (t : T) :
    (K.asFunctorCompHomologyFunctorIso i).hom.app t =
      ((K.sc i).mapHomologyIso ((evaluation T V).obj t)).hom :=
  rfl

end HomologicalComplex

namespace Stacks.EtaleCohomology

attribute [local instance] smallEtalePushforward_additive

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- The complex of abelian presheaves `f_* J^•` on the small étale site of `Y` obtained from a
resolution `F → J^•`, by applying the direct image along `f` and forgetting the sheaf
condition. -/
abbrev directImagePresheafComplex (J : InjectiveResolution F) :
    CochainComplex (Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ :=
  ((etaleAbelianDirectImage.{u, u + 1} f ⋙
    sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex _).obj
      J.cocomplex

/-- **The cohomology presheaf `P^i_J` of a direct image.** For a morphism of schemes
`f : X ⟶ Y`, an injective resolution `F → J^•` of an abelian sheaf on the small étale site of
`X` and `i : ℕ`, this is the presheaf of abelian groups on the small étale site of `Y`,
`U ↦ H^i((f_* J^•)(U))`, the `i`-th cohomology of the complex of abelian groups
`(f_* J^•)(U)`. -/
@[weil "def_fk102_direct_image_cohomology_presheaf"]
def directImageCohomologyPresheaf (J : InjectiveResolution F) (i : ℕ) :
    Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (directImagePresheafComplex f J).asFunctor ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) i

/-- The value of `P^i_J` at `U` is the `i`-th cohomology of the complex of sections
`(f_* J^•)(U)`. -/
lemma directImageCohomologyPresheaf_obj (J : InjectiveResolution F) (i : ℕ)
    (U : Y.Etaleᵒᵖ) :
    (directImageCohomologyPresheaf f J i).obj U =
      ((directImagePresheafComplex f J).asFunctor.obj U).homology i :=
  rfl

/-- The `n`-th term of the complex of sections `(f_* J^•)(U)` is `(f_* J^n)(U)`. -/
lemma directImagePresheafComplex_asFunctor_obj_X (J : InjectiveResolution F) (U : Y.Etaleᵒᵖ)
    (n : ℕ) :
    ((directImagePresheafComplex f J).asFunctor.obj U).X n =
      ((etaleAbelianDirectImage.{u, u + 1} f).obj (J.cocomplex.X n)).obj.obj U :=
  rfl

/-- `P^i_J` is the `i`-th homology, computed in the category of presheaves, of the complex of
presheaves `f_* J^•`. -/
def directImageCohomologyPresheafIsoHomology (J : InjectiveResolution F) (i : ℕ) :
    directImageCohomologyPresheaf f J i ≅ (directImagePresheafComplex f J).homology i :=
  (directImagePresheafComplex f J).asFunctorCompHomologyFunctorIso i

variable [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **`P^i_J` is the derived-functor cohomology presheaf.** For any injective resolution `J` of
`F`, the presheaf `U ↦ H^i((f_* J^•)(U))` is isomorphic to the `i`-th right derived functor of
`F ↦ f_* F` (as a presheaf) evaluated at `F`, i.e. to
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageCohomologyPresheaf f F i`. -/
def directImageCohomologyPresheafIso (J : InjectiveResolution F) (i : ℕ) :
    directImageCohomologyPresheaf f J i ≅ smallEtaleHigherDirectImageCohomologyPresheaf f F i :=
  directImageCohomologyPresheafIsoHomology f J i ≪≫
    (J.isoRightDerivedObj (etaleAbelianDirectImage.{u, u + 1} f ⋙
      sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) i).symm

/-- The cohomology presheaves attached to two injective resolutions of `F` are canonically
isomorphic. -/
def directImageCohomologyPresheafIsoOfInjectiveResolutions (J J' : InjectiveResolution F)
    (i : ℕ) :
    directImageCohomologyPresheaf f J i ≅ directImageCohomologyPresheaf f J' i :=
  directImageCohomologyPresheafIso f J i ≪≫ (directImageCohomologyPresheafIso f J' i).symm

end Stacks.EtaleCohomology
