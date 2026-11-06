module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionSheafCategory
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage

/-!
# Constructible sheaves form an abelian subcategory of the torsion sheaves

Let `X` be a scheme. The kernel and the cokernel (computed in the abelian sheaves on the small
étale site of `X`) of a morphism of constructible sheaves of abelian groups are constructible, and
so is the direct sum of two constructible sheaves. Since constructible sheaves are torsion
sheaves, they form a full subcategory of the abelian category `𝒯(X)` of torsion sheaves which
contains `0` and is closed under kernels, cokernels, finite direct sums and extensions. Hence the
constructible sheaves form an abelian category, whose inclusion into `𝒯(X)` is exact: kernels,
cokernels and exact sequences of constructible sheaves are those of `𝒯(X)`.

## Main definitions

* `AlgebraicGeometry.IsConstructibleTorsionSheaf`: the constructible sheaves, as a property of
  objects of the category of torsion sheaves.
* `AlgebraicGeometry.ConstructibleSheafCategory`: the full subcategory of `𝒯(X)` of
  constructible sheaves.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianSheaf_kernel_cokernel_biprod`: kernels, cokernels and
  binary direct sums of constructible abelian sheaves are constructible.
* `AlgebraicGeometry.isWeakSerreClass_isConstructibleTorsionSheaf`: the constructible sheaves
  form a weak Serre subcategory of `𝒯(X)`.
* `AlgebraicGeometry.ConstructibleSheafCategory.abelian`: the constructible sheaves form an
  abelian category.
* `AlgebraicGeometry.ConstructibleSheafCategory.preservesFiniteLimits_ι`,
  `AlgebraicGeometry.ConstructibleSheafCategory.preservesFiniteColimits_ι`: its kernels and
  cokernels are those of `𝒯(X)`.
* `AlgebraicGeometry.ConstructibleSheafCategory.exact_map_ι_iff`: its exact sequences are those
  of `𝒯(X)`.

## Implementation notes

The closure of constructible sheaves under kernels, cokernels and extensions in the category of
all abelian sheaves is Stacks, Tag 03RZ
(`AlgebraicGeometry.constructibleAbelianSheaf_isWeakSerreClass`), proved by restricting to the
strata of a common stratification; a direct sum is an extension. This replaces the argument of
[FK] through noetherian torsion sheaves and stalks. Since the inclusion of `𝒯(X)` into the
abelian sheaves is exact, the weak Serre class pulls back to `𝒯(X)`.

The torsion sheaves here are `AlgebraicGeometry.SmallEtale.IsTorsionSheaf` with coefficients in
`AddCommGrpCat.{u + 1}`, the universe in which constructibility on the small étale site of an
object of a big étale site `BigEtaleSite.{u}` is studied.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- **Kernels, cokernels and direct sums of constructible sheaves.** For a morphism `φ : F ⟶ G`
of constructible abelian sheaves on the small étale site of `X`, the kernel and the cokernel of
`φ` (in the abelian sheaves) and the direct sum `F ⊞ G` are constructible. -/
@[weil "lem_fk104_constructible_category_abelian"]
theorem isConstructibleAbelianSheaf_kernel_cokernel_biprod
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (hF : IsConstructibleAbelianSheaf B X F) (hG : IsConstructibleAbelianSheaf B X G) :
    IsConstructibleAbelianSheaf B X (kernel φ) ∧ IsConstructibleAbelianSheaf B X (cokernel φ) ∧
      IsConstructibleAbelianSheaf B X (F ⊞ G) :=
  ⟨isConstructibleAbelianSheaf_kernel B X φ hF hG,
    isConstructibleAbelianSheaf_cokernel B X φ hF hG,
    ObjectProperty.prop_of_iso (fun F => IsConstructibleAbelianSheaf B X F)
      (biprod.isoProd F G).symm (ObjectProperty.prop_prod _ F G hF hG)⟩

/-- The constructible sheaves, as a property of objects of the category `𝒯(X)` of torsion
sheaves on the small étale site of `X`. -/
abbrev IsConstructibleTorsionSheaf :
    ObjectProperty (SmallEtale.IsTorsionSheaf.{u + 1} B X.obj X.property).FullSubcategory :=
  ObjectProperty.inverseImage
    (fun F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
      IsConstructibleAbelianSheaf B X F)
    (SmallEtale.IsTorsionSheaf.{u + 1} B X.obj X.property).ι

/-- Every constructible abelian sheaf is an object of `𝒯(X)`, where it satisfies
`AlgebraicGeometry.IsConstructibleTorsionSheaf`. -/
theorem isConstructibleTorsionSheaf_mk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B X F) :
    IsConstructibleTorsionSheaf B X ⟨F, isTorsionSheaf_of_isConstructibleAbelianSheaf B X F hF⟩ :=
  hF

/-- **The constructible sheaves form a weak Serre subcategory of `𝒯(X)`**: they contain `0` and
are closed under isomorphisms, kernels, cokernels and extensions in the category of torsion
sheaves. -/
@[weil "lem_fk104_constructible_category_abelian"]
instance isWeakSerreClass_isConstructibleTorsionSheaf :
    (IsConstructibleTorsionSheaf B X).IsWeakSerreClass :=
  ObjectProperty.isWeakSerreClass_inverseImage _ _

/-- The full subcategory of `𝒯(X)` whose objects are the constructible sheaves. -/
abbrev ConstructibleSheafCategory : Type (u + 2) :=
  (IsConstructibleTorsionSheaf B X).FullSubcategory

namespace ConstructibleSheafCategory

/-- The inclusion of the constructible sheaves into the torsion sheaves. -/
abbrev ι : ConstructibleSheafCategory B X ⥤
    (SmallEtale.IsTorsionSheaf.{u + 1} B X.obj X.property).FullSubcategory :=
  (IsConstructibleTorsionSheaf B X).ι

/-- **The constructible sheaves form an abelian category.** It is the abelian structure of the
full subcategory of a weak Serre class of `𝒯(X)`. -/
@[weil "lem_fk104_constructible_category_abelian"]
noncomputable instance abelian : Abelian (ConstructibleSheafCategory B X) :=
  have : (IsConstructibleTorsionSheaf B X).IsClosedUnderFiniteProducts := inferInstance
  inferInstance

/-- **Kernels of constructible sheaves are those of `𝒯(X)`**: the inclusion preserves finite
limits. -/
@[weil "lem_fk104_constructible_category_abelian"]
instance preservesFiniteLimits_ι : PreservesFiniteLimits (ι B X) :=
  (IsConstructibleTorsionSheaf B X).preservesFiniteLimits_ι_of_isWeakSerreClass

/-- **Cokernels of constructible sheaves are those of `𝒯(X)`**: the inclusion preserves finite
colimits. -/
@[weil "lem_fk104_constructible_category_abelian"]
instance preservesFiniteColimits_ι : PreservesFiniteColimits (ι B X) :=
  (IsConstructibleTorsionSheaf B X).preservesFiniteColimits_ι_of_isWeakSerreClass

/-- **Exact sequences of constructible sheaves are those of `𝒯(X)`.** -/
@[weil "lem_fk104_constructible_category_abelian"]
theorem exact_map_ι_iff (T : ShortComplex (ConstructibleSheafCategory B X)) :
    (T.map (ι B X)).Exact ↔ T.Exact :=
  T.exact_map_iff_of_faithful (ι B X)

end ConstructibleSheafCategory

end AlgebraicGeometry

end
