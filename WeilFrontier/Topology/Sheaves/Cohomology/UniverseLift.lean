/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftCohomology

/-!
# Sheaf cohomology on a topological space does not depend on the coefficient universe

Let `X` be a topological space in `TopCat.{u}` and let `F` be a sheaf of abelian groups on `X`
with groups of sections in `Type u`. Raising the universe of every group of sections gives a
sheaf `F ⋙ uliftFunctor` with groups of sections in `Type (max u w)`, and

  `H ^ n (X, F) ≃+ H ^ n (X, F ⋙ uliftFunctor)`

in every degree, naturally in `F` and compatibly with the connecting maps of short exact
sequences. For a constant sheaf with value `M` this reads `H ^ n (X, M) ≃+ H ^ n (X, ULift M)`,
naturally in `M`.

The site of open subsets of `X` is small, so abelian sheaves with sections in the larger universe
`max u w` still form a Grothendieck abelian category with a left exact sheafification; this file
registers those facts as instances, together with the preservation of injective sheaves by the
universe lift, so that the comparison of the Stacks project formalization applies.

## Main definitions

* `TopCat.sheafHULiftAddEquiv`: `H ^ n (X, F) ≃+ H ^ n (X, F ⋙ uliftFunctor)`.
* `TopCat.constantSheafULiftIso`: the universe lift of the constant sheaf `M` is the constant
  sheaf `ULift M`, naturally in `M`.
* `TopCat.constantSheafHULiftAddEquiv`: `H ^ n (X, M) ≃+ H ^ n (X, ULift M)` for constant
  sheaves.

## Main results

* `TopCat.sheafHULiftAddEquiv_naturality`, `TopCat.constantSheafHULiftAddEquiv_naturality`:
  naturality in the sheaf and in the group of coefficients.
* `TopCat.sheafHULiftAddEquiv_comp_extClass`: compatibility with the connecting maps.

## Implementation notes

The `Ext` groups on both sides are arbitrary instances `HasExt.{w₁}` and `HasExt.{w₂}`; with
`CategoryTheory.IsGrothendieckAbelian.hasExt.{u}` and `.{max u w}` the source is the cohomology
used throughout for the analytic topology. The instances on sheaves with sections in a larger
universe are stated for a free universe `w` under the instance argument `UnivLE.{u, w}`, at low
priority. An instance whose conclusion determines its universe only through `max u w` would be
tried before the library's instance at the universe `u` itself and stop elaboration on the
constraint `u =?= max u ?w`, which has two solutions, instead of failing over
(lean4#2297); with free universes the conclusion fixes `w`, and the side condition fails cleanly.

## References

* [Stacks Project, Tag 01FT](https://stacks.math.columbia.edu/tag/01FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite

universe w₁ w₂ w u

namespace TopCat

variable (X : TopCat.{u})

/-! The instances below hold for sections in any universe `w` into which `Type u` embeds. Their
universes are free variables and the side condition `UnivLE.{u, w}` is an instance argument, so
at a goal they do not apply to, instance search fails on that argument and moves on; they have
low priority, so that the library's instances at the universe of the site are tried first. -/

/-- Abelian presheaves on the opens of `X` with sections in any universe `w` above `u` have a
left exact sheafification. -/
instance (priority := low) hasSheafify_opens_addCommGrpCat [UnivLE.{u, w}] :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w} :=
  have : EssentiallySmall.{w} (Opens X) := essentiallySmall_of_small_of_locallySmall _
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{w} _

/-- On the opens of `X`, a morphism of abelian presheaves with sections in any universe `w`
above `u` is inverted by sheafification exactly when it is locally bijective. -/
instance (priority := low) wEqualsLocallyBijective_opens_addCommGrpCat [UnivLE.{u, w}] :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  have : EssentiallySmall.{w} (Opens X) := essentiallySmall_of_small_of_locallySmall _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall (A := AddCommGrpCat.{w})
    (Opens.grothendieckTopology X)

/-- Abelian sheaves on `X` with sections in any universe `w` above `u` form a Grothendieck
abelian category. -/
instance (priority := low) isGrothendieckAbelian_sheaf_opens_addCommGrpCat [UnivLE.{u, w}] :
    IsGrothendieckAbelian.{w}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) :=
  have : EssentiallySmall.{w} (Opens X) := essentiallySmall_of_small_of_locallySmall _
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

/-! The same instances for a space given as `TopCat.of T`: instance search unfolds the carrier
of `TopCat.of T` to `T`, so the instances stated for a variable `X : TopCat` are not found there. -/

section OfType

variable (T : Type u) [TopologicalSpace T]

instance (priority := low) hasSheafify_opens_of_addCommGrpCat [UnivLE.{u, w}] :
    HasSheafify (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{w} :=
  hasSheafify_opens_addCommGrpCat _

instance (priority := low) wEqualsLocallyBijective_opens_of_addCommGrpCat [UnivLE.{u, w}] :
    (Opens.grothendieckTopology (TopCat.of T)).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  wEqualsLocallyBijective_opens_addCommGrpCat _

instance (priority := low) isGrothendieckAbelian_sheaf_opens_of_addCommGrpCat [UnivLE.{u, w}] :
    IsGrothendieckAbelian.{w}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of T)) AddCommGrpCat.{w}) :=
  isGrothendieckAbelian_sheaf_opens_addCommGrpCat _

end OfType

/-- The universe lift of abelian sheaves on `X` preserves injective sheaves: on a small site an
injective sheaf is injective as a presheaf, and the universe lift of abelian groups preserves
injective groups. -/
instance preservesInjectiveObjects_uliftSheafFunctor_opens :
    (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{w, u}
      (Opens.grothendieckTopology X)).PreservesInjectiveObjects :=
  have := Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_addCommGrpCat_uliftFunctor.{w, u}
  Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects _ _

/-- The universe lift of abelian sheaves on `X` is right exact. -/
instance preservesFiniteColimits_uliftSheafFunctor_opens :
    PreservesFiniteColimits
      (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{w, u} (Opens.grothendieckTopology X)) :=
  Stacks.Sheaves.UniverseLift.preservesFiniteColimits_uliftSheafFunctor.{w, u} _

section Cohomology

variable [HasExt.{w₁} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w₂} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w})]

/-- **The cohomology of an abelian sheaf on `X` does not depend on the coefficient universe**:
`H ^ n (X, F) ≃+ H ^ n (X, F ⋙ uliftFunctor)`. -/
def sheafHULiftAddEquiv
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H.{w₁} F n ≃+
      CategoryTheory.Sheaf.H.{w₂} ((sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{w, u}).obj F) n :=
  Stacks.Sheaves.UniverseLift.sheafHUliftAddEquiv.{w₁, w₂, w, u} _ F n

lemma sheafHULiftAddEquiv_apply
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (x : CategoryTheory.Sheaf.H.{w₁} F n) :
    sheafHULiftAddEquiv.{w₁, w₂, w} X F n x =
      (Ext.mk₀ (Stacks.Sheaves.UniverseLift.uliftSheafFunctorConstantIntIso.{w, u}
          (Opens.grothendieckTopology X)).inv).comp
        (x.mapExactFunctor (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{w, u}
          (Opens.grothendieckTopology X))) (zero_add n) :=
  rfl

/-- `TopCat.sheafHULiftAddEquiv` is natural in the sheaf. -/
lemma sheafHULiftAddEquiv_naturality
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (ψ : F ⟶ G)
    (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{w₁} F n) :
    sheafHULiftAddEquiv.{w₁, w₂, w} X G n (CategoryTheory.Sheaf.H.map ψ n x) =
      CategoryTheory.Sheaf.H.map ((sheafCompose (Opens.grothendieckTopology X)
        AddCommGrpCat.uliftFunctor.{w, u}).map ψ) n (sheafHULiftAddEquiv.{w₁, w₂, w} X F n x) :=
  Stacks.Sheaves.UniverseLift.sheafHUliftAddEquiv_naturality.{w₁, w₂, w, u} _ ψ n x

/-- `TopCat.sheafHULiftAddEquiv` is compatible with the connecting maps: for a short exact
sequence `0 → S₁ → S₂ → S₃ → 0` of abelian sheaves on `X`, the connecting map
`H ^ n (X, S₃) → H ^ (n + 1) (X, S₁)` corresponds to the connecting map of the lifted short
exact sequence. -/
lemma sheafHULiftAddEquiv_comp_extClass
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ) (x : CategoryTheory.Sheaf.H.{w₁} S.X₃ n) :
    sheafHULiftAddEquiv.{w₁, w₂, w} X S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (sheafHULiftAddEquiv.{w₁, w₂, w} X S.X₃ n x).comp
        (hS.map_of_exact (Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{w, u}
          (Opens.grothendieckTopology X))).extClass rfl := by
  rw [sheafHULiftAddEquiv_apply, sheafHULiftAddEquiv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.comp_assoc]
  omega

end Cohomology

/-- **The universe lift of a constant sheaf is constant**: the lift of the constant sheaf `M`
on `X` is the constant sheaf `ULift M`, naturally in `M`. -/
def constantSheafULiftIso :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        sheafCompose (Opens.grothendieckTopology X) AddCommGrpCat.uliftFunctor.{w, u} ≅
      AddCommGrpCat.uliftFunctor.{w, u} ⋙
        constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} :=
  have := Stacks.Sheaves.UniverseLift.preservesSheafification_uliftFunctor.{u, u, u, w}
    (J := Opens.grothendieckTopology X)
  constantCommuteCompose _ _

section Constant

variable [HasExt.{w₁} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{w₂} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w})]

/-- **Constant coefficients**: `H ^ n (X, M) ≃+ H ^ n (X, ULift M)` for the constant sheaves
with values `M` and `ULift M` on `X`. -/
def constantSheafHULiftAddEquiv (M : AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H.{w₁}
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj M) n ≃+
      CategoryTheory.Sheaf.H.{w₂}
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}).obj
          (AddCommGrpCat.uliftFunctor.{w, u}.obj M)) n :=
  (sheafHULiftAddEquiv.{w₁, w₂, w} X _ n).trans
    { toFun := CategoryTheory.Sheaf.H.map ((constantSheafULiftIso.{w} X).hom.app M) n
      invFun := CategoryTheory.Sheaf.H.map ((constantSheafULiftIso.{w} X).inv.app M) n
      left_inv := fun x ↦ by
        rw [← CategoryTheory.Sheaf.H.map_comp_apply, Iso.hom_inv_id_app,
          CategoryTheory.Sheaf.H.map_id_apply]
      right_inv := fun x ↦ by
        rw [← CategoryTheory.Sheaf.H.map_comp_apply, Iso.inv_hom_id_app,
          CategoryTheory.Sheaf.H.map_id_apply]
      map_add' := map_add _ }

/-- `TopCat.constantSheafHULiftAddEquiv` is natural in the group of coefficients. -/
lemma constantSheafHULiftAddEquiv_naturality {M N : AddCommGrpCat.{u}} (g : M ⟶ N) (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{w₁}
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj M) n) :
    constantSheafHULiftAddEquiv.{w₁, w₂, w} X N n
        (CategoryTheory.Sheaf.H.map
          ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map g) n x) =
      CategoryTheory.Sheaf.H.map
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w}).map
          (AddCommGrpCat.uliftFunctor.{w, u}.map g)) n
        (constantSheafHULiftAddEquiv.{w₁, w₂, w} X M n x) := by
  change CategoryTheory.Sheaf.H.map _ n
      (sheafHULiftAddEquiv.{w₁, w₂, w} X _ n (CategoryTheory.Sheaf.H.map _ n x)) =
    CategoryTheory.Sheaf.H.map _ n
      (CategoryTheory.Sheaf.H.map _ n (sheafHULiftAddEquiv.{w₁, w₂, w} X _ n x))
  rw [sheafHULiftAddEquiv_naturality, ← CategoryTheory.Sheaf.H.map_comp_apply,
    ← CategoryTheory.Sheaf.H.map_comp_apply]
  congr 2
  exact (constantSheafULiftIso.{w} X).hom.naturality g

end Constant

end TopCat

end
