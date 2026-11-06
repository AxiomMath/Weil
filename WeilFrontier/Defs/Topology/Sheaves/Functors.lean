module

public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianSheavesOnSpace
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.Attr

/-!
# The derived direct image of abelian sheaves along a continuous map

Let `g : Z ⟶ W` be a continuous map of topological spaces. The direct image
`g_* : Sh(Z, Ab) ⥤ Sh(W, Ab)`, `(g_*F)(V) = F(g⁻¹V)`, is an additive left exact functor
between abelian categories, and `Sh(Z, Ab)` has enough injectives. Its right derived functor
on the bounded below derived category is the *derived direct image*
`Rg_* : D⁺(Z) ⥤ D⁺(W)`, and its cohomology sheaves are the higher direct images
`R^νg_*(K) = H^ν(Rg_* K)`.

When the derived functor is computed with a choice of injective resolutions `X ↦ I(X)`
(an injective-resolution functor `ρ`), it is `K ↦ g_*(I(K))`, with values in `D(W)`;
this functor is isomorphic to `Rg_*` followed by the inclusion `D⁺(W) ⥤ D(W)`, and its
cohomology `K ↦ H^ν(g_*(I(K)))` is isomorphic to `R^νg_*`.

## Main definitions

* `TopCat.Sheaf.derivedPushforward`: the derived direct image `Rg_* : D⁺(Z) ⥤ D⁺(W)`.
* `TopCat.Sheaf.higherDirectImage`: the higher direct images `R^νg_* : D⁺(Z) ⥤ Sh(W, Ab)`.
* `TopCat.Sheaf.derivedPushforwardIso`: for an injective-resolution functor `ρ`, the
  isomorphism between `K ↦ g_*(I(K))` and `Rg_*` followed by `D⁺(W) ⥤ D(W)`.
* `TopCat.Sheaf.higherDirectImageIso`: for an injective-resolution functor `ρ`, the
  isomorphism between `K ↦ H^ν(g_*(I(K)))` and `R^νg_*`.

## Main results

* `TopCat.Sheaf.higherDirectImage_obj`: `R^νg_*(K) = H^ν(Rg_* K)`.

## Implementation notes

Abelian sheaves on `Z` are `TopCat.Sheaf AddCommGrpCat Z`, abelian by
`Mathlib.Topology.Sheaves.Abelian` and with enough injectives by Stacks, Tag 01DG; the direct
image is Mathlib's `TopCat.Sheaf.pushforward`.

The derived direct image takes values in `D⁺(W)`; the source writes `D(W)`, and the
inclusion `DerivedCategory.Plus.ι` recovers that form (see `derivedPushforwardIso`). The
derived categories are instance arguments, so that a consumer may supply
`HasDerivedCategory.standard` or any other model.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.11.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {Z W : TopCat.{u}} (g : Z ⟶ W)

/-- The direct image of abelian sheaves is additive: on sections it is a reindexing. -/
instance additive_pushforward_addCommGrpCat :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).Additive where
  map_add := rfl

variable [HasDerivedCategory (Z.Sheaf AddCommGrpCat.{u})]
  [HasDerivedCategory (W.Sheaf AddCommGrpCat.{u})]

/-- The derived direct image `Rg_* : D⁺(Z) ⥤ D⁺(W)` of abelian sheaves along a continuous map
`g : Z ⟶ W`: the total right derived functor of the direct image `g_*`. -/
@[weil "def_fk111_space_derived_direct_image"]
noncomputable abbrev derivedPushforward :
    DerivedCategory.Plus (Z.Sheaf AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (W.Sheaf AddCommGrpCat.{u}) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).rightDerivedFunctorPlus

/-- The `ν`-th higher direct image `R^νg_* : D⁺(Z) ⥤ Sh(W, Ab)`, the `ν`-th cohomology sheaf of
the derived direct image. -/
@[weil "def_fk111_space_derived_direct_image"]
noncomputable abbrev higherDirectImage (ν : ℤ) :
    DerivedCategory.Plus (Z.Sheaf AddCommGrpCat.{u}) ⥤ W.Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).rightDerivedFunctorPlusHomology ν

/-- `R^νg_*(K) = H^ν(Rg_* K)`. -/
lemma higherDirectImage_obj (ν : ℤ)
    (K : DerivedCategory.Plus (Z.Sheaf AddCommGrpCat.{u})) :
    (higherDirectImage g ν).obj K =
      (DerivedCategory.Plus.homologyFunctor _ ν).obj ((derivedPushforward g).obj K) :=
  rfl

/-- `R^νg_* = H^ν ∘ Rg_*` as functors. -/
lemma higherDirectImage_eq (ν : ℤ) :
    higherDirectImage g ν =
      derivedPushforward g ⋙ DerivedCategory.Plus.homologyFunctor _ ν :=
  rfl

variable {c : CochainComplex.ChoiceOfInjectiveResolutions (Z.Sheaf AddCommGrpCat.{u})}
  (ρ : CochainComplex.InjectiveResolutionFunctor c)

/-- The derived direct image computed with a choice of injective resolutions, `K ↦ g_*(I(K))`
with values in `D(W)`, is isomorphic to `Rg_*` followed by the inclusion `D⁺(W) ⥤ D(W)`. -/
@[weil "def_fk111_space_derived_direct_image"]
noncomputable def derivedPushforwardIso :
    ρ.rightDerivedFunctor (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g) ≅
      DerivedCategory.PlusComplexes.toPlus _ ⋙ derivedPushforward g ⋙
        DerivedCategory.Plus.ι :=
  ρ.rightDerivedFunctorIso (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g)

/-- The higher direct images computed with a choice of injective resolutions,
`K ↦ H^ν(g_*(I(K)))`, are isomorphic to `R^νg_*`. -/
@[weil "def_fk111_space_derived_direct_image"]
noncomputable def higherDirectImageIso (ν : ℤ) :
    ρ.classicalRightDerived (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g) ν ≅
      DerivedCategory.PlusComplexes.toPlus _ ⋙ higherDirectImage g ν :=
  ρ.classicalRightDerivedIso (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g) ν

end TopCat.Sheaf
