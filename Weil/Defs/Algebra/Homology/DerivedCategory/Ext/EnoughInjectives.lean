module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import Weil.Attr

/-!
# `Ext` of sheaves of modules as right derived functors of `Hom`

Let `R` be a ring, `J` a Grothendieck topology (for instance the small étale site of a scheme `Z`)
and `𝒜`, `ℬ` sheaves of `R`-modules on it. The group `Extᵖ_R(Z; 𝒜, ℬ)` is the `p`-th right derived
functor of the left exact functor `Hom(𝒜, -)`, evaluated at `ℬ`: for an injective resolution
`ℬ → I^•`, it is `Hᵖ(Hom(𝒜, I^•))`.

The `Ext`-groups of the abelian category `Sheaf J (ModuleCat R)` are Mathlib's
`CategoryTheory.Abelian.Ext`, defined through the derived category. This file identifies them,
in any abelian category with enough injectives whose `Ext`-groups live in the universe of its
morphisms, with the classical right derived functors of `Hom(𝒜, -)`, and with the cohomology of
`Hom(𝒜, I^•)` for any injective resolution `I^•` of `ℬ`. The identification is natural in `ℬ`,
hence compatible with the `R`-module structures: the action of `r ∈ R` on both sides is the map
induced by `r • 𝟙 ℬ`.

## Main definitions

* `CategoryTheory.Abelian.Ext.addEquivRightDerivedCoyoneda`: `Extᵖ(X, Y) ≃+ (Rᵖ Hom(X, -))(Y)`.
* `CategoryTheory.Abelian.Ext.addEquivHomologyOfInjectiveResolution`: for an injective
  resolution `I` of `Y`, `Extᵖ(X, Y) ≃+ Hᵖ(Hom(X, I^•))`.

## Main results

* `CategoryTheory.Abelian.Ext.addEquivRightDerivedCoyoneda_naturality`: naturality in `Y`.
* `CategoryTheory.Abelian.Ext.addEquivRightDerivedCoyoneda_smul`: compatibility with the
  `R`-module structure of an `R`-linear category, such as `Sheaf J (ModuleCat R)`.

## Implementation notes

No new definition of `Ext` is made: the object is Mathlib's `CategoryTheory.Abelian.Ext`, and the
comparison with the derived functor of `Hom(X, -)` is
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda`. The results are stated
for an arbitrary abelian category with enough injectives; `Sheaf J (ModuleCat R)` on a small site
is one (it is Grothendieck abelian). For a noncommutative ring `R`, `Hom_R(𝒜, ℬ)` is only an
abelian group, so the comparison is stated as an isomorphism of abelian groups; for `R`
commutative, the `R`-module structures correspond by `addEquivRightDerivedCoyoneda_smul`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.4
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

namespace CategoryTheory.Abelian.Ext

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]

/-- **`Ext` is the right derived functor of `Hom`.** For objects `X`, `Y` of an abelian category
with injective resolutions, `Extᵖ(X, Y)` is the value at `Y` of the `p`-th right derived functor
of the left exact functor `Hom(X, -)`. -/
@[weil "def_fk104_ext_sheaves_of_modules"]
def addEquivRightDerivedCoyoneda (X Y : A) (p : ℕ) :
    Ext X Y p ≃+ ((preadditiveCoyoneda.obj (op X)).rightDerived p).obj Y :=
  ((Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda X p).app
    Y).addCommGroupIsoToAddEquiv

/-- The identification `addEquivRightDerivedCoyoneda` is natural in the second variable. -/
lemma addEquivRightDerivedCoyoneda_naturality (X : A) {Y Y' : A} (f : Y ⟶ Y') (p : ℕ)
    (x : Ext X Y p) :
    addEquivRightDerivedCoyoneda X Y' p (x.comp (Ext.mk₀ f) (add_zero p)) =
      ((preadditiveCoyoneda.obj (op X)).rightDerived p).map f
        (addEquivRightDerivedCoyoneda X Y p x) := by
  have h := congrArg (fun g => AddCommGrpCat.Hom.hom g x)
    ((Stacks.Cohomology.ExtComparison.extFunctorObjIsoRightDerivedCoyoneda X p).hom.naturality f)
  exact h

/-- **`Ext` computed by an injective resolution.** For an injective resolution `I` of `Y`,
`Extᵖ(X, Y)` is the `p`-th cohomology group of the complex `Hom(X, I^•)`. -/
@[weil "def_fk104_ext_sheaves_of_modules"]
def addEquivHomologyOfInjectiveResolution (X : A) {Y : A} (I : InjectiveResolution Y) (p : ℕ) :
    Ext X Y p ≃+
      (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex _).obj I.cocomplex).homology p :=
  (addEquivRightDerivedCoyoneda X Y p).trans
    (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) p).addCommGroupIsoToAddEquiv

lemma addEquivHomologyOfInjectiveResolution_apply (X : A) {Y : A} (I : InjectiveResolution Y)
    (p : ℕ) (x : Ext X Y p) :
    addEquivHomologyOfInjectiveResolution X I p x =
      (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) p).hom
        (addEquivRightDerivedCoyoneda X Y p x) :=
  rfl

section Linear

variable {R : Type*} [Ring R] [Linear R A]

/-- **Compatibility with the `R`-module structures.** In an `R`-linear category (for instance
`Sheaf J (ModuleCat R)` with `R` commutative), the action of `r : R` on `Extᵖ(X, Y)` corresponds
under `addEquivRightDerivedCoyoneda` to the map induced on `Rᵖ Hom(X, -)` by `r • 𝟙 Y`. -/
@[weil "def_fk104_ext_sheaves_of_modules"]
lemma addEquivRightDerivedCoyoneda_smul (X Y : A) (p : ℕ) (r : R) (x : Ext X Y p) :
    addEquivRightDerivedCoyoneda X Y p (r • x) =
      ((preadditiveCoyoneda.obj (op X)).rightDerived p).map (r • 𝟙 Y)
        (addEquivRightDerivedCoyoneda X Y p x) := by
  rw [smul_eq_comp_mk₀, addEquivRightDerivedCoyoneda_naturality]

end Linear

end CategoryTheory.Abelian.Ext
