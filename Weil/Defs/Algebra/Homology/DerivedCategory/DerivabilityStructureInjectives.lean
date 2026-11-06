module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Weil.Attr

/-!
# Injective resolutions of cochain complexes

Let `C` be an abelian category. An injective resolution of a cochain complex `K` is a
bounded below complex `I` of injective objects of `C` together with a quasi-isomorphism
of complexes `K ⟶ I`.

## Main definitions

* `CochainComplex.InjectiveResolutionPlus K`: an injective resolution of the cochain complex `K`,
  the complex of injectives being an object of `CochainComplex.Plus (InjectiveObject C)`.
* `CochainComplex.InjectiveResolutionPlus.cocomplex`: the underlying complex of `C`.

## Main results

* `CochainComplex.InjectiveResolutionPlus.rightResolutionEquiv`: for a bounded below complex `K`,
  injective resolutions of `K` are the same as right resolutions of `K` for the localizer
  morphism `CochainComplex.Plus.localizerMorphism C` given by the inclusion
  `CochainComplex.Plus (InjectiveObject C) ⥤ CochainComplex.Plus C`.
* The underlying complex of an injective resolution is K-injective, and termwise injective.

## Implementation notes

The complex `K` being resolved is an arbitrary cochain complex indexed by `ℤ`; it is not
required to be bounded below. (A complex admitting an injective resolution is automatically
cohomologically bounded below.) The complex of injectives is taken in Mathlib's category
`CochainComplex.Plus (InjectiveObject C)`, the source of the injective derivability structure.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- An injective resolution of a cochain complex `K`: a bounded below cochain complex `I` of
injective objects together with a quasi-isomorphism `ι : K ⟶ I`. -/
@[weil "def_fka2_injective_resolution_of_complex"]
structure InjectiveResolutionPlus (K : CochainComplex C ℤ) where
  /-- The bounded below complex of injective objects. -/
  I : CochainComplex.Plus (InjectiveObject C)
  /-- The quasi-isomorphism from `K` to the complex of injectives. -/
  ι : K ⟶ ((InjectiveObject.ι C).mapCochainComplexPlus.obj I).obj
  quasiIso_ι : QuasiIso ι := by infer_instance

namespace InjectiveResolutionPlus

attribute [instance] quasiIso_ι

variable {K : CochainComplex C ℤ} (R : InjectiveResolutionPlus K)

/-- The complex of injective objects of an injective resolution, as a complex in `C`. -/
abbrev cocomplex : CochainComplex C ℤ :=
  ((InjectiveObject.ι C).mapCochainComplexPlus.obj R.I).obj

instance (n : ℤ) : Injective (R.cocomplex.X n) :=
  (R.I.obj.X n).property

instance : IsKInjective R.cocomplex :=
  inferInstanceAs (IsKInjective
    (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj R.I.obj))

lemma exists_isStrictlyGE : ∃ n : ℤ, R.cocomplex.IsStrictlyGE n :=
  ((InjectiveObject.ι C).mapCochainComplexPlus.obj R.I).property

/-- For a bounded below complex `K`, injective resolutions of `K` are the right resolutions
of `K` for the localizer morphism `CochainComplex.Plus.localizerMorphism C`. -/
@[simps]
def rightResolutionEquiv (K : CochainComplex.Plus C) :
    InjectiveResolutionPlus K.obj ≃
      (CochainComplex.Plus.localizerMorphism C).RightResolution K where
  toFun R :=
    { X₁ := R.I
      w := ObjectProperty.homMk R.ι
      hw := by
        change HomologicalComplex.quasiIso C _ R.ι
        rw [HomologicalComplex.mem_quasiIso_iff]
        infer_instance }
  invFun R :=
    { I := R.X₁
      ι := R.w.hom
      quasiIso_ι := by
        have := R.hw
        change HomologicalComplex.quasiIso C _ R.w.hom at this
        rwa [HomologicalComplex.mem_quasiIso_iff] at this }
  left_inv R := rfl
  right_inv R := rfl

end InjectiveResolutionPlus

end CochainComplex
