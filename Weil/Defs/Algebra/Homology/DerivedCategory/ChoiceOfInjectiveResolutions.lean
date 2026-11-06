module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Weil.Defs.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Weil.Attr

/-!
# Choices of injective resolutions on the bounded below derived category

Let `C` be an abelian category. The objects of the bounded below derived category `D⁺(C)` are
the cochain complexes `K` whose image in the derived category is isomorphic to a bounded below
complex, i.e. the complexes with `Hⁿ(K) = 0` for `n ≪ 0`. A choice of injective resolutions on
`D⁺(C)` is a family `(I(K), i_K)` indexed by these complexes, each `(I(K), i_K)` being an
injective resolution of `K` (`CochainComplex.InjectiveResolutionPlus K`).

## Main definitions

* `CochainComplex.ChoiceOfInjectiveResolutions C`: a choice of an injective resolution of every
  cochain complex `K` with `K.IsGE n` for some `n`.

## Main results

* `CochainComplex.exists_isGE_iff_plus_Q_obj`: a cochain complex is cohomologically bounded
  below if and only if its image under `DerivedCategory.Q` is an object of `D⁺(C)`, so the
  index set of a choice of injective resolutions is the set of objects of `D⁺(C)`.

## Implementation notes

In Mathlib the objects of `DerivedCategory C` are not literally cochain complexes (the derived
category is only a localization up to equivalence), so a family indexed by the objects of
`DerivedCategory.Plus C` would have no complex to resolve. The family is therefore indexed by
the cochain complexes `K` which are cohomologically bounded below (`∃ n, K.IsGE n`); by
`CochainComplex.exists_isGE_iff_plus_Q_obj` these are exactly the complexes representing
objects of `D⁺(C)`, which is the meaning of the objects of `D_+(A)` in the source. The
definition needs no `HasDerivedCategory` instance.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II,
  p. 296.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable (C : Type*) [Category* C] [Abelian C]

/-- A choice of injective resolutions on the bounded below derived category: for every cochain
complex `K` which is cohomologically bounded below (`K.IsGE n` for some `n`), an injective
resolution `(I(K), i_K)` of `K`. -/
@[weil "def_fka2_choice_of_injective_resolutions"]
abbrev ChoiceOfInjectiveResolutions : Type _ :=
  ∀ (K : CochainComplex C ℤ), (∃ n : ℤ, K.IsGE n) → InjectiveResolutionPlus K

variable {C}

/-- A cochain complex is cohomologically bounded below if and only if its image in the derived
category lies in the bounded below derived category `D⁺(C)`. -/
lemma exists_isGE_iff_plus_Q_obj [HasDerivedCategory C] (K : CochainComplex C ℤ) :
    (∃ n : ℤ, K.IsGE n) ↔ DerivedCategory.TStructure.t.plus (DerivedCategory.Q.obj K) := by
  change _ ↔ ∃ n : ℤ, (DerivedCategory.Q.obj K).IsGE n
  simp only [DerivedCategory.isGE_Q_obj_iff]

end CochainComplex
