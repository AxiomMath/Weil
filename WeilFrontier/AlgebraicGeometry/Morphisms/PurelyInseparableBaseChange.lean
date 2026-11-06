/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import WeilFrontier.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Weil.Attr

/-!
# Base change of purely inseparable morphisms

A (finite) purely inseparable morphism of schemes `f : X ⟶ Y` is one which is finite,
universally injective and surjective. Each of these three properties is stable under base
change, hence so is being purely inseparable: for any morphism `g : Z ⟶ Y`, the projection
`X ×_Y Z ⟶ Z` is purely inseparable.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsPurelyInseparable.pullback_snd`: the projection
  `pullback f g ⟶ Z` is purely inseparable when `f` is.
* `AlgebraicGeometry.Scheme.Hom.IsPurelyInseparable.pullback_fst`: the symmetric version.

## Implementation notes

The source deduces the statement from the characterisation by unique lifts of geometric points;
here it follows directly from the stability under base change of `IsFinite`,
`UniversallyInjective` and `Surjective`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §3.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y}

/-- The base change of a purely inseparable morphism `f : X ⟶ Y` along any morphism
`g : Z ⟶ Y` is purely inseparable: the projection `X ×_Y Z ⟶ Z` is purely inseparable. -/
@[weil "lem_fk103_purely_inseparable_base_change"]
theorem IsPurelyInseparable.pullback_snd (hf : f.IsPurelyInseparable) (g : Z ⟶ Y) :
    (pullback.snd f g).IsPurelyInseparable := by
  have h := IsPullback.of_hasPullback f g
  exact ⟨MorphismProperty.of_isPullback h hf.1, MorphismProperty.of_isPullback h hf.2.1,
    MorphismProperty.of_isPullback h hf.2.2⟩

/-- The base change of a purely inseparable morphism `f : X ⟶ Y` along any morphism
`g : Z ⟶ Y`, with the factors in the other order: the projection `Z ×_Y X ⟶ Z` is purely
inseparable. -/
theorem IsPurelyInseparable.pullback_fst (hf : f.IsPurelyInseparable) (g : Z ⟶ Y) :
    (pullback.fst g f).IsPurelyInseparable := by
  have h := (IsPullback.of_hasPullback g f).flip
  exact ⟨MorphismProperty.of_isPullback h hf.1, MorphismProperty.of_isPullback h hf.2.1,
    MorphismProperty.of_isPullback h hf.2.2⟩

end AlgebraicGeometry.Scheme.Hom
