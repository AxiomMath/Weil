module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Open immersions with closed image in a square with a proper map

Consider a commutative square of schemes
```
X  --i-->  X̄
|f         |f̄
v          v
Y  --j-->  Ȳ
```
where `i` and `j` are open immersions, `f` is proper and `f̄` is separated. Put
`X₁ := X̄ ×_Ȳ Y` and let `i₁ : X ⟶ X₁` be the morphism induced by `i` and `f`. Then `i₁` is an
open immersion, and it is proper (since `f = i₁ ≫ f₁` is proper and `f₁ : X₁ ⟶ Y` is
separated), so its image is open and closed. The same holds after base change along any
morphism `g : V ⟶ Y`: the morphism `X ×_Y V ⟶ X̄ ×_Ȳ V` induced by `i` is an open immersion
with closed image.

## Main results

* `AlgebraicGeometry.isOpenImmersion_and_isProper_pullbackLift`: `i₁` is an open immersion and
  proper.
* `AlgebraicGeometry.isOpenImmersion_and_isClosed_range_pullbackLift`: `i₁` is an open immersion
  with closed range.
* `AlgebraicGeometry.isOpenImmersion_and_isClosed_range_pullbackLift_comp`: for every
  `g : V ⟶ Y`, the induced morphism `X ×_Y V ⟶ X̄ ×_Ȳ V` (with `V` over `Ȳ` through `g ≫ j`) is an
  open immersion with closed range.

## Implementation notes

The source assumes all schemes separated; only the separatedness of `f̄` is used here, and it
is needed (the affine line inside the line with doubled origin, over the affine line, is a
counterexample without it). The base change statement is proved for an arbitrary morphism
`V ⟶ Y`, not only for étale ones.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.8.5.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') (f : X ⟶ Y) (f' : X' ⟶ Y')
  (h : i ≫ f' = f ≫ j)

/-- In a commutative square `i ≫ f' = f ≫ j` with `i`, `j` open immersions, `f` proper and `f'`
separated, the induced morphism `X ⟶ X' ×_{Y'} Y` is an open immersion and proper. -/
theorem isOpenImmersion_and_isProper_pullbackLift [IsOpenImmersion i] [IsOpenImmersion j]
    [IsProper f] [IsSeparated f'] :
    IsOpenImmersion (pullback.lift i f h) ∧ IsProper (pullback.lift i f h) := by
  have h1 : IsOpenImmersion (pullback.lift i f h) := by
    have : IsOpenImmersion (pullback.lift i f h ≫ pullback.fst f' j) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst f' j)
  refine ⟨h1, ?_⟩
  have : IsProper (pullback.lift i f h ≫ pullback.snd f' j) := by
    rw [pullback.lift_snd]; infer_instance
  exact IsProper.of_comp _ (pullback.snd f' j)

/-- In a commutative square `i ≫ f' = f ≫ j` with `i`, `j` open immersions, `f` proper and `f'`
separated, the induced morphism `i₁ : X ⟶ X' ×_{Y'} Y` is an open immersion with closed
range. -/
@[weil "lem_fk108_open_proper_square_open_closed"]
theorem isOpenImmersion_and_isClosed_range_pullbackLift [IsOpenImmersion i] [IsOpenImmersion j]
    [IsProper f] [IsSeparated f'] :
    IsOpenImmersion (pullback.lift i f h) ∧ IsClosed (Set.range (pullback.lift i f h).base) := by
  obtain ⟨h1, h2⟩ := isOpenImmersion_and_isProper_pullbackLift i j f f' h
  exact ⟨h1, (pullback.lift i f h).isClosedMap.isClosed_range⟩

/-- In a commutative square `i ≫ f' = f ≫ j` with `i`, `j` open immersions, `f` proper and `f'`
separated, for every morphism `g : V ⟶ Y` the morphism `X ×_Y V ⟶ X' ×_{Y'} V` induced by `i`
(with `V` over `Y'` through `g ≫ j`) is an open immersion with closed range. -/
@[weil "lem_fk108_open_proper_square_open_closed"]
theorem isOpenImmersion_and_isClosed_range_pullbackLift_comp [IsOpenImmersion i]
    [IsOpenImmersion j] [IsProper f] [IsSeparated f'] {V : Scheme.{u}} (g : V ⟶ Y) :
    IsOpenImmersion (pullback.lift (pullback.fst f g ≫ i) (pullback.snd f g)
        (by rw [Category.assoc, h, ← Category.assoc, pullback.condition, Category.assoc]) :
        pullback f g ⟶ pullback f' (g ≫ j)) ∧
      IsClosed (Set.range (pullback.lift (pullback.fst f g ≫ i) (pullback.snd f g)
        (by rw [Category.assoc, h, ← Category.assoc, pullback.condition, Category.assoc]) :
        pullback f g ⟶ pullback f' (g ≫ j)).base) := by
  obtain ⟨h1, h2⟩ := isOpenImmersion_and_isProper_pullbackLift i j f f' h
  set i₁ := pullback.lift i f h
  -- the map `X' ×_{Y'} V ⟶ X' ×_{Y'} Y`
  let q : pullback f' (g ≫ j) ⟶ pullback f' j :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g)
      (by rw [pullback.condition, Category.assoc])
  have hq : IsPullback q (pullback.snd f' (g ≫ j)) (pullback.snd f' j) g := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f' j)
    rw [pullback.lift_fst]
    exact IsPullback.of_hasPullback f' (g ≫ j)
  have hf : i₁ ≫ pullback.snd f' j = f := pullback.lift_snd _ _ _
  have hsq : IsPullback (pullback.lift (pullback.fst f g ≫ i) (pullback.snd f g)
        (by rw [Category.assoc, h, ← Category.assoc, pullback.condition, Category.assoc]) :
        pullback f g ⟶ pullback f' (g ≫ j)) (pullback.fst f g) q i₁ := by
    refine IsPullback.of_right ?_ ?_ hq.flip
    · rw [pullback.lift_snd, hf]
      exact (IsPullback.of_hasPullback f g).flip
    · apply pullback.hom_ext
      · simp only [q, i₁, Category.assoc, pullback.lift_fst]
      · simp only [q, i₁, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          pullback.condition]
  have k1 := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq.flip h1
  have k2 := MorphismProperty.of_isPullback (P := @IsProper) hsq.flip h2
  exact ⟨k1, (Scheme.Hom.isClosedMap _).isClosed_range⟩

end AlgebraicGeometry
