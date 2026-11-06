module

public import Weil.CategoryTheory.Abelian.Subcategory
public import Weil.Defs.CategoryTheory.ObjectProperty.ShiftedSystem
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Weil.Attr

/-!
# The shift of projective systems is an exact additive functor

For every `r : ℤ`, the shift `[r] : F ↦ F[r] = (F_{n+r})_{n ∈ ℤ}` of the abelian category
`CategoryTheory.ProjectiveSystem Λ l` of projective systems of `l`-power torsion `Λ`-modules is
an additive functor preserving finite limits and finite colimits, i.e. an exact functor. Since
limits and colimits in the functor category `ℤᵒᵖ ⥤ ModuleCat Λ` are computed pointwise,
precomposition with the translation `n ↦ n + r` preserves them, and the inclusion of projective
systems into the functor category preserves finite limits and colimits and reflects them.

## Main results

* `CategoryTheory.ProjectiveSystem.shift_additive`: `[r]` is additive.
* `CategoryTheory.ProjectiveSystem.preservesFiniteLimits_shift`,
  `CategoryTheory.ProjectiveSystem.preservesFiniteColimits_shift`: `[r]` is exact.
* `CategoryTheory.ProjectiveSystem.shortComplex_exact_map_shift`: `[r]` sends exact short
  complexes to exact short complexes.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The shift followed by the inclusion into the functor category is the inclusion followed by
precomposition with the translation. -/
lemma shift_comp_ι (r : ℤ) :
    shift.{v} (Λ := Λ) (l := l) r ⋙ (isTorsionBounded.{v} Λ l).ι =
      (isTorsionBounded.{v} Λ l).ι ⋙ (Functor.whiskeringLeft _ _ _).obj (translate r) :=
  rfl

/-- The shift `[r]` is an additive functor. -/
@[weil "lem_fk112_shift_exact_functor"]
instance shift_additive (r : ℤ) : (shift.{v} (Λ := Λ) (l := l) r).Additive where
  map_add {_ _ _ _} := hom_ext fun _ => rfl

/-- The shift `[r]` preserves finite limits. -/
@[weil "lem_fk112_shift_exact_functor"]
instance preservesFiniteLimits_shift (r : ℤ) :
    PreservesFiniteLimits (shift.{v} (Λ := Λ) (l := l) r) where
  preservesFiniteLimits J _ _ := ⟨fun {K} =>
    have : PreservesLimit K (shift.{v} (Λ := Λ) (l := l) r ⋙ (isTorsionBounded.{v} Λ l).ι) := by
      rw [shift_comp_ι]; infer_instance
    preservesLimit_of_reflects_of_preserves _ (isTorsionBounded.{v} Λ l).ι⟩

/-- The shift `[r]` preserves finite colimits. -/
@[weil "lem_fk112_shift_exact_functor"]
instance preservesFiniteColimits_shift (r : ℤ) :
    PreservesFiniteColimits (shift.{v} (Λ := Λ) (l := l) r) where
  preservesFiniteColimits J _ _ := ⟨fun {K} =>
    have : PreservesColimit K (shift.{v} (Λ := Λ) (l := l) r ⋙ (isTorsionBounded.{v} Λ l).ι) := by
      rw [shift_comp_ι]; infer_instance
    preservesColimit_of_reflects_of_preserves _ (isTorsionBounded.{v} Λ l).ι⟩

/-- The shift `[r]` sends exact short complexes of projective systems to exact ones. -/
@[weil "lem_fk112_shift_exact_functor"]
theorem shortComplex_exact_map_shift (r : ℤ) {S : ShortComplex (ProjectiveSystem.{v} Λ l)}
    (hS : S.Exact) : (S.map (shift r)).Exact :=
  hS.map (shift r)

end ProjectiveSystem

end CategoryTheory
