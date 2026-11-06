module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.OpenClosedPointReduction
public import Weil.Attr

/-!
# Field-valued points factor uniquely through immersions

Let `ι : Y ⟶ X` be a preimmersion of schemes (for instance an immersion: a closed immersion
into an open subscheme followed by the inclusion), `K` a field and `a : Spec K ⟶ X` a morphism
whose point lies in the image of `ι`. Then `a` factors through `ι` in exactly one way. If `X` is
a scheme over a base `S` and `a` is an `S`-morphism, the factorization is an `S`-morphism for
the structure morphism of `Y` obtained by composing with `ι`.

## Main results

* `AlgebraicGeometry.existsUnique_lift_of_isPreimmersion`: the unique factorization of a
  field-valued point through a preimmersion.
* `AlgebraicGeometry.existsUnique_lift_over_of_isPreimmersion`: the same over a base scheme `S`.

## Implementation notes

The statement is made for preimmersions rather than immersions (every immersion is a
preimmersion) and over an arbitrary base scheme `S` rather than the spectrum of a field.
Existence is `AlgebraicGeometry.exists_lift_of_isPreimmersion`; uniqueness holds because a
preimmersion is a monomorphism of schemes.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter 0]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism from the spectrum of a field to `X` whose point lies in the image of a
preimmersion `ι : Y ⟶ X` factors through `ι` in exactly one way. -/
theorem existsUnique_lift_of_isPreimmersion {K : Type u} [Field K] {Y X : Scheme.{u}}
    (ι : Y ⟶ X) [IsPreimmersion ι] (a : Spec (.of K) ⟶ X) (ha : a default ∈ Set.range ι) :
    ∃! b : Spec (.of K) ⟶ Y, b ≫ ι = a := by
  obtain ⟨y, hy⟩ := ha
  obtain ⟨b, hb⟩ := exists_lift_of_isPreimmersion ι a y hy
  exact ⟨b, hb, fun b' hb' => (cancel_mono ι).1 (hb'.trans hb.symm)⟩

/-- Let `X` be a scheme over `S` with structure morphism `sX`, `ι : Y ⟶ X` a preimmersion
(so `Y` is an `S`-scheme via `ι ≫ sX`), `K` a field and `a : Spec K ⟶ X` an `S`-morphism
(for a structure morphism `sK` of `Spec K`) whose point lies in the image of `ι`. Then there is
exactly one `b : Spec K ⟶ Y` with `b ≫ ι = a`, and `b` is an `S`-morphism. -/
@[weil "lem_fk0_field_valued_point_factors_through_immersion"]
theorem existsUnique_lift_over_of_isPreimmersion {K : Type u} [Field K] {S Y X : Scheme.{u}}
    (sX : X ⟶ S) (sK : Spec (.of K) ⟶ S) (ι : Y ⟶ X) [IsPreimmersion ι]
    (a : Spec (.of K) ⟶ X) (has : a ≫ sX = sK) (ha : a default ∈ Set.range ι) :
    (∃! b : Spec (.of K) ⟶ Y, b ≫ ι = a) ∧
      ∀ b : Spec (.of K) ⟶ Y, b ≫ ι = a → b ≫ ι ≫ sX = sK := by
  refine ⟨existsUnique_lift_of_isPreimmersion ι a ha, fun b hb => ?_⟩
  rw [← Category.assoc, hb, has]

end AlgebraicGeometry
