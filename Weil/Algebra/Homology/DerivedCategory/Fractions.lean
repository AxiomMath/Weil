module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Weil.Attr

/-!
# Cancellation of quasi-isomorphisms in the homotopy category

Let `A` be an abelian category and `K(A)` the homotopy category of cochain complexes in `A`,
with `S` the class of quasi-isomorphisms of `K(A)`. For two morphisms `f g : X ⟶ Y` of `K(A)`,
there is `s : P ⟶ X` in `S` with `s ≫ f = s ≫ g` if and only if there is `t : Y ⟶ Q` in `S`
with `f ≫ t = g ≫ t`.

Both implications are the `ext` axioms of the left and right calculus of fractions for
`HomotopyCategory.quasiIso A (ComplexShape.up ℤ)`. These hold because this class is the class
of morphisms whose cone is acyclic (`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`),
and the class of morphisms whose cone lies in a triangulated subcategory admits a calculus of
left and right fractions.

## Main results

* `HomotopyCategory.exists_quasiIso_comp_eq_iff_exists_comp_quasiIso_eq`: the cancellation
  criterion.

## Implementation notes

The calculus-of-fractions instances are derived here directly from
`HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic`, so the result does not assume that the
derived category exists (`HasDerivedCategory`), unlike the instances of
`Mathlib.Algebra.Homology.DerivedCategory.Fractions`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.II.
-/

@[expose] public section

open CategoryTheory

namespace HomotopyCategory

variable {A : Type*} [Category A] [Abelian A]

/-- Quasi-isomorphisms of `K(A)` admit a calculus of left fractions. -/
lemma quasiIso_hasLeftCalculusOfFractions :
    (quasiIso A (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/-- Quasi-isomorphisms of `K(A)` admit a calculus of right fractions. -/
lemma quasiIso_hasRightCalculusOfFractions :
    (quasiIso A (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/-- Two morphisms `f g : X ⟶ Y` of the homotopy category are equalized by precomposition with
some quasi-isomorphism `s : P ⟶ X` if and only if they are equalized by postcomposition with
some quasi-isomorphism `t : Y ⟶ Q`. -/
@[weil "lem_fka2_qis_cancellation"]
theorem exists_quasiIso_comp_eq_iff_exists_comp_quasiIso_eq
    {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (f g : X ⟶ Y) :
    (∃ (P : HomotopyCategory A (ComplexShape.up ℤ)) (s : P ⟶ X),
        quasiIso A (ComplexShape.up ℤ) s ∧ s ≫ f = s ≫ g) ↔
      ∃ (Q : HomotopyCategory A (ComplexShape.up ℤ)) (t : Y ⟶ Q),
        quasiIso A (ComplexShape.up ℤ) t ∧ f ≫ t = g ≫ t := by
  have := quasiIso_hasLeftCalculusOfFractions (A := A)
  have := quasiIso_hasRightCalculusOfFractions (A := A)
  constructor
  · rintro ⟨P, s, hs, h⟩
    obtain ⟨Q, t, ht, h'⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext f g s hs h
    exact ⟨Q, t, ht, h'⟩
  · rintro ⟨Q, t, ht, h⟩
    obtain ⟨P, s, hs, h'⟩ := MorphismProperty.HasRightCalculusOfFractions.ext f g t ht h
    exact ⟨P, s, hs, h'⟩

end HomotopyCategory
