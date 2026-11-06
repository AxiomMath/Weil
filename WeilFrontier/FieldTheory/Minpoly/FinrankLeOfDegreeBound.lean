module

public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Perfect

/-!
# Field extensions in which every element has bounded degree

Let `E / F` be a separable field extension and `d` a natural number such that every element of
`E` is a root of a nonzero polynomial over `F` of degree at most `d`. Then `E / F` is finite of
degree at most `d`.

The proof: by the primitive element theorem every finite intermediate field `K` is `F⟮α⟯` for
some `α`, so `[K : F] = deg (minpoly F α) ≤ d`. An intermediate field of maximal finite degree
`K` then contains every `y : E`, since `K ⊔ F⟮y⟯` is again finite, of degree at least and hence
equal to that of `K`.

Over a perfect field (for instance a field of characteristic zero) separability is automatic,
since the hypothesis makes `E` algebraic over `F`.

## Main results

* `Field.finiteDimensional_and_finrank_le_of_forall_aeval_of_isSeparable`: the statement for a
  separable extension.
* `Field.finiteDimensional_and_finrank_le_of_forall_aeval`: the statement over a perfect field,
  in particular over a field of characteristic zero.
-/

public section

open Polynomial IntermediateField Module

namespace Field

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {d : ℕ}

/-- If every element of a separable extension `E / F` is a root of a nonzero polynomial of degree
at most `d`, then every finite-dimensional intermediate field has degree at most `d`. -/
theorem finrank_intermediateField_le_of_forall_aeval [Algebra.IsSeparable F E]
    (h : ∀ x : E, ∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ d ∧ aeval x p = 0)
    (K : IntermediateField F E) [FiniteDimensional F K] : finrank F K ≤ d := by
  have : Algebra.IsSeparable F K := Algebra.isSeparable_tower_bot_of_isSeparable F K E
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F K
  have hint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [← IntermediateField.finrank_top', ← hα, IntermediateField.adjoin.finrank hint,
    IntermediateField.minpoly_eq]
  obtain ⟨p, hp0, hpd, hpx⟩ := h (α : E)
  have hdeg := minpoly.degree_le_of_ne_zero F (α : E) hp0 hpx
  exact (Polynomial.natDegree_le_natDegree hdeg).trans hpd

/-- If every element of a separable extension `E / F` is a root of a nonzero polynomial of degree
at most `d`, then `E / F` is finite of degree at most `d`. -/
theorem finiteDimensional_and_finrank_le_of_forall_aeval_of_isSeparable [Algebra.IsSeparable F E]
    (h : ∀ x : E, ∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ d ∧ aeval x p = 0) :
    FiniteDimensional F E ∧ finrank F E ≤ d := by
  classical
  -- the degrees of the finite intermediate fields are bounded by `d`
  let S : Set ℕ := {n | ∃ K : IntermediateField F E, FiniteDimensional F K ∧ finrank F K = n}
  have hS : BddAbove S := ⟨d, by
    rintro n ⟨K, hK, rfl⟩
    exact finrank_intermediateField_le_of_forall_aeval h K⟩
  have hne : S.Nonempty := ⟨_, ⊥, inferInstance, rfl⟩
  obtain ⟨K, hK, hKmax⟩ := Nat.sSup_mem hne hS
  -- an intermediate field of maximal degree is everything
  have htop : K = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hy : IsIntegral F y := by
      obtain ⟨p, hp0, -, hpy⟩ := h y
      exact (isAlgebraic_iff_isIntegral).mp ⟨p, hp0, hpy⟩
    have : FiniteDimensional F F⟮y⟯ := IntermediateField.adjoin.finiteDimensional hy
    have : FiniteDimensional F ↥(K ⊔ F⟮y⟯) := inferInstance
    have hle : K ≤ K ⊔ F⟮y⟯ := le_sup_left
    have hfin : finrank F ↥(K ⊔ F⟮y⟯) ≤ finrank F K := by
      rw [hKmax]
      exact le_csSup hS ⟨_, inferInstance, rfl⟩
    have heq : K = K ⊔ F⟮y⟯ := IntermediateField.eq_of_le_of_finrank_le hle hfin
    have : y ∈ K ⊔ F⟮y⟯ := le_sup_right (a := K) (IntermediateField.mem_adjoin_simple_self F y)
    rwa [← heq] at this
  subst htop
  have : FiniteDimensional F E :=
    LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  refine ⟨inferInstance, ?_⟩
  rw [← IntermediateField.finrank_top']
  exact finrank_intermediateField_le_of_forall_aeval h ⊤

/-- If every element of an extension `E` of a perfect field `F` (for instance a field of
characteristic zero) is a root of a nonzero polynomial of degree at most `d`, then `E / F` is
finite of degree at most `d`. -/
theorem finiteDimensional_and_finrank_le_of_forall_aeval [PerfectField F]
    (h : ∀ x : E, ∃ p : F[X], p ≠ 0 ∧ p.natDegree ≤ d ∧ aeval x p = 0) :
    FiniteDimensional F E ∧ finrank F E ≤ d := by
  have : Algebra.IsAlgebraic F E := ⟨fun x => by
    obtain ⟨p, hp0, -, hpx⟩ := h x
    exact ⟨p, hp0, hpx⟩⟩
  exact finiteDimensional_and_finrank_le_of_forall_aeval_of_isSeparable h

end Field
