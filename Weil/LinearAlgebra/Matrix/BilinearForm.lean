module

public import Weil.Attr
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Nondegenerate alternating forms live on even-dimensional spaces

Let `β : V × V → K` be a bilinear form on a finite-dimensional vector space `V` over a field `K`
which is alternating (`β x x = 0` for all `x`) and nondegenerate (`x ↦ β x ·` is injective).
Then `dim V` is even.

The proof goes through the determinant of an alternating matrix: an alternating square matrix
of odd size has determinant zero over every commutative ring. Over `ℤ`, and hence over the
polynomial ring `MvPolynomial _ ℤ` which has characteristic zero and no zero divisors, this
follows from `det Aᵀ = det (-A) = (-1)ⁿ det A`. A generic alternating matrix over that
polynomial ring specialises to any alternating matrix, which gives the statement over any
commutative ring. The Gram matrix of `β` in a basis is alternating and, by nondegeneracy,
has nonzero determinant, so its size `dim V` cannot be odd.

## Main results

* `Matrix.det_eq_zero_of_alternating_of_odd`: an alternating matrix of odd size has
  determinant zero.
* `LinearMap.BilinForm.even_finrank_of_isAlt_of_injective`: a nondegenerate alternating
  bilinear form exists only on an even-dimensional space.

## Implementation notes

The source assumes `char K ≠ 2` in its proof (where `(-1)ᵇ = 1` forces `b` even). The
statement holds over every field, and is proved here without that assumption, by passing
through the generic alternating matrix over `ℤ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
-/

@[expose] public section

open Matrix

namespace Matrix

/-- The generic alternating `n × n` matrix over `MvPolynomial (Fin n × Fin n) ℤ`: entry `X (i, j)`
above the diagonal, `-X (j, i)` below it, and `0` on it. -/
noncomputable def genericAlternating (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
  fun i j => if i < j then MvPolynomial.X (i, j) else if j < i then -MvPolynomial.X (j, i) else 0

lemma genericAlternating_transpose (n : ℕ) :
    (genericAlternating n)ᵀ = -genericAlternating n := by
  ext i j
  simp only [transpose_apply, neg_apply, genericAlternating]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, not_lt.mpr h.le]
  · simp
  · simp [h, not_lt.mpr h.le]

lemma det_genericAlternating_of_odd {n : ℕ} (hn : Odd n) :
    (genericAlternating n).det = 0 := by
  have h := congrArg Matrix.det (genericAlternating_transpose n)
  rw [det_transpose, det_neg, Fintype.card_fin, hn.neg_one_pow, neg_one_mul] at h
  have h2 : (2 : MvPolynomial (Fin n × Fin n) ℤ) * (genericAlternating n).det = 0 := by
    rw [two_mul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

/-- An alternating square matrix (zero diagonal, `Aᵀ = -A`) of odd size has determinant zero,
over any commutative ring. -/
theorem det_eq_zero_of_alternating_of_odd {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hdiag : ∀ i, A i i = 0) (hskew : Aᵀ = -A) (hn : Odd n) :
    A.det = 0 := by
  let f : MvPolynomial (Fin n × Fin n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    (fun p => A p.1 p.2)
  have hmap : (genericAlternating n).map f = A := by
    ext i j
    simp only [map_apply, genericAlternating]
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, f]
    · simp [hdiag]
    · simp only [not_lt.mpr h.le, ite_false, h, ite_true, map_neg, f, MvPolynomial.eval₂Hom_X']
      have := congrFun (congrFun hskew i) j
      simp only [transpose_apply, neg_apply] at this
      rw [this, neg_neg]
  have hdet := RingHom.map_det f (genericAlternating n)
  rw [RingHom.mapMatrix_apply, hmap, det_genericAlternating_of_odd hn, map_zero] at hdet
  exact hdet.symm

end Matrix

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A bilinear form `β` on a finite-dimensional vector space which is alternating
(`β x x = 0` for all `x`) and nondegenerate (`x ↦ β x ·` injective) forces `dim V` to be even. -/
@[weil "lem_fk401_alternating_nondegenerate_even_dimension"]
theorem even_finrank_of_isAlt_of_injective (β : LinearMap.BilinForm K V) (hβ : β.IsAlt)
    (hinj : Function.Injective β) : Even (Module.finrank K V) := by
  set b := Module.finBasis K V
  set A := BilinForm.toMatrix b β
  have hnd : β.Nondegenerate := nondegenerate_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hinj)
  have hdet : A.det ≠ 0 := (nondegenerate_iff_det_ne_zero b).mp hnd
  have hdiag : ∀ i, A i i = 0 := fun i => by simp [A, BilinForm.toMatrix_apply, hβ.self_eq_zero]
  have hskew : Aᵀ = -A := by
    ext i j
    simp [A, BilinForm.toMatrix_apply, ← hβ.neg_eq (b i) (b j)]
  by_contra hodd
  exact hdet (Matrix.det_eq_zero_of_alternating_of_odd A hdiag hskew
    (Nat.not_even_iff_odd.mp hodd))

end LinearMap.BilinForm
