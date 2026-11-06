module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DeligneConjectureConclusions

/-!
# The trivial representation has the conclusions of Deligne's conjecture

Let `G` be a topological group (in the source the fundamental group `π₁(S₀, ω)`) with Frobenius
elements `Fr : P → G` indexed by the closed points, and let `K` be a field of characteristic
zero (in the source `ℚ_ℓ`). The trivial representation `1 : G →* GL_r(K)` has the conclusions
of Deligne's conjecture along every ring homomorphism `ι : K →+* ℂ`: every Frobenius
characteristic polynomial is `(T - 1)ʳ`, whose coefficients are rational, whose only complex
root is `1`, and which is the characteristic polynomial of the Frobenii under the trivial
representation over every completion of `ℚ`.

## Main results

* `Weil.hasDeligneConclusions_one`: the trivial representation `1 : G →* GL_r(K)` has the
  conclusions of Deligne's conjecture, for every family of Frobenius elements, every residue
  characteristic `p` and every `ι : K →+* ℂ`.
* `Weil.continuous_one_representation`: the trivial representation is continuous.

## Implementation notes

The conclusions are Stacks' `Stacks.EtaleCohomology.HasDeligneConclusions`. The statement is
proved for the trivial representation of any rank `r`; the source's case is `r = 1`. The number
field in conclusions (1) and (3) is `ℚ` itself, as the bottom intermediate field of `K / ℚ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.4.
-/

@[expose] public section

open Polynomial NumberField IsDedekindDomain Stacks.EtaleCohomology

namespace Weil

variable {G : Type*} [Group G] [TopologicalSpace G] {P : Type*} {K : Type*} [Field K]
  [CharZero K]

/-- The bottom intermediate field `ℚ ⊆ K` is a number field. -/
theorem numberField_bot_intermediateField : NumberField (⊥ : IntermediateField ℚ K) where
  to_finiteDimensional := inferInstance

/-- The trivial representation `1 : G →* GL_r(R)` is continuous. -/
theorem continuous_one_representation {R : Type*} [CommRing R] [TopologicalSpace R] {r : ℕ} :
    Continuous (1 : G →* GL (Fin r) R) :=
  continuous_const

/-- **The trivial representation has the conclusions of Deligne's conjecture**: for every family
of Frobenius elements `Fr`, every `p` and every ring homomorphism `ι : K →+* ℂ`, the trivial
representation `1 : G →* GL_r(K)` satisfies `HasDeligneConclusions Fr p ι`. -/
@[weil "lem_fk404_trivial_representation_deligne_conclusions"]
theorem hasDeligneConclusions_one (Fr : P → G) (p : ℕ) (ι : K →+* ℂ) (r : ℕ) :
    HasDeligneConclusions Fr p ι (1 : G →* GL (Fin r) K) where
  exists_numberField := by
    refine ⟨⊥, inferInstance, fun x n => ?_⟩
    simp only [MonoidHom.one_apply, Units.val_one, Matrix.charpoly_one, Fintype.card_fin]
    rw [show ((X - 1 : K[X]) ^ r) = ((X - 1 : ℚ[X]) ^ r).map (algebraMap ℚ K) by simp,
      coeff_map]
    exact IntermediateField.algebraMap_mem _ _
  norm_eq_one := by
    intro x z hz
    simp only [MonoidHom.one_apply, Units.val_one, Matrix.charpoly_one, Fintype.card_fin,
      Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one, IsRoot, eval_pow,
      eval_sub, eval_X, eval_one] at hz
    rw [sub_eq_zero.1 (eq_zero_of_pow_eq_zero hz)]
    simp
  exists_companions := by
    refine ⟨⊥, numberField_bot_intermediateField, fun _ => (X - 1) ^ r, fun x => ?_,
      fun v _ => ⟨1, continuous_const, fun x => ?_⟩⟩
    · simp [Matrix.charpoly_one]
    · simp [Matrix.charpoly_one]

end Weil

end
