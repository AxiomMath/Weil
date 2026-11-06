module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing
public import Weil.Attr

/-!
# Endomorphisms pure of weight `w` along an embedding `ι : K →+* ℂ`

Let `K` be a field, `V` a finite-dimensional `K`-vector space, `φ` an endomorphism of `V`,
`Q` a natural number, `w` an integer and `ι : K →+* ℂ` a ring homomorphism. The endomorphism
`φ` is `ι`-pure of weight `w` relative to `Q` if every complex root `z` of the characteristic
polynomial of `φ` read along `ι` is algebraic over `ℚ` and satisfies `|z| = Q ^ (w / 2)`.

This notion is `Stacks.EtaleCohomology.IsCharpolyPureOfWeight Q ι w φ`, whose roots are
`Q`-Weil numbers of weight `w` (`Stacks.EtaleCohomology.IsWeilNumber`). This file identifies
it with the unfolded condition, both in terms of `Polynomial.IsRoot` and of the multiset
`Polynomial.roots`.

## Main results

* `Stacks.EtaleCohomology.isCharpolyPureOfWeight_iff`: `φ` is `ι`-pure of weight `w` relative
  to `Q` iff every root of `φ.charpoly.map ι` in `ℂ` is algebraic over `ℚ` of absolute value
  `Q ^ (w / 2)`.
* `Stacks.EtaleCohomology.isCharpolyPureOfWeight_iff_forall_mem_roots`: the same with the
  roots taken in `(φ.charpoly.map ι).roots`.

## Implementation notes

The source assumes `Q ≥ 2`; the definition makes sense, and is stated here, for every natural
number `Q`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §4.
-/

@[expose] public section

namespace Stacks.EtaleCohomology

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An endomorphism `φ` of a finite-dimensional `K`-vector space is `ι`-pure of weight `w`
relative to `Q` (`IsCharpolyPureOfWeight Q ι w φ`) iff every complex root of its characteristic
polynomial read along `ι : K →+* ℂ` is algebraic over `ℚ` and has absolute value
`Q ^ (w / 2)`. -/
@[weil "def_fk404_charpoly_pure_of_weight"]
theorem isCharpolyPureOfWeight_iff (Q : ℕ) (ι : K →+* ℂ) (w : ℤ) (φ : Module.End K V) :
    IsCharpolyPureOfWeight Q ι w φ ↔
      ∀ z : ℂ, (φ.charpoly.map ι).IsRoot z →
        IsAlgebraic ℚ z ∧ ‖z‖ = (Q : ℝ) ^ ((w : ℝ) / 2) :=
  forall₂_congr fun _ _ => ⟨fun h => ⟨h.isAlgebraic, h.norm_eq⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `ι`-purity of weight `w` read on the multiset of roots of `φ.charpoly.map ι`. -/
theorem isCharpolyPureOfWeight_iff_forall_mem_roots (Q : ℕ) (ι : K →+* ℂ) (w : ℤ)
    (φ : Module.End K V) :
    IsCharpolyPureOfWeight Q ι w φ ↔
      ∀ z ∈ (φ.charpoly.map ι).roots, IsAlgebraic ℚ z ∧ ‖z‖ = (Q : ℝ) ^ ((w : ℝ) / 2) := by
  have hne : φ.charpoly.map ι ≠ 0 := (φ.charpoly_monic.map ι).ne_zero
  rw [isCharpolyPureOfWeight_iff]
  exact forall_congr' fun z => by rw [Polynomial.mem_roots hne]

end Stacks.EtaleCohomology

end
