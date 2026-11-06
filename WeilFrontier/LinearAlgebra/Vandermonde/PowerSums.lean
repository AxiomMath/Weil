module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Power sums of large exponent determine a multiset

Let `K` be an integral domain of characteristic zero and let `s`, `t` be multisets of nonzero
elements of `K`. If the power sums `∑_{a ∈ s} a ^ m` and `∑_{a ∈ t} a ^ m` agree for every
sufficiently large exponent `m`, then `s = t`.

The proof uses the linear independence of the distinct monoid homomorphisms
`Multiplicative ℕ →* K`, `m ↦ a ^ m` (Dedekind–Artin), applied to the sequences
`m ↦ a ^ (M + m)`: the coefficient of `m ↦ a ^ m` in the resulting relation is
`(count a s - count a t) * a ^ M`, which must vanish.

## Main results

* `Multiset.eq_of_forall_ge_sum_map_pow_eq`: power sums agreeing for all exponents `m ≥ M`
  force equality of multisets of nonzero elements in characteristic zero.

## Implementation notes

The characteristic zero hypothesis is necessary: in characteristic `p` the multiset consisting
of `p` copies of `1` has the same power sums as the empty multiset.
-/

@[expose] public section

namespace Multiset

variable {K : Type*} [CommRing K] [IsDomain K] [CharZero K]

/-- Two multisets of nonzero elements of a characteristic zero domain whose power sums agree
for all sufficiently large exponents are equal. -/
theorem eq_of_forall_ge_sum_map_pow_eq {s t : Multiset K} (hs : (0 : K) ∉ s) (ht : (0 : K) ∉ t)
    (M : ℕ) (h : ∀ m ≥ M, (s.map (· ^ m)).sum = (t.map (· ^ m)).sum) : s = t := by
  classical
  set S := (s + t).toFinset with hS
  -- power sums as finite sums over `S`
  have key : ∀ (u : Multiset K), u ≤ s + t → ∀ n : ℕ,
      (u.map (· ^ n)).sum = ∑ a ∈ S, (u.count a : K) * a ^ n := by
    intro u hu n
    rw [Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
    refine Finset.sum_subset (fun a ha => ?_) (fun a _ ha => ?_)
    · rw [hS, Multiset.mem_toFinset]
      exact Multiset.mem_of_le hu (Multiset.mem_toFinset.mp ha)
    · rw [Multiset.mem_toFinset, ← Multiset.count_eq_zero] at ha
      simp [ha]
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) K).comp (powersHom K)
    (powersHom K).injective
  rw [linearIndependent_iff'] at hli
  have hrel : ∑ a ∈ S, (((s.count a : K) - t.count a) * a ^ M) •
      ((⇑) ∘ powersHom K) a = 0 := by
    funext x
    simp only [Finset.sum_apply, Function.comp_apply, powersHom_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply]
    have := h (M + x.toAdd) (Nat.le_add_right _ _)
    rw [key s (Multiset.le_add_right _ _), key t (Multiset.le_add_left _ _)] at this
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pow_add, sub_mul, sub_mul, mul_assoc, mul_assoc]
  ext a
  by_cases ha : a ∈ S
  · have h0 := hli S _ hrel a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [hS, Multiset.mem_toFinset, Multiset.mem_add] at ha
      exact ha.elim hs ht
    rw [mul_eq_zero, sub_eq_zero] at h0
    exact_mod_cast h0.resolve_right (pow_ne_zero _ ha0)
  · rw [hS, Multiset.mem_toFinset, Multiset.mem_add, not_or] at ha
    rw [Multiset.count_eq_zero.mpr ha.1, Multiset.count_eq_zero.mpr ha.2]

end Multiset
