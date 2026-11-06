module

public import WeilFrontier.LinearAlgebra.PerfectPairing.Basic
public import Weil.Attr

/-!
# The determinant of a self-duality

Let `B : V × V → K` be a `c`-duality for `(f, f)` (`LinearMap.IsFrobeniusDuality B f f c`), with
`V` finite-dimensional of dimension `b`, let `L` be an algebraically closed extension of `K` and
`γ ∈ L` with `γ ^ 2 = c`. Then `det f = (-1) ^ N₋ * γ ^ b`, where `N₋` is the multiplicity of `-γ`
as an eigenvalue of `f`.

The eigenvalues of `f` in `L` are nonzero and, as a multiset, invariant under the involution
`μ ↦ c / μ` (`LinearMap.IsFrobeniusDuality.charpoly_map_eq_prod_roots`). The fixed points of this
involution are `γ` and `-γ`; the remaining eigenvalues fall into pairs `{μ, c / μ}`, each
contributing `c = γ ^ 2` to the product. Hence the product of all eigenvalues is
`γ ^ (2M) γ ^ N₊ (-γ) ^ N₋ = (-1) ^ N₋ γ ^ b`.

## Main results

* `Multiset.prod_eq_neg_one_pow_count_mul_pow_card`: a multiset of nonzero elements of a field
  invariant under `μ ↦ c / μ`, with `γ ^ 2 = c`, has product `(-1) ^ count (-γ) * γ ^ card`.
* `LinearMap.IsFrobeniusDuality.det_eq_neg_one_pow_mul_pow`: `det f = (-1) ^ N₋ * γ ^ b`.

## Implementation notes

No hypothesis on the characteristic of `K` is needed: in characteristic `2` one has `γ = -γ` and
`-1 = 1`, and the pairing argument still gives `det f = γ ^ b`. The multiplicity `N₋` is the
number of occurrences of `-γ` among the roots in `L` of the characteristic polynomial of `f`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

public section

open Polynomial

namespace Multiset

/-- A multiset of nonzero elements of a field which is invariant under `μ ↦ c / μ`, where
`γ ^ 2 = c`, has product `(-1) ^ (count (-γ)) * γ ^ card`. -/
theorem prod_eq_neg_one_pow_count_mul_pow_card {L : Type*} [Field L] [DecidableEq L]
    {c γ : L} (hγ : γ ^ 2 = c) :
    ∀ {s : Multiset L}, (0 : L) ∉ s → s.map (c / ·) = s →
      s.prod = (-1) ^ s.count (-γ) * γ ^ card s := by
  intro s
  induction hn : card s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  intro h0 hs
  subst hn
  rcases empty_or_exists_mem s with rfl | ⟨a, ha⟩
  · simp
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    have hc : c = 0 := by rw [← hγ]; ring
    have : (0 : L) ∈ s := by
      rw [← hs]; exact mem_map.mpr ⟨a, ha, by simp [hc]⟩
    exact h0 this
  obtain ⟨t, rfl⟩ := exists_cons_of_mem ha
  by_cases hfix : c / a = a
  · -- `a` is a fixed point, hence `a = γ` or `a = -γ`.
    have ht : t.map (c / ·) = t := by
      rw [map_cons, hfix] at hs; exact (cons_inj_right a).mp hs
    have ht0 : (0 : L) ∉ t := fun h => h0 (mem_cons_of_mem h)
    have iht := ih (card t) (by simp) rfl ht0 ht
    have ha2 : a ^ 2 = γ ^ 2 := by
      rw [hγ]
      calc a ^ 2 = (c / a) * a := by rw [hfix, sq]
        _ = c := div_mul_cancel₀ c ha0
    rw [prod_cons, iht, card_cons, count_cons]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha2 with h | h
    · subst h
      by_cases hne : -a = a
      · simp only [hne, ↓reduceIte]
        rw [pow_succ, pow_succ]
        nth_rewrite 1 [← hne]
        ring
      · simp only [hne, ↓reduceIte]
        ring
    · -- `a = -γ`
      subst h
      simp only [↓reduceIte]
      ring
  · -- `a` is paired with `c / a ≠ a`.
    have hb : c / a ∈ t := by
      have : c / a ∈ (a ::ₘ t).map (c / ·) := mem_map.mpr ⟨a, mem_cons_self a t, rfl⟩
      rw [hs] at this
      rcases mem_cons.mp this with h | h
      · exact absurd h hfix
      · exact h
    obtain ⟨u, rfl⟩ := exists_cons_of_mem hb
    have hc0 : c ≠ 0 := by rw [← hγ]; exact pow_ne_zero 2 hγ0
    have hba : c / (c / a) = a := by field_simp
    have hu : u.map (c / ·) = u := by
      rw [map_cons, map_cons, hba, cons_swap] at hs
      exact (cons_inj_right _).mp ((cons_inj_right _).mp hs)
    have hu0 : (0 : L) ∉ u := fun h => h0 (mem_cons_of_mem (mem_cons_of_mem h))
    have ihu := ih (card u) (by simp) rfl hu0 hu
    have hna : a ≠ -γ := by
      rintro rfl
      apply hfix
      rw [← hγ]; field_simp
    have hnb : c / a ≠ -γ := by
      intro h
      apply hna
      rw [← hba, h, ← hγ]; field_simp
    rw [prod_cons, prod_cons, ihu, card_cons, card_cons, count_cons, count_cons]
    simp only [Ne.symm hna, Ne.symm hnb, ↓reduceIte, add_zero]
    have : a * (c / a) = γ ^ 2 := by rw [hγ]; field_simp
    rw [← mul_assoc, this]
    ring

end Multiset

namespace LinearMap.IsFrobeniusDuality

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₗ[K] V →ₗ[K] K} {f : Module.End K V} {c : Kˣ}

/-- **The determinant of a self-duality.** Let `B` be a `c`-duality for `(f, f)` on a
finite-dimensional `V`, `L` an algebraically closed extension of `K` and `γ ∈ L` with
`γ ^ 2 = c`. Then `det f = (-1) ^ N₋ * γ ^ (dim V)`, where `N₋` is the multiplicity of `-γ` as a
root of the characteristic polynomial of `f` over `L`. -/
@[weil "lem_fk401_self_duality_determinant"]
theorem det_eq_neg_one_pow_mul_pow (h : B.IsFrobeniusDuality f f c)
    (L : Type*) [Field L] [Algebra K L] [IsAlgClosed L] [DecidableEq L] {γ : L}
    (hγ : γ ^ 2 = algebraMap K L c) :
    algebraMap K L (LinearMap.det f) =
      (-1) ^ (f.charpoly.map (algebraMap K L)).roots.count (-γ) *
        γ ^ Module.finrank K V := by
  set s := (f.charpoly.map (algebraMap K L)).roots with hs_def
  -- the determinant is the product of the eigenvalues
  have hdet : algebraMap K L (LinearMap.det f) = s.prod := by
    let b := Module.finBasis K V
    rw [← LinearMap.det_toMatrix b f, RingHom.map_det, hs_def, ← LinearMap.charpoly_toMatrix f b,
      ← Matrix.charpoly_map]
    exact Matrix.det_eq_prod_roots_charpoly _
  have hcard : Multiset.card s = Module.finrank K V := by
    rw [hs_def, splits_iff_card_roots.mp (IsAlgClosed.splits _),
      natDegree_map_eq_of_injective (algebraMap K L).injective, LinearMap.charpoly_natDegree]
  have hs0 : (0 : L) ∉ s := by
    intro h0
    have hu := (LinearMap.isUnit_det f h.isUnit_left).map (algebraMap K L)
    rw [hdet] at hu
    exact hu.ne_zero (Multiset.prod_eq_zero h0)
  have hinv : s.map (algebraMap K L c / ·) = s := by
    have hp := h.charpoly_map_eq_prod_roots L
    have hr := congrArg Polynomial.roots hp
    have hm : s.map (fun μ => X - C (algebraMap K L c / μ)) =
        (s.map (algebraMap K L c / ·)).map (fun μ => X - C μ) := by
      rw [Multiset.map_map]; rfl
    rw [← hs_def, hm, Polynomial.roots_multiset_prod_X_sub_C] at hr
    exact hr.symm
  rw [hdet, ← hcard]
  exact Multiset.prod_eq_neg_one_pow_count_mul_pow_card hγ hs0 hinv

end LinearMap.IsFrobeniusDuality
