module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.BigOperators.Intervals
public import WeilFrontier.LinearAlgebra.PerfectPairing.SelfDualityDeterminant

/-!
# The functional equation of a family of characteristic polynomials

Let `K` be a field of characteristic zero, `L` an algebraically closed extension of `K`,
`n, q` natural numbers with `q ≠ 0` and `c = q ^ n`. Let `χ ν ∈ K[X]` (`0 ≤ ν ≤ 2n`) be monic
polynomials with nonzero constant term, of degrees `b ν`, such that

* (duality) the roots in `L` of `χ (2n - ν)` are the `c / μ`, `μ` running over the roots of `χ ν`
  (with multiplicities);
* (middle) if `n` is odd, `b n` is even and every square root `γ` of `c` in `L` is a root of
  `χ n` of even multiplicity.

Write `P ν = reverse (χ ν) = ∏ (1 - μ t)`, `e = ∑ (-1) ^ ν b ν` and
`ε = 1` if `n` is odd, `ε = (-1) ^ N` with `N` the multiplicity of `q ^ (n / 2)` as a root of
`χ n` if `n` is even. Then `n e` is even and, in `K(t)`,
`∏ P ν (1 / (c t)) ^ (-1) ^ (ν + 1) = ε q ^ (n e / 2) t ^ e ∏ P ν (t) ^ (-1) ^ (ν + 1)`.

This is the algebraic part of Deligne's functional equation of the zeta function of a smooth
projective variety over a finite field, with `χ ν` the characteristic polynomial of the
geometric Frobenius on `H^ν` and `e` the Euler characteristic.

The proof: duality gives `b (2n - ν) = b ν` and the polynomial identity
`χ (2n - ν) (0) · χ ν (c X) = c ^ (b ν) · P (2n - ν)`, so
`P ν (1 / (c t)) = t ^ (-b ν) · χ (2n - ν) (0)⁻¹ · P (2n - ν) (t)`; reindexing `ν ↦ 2n - ν`
reduces the identity to the value of `∏ χ ν (0) ^ (-1) ^ ν`. Pairing `ν` with `2n - ν`, and using
`χ ν (0) · χ (2n - ν) (0) = c ^ (b ν)`, this is `q ^ (n e / 2)` times the sign
`χ n (0) / q ^ (n b n / 2) = ε`, which follows from the pairing of the roots of `χ n` under
`μ ↦ c / μ` (`Multiset.prod_eq_neg_one_pow_count_mul_pow_card`).

## Main results

* `Weil.even_mul_sum_neg_one_pow_mul_natDegree`: `n e` is even.
* `Weil.prod_aeval_inv_reverse_zpow_eq`: the functional equation in `RatFunc K`.
* `Weil.aeval_inv_reverse_eq`: the factor identity `P ν (1 / (c t)) = t ^ (-b) a⁻¹ P (2n - ν) (t)`.
* `Weil.C_coeff_zero_mul_comp_eq_C_pow_mul_reverse`: the polynomial form of the duality.
* `Weil.coeff_zero_eq_sign_mul_pow`: the constant term of the self-dual `χ n` is
  `ε q ^ (n b n / 2)`.
* `Weil.prod_inv_coeff_zero_zpow_eq`: `∏ χ ν (0) ^ (-1) ^ ν = ε q ^ (n e / 2)`.

## Implementation notes

`P ν (1 / (q ^ n t))` is written `aeval ((algebraMap K (RatFunc K) (q ^ n) * RatFunc.X)⁻¹) (P ν)`
and `P ν (t)` is `algebraMap K[X] (RatFunc K) (P ν)`. The duality hypothesis is stated through
the roots in `L`, as for characteristic polynomials of a `c`-duality of linear maps. The
characteristic zero hypothesis is used only through `(q : K) ≠ 0`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

public section

open Polynomial Finset

namespace Weil

/-- A product over `range (2n + 1)` splits into the pairs `{ν, 2n - ν}` for `ν < n` and the
middle factor. -/
@[to_additive sum_range_two_mul_add_one]
theorem prod_range_two_mul_add_one {M : Type*} [CommMonoid M] (F : ℕ → M) (n : ℕ) :
    ∏ ν ∈ range (2 * n + 1), F ν = (∏ ν ∈ range n, F ν * F (2 * n - ν)) * F n := by
  rw [show 2 * n + 1 = (n + 1) + n by ring, prod_range_add, prod_range_succ, prod_mul_distrib,
    ← prod_range_reflect (fun x => F (n + 1 + x)) n]
  have : ∀ ν ∈ range n, F (n + 1 + (n - 1 - ν)) = F (2 * n - ν) := by
    intro ν hν; rw [mem_range] at hν; congr 1; omega
  rw [prod_congr rfl this]; exact mul_right_comm _ _ _

/-- The reverse commutes with an injective change of coefficients. -/
theorem reverse_map_of_injective {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : Function.Injective f) (p : R[X]) : (p.map f).reverse = p.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

/-- For `p = ∏ (X - μ)` over a multiset of nonzero `μ` and `g = ∏ (X - c / μ)`,
`p(0) · g(c X) = c ^ (deg p) · reverse p`. -/
theorem C_coeff_zero_mul_prod_X_sub_C_div_comp {L : Type*} [Field L] (c : L) {s : Multiset L}
    (hs : (0 : L) ∉ s) :
    C ((s.map fun μ => X - C μ).prod.coeff 0) * (s.map fun μ => X - C (c / μ)).prod.comp (C c * X)
      = C (c ^ Multiset.card s) * (s.map fun μ => X - C μ).prod.reverse := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one_zero,
      one_comp, mul_one]
    rw [← C_1, reverse_C]; simp
  | cons a s ih =>
    have ha : a ≠ 0 := fun h => hs (h ▸ Multiset.mem_cons_self a s)
    have hs' : (0 : L) ∉ s := fun h => hs (Multiset.mem_cons_of_mem h)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, mul_coeff_zero, mul_comp,
      reverse_mul_of_domain, C_mul, pow_succ]
    have h1 : C ((X - C a).coeff 0) * (X - C (c / a)).comp (C c * X) = C c * (X - C a).reverse := by
      have h : C a * C (c / a) = C c := by rw [← C_mul, mul_div_cancel₀ c ha]
      have hr : (X - C a).reverse = 1 - C a * X := by
        rw [sub_eq_add_neg, ← C_neg, reverse_add_C]
        have hX : (X : L[X]).reverse = 1 := by
          rw [← one_mul X, reverse_mul_X, ← C_1, reverse_C]
        simp [hX]; ring
      rw [hr]; simp
      linear_combination h
    calc _ = (C ((X - C a).coeff 0) * (X - C (c / a)).comp (C c * X)) *
          (C ((s.map fun μ => X - C μ).prod.coeff 0) *
            (s.map fun μ => X - C (c / μ)).prod.comp (C c * X)) := by ring
      _ = _ := by rw [h1, ih hs']; ring


section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]

omit [IsAlgClosed L] in
/-- A polynomial with nonzero constant term has no root `0` in any extension. -/
theorem zero_notMem_roots_map {f : K[X]} (hf0 : f.coeff 0 ≠ 0) :
    (0 : L) ∉ (f.map (algebraMap K L)).roots := by
  intro h
  have h' := (mem_roots'.mp h).2
  rw [IsRoot, eval_map, eval₂_at_zero] at h'
  exact hf0 ((map_eq_zero_iff _ (algebraMap K L).injective).mp h')

/-- If the roots of `g` in an algebraically closed `L` are the `c / μ`, `μ` the roots of `f`,
then `g` and `f` have the same degree. -/
theorem natDegree_eq_of_map_eq_prod_roots {c : K} {f g : K[X]}
    (hfg : g.map (algebraMap K L) =
      ((f.map (algebraMap K L)).roots.map fun μ => X - C (algebraMap K L c / μ)).prod) :
    g.natDegree = f.natDegree := by
  have h := congrArg natDegree hfg
  rw [natDegree_map_eq_of_injective (algebraMap K L).injective,
    show ((f.map (algebraMap K L)).roots.map fun μ => X - C (algebraMap K L c / μ)) =
      (((f.map (algebraMap K L)).roots.map (algebraMap K L c / ·)).map fun μ => X - C μ) by
      rw [Multiset.map_map]; rfl,
    natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map,
    ← (IsAlgClosed.splits _).natDegree_eq_card_roots,
    natDegree_map_eq_of_injective (algebraMap K L).injective] at h
  exact h

/-- **Duality as a polynomial identity.** If `f` is monic with `f(0) ≠ 0` and the roots of `g`
in an algebraically closed `L` are the `c / μ`, `μ` the roots of `f`, then
`f(0) · g(c X) = c ^ (deg f) · reverse f` in `K[X]`. -/
theorem C_coeff_zero_mul_comp_eq_C_pow_mul_reverse {c : K} {f g : K[X]} (hf : f.Monic)
    (hf0 : f.coeff 0 ≠ 0)
    (hfg : g.map (algebraMap K L) =
      ((f.map (algebraMap K L)).roots.map fun μ => X - C (algebraMap K L c / μ)).prod) :
    C (f.coeff 0) * g.comp (C c * X) = C (c ^ f.natDegree) * f.reverse := by
  apply map_injective (algebraMap K L) (algebraMap K L).injective
  rw [Polynomial.map_mul, Polynomial.map_mul, map_C, map_C, map_comp, Polynomial.map_mul, map_C,
    map_X, ← reverse_map_of_injective (algebraMap K L).injective, hfg, map_pow,
    ← natDegree_map_eq_of_injective (algebraMap K L).injective f, ← coeff_map]
  set F := f.map (algebraMap K L)
  have hF : F = (F.roots.map fun μ => X - C μ).prod :=
    (IsAlgClosed.splits F).eq_prod_roots_of_monic (hf.map _)
  have key := C_coeff_zero_mul_prod_X_sub_C_div_comp (algebraMap K L c)
    (zero_notMem_roots_map (L := L) hf0)
  rw [← hF, ← (IsAlgClosed.splits F).natDegree_eq_card_roots] at key
  exact key

/-- The constant terms in the duality identity: `f(0) · g(0) = c ^ (deg f)`. -/
theorem coeff_zero_mul_coeff_zero_eq_pow {c : K} {f g : K[X]} (hf : f.Monic)
    (hfg : C (f.coeff 0) * g.comp (C c * X) = C (c ^ f.natDegree) * f.reverse) :
    f.coeff 0 * g.coeff 0 = c ^ f.natDegree := by
  have h := congrArg (eval 0) hfg
  simp only [eval_mul, eval_C, eval_comp, eval_X, mul_zero, ← coeff_zero_eq_eval_zero,
    coeff_zero_reverse, hf.leadingCoeff, mul_one] at h
  exact h

/-- **The factor identity.** If `a · g(c X) = c ^ (deg g) · reverse f`, then in `K(t)`,
`(reverse g)(1 / (c t)) = a⁻¹ t ^ (-deg g) (reverse f)(t)`. -/
theorem aeval_inv_reverse_eq {c a : K} {f g : K[X]} (hc : c ≠ 0) (ha : a ≠ 0)
    (hfg : C a * g.comp (C c * X) = C (c ^ g.natDegree) * f.reverse) :
    aeval ((algebraMap K (RatFunc K) c * RatFunc.X)⁻¹) g.reverse =
      (algebraMap K (RatFunc K) a)⁻¹ * RatFunc.X ^ (-(g.natDegree : ℤ)) *
        algebraMap K[X] (RatFunc K) f.reverse := by
  set x : RatFunc K := algebraMap K (RatFunc K) c * RatFunc.X
  have hc' : algebraMap K (RatFunc K) c ≠ 0 := by simpa using hc
  have ha' : algebraMap K (RatFunc K) a ≠ 0 := by simpa using ha
  have hx : x ≠ 0 := mul_ne_zero hc' RatFunc.X_ne_zero
  let _ : Invertible x := invertibleOfNonzero hx
  have h1 := eval₂_reverse_mul_pow (algebraMap K (RatFunc K)) x g
  rw [invOf_eq_inv, ← aeval_def, ← aeval_def] at h1
  have h2 := congrArg (aeval (RatFunc.X : RatFunc K)) hfg
  rw [map_mul, map_mul, aeval_C, aeval_C, aeval_comp, map_mul, aeval_C, aeval_X,
    RatFunc.aeval_X_left_eq_algebraMap] at h2
  rw [zpow_neg, zpow_natCast]
  have hX : (RatFunc.X : RatFunc K) ^ g.natDegree ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  have hxb : x ^ g.natDegree ≠ 0 := pow_ne_zero _ hx
  rw [← h1] at h2
  generalize aeval x⁻¹ g.reverse = y at h2 ⊢
  simp only [x, mul_pow, map_pow] at h2 hxb ⊢
  have h3 : algebraMap K (RatFunc K) a * y * RatFunc.X ^ g.natDegree =
      algebraMap K[X] (RatFunc K) f.reverse := by
    apply mul_left_cancel₀ (pow_ne_zero g.natDegree hc')
    linear_combination h2
  field_simp
  linear_combination h3


omit [IsAlgClosed L] in
/-- A self-dual `f` has its roots invariant under `μ ↦ c / μ`. -/
theorem map_div_roots_eq_roots {c : K} {f : K[X]}
    (hff : f.map (algebraMap K L) =
      ((f.map (algebraMap K L)).roots.map fun μ => X - C (algebraMap K L c / μ)).prod) :
    (f.map (algebraMap K L)).roots.map (algebraMap K L c / ·) = (f.map (algebraMap K L)).roots := by
  conv_rhs => rw [hff]
  rw [show ((f.map (algebraMap K L)).roots.map fun μ => X - C (algebraMap K L c / μ)) =
      (((f.map (algebraMap K L)).roots.map (algebraMap K L c / ·)).map fun μ => X - C μ) by
      rw [Multiset.map_map]; rfl, roots_multiset_prod_X_sub_C]

/-- **The constant term of a self-dual polynomial.** Let `f` be monic with `f(0) ≠ 0` whose
roots in an algebraically closed `L` are invariant under `μ ↦ q ^ n / μ`, and, for `n` odd, of
even degree with every square root of `q ^ n` a root of even multiplicity. Then
`f(0) = ε q ^ (n deg f / 2)`, where `ε = 1` for `n` odd and `ε = (-1) ^ N` for `n` even, `N` the
multiplicity of `q ^ (n / 2)` as a root of `f`. -/
theorem coeff_zero_eq_sign_mul_pow {n q : ℕ} {f : K[X]} (hf : f.Monic) (hf0 : f.coeff 0 ≠ 0)
    (hff : f.map (algebraMap K L) =
      ((f.map (algebraMap K L)).roots.map fun μ => X - C (algebraMap K L ((q : K) ^ n) / μ)).prod)
    (hodd : Odd n → Even f.natDegree ∧ ∀ γ : L, γ ^ 2 = algebraMap K L ((q : K) ^ n) →
      Even ((f.map (algebraMap K L)).rootMultiplicity γ)) :
    f.coeff 0 = (((if Odd n then 1 else (-1) ^ f.rootMultiplicity ((q : K) ^ (n / 2)) : ℤ)) : K) *
      (q : K) ^ (n * f.natDegree / 2) := by
  classical
  set φ := algebraMap K L
  set F := f.map φ
  set s := F.roots
  have hs : s.map (φ ((q : K) ^ n) / ·) = s := map_div_roots_eq_roots hff
  have h0 : (0 : L) ∉ s := zero_notMem_roots_map hf0
  have hsplit := IsAlgClosed.splits F
  have hb : Multiset.card s = f.natDegree := by
    rw [← hsplit.natDegree_eq_card_roots, natDegree_map_eq_of_injective φ.injective]
  have hcoeff : φ (f.coeff 0) = (-1) ^ f.natDegree * s.prod := by
    rw [← coeff_map, hsplit.coeff_zero_eq_prod_roots_of_monic (hf.map φ),
      natDegree_map_eq_of_injective φ.injective]
  apply φ.injective
  rw [hcoeff, map_mul, map_intCast, map_pow, map_natCast]
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hn
  · have hn : ¬ Odd (m + m) := Nat.not_odd_iff_even.mpr ⟨m, rfl⟩
    have hm : (m + m) / 2 = m := by omega
    rw [show (m + m) * f.natDegree / 2 = m * f.natDegree by
      rw [← two_mul, mul_assoc, Nat.mul_div_cancel_left _ two_pos], hm]
    simp only [hn, ↓reduceIte]
    set γ := φ ((q : K) ^ m)
    have hγ : (-γ) ^ 2 = φ ((q : K) ^ (m + m)) := by
      rw [neg_sq, ← map_pow, ← pow_mul, mul_two]
    have hγ' : (q : L) ^ (m * f.natDegree) = γ ^ f.natDegree := by simp [γ, pow_mul]
    have h1 : ((-1 : L)) ^ f.natDegree * (-1) ^ f.natDegree = 1 := by rw [← mul_pow]; simp
    rw [Multiset.prod_eq_neg_one_pow_count_mul_pow_card hγ h0 hs, neg_neg, count_roots, hb,
      ← eq_rootMultiplicity_map φ.injective, neg_pow γ, hγ']
    push_cast
    linear_combination ((-1 : L) ^ rootMultiplicity ((q : K) ^ m) f * γ ^ f.natDegree) * h1
  · obtain ⟨hbe, hγe⟩ := hodd hn
    obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (φ ((q : K) ^ n)) two_pos
    have hNe := hγe (-γ) (by rw [neg_sq, hγ])
    simp only [hn, ↓reduceIte]
    rw [Multiset.prod_eq_neg_one_pow_count_mul_pow_card hγ h0 hs, count_roots, hb,
      hNe.neg_one_pow, hbe.neg_one_pow]
    obtain ⟨k, hk⟩ := hbe
    rw [hk, show n * (k + k) = 2 * (n * k) by ring, Nat.mul_div_cancel_left _ two_pos, ← two_mul,
      pow_mul, hγ, ← map_natCast φ, ← map_pow, ← map_pow, ← pow_mul]
    simp

/-- `n · deg f` is even when `deg f` is even for odd `n`. -/
theorem even_mul_natDegree {n : ℕ} {f : K[X]} (hodd : Odd n → Even f.natDegree) :
    Even (n * f.natDegree) := by
  rcases Nat.even_or_odd n with hn | hn
  · exact hn.mul_right _
  · exact (hodd hn).mul_left _

end Field

/-- `(-1) ^ (2n - j) = (-1) ^ j` for `j ≤ 2n`. -/
theorem neg_one_pow_two_mul_sub {R : Type*} [CommRing R] {n j : ℕ} (hj : j ≤ 2 * n) :
    (-1 : R) ^ (2 * n - j) = (-1) ^ j := by
  have h1 : (-1 : R) ^ (2 * n - j) * (-1) ^ j = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj, pow_mul]; simp
  have h2 : (-1 : R) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; simp
  linear_combination (-(-1 : R) ^ (2 * n - j)) * h2 + (-1 : R) ^ j * h1

/-- A product of integer powers of a nonzero element is the power by the sum. -/
theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroupWithZero G] {ι : Type*}
    (s : Finset ι) {x : G} (hx : x ≠ 0) (f : ι → ℤ) : ∏ i ∈ s, x ^ f i = x ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ hx]

/-- An element with `u * u = 1` is fixed by `u ↦ u ^ (± 1)`. -/
theorem zpow_neg_one_pow_of_mul_self_eq_one {G : Type*} [DivisionRing G] {u : G} (hu : u * u = 1)
    (k : ℕ) : u ^ ((-1 : ℤ) ^ k) = u := by
  rcases neg_one_pow_eq_or ℤ k with h | h
  · rw [h, zpow_one]
  · rw [h, zpow_neg_one]; exact inv_eq_of_mul_eq_one_left hu

section Main

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L] {n q : ℕ} {χ : ℕ → K[X]}

/-- Under duality, `∑_{ν ≤ 2n} (-1) ^ ν b ν = 2 ∑_{ν < n} (-1) ^ ν b ν + (-1) ^ n b n`. -/
theorem sum_neg_one_pow_mul_natDegree_eq
    (hR1 : ∀ ν ≤ 2 * n, (χ (2 * n - ν)).map (algebraMap K L) =
      (((χ ν).map (algebraMap K L)).roots.map
        fun μ => X - C (algebraMap K L ((q : K) ^ n) / μ)).prod) :
    ∑ ν ∈ range (2 * n + 1), (-1) ^ ν * ((χ ν).natDegree : ℤ) =
      2 * ∑ ν ∈ range n, (-1) ^ ν * ((χ ν).natDegree : ℤ) + (-1) ^ n * ((χ n).natDegree : ℤ) := by
  rw [sum_range_two_mul_add_one, mul_sum, ← sum_congr rfl]
  intro ν hν
  rw [mem_range] at hν
  rw [natDegree_eq_of_map_eq_prod_roots (hR1 ν (by omega)), neg_one_pow_two_mul_sub (by omega)]
  ring

/-- **`n e` is even**, where `e = ∑_{ν ≤ 2n} (-1) ^ ν deg χ ν`. -/
theorem even_mul_sum_neg_one_pow_mul_natDegree
    (hR1 : ∀ ν ≤ 2 * n, (χ (2 * n - ν)).map (algebraMap K L) =
      (((χ ν).map (algebraMap K L)).roots.map
        fun μ => X - C (algebraMap K L ((q : K) ^ n) / μ)).prod)
    (hodd : Odd n → Even (χ n).natDegree) :
    Even ((n : ℤ) * ∑ ν ∈ range (2 * n + 1), (-1) ^ ν * ((χ ν).natDegree : ℤ)) := by
  obtain ⟨m, hm⟩ := even_mul_natDegree hodd
  have hm' : (n : ℤ) * (χ n).natDegree = m + m := by exact_mod_cast hm
  rw [sum_neg_one_pow_mul_natDegree_eq hR1]
  exact ⟨n * ∑ ν ∈ range n, (-1) ^ ν * ((χ ν).natDegree : ℤ) + (-1) ^ n * m, by
    linear_combination (-1 : ℤ) ^ n * hm'⟩

/-- **The constant of the functional equation.**
`∏_{ν ≤ 2n} χ ν (0)⁻¹ ^ (-1) ^ (ν + 1) = ε q ^ (n e / 2)`. -/
theorem prod_inv_coeff_zero_zpow_eq [CharZero K] (hq : q ≠ 0) (hmonic : ∀ ν, (χ ν).Monic)
    (h0 : ∀ ν, (χ ν).coeff 0 ≠ 0)
    (hR1 : ∀ ν ≤ 2 * n, (χ (2 * n - ν)).map (algebraMap K L) =
      (((χ ν).map (algebraMap K L)).roots.map
        fun μ => X - C (algebraMap K L ((q : K) ^ n) / μ)).prod)
    (hR2 : Odd n → Even (χ n).natDegree ∧ ∀ γ : L, γ ^ 2 = algebraMap K L ((q : K) ^ n) →
      Even (((χ n).map (algebraMap K L)).rootMultiplicity γ)) :
    ∏ ν ∈ range (2 * n + 1), ((χ ν).coeff 0)⁻¹ ^ ((-1 : ℤ) ^ (ν + 1)) =
      (((if Odd n then 1 else (-1) ^ (χ n).rootMultiplicity ((q : K) ^ (n / 2)) : ℤ)) : K) *
        (q : K) ^ ((n : ℤ) * (∑ ν ∈ range (2 * n + 1), (-1) ^ ν * ((χ ν).natDegree : ℤ)) / 2) := by
  have hq' : (q : K) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hinv : ∀ ν, ((χ ν).coeff 0)⁻¹ ^ ((-1 : ℤ) ^ (ν + 1)) = ((χ ν).coeff 0) ^ ((-1 : ℤ) ^ ν) := by
    intro ν; rw [inv_zpow', pow_succ, mul_neg_one, neg_neg]
  have hpair : ∀ ν ∈ range n, (χ ν).coeff 0 ^ ((-1 : ℤ) ^ ν) *
      (χ (2 * n - ν)).coeff 0 ^ ((-1 : ℤ) ^ (2 * n - ν)) =
      (q : K) ^ ((n : ℤ) * ((-1) ^ ν * ((χ ν).natDegree : ℤ))) := by
    intro ν hν
    rw [mem_range] at hν
    rw [neg_one_pow_two_mul_sub (by omega), ← mul_zpow,
      coeff_zero_mul_coeff_zero_eq_pow (hmonic ν)
        (C_coeff_zero_mul_comp_eq_C_pow_mul_reverse (hmonic ν) (h0 ν) (hR1 ν (by omega))),
      ← pow_mul, ← zpow_natCast, ← zpow_mul]
    congr 1; push_cast; ring
  obtain ⟨m, hm⟩ := even_mul_natDegree (fun h => (hR2 h).1)
  have hm' : (n : ℤ) * (χ n).natDegree = m + m := by exact_mod_cast hm
  set ε : ℤ := if Odd n then 1 else (-1) ^ (χ n).rootMultiplicity ((q : K) ^ (n / 2))
  have hε : (ε : K) * ε = 1 := by
    simp only [ε]; split_ifs
    · simp
    · push_cast; rw [← mul_pow]; simp
  rw [prod_congr rfl (fun ν _ => hinv ν), prod_range_two_mul_add_one, prod_congr rfl hpair,
    prod_zpow_eq_zpow_sum _ hq', coeff_zero_eq_sign_mul_pow (hmonic n) (h0 n)
      (by simpa [show 2 * n - n = n by omega] using hR1 n (by omega)) hR2, mul_zpow,
    zpow_neg_one_pow_of_mul_self_eq_one hε, show n * (χ n).natDegree / 2 = m by omega,
    sum_neg_one_pow_mul_natDegree_eq hR1,
    show (n : ℤ) * (2 * ∑ ν ∈ range n, (-1) ^ ν * ((χ ν).natDegree : ℤ) +
      (-1) ^ n * ((χ n).natDegree : ℤ)) =
      2 * (∑ ν ∈ range n, n * ((-1) ^ ν * ((χ ν).natDegree : ℤ)) + (-1) ^ n * m) by
      rw [← mul_sum]; linear_combination (-1 : ℤ) ^ n * hm',
    Int.mul_ediv_cancel_left _ two_ne_zero, zpow_add₀ hq', ← zpow_natCast, ← zpow_mul]
  rw [mul_comm (m : ℤ)]
  ring

/-- **The functional equation** (FK IV.1, algebraic part). With `P ν = reverse (χ ν)`,
`e = ∑ (-1) ^ ν deg χ ν` and `ε` as in `Weil.coeff_zero_eq_sign_mul_pow`, in `K(t)`:
`∏ P ν (1 / (q ^ n t)) ^ (-1) ^ (ν + 1) = ε q ^ (n e / 2) t ^ e ∏ P ν (t) ^ (-1) ^ (ν + 1)`. -/
theorem prod_aeval_inv_reverse_zpow_eq [CharZero K] (hq : q ≠ 0) (hmonic : ∀ ν, (χ ν).Monic)
    (h0 : ∀ ν, (χ ν).coeff 0 ≠ 0)
    (hR1 : ∀ ν ≤ 2 * n, (χ (2 * n - ν)).map (algebraMap K L) =
      (((χ ν).map (algebraMap K L)).roots.map
        fun μ => X - C (algebraMap K L ((q : K) ^ n) / μ)).prod)
    (hR2 : Odd n → Even (χ n).natDegree ∧ ∀ γ : L, γ ^ 2 = algebraMap K L ((q : K) ^ n) →
      Even (((χ n).map (algebraMap K L)).rootMultiplicity γ)) :
    ∏ ν ∈ range (2 * n + 1),
        (aeval ((algebraMap K (RatFunc K) ((q : K) ^ n) * RatFunc.X)⁻¹) (χ ν).reverse) ^
          ((-1 : ℤ) ^ (ν + 1)) =
      (((if Odd n then 1 else (-1) ^ (χ n).rootMultiplicity ((q : K) ^ (n / 2)) : ℤ)) :
          RatFunc K) *
        (q : RatFunc K) ^
          ((n : ℤ) * (∑ ν ∈ range (2 * n + 1), (-1) ^ ν * ((χ ν).natDegree : ℤ)) / 2) *
        RatFunc.X ^ (∑ ν ∈ range (2 * n + 1), (-1) ^ ν * ((χ ν).natDegree : ℤ)) *
        ∏ ν ∈ range (2 * n + 1),
          (algebraMap K[X] (RatFunc K) (χ ν).reverse) ^ ((-1 : ℤ) ^ (ν + 1)) := by
  have hc : (q : K) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq)
  have hfac : ∀ ν ∈ range (2 * n + 1),
      aeval ((algebraMap K (RatFunc K) ((q : K) ^ n) * RatFunc.X)⁻¹) (χ ν).reverse =
        (algebraMap K (RatFunc K) ((χ (2 * n - ν)).coeff 0))⁻¹ *
          RatFunc.X ^ (-((χ ν).natDegree : ℤ)) *
            algebraMap K[X] (RatFunc K) (χ (2 * n - ν)).reverse := by
    intro ν hν
    rw [mem_range] at hν
    have hR := hR1 (2 * n - ν) (by omega)
    rw [show 2 * n - (2 * n - ν) = ν by omega] at hR
    have hD := C_coeff_zero_mul_comp_eq_C_pow_mul_reverse (hmonic (2 * n - ν)) (h0 _) hR
    rw [natDegree_eq_of_map_eq_prod_roots (hR1 ν (by omega))] at hD
    exact aeval_inv_reverse_eq hc (h0 _) hD
  have hconst : ∏ ν ∈ range (2 * n + 1),
      ((algebraMap K (RatFunc K) ((χ (2 * n - ν)).coeff 0))⁻¹) ^ ((-1 : ℤ) ^ (ν + 1)) =
      algebraMap K (RatFunc K)
        (∏ ν ∈ range (2 * n + 1), ((χ ν).coeff 0)⁻¹ ^ ((-1 : ℤ) ^ (ν + 1))) := by
    rw [map_prod, ← prod_range_reflect
      (fun ν => (algebraMap K (RatFunc K)) (((χ ν).coeff 0)⁻¹ ^ ((-1 : ℤ) ^ (ν + 1))))]
    refine prod_congr rfl fun ν hν => ?_
    rw [mem_range] at hν
    rw [show 2 * n + 1 - 1 - ν = 2 * n - ν by omega, map_zpow₀, map_inv₀, pow_succ, pow_succ,
      neg_one_pow_two_mul_sub (by omega)]
  have hP : ∏ ν ∈ range (2 * n + 1),
      (algebraMap K[X] (RatFunc K) (χ (2 * n - ν)).reverse) ^ ((-1 : ℤ) ^ (ν + 1)) =
      ∏ ν ∈ range (2 * n + 1),
        (algebraMap K[X] (RatFunc K) (χ ν).reverse) ^ ((-1 : ℤ) ^ (ν + 1)) := by
    rw [← prod_range_reflect
      (fun ν => (algebraMap K[X] (RatFunc K) (χ ν).reverse) ^ ((-1 : ℤ) ^ (ν + 1)))]
    refine prod_congr rfl fun ν hν => ?_
    rw [mem_range] at hν
    rw [show 2 * n + 1 - 1 - ν = 2 * n - ν by omega, pow_succ, pow_succ,
      neg_one_pow_two_mul_sub (by omega)]
  have hX : ∏ ν ∈ range (2 * n + 1),
      (RatFunc.X ^ (-((χ ν).natDegree : ℤ))) ^ ((-1 : ℤ) ^ (ν + 1)) =
      (RatFunc.X : RatFunc K) ^ (∑ ν ∈ range (2 * n + 1), (-1) ^ ν * ((χ ν).natDegree : ℤ)) := by
    rw [prod_congr rfl (fun ν _ => (zpow_mul _ _ _).symm),
      prod_zpow_eq_zpow_sum _ RatFunc.X_ne_zero]
    congr 1
    refine sum_congr rfl fun ν _ => ?_
    rw [pow_succ]; ring
  rw [prod_congr rfl (fun ν hν => by rw [hfac ν hν, mul_zpow, mul_zpow]), prod_mul_distrib,
    prod_mul_distrib, hconst, hP, hX, prod_inv_coeff_zero_zpow_eq hq hmonic h0 hR1 hR2, map_mul,
    map_intCast, map_zpow₀, map_natCast]

end Main

end Weil
