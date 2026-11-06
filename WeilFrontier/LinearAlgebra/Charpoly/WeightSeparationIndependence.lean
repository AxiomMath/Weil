module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Independence of the integer polynomials `P_ν` by separation of weights

Let `q > 1`, and for `0 ≤ ν ≤ 2n` let `χ_ν` be monic polynomials over a field `K` of
characteristic zero whose roots `μ` in an algebraic closure of `K` are algebraic over `ℚ` and pure
of weight `ν`: `|ι μ| = q ^ (ν / 2)` for every embedding `ι : ℚ(μ) → ℂ`. Suppose the reverse
polynomials `P_ν = reverse χ_ν` have integer models `p_ν ∈ ℤ[X]`, and that a power series
`Z ∈ ℤ⟦X⟧` satisfies `Z · ∏_{ν even} P_ν = ∏_{ν odd} P_ν`. Then the `p_ν` are determined by `Z`:
for a second such family `χ'_ν` over another field `K'` of characteristic zero with the same `Z`,
`p_ν = p'_ν` for every `ν`.

The proof follows the one of the independence of `ℓ` in Deligne's theorem: both identities descend
to `ℤ⟦X⟧`, and cross-multiplying gives `∏_{odd} p_ν · ∏_{even} p'_ν = ∏_{odd} p'_ν · ∏_{even} p_ν`
in `ℤ[X]`. Every complex root `z` of `p_ν` satisfies `|z⁻¹| = q ^ (ν / 2)`, since `z⁻¹` is
conjugate over `ℚ` to a root of `χ_ν`. As `q > 1`, the roots of different `p_ν` have different
absolute values, so comparing root multiplicities in `ℂ[X]` gives `p_ν` and `p'_ν` the same complex
roots; both have constant term `1`, hence they are equal.

## Main results

* `Weil.eq_of_weight_of_mul_eq`: the polynomials `p_ν` are independent of the family `χ_ν`.

## References

* [FK88] E. Freitag, R. Kiehl, *Etale Cohomology and the Weil Conjecture*, Chapter IV, §1,
  proof of Theorem 1.2.
-/

@[expose] public section

open Polynomial PowerSeries

namespace Weil

private lemma coeff_zero_eq_one_of_map_eq_reverse {K : Type*} [Field K] [CharZero K] {χ : K[X]}
    (hχ : χ.Monic) {p : ℤ[X]} (hp : p.map (Int.castRingHom K) = χ.reverse) : p.coeff 0 = 1 := by
  apply Int.cast_injective (α := K)
  have := congrArg (fun f => Polynomial.coeff f 0) hp
  simpa [Polynomial.coeff_map, coeff_zero_reverse, hχ.leadingCoeff] using this

private lemma norm_inv_eq_of_isRoot {K : Type*} [Field K] [CharZero K] {χ : K[X]} (hχ : χ.Monic)
    (w : ℝ) (hW : ∀ μ : AlgebraicClosure K, aeval μ χ = 0 →
      ∀ ι : IntermediateField.adjoin ℚ {μ} →+* ℂ,
        ‖ι (IntermediateField.AdjoinSimple.gen ℚ μ)‖ = w)
    {p : ℤ[X]} (hp : p.map (Int.castRingHom K) = χ.reverse) {z : ℂ}
    (hz : (p.map (Int.castRingHom ℂ)).IsRoot z) : ‖z⁻¹‖ = w := by
  have hp0 := coeff_zero_eq_one_of_map_eq_reverse hχ hp
  have hpne : p ≠ 0 := by rintro rfl; simp at hp0
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [IsRoot, ← coeff_zero_eq_eval_zero, Polynomial.coeff_map, hp0] at hz
    simp at hz
  set h : ℚ[X] := p.reverse.map (algebraMap ℤ ℚ) with hh
  have hne : h ≠ 0 := by
    rw [hh, Ne, Polynomial.map_eq_zero_iff (algebraMap ℤ ℚ).injective_int, reverse_eq_zero]
    exact hpne
  have hzr : aeval z⁻¹ h = 0 := by
    let : Invertible z := invertibleOfNonzero hz0
    rw [hh, aeval_map_algebraMap, aeval_def, ← invOf_eq_inv, eval₂_reverse_eq_zero_iff,
      algebraMap_int_eq, ← eval_map]
    exact hz
  have hint : IsIntegral ℚ z⁻¹ := (isAlgebraic_iff_isIntegral).1 ⟨h, hne, hzr⟩
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (minpoly ℚ z⁻¹)
    (minpoly.degree_pos hint).ne'
  have hμh : aeval μ h = 0 :=
    Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero (minpoly.dvd ℚ z⁻¹ hzr) hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero', hh, Polynomial.coeff_map, coeff_zero_reverse] at hμh
    simp [hpne] at hμh
  have hμχ : aeval μ χ = 0 := by
    let : Invertible μ := invertibleOfNonzero hμ0
    let : Invertible μ⁻¹ := invertibleOfNonzero (inv_ne_zero hμ0)
    rw [hh, aeval_map_algebraMap, aeval_def] at hμh
    rw [show μ = ⅟(μ⁻¹) by simp, eval₂_reverse_eq_zero_iff] at hμh
    rw [aeval_def, ← eval₂_reverse_eq_zero_iff, ← hp, eval₂_map, invOf_eq_inv]
    rwa [show (algebraMap K (AlgebraicClosure K)).comp (Int.castRingHom K) =
      algebraMap ℤ (AlgebraicClosure K) from RingHom.ext_int _ _]
  have hmin : minpoly ℚ μ = minpoly ℚ z⁻¹ :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hμ (minpoly.monic hint)).symm
  have hμint : IsIntegral ℚ μ := (isAlgebraic_iff_isIntegral).1
    ⟨minpoly ℚ z⁻¹, minpoly.ne_zero hint, hμ⟩
  have mem : z⁻¹ ∈ (minpoly ℚ μ).aroots ℂ := by
    rw [hmin, mem_aroots]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval ℚ z⁻¹⟩
  have := hW μ hμχ
    ((IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) hμint).symm ⟨_, mem⟩).toRingHom
  rwa [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen] at this

private lemma sum_eq_ite_of_forall_ne {s : Finset ℕ} {c : ℕ → ℕ} {ν : ℕ}
    (h : ∀ i ∈ s, i ≠ ν → c i = 0) : ∑ i ∈ s, c i = if ν ∈ s then c ν else 0 := by
  split_ifs with h'
  · exact Finset.sum_eq_single_of_mem _ h' h
  · exact Finset.sum_eq_zero fun i hi => h i hi (by rintro rfl; exact h' hi)

private lemma rpow_half_injective {q : ℕ} (hq : 1 < q) {a b : ℕ}
    (h : (q : ℝ) ^ ((a : ℝ) / 2) = (q : ℝ) ^ ((b : ℝ) / 2)) : a = b := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have h1 := (Real.rpow_le_rpow_left_iff hq').1 h.le
  have h2 := (Real.rpow_le_rpow_left_iff hq').1 h.ge
  have : (a : ℝ) = b := by linarith
  exact_mod_cast this

/-- The pulled-back cross-multiplied identity: from `Z * ∏_{even} P = ∏_{odd} P` over two
char-zero fields, the integer models satisfy `∏_{odd} p * ∏_{even} p' = ∏_{odd} p' * ∏_{even} p`. -/
private lemma int_prod_eq {K : Type*} [Field K] [CharZero K] (s t : Finset ℕ) (χ : ℕ → K[X])
    (p : ℕ → ℤ[X]) (hp : ∀ ν ∈ s ∪ t, (p ν).map (Int.castRingHom K) = (χ ν).reverse) (Z : ℤ⟦X⟧)
    (hZ : PowerSeries.map (Int.castRingHom K) Z * ∏ ν ∈ s, ((χ ν).reverse : K⟦X⟧) =
      ∏ ν ∈ t, ((χ ν).reverse : K⟦X⟧)) :
    Z * ((∏ ν ∈ s, p ν : ℤ[X]) : ℤ⟦X⟧) = ((∏ ν ∈ t, p ν : ℤ[X]) : ℤ⟦X⟧) := by
  apply PowerSeries.map_injective (Int.castRingHom K) Int.cast_injective
  have hc : ∀ (u : Finset ℕ) (f : ℕ → ℤ[X]),
      ((∏ i ∈ u, f i : ℤ[X]) : ℤ⟦X⟧) = ∏ i ∈ u, (f i : ℤ⟦X⟧) :=
    fun u f => map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℤ) : ℤ[X] →+* ℤ⟦X⟧) f u
  rw [map_mul, hc, hc, map_prod, map_prod]
  have h1 : ∏ ν ∈ s, ((χ ν).reverse : K⟦X⟧) =
      ∏ ν ∈ s, PowerSeries.map (Int.castRingHom K) (p ν : ℤ⟦X⟧) :=
    Finset.prod_congr rfl fun ν hν => by
      rw [← Polynomial.polynomial_map_coe, hp ν (Finset.mem_union_left _ hν)]
  have h2 : ∏ ν ∈ t, ((χ ν).reverse : K⟦X⟧) =
      ∏ ν ∈ t, PowerSeries.map (Int.castRingHom K) (p ν : ℤ⟦X⟧) :=
    Finset.prod_congr rfl fun ν hν => by
      rw [← Polynomial.polynomial_map_coe, hp ν (Finset.mem_union_right _ hν)]
  rwa [h1, h2] at hZ

theorem eq_of_weight_of_mul_eq {K K' : Type*} [Field K] [CharZero K] [Field K'] [CharZero K']
    (q : ℕ) (hq : 1 < q) (n : ℕ) (χ : ℕ → K[X]) (χ' : ℕ → K'[X])
    (hχ : ∀ ν, (χ ν).Monic) (hχ' : ∀ ν, (χ' ν).Monic)
    (hW : ∀ ν ∈ Finset.range (2 * n + 1), ∀ μ : AlgebraicClosure K, aeval μ (χ ν) = 0 →
      IsAlgebraic ℚ μ ∧ ∀ ι : IntermediateField.adjoin ℚ {μ} →+* ℂ,
        ‖ι (IntermediateField.AdjoinSimple.gen ℚ μ)‖ = (q : ℝ) ^ ((ν : ℝ) / 2))
    (hW' : ∀ ν ∈ Finset.range (2 * n + 1), ∀ μ : AlgebraicClosure K', aeval μ (χ' ν) = 0 →
      IsAlgebraic ℚ μ ∧ ∀ ι : IntermediateField.adjoin ℚ {μ} →+* ℂ,
        ‖ι (IntermediateField.AdjoinSimple.gen ℚ μ)‖ = (q : ℝ) ^ ((ν : ℝ) / 2))
    (p p' : ℕ → ℤ[X])
    (hp : ∀ ν ∈ Finset.range (2 * n + 1), (p ν).map (Int.castRingHom K) = (χ ν).reverse)
    (hp' : ∀ ν ∈ Finset.range (2 * n + 1), (p' ν).map (Int.castRingHom K') = (χ' ν).reverse)
    (Z : ℤ⟦X⟧)
    (hZ : PowerSeries.map (Int.castRingHom K) Z *
        ∏ ν ∈ (Finset.range (2 * n + 1)).filter Even, ((χ ν).reverse : K⟦X⟧) =
      ∏ ν ∈ (Finset.range (2 * n + 1)).filter (¬ Even ·), ((χ ν).reverse : K⟦X⟧))
    (hZ' : PowerSeries.map (Int.castRingHom K') Z *
        ∏ ν ∈ (Finset.range (2 * n + 1)).filter Even, ((χ' ν).reverse : K'⟦X⟧) =
      ∏ ν ∈ (Finset.range (2 * n + 1)).filter (¬ Even ·), ((χ' ν).reverse : K'⟦X⟧)) :
    ∀ ν ∈ Finset.range (2 * n + 1), p ν = p' ν := by
  classical
  set R := Finset.range (2 * n + 1) with hR
  set E := R.filter Even
  set O := R.filter (¬ Even ·)
  have hEO : E ∪ O = R := Finset.filter_union_filter_not_eq _ _
  -- the identity `∏_{odd} p * ∏_{even} p' = ∏_{odd} p' * ∏_{even} p` in `ℤ[X]`
  have hI := int_prod_eq E O χ p (hEO ▸ hp) Z hZ
  have hI' := int_prod_eq E O χ' p' (hEO ▸ hp') Z hZ'
  have key : (∏ ν ∈ O, p ν) * ∏ ν ∈ E, p' ν = (∏ ν ∈ O, p' ν) * ∏ ν ∈ E, p ν := by
    apply Polynomial.coe_injective ℤ
    rw [Polynomial.coe_mul, Polynomial.coe_mul, ← hI, ← hI']
    ring
  -- map to `ℂ[X]`
  set P : ℕ → ℂ[X] := fun ν => (p ν).map (Int.castRingHom ℂ) with hP
  set P' : ℕ → ℂ[X] := fun ν => (p' ν).map (Int.castRingHom ℂ) with hP'
  have keyC : (∏ ν ∈ O, P ν) * ∏ ν ∈ E, P' ν = (∏ ν ∈ O, P' ν) * ∏ ν ∈ E, P ν := by
    have := congrArg (Polynomial.map (Int.castRingHom ℂ)) key
    simpa only [Polynomial.map_mul, Polynomial.map_prod] using this
  have hc0 : ∀ ν ∈ R, (P ν).coeff 0 = 1 := fun ν hν => by
    simp [hP, Polynomial.coeff_map, coeff_zero_eq_one_of_map_eq_reverse (hχ ν) (hp ν hν)]
  have hc0' : ∀ ν ∈ R, (P' ν).coeff 0 = 1 := fun ν hν => by
    simp [hP', Polynomial.coeff_map, coeff_zero_eq_one_of_map_eq_reverse (hχ' ν) (hp' ν hν)]
  have hne : ∀ ν ∈ R, P ν ≠ 0 := fun ν hν h => by simpa [h] using hc0 ν hν
  have hne' : ∀ ν ∈ R, P' ν ≠ 0 := fun ν hν h => by simpa [h] using hc0' ν hν
  have hw : ∀ ν ∈ R, ∀ z, (P ν).IsRoot z → ‖z⁻¹‖ = (q : ℝ) ^ ((ν : ℝ) / 2) :=
    fun ν hν z hz => norm_inv_eq_of_isRoot (hχ ν) _ (fun μ hμ => (hW ν hν μ hμ).2) (hp ν hν) hz
  have hw' : ∀ ν ∈ R, ∀ z, (P' ν).IsRoot z → ‖z⁻¹‖ = (q : ℝ) ^ ((ν : ℝ) / 2) :=
    fun ν hν z hz => norm_inv_eq_of_isRoot (hχ' ν) _ (fun μ hμ => (hW' ν hν μ hμ).2) (hp' ν hν) hz
  have hER : E ⊆ R := Finset.filter_subset _ _
  have hOR : O ⊆ R := Finset.filter_subset _ _
  have hprod : ∀ (F : ℕ → ℂ[X]), (∀ ν ∈ R, F ν ≠ 0) → ∀ u ⊆ R, ∏ ν ∈ u, F ν ≠ 0 :=
    fun F hF u hu => Finset.prod_ne_zero_iff.2 fun ν hν => hF ν (hu hν)
  intro ν hν
  -- the complex root multisets of `P ν` and `P' ν` agree
  have hroots : (P ν).roots = (P' ν).roots := by
    ext z
    by_cases hz : ‖z⁻¹‖ = (q : ℝ) ^ ((ν : ℝ) / 2)
    · have hoff : ∀ (F : ℕ → ℂ[X]), (∀ μ ∈ R, ∀ z, (F μ).IsRoot z →
          ‖z⁻¹‖ = (q : ℝ) ^ ((μ : ℝ) / 2)) → ∀ u ⊆ R, ∀ i ∈ u, i ≠ ν →
          Multiset.count z (F i).roots = 0 := by
        intro F hF u hu i hi hiν
        refine Multiset.count_eq_zero.2 fun hm => hiν ?_
        exact rpow_half_injective hq ((hF i (hu hi) z (isRoot_of_mem_roots hm)).symm.trans hz)
      have := congrArg (fun f => Multiset.count z (Polynomial.roots f)) keyC
      rw [roots_mul (mul_ne_zero (hprod P hne O hOR) (hprod P' hne' E hER)),
        roots_mul (mul_ne_zero (hprod P' hne' O hOR) (hprod P hne E hER)),
        roots_prod _ _ (hprod P hne O hOR), roots_prod _ _ (hprod P' hne' E hER),
        roots_prod _ _ (hprod P' hne' O hOR), roots_prod _ _ (hprod P hne E hER)] at this
      simp only [Multiset.count_add, Multiset.count_bind, Finset.sum_map_val] at this
      rw [sum_eq_ite_of_forall_ne (hoff P hw O hOR), sum_eq_ite_of_forall_ne (hoff P' hw' E hER),
        sum_eq_ite_of_forall_ne (hoff P' hw' O hOR), sum_eq_ite_of_forall_ne (hoff P hw E hER)]
        at this
      by_cases he : Even ν
      · have ho : ¬ Odd ν := Nat.not_odd_iff_even.2 he
        simp [O, E, he, ho, hν, count_roots] at this ⊢
        omega
      · have ho : Odd ν := Nat.not_even_iff_odd.1 he
        simp [O, E, he, ho, hν, count_roots] at this ⊢
        omega
    · rw [Multiset.count_eq_zero.2 fun hm => hz (hw ν hν z (isRoot_of_mem_roots hm)),
        Multiset.count_eq_zero.2 fun hm => hz (hw' ν hν z (isRoot_of_mem_roots hm))]
  -- a polynomial over `ℂ` with constant term `1` is determined by its roots
  have hsplit := (IsAlgClosed.splits (P ν)).eq_prod_roots
  have hsplit' := (IsAlgClosed.splits (P' ν)).eq_prod_roots
  rw [hroots] at hsplit
  set Q := (Multiset.map (fun x => Polynomial.X - Polynomial.C x) (P' ν).roots).prod
  have h1 := hc0 ν hν
  have h1' := hc0' ν hν
  rw [hsplit, Polynomial.coeff_C_mul] at h1
  rw [hsplit', Polynomial.coeff_C_mul] at h1'
  have hlc : (P ν).leadingCoeff = (P' ν).leadingCoeff := by
    have hQ : Q.coeff 0 ≠ 0 := right_ne_zero_of_mul_eq_one h1
    exact mul_right_cancel₀ hQ (h1.trans h1'.symm)
  have hPP : P ν = P' ν := by rw [hsplit, hsplit', hlc]
  exact Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective hPP

end Weil
