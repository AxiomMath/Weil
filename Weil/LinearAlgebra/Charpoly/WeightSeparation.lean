module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Rational coefficients of polynomials by separation of weights

Let `K` be a field of characteristic zero and let `χ 0, …, χ (2n)` be monic polynomials over `K`
such that every root `μ` of `χ ν` in an algebraic closure of `K` is algebraic over `ℚ` and
satisfies `|ι μ| = q ^ (ν / 2)` for every embedding `ι : ℚ(μ) → ℂ`, where `q > 1`. Suppose that the
alternating product `∏_{ν odd} (χ ν).reverse / ∏_{ν even} (χ ν).reverse` is a quotient `A / B` of
coprime polynomials `A, B ∈ ℚ[X]` with constant term `1`. Then each `(χ ν).reverse` has rational
coefficients, and divides `A` (for `ν` odd) or `B` (for `ν` even).

The proof works with polynomials over the algebraic closure `E` of `K`. Roots of different
weights are never equal, so the odd and even products are coprime and are the images of `A` and
`B` up to units. The rational polynomial `A` is then split according to the weights of its
irreducible factors over `ℚ`: all roots of an irreducible factor are conjugate over `ℚ`, hence
have the same weight, because the weight condition depends only on the minimal polynomial over
`ℚ`. The product of the factors of weight `ν`, normalized to constant term `1`, is the required
rational form of `(χ ν).reverse`.

## Main results

* `Weil.exists_rat_reverse_charpoly_of_weight`: under the hypotheses above, every
  `(χ ν).reverse` is the image of a polynomial `r ∈ ℚ[X]` with `r.coeff 0 = 1`, dividing `B` for
  `ν` even and `A` for `ν` odd.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, proof of
  Theorem 1.2.
-/

@[expose] public section

open Polynomial

namespace Weil

/-- `RevWt q x ν`: every complex conjugate `z` of `x` (a complex root of the minimal polynomial of
`x` over `ℚ`) has `|z|⁻¹ = q ^ (ν / 2)`. This condition depends only on `minpoly ℚ x`. -/
private def RevWt (q : ℕ) {L : Type*} [Field L] [CharZero L] (x : L) (ν : ℕ) : Prop :=
  ∀ z : ℂ, aeval z (minpoly ℚ x) = 0 → ‖z‖⁻¹ = (q : ℝ) ^ ((ν : ℝ) / 2)

private lemma revWt_inv {q : ℕ} {L : Type*} [Field L] [CharZero L] {μ : L} {ν : ℕ}
    (halg : IsAlgebraic ℚ μ)
    (h : ∀ ι : IntermediateField.adjoin ℚ {μ} →+* ℂ,
        ‖ι (IntermediateField.AdjoinSimple.gen ℚ μ)‖ = (q : ℝ) ^ ((ν : ℝ) / 2)) :
    RevWt q μ⁻¹ ν := by
  intro z hz
  have hint : IsIntegral ℚ μ⁻¹ := (halg.inv).isIntegral
  have hzr : z ∈ (minpoly ℚ μ⁻¹).aroots ℂ := by
    rw [mem_aroots]; exact ⟨minpoly.ne_zero hint, hz⟩
  let φ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := ℂ) hint).symm ⟨z, hzr⟩
  have hφ : φ (IntermediateField.AdjoinSimple.gen ℚ μ⁻¹) = z :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint ⟨z, hzr⟩
  have hle : IntermediateField.adjoin ℚ {μ} ≤ IntermediateField.adjoin ℚ {μ⁻¹} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    simpa using inv_mem (IntermediateField.mem_adjoin_simple_self ℚ μ⁻¹)
  have key := h ((φ.comp (IntermediateField.inclusion hle)).toRingHom)
  have hinc : IntermediateField.inclusion hle (IntermediateField.AdjoinSimple.gen ℚ μ) =
      (IntermediateField.AdjoinSimple.gen ℚ μ⁻¹)⁻¹ := by
    apply Subtype.ext; simp
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, hinc, map_inv₀, hφ] at key
  simpa using key


private lemma rpow_half_inj {q : ℕ} (hq : 1 < q) {ν μ : ℕ}
    (h : (q : ℝ) ^ ((ν : ℝ) / 2) = (q : ℝ) ^ ((μ : ℝ) / 2)) : ν = μ := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have : (ν : ℝ) / 2 = (μ : ℝ) / 2 := by
    rcases lt_trichotomy ((ν : ℝ) / 2) ((μ : ℝ) / 2) with h1 | h1 | h1
    · exact absurd h (Real.rpow_lt_rpow_of_exponent_lt hq' h1).ne
    · exact h1
    · exact absurd h (Real.rpow_lt_rpow_of_exponent_lt hq' h1).ne'
  exact_mod_cast (by linarith : (ν : ℝ) = μ)

/-- Two weights of an integral element agree. -/
private lemma revWt_unique {q : ℕ} (hq : 1 < q) {L : Type*} [Field L] [CharZero L] {x : L}
    (hx : IsIntegral ℚ x) {ν μ : ℕ} (h1 : RevWt q x ν) (h2 : RevWt q x μ) : ν = μ := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ (minpoly ℚ x) (minpoly.degree_pos hx).ne'
  exact rpow_half_inj hq ((h1 z hz).symm.trans (h2 z hz))

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]

private lemma isCoprime_of_revWt {q : ℕ} (hq : 1 < q) {f g : L[X]} {ν μ : ℕ} (hνμ : ν ≠ μ)
    (hf : ∀ x, eval x f = 0 → RevWt q x ν)
    (hg : ∀ x, eval x g = 0 → IsIntegral ℚ x ∧ RevWt q x μ) : IsCoprime f g := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed L L]
  intro a
  by_contra hc
  push Not at hc
  simp only [coe_aeval_eq_eval] at hc
  obtain ⟨hi, hw⟩ := hg a hc.2
  exact hνμ (revWt_unique hq hi (hf a hc.1) hw)

private lemma isCoprime_prod_of_revWt {q : ℕ} (hq : 1 < q) (g : ℕ → L[X]) {S T : Finset ℕ}
    (hST : Disjoint S T)
    (hg : ∀ ν ∈ S ∪ T, ∀ x, eval x (g ν) = 0 → IsIntegral ℚ x ∧ RevWt q x ν) :
    IsCoprime (∏ ν ∈ S, g ν) (∏ ν ∈ T, g ν) := by
  rw [IsCoprime.prod_left_iff]
  intro ν hν
  rw [IsCoprime.prod_right_iff]
  intro μ hμ
  refine isCoprime_of_revWt hq (by rintro rfl; exact Finset.disjoint_left.mp hST hν hμ)
    (fun x hx => (hg ν (Finset.mem_union_left _ hν) x hx).2)
    (hg μ (Finset.mem_union_right _ hμ))


omit [IsAlgClosed L] in
/-- A root of the product of a filtered multiset of polynomials is a root of one of them. -/
private lemma exists_mem_filter_of_aeval_prod_eq_zero (P : ℚ[X] → Prop) [DecidablePred P]
    (F : Multiset ℚ[X]) {x : L} (hx : aeval x (F.filter P).prod = 0) :
    ∃ π ∈ F, P π ∧ aeval x π = 0 := by
  rw [map_multiset_prod, Multiset.prod_eq_zero_iff] at hx
  obtain ⟨π, hπ, hπx⟩ := Multiset.mem_map.mp hx
  exact ⟨π, (Multiset.mem_filter.mp hπ).1, (Multiset.mem_filter.mp hπ).2, hπx⟩

private lemma exists_rat_of_associated {q : ℕ} (hq : 1 < q) (g : ℕ → L[X]) {S : Finset ℕ}
    (hg0 : ∀ ν ∈ S, (g ν).coeff 0 = 1)
    (hg : ∀ ν ∈ S, ∀ x, eval x (g ν) = 0 → IsIntegral ℚ x ∧ RevWt q x ν)
    (A : ℚ[X]) (hA : A ≠ 0) (h1 : A.map (algebraMap ℚ L) ∣ ∏ ν ∈ S, g ν)
    (h2 : ∏ ν ∈ S, g ν ∣ A.map (algebraMap ℚ L)) :
    ∀ ν ∈ S, ∃ r : ℚ[X], r.coeff 0 = 1 ∧ r.map (algebraMap ℚ L) = g ν ∧ r ∣ A := by
  classical
  intro ν hν
  set F := UniqueFactorizationMonoid.normalizedFactors A with hF
  let Q : ℚ[X] → Prop := fun π => ∀ y : L, aeval y π = 0 → RevWt q y ν
  set r0 := (F.filter Q).prod with hr0
  set s0 := (F.filter (fun π => ¬ Q π)).prod with hs0
  have hassoc : Associated (r0 * s0) A := by
    rw [hr0, hs0, Multiset.prod_filter_mul_prod_filter_not]
    exact UniqueFactorizationMonoid.prod_normalizedFactors hA
  have hr0A : r0 ∣ A := (Dvd.intro _ rfl).trans hassoc.dvd
  -- (a) `r0` divides `g ν`
  have ha : r0.map (algebraMap ℚ L) ∣ g ν := by
    have hdvd : r0.map (algebraMap ℚ L) ∣ g ν * ∏ μ ∈ S.erase ν, g μ := by
      rw [Finset.mul_prod_erase S g hν]
      exact (Polynomial.map_dvd _ hr0A).trans h1
    refine IsCoprime.dvd_of_dvd_mul_right ?_ hdvd
    rw [IsCoprime.prod_right_iff]
    intro μ hμ
    refine isCoprime_of_revWt hq (Finset.ne_of_mem_erase hμ).symm ?_
      (hg μ (Finset.mem_of_mem_erase hμ))
    intro x hx
    rw [eval_map_algebraMap] at hx
    obtain ⟨π, -, hπQ, hπx⟩ := exists_mem_filter_of_aeval_prod_eq_zero Q F hx
    exact hπQ x hπx
  -- (b) `g ν` divides `r0`
  have hb : g ν ∣ r0.map (algebraMap ℚ L) := by
    have hdvd : g ν ∣ r0.map (algebraMap ℚ L) * s0.map (algebraMap ℚ L) := by
      rw [← Polynomial.map_mul]
      exact (Finset.dvd_prod_of_mem g hν).trans (h2.trans (Polynomial.map_dvd _ hassoc.symm.dvd))
    refine IsCoprime.dvd_of_dvd_mul_right ?_ hdvd
    rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed L L]
    intro x
    by_contra hc
    push Not at hc
    simp only [coe_aeval_eq_eval, eval_map_algebraMap] at hc
    obtain ⟨hxi, hxw⟩ := hg ν hν x hc.1
    obtain ⟨π, hπF, hπQ, hπx⟩ := exists_mem_filter_of_aeval_prod_eq_zero _ F hc.2
    apply hπQ
    intro y hy
    have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor π hπF
    have hm : minpoly ℚ y = minpoly ℚ x := by
      rw [← minpoly.eq_of_irreducible hirr hy, ← minpoly.eq_of_irreducible hirr hπx]
    intro z hz
    rw [hm] at hz
    exact hxw z hz
  -- normalise the constant term
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd ha hb
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hcoeff : algebraMap ℚ L (r0.coeff 0) * c = 1 := by
    have := congrArg (fun p => p.coeff 0) hu
    simp only [← hc, coeff_mul_C, coeff_map] at this
    rw [this, hg0 ν hν]
  have hr00 : r0.coeff 0 ≠ 0 := by
    rintro h0
    simp [h0] at hcoeff
  refine ⟨C (r0.coeff 0)⁻¹ * r0, ?_, ?_, ?_⟩
  · rw [coeff_C_mul, inv_mul_cancel₀ hr00]
  · rw [← hu, ← hc, Polynomial.map_mul, map_C, mul_comm, map_inv₀]
    congr 2
    exact (eq_inv_of_mul_eq_one_right hcoeff).symm
  · exact (C_mul_dvd (inv_ne_zero hr00)).mpr hr0A


omit [IsAlgClosed L] in
private lemma map_map_rat {K : Type*} [Field K] [CharZero K] [Algebra K L] (p : ℚ[X]) :
    (p.map (algebraMap ℚ K)).map (algebraMap K L) = p.map (algebraMap ℚ L) := by
  rw [Polynomial.map_map]
  congr 1
  exact Subsingleton.elim _ _

/-- **Weight separation.** Let `χ ν` (`ν ≤ 2n`) be monic polynomials over a field `K` of
characteristic zero all of whose roots `μ` are algebraic over `ℚ` with `|ι μ| = q ^ (ν / 2)` for
every embedding `ι : ℚ(μ) → ℂ`. If `A, B ∈ ℚ[X]` are coprime with constant term `1` and
`A · ∏_{ν even} (χ ν).reverse = B · ∏_{ν odd} (χ ν).reverse`, then every `(χ ν).reverse` has
rational coefficients: it is the image of some `r ∈ ℚ[X]` with constant term `1`, dividing `B`
for `ν` even and `A` for `ν` odd. -/
theorem exists_rat_reverse_charpoly_of_weight {K : Type*} [Field K] [CharZero K]
    (q : ℕ) (hq : 1 < q) (n : ℕ) (χ : ℕ → K[X]) (hχ : ∀ ν, (χ ν).Monic)
    (hW : ∀ ν ∈ Finset.range (2 * n + 1), ∀ μ : AlgebraicClosure K, aeval μ (χ ν) = 0 →
      IsAlgebraic ℚ μ ∧ ∀ ι : IntermediateField.adjoin ℚ {μ} →+* ℂ,
        ‖ι (IntermediateField.AdjoinSimple.gen ℚ μ)‖ = (q : ℝ) ^ ((ν : ℝ) / 2))
    (A B : ℚ[X]) (hA : A.coeff 0 = 1) (hB : B.coeff 0 = 1) (hAB : IsCoprime A B)
    (h : A.map (algebraMap ℚ K) * ∏ ν ∈ (Finset.range (2 * n + 1)).filter Even, (χ ν).reverse =
      B.map (algebraMap ℚ K) * ∏ ν ∈ (Finset.range (2 * n + 1)).filter (¬ Even ·), (χ ν).reverse) :
    ∀ ν ∈ Finset.range (2 * n + 1), ∃ r : ℚ[X], r.coeff 0 = 1 ∧
      r.map (algebraMap ℚ K) = (χ ν).reverse ∧ (if Even ν then r ∣ B else r ∣ A) := by
  classical
  let E := AlgebraicClosure K
  let g : ℕ → E[X] := fun ν => (χ ν).reverse.map (algebraMap K E)
  set U := Finset.range (2 * n + 1) with hU
  have hg0 : ∀ ν, (g ν).coeff 0 = 1 := by
    intro ν
    simp [g, coeff_map, coeff_zero_reverse, (hχ ν).leadingCoeff]
  have hg : ∀ ν ∈ U, ∀ x, eval x (g ν) = 0 → IsIntegral ℚ x ∧ RevWt q x ν := by
    intro ν hν x hx
    rw [eval_map_algebraMap] at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [aeval_def, eval₂_at_zero, coeff_zero_reverse, (hχ ν).leadingCoeff, map_one] at hx
      exact one_ne_zero hx
    let _ : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
    have h' := eval₂_reverse_eq_zero_iff (algebraMap K E) x⁻¹ (χ ν)
    rw [invOf_eq_inv, inv_inv] at h'
    have hroot : aeval x⁻¹ (χ ν) = 0 := by
      rw [aeval_def]; exact h'.mp (by rwa [aeval_def] at hx)
    obtain ⟨halg, hι⟩ := hW ν hν x⁻¹ hroot
    have hw := revWt_inv halg hι
    rw [inv_inv] at hw
    refine ⟨?_, hw⟩
    simpa using halg.inv.isIntegral
  have hE : A.map (algebraMap ℚ E) * ∏ ν ∈ U.filter Even, g ν =
      B.map (algebraMap ℚ E) * ∏ ν ∈ U.filter (¬ Even ·), g ν := by
    have := congrArg (Polynomial.map (algebraMap K E)) h
    simpa only [Polynomial.map_mul, Polynomial.map_prod, map_map_rat, g] using this
  have hcop : IsCoprime (∏ ν ∈ U.filter (¬ Even ·), g ν) (∏ ν ∈ U.filter Even, g ν) :=
    isCoprime_prod_of_revWt hq g (Finset.disjoint_filter_filter_not U U Even).symm
      (fun ν hν => hg ν (by simp only [Finset.mem_union, Finset.mem_filter] at hν; tauto))
  have hAB' : IsCoprime (A.map (algebraMap ℚ E)) (B.map (algebraMap ℚ E)) := by
    simpa only [coe_mapRingHom] using hAB.map (mapRingHom (algebraMap ℚ E))
  have hA0 : A ≠ 0 := by rintro rfl; simp at hA
  have hB0 : B ≠ 0 := by rintro rfl; simp at hB
  intro ν hν
  have hfin : ∀ r : ℚ[X], r.map (algebraMap ℚ E) = g ν → r.map (algebraMap ℚ K) = (χ ν).reverse :=
    fun r hr => Polynomial.map_injective (algebraMap K E) (algebraMap K E).injective
      (by rw [map_map_rat]; exact hr)
  by_cases hev : Even ν
  · obtain ⟨r, hr0, hr, hrB⟩ := exists_rat_of_associated hq g (fun ν _ => hg0 ν)
      (fun ν hν => hg ν (Finset.mem_of_mem_filter ν hν)) B hB0
      (hAB'.symm.dvd_of_dvd_mul_left ⟨_, hE⟩)
      (hcop.symm.dvd_of_dvd_mul_right ⟨_, by rw [← hE, mul_comm]⟩) ν
      (Finset.mem_filter.mpr ⟨hν, hev⟩)
    exact ⟨r, hr0, hfin r hr, by simpa [hev] using hrB⟩
  · obtain ⟨r, hr0, hr, hrA⟩ := exists_rat_of_associated hq g (fun ν _ => hg0 ν)
      (fun ν hν => hg ν (Finset.mem_of_mem_filter ν hν)) A hA0
      (hAB'.dvd_of_dvd_mul_left ⟨_, hE.symm⟩)
      (hcop.dvd_of_dvd_mul_right ⟨_, by rw [hE, mul_comm]⟩) ν (Finset.mem_filter.mpr ⟨hν, hev⟩)
    exact ⟨r, hr0, hfin r hr, by simpa [hev] using hrA⟩

end Weil
