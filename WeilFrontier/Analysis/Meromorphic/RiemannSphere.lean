module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Meromorphic functions on the Riemann sphere are rational

A function `f : ℂ → ℂ` that is meromorphic on `ℂ` and such that `w ↦ f (1 / w)` is meromorphic
at `0` (that is, `f` is meromorphic on the Riemann sphere `ℂ ∪ {∞}`) agrees, away from a discrete
subset of `ℂ`, with a quotient `p / q` of complex polynomials.

The proof: if `f` vanishes identically near some point, it vanishes codiscretely and `p = 0`.
Otherwise `f` is analytic and nonzero on a neighbourhood `‖z‖ > R` of `∞`, so its divisor is
supported in the closed ball of radius `R` and hence finite. Dividing out the zeros and poles
(`MeromorphicOn.extract_zeros_poles`) writes `f = (p₀ / q) · g` with `g` entire and nowhere zero
and `w ↦ g (1 / w)` meromorphic at `0`. One of `g`, `1 / g` then has a limit at `∞`, so it is
constant by Liouville's theorem, and so is `g`.

## Main results

* `Complex.eq_const_of_differentiable_of_meromorphicOrderAt_inv_nonneg`: an entire function `k`
  such that `w ↦ k (1 / w)` is meromorphic of nonnegative order at `0` is constant.
* `Complex.exists_polynomial_div_eq_of_meromorphicOn_univ`: a meromorphic function on the Riemann
  sphere is codiscretely equal to a rational function.
-/

@[expose] public section

open Filter Topology Polynomial

namespace Complex

/-- `Inv.inv` maps a neighbourhood of `∞` to a punctured neighbourhood of `0`. -/
theorem tendsto_inv_cobounded_nhdsNE_zero :
    Tendsto (Inv.inv : ℂ → ℂ) (Bornology.cobounded ℂ) (𝓝[≠] 0) :=
  inv_cobounded₀.le

/-- Liouville at `∞`: an entire function `k` such that `w ↦ k (1 / w)` is meromorphic at `0` of
nonnegative order is constant. -/
theorem eq_const_of_differentiable_of_meromorphicOrderAt_inv_nonneg {k : ℂ → ℂ}
    (hk : Differentiable ℂ k) (hm : MeromorphicAt (fun w => k w⁻¹) 0)
    (h0 : 0 ≤ meromorphicOrderAt (fun w => k w⁻¹) 0) : ∃ c, ∀ z, k z = c := by
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hm h0
  have hk' : Tendsto k (cocompact ℂ) (𝓝 c) := by
    rw [← Metric.cobounded_eq_cocompact]
    have := hc.comp tendsto_inv_cobounded_nhdsNE_zero
    simpa [Function.comp_def] using this
  exact ⟨c, fun z => hk.apply_eq_of_tendsto_cocompact z hk'⟩

/-- An entire nowhere vanishing function `g` such that `w ↦ g (1 / w)` is meromorphic at `0` is
constant. -/
theorem eq_const_of_differentiable_of_meromorphicAt_inv_of_ne_zero {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hg0 : ∀ z, g z ≠ 0) (hm : MeromorphicAt (fun w => g w⁻¹) 0) :
    ∃ c, ∀ z, g z = c := by
  by_cases h : 0 ≤ meromorphicOrderAt (fun w => g w⁻¹) 0
  · exact eq_const_of_differentiable_of_meromorphicOrderAt_inv_nonneg hg hm h
  · have hinv : 0 ≤ meromorphicOrderAt (fun w => (g w⁻¹)⁻¹) 0 := by
      have : (fun w => (g w⁻¹)⁻¹) = (fun w => g w⁻¹)⁻¹ := rfl
      rw [this, meromorphicOrderAt_inv]
      generalize meromorphicOrderAt (fun w => g w⁻¹) 0 = o at h ⊢
      induction o with
      | top => exact absurd le_top h
      | coe n =>
        have hn : n < 0 := by exact_mod_cast not_le.1 h
        rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
        exact_mod_cast (neg_pos.2 hn).le
    obtain ⟨c, hc⟩ := eq_const_of_differentiable_of_meromorphicOrderAt_inv_nonneg
      (k := fun z => (g z)⁻¹) (hg.inv hg0) hm.inv hinv
    exact ⟨c⁻¹, fun z => by rw [← hc z, inv_inv]⟩

/-- `x ^ k = x ^ k₊ / x ^ k₋` in `ℂ`, also when `x = 0`. -/
private theorem zpow_eq_pow_toNat_div_pow_toNat (x : ℂ) (k : ℤ) :
    x ^ k = x ^ k.toNat / x ^ (-k).toNat := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k <;> simp

/-- `w ↦ p (1 / w)` is meromorphic everywhere, for a polynomial `p`. -/
theorem meromorphicAt_eval_inv (p : ℂ[X]) (x : ℂ) : MeromorphicAt (fun w => p.eval w⁻¹) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact hp.add hq
  | monomial n a =>
    simp only [eval_monomial]
    fun_prop

/-- **Meromorphic functions on the Riemann sphere are rational.** If `f : ℂ → ℂ` is meromorphic
on `ℂ` and `w ↦ f (1 / w)` is meromorphic at `0`, then `f` agrees with a quotient of polynomials
`p / q`, `q ≠ 0`, outside a discrete subset of `ℂ`. -/
theorem exists_polynomial_div_eq_of_meromorphicOn_univ {f : ℂ → ℂ}
    (hf : MeromorphicOn f Set.univ) (hinf : MeromorphicAt (fun w => f w⁻¹) 0) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ f =ᶠ[codiscrete ℂ] fun z => p.eval z / q.eval z := by
  by_cases htop : ∃ u : (Set.univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤
  swap
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    push Not at htop
    change _ ∈ codiscreteWithin Set.univ
    rw [mem_codiscreteWithin]
    intro x _
    rw [disjoint_principal_right]
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 (htop ⟨x, Set.mem_univ x⟩)] with y hy
    simp [hy]
  have hall := (hf.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1 htop
  -- `f` does not vanish identically near `∞`
  have hhtop : meromorphicOrderAt (fun w => f w⁻¹) 0 ≠ ⊤ := by
    intro H
    have hev : ∀ᶠ z in Bornology.cobounded ℂ, f z = 0 := by
      have := tendsto_inv_cobounded_nhdsNE_zero.eventually (meromorphicOrderAt_eq_top_iff.1 H)
      simpa using this
    obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 hev
    have hz : ((|R| + 1 : ℝ) : ℂ) ∈ (Metric.closedBall (0 : ℂ) R)ᶜ := by
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, not_le]
      rw [abs_of_pos (by positivity)]
      linarith [le_abs_self R]
    apply hall ⟨_, Set.mem_univ ((|R| + 1 : ℝ) : ℂ)⟩
    rw [meromorphicOrderAt_eq_top_iff]
    exact nhdsWithin_le_nhds (Filter.mem_of_superset
      (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hz) fun y hy => hR hy)
  -- `f` is analytic and nonzero near `∞`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z : ℂ, R < ‖z‖ → AnalyticAt ℂ f z ∧ f z ≠ 0 := by
    have h1 := tendsto_inv_cobounded_nhdsNE_zero.eventually hinf.eventually_analyticAt
    have h2 := tendsto_inv_cobounded_nhdsNE_zero.eventually
      ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero hinf).1 hhtop)
    have h3 := tendsto_inv_cobounded_nhdsNE_zero.eventually (self_mem_nhdsWithin (a := (0 : ℂ)))
    obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1
      (h1.and (h2.and h3))
    refine ⟨R, fun z hz => ?_⟩
    obtain ⟨ha, hne, hz0⟩ := hR (show z ∈ (Metric.closedBall (0 : ℂ) R)ᶜ by simpa using hz)
    have hz0' : z ≠ 0 := by simpa using hz0
    have key : AnalyticAt ℂ ((fun w => f w⁻¹) ∘ Inv.inv) z := ha.comp (analyticAt_inv hz0')
    exact ⟨by simpa [Function.comp_def] using key, by simpa using hne⟩
  set D := MeromorphicOn.divisor f Set.univ with hD
  have hsupp : D.support ⊆ Metric.closedBall 0 R := by
    intro z hz
    by_contra hz'
    have hz'' : R < ‖z‖ := by simpa using hz'
    obtain ⟨ha, hne⟩ := hR z hz''
    apply hz
    rw [hD, MeromorphicOn.divisor_apply hf (Set.mem_univ z), ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_zero.2 hne]
    simp
  have hfin : D.support.Finite :=
    ((isCompact_closedBall 0 R).of_isClosed_subset (D.closedSupport isClosed_univ) hsupp).finite
      D.discreteSupport
  obtain ⟨g, hga, hg0, hfg⟩ := hf.extract_zeros_poles hall hfin
  set s := hfin.toFinset with hs
  set p₀ : ℂ[X] := ∏ u ∈ s, (X - C u) ^ (D u).toNat with hp₀
  set q : ℂ[X] := ∏ u ∈ s, (X - C u) ^ (-D u).toNat with hq_def
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun u _ => pow_ne_zero _ (X_sub_C_ne_zero u)
  have hr : ∀ z, (∏ᶠ u, (fun x => x - u) ^ D u) z = p₀.eval z / q.eval z := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
    · simp only [Finset.prod_apply, Pi.pow_apply, hp₀, hq_def, eval_prod, eval_pow, eval_sub,
        eval_X, eval_C]
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun u _ => zpow_eq_pow_toNat_div_pow_toNat _ _
    · intro u hu
      rw [hs, Set.Finite.coe_toFinset]
      by_contra h'
      apply hu
      simp [Function.notMem_support.1 h']
  have hfg' : f =ᶠ[codiscrete ℂ] fun z => p₀.eval z / q.eval z * g z := by
    filter_upwards [hfg] with z hz
    rw [hz, Pi.smul_apply', ← hD, hr, smul_eq_mul]
  have hg : Differentiable ℂ g := fun z => (hga z (Set.mem_univ z)).differentiableAt
  have hpq : ∀ z : ℂ, R < ‖z‖ → p₀.eval z ≠ 0 ∧ q.eval z ≠ 0 := by
    intro z hz
    have hu : ∀ u ∈ s, z - u ≠ 0 := by
      intro u hu h0
      have : ‖u‖ ≤ R := by simpa using hsupp (hfin.mem_toFinset.1 hu)
      rw [sub_eq_zero] at h0
      subst h0
      linarith
    simp only [hp₀, hq_def, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
    exact ⟨Finset.prod_ne_zero_iff.2 fun u hu' => pow_ne_zero _ (hu u hu'),
      Finset.prod_ne_zero_iff.2 fun u hu' => pow_ne_zero _ (hu u hu')⟩
  have hfeq : ∀ z : ℂ, R < ‖z‖ → f z = p₀.eval z / q.eval z * g z := by
    intro z hz
    have hc1 : ContinuousAt f z := (hR z hz).1.continuousAt
    have hc2 : ContinuousAt (fun z => p₀.eval z / q.eval z * g z) z :=
      ((p₀.continuous.continuousAt).div q.continuous.continuousAt (hpq z hz).2).mul
        (hg z).continuousAt
    have hev : f =ᶠ[𝓝[≠] z] fun z => p₀.eval z / q.eval z * g z := by
      have := (mem_codiscreteWithin.1 (show _ ∈ codiscreteWithin Set.univ from hfg')) z
        (Set.mem_univ z)
      rw [disjoint_principal_right] at this
      filter_upwards [this] with y hy
      simpa using hy
    exact ((hc1.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hc2).1 hev).eq_of_nhds
  have hgm : MeromorphicAt (fun w => g w⁻¹) 0 := by
    have hm : MeromorphicAt (fun w => f w⁻¹ * q.eval w⁻¹ / p₀.eval w⁻¹) 0 :=
      (hinf.mul (meromorphicAt_eval_inv q 0)).div (meromorphicAt_eval_inv p₀ 0)
    refine hm.congr ?_
    rw [← inv_cobounded₀]
    change ∀ᶠ w in Filter.map Inv.inv (Bornology.cobounded ℂ), _
    rw [eventually_map]
    refine (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.2
      ⟨R, trivial, fun z hz => ?_⟩
    have hz' : R < ‖z‖ := by simpa using hz
    obtain ⟨hp0, hq0⟩ := hpq z hz'
    simp only [inv_inv, hfeq z hz']
    field_simp
  obtain ⟨c, hc⟩ := eq_const_of_differentiable_of_meromorphicAt_inv_of_ne_zero hg
    (fun z => hg0 ⟨z, Set.mem_univ z⟩) hgm
  refine ⟨C c * p₀, q, hq, ?_⟩
  filter_upwards [hfg'] with z hz
  rw [hz, hc z, eval_mul, eval_C]
  ring

end Complex
