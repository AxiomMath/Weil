module

public import Mathlib.Analysis.Convolution
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The inhomogeneous Cauchy–Riemann equation in one variable

For `u : ℂ → E` the Wirtinger derivative `∂u/∂z̄` is
`∂u/∂z̄ (z) = (1/2) (∂u/∂x + i ∂u/∂y) = (1/2) (Du(z) 1 + i Du(z) i)`, where `Du(z)` is the real
Fréchet derivative. A function is holomorphic exactly where it is real differentiable with
`∂u/∂z̄ = 0`.

The Cauchy transform of a compactly supported function `g : ℂ → ℂ` is
`u(z) = (1/π) ∫ g(w) / (z - w) dλ(w)`, `λ` being Lebesgue measure on `ℂ ≃ ℝ²`. It is the
convolution of `g` with the locally integrable kernel `w ↦ 1 / (π w)`, a fundamental solution of
`∂/∂z̄`. We prove the Dolbeault lemma in one variable: if `g` is `C^n`, `1 ≤ n`, with compact
support, then `u` is `C^n` and `∂u/∂z̄ = g`. Differentiating under the integral,
`∂u/∂z̄ (z) = (1/π) ∫ (∂g/∂z̄)(z - w) / w dλ(w)`, and the right side equals `g(z)` by the
identity `∫ (∂h/∂z̄)(w) / w dλ(w) = -π h(0)` for compactly supported `C¹` functions `h`.
In polar coordinates `w = r e^{iθ}` this integrand, times the Jacobian `r`, is
`(1/2) (∂_r H + (i/r) ∂_θ H)` with `H(r, θ) = h(r e^{iθ})`; the radial term integrates to
`-h(0)` on each ray and the angular one to `0` on each circle.

Multiplying by a bump function gives the local statement: a `C^n` function on a disc `B(z₀, r)`
is `∂/∂z̄` of a `C^n` function on every smaller concentric disc.

## Main definitions

* `Complex.dbar`: the Wirtinger derivative `∂u/∂z̄`.
* `Complex.cauchyTransform`: the Cauchy transform `(1/π) ∫ g(w) / (z - w) dλ(w)`.

## Main results

* `Complex.integral_inv_mul_dbar`: `∫ (∂h/∂z̄)(w) / w dλ(w) = -π h(0)` for `h ∈ C¹_c(ℂ)`.
* `Complex.contDiff_cauchyTransform`: the Cauchy transform of a compactly supported `C^n`
  function is `C^n`.
* `Complex.dbar_cauchyTransform`: `∂/∂z̄` of the Cauchy transform of `g ∈ C¹_c(ℂ)` is `g`.
* `Complex.exists_contDiff_dbar_eq_on_ball`, `Complex.exists_contDiff_dbar_eq_on_half_ball`:
  local solvability of `∂u/∂z̄ = g` on discs.

## Implementation notes

The smoothness classes are indexed by `n : ℕ∞`, so `n = ⊤` is `C^∞`; real analyticity is not
claimed. The Cauchy transform is defined for every `g`; its integral is the Bochner integral,
which is `0` when the integrand is not integrable.

## References

* [L. Hörmander, *An introduction to complex analysis in several variables*][hormander1966],
  Theorem 1.2.2.
-/

open MeasureTheory Set Filter Topology
open scoped Convolution

@[expose] public noncomputable section

namespace Complex

/-- The Wirtinger derivative `∂/∂z̄` of `u : ℂ → E` at `z`. -/
def dbar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : ℂ → E) (z : ℂ) : E :=
  (1 / 2 : ℂ) • (fderiv ℝ u z 1 + I • fderiv ℝ u z I)

/-- A complex differentiable function has vanishing Wirtinger derivative `∂/∂z̄`. -/
theorem dbar_eq_zero_of_differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : ℂ → E} {z : ℂ} (hu : DifferentiableAt ℂ u z) : dbar u z = 0 := by
  rw [dbar, (hu.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  have hI : fderiv ℂ u z I = I • fderiv ℂ u z 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hI, smul_smul, I_mul_I, neg_one_smul, add_neg_cancel, smul_zero]

/-- Every real-linear map `ℂ → ℂ` is determined by its values at `1` and `I`. -/
private theorem clm_apply_eq_re_im (L : ℂ →L[ℝ] ℂ) (v : ℂ) : L v = v.re * L 1 + v.im * L I := by
  conv_lhs => rw [← re_add_im v]
  rw [map_add, show (v.im : ℂ) * I = (v.im : ℝ) • I by simp,
    show (v.re : ℂ) = (v.re : ℝ) • (1 : ℂ) by simp, map_smul, map_smul]
  simp [real_smul]

/-- The point of angle `θ` on the unit circle. -/
local notation "e" θ => ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)

private theorem polar_integrand_eq (h : ℂ → ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r • ((r * e θ)⁻¹ * dbar h (r * e θ)) =
      (1 / 2 : ℂ) * (fderiv ℝ h (r * e θ) (e θ) + I * fderiv ℝ h (r * e θ) (I * e θ)) := by
  have he : (e θ) * ((Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I) = 1 := by
    have := Real.cos_sq_add_sin_sq θ
    linear_combination (norm := ring_nf) (congrArg ((↑) : ℝ → ℂ) this)
    simp only [I_sq]; push_cast; ring
  have hinv : (e θ)⁻¹ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
    exact inv_eq_of_mul_eq_one_right he
  simp only [dbar, smul_eq_mul, real_smul, mul_inv, hinv]
  generalize fderiv ℝ h (r * e θ) = L
  rw [clm_apply_eq_re_im L (e θ), clm_apply_eq_re_im L (I * e θ)]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  field_simp
  push_cast
  linear_combination (-(Complex.sin θ) * L I) * I_sq

private theorem norm_ofReal_mul_circle (r θ : ℝ) : ‖(r : ℂ) * e θ‖ = |r| := by
  have := Complex.polarCoord_symm_apply (r, θ)
  rw [← Complex.norm_polarCoord_symm (r, θ), this]

private theorem hasDerivAt_circle (θ : ℝ) : HasDerivAt (fun θ : ℝ => e θ) (I * e θ) θ := by
  have := (Real.hasDerivAt_cos θ).ofReal_comp.add ((Real.hasDerivAt_sin θ).ofReal_comp.mul_const I)
  exact this.congr_deriv (by push_cast; linear_combination (-(Complex.sin θ)) * I_sq)

/-- A continuous function on `ℝ × ℝ` vanishing for large first coordinate is integrable on the
target `(0, ∞) × (-π, π)` of polar coordinates. -/
private theorem integrableOn_polarTarget_of_continuous {F : ℝ × ℝ → ℂ} (hF : Continuous F) {R : ℝ}
    (hR : ∀ p : ℝ × ℝ, R ≤ p.1 → F p = 0) :
    IntegrableOn F (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hK : IntegrableOn F (Icc 0 R ×ˢ Icc (-Real.pi) Real.pi) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine hK.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
  apply hR
  by_contra! hlt
  exact hn ⟨⟨le_of_lt hr, hlt.le⟩, Ioo_subset_Icc_self hθ⟩

/-- The key identity behind the Cauchy–Pompeiu formula: for a compactly supported `C¹`
function `h`, `∫ (∂h/∂z̄)(w) / w dλ(w) = -π h(0)`. -/
theorem integral_inv_mul_dbar {h : ℂ → ℂ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) :
    ∫ w, w⁻¹ * dbar h w = -(Real.pi : ℂ) * h 0 := by
  obtain ⟨R, -, hR⟩ := (hc.fderiv (𝕜 := ℝ)).exists_pos_le_norm
  obtain ⟨R', -, hR'⟩ := hc.exists_pos_le_norm
  have hDc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hd : Differentiable ℝ h := hh.differentiable one_ne_zero
  have hec : Continuous fun θ : ℝ => e θ := by fun_prop
  set A : ℝ × ℝ → ℂ := fun p => fderiv ℝ h (p.1 * e p.2) (e p.2) with hA
  set B : ℝ × ℝ → ℂ := fun p => fderiv ℝ h (p.1 * e p.2) (I * e p.2) with hB
  have hAc : Continuous A :=
    (hDc.comp (by fun_prop)).clm_apply (hec.comp continuous_snd)
  have hBc : Continuous B :=
    (hDc.comp (by fun_prop)).clm_apply (continuous_const.mul (hec.comp continuous_snd))
  have hD0 : ∀ r θ : ℝ, R ≤ |r| → fderiv ℝ h (r * e θ) = 0 := fun r θ hr =>
    hR _ (by rw [norm_ofReal_mul_circle]; exact hr)
  have hA0 : ∀ p : ℝ × ℝ, R ≤ p.1 → A p = 0 := fun p hp => by
    simp only [hA, hD0 p.1 p.2 (hp.trans (le_abs_self _)), zero_apply]
  have hB0 : ∀ p : ℝ × ℝ, R ≤ p.1 → B p = 0 := fun p hp => by
    simp only [hB, hD0 p.1 p.2 (hp.trans (le_abs_self _)), zero_apply]
  have hAi := integrableOn_polarTarget_of_continuous hAc hA0
  have hBi := integrableOn_polarTarget_of_continuous hBc hB0
  rw [← Complex.integral_comp_polarCoord_symm]
  have step : ∫ p in polarCoord.target,
      p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar h (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, (1 / 2 : ℂ) * (A p + I * B p) := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    simp only [Complex.polarCoord_symm_apply]
    exact polar_integrand_eq h (ne_of_gt hp.1) p.2
  have htarget : (polarCoord.target : Set (ℝ × ℝ)) = Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi := rfl
  rw [step, htarget, integral_const_mul, integral_add hAi (hBi.const_mul I), integral_const_mul]
  -- the radial term
  have hAint : ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, A p = -(2 * Real.pi : ℂ) * h 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod A hAi, integral_integral_swap
      (by rw [Measure.prod_restrict]; exact hAi)]
    have inner : ∀ θ : ℝ, ∫ r in Ioi 0, A (r, θ) = -h 0 := by
      intro θ
      have hcs : HasCompactSupport fun r : ℝ => A (r, θ) := by
        refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun r hr => ?_
        simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hr
        simp only [hA, hD0 r θ hr.le, zero_apply]
      have hcr : Continuous fun r : ℝ => A (r, θ) := hAc.comp (by fun_prop)
      rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun r : ℝ => h (r * e θ)) (m := 0)]
      · simp
      · exact (hh.continuous.comp (by fun_prop)).continuousWithinAt
      · intro r _
        have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) * e θ) (1 * e θ) r :=
          (hasDerivAt_id r).ofReal_comp.mul_const _
        have := (hd _).hasFDerivAt.comp_hasDerivAt r h1
        rw [one_mul] at this
        exact this
      · exact (hcr.integrable_of_hasCompactSupport hcs).integrableOn
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop R'] with r hr
        refine (hR' _ ?_).symm
        rw [norm_ofReal_mul_circle]
        exact hr.trans (le_abs_self _)
    simp_rw [inner]
    rw [setIntegral_const, Real.volume_real_Ioo, max_eq_left (by linarith [Real.pi_pos])]
    simp only [real_smul]
    push_cast
    ring
  -- the angular term
  have hBint : ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi, B p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod B hBi]
    refine (setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_).trans
      (integral_zero _ _)
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ : ℝ => (r : ℂ)⁻¹ * h (r * e θ))]
    · simp [Real.cos_neg, Real.sin_neg]
    · intro θ _
      have h1 := ((hasDerivAt_circle θ).const_mul (r : ℂ))
      have h2 := ((hd _).hasFDerivAt.comp_hasDerivAt θ h1).const_mul (r : ℂ)⁻¹
      refine h2.congr_deriv ?_
      simp only [hB]
      rw [show (r : ℂ) * (I * e θ) = r • (I * e θ) by simp [real_smul], map_smul, real_smul]
      field_simp
    · exact (hBc.comp (by fun_prop)).intervalIntegrable _ _
  rw [hAint, hBint]
  ring

/-- The Cauchy transform `(1/π) ∫ g(w) / (z - w) dλ(w)` of `g : ℂ → ℂ`, `λ` being Lebesgue
measure on `ℂ ≃ ℝ²`. -/
def cauchyTransform (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ w, g w / (z - w)

/-- The kernel `w ↦ w⁻¹` is locally integrable on `ℂ`. -/
theorem locallyIntegrable_inv : LocallyIntegrable (fun w : ℂ => w⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (Eventually.of_forall fun w => ?_) measurable_inv.aestronglyMeasurable
  rw [norm_inv, Real.rpow_neg_one, one_mul]

/-- The Cauchy transform is `1/π` times the convolution of `g` with the kernel `w ↦ w⁻¹`. -/
theorem cauchyTransform_eq_convolution (g : ℂ → ℂ) :
    cauchyTransform g = fun z => (Real.pi : ℂ)⁻¹ *
      ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] g) z := by
  ext z
  rw [cauchyTransform, convolution_def, ← integral_sub_left_eq_self _ volume z]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp [div_eq_inv_mul]

/-- `∂/∂z̄` of `t ↦ g(z - t)`. -/
theorem dbar_comp_sub_left {g : ℂ → ℂ} (hg : Differentiable ℝ g) (z w : ℂ) :
    dbar (fun t => g (z - t)) w = -dbar g (z - w) := by
  have h1 := (hasFDerivAt_const (𝕜 := ℝ) z w).fun_sub (hasFDerivAt_id (𝕜 := ℝ) w)
  have := ((hg (z - w)).hasFDerivAt.comp w h1).fderiv
  simp only [dbar, Function.comp_def] at this ⊢
  rw [this]
  simp only [ContinuousLinearMap.comp_apply, zero_sub, smul_eq_mul]
  simp
  ring

/-- The Cauchy transform of a compactly supported `C^n` function is `C^n`. -/
theorem contDiff_cauchyTransform {g : ℂ → ℂ} {n : ℕ∞} (hg : ContDiff ℝ n g)
    (hc : HasCompactSupport g) : ContDiff ℝ n (cauchyTransform g) := by
  rw [cauchyTransform_eq_convolution]
  exact contDiff_const.mul (hc.contDiff_convolution_right _ locallyIntegrable_inv hg)

/-- **The inhomogeneous Cauchy–Riemann equation** (Dolbeault lemma in one variable): if
`g : ℂ → ℂ` is `C¹` with compact support, its Cauchy transform
`u(z) = (1/π) ∫ g(w) / (z - w) dλ(w)` solves `∂u/∂z̄ = g` everywhere. -/
theorem dbar_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (z : ℂ) : dbar (cauchyTransform g) z = g z := by
  set L := ContinuousLinearMap.mul ℝ ℂ
  set k : ℂ → ℂ := fun w => w⁻¹
  have hk : LocallyIntegrable k volume := locallyIntegrable_inv
  have hD : HasFDerivAt (k ⋆[L, volume] g) ((k ⋆[L.precompR ℂ, volume] fderiv ℝ g) z) z :=
    hc.hasFDerivAt_convolution_right L hk hg z
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hDs : HasCompactSupport (fderiv ℝ g) := hc.fderiv (𝕜 := ℝ)
  have hu : HasFDerivAt (cauchyTransform g)
      ((Real.pi : ℂ)⁻¹ • (k ⋆[L.precompR ℂ, volume] fderiv ℝ g) z) z := by
    rw [cauchyTransform_eq_convolution]
    exact hD.const_mul _
  have happ : ∀ v : ℂ, fderiv ℝ (cauchyTransform g) z v =
      (Real.pi : ℂ)⁻¹ * ∫ t, t⁻¹ * fderiv ℝ g (z - t) v := by
    intro v
    rw [hu.fderiv, smul_apply, convolution_precompR_apply L hk hDs hDc,
      convolution_def, smul_eq_mul]
    rfl
  have hint : ∀ v : ℂ, Integrable fun t => t⁻¹ * fderiv ℝ g (z - t) v := fun v =>
    ((hDs.comp_left (g := fun T : ℂ →L[ℝ] ℂ => T v) rfl).convolutionExists_right L hk
      (hDc.clm_apply continuous_const)) z
  -- `∂̄u(z) = (1/π) ∫ (∂̄g)(z - t) / t`
  have h1 : dbar (cauchyTransform g) z = (Real.pi : ℂ)⁻¹ * ∫ t, t⁻¹ * dbar g (z - t) := by
    have hsplit : ∫ t, t⁻¹ * dbar g (z - t) = 1 / 2 * ((∫ t, t⁻¹ * fderiv ℝ g (z - t) 1) +
        I * ∫ t, t⁻¹ * fderiv ℝ g (z - t) I) := by
      rw [← integral_const_mul I, ← integral_add (hint 1) ((hint I).const_mul I),
        ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [dbar, smul_eq_mul]
      ring
    rw [hsplit]
    simp only [dbar, happ, smul_eq_mul]
    ring
  -- `h(t) = g(z - t)` and the key identity
  set h : ℂ → ℂ := fun t => g (z - t)
  have hh : ContDiff ℝ 1 h := hg.comp (contDiff_const.sub contDiff_id)
  have hhc : HasCompactSupport h := hc.comp_homeomorph (Homeomorph.subLeft z)
  have key := integral_inv_mul_dbar hh hhc
  simp only [h, dbar_comp_sub_left (hg.differentiable one_ne_zero), mul_neg, integral_neg,
    sub_zero] at key
  have key' : ∫ t, t⁻¹ * dbar g (z - t) = Real.pi * g z := by linear_combination -key
  rw [h1, key']
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **Local solvability of `∂u/∂z̄ = g`**: if `g` is `C^n` (`1 ≤ n`) on the open disc
`B(z₀, r)` and `r' < r`, there is a `C^n` function `u : ℂ → ℂ` with `∂u/∂z̄ = g` on `B(z₀, r')`. -/
theorem exists_contDiff_dbar_eq_on_ball {g : ℂ → ℂ} {n : ℕ∞} (hn : 1 ≤ n) {z₀ : ℂ}
    {r r' : ℝ} (hr : r' < r) (hg : ContDiffOn ℝ n g (Metric.ball z₀ r)) :
    ∃ u : ℂ → ℂ, ContDiff ℝ n u ∧ ∀ z ∈ Metric.ball z₀ r', dbar u z = g z := by
  by_cases h0 : 0 < r'
  · let χ : ContDiffBump z₀ := ⟨r', (r' + r) / 2, h0, by linarith⟩
    set G : ℂ → ℂ := fun w => (χ w : ℂ) * g w with hG
    have hGc : HasCompactSupport G := by
      refine χ.hasCompactSupport.mono fun w hw hχ => hw ?_
      simp [hG, hχ]
    have hGd : ContDiff ℝ n G := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x ∈ Metric.ball z₀ r
      · exact (ofRealCLM.contDiff.comp χ.contDiff).contDiffAt.mul
          (hg.contDiffAt (Metric.isOpen_ball.mem_nhds hx))
      · have hxs : x ∉ tsupport χ := by
          rw [χ.tsupport_eq]
          exact fun hx' => hx (Metric.closedBall_subset_ball (by simp [χ]; linarith) hx')
        have hev : G =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with w hw
          simp [hG, hw]
        exact contDiffAt_const.congr_of_eventuallyEq hev
    refine ⟨cauchyTransform G, contDiff_cauchyTransform hGd hGc, fun z hz => ?_⟩
    rw [dbar_cauchyTransform (hGd.of_le (by exact_mod_cast hn)) hGc]
    simp [hG, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)]
  · refine ⟨0, contDiff_const, fun z hz => absurd hz ?_⟩
    rw [Metric.ball_eq_empty.mpr (not_lt.mp h0)]
    exact notMem_empty z

/-- `∂u/∂z̄ = g` is solvable on the half disc: for `g` of class `C^n` (`1 ≤ n`) on `B(z₀, r)`
there is a `C^n` function `u` with `∂u/∂z̄ = g` on `B(z₀, r / 2)`. -/
theorem exists_contDiff_dbar_eq_on_half_ball {g : ℂ → ℂ} {n : ℕ∞} (hn : 1 ≤ n) {z₀ : ℂ}
    {r : ℝ} (hg : ContDiffOn ℝ n g (Metric.ball z₀ r)) :
    ∃ u : ℂ → ℂ, ContDiff ℝ n u ∧ ∀ z ∈ Metric.ball z₀ (r / 2), dbar u z = g z := by
  by_cases hr : 0 < r
  · exact exists_contDiff_dbar_eq_on_ball hn (by linarith) hg
  · refine ⟨0, contDiff_const, fun z hz => absurd hz ?_⟩
    rw [Metric.ball_eq_empty.mpr (by linarith)]
    exact notMem_empty z

end Complex

end
