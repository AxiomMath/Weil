module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Compact perturbations of surjective operators

Let `Φ, Ψ : E → F` be continuous linear maps between Banach spaces over `ℝ` or `ℂ`, with `Φ`
surjective and `Ψ` compact. Then the range of `Φ - Ψ` has finite codimension: there is a
finite-dimensional subspace `F₀ ⊆ F` with `range (Φ - Ψ) + F₀ = F`. This is Schwartz's lemma,
the analytic input of the Cartan–Serre proof that the first cohomology of a coherent sheaf on a
compact complex manifold is finite-dimensional.

The proof: by the open mapping theorem every `y` has a preimage `x` under `Φ` with
`‖x‖ ≤ C ‖y‖`. The image under `Ψ` of the closed ball of radius `C` is relatively compact, so it
has a finite `1/2`-net `t` contained in it; let `F₀` be the span of `t`. Writing
`y = (Φ - Ψ) x + f + (Ψ x - f)` with `f` a rescaled point of the net, the map
`E × F₀ → F, (x, f) ↦ (Φ - Ψ) x + f` approximates every `y` up to `‖y‖ / 2` by a preimage of norm
`O(‖y‖)`. Such a map is surjective, by the geometric series argument of the open mapping theorem
(`ContinuousLinearMap.surjective_of_exists_approx_preimage_norm_le`).

## Main results

* `ContinuousLinearMap.surjective_of_exists_approx_preimage_norm_le`: a continuous linear map
  from a Banach space all of whose values are approximated up to half their norm by images of
  vectors of controlled norm is surjective.
* `ContinuousLinearMap.exists_finiteDimensional_range_sub_sup_eq_top`: Schwartz's lemma.

## Implementation notes

The usual statement takes Hilbert or Fréchet spaces; the Banach form suffices for spaces of
bounded holomorphic functions with the sup norm, and its proof needs no inner product.

## References

* [O. Forster, *Lectures on Riemann Surfaces*, §14][forster1981]
* [L. Schwartz, *Homomorphismes et applications complètement continues*][schwartz1953]
-/

public section

open Metric Filter Topology Function

namespace ContinuousLinearMap

section Approx

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear map `f` from a Banach space is surjective as soon as every `y` is
approximated up to `‖y‖ / 2` by some `f x` with `‖x‖ ≤ C ‖y‖`. -/
theorem surjective_of_exists_approx_preimage_norm_le [CompleteSpace E] (f : E →L[𝕜] F)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    Surjective f := by
  intro y
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [Finset.sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f (∑' n, u n))) :=
    (f.continuous.tendsto _).comp su.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;>
      norm_num
  exact ⟨_, (tendsto_nhds_unique L₁ L₂).trans (sub_zero y)⟩

end Approx

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Schwartz's lemma**, Banach form: a compact perturbation `Φ - Ψ` of a surjective continuous
linear map `Φ` between Banach spaces has range of finite codimension. -/
theorem exists_finiteDimensional_range_sub_sup_eq_top [CompleteSpace E] [CompleteSpace F]
    (Φ Ψ : E →L[𝕜] F) (hΦ : Surjective Φ) (hΨ : IsCompactOperator Ψ) :
    ∃ F₀ : Submodule 𝕜 F, FiniteDimensional 𝕜 F₀ ∧
      LinearMap.range ((Φ - Ψ : E →L[𝕜] F) : E →ₗ[𝕜] F) ⊔ F₀ = ⊤ := by
  obtain ⟨C, hC0, hC⟩ := Φ.exists_preimage_norm_le hΦ
  obtain ⟨K, hK, hKsub⟩ := hΨ.image_closedBall_subset_compact C
  obtain ⟨t, hts, htfin, hcov⟩ :=
    finite_approx_of_totallyBounded (hK.totallyBounded.subset hKsub) (1 / 2) (by norm_num)
  let F₀ : Submodule 𝕜 F := Submodule.span 𝕜 t
  have : FiniteDimensional 𝕜 F₀ := FiniteDimensional.span_of_finite 𝕜 htfin
  have : CompleteSpace F₀ := FiniteDimensional.complete 𝕜 F₀
  refine ⟨F₀, inferInstance, ?_⟩
  let T : (E × F₀) →L[𝕜] F := (Φ - Ψ).coprod F₀.subtypeL
  have hTapply : ∀ p : E × F₀, T p = (Φ - Ψ) p.1 + p.2 := fun p => rfl
  have hT : Surjective T := by
    refine T.surjective_of_exists_approx_preimage_norm_le (C := C + ‖Ψ‖ * C) (by positivity)
      fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, by simp⟩
    obtain ⟨x, hx, hxn⟩ := hC y
    set s : ℝ := ‖y‖ with hs_def
    have hs : 0 < s := norm_pos_iff.2 hy
    let x' : E := ((s⁻¹ : ℝ) : 𝕜) • x
    have hxx' : x = ((s : ℝ) : 𝕜) • x' := by
      simp only [x', smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hs.ne', RCLike.ofReal_one,
        one_smul]
    have hx' : x' ∈ closedBall (0 : E) C := by
      rw [mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal, abs_inv, abs_of_pos hs]
      rw [inv_mul_le_iff₀ hs, mul_comm]
      exact hxn
    obtain ⟨f, hft, hf⟩ : ∃ f ∈ t, dist (Ψ x') f < 1 / 2 := by
      simpa using hcov ⟨x', hx', rfl⟩
    obtain ⟨z, hz, rfl⟩ := hts hft
    have hzn : ‖z‖ ≤ C := mem_closedBall_zero_iff.1 hz
    refine ⟨(x, ⟨((s : ℝ) : 𝕜) • Ψ z, F₀.smul_mem _ (Submodule.subset_span hft)⟩), ?_, ?_⟩
    · rw [hTapply, dist_eq_norm]
      have : (Φ - Ψ) x + ((s : ℝ) : 𝕜) • Ψ z - y = -(((s : ℝ) : 𝕜) • (Ψ x' - Ψ z)) := by
        rw [sub_apply, hx, hxx', map_smul, smul_sub]
        abel
      rw [this, norm_neg, norm_smul, RCLike.norm_ofReal, abs_of_pos hs, ← dist_eq_norm]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hf.le hs.le
    · rw [Prod.norm_def, max_le_iff]
      constructor
      · calc ‖x‖ ≤ C * s := hxn
          _ ≤ (C + ‖Ψ‖ * C) * s := by gcongr; nlinarith [norm_nonneg Ψ]
      · change ‖((s : ℝ) : 𝕜) • Ψ z‖ ≤ _
        rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hs]
        calc s * ‖Ψ z‖ ≤ s * (‖Ψ‖ * C) := by
              gcongr; exact (Ψ.le_opNorm z).trans (by gcongr)
          _ ≤ (C + ‖Ψ‖ * C) * s := by nlinarith
  rw [eq_top_iff]
  rintro y -
  obtain ⟨p, rfl⟩ := hT y
  rw [hTapply]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) p.2.2

end ContinuousLinearMap
