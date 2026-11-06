module

public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Compact regular zero sets are neighbourhood retracts

Let `E` be a real Hilbert space and `K ⊆ E` a compact set which is, near each of its points, the
zero set of a `C²` map `g : E → ℝᵐ` with surjective derivative (a compact `C²` submanifold of `E`,
given by local regular equations). We show that `K` has *positive reach*: there is `ε > 0` such
that every point at distance `< ε` from `K` has a unique nearest point in `K`. The nearest-point
map is then continuous on the `ε`-thickening of `K`, and it is a retraction of that open
neighbourhood onto `K`.

The proof of positive reach is the classical one. If `x ∈ K` is a nearest point of `z`, then `x`
minimizes `u ↦ ‖u - z‖²` on the level set `{g = 0}`, so by the Lagrange multiplier rule
`⟪x - z, v⟫ = μ (g' x v)` for a linear form `μ`, whose norm is `O(‖x - z‖)` because `g' x` has
a right inverse of bounded norm. A second-order Taylor estimate gives `‖g' x (y - x)‖ = O(‖y - x‖²)`
for `y ∈ K` near `x`; hence `|⟪x - z, y - x⟫| ≤ C ‖x - z‖ ‖y - x‖²`. If `y` is a second nearest
point of `z`, then `‖y - x‖² = 2 ⟪z - x, y - x⟫ ≤ 2 C ‖z - x‖ ‖y - x‖²`, forcing `y = x` once
`‖z - x‖ < 1 / (2 C)`. Compactness makes the constants uniform.

## Main results

* `Metric.continuousAt_of_forall_eq_of_infDist_eq` — a nearest-point map to a compact set is
  continuous at every point having a unique nearest point.
* `IsCompact.exists_pos_eq_of_infDist_eq_of_regularZeroSet` — positive reach: points at
  distance `< ε` from `K` have a unique nearest point in `K`.
* `IsCompact.exists_retraction_thickening_of_regularZeroSet` — a continuous retraction of the
  `ε`-thickening of `K` onto `K`.
* `IsCompact.exists_isOpen_retraction_of_regularZeroSet` — `K` is a neighbourhood retract: an
  open `T ⊇ K` and a continuous `r : C(T, K)` restricting to the identity on `K`.

## Implementation notes

The local hypothesis on `K` is stated directly: for every `p ∈ K` there are an open `V ∋ p`, an
integer `m` and `g : E → EuclideanSpace ℝ (Fin m)`, `C²` on `V`, with `fderiv ℝ g x` surjective
for `x ∈ V` and `K ∩ V = {x ∈ V | g x = 0}`. The local estimate
(`abs_inner_le_of_forall_norm_le_of_regularZeroSet`) is proved for any finite-dimensional
codomain.

## References

* [H. Federer, *Curvature measures*][federer1959], §4.
-/

@[expose] public section

open Metric Set Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The local second-order estimate behind positive reach: near a point `p` of a set `K` which is
locally the regular zero set of a `C²` map `g`, if `x ∈ K` is a nearest point of `z` in `K` and
`y ∈ K`, then `|⟪x - z, y - x⟫| ≤ C ‖x - z‖ ‖y - x‖²`. -/
theorem abs_inner_le_of_forall_norm_le_of_regularZeroSet [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K V : Set E} {g : E → F} {p : E} (hV : IsOpen V) (hpV : p ∈ V)
    (hg : ContDiffOn ℝ 2 g V) (hsurj : ∀ x ∈ V, Function.Surjective (fderiv ℝ g x))
    (hKV : K ∩ V = {x ∈ V | g x = 0}) :
    ∃ ρ > 0, ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ∀ z : E, x ∈ ball p ρ → y ∈ ball p ρ →
      (∀ k ∈ K, ‖z - x‖ ≤ ‖z - k‖) → |⟪x - z, y - x⟫| ≤ C * ‖x - z‖ * ‖y - x‖ ^ 2 := by
  have hgp : ContDiffAt ℝ 2 g p := hg.contDiffAt (hV.mem_nhds hpV)
  have hg'p : ContDiffAt ℝ 1 (fderiv ℝ g) p := hgp.fderiv_right (m := 1) (by norm_num)
  obtain ⟨L, t, ht, hL⟩ := hg'p.exists_lipschitzOnWith
  set A₀ := fderiv ℝ g p with hA₀
  obtain ⟨R, hR⟩ := (A₀ : E →ₗ[ℝ] F).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (hsurj p hpV))
  set R₀ : F →L[ℝ] E := LinearMap.toContinuousLinearMap R
  have hR₀ : ∀ u, A₀ (R₀ u) = u := fun u => LinearMap.congr_fun hR u
  have hev : ∀ᶠ x in 𝓝 p, x ∈ V ∧ x ∈ t ∧ ‖fderiv ℝ g x - A₀‖ * ‖R₀‖ ≤ 1 / 2 := by
    refine (hV.eventually_mem hpV).and ((Filter.eventually_mem_set.2 ht).and ?_)
    have : Tendsto (fun x => ‖fderiv ℝ g x - A₀‖ * ‖R₀‖) (𝓝 p) (𝓝 (‖A₀ - A₀‖ * ‖R₀‖)) :=
      ((hg'p.continuousAt.sub continuousAt_const).norm.mul continuousAt_const)
    rw [sub_self, norm_zero, zero_mul] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ρ, hρ, 2 * ‖R₀‖ * L, ?_⟩
  intro x hxK y hyK z hx hy hmin
  obtain ⟨hxV, hxt, hxA⟩ := hball x hx
  obtain ⟨hyV, hyt, -⟩ := hball y hy
  have hzero : ∀ u ∈ V, u ∈ K ↔ g u = 0 := fun u hu => by
    constructor
    · intro huK
      have : u ∈ K ∩ V := ⟨huK, hu⟩
      rw [hKV] at this
      exact this.2
    · intro hgu
      have : u ∈ {x ∈ V | g x = 0} := ⟨hu, hgu⟩
      rw [← hKV] at this
      exact this.1
  have hgx : g x = 0 := (hzero x hxV).1 hxK
  have hgy : g y = 0 := (hzero y hyV).1 hyK
  set A := fderiv ℝ g x with hA
  have hgxa : ContDiffAt ℝ 2 g x := hg.contDiffAt (hV.mem_nhds hxV)
  -- Lagrange multipliers: `x` minimizes `‖· - z‖²` on the level set of `g` through `x`.
  have hextr : IsLocalExtrOn (fun u => ‖u - z‖ ^ 2) {u | g u = g x} x := by
    refine Or.inl ?_
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hxV), self_mem_nhdsWithin] with u huV hu
    have huK : u ∈ K := (hzero u huV).2 (by rw [show g u = g x from hu, hgx])
    have h1 := hmin u huK
    rw [norm_sub_rev z x, norm_sub_rev z u] at h1
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hφ : HasStrictFDerivAt (fun u => ‖u - z‖ ^ 2) (2 • innerSL ℝ (x - z)) x := by
    have := (hasStrictFDerivAt_norm_sq (x - z)).comp x ((hasStrictFDerivAt_id x).sub_const z)
    simpa using this
  obtain ⟨Λ, Λ₀, hne, hΛ⟩ :=
    hextr.exists_linear_map_of_hasStrictFDerivAt (hgxa.hasStrictFDerivAt two_ne_zero) hφ
  have hΛ' : ∀ v, Λ (A v) + Λ₀ * (2 * ⟪x - z, v⟫) = 0 := by
    intro v
    have := hΛ v
    simpa [innerSL_apply_apply, inner_sub_left] using this
  have hΛ₀ : Λ₀ ≠ 0 := by
    rintro rfl
    apply hne
    have : Λ = 0 := by
      ext u
      obtain ⟨v, rfl⟩ := hsurj x hxV u
      simpa using hΛ' v
    simp [this]
  set μ : StrongDual ℝ F := LinearMap.toContinuousLinearMap ((-(2 * Λ₀)⁻¹) • Λ) with hμdef
  have hμ : ∀ v, μ (A v) = ⟪x - z, v⟫ := by
    intro v
    have h := hΛ' v
    simp only [hμdef, LinearMap.coe_toContinuousLinearMap', LinearMap.smul_apply, smul_eq_mul]
    have h2 : Λ (A v) = -(2 * Λ₀) * ⟪x - z, v⟫ := by linarith
    rw [h2]
    field_simp
  -- The multiplier has norm `O(‖x - z‖)`.
  have hμbound : ‖μ‖ ≤ 2 * ‖R₀‖ * ‖x - z‖ := by
    have hAA : ‖A₀ - A‖ * ‖R₀‖ ≤ 1 / 2 := by rw [norm_sub_rev]; exact hxA
    have key : ‖μ‖ ≤ ‖R₀‖ * ‖x - z‖ + ‖μ‖ * (1 / 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
      have hsplit : μ u = ⟪x - z, R₀ u⟫ + μ ((A₀ - A) (R₀ u)) := by
        conv_lhs => rw [← hR₀ u]
        rw [← hμ, ← map_add]
        congr 1
        simp
      rw [hsplit]
      calc ‖⟪x - z, R₀ u⟫ + μ ((A₀ - A) (R₀ u))‖
          ≤ ‖⟪x - z, R₀ u⟫‖ + ‖μ ((A₀ - A) (R₀ u))‖ := norm_add_le _ _
        _ ≤ ‖x - z‖ * (‖R₀‖ * ‖u‖) + ‖μ‖ * (‖A₀ - A‖ * (‖R₀‖ * ‖u‖)) := by
          gcongr
          · rw [Real.norm_eq_abs]
            exact (abs_real_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_left (R₀.le_opNorm u) (norm_nonneg _))
          · exact (μ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
              (((A₀ - A).le_opNorm _).trans
                (mul_le_mul_of_nonneg_left (R₀.le_opNorm u) (norm_nonneg _))) (norm_nonneg _))
        _ ≤ (‖R₀‖ * ‖x - z‖ + ‖μ‖ * (1 / 2)) * ‖u‖ := by
          have := mul_le_mul_of_nonneg_left hAA (mul_nonneg (norm_nonneg μ) (norm_nonneg u))
          nlinarith [norm_nonneg u, norm_nonneg μ]
    linarith
  -- Second-order Taylor estimate: `‖A (y - x)‖ ≤ L ‖y - x‖²`.
  have htaylor : ‖A (y - x)‖ ≤ L * ‖y - x‖ ^ 2 := by
    set s := closedBall x ‖y - x‖ ∩ ball p ρ
    have hs : Convex ℝ s := (convex_closedBall _ _).inter (convex_ball _ _)
    have hxs : x ∈ s := ⟨mem_closedBall_self (norm_nonneg _), hx⟩
    have hys : y ∈ s := ⟨by rw [mem_closedBall, dist_eq_norm], hy⟩
    have hderiv : ∀ u ∈ s, HasFDerivWithinAt (fun u => g u - A u) (fderiv ℝ g u - A) s u := by
      intro u hu
      have huV := (hball u hu.2).1
      have hgu : ContDiffAt ℝ 2 g u := hg.contDiffAt (hV.mem_nhds huV)
      exact ((hgu.differentiableAt (by norm_num)).hasFDerivAt.sub
        A.hasFDerivAt).hasFDerivWithinAt
    have hbound : ∀ u ∈ s, ‖fderiv ℝ g u - A‖ ≤ L * ‖y - x‖ := by
      intro u hu
      have hut := (hball u hu.2).2.1
      rw [← dist_eq_norm]
      calc dist (fderiv ℝ g u) A ≤ L * dist u x := hL.dist_le_mul u hut x hxt
        _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (mem_closedBall.1 hu.1) L.2
    have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hxs hys
    simp only [hgx, hgy, zero_sub] at this
    rw [show -A y - -A x = -(A y - A x) by abel, norm_neg] at this
    rw [map_sub]
    calc ‖A y - A x‖ ≤ L * ‖y - x‖ * ‖y - x‖ := this
      _ = L * ‖y - x‖ ^ 2 := by ring
  calc |⟪x - z, y - x⟫| = ‖μ (A (y - x))‖ := by rw [hμ, Real.norm_eq_abs]
    _ ≤ ‖μ‖ * ‖A (y - x)‖ := μ.le_opNorm _
    _ ≤ (2 * ‖R₀‖ * ‖x - z‖) * (L * ‖y - x‖ ^ 2) :=
        mul_le_mul hμbound htaylor (norm_nonneg _) (by positivity)
    _ = 2 * ‖R₀‖ * L * ‖x - z‖ * ‖y - x‖ ^ 2 := by ring

/-- A nearest-point map `r` to a compact set `K` of a metric space is continuous at every point
`z₀` whose nearest point in `K` is unique. -/
theorem Metric.continuousAt_of_forall_eq_of_infDist_eq {α : Type*} [MetricSpace α] {K : Set α}
    (hK : IsCompact K) {r : α → α} (hrK : ∀ z, r z ∈ K) (hr : ∀ z, dist z (r z) = infDist z K)
    {z₀ : α} (huniq : ∀ y ∈ K, dist z₀ y = infDist z₀ K → y = r z₀) : ContinuousAt r z₀ := by
  rw [Metric.continuousAt_iff]
  intro η hη
  set S := K ∩ (ball (r z₀) η)ᶜ
  have hS : IsCompact S := hK.inter_right isOpen_ball.isClosed_compl
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · refine ⟨1, one_pos, fun z _ => ?_⟩
    by_contra h
    have : r z ∈ S := ⟨hrK z, fun hb => h (mem_ball.1 hb)⟩
    rw [hSe] at this
    exact this
  obtain ⟨k₀, hk₀S, hk₀min⟩ := hS.exists_isMinOn hSne
    ((continuous_const.dist continuous_id).sub continuous_const).continuousOn
      (f := fun k => dist z₀ k - infDist z₀ K)
  set τ := dist z₀ k₀ - infDist z₀ K
  have hτ : 0 < τ := by
    have h0 : infDist z₀ K ≤ dist z₀ k₀ := infDist_le_dist_of_mem hk₀S.1
    rcases h0.lt_or_eq with h | h
    · exact sub_pos.2 h
    · exfalso
      have := huniq k₀ hk₀S.1 h.symm
      apply hk₀S.2
      rw [this]
      exact mem_ball_self hη
  refine ⟨τ / 2, half_pos hτ, fun z hz => ?_⟩
  by_contra h
  have hzS : r z ∈ S := ⟨hrK z, fun hb => h (mem_ball.1 hb)⟩
  have h1 : τ ≤ dist z₀ (r z) - infDist z₀ K := hk₀min hzS
  have h2 : dist z₀ (r z) ≤ dist z₀ z + dist z (r z) := dist_triangle _ _ _
  have h3 : infDist z K ≤ infDist z₀ K + dist z z₀ := infDist_le_infDist_add_dist
  rw [hr z, dist_comm z₀ z] at *
  linarith

/-- Uniform version of `abs_inner_le_of_forall_norm_le_of_regularZeroSet` over a compact set
which is locally the regular zero set of `C²` maps. -/
theorem IsCompact.exists_abs_inner_le_of_regularZeroSet [CompleteSpace E] {K : Set E}
    (hK : IsCompact K)
    (hloc : ∀ p ∈ K, ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)),
      ContDiffOn ℝ 2 g V ∧ (∀ x ∈ V, Function.Surjective (fderiv ℝ g x)) ∧
        K ∩ V = {x ∈ V | g x = 0}) :
    ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K, ∀ z : E, dist y x < δ →
      (∀ k ∈ K, ‖z - x‖ ≤ ‖z - k‖) → |⟪x - z, y - x⟫| ≤ C * ‖x - z‖ * ‖y - x‖ ^ 2 := by
  have hl : ∀ p ∈ K, ∃ ρ > 0, ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ∀ z : E, x ∈ ball p ρ →
      y ∈ ball p ρ → (∀ k ∈ K, ‖z - x‖ ≤ ‖z - k‖) →
        |⟪x - z, y - x⟫| ≤ C * ‖x - z‖ * ‖y - x‖ ^ 2 := fun p hp => by
    obtain ⟨V, hV, hpV, m, g, hg, hs, hKV⟩ := hloc p hp
    exact abs_inner_le_of_forall_norm_le_of_regularZeroSet hV hpV hg hs hKV
  choose! ρ hρ C hC using hl
  obtain ⟨b, hbK, hbfin, hcov⟩ := hK.elim_finite_subcover_image (b := K)
    (c := fun p => ball p (ρ p)) (fun _ _ => isOpen_ball)
    (fun p hp => mem_biUnion hp (mem_ball_self (hρ p hp)))
  have hcov' : K ⊆ ⋃ i : b, ball (i : E) (ρ i) := by
    rwa [← biUnion_eq_iUnion b (fun i _ => ball i (ρ i))]
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun _ => isOpen_ball) hcov'
  refine ⟨δ, hδ, ∑ i ∈ hbfin.toFinset, max (C i) 0,
    Finset.sum_nonneg fun _ _ => le_max_right _ _, ?_⟩
  intro x hxK y hyK z hxy hmin
  obtain ⟨⟨i, hib⟩, hi⟩ := hleb x hxK
  have hx : x ∈ ball i (ρ i) := hi (mem_ball_self hδ)
  have hy : y ∈ ball i (ρ i) := hi (mem_ball.2 hxy)
  have hle : C i ≤ ∑ i ∈ hbfin.toFinset, max (C i) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (C i) 0)
      (fun _ _ => le_max_right _ _) (hbfin.mem_toFinset.2 hib))
  refine (hC i (hbK hib) x hxK y hyK z hx hy hmin).trans ?_
  gcongr

/-- Positive reach of a compact set which is locally the regular zero set of `C²` maps: there is
`ε > 0` such that every point at distance `< ε` from `K` has a unique nearest point in `K`. -/
theorem IsCompact.exists_pos_eq_of_infDist_eq_of_regularZeroSet [CompleteSpace E] {K : Set E}
    (hK : IsCompact K)
    (hloc : ∀ p ∈ K, ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)),
      ContDiffOn ℝ 2 g V ∧ (∀ x ∈ V, Function.Surjective (fderiv ℝ g x)) ∧
        K ∩ V = {x ∈ V | g x = 0}) :
    ∃ ε > 0, ∀ z : E, infDist z K < ε → ∀ x ∈ K, ∀ y ∈ K,
      dist z x = infDist z K → dist z y = infDist z K → x = y := by
  obtain ⟨δ, hδ, C, hC0, hC⟩ := hK.exists_abs_inner_le_of_regularZeroSet hloc
  refine ⟨min (δ / 2) (1 / (2 * C + 1)), lt_min (half_pos hδ) (by positivity), ?_⟩
  intro z hz x hxK y hyK hx hy
  set d := infDist z K
  have hzd1 : d < δ / 2 := hz.trans_le (min_le_left _ _)
  have hzd2 : d < 1 / (2 * C + 1) := hz.trans_le (min_le_right _ _)
  have hd0 : 0 ≤ d := infDist_nonneg
  have hmin : ∀ k ∈ K, ‖z - x‖ ≤ ‖z - k‖ := fun k hk => by
    rw [← dist_eq_norm, ← dist_eq_norm, hx]
    exact infDist_le_dist_of_mem hk
  have hxy : dist y x < δ := by
    calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ = 2 * d := by rw [dist_comm, hy, hx]; ring
      _ < δ := by linarith
  have hest := hC x hxK y hyK z hxy hmin
  have hnx : ‖x - z‖ = d := by rw [← dist_eq_norm, dist_comm, hx]
  have hny : ‖z - y‖ = d := by rw [← dist_eq_norm, hy]
  -- `‖y - x‖² = 2 ⟪z - x, y - x⟫` since `x` and `y` are equidistant from `z`.
  have hid : ‖y - x‖ ^ 2 = -2 * ⟪x - z, y - x⟫ := by
    have h1 := norm_sub_sq_real (z - x) (y - x)
    rw [show z - x - (y - x) = z - y by abel, hny, ← norm_neg (z - x), neg_sub, hnx,
      ← neg_sub x z, inner_neg_left] at h1
    linarith
  rw [hnx] at hest
  have hle : ‖y - x‖ ^ 2 ≤ 2 * C * d * ‖y - x‖ ^ 2 := by
    have := neg_abs_le ⟪x - z, y - x⟫
    nlinarith
  have hlt : 2 * C * d < 1 := by
    have h2 : (2 * C + 1) * d < 1 := by
      rwa [lt_div_iff₀ (by positivity), mul_comm] at hzd2
    nlinarith
  have hsq : ‖y - x‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖y - x‖]
  have : y - x = 0 := by simpa using hsq
  exact (sub_eq_zero.1 this).symm

/-- A compact set which is locally the regular zero set of `C²` maps is a retract of one of its
thickenings: there are `ε > 0` and `r : E → E`, continuous on the `ε`-thickening of `K`, mapping
it into `K` and fixing `K` pointwise (the nearest-point map). -/
theorem IsCompact.exists_retraction_thickening_of_regularZeroSet [CompleteSpace E] {K : Set E}
    (hK : IsCompact K)
    (hloc : ∀ p ∈ K, ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)),
      ContDiffOn ℝ 2 g V ∧ (∀ x ∈ V, Function.Surjective (fderiv ℝ g x)) ∧
        K ∩ V = {x ∈ V | g x = 0}) :
    ∃ ε > 0, ∃ r : E → E, ContinuousOn r (thickening ε K) ∧ MapsTo r (thickening ε K) K ∧
      ∀ x ∈ K, r x = x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, id, by simp [thickening_empty]⟩
  obtain ⟨ε, hε, huniq⟩ := hK.exists_pos_eq_of_infDist_eq_of_regularZeroSet hloc
  choose r hrK hr using hK.exists_infDist_eq_dist hne
  have hr' : ∀ z, dist z (r z) = infDist z K := fun z => (hr z).symm
  refine ⟨ε, hε, r, fun z hz => ?_, fun z _ => hrK z, fun x hx => ?_⟩
  · rw [mem_thickening_iff_infDist_lt hne] at hz
    exact (Metric.continuousAt_of_forall_eq_of_infDist_eq hK hrK hr'
      fun y hy hzy => huniq z hz y hy (r z) (hrK z) hzy (hr' z)).continuousWithinAt
  · have h0 : infDist x K = 0 := infDist_zero_of_mem hx
    exact huniq x (by rw [h0]; exact hε) (r x) (hrK x) x hx (hr' x) (by rw [h0, dist_self])

/-- A compact set which is locally the regular zero set of `C²` maps (a compact `C²` submanifold
given by local regular equations) is a neighbourhood retract: there are an open `T ⊇ K` and a
continuous retraction `r : T → K`. -/
theorem IsCompact.exists_isOpen_retraction_of_regularZeroSet [CompleteSpace E] {K : Set E}
    (hK : IsCompact K)
    (hloc : ∀ p ∈ K, ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ ∃ (m : ℕ) (g : E → EuclideanSpace ℝ (Fin m)),
      ContDiffOn ℝ 2 g V ∧ (∀ x ∈ V, Function.Surjective (fderiv ℝ g x)) ∧
        K ∩ V = {x ∈ V | g x = 0}) :
    ∃ (T : Set E) (_ : IsOpen T) (hKT : K ⊆ T) (r : C(T, K)), ∀ x : K, r (inclusion hKT x) = x := by
  obtain ⟨ε, hε, r, hcont, hmaps, hfix⟩ :=
    hK.exists_retraction_thickening_of_regularZeroSet hloc
  refine ⟨thickening ε K, isOpen_thickening, self_subset_thickening hε K,
    ⟨fun z => ⟨r z, hmaps z.2⟩, hcont.domRestrict.subtype_mk _⟩, fun x => ?_⟩
  ext
  exact hfix x x.2

end
