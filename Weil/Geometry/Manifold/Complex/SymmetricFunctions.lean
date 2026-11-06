module

public import Weil.Geometry.Manifold.Complex.BranchedCover
public import Weil.Analysis.Meromorphic.RiemannSphere
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Meromorphic functions on a compact Riemann surface are algebraic over `ℂ(t)`

Let `M` be a compact Riemann surface and `t : M → ℂ` a meromorphic function in normal form which
is constant on no open set, of degree `d = fibreDegree t`. Every meromorphic function `f` on `M`
satisfies a polynomial equation `P(t, f) = 0` of degree `d` in `f`, with coefficients
polynomials in `t`.

The proof is the classical one by symmetric functions. For a value `z`, let `e_k(z)` be the
`k`-th elementary symmetric function of the values of `f` at the points of the fibre of `z`
where `t` is holomorphic. Off a finite set of values (the values of `t` at its critical points
and at the poles of `f`), the fibre is given by `d` holomorphic local sections of `t`, so `e_k`
is holomorphic there. Near any value `b` (and near `∞`) the values of `f` on the fibre grow at
most like a power of `|z - b|⁻¹` (of `|z|`): this is a local estimate at each point of `M`,
made uniform by compactness. By the removable singularity theorem `e_k` is meromorphic on the
Riemann sphere, hence a rational function. Clearing denominators in
`∏_{x ∈ t⁻¹(z)} (Y - f(x)) = ∑_k (-1)^k e_k(z) Y^{d-k}` gives `P`, and `P(t(x), f(x)) = 0` for
every `x` off a finite set.

## Main definitions

* `RiemannSurface.HasNonzeroDerivAt t x`: in some chart at `x`, `t` is analytic with nonzero
  derivative.
* `RiemannSurface.fibreFinset t z`: the finite set `regularFibre t z`, as a `Finset`.
* `RiemannSurface.fibreEsymm t f k z`: the `k`-th elementary symmetric function of the values of
  `f` on `fibreFinset t z`.
* `RiemannSurface.fibreSingularValues t f`: the finitely many values over which these symmetric
  functions may fail to be holomorphic.

## Main results

* `Complex.meromorphicAt_of_eventually_norm_mul_pow_le`: a function holomorphic on a punctured
  neighbourhood of `c`, with at most polynomial growth in `|z - c|⁻¹`, is meromorphic at `c`.
* `RiemannSurface.meromorphicAt_fibreEsymm`, `RiemannSurface.meromorphicAt_fibreEsymm_inv`:
  the symmetric functions are meromorphic on the Riemann sphere.
* `RiemannSurface.exists_polynomial_eval_eq_zero_of_notMem`: the same, with `P(t(x), f(x)) = 0`
  whenever `t(x)` avoids a finite set.
* `RiemannSurface.exists_polynomial_eval_eq_zero`: every meromorphic function `f` satisfies
  `P(t, f) = 0` codiscretely for some `P ∈ ℂ[t][Y]` of degree `fibreDegree t`.

## References

* [O. Forster, *Lectures on Riemann Surfaces*][forster1981], §8.
-/

@[expose] public section

open Manifold Set Filter Topology Polynomial

namespace Complex

/-- **Removable singularities with polynomial growth.** A function holomorphic on a punctured
neighbourhood of `c` such that `g z * (z - c) ^ N` stays bounded is meromorphic at `c`. -/
theorem meromorphicAt_of_eventually_norm_mul_pow_le {g : ℂ → ℂ} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ g z) {N : ℕ} {C : ℝ}
    (hb : ∀ᶠ z in 𝓝[≠] c, ‖g z‖ * ‖z - c‖ ^ N ≤ C) : MeromorphicAt g c := by
  set h : ℂ → ℂ := fun z => (z - c) ^ N * g z with hh
  have hev := hd.and hb
  rw [eventually_nhdsWithin_iff] at hev
  set s := {z | z ∈ ({c}ᶜ : Set ℂ) → DifferentiableAt ℂ g z ∧ ‖g z‖ * ‖z - c‖ ^ N ≤ C}
  have hs : s ∈ 𝓝 c := hev
  have hdiff : DifferentiableOn ℂ h (s \ {c}) := fun z hz =>
    (((differentiableAt_id.sub_const c).pow N).mul (hz.1 hz.2).1).differentiableWithinAt
  have hbdd : BddAbove (norm ∘ h '' (s \ {c})) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have := (hz.1 hz.2).2
    simp only [Function.comp_apply, hh, norm_mul, norm_pow]
    linarith
  have han : AnalyticAt ℂ (Function.update h c (limUnder (𝓝[≠] c) h)) c :=
    (differentiableOn_update_limUnder_of_bddAbove hs hdiff hbdd).analyticAt hs
  have hmh : MeromorphicAt h c := han.meromorphicAt.congr (by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Function.update_of_ne hz _ _)
  have hpow : MeromorphicAt (fun z => ((z - c) ^ N)⁻¹) c :=
    ((analyticAt_id.sub analyticAt_const).pow N).meromorphicAt.inv
  refine (hpow.mul hmh).congr ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : (z - c) ^ N ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
  simp only [Pi.mul_apply, hh]
  field_simp

/-- `Inv.inv` maps a punctured neighbourhood of `0` to a neighbourhood of `∞`. -/
theorem tendsto_inv_nhdsNE_zero_cobounded :
    Tendsto (Inv.inv : ℂ → ℂ) (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
  rw [← inv_cobounded₀ (α := ℂ)]
  change Tendsto Inv.inv (Filter.map Inv.inv _) _
  rw [tendsto_map'_iff]
  simp only [inv_involutive.comp_self]
  exact tendsto_id

end Complex

/-- The elementary symmetric functions of a family of complex numbers which, multiplied by
`r ≥ 0`, are bounded by `C`, are bounded after multiplication by the corresponding power of
`r`. -/
theorem Finset.norm_esymm_map_val_mul_pow_le {ι : Type*} (s : Finset ι) (g : ι → ℂ) {r C : ℝ}
    (hr : 0 ≤ r) (hC : ∀ i ∈ s, ‖g i‖ * r ≤ C) (k : ℕ) :
    ‖(s.val.map g).esymm k‖ * r ^ k ≤ (s.card.choose k : ℝ) * C ^ k := by
  rw [Finset.esymm_map_val]
  calc ‖∑ u ∈ s.powersetCard k, ∏ i ∈ u, g i‖ * r ^ k
      ≤ (∑ u ∈ s.powersetCard k, ‖∏ i ∈ u, g i‖) * r ^ k :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hr k)
    _ = ∑ u ∈ s.powersetCard k, ∏ i ∈ u, (‖g i‖ * r) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [norm_prod, Finset.prod_mul_distrib, Finset.prod_const,
          (Finset.mem_powersetCard.1 hu).2]
    _ ≤ ∑ u ∈ s.powersetCard k, C ^ k := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hu' := Finset.mem_powersetCard.1 hu
        rw [← hu'.2, ← Finset.prod_const]
        exact Finset.prod_le_prod (fun i _ => mul_nonneg (norm_nonneg _) hr)
          fun i hi => hC i (hu'.1 hi)
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

namespace RiemannSurface

section Defs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- In some chart of the atlas at `x`, `t` is analytic with nonzero derivative. -/
def HasNonzeroDerivAt (t : M → ℂ) (x : M) : Prop :=
  ∃ e ∈ atlas ℂ M, x ∈ e.source ∧ AnalyticAt ℂ (t ∘ e.symm) (e x) ∧ deriv (t ∘ e.symm) (e x) ≠ 0

open Classical in
/-- The fibre `regularFibre t z` as a `Finset` (empty if the fibre is infinite). -/
noncomputable def fibreFinset (t : M → ℂ) (z : ℂ) : Finset M :=
  if h : (regularFibre t z).Finite then h.toFinset else ∅

/-- The `k`-th elementary symmetric function of the values of `f` at the points of the fibre of
`z` at which `t` is holomorphic. -/
noncomputable def fibreEsymm (t f : M → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  ((fibreFinset t z).val.map f).esymm k

variable {t : M → ℂ} {z : ℂ}

theorem mem_fibreFinset (h : (regularFibre t z).Finite) {x : M} :
    x ∈ fibreFinset t z ↔ x ∈ regularFibre t z := by
  simp [fibreFinset, h]

theorem coe_fibreFinset (h : (regularFibre t z).Finite) :
    (fibreFinset t z : Set M) = regularFibre t z := by
  ext x
  exact mem_fibreFinset h

end Defs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  {t : M → ℂ}

theorem HasNonzeroDerivAt.isUnramifiedAt {x : M} (h : HasNonzeroDerivAt t x) :
    IsUnramifiedAt t x := by
  obtain ⟨e, he, hx, han, hd⟩ := h
  exact isUnramifiedAt_of_mem_atlas he hx han hd

theorem HasNonzeroDerivAt.mdifferentiableAt {x : M} (h : HasNonzeroDerivAt t x) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t x := by
  obtain ⟨e, he, hx, han, -⟩ := h
  exact (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he hx).2 han.differentiableAt

/-- The points near which a meromorphic function `f` is not holomorphic are finite in number on a
compact Riemann surface. -/
theorem finite_setOf_not_eventually_mdifferentiableAt [CompactSpace M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) :
    {x | ¬∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y}.Finite := by
  refine finite_of_eventually_nhdsNE_notMem fun x => ?_
  set e := chartAt ℂ x
  have han : ∀ᶠ z in 𝓝[≠] e x, AnalyticAt ℂ (f ∘ e.symm) z :=
    _root_.MeromorphicAt.eventually_analyticAt (hf x (mem_univ x))
  have htgt : ∀ᶠ z in 𝓝[≠] e x, z ∈ e.target := mem_nhdsWithin_of_mem_nhds
    (e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x)))
  rw [eventually_nhdsNE_iff_of_mem_source e (mem_chart_source ℂ x)]
  filter_upwards [han, htgt] with z hz1 hz2
  simp only [not_not]
  exact eventually_mdifferentiableAt_of_analyticAt_comp_symm (chart_mem_atlas ℂ x)
    (e.map_target hz2) (by rwa [e.right_inv hz2])

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- A bound `‖f‖ · ‖h‖ ^ m ≤ C` near `x` when `h` vanishes at `x` (has positive order): `f` grows at
most like a power of `h⁻¹`. -/
theorem exists_norm_mul_norm_pow_le_of_orderAt_pos {f h : M → ℂ} {x : M}
    (hf : MeromorphicAt f x) (hh : MeromorphicAt h x) (hk : 0 < orderAt h x) :
    ∃ m : ℕ, ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x, ‖f y‖ * ‖h y‖ ^ m ≤ C := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 ≤ orderAt f x + m * orderAt h x := by
    cases hfo : orderAt f x with
    | top => exact ⟨0, by simp⟩
    | coe n =>
      cases hho : orderAt h x with
      | top =>
        refine ⟨1, ?_⟩
        rw [WithTop.mul_top (by norm_num)]
        simp
      | coe k =>
        rw [hho] at hk
        have hk' : 0 < k := by exact_mod_cast hk
        refine ⟨(-n).toNat, ?_⟩
        have : (0 : ℤ) ≤ n + ((-n).toNat : ℤ) * k := by
          nlinarith [Int.self_le_toNat (-n),
            mul_nonneg (Int.natCast_nonneg (-n).toNat) (by omega : (0 : ℤ) ≤ k - 1)]
        exact_mod_cast this
  have hmer : MeromorphicAt (f * h ^ m) x := hf.mul (hh.pow m)
  have hord : 0 ≤ orderAt (f * h ^ m) x := by
    rw [orderAt_mul hf (hh.pow m), orderAt_pow hh]
    exact hm
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmer hord
  refine ⟨m, ‖c‖ + 1, ?_⟩
  rw [eventually_nhdsNE_iff_of_mem_source (chartAt ℂ x) (mem_chart_source ℂ x)]
  filter_upwards [hc.norm.eventually (eventually_le_nhds (lt_add_one ‖c‖))] with z hz
  simpa [norm_mul, norm_pow] using hz

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- A uniform bound on the values of `f` on the fibres of `t`, along a filter `l` of values,
follows from a bound near every point of `M`, by compactness. -/
theorem exists_forall_regularFibre_norm_mul_pow_le [CompactSpace M] {f : M → ℂ} {l : Filter ℂ}
    {ρ : ℂ → ℂ} (hρ : ∀ᶠ z in l, ‖ρ z‖ ≤ 1)
    (hloc : ∀ x : M, ∃ V ∈ 𝓝 x, ∃ m : ℕ, ∃ C : ℝ,
      ∀ᶠ z in l, ∀ y ∈ V, y ∈ regularFibre t z → ‖f y‖ * ‖ρ z‖ ^ m ≤ C) :
    ∃ m : ℕ, ∃ C : ℝ, ∀ᶠ z in l, ∀ y ∈ regularFibre t z, ‖f y‖ * ‖ρ z‖ ^ m ≤ C := by
  have key := isCompact_univ.induction_on (p := fun S : Set M => ∃ m : ℕ, ∃ C : ℝ,
      ∀ᶠ z in l, ∀ y ∈ S, y ∈ regularFibre t z → ‖f y‖ * ‖ρ z‖ ^ m ≤ C)
    ⟨0, 0, Eventually.of_forall fun z y hy => absurd hy (notMem_empty y)⟩
    (fun S T hST ⟨m, C, h⟩ => ⟨m, C, h.mono fun z hz y hy => hz y (hST hy)⟩)
    (fun S T ⟨m₁, C₁, h₁⟩ ⟨m₂, C₂, h₂⟩ => ⟨max m₁ m₂, max C₁ C₂, by
      filter_upwards [h₁, h₂, hρ] with z hz₁ hz₂ hzρ y hy hyF
      have h0 : 0 ≤ ‖ρ z‖ := norm_nonneg _
      rcases hy with hy | hy
      · calc ‖f y‖ * ‖ρ z‖ ^ max m₁ m₂ ≤ ‖f y‖ * ‖ρ z‖ ^ m₁ :=
              mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 hzρ (le_max_left _ _))
                (norm_nonneg _)
          _ ≤ C₁ := hz₁ y hy hyF
          _ ≤ _ := le_max_left _ _
      · calc ‖f y‖ * ‖ρ z‖ ^ max m₁ m₂ ≤ ‖f y‖ * ‖ρ z‖ ^ m₂ :=
              mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 hzρ (le_max_right _ _))
                (norm_nonneg _)
          _ ≤ C₂ := hz₂ y hy hyF
          _ ≤ _ := le_max_right _ _⟩)
    (fun x _ => by
      obtain ⟨V, hV, m, C, h⟩ := hloc x
      exact ⟨V, by rwa [nhdsWithin_univ], m, C, h⟩)
  obtain ⟨m, C, h⟩ := key
  exact ⟨m, C, h.mono fun z hz y hy => hz y (mem_univ y) hy⟩

/-- The values `z` over which the symmetric functions `fibreEsymm t f k` may fail to be
holomorphic: the values of `t` at the points where it does not have nonzero derivative, and at the
points near which `f` is not holomorphic. -/
def fibreSingularValues (t f : M → ℂ) : Set ℂ :=
  t '' {x | ¬HasNonzeroDerivAt t x} ∪ t '' {x | ¬∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y}

theorem branchValues_subset_fibreSingularValues (f : M → ℂ) :
    branchValues t ⊆ fibreSingularValues t f := by
  rintro _ ⟨x, hx, rfl⟩
  exact Or.inl ⟨x, fun h => hx h.isUnramifiedAt, rfl⟩

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem hasNonzeroDerivAt_of_notMem_fibreSingularValues {f : M → ℂ} {x : M}
    (hx : t x ∉ fibreSingularValues t f) : HasNonzeroDerivAt t x := by
  by_contra h
  exact hx (Or.inl ⟨x, h, rfl⟩)

section Fibres

variable (ht : ∀ x, MeromorphicNFAt t x) (hnc : ∀ x (c : ℂ), orderAt (fun y => t y - c) x ≠ ⊤)
include ht

/-- The values of `f` on the fibres of `t` over a punctured neighbourhood of `b` grow at most like
a power of `|z - b|⁻¹`. -/
theorem exists_forall_regularFibre_norm_mul_sub_pow_le [CompactSpace M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) (b : ℂ) :
    ∃ m : ℕ, ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] b, ∀ y ∈ regularFibre t z, ‖f y‖ * ‖z - b‖ ^ m ≤ C := by
  refine exists_forall_regularFibre_norm_mul_pow_le (ρ := fun z => z - b) ?_ fun x => ?_
  · filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds b one_pos)] with z hz
    simpa [dist_eq_norm] using hz
  by_cases hx : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t x
  · by_cases hxb : t x = b
    · set e := chartAt ℂ x
      have han : AnalyticAt ℂ (t ∘ e.symm) (e x) := (mdifferentiableAt_iff_analyticAt_chart ht).1 hx
      have hh : MeromorphicAt (fun y => t y - b) x :=
        (ht x).meromorphicAt.sub (meromorphicAt_const b x)
      have hpos : 0 < orderAt (fun y => t y - b) x := by
        have han' : AnalyticAt ℂ ((fun y => t y - b) ∘ e.symm) (e x) := han.sub analyticAt_const
        have h0 : 0 ≤ orderAt (fun y => t y - b) x := han'.meromorphicOrderAt_nonneg
        have hne : orderAt (fun y => t y - b) x ≠ 0 := by
          change meromorphicOrderAt _ _ ≠ 0
          rw [Ne, han'.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
          simp [e.left_inv (mem_chart_source ℂ x), hxb]
        exact lt_of_le_of_ne h0 hne.symm
      obtain ⟨m, C, hC⟩ := exists_norm_mul_norm_pow_le_of_orderAt_pos (hf x (mem_univ x)) hh hpos
      rw [eventually_nhdsWithin_iff] at hC
      refine ⟨_, hC, m, C, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz y hyV hyF
      have hyx : y ≠ x := by
        rintro rfl
        exact hz (hyF.2.symm.trans hxb)
      have := hyV hyx
      rwa [hyF.2] at this
    · have hc : ContinuousAt t x := hx.continuousAt
      have hδ : 0 < dist (t x) b / 2 := half_pos (dist_pos.2 hxb)
      refine ⟨t ⁻¹' Metric.ball (t x) (dist (t x) b / 2),
        hc.preimage_mem_nhds (Metric.ball_mem_nhds _ hδ), 0, 0, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds b hδ)] with z hz y hyV hyF
      exfalso
      rw [mem_preimage, hyF.2, Metric.mem_ball, dist_comm] at hyV
      rw [Metric.mem_ball] at hz
      have := dist_triangle (t x) z b
      linarith
  · refine ⟨_, eventually_lt_norm_of_not_mdifferentiableAt ht hx (‖b‖ + 1), 0, 0, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds b one_pos)] with z hz y hyV hyF
    exfalso
    have h1 := hyV hyF.1
    rw [hyF.2] at h1
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := norm_sub_norm_le z b
    linarith

/-- The values of `f` on the fibres of `t` over a neighbourhood of `∞` grow at most like a power
of `|z|`. -/
theorem exists_forall_regularFibre_norm_mul_inv_pow_le [CompactSpace M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) :
    ∃ m : ℕ, ∃ C : ℝ, ∀ᶠ z in Bornology.cobounded ℂ, ∀ y ∈ regularFibre t z,
      ‖f y‖ * ‖z⁻¹‖ ^ m ≤ C := by
  have hcob : ∀ R : ℝ, ∀ᶠ z in Bornology.cobounded ℂ, R < ‖z‖ := fun R =>
    tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)
  refine exists_forall_regularFibre_norm_mul_pow_le (ρ := fun z => z⁻¹) ?_ fun x => ?_
  · filter_upwards [hcob 1] with z hz
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hz.le
  by_cases hx : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t x
  · refine ⟨t ⁻¹' Metric.ball (t x) 1,
      hx.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos), 0, 0, ?_⟩
    filter_upwards [hcob (‖t x‖ + 1)] with z hz y hyV hyF
    exfalso
    rw [mem_preimage, hyF.2, Metric.mem_ball, dist_eq_norm] at hyV
    have := norm_sub_norm_le z (t x)
    linarith
  · have hh : MeromorphicAt (fun y => (t y)⁻¹) x := (ht x).meromorphicAt.inv
    have hneg : orderAt t x < 0 := by
      rcases meromorphicNFAt_iff_analyticAt_or.1 (ht x) with h | ⟨-, h, -⟩
      · exact absurd ((mdifferentiableAt_iff_analyticAt_chart ht).2 h) hx
      · exact h
    have hpos : 0 < orderAt (fun y => (t y)⁻¹) x := by
      have : orderAt (fun y => (t y)⁻¹) x = -orderAt t x := orderAt_inv
      rw [this]
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hneg.trans_le le_top).ne
      rw [← hn] at hneg ⊢
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg]
      exact_mod_cast (neg_pos.2 (by exact_mod_cast hneg))
    obtain ⟨m, C, hC⟩ := exists_norm_mul_norm_pow_le_of_orderAt_pos (hf x (mem_univ x)) hh hpos
    rw [eventually_nhdsWithin_iff] at hC
    refine ⟨_, hC, m, C, Eventually.of_forall fun z y hyV hyF => ?_⟩
    have hyx : y ≠ x := by
      rintro rfl
      exact hx hyF.1
    have := hyV hyx
    rwa [hyF.2] at this

include hnc

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- Points at which `t` has vanishing derivative (in a chart), or a pole, are isolated. -/
theorem eventually_hasNonzeroDerivAt (x : M) : ∀ᶠ y in 𝓝[≠] x, HasNonzeroDerivAt t y := by
  set e := chartAt ℂ x with he
  set φ := t ∘ e.symm with hφ
  have hNF : _root_.MeromorphicNFAt φ (e x) := ht x
  set c := φ (e x) with hc
  have hNFc : _root_.MeromorphicNFAt (fun z => φ z - c) (e x) := by
    rcases meromorphicNFAt_iff_analyticAt_or.1 hNF with h | ⟨-, -, h0⟩
    · exact (h.sub analyticAt_const).meromorphicNFAt
    · have : (fun z => φ z - c) = φ := by funext z; simp [c, h0]
      rw [this]; exact hNF
  have hord0 : meromorphicOrderAt (fun z => φ z - c) (e x) ≠ 0 := by
    rw [Ne, hNFc.meromorphicOrderAt_eq_zero_iff]; simp [c]
  have hordtop : meromorphicOrderAt (fun z => φ z - c) (e x) ≠ ⊤ := hnc x c
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hordtop
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hord0 hn.symm
  have hder : meromorphicOrderAt (deriv (fun z => φ z - c)) (e x) = ↑(n - 1) :=
    meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hn0) hn.symm
  have hder' : deriv (fun z => φ z - c) = deriv φ := by
    funext z; exact deriv_sub_const c
  have hmer' : _root_.MeromorphicAt (deriv φ) (e x) := hNF.meromorphicAt.deriv
  have hne : ∀ᶠ z in 𝓝[≠] e x, deriv φ z ≠ 0 := by
    rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer', ← hder', hder]
    simp
  have han : ∀ᶠ z in 𝓝[≠] e x, AnalyticAt ℂ φ z := hNF.meromorphicAt.eventually_analyticAt
  have htgt : ∀ᶠ z in 𝓝[≠] e x, z ∈ e.target := mem_nhdsWithin_of_mem_nhds
    (e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ x)))
  rw [eventually_nhdsNE_iff_of_mem_source e (mem_chart_source ℂ x)]
  filter_upwards [hne, han, htgt] with z hz1 hz2 hz3
  exact ⟨e, chart_mem_atlas ℂ x, e.map_target hz3, by rwa [e.right_inv hz3],
    by rwa [e.right_inv hz3]⟩

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- On a compact Riemann surface, `t` has nonzero derivative at all but finitely many points. -/
theorem finite_not_hasNonzeroDerivAt [CompactSpace M] : {x | ¬HasNonzeroDerivAt t x}.Finite :=
  finite_of_eventually_nhdsNE_notMem fun x =>
    (eventually_hasNonzeroDerivAt ht hnc x).mono fun _ hy h => h hy

/-- If every point of the fibre of `z₀` is a point where `t` has nonzero derivative and near which
`f` is holomorphic, the symmetric functions of `f` over the fibres are holomorphic at `z₀`. -/
theorem differentiableAt_fibreEsymm [CompactSpace M] [T2Space M] {f : M → ℂ} {z₀ : ℂ}
    (h₁ : ∀ x ∈ regularFibre t z₀, HasNonzeroDerivAt t x)
    (h₂ : ∀ x ∈ regularFibre t z₀, ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (k : ℕ) :
    DifferentiableAt ℂ (fibreEsymm t f k) z₀ := by
  obtain ⟨r, hr, σ, hσt, hσc, hσb, hσF⟩ :=
    exists_local_sections ht hnc (fun x hx => (h₁ x hx).isUnramifiedAt)
  have : Fintype (regularFibre t z₀) := (finite_regularFibre ht hnc z₀).fintype
  have hball : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hσd : ∀ i, DifferentiableAt ℂ (fun z => f (σ i z)) z₀ := by
    intro i
    obtain ⟨e, he, hxe, han, hd⟩ := h₁ i i.2
    have hfi := (h₂ i i.2).self_of_nhds
    have hσca : ContinuousAt (σ i) z₀ := (hσc i).continuousAt hball
    rw [← hσb i] at hxe han hd hfi
    have hsrc : ∀ᶠ z in 𝓝 z₀, σ i z ∈ e.source :=
      hσca.preimage_mem_nhds (e.open_source.mem_nhds hxe)
    have hτ : ContinuousAt (fun z => e (σ i z)) z₀ := (e.continuousAt hxe).comp hσca
    have hinv : ∀ᶠ z in 𝓝 z₀, (t ∘ e.symm) (e (σ i z)) = z := by
      filter_upwards [hsrc, hball] with z hz hzb
      simp [e.left_inv hz, (hσt i z hzb).1]
    have hτd := HasDerivAt.of_local_left_inverse hτ han.differentiableAt.hasDerivAt hd hinv
    have hfd : DifferentiableAt ℂ (f ∘ e.symm) (e (σ i z₀)) :=
      (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he hxe).1 hfi
    refine (hfd.comp z₀ hτd.differentiableAt).congr_of_eventuallyEq ?_
    filter_upwards [hsrc] with z hz
    simp [e.left_inv hz]
  have heq : fibreEsymm t f k =ᶠ[𝓝 z₀] fun z =>
      ∑ u ∈ (Finset.univ : Finset (regularFibre t z₀)).powersetCard k, ∏ i ∈ u, f (σ i z) := by
    filter_upwards [hball] with z hz
    have hfin : (regularFibre t z).Finite := finite_regularFibre ht hnc z
    have hF : fibreFinset t z = Finset.univ.map ⟨fun i => σ i z, (hσF z hz).2⟩ := by
      ext y
      have h1 := (hσF z hz).1
      rw [mem_fibreFinset hfin, Finset.mem_map]
      simp only [h1, Finset.mem_univ, true_and, mem_range, Function.Embedding.coeFn_mk]
    rw [fibreEsymm, hF, Finset.map_val, Multiset.map_map]
    exact Finset.esymm_map_val _ _ _
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have : DifferentiableAt ℂ (∑ u ∈ (Finset.univ : Finset (regularFibre t z₀)).powersetCard k,
      ∏ i ∈ u, fun z => f (σ i z)) z₀ :=
    DifferentiableAt.sum fun u _ => DifferentiableAt.finsetProd fun i _ => hσd i
  convert this using 1
  ext z
  simp [Finset.sum_apply, Finset.prod_apply]

theorem finite_fibreSingularValues [CompactSpace M] {f : M → ℂ} (hf : MeromorphicOn f univ) :
    (fibreSingularValues t f).Finite :=
  ((finite_not_hasNonzeroDerivAt ht hnc).image t).union
    ((finite_setOf_not_eventually_mdifferentiableAt hf).image t)

theorem differentiableAt_fibreEsymm_of_notMem [CompactSpace M] [T2Space M] {f : M → ℂ} {z : ℂ}
    (hz : z ∉ fibreSingularValues t f) (k : ℕ) : DifferentiableAt ℂ (fibreEsymm t f k) z :=
  differentiableAt_fibreEsymm ht hnc
    (fun x hx => by
      by_contra h
      exact hz (Or.inl ⟨x, h, hx.2⟩))
    (fun x hx => by
      by_contra h
      exact hz (Or.inr ⟨x, h, hx.2⟩)) k

/-- A bound on the values of `f` on the fibres gives a bound on their symmetric functions. -/
theorem exists_norm_fibreEsymm_mul_pow_le [CompactSpace M] [T2Space M] {f : M → ℂ} {l : Filter ℂ}
    {ρ : ℂ → ℂ} (hl : ∀ᶠ z in l, z ∉ branchValues t) {m : ℕ} {C : ℝ}
    (h : ∀ᶠ z in l, ∀ y ∈ regularFibre t z, ‖f y‖ * ‖ρ z‖ ^ m ≤ C) (k : ℕ) :
    ∃ C' : ℝ, ∀ᶠ z in l, ‖fibreEsymm t f k z‖ * ‖ρ z‖ ^ (m * k) ≤ C' := by
  refine ⟨((fibreDegree t).choose k : ℝ) * (max C 0) ^ k, ?_⟩
  filter_upwards [hl, h] with z hz hzC
  have hfin := finite_regularFibre ht hnc z
  have hcard : (fibreFinset t z).card = fibreDegree t := by
    rw [← ncard_regularFibre_eq_fibreDegree ht hnc hz, ← Set.ncard_coe_finset,
      coe_fibreFinset hfin]
  rw [pow_mul, ← hcard]
  exact Finset.norm_esymm_map_val_mul_pow_le _ _ (pow_nonneg (norm_nonneg _) _)
    (fun y hy => (hzC y ((mem_fibreFinset hfin).1 hy)).trans (le_max_left _ _)) k

/-- The symmetric functions of `f` over the fibres of `t` are meromorphic on `ℂ`. -/
theorem meromorphicAt_fibreEsymm [CompactSpace M] [T2Space M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) (k : ℕ) (b : ℂ) : _root_.MeromorphicAt (fibreEsymm t f k) b := by
  have hS := finite_fibreSingularValues ht hnc hf
  have hev : ∀ᶠ z in 𝓝[≠] b, z ∉ fibreSingularValues t f := by
    have h1 : (fibreSingularValues t f \ {b})ᶜ ∈ 𝓝 b :=
      (hS.sdiff).isClosed.isOpen_compl.mem_nhds fun h => h.2 rfl
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzb hS'
    exact hz ⟨hS', hzb⟩
  obtain ⟨m, C, hC⟩ := exists_forall_regularFibre_norm_mul_sub_pow_le ht hf b
  obtain ⟨C', hC'⟩ := exists_norm_fibreEsymm_mul_pow_le ht hnc
    (hev.mono fun z hz h => hz (branchValues_subset_fibreSingularValues f h)) hC k
  exact Complex.meromorphicAt_of_eventually_norm_mul_pow_le
    (hev.mono fun z hz => differentiableAt_fibreEsymm_of_notMem ht hnc hz k) hC'

/-- The symmetric functions of `f` over the fibres of `t` are meromorphic at `∞`. -/
theorem meromorphicAt_fibreEsymm_inv [CompactSpace M] [T2Space M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) (k : ℕ) :
    _root_.MeromorphicAt (fun w => fibreEsymm t f k w⁻¹) 0 := by
  have hS := finite_fibreSingularValues ht hnc hf
  have hT := Complex.tendsto_inv_nhdsNE_zero_cobounded
  have hev : ∀ᶠ z in Bornology.cobounded ℂ, z ∉ fibreSingularValues t f :=
    Bornology.isBounded_def.1 hS.isBounded
  obtain ⟨m, C, hC⟩ := exists_forall_regularFibre_norm_mul_inv_pow_le ht hf
  obtain ⟨C', hC'⟩ := exists_norm_fibreEsymm_mul_pow_le ht hnc
    (hev.mono fun z hz h => hz (branchValues_subset_fibreSingularValues f h)) hC k
  refine Complex.meromorphicAt_of_eventually_norm_mul_pow_le (N := m * k) (C := C') ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, hT.eventually hev] with w hw hw'
    exact (differentiableAt_fibreEsymm_of_notMem ht hnc hw' k).comp w (differentiableAt_inv hw)
  · filter_upwards [hT.eventually hC'] with w hw
    simpa using hw

/-- The symmetric functions of `f` over the fibres of `t` are rational functions of the value,
away from finitely many values. -/
theorem exists_eval_div_eq_fibreEsymm [CompactSpace M] [T2Space M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) (k : ℕ) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ ∀ z, z ∉ fibreSingularValues t f → q.eval z ≠ 0 →
      fibreEsymm t f k z = p.eval z / q.eval z := by
  obtain ⟨p, q, hq, hpq⟩ := Complex.exists_polynomial_div_eq_of_meromorphicOn_univ
    (fun z _ => meromorphicAt_fibreEsymm ht hnc hf k z) (meromorphicAt_fibreEsymm_inv ht hnc hf k)
  refine ⟨p, q, hq, fun z hz hqz => ?_⟩
  have hne : ∀ᶠ w in 𝓝[≠] z, fibreEsymm t f k w = p.eval w / q.eval w := by
    have := disjoint_principal_right.1 (mem_codiscrete.1 hpq z)
    rwa [compl_compl] at this
  have h1 : Tendsto (fibreEsymm t f k) (𝓝[≠] z) (𝓝 (fibreEsymm t f k z)) :=
    (differentiableAt_fibreEsymm_of_notMem ht hnc hz k).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have h2 : Tendsto (fun w => p.eval w / q.eval w) (𝓝[≠] z) (𝓝 (p.eval z / q.eval z)) :=
    (((p.continuous.continuousAt).div (q.continuous.continuousAt) hqz).tendsto).mono_left
      nhdsWithin_le_nhds
  exact tendsto_nhds_unique (h1.congr' hne) h2

/-- **Every meromorphic function on a compact Riemann surface is algebraic over `ℂ(t)`**, of
degree at most `fibreDegree t`: there is `P ∈ ℂ[t][Y]` of degree `fibreDegree t` in `Y` such that
`P(t(x), f(x)) = 0` whenever `t(x)` avoids a finite set of values. -/
theorem exists_polynomial_eval_eq_zero_of_notMem [CompactSpace M] [T2Space M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) :
    ∃ P : Polynomial (Polynomial ℂ), P.natDegree = fibreDegree t ∧ P.leadingCoeff ≠ 0 ∧
      ∃ E : Set ℂ, E.Finite ∧
        ∀ x, t x ∉ E → (P.map (Polynomial.evalRingHom (t x))).eval (f x) = 0 := by
  classical
  set d := fibreDegree t with hd
  choose p q hq hpq using fun k => exists_eval_div_eq_fibreEsymm ht hnc hf k
  have hS := finite_fibreSingularValues ht hnc hf
  set E : Set ℂ := fibreSingularValues t f ∪ ⋃ k ∈ Finset.range (d + 1), {z | (q k).IsRoot z}
    with hEdef
  have hE : E.Finite := hS.union (Set.Finite.biUnion (Finset.range (d + 1)).finite_toSet
    fun k _ => Polynomial.finite_setOfPred_isRoot (hq k))
  have hmemE : ∀ z, z ∉ E →
      z ∉ fibreSingularValues t f ∧ ∀ k ∈ Finset.range (d + 1), (q k).eval z ≠ 0 := by
    intro z hz
    refine ⟨fun h => hz (Or.inl h), fun k hk h => hz (Or.inr ?_)⟩
    exact mem_iUnion₂.2 ⟨k, hk, h⟩
  set R : ℕ → ℂ[X] := fun j => ∏ i ∈ (Finset.range (d + 1)).erase j, q i with hRdef
  set Q : ℂ[X] := ∏ i ∈ Finset.range (d + 1), q i with hQdef
  set c : ℕ → ℂ[X] := fun j => (-1) ^ j * p j * R j with hcdef
  set P : Polynomial ℂ[X] := ∑ j ∈ Finset.range (d + 1), C (c j) * X ^ (d - j) with hPdef
  have hp0 : p 0 ≠ 0 := by
    obtain ⟨z, hz⟩ := hE.infinite_compl.nonempty
    obtain ⟨hzS, hzq⟩ := hmemE z hz
    have h := hpq 0 z hzS (hzq 0 (by simp))
    rw [fibreEsymm, Multiset.esymm_zero] at h
    rintro h0
    rw [h0, eval_zero, zero_div] at h
    exact one_ne_zero h
  have hR : ∀ j, R j ≠ 0 := fun j => Finset.prod_ne_zero_iff.2 fun i _ => hq i
  have hcoeff : P.coeff d = c 0 := by
    simp only [hPdef, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      have := Finset.mem_range.1 hj
      simp only [ite_eq_right_iff]
      intro h
      omega
    · simp
  have hc0 : c 0 ≠ 0 := by simp [hcdef, hp0, hR 0]
  have hdeg : P.natDegree = d := natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_sum_le_of_forall_le _ _ fun j _ =>
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)) (hcoeff ▸ hc0)
  refine ⟨P, hdeg, ?_, E, hE, fun x hx => ?_⟩
  · rw [leadingCoeff, hdeg, hcoeff]
    exact hc0
  obtain ⟨hzS, hzq⟩ := hmemE (t x) hx
  have hxF : x ∈ regularFibre t (t x) :=
    ⟨(hasNonzeroDerivAt_of_notMem_fibreSingularValues hzS).mdifferentiableAt, rfl⟩
  have hfin := finite_regularFibre ht hnc (t x)
  set s : Multiset ℂ := (fibreFinset t (t x)).val.map f with hsdef
  have hcard : Multiset.card s = d := by
    rw [hsdef, Multiset.card_map, Finset.card_val, ← Set.ncard_coe_finset, coe_fibreFinset hfin]
    exact ncard_regularFibre_eq_fibreDegree ht hnc
      (fun h => hzS (branchValues_subset_fibreSingularValues f h))
  have hzero : ((s.map fun a => X - C a).prod).eval (f x) = 0 := by
    rw [eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map, Multiset.mem_map]
    exact ⟨f x, Multiset.mem_map_of_mem f ((mem_fibreFinset hfin).2 hxF), by simp⟩
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hcard] at hzero
  have hcz : ∀ j ∈ Finset.range (d + 1),
      (c j).eval (t x) = Q.eval (t x) * ((-1) ^ j * s.esymm j) := by
    intro j hj
    have h := hpq j (t x) hzS (hzq j hj)
    have hQ : Q = q j * R j := (Finset.mul_prod_erase _ _ hj).symm
    have hqj := hzq j hj
    rw [hQ]
    simp only [hcdef, eval_mul, eval_pow, eval_neg, eval_one]
    rw [show s.esymm j = fibreEsymm t f j (t x) from rfl, h]
    field_simp
  have hsum : ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (s.esymm j * f x ^ (d - j)) = 0 := by
    simpa [eval_finsetSum] using hzero
  calc (P.map (evalRingHom (t x))).eval (f x)
      = ∑ j ∈ Finset.range (d + 1), (c j).eval (t x) * f x ^ (d - j) := by
        simp [hPdef, Polynomial.map_sum, eval_finsetSum]
    _ = Q.eval (t x) * ∑ j ∈ Finset.range (d + 1), (-1) ^ j * (s.esymm j * f x ^ (d - j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hcz j hj]
        ring
    _ = 0 := by rw [hsum, mul_zero]

/-- **Every meromorphic function on a compact Riemann surface is algebraic over `ℂ(t)`**, of
degree at most `fibreDegree t`: there is `P ∈ ℂ[t][Y]` of degree `fibreDegree t` in `Y` with
`P(t, f) = 0` away from a discrete set. -/
theorem exists_polynomial_eval_eq_zero [CompactSpace M] [T2Space M] {f : M → ℂ}
    (hf : MeromorphicOn f univ) :
    ∃ P : Polynomial (Polynomial ℂ), P.natDegree = fibreDegree t ∧ P.leadingCoeff ≠ 0 ∧
      ∀ᶠ x in Filter.codiscrete M, (P.map (Polynomial.evalRingHom (t x))).eval (f x) = 0 := by
  obtain ⟨P, h1, h2, E, hE, hP⟩ := exists_polynomial_eval_eq_zero_of_notMem ht hnc hf
  refine ⟨P, h1, h2, ?_⟩
  have hfin : (t ⁻¹' E).Finite := hE.preimage' fun b _ => finite_setOf_eq ht hnc b
  filter_upwards [hfin.compl_mem_codiscrete] with x hx using hP x hx

end Fibres

end RiemannSurface
