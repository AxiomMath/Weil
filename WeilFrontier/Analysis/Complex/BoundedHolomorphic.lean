module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Banach spaces of bounded holomorphic functions

For a set `U ⊆ ℂ`, the bounded holomorphic functions on `U` form a subspace
`Complex.boundedHolomorphic U` of the Banach space `U →ᵇ ℂ` of bounded continuous functions with
the supremum norm: those `f` which agree on `U` with a function `ℂ → ℂ` complex differentiable on
`U`. When `U` is open this subspace is closed, since a uniform limit of holomorphic functions is
holomorphic; hence it is a Banach space. It is closed under multiplication.

Restriction to a smaller set `V ⊆ U` is a continuous linear map of norm at most one, and
multiplication by a bounded holomorphic function `g` on `V` is a continuous linear map of norm at
most `‖g‖`. The main result is that restriction is a compact operator when `U` is open and the
closure of `V` is a compact subset of `U`: by the Cauchy estimate, the functions of norm `< 1` on
`U` are uniformly Lipschitz on the closure of `V`, hence form a relatively compact family by the
Arzelà–Ascoli theorem.

## Main definitions

* `Complex.boundedHolomorphic U`: the bounded holomorphic functions on `U`, as a submodule of
  `U →ᵇ ℂ`.
* `Complex.boundedHolomorphic.restrictL`: for `V ⊆ U`, restriction
  `boundedHolomorphic U →L[ℂ] boundedHolomorphic V`.
* `Complex.boundedHolomorphic.mulL`: multiplication by a bounded holomorphic function.

## Main results

* `Complex.isClosed_boundedHolomorphic`: for `U` open, the bounded holomorphic functions form a
  closed subspace; in particular `boundedHolomorphic U` is complete.
* `Complex.norm_sub_le_of_differentiableOn_ball`: the Lipschitz bound `‖g x - g c‖ ≤ 2C/δ ‖x - c‖`
  on `ball c (δ/2)` for `g` holomorphic and bounded by `C` on `ball c δ`.
* `Complex.boundedHolomorphic.isCompactOperator_restrictL`: restriction from an open `U` to a
  set `V` whose closure is compact and contained in `U` is a compact operator.

## References

* [R. C. Gunning, *Lectures on Riemann surfaces*][gunning1966].
-/

@[expose] public section

open Set Filter Topology Metric BoundedContinuousFunction

namespace Complex

/-- The bounded holomorphic functions on `U ⊆ ℂ`: the bounded continuous functions on `U` which
agree on `U` with a function complex differentiable on `U`. -/
def boundedHolomorphic (U : Set ℂ) : Submodule ℂ (U →ᵇ ℂ) where
  carrier := {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ x : U, f x = g x}
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, e₁⟩ ⟨g₂, hg₂, e₂⟩
    exact ⟨g₁ + g₂, hg₁.add hg₂, fun x => by simp [e₁, e₂]⟩
  zero_mem' := ⟨0, differentiableOn_const 0, fun x => by simp⟩
  smul_mem' := by
    rintro c f ⟨g, hg, e⟩
    exact ⟨c • g, hg.const_smul c, fun x => by simp [e]⟩

variable {U V W : Set ℂ}

theorem mem_boundedHolomorphic {f : U →ᵇ ℂ} :
    f ∈ boundedHolomorphic U ↔ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ x : U, f x = g x :=
  Iff.rfl

open scoped Classical in
/-- A bounded continuous function on `U` is holomorphic iff its extension by zero is complex
differentiable on `U`. -/
theorem mem_boundedHolomorphic_iff_differentiableOn_dite {f : U →ᵇ ℂ} :
    f ∈ boundedHolomorphic U ↔
      DifferentiableOn ℂ (fun z => if h : z ∈ U then f ⟨z, h⟩ else 0) U := by
  refine ⟨fun ⟨g, hg, e⟩ => hg.congr fun z hz => by simp [hz, e], fun h => ⟨_, h, fun x => ?_⟩⟩
  simp [x.2]

theorem mul_mem_boundedHolomorphic {f₁ f₂ : U →ᵇ ℂ} (h₁ : f₁ ∈ boundedHolomorphic U)
    (h₂ : f₂ ∈ boundedHolomorphic U) : f₁ * f₂ ∈ boundedHolomorphic U := by
  obtain ⟨g₁, hg₁, e₁⟩ := h₁
  obtain ⟨g₂, hg₂, e₂⟩ := h₂
  exact ⟨g₁ * g₂, hg₁.mul hg₂, fun x => by simp [e₁, e₂]⟩

theorem one_mem_boundedHolomorphic : (1 : U →ᵇ ℂ) ∈ boundedHolomorphic U :=
  ⟨1, differentiableOn_const 1, fun x => by simp⟩

/-- For `U` open, a uniform limit of bounded holomorphic functions on `U` is holomorphic. -/
theorem isClosed_boundedHolomorphic (hU : IsOpen U) :
    IsClosed (boundedHolomorphic U : Set (U →ᵇ ℂ)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hF, hFf⟩ := mem_closure_iff_seq_limit.1 hf
  choose g hg e using hF
  rw [SetLike.mem_coe, mem_boundedHolomorphic_iff_differentiableOn_dite]
  classical
  refine TendstoLocallyUniformlyOn.differentiableOn (φ := atTop) (F := g) ?_
    (Eventually.of_forall hg) hU
  apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.1 hFf
  convert this using 1
  · ext n x; exact (e n x).symm
  · ext x; simp

instance (U : Set ℂ) [Fact (IsOpen U)] : CompleteSpace (boundedHolomorphic U) :=
  haveI : IsClosed (boundedHolomorphic U : Set (U →ᵇ ℂ)) :=
    isClosed_boundedHolomorphic (Fact.out)
  IsClosed.completeSpace_coe

theorem completeSpace_boundedHolomorphic (hU : IsOpen U) :
    CompleteSpace (boundedHolomorphic U) :=
  haveI : Fact (IsOpen U) := ⟨hU⟩
  inferInstance

/-- The Cauchy estimate in Lipschitz form: a function holomorphic and bounded by `C` on
`ball c δ` is `2C/δ`-Lipschitz relative to `c` on `ball c (δ / 2)`. -/
theorem norm_sub_le_of_differentiableOn_ball {g : ℂ → ℂ} {c x : ℂ} {δ C : ℝ}
    (hg : DifferentiableOn ℂ g (ball c δ)) (hC : ∀ z ∈ ball c δ, ‖g z‖ ≤ C)
    (hx : x ∈ ball c (δ / 2)) : ‖g x - g c‖ ≤ 2 * C / δ * ‖x - c‖ := by
  have hδ : 0 < δ := by
    have := mem_ball.1 hx
    linarith [dist_nonneg (x := x) (y := c)]
  have hsub : ∀ w ∈ ball c (δ / 2), closedBall w (δ / 2) ⊆ ball c δ := fun w hw z hz => by
    rw [mem_ball] at hw ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z w c]
  refine Convex.norm_image_sub_le_of_norm_deriv_le (s := ball c (δ / 2)) (fun w hw => ?_)
    (fun w hw => ?_) (convex_ball c (δ / 2)) (mem_ball_self (half_pos hδ)) hx
  · exact hg.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hw))
  · have := norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hδ)
      (hg.diffContOnCl_ball (hsub w hw))
      (fun z hz => hC z (hsub w hw (sphere_subset_closedBall hz)))
    calc ‖deriv g w‖ ≤ C / (δ / 2) := this
      _ = 2 * C / δ := by field_simp

theorem compContinuous_inclusion_mem_boundedHolomorphic (hVU : V ⊆ U) {f : U →ᵇ ℂ}
    (hf : f ∈ boundedHolomorphic U) :
    f.compContinuous ⟨inclusion hVU, continuous_inclusion hVU⟩ ∈ boundedHolomorphic V := by
  obtain ⟨g, hg, e⟩ := hf
  exact ⟨g, hg.mono hVU, fun x => e _⟩

namespace boundedHolomorphic

/-- Restriction of bounded holomorphic functions on `U` to a subset `V`. -/
noncomputable def restrictL (hVU : V ⊆ U) : boundedHolomorphic U →L[ℂ] boundedHolomorphic V :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨(f : U →ᵇ ℂ).compContinuous ⟨inclusion hVU, continuous_inclusion hVU⟩,
        compContinuous_inclusion_mem_boundedHolomorphic hVU f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun f => by
      rw [one_mul]
      exact norm_compContinuous_le (f : U →ᵇ ℂ) ⟨inclusion hVU, continuous_inclusion hVU⟩

@[simp]
theorem restrictL_apply (hVU : V ⊆ U) (f : boundedHolomorphic U) (x : V) :
    (restrictL hVU f : V →ᵇ ℂ) x = (f : U →ᵇ ℂ) (inclusion hVU x) :=
  rfl

theorem norm_restrictL_le (hVU : V ⊆ U) : ‖restrictL hVU‖ ≤ 1 :=
  (restrictL hVU).opNorm_le_bound zero_le_one fun f => by
    rw [one_mul]
    exact norm_compContinuous_le (f : U →ᵇ ℂ) ⟨inclusion hVU, continuous_inclusion hVU⟩

/-- Multiplication by a bounded holomorphic function `g` on `V`. -/
noncomputable def mulL (g : boundedHolomorphic V) :
    boundedHolomorphic V →L[ℂ] boundedHolomorphic V :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨(g : V →ᵇ ℂ) * f, mul_mem_boundedHolomorphic g.2 f.2⟩
      map_add' := fun _ _ => Subtype.ext (mul_add _ _ _)
      map_smul' := fun c _ => Subtype.ext (mul_smul_comm c _ _) }
    ‖g‖ fun f => norm_mul_le (g : V →ᵇ ℂ) f

@[simp]
theorem mulL_apply (g f : boundedHolomorphic V) (x : V) :
    (mulL g f : V →ᵇ ℂ) x = (g : V →ᵇ ℂ) x * (f : V →ᵇ ℂ) x :=
  rfl

theorem norm_mulL_le (g : boundedHolomorphic V) : ‖mulL g‖ ≤ ‖g‖ :=
  (mulL g).opNorm_le_bound (norm_nonneg _) fun f => norm_mul_le (g : V →ᵇ ℂ) f

theorem restrictL_comp (hWV : W ⊆ V) (hVU : V ⊆ U) :
    (restrictL hWV).comp (restrictL hVU) = restrictL (hWV.trans hVU) :=
  rfl

/-- The case of `isCompactOperator_restrictL` where `V` is open. -/
private theorem isCompactOperator_restrictL_of_isOpen (hU : IsOpen U) (hVo : IsOpen V)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    IsCompactOperator (restrictL (subset_closure.trans hVU)) := by
  set K := closure V
  have : CompactSpace K := isCompact_iff_compactSpace.1 hV
  obtain ⟨δ, hδ, hδU⟩ := hV.exists_thickening_subset_open hU hVU
  -- restriction to the compact set `K`
  let T : boundedHolomorphic U → (K →ᵇ ℂ) := fun f =>
    (f : U →ᵇ ℂ).compContinuous ⟨inclusion hVU, continuous_inclusion hVU⟩
  let A : Set (K →ᵇ ℂ) := T '' ball 0 1
  have in_s : ∀ (h : K →ᵇ ℂ) (x : K), h ∈ A → h x ∈ closedBall (0 : ℂ) 1 := by
    rintro _ x ⟨f, hf, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact ((f : U →ᵇ ℂ).norm_coe_le_norm _).trans (mem_ball_zero_iff.1 hf).le
  have equi : Equicontinuous ((↑) : A → K → ℂ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hη : 0 < min (δ / 2) (ε * δ / 4) := lt_min (half_pos hδ) (by positivity)
    filter_upwards [ball_mem_nhds x₀ hη] with x hx
    rintro ⟨_, f, hf, rfl⟩
    obtain ⟨g, hg, e⟩ := f.2
    have hball : ball (x₀ : ℂ) δ ⊆ U := (ball_subset_thickening x₀.2 δ).trans hδU
    have hxx : dist (x : ℂ) x₀ < min (δ / 2) (ε * δ / 4) := hx
    have key := norm_sub_le_of_differentiableOn_ball (C := 1) (hg.mono hball)
      (fun z hz => by
        have := ((f : U →ᵇ ℂ).norm_coe_le_norm ⟨z, hball hz⟩).trans (mem_ball_zero_iff.1 hf).le
        rwa [e] at this)
      (mem_ball.2 (hxx.trans_le (min_le_left _ _)))
    change dist ((f : U →ᵇ ℂ) (inclusion hVU x₀)) ((f : U →ᵇ ℂ) (inclusion hVU x)) < ε
    rw [dist_comm, dist_eq_norm, e, e]
    calc ‖g x - g x₀‖ ≤ 2 * 1 / δ * ‖(x : ℂ) - x₀‖ := key
      _ < 2 * 1 / δ * (ε * δ / 4) := by
          gcongr
          rw [← dist_eq_norm]
          exact hxx.trans_le (min_le_right _ _)
      _ = ε / 2 := by field_simp; ring
      _ < ε := half_lt_self hε
  have hA : IsCompact (closure A) :=
    arzela_ascoli (closedBall (0 : ℂ) 1) (isCompact_closedBall 0 1) A in_s equi
  -- restriction from `K` to `V`
  let R : (K →ᵇ ℂ) → (V →ᵇ ℂ) := fun h =>
    h.compContinuous ⟨inclusion subset_closure, continuous_inclusion subset_closure⟩
  have hR : Continuous R := (lipschitz_compContinuous _).continuous
  let K' : Set (V →ᵇ ℂ) := R '' closure A ∩ boundedHolomorphic V
  have hK' : IsCompact K' := (hA.image hR).inter_right (isClosed_boundedHolomorphic hVo)
  refine ⟨((↑) : boundedHolomorphic V → V →ᵇ ℂ) ⁻¹' K', ?_, ?_⟩
  · rw [Subtype.isCompact_iff, image_preimage_eq_of_subset]
    · exact hK'
    · exact fun h hh => ⟨⟨h, hh.2⟩, rfl⟩
  · filter_upwards [ball_mem_nhds (0 : boundedHolomorphic U) one_pos] with f hf
    exact ⟨⟨T f, subset_closure ⟨f, hf, rfl⟩, rfl⟩, (restrictL _ f).2⟩

/-- Restriction of bounded holomorphic functions from an open set `U` to a set `V` whose closure
is compact and contained in `U` is a compact operator. -/
theorem isCompactOperator_restrictL (hU : IsOpen U) (hV : IsCompact (closure V))
    (hVU : closure V ⊆ U) : IsCompactOperator (restrictL (subset_closure.trans hVU)) := by
  obtain ⟨δ, hδ, hδU⟩ := hV.exists_thickening_subset_open hU hVU
  set W := thickening (δ / 2) (closure V)
  have hWc : closure W ⊆ cthickening (δ / 2) (closure V) :=
    closure_thickening_subset_cthickening _ _
  have hWU : closure W ⊆ U :=
    hWc.trans ((cthickening_subset_thickening' hδ (half_lt_self hδ) _).trans hδU)
  have hVW : V ⊆ W := subset_closure.trans (self_subset_thickening (half_pos hδ) _)
  have h := isCompactOperator_restrictL_of_isOpen hU isOpen_thickening
    (hV.cthickening.of_isClosed_subset isClosed_closure hWc) hWU
  have := h.clm_comp (restrictL hVW)
  exact this

end boundedHolomorphic

end Complex
