module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Topology.Connected.Clopen

/-!
# Meromorphic functions on a Riemann surface

Let `M` be a one-dimensional complex manifold, that is a topological space with an atlas of charts
to `ℂ` whose transition maps are holomorphic (`IsManifold 𝓘(ℂ) 1 M`; holomorphic transition maps
are automatically analytic). A function `f : M → ℂ` is *meromorphic at* `x` if `f ∘ φ⁻¹` is
meromorphic at `φ x` for the preferred chart `φ = chartAt ℂ x`, and its *order* at `x` is the
meromorphic order of `f ∘ φ⁻¹` at `φ x`. A transition map `ψ ∘ φ⁻¹` between two charts is
analytic with nowhere vanishing derivative, and both notions are invariant under composition
with such a map; hence they can be computed in any chart of the atlas.

From the one-variable theory one obtains, chart by chart: holomorphic functions are meromorphic
in normal form; meromorphic functions form a field-like algebra and the order is additive under
multiplication; the identity theorem (two meromorphic functions on a preconnected set which agree
near one point agree near every point); and the divisor of a meromorphic function on a set `U`,
a function `U → ℤ` with locally finite support.

Finally, a complex manifold is a real manifold of the same smoothness: holomorphic transition
maps are real smooth.

## Main definitions

* `RiemannSurface.MeromorphicAt f x`, `RiemannSurface.MeromorphicNFAt f x`,
  `RiemannSurface.MeromorphicOn f U`: meromorphy (in normal form) of `f : M → ℂ`, by charts.
* `RiemannSurface.orderAt f x : WithTop ℤ`: the order of `f` at `x`.
* `RiemannSurface.divisorOn f U : Function.locallyFinsuppWithin U ℤ`: the divisor of `f` on `U`.

## Main results

* `RiemannSurface.meromorphicAt_iff_of_mem_atlas`,
  `RiemannSurface.meromorphicNFAt_iff_of_mem_atlas`,
  `RiemannSurface.orderAt_eq_of_mem_atlas`: the notions may be computed in any chart.
* `RiemannSurface.mdifferentiableAt_iff_differentiableAt_of_mem_atlas`: holomorphy in charts.
* `RiemannSurface.meromorphicNFAt_of_eventually_mdifferentiableAt`,
  `RiemannSurface.meromorphicOn_of_mdifferentiableOn`: holomorphic functions are meromorphic.
* `RiemannSurface.orderAt_mul`, `RiemannSurface.orderAt_inv`, `RiemannSurface.orderAt_eq_top_iff`.
* `RiemannSurface.eventuallyEq_nhdsNE_of_isPreconnected`: the identity theorem.
* `RiemannSurface.divisorOn_apply`, `RiemannSurface.divisorOn_mul`, `RiemannSurface.divisorOn_inv`.
* `RiemannSurface.isManifold_real`: a complex manifold is a real manifold.

## Implementation notes

Meromorphy and order are defined with the preferred chart `chartAt ℂ x`, so that they are plain
propositions about functions on open subsets of `ℂ`, and every result of the one-variable theory
in `Mathlib.Analysis.Meromorphic` applies after `RiemannSurface.meromorphicAt_iff_of_mem_atlas`.
Functions are `ℂ`-valued and not quotiented by codiscrete equality; as in the one-variable
theory, a meromorphic function in the sense of function fields is a class of such functions, or
its normal form.

## References

* [O. Forster, *Lectures on Riemann Surfaces*][forster1981], §1–§2.
-/

@[expose] public section

open Manifold Set Filter Topology

namespace RiemannSurface

section Chart

/-- An open partial homeomorphism transports the punctured neighbourhood filter of a point of its
source to that of the image point. -/
theorem eventually_nhdsNE_iff_of_mem_source {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source)
    {P : X → Prop} :
    (∀ᶠ y in 𝓝[≠] x, P y) ↔ ∀ᶠ z in 𝓝[≠] (e x), P (e.symm z) := by
  have himg : e '' (e.source ∩ {x}ᶜ) = e.target ∩ {e x}ᶜ := by
    ext z
    constructor
    · rintro ⟨y, ⟨hy, hyx⟩, rfl⟩
      exact ⟨e.map_source hy, fun h => hyx (e.injOn hy hx h)⟩
    · rintro ⟨hz, hzx⟩
      refine ⟨e.symm z, ⟨e.map_target hz, fun h => hzx ?_⟩, e.right_inv hz⟩
      rw [mem_singleton_iff] at h ⊢
      rw [← h, e.right_inv hz]
  have hmap : map e (𝓝[≠] x) = 𝓝[≠] (e x) := by
    rw [e.map_nhdsWithin_eq hx, himg, nhdsWithin_inter_of_mem]
    exact mem_nhdsWithin_of_mem_nhds (e.open_target.mem_nhds (e.map_source hx))
  have hsrc : ∀ᶠ y in 𝓝[≠] x, y ∈ e.source :=
    mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds hx)
  rw [← hmap, eventually_map]
  constructor
  · intro h
    filter_upwards [h, hsrc] with y hy hy' using by rwa [e.left_inv hy']
  · intro h
    filter_upwards [h, hsrc] with y hy hy' using by rwa [e.left_inv hy'] at hy

variable {M : Type*} [TopologicalSpace M]

/-- The source of a transition map is a neighbourhood of the image of a common point. -/
theorem transition_source_mem_nhds {e e' : OpenPartialHomeomorph M ℂ} {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (e'.symm.trans e).source ∈ 𝓝 (e' x) :=
  (e'.symm.trans e).open_source.mem_nhds (by simp [hx, hx', e'.map_source hx'])

theorem transition_apply {e e' : OpenPartialHomeomorph M ℂ} {x : M} (hx' : x ∈ e'.source) :
    (e ∘ e'.symm) (e' x) = e x := by
  simp [e'.left_inv hx']

/-- Near a common point, `f` read in the chart `e'` is `f` read in the chart `e`, composed with
the transition map. -/
theorem comp_symm_eventuallyEq {e e' : OpenPartialHomeomorph M ℂ} {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) {E : Type*} (f : M → E) :
    f ∘ e'.symm =ᶠ[𝓝 (e' x)] (f ∘ e.symm) ∘ (e ∘ e'.symm) := by
  filter_upwards [transition_source_mem_nhds hx hx'] with z hz
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    mem_inter_iff, mem_preimage] at hz
  simp [e.left_inv hz.2]

variable [ChartedSpace ℂ M]

/-- A space with charts to `ℂ` has no isolated points. -/
theorem nhdsNE_neBot (x : M) : (𝓝[≠] x).NeBot := by
  rw [neBot_iff, Ne, ← eventually_false_iff_eq_bot,
    eventually_nhdsNE_iff_of_mem_source (chartAt ℂ x) (mem_chart_source ℂ x),
    eventually_false_iff_eq_bot]
  exact NeBot.ne inferInstance

variable [IsManifold 𝓘(ℂ) 1 M]

/-- Transition maps of a complex manifold are holomorphic on their source. -/
theorem contDiffOn_transition {e e' : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (he' : e' ∈ atlas ℂ M) :
    ContDiffOn ℂ 1 (e ∘ e'.symm) (e'.symm.trans e).source := by
  have h := HasGroupoid.compatible (G := contDiffGroupoid 1 𝓘(ℂ)) he' he
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  simpa [contDiffPregroupoid] using h.1

theorem analyticAt_transition {e e' : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (he' : e' ∈ atlas ℂ M) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    AnalyticAt ℂ (e ∘ e'.symm) (e' x) :=
  ((contDiffOn_transition he he').differentiableOn one_ne_zero).analyticAt
    (transition_source_mem_nhds hx hx')

/-- The derivative of a transition map does not vanish. -/
theorem deriv_transition_ne_zero {e e' : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (he' : e' ∈ atlas ℂ M) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    deriv (e ∘ e'.symm) (e' x) ≠ 0 := by
  have h1 := (analyticAt_transition he he' hx hx').differentiableAt.hasDerivAt
  have h2 := (analyticAt_transition he' he hx' hx).differentiableAt.hasDerivAt
  rw [← transition_apply (e := e) hx'] at h2
  have h3 := h2.comp (e' x) h1
  have h4 : (e' ∘ e.symm) ∘ (e ∘ e'.symm) =ᶠ[𝓝 (e' x)] id := by
    filter_upwards [transition_source_mem_nhds hx hx'] with z hz
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage] at hz
    simp [e.left_inv hz.2, e'.right_inv hz.1]
  have h6 := h3.unique ((hasDerivAt_id (e' x)).congr_of_eventuallyEq h4)
  intro h
  rw [h, mul_zero] at h6
  exact zero_ne_one h6

end Chart

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- `f : M → ℂ` is meromorphic at `x` if it is meromorphic at `x` in the preferred chart. -/
def MeromorphicAt (f : M → ℂ) (x : M) : Prop :=
  _root_.MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- `f : M → ℂ` is meromorphic in normal form at `x` if it is so in the preferred chart. -/
def MeromorphicNFAt (f : M → ℂ) (x : M) : Prop :=
  _root_.MeromorphicNFAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- `f : M → ℂ` is meromorphic on `U` if it is meromorphic at every point of `U`. -/
def MeromorphicOn (f : M → ℂ) (U : Set M) : Prop :=
  ∀ x ∈ U, MeromorphicAt f x

/-- The order of `f : M → ℂ` at `x`: the meromorphic order in the preferred chart. It is `⊤` if
`f` vanishes on a punctured neighbourhood of `x`, and `0` if `f` is not meromorphic at `x`. -/
noncomputable def orderAt (f : M → ℂ) (x : M) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

variable {f g : M → ℂ} {x : M} {U : Set M}

section Algebra

/-! The algebraic operations need no compatibility of charts. -/

theorem MeromorphicAt.add (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x :=
  _root_.MeromorphicAt.add hf hg

theorem MeromorphicAt.sub (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x :=
  _root_.MeromorphicAt.sub hf hg

theorem MeromorphicAt.neg (hf : MeromorphicAt f x) : MeromorphicAt (-f) x :=
  _root_.MeromorphicAt.neg hf

theorem MeromorphicAt.mul (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f * g) x :=
  _root_.MeromorphicAt.mul hf hg

theorem MeromorphicAt.inv (hf : MeromorphicAt f x) : MeromorphicAt f⁻¹ x :=
  _root_.MeromorphicAt.inv hf

theorem MeromorphicAt.div (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f / g) x :=
  _root_.MeromorphicAt.div hf hg

theorem MeromorphicAt.pow (hf : MeromorphicAt f x) (n : ℕ) : MeromorphicAt (f ^ n) x :=
  _root_.MeromorphicAt.pow hf n

theorem MeromorphicAt.zpow (hf : MeromorphicAt f x) (n : ℤ) : MeromorphicAt (f ^ n) x :=
  _root_.MeromorphicAt.zpow hf n

theorem meromorphicAt_const (c : ℂ) (x : M) : MeromorphicAt (fun _ => c) x :=
  _root_.MeromorphicAt.const c _

theorem MeromorphicOn.add (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    MeromorphicOn (f + g) U := fun x hx => (hf x hx).add (hg x hx)

theorem MeromorphicOn.sub (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    MeromorphicOn (f - g) U := fun x hx => (hf x hx).sub (hg x hx)

theorem MeromorphicOn.neg (hf : MeromorphicOn f U) : MeromorphicOn (-f) U :=
  fun x hx => (hf x hx).neg

theorem MeromorphicOn.mul (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    MeromorphicOn (f * g) U := fun x hx => (hf x hx).mul (hg x hx)

theorem MeromorphicOn.inv (hf : MeromorphicOn f U) : MeromorphicOn f⁻¹ U :=
  fun x hx => (hf x hx).inv

theorem MeromorphicOn.div (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    MeromorphicOn (f / g) U := fun x hx => (hf x hx).div (hg x hx)

theorem MeromorphicOn.pow (hf : MeromorphicOn f U) (n : ℕ) : MeromorphicOn (f ^ n) U :=
  fun x hx => (hf x hx).pow n

theorem MeromorphicOn.zpow (hf : MeromorphicOn f U) (n : ℤ) : MeromorphicOn (f ^ n) U :=
  fun x hx => (hf x hx).zpow n

theorem meromorphicOn_const (c : ℂ) (U : Set M) : MeromorphicOn (fun _ => c) U :=
  fun x _ => meromorphicAt_const c x

theorem MeromorphicOn.mono {V : Set M} (hf : MeromorphicOn f U) (hVU : V ⊆ U) :
    MeromorphicOn f V := fun x hx => hf x (hVU hx)

theorem MeromorphicNFAt.meromorphicAt (hf : MeromorphicNFAt f x) : MeromorphicAt f x :=
  _root_.MeromorphicNFAt.meromorphicAt hf

theorem orderAt_mul (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    orderAt (f * g) x = orderAt f x + orderAt g x :=
  meromorphicOrderAt_mul hf hg

theorem orderAt_inv : orderAt f⁻¹ x = -orderAt f x :=
  meromorphicOrderAt_inv

theorem orderAt_pow (hf : MeromorphicAt f x) (n : ℕ) : orderAt (f ^ n) x = n * orderAt f x :=
  meromorphicOrderAt_pow (n := n) hf

theorem orderAt_of_not_meromorphicAt (hf : ¬MeromorphicAt f x) : orderAt f x = 0 :=
  meromorphicOrderAt_of_not_meromorphicAt hf

theorem MeromorphicAt.congr (hf : MeromorphicAt f x) (h : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x := by
  have h' : f ∘ (chartAt ℂ x).symm =ᶠ[𝓝[≠] (chartAt ℂ x x)] g ∘ (chartAt ℂ x).symm :=
    (eventually_nhdsNE_iff_of_mem_source (chartAt ℂ x) (mem_chart_source ℂ x)
      (P := fun y => f y = g y)).1 h
  exact _root_.MeromorphicAt.congr hf h'

theorem orderAt_congr (h : f =ᶠ[𝓝[≠] x] g) : orderAt f x = orderAt g x :=
  meromorphicOrderAt_congr
    ((eventually_nhdsNE_iff_of_mem_source (chartAt ℂ x) (mem_chart_source ℂ x)
      (P := fun y => f y = g y)).1 h)

/-- The order is `⊤` iff `f` vanishes on a punctured neighbourhood. -/
theorem orderAt_eq_top_iff : orderAt f x = ⊤ ↔ ∀ᶠ y in 𝓝[≠] x, f y = 0 := by
  rw [orderAt, meromorphicOrderAt_eq_top_iff]
  exact (eventually_nhdsNE_iff_of_mem_source (chartAt ℂ x) (mem_chart_source ℂ x)
    (P := fun y => f y = 0)).symm

/-- A meromorphic function vanishes on a punctured neighbourhood of a point or on none of its
points near it. -/
theorem MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero (hf : MeromorphicAt f x) :
    (∀ᶠ y in 𝓝[≠] x, f y = 0) ∨ (∀ᶠ y in 𝓝[≠] x, f y ≠ 0) := by
  rw [eventually_nhdsNE_iff_of_mem_source (chartAt ℂ x) (mem_chart_source ℂ x)
      (P := fun y => f y = 0),
    eventually_nhdsNE_iff_of_mem_source (chartAt ℂ x) (mem_chart_source ℂ x)
      (P := fun y => f y ≠ 0)]
  exact _root_.MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero hf

/-- Isolated zeros: a meromorphic function with zeros accumulating at `x` vanishes near `x`. -/
theorem MeromorphicAt.frequently_zero_iff_eventually_zero (hf : MeromorphicAt f x) :
    (∃ᶠ y in 𝓝[≠] x, f y = 0) ↔ ∀ᶠ y in 𝓝[≠] x, f y = 0 := by
  have := nhdsNE_neBot x
  refine ⟨fun h => ?_, fun h => h.frequently⟩
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h' | h'
  · exact h'
  · exact absurd h' (by simpa [Filter.not_eventually] using h)

end Algebra

section Atlas

variable [IsManifold 𝓘(ℂ) 1 M] {e : OpenPartialHomeomorph M ℂ}

theorem meromorphicAt_comp_symm_iff {e' : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (he' : e' ∈ atlas ℂ M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    _root_.MeromorphicAt (f ∘ e'.symm) (e' x) ↔ _root_.MeromorphicAt (f ∘ e.symm) (e x) := by
  rw [_root_.MeromorphicAt.meromorphicAt_congr
      ((comp_symm_eventuallyEq hx hx' f).filter_mono nhdsWithin_le_nhds),
    meromorphicAt_comp_iff_of_deriv_ne_zero (analyticAt_transition he he' hx hx')
      (deriv_transition_ne_zero he he' hx hx'), transition_apply hx']

theorem meromorphicNFAt_comp_symm_iff {e' : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (he' : e' ∈ atlas ℂ M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    _root_.MeromorphicNFAt (f ∘ e'.symm) (e' x) ↔ _root_.MeromorphicNFAt (f ∘ e.symm) (e x) := by
  rw [meromorphicNFAt_congr (comp_symm_eventuallyEq hx hx' f),
    meromorphicNFAt_comp_iff_of_deriv_ne_zero (analyticAt_transition he he' hx hx')
      (deriv_transition_ne_zero he he' hx hx'), transition_apply hx']

theorem meromorphicOrderAt_comp_symm_eq {e' : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (he' : e' ∈ atlas ℂ M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    meromorphicOrderAt (f ∘ e'.symm) (e' x) = meromorphicOrderAt (f ∘ e.symm) (e x) := by
  rw [meromorphicOrderAt_congr ((comp_symm_eventuallyEq hx hx' f).filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_comp_of_deriv_ne_zero (analyticAt_transition he he' hx hx')
      (deriv_transition_ne_zero he he' hx hx'), transition_apply hx']

/-- Meromorphy may be checked in any chart of the atlas. -/
theorem meromorphicAt_iff_of_mem_atlas (he : e ∈ atlas ℂ M) (hx : x ∈ e.source) :
    MeromorphicAt f x ↔ _root_.MeromorphicAt (f ∘ e.symm) (e x) :=
  meromorphicAt_comp_symm_iff he (chart_mem_atlas ℂ x) hx (mem_chart_source ℂ x)

/-- Meromorphy in normal form may be checked in any chart of the atlas. -/
theorem meromorphicNFAt_iff_of_mem_atlas (he : e ∈ atlas ℂ M) (hx : x ∈ e.source) :
    MeromorphicNFAt f x ↔ _root_.MeromorphicNFAt (f ∘ e.symm) (e x) :=
  meromorphicNFAt_comp_symm_iff he (chart_mem_atlas ℂ x) hx (mem_chart_source ℂ x)

/-- The order may be computed in any chart of the atlas. -/
theorem orderAt_eq_of_mem_atlas (he : e ∈ atlas ℂ M) (hx : x ∈ e.source) :
    orderAt f x = meromorphicOrderAt (f ∘ e.symm) (e x) :=
  meromorphicOrderAt_comp_symm_eq he (chart_mem_atlas ℂ x) hx (mem_chart_source ℂ x)

/-- `f` is meromorphic on `U` iff, in a chart `e`, `f ∘ e.symm` is meromorphic on the image of
`U ∩ e.source`. -/
theorem meromorphicOn_comp_symm (he : e ∈ atlas ℂ M) (hf : MeromorphicOn f U) :
    _root_.MeromorphicOn (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) := by
  intro z hz
  have h := (meromorphicAt_iff_of_mem_atlas he (e.map_target hz.1)).1 (hf _ hz.2)
  rwa [e.right_inv hz.1] at h

/-- Holomorphy of a `ℂ`-valued function may be checked in any chart of the atlas. -/
theorem mdifferentiableAt_iff_differentiableAt_of_mem_atlas (he : e ∈ atlas ℂ M)
    (hx : x ∈ e.source) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x ↔ DifferentiableAt ℂ (f ∘ e.symm) (e x) := by
  constructor
  · intro hf
    rw [← e.left_inv hx] at hf
    exact (hf.comp (e x) (mdifferentiableAt_atlas_symm he (e.map_source hx))).differentiableAt
  · intro hf
    have h := (hf.mdifferentiableAt).comp x (mdifferentiableAt_atlas he hx)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]

/-- A function holomorphic near `x` is analytic at `x` in every chart. -/
theorem analyticAt_comp_symm_of_eventually_mdifferentiableAt (he : e ∈ atlas ℂ M)
    (hx : x ∈ e.source) (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    AnalyticAt ℂ (f ∘ e.symm) (e x) := by
  have hcont : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have := e.continuousAt_symm (e.map_source hx)
    rwa [ContinuousAt, e.left_inv hx] at this
  have hev : ∀ᶠ z in 𝓝 (e x), DifferentiableAt ℂ (f ∘ e.symm) z := by
    filter_upwards [hcont.eventually hf, e.open_target.mem_nhds (e.map_source hx)] with z hz hzt
    have := (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he (e.map_target hzt)).1 hz
    rwa [e.right_inv hzt] at this
  exact DifferentiableOn.analyticAt (s := {z | DifferentiableAt ℂ (f ∘ e.symm) z})
    (fun z hz => DifferentiableAt.differentiableWithinAt hz) hev

/-- A function analytic in a chart at `e x` is holomorphic near `x`. -/
theorem eventually_mdifferentiableAt_of_analyticAt_comp_symm (he : e ∈ atlas ℂ M)
    (hx : x ∈ e.source) (hf : AnalyticAt ℂ (f ∘ e.symm) (e x)) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y := by
  have hcont : Tendsto e (𝓝 x) (𝓝 (e x)) := e.continuousAt hx
  filter_upwards [hcont.eventually hf.eventually_analyticAt, e.open_source.mem_nhds hx]
    with y hy hys
  exact (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he hys).2 hy.differentiableAt

/-- Holomorphy near `x` is analyticity in a chart. -/
theorem eventually_mdifferentiableAt_iff_analyticAt (he : e ∈ atlas ℂ M) (hx : x ∈ e.source) :
    (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) ↔ AnalyticAt ℂ (f ∘ e.symm) (e x) :=
  ⟨analyticAt_comp_symm_of_eventually_mdifferentiableAt he hx,
    eventually_mdifferentiableAt_of_analyticAt_comp_symm he hx⟩

/-- A function holomorphic near `x` is meromorphic in normal form at `x`. -/
theorem meromorphicNFAt_of_eventually_mdifferentiableAt
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) : MeromorphicNFAt f x :=
  (analyticAt_comp_symm_of_eventually_mdifferentiableAt (chart_mem_atlas ℂ x)
    (mem_chart_source ℂ x) hf).meromorphicNFAt

/-- A function holomorphic near `x` is meromorphic at `x`. -/
theorem meromorphicAt_of_eventually_mdifferentiableAt
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) : MeromorphicAt f x :=
  (meromorphicNFAt_of_eventually_mdifferentiableAt hf).meromorphicAt

/-- A function holomorphic near `x` has nonnegative order at `x`. -/
theorem orderAt_nonneg_of_eventually_mdifferentiableAt
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) : 0 ≤ orderAt f x :=
  (meromorphicNFAt_of_eventually_mdifferentiableAt hf).meromorphicOrderAt_nonneg_iff_analyticAt.2
    (analyticAt_comp_symm_of_eventually_mdifferentiableAt (chart_mem_atlas ℂ x)
      (mem_chart_source ℂ x) hf)

/-- A function holomorphic on an open set is meromorphic there. -/
theorem meromorphicOn_of_mdifferentiableOn (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U)
    (hU : IsOpen U) : MeromorphicOn f U := fun _ hx =>
  meromorphicAt_of_eventually_mdifferentiableAt
    (eventually_of_mem (hU.mem_nhds hx) fun y hy => (hf y hy).mdifferentiableAt (hU.mem_nhds hy))

/-- A holomorphic function is meromorphic everywhere. -/
theorem meromorphicOn_of_mdifferentiable (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (U : Set M) :
    MeromorphicOn f U := fun _ _ =>
  meromorphicAt_of_eventually_mdifferentiableAt (Eventually.of_forall hf)

end Atlas

section Identity

variable [T1Space M]

/-- Near a point where `f` is meromorphic, the property "`f` vanishes on a punctured
neighbourhood" is locally constant. -/
theorem MeromorphicAt.eventually_eventually_eq_zero_iff (hf : MeromorphicAt f x) :
    ∀ᶠ y in 𝓝 x, ((∀ᶠ w in 𝓝[≠] y, f w = 0) ↔ ∀ᶠ w in 𝓝[≠] x, f w = 0) := by
  -- an open neighbourhood `W` of `x` on which `P` holds off `x` gives `P` near every `y ≠ x`
  have key : ∀ {P : M → Prop}, (∀ᶠ w in 𝓝[≠] x, P w) →
      ∀ᶠ y in 𝓝 x, y ≠ x → ∀ᶠ w in 𝓝 y, P w := by
    intro P hP
    obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hP)
    filter_upwards [hWo.mem_nhds hxW] with y hy hyx
    filter_upwards [(hWo.inter isOpen_compl_singleton).mem_nhds ⟨hy, hyx⟩] with w hw
    exact hW w hw.1 hw.2
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with h | h
  · filter_upwards [key h] with y hy
    refine iff_of_true ?_ h
    by_cases hyx : y = x
    · rwa [hyx]
    · exact nhdsWithin_le_nhds (hy hyx)
  · have hnot : ¬∀ᶠ w in 𝓝[≠] x, f w = 0 := fun h' =>
      haveI := nhdsNE_neBot x
      (h'.and h).exists.elim fun w hw => hw.2 hw.1
    filter_upwards [key h] with y hy
    refine iff_of_false ?_ hnot
    by_cases hyx : y = x
    · rwa [hyx]
    · intro h'
      have := nhdsNE_neBot y
      exact (h'.and (nhdsWithin_le_nhds (hy hyx))).exists.elim fun w hw => hw.2 hw.1

/-- **Identity theorem.** Two functions meromorphic on a preconnected set `U` which agree on a
punctured neighbourhood of one point of `U` agree on a punctured neighbourhood of every point of
`U`. -/
theorem eventuallyEq_nhdsNE_of_isPreconnected (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsPreconnected U) {x₀ : M} (hx₀ : x₀ ∈ U) (h : f =ᶠ[𝓝[≠] x₀] g) {x : M} (hx : x ∈ U) :
    f =ᶠ[𝓝[≠] x] g := by
  have hfg : MeromorphicOn (f - g) U := hf.sub hg
  let Q : M → Prop := fun y => ∀ᶠ w in 𝓝[≠] y, (f - g) w = 0
  have hQ : ∀ y, Q y ↔ f =ᶠ[𝓝[≠] y] g := fun y => by
    simp only [Q, Pi.sub_apply, sub_eq_zero]
    rfl
  have hiff : Q x₀ ↔ Q x := by
    refine hU.induction₂ (fun a b => Q a ↔ Q b) (fun a ha => ?_)
      (fun a b c _ _ _ hab hbc => hab.trans hbc) (fun a b _ _ hab => hab.symm) hx₀ hx
    filter_upwards [nhdsWithin_le_nhds ((hfg a ha).eventually_eventually_eq_zero_iff)] with b hb
    exact hb.symm
  exact (hQ x).1 (hiff.1 ((hQ x₀).2 h))

/-- **Identity theorem**, codiscrete form: two functions meromorphic on a preconnected set `U`
which agree on a punctured neighbourhood of one point of `U` agree on `U` off a set which is
discrete in `U`. -/
theorem eventuallyEq_codiscreteWithin_of_isPreconnected (hf : MeromorphicOn f U)
    (hg : MeromorphicOn g U) (hU : IsPreconnected U) {x₀ : M} (hx₀ : x₀ ∈ U)
    (h : f =ᶠ[𝓝[≠] x₀] g) : f =ᶠ[codiscreteWithin U] g := by
  rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  filter_upwards [eventuallyEq_nhdsNE_of_isPreconnected hf hg hU hx₀ h hx] with y hy
  simp [hy]

/-- Two functions meromorphic on a preconnected set `U` which agree at points accumulating at a
point of `U` agree on a punctured neighbourhood of every point of `U`. -/
theorem eventuallyEq_nhdsNE_of_frequently_eq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hU : IsPreconnected U) {x₀ : M} (hx₀ : x₀ ∈ U) (h : ∃ᶠ y in 𝓝[≠] x₀, f y = g y) {x : M}
    (hx : x ∈ U) : f =ᶠ[𝓝[≠] x] g := by
  refine eventuallyEq_nhdsNE_of_isPreconnected hf hg hU hx₀ ?_ hx
  have h' : ∃ᶠ y in 𝓝[≠] x₀, (f - g) y = 0 := h.mono fun y hy => by simp [hy]
  filter_upwards [((hf.sub hg) x₀ hx₀).frequently_zero_iff_eventually_zero.1 h'] with y hy
  exact sub_eq_zero.1 hy

end Identity

section Divisor

variable [IsManifold 𝓘(ℂ) 1 M]

/-- In a chart `e`, the order of `f` at a point of `U ∩ e.source` is read off the divisor of
`f ∘ e.symm` on the image of `U`. -/
theorem untop₀_orderAt_eq_divisor {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (hf : MeromorphicOn f U) {y : M} (hyU : y ∈ U) (hy : y ∈ e.source) :
    (orderAt f y).untop₀ =
      _root_.MeromorphicOn.divisor (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) (e y) := by
  rw [MeromorphicOn.divisor_apply (meromorphicOn_comp_symm he hf)
    ⟨e.map_source hy, by simpa [e.left_inv hy] using hyU⟩, orderAt_eq_of_mem_atlas he hy]

open scoped Classical in
/-- The divisor of `f` on `U`: the function sending `x ∈ U` to the order of `f` at `x` (`0` where
the order is infinite), and everything to `0` if `f` is not meromorphic on `U`. Its support is
locally finite in `U`. -/
noncomputable def divisorOn (f : M → ℂ) (U : Set M) : Function.locallyFinsuppWithin U ℤ where
  toFun := fun x => if MeromorphicOn f U ∧ x ∈ U then (orderAt f x).untop₀ else 0
  supportWithinDomain' x hx := by
    by_contra h
    simp [h] at hx
  supportLocallyFiniteWithinDomain' z hz := by
    by_cases hf : MeromorphicOn f U
    swap
    · exact ⟨univ, univ_mem, by simp [hf]⟩
    set e := chartAt ℂ z
    have he : e ∈ atlas ℂ M := chart_mem_atlas ℂ z
    have hzs : z ∈ e.source := mem_chart_source ℂ z
    set D := _root_.MeromorphicOn.divisor (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' U)
    obtain ⟨t, ht, htf⟩ := D.supportLocallyFiniteWithinDomain' (e z)
      ⟨e.map_source hzs, by simpa [e.left_inv hzs] using hz⟩
    refine ⟨e.source ∩ e ⁻¹' t, inter_mem (e.open_source.mem_nhds hzs)
      (e.continuousAt hzs ht), (htf.image e.symm).subset ?_⟩
    rintro y ⟨⟨hys, hyt⟩, hy⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hy
    refine ⟨e y, ⟨hyt, ?_⟩, e.left_inv hys⟩
    change D (e y) ≠ 0
    rw [← untop₀_orderAt_eq_divisor he hf hy.1.2 hys]
    exact hy.2

open scoped Classical in
theorem divisorOn_def (f : M → ℂ) (U : Set M) (x : M) :
    divisorOn f U x = if MeromorphicOn f U ∧ x ∈ U then (orderAt f x).untop₀ else 0 :=
  rfl

@[simp]
theorem divisorOn_apply (hf : MeromorphicOn f U) (hx : x ∈ U) :
    divisorOn f U x = (orderAt f x).untop₀ := by
  simp [divisorOn_def, hf, hx]

theorem divisorOn_of_not_meromorphicOn (hf : ¬MeromorphicOn f U) : divisorOn f U = 0 := by
  ext x
  simp [divisorOn_def, hf]

theorem divisorOn_apply_of_notMem (hx : x ∉ U) : divisorOn f U x = 0 := by
  simp [hx]

/-- In a chart, the divisor of `f` is the divisor of `f` read in the chart. -/
theorem divisorOn_eq_divisor_comp_symm {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    (hf : MeromorphicOn f U) {y : M} (hy : y ∈ e.source) :
    divisorOn f U y =
      _root_.MeromorphicOn.divisor (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) (e y) := by
  by_cases hyU : y ∈ U
  · rw [divisorOn_apply hf hyU, untop₀_orderAt_eq_divisor he hf hyU hy]
  · rw [divisorOn_apply_of_notMem hyU, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem]
    rintro ⟨-, h⟩
    exact hyU (by simpa [e.left_inv hy] using h)

/-- The divisor of a product is the sum of the divisors, for functions vanishing identically near
no point of `U`. -/
theorem divisorOn_mul (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hf' : ∀ x ∈ U, orderAt f x ≠ ⊤) (hg' : ∀ x ∈ U, orderAt g x ≠ ⊤) :
    divisorOn (f * g) U = divisorOn f U + divisorOn g U := by
  ext x
  by_cases hx : x ∈ U
  · simp only [divisorOn_apply (hf.mul hg) hx, Function.locallyFinsuppWithin.coe_add,
      Pi.add_apply, divisorOn_apply hf hx, divisorOn_apply hg hx, orderAt_mul (hf x hx) (hg x hx)]
    exact WithTop.untop₀_add (hf' x hx) (hg' x hx)
  · simp [divisorOn_apply_of_notMem hx]

/-- The divisor of the inverse is the negative of the divisor. -/
theorem divisorOn_inv : divisorOn f⁻¹ U = -divisorOn f U := by
  ext x
  by_cases hf : MeromorphicOn f U
  · by_cases hx : x ∈ U
    · simp [divisorOn_apply hf.inv hx, divisorOn_apply hf hx, orderAt_inv]
    · simp [divisorOn_apply_of_notMem hx]
  · have hf' : ¬MeromorphicOn f⁻¹ U := fun h => hf (by simpa using h.inv)
    simp [divisorOn_of_not_meromorphicOn hf, divisorOn_of_not_meromorphicOn hf']

end Divisor

section RealManifold

/-- A complex manifold is a real manifold of the same smoothness: holomorphic transition maps
are real smooth. -/
theorem isManifold_real {n : WithTop ℕ∞} [IsManifold 𝓘(ℂ) n M] : IsManifold 𝓘(ℝ, ℂ) n M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have h := HasGroupoid.compatible (G := contDiffGroupoid n 𝓘(ℂ)) he he'
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  simpa [contDiffPregroupoid] using h.1.restrict_scalars ℝ

end RealManifold

end RiemannSurface

end
