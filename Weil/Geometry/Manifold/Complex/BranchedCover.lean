module

public import Weil.Geometry.Manifold.Complex.Meromorphic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Meromorphic functions on a compact Riemann surface are branched coverings

Let `M` be a compact Riemann surface and `t : M → ℂ` a meromorphic function in normal form which
is constant on no open set. Then `t`, viewed as a map to the Riemann sphere, is a finite branched
covering: outside a finite set `B ⊆ ℂ` of values, every value `b` has the same number `d` of
preimages at which `t` is holomorphic, and over a small disc around `b` the map `t` has `d`
continuous holomorphic sections whose images are exactly these preimages.

The proof is the classical one. At a point which is not a pole and where the derivative of `t`
(in a chart) does not vanish, the holomorphic inverse function theorem makes `t` a local
homeomorphism. The other points, poles and critical points, are isolated, hence finite in number
by compactness; `B` is the set of their values. For `b ∉ B`, the fibre of `b` is finite, and a
compactness argument (near a pole, `t` tends to infinity) shows that every holomorphic preimage
of a value close to `b` lies in one of finitely many disjoint neighbourhoods on which `t` is
injective. Hence the fibre cardinality is locally constant on the complement of `B`, which is
connected, so it is constant.

## Main definitions

* `RiemannSurface.regularFibre t b`: the points `x` where `t` is holomorphic and `t x = b`.
* `RiemannSurface.fibreDegree t`: the cardinality of `regularFibre t b` for all but finitely
  many `b`.
* `RiemannSurface.IsUnramifiedAt t x`: `t` is a holomorphic local homeomorphism near `x`.
* `RiemannSurface.branchValues t`: the values of `t` at the points where it is not unramified.

## Main results

* `RiemannSurface.isBranchedCover`: the local structure of `t` over the complement of a finite
  set of values.
* `RiemannSurface.fibreDegree_pos`: on a nonempty compact Riemann surface the degree is positive.
* `RiemannSurface.fibreDegree_add_fibreDegree_compl`: the degree is additive over a splitting of
  `M` into two clopen subsets.

## References

* [O. Forster, *Lectures on Riemann Surfaces*][forster1981], §4 and §8.
-/

@[expose] public section

open Manifold Set Filter Topology

namespace RiemannSurface

section Defs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The points at which `t` is holomorphic and takes the value `b`. -/
def regularFibre (t : M → ℂ) (b : ℂ) : Set M :=
  {x | MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t x ∧ t x = b}

open Classical in
/-- The number of points of `regularFibre t b` for all but finitely many `b` (and `0` if there
is no such number). -/
noncomputable def fibreDegree (t : M → ℂ) : ℕ :=
  if h : ∃ d : ℕ, ∀ᶠ b in cofinite, (regularFibre t b).ncard = d then h.choose else 0

theorem fibreDegree_eq_of_eventually {t : M → ℂ} {d : ℕ}
    (h : ∀ᶠ b in cofinite, (regularFibre t b).ncard = d) : fibreDegree t = d := by
  have hex : ∃ d : ℕ, ∀ᶠ b in cofinite, (regularFibre t b).ncard = d := ⟨d, h⟩
  simp only [fibreDegree, hex, ↓reduceDIte]
  obtain ⟨b, hb1, hb2⟩ := (hex.choose_spec.and h).exists
  exact hb1.symm.trans hb2

/-- `t` is unramified at `x`: it is a holomorphic local homeomorphism near `x`. -/
def IsUnramifiedAt (t : M → ℂ) (x : M) : Prop :=
  ∃ T : OpenPartialHomeomorph M ℂ, x ∈ T.source ∧ EqOn t T T.source ∧
    ∀ y ∈ T.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t y

/-- The branch values of `t`: its values at the points where it is not unramified. -/
def branchValues (t : M → ℂ) : Set ℂ :=
  t '' {x | ¬IsUnramifiedAt t x}

end Defs

/-- In a compact space, a set none of whose points accumulate anywhere is finite. -/
theorem finite_of_eventually_nhdsNE_notMem {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {S : Set X} (h : ∀ x, ∀ᶠ y in 𝓝[≠] x, y ∉ S) : S.Finite := by
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover (fun x => {x} ∪ Sᶜ) (fun x _ => by
    have := h x
    rw [eventually_nhdsWithin_iff] at this
    filter_upwards [this] with y hy
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr (hy hyx))
  refine s.finite_toSet.subset fun y hy => ?_
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hs (mem_univ y))
  rcases hyx with hyx | hyx
  · rw [mem_singleton_iff.1 hyx]; exact hx
  · exact absurd hy hyx

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]
  {t : M → ℂ}

section Local

/-- The holomorphic inverse function theorem on a Riemann surface: if `t` is analytic in a chart
at `x` with nonzero derivative, then `t` is unramified at `x`. -/
theorem isUnramifiedAt_of_mem_atlas {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    {x : M} (hx : x ∈ e.source) (han : AnalyticAt ℂ (t ∘ e.symm) (e x))
    (hd : deriv (t ∘ e.symm) (e x) ≠ 0) : IsUnramifiedAt t x := by
  set φ := t ∘ e.symm with hφ
  have hs := han.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  set h := hs.toOpenPartialHomeomorph φ with hh
  have hhcoe : (h : ℂ → ℂ) = φ := hs.toOpenPartialHomeomorph_coe
  let W : Set ℂ := e.target ∩ {z | AnalyticAt ℂ φ z}
  have hW : IsOpen W := e.open_target.inter (isOpen_analyticAt ℂ φ)
  have hsrc : ∀ y, y ∈ (e.trans (h.restrOpen W hW)).source ↔
      y ∈ e.source ∧ e y ∈ h.source ∧ e y ∈ e.target ∧ AnalyticAt ℂ φ (e y) := by
    intro y
    simp [W]
  refine ⟨e.trans (h.restrOpen W hW), ?_, ?_, ?_⟩
  · exact (hsrc x).2 ⟨hx, hs.mem_toOpenPartialHomeomorph_source, e.map_source hx, han⟩
  · intro y hy
    have hy' := (hsrc y).1 hy
    change t y = h (e y)
    rw [hhcoe, hφ, Function.comp_apply, e.left_inv hy'.1]
  · intro y hy
    have hy' := (hsrc y).1 hy
    exact (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he hy'.1).2
      hy'.2.2.2.differentiableAt

variable (ht : ∀ x, MeromorphicNFAt t x) (hnc : ∀ x (c : ℂ), orderAt (fun y => t y - c) x ≠ ⊤)
include ht


theorem mdifferentiableAt_iff_analyticAt_chart {x : M} :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t x ↔
      AnalyticAt ℂ (t ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
  set e := chartAt ℂ x
  constructor
  · intro hd
    have hdiff := (mdifferentiableAt_iff_differentiableAt_of_mem_atlas (chart_mem_atlas ℂ x)
      (mem_chart_source ℂ x)).1 hd
    rcases meromorphicNFAt_iff_analyticAt_or.1 (ht x) with h | ⟨-, hneg, -⟩
    · exact h
    · exfalso
      have h1 := tendsto_norm_atTop_iff_cobounded.2
        (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)
      have h2 : Tendsto (fun z => ‖(t ∘ e.symm) z‖) (𝓝[≠] (e x)) (𝓝 ‖(t ∘ e.symm) (e x)‖) :=
        (hdiff.continuousAt.norm).tendsto.mono_left nhdsWithin_le_nhds
      exact not_tendsto_atTop_of_tendsto_nhds h2 h1
  · intro han
    exact (eventually_mdifferentiableAt_of_analyticAt_comp_symm (chart_mem_atlas ℂ x)
      (mem_chart_source ℂ x) han).self_of_nhds

/-- Near a pole, `t` takes large values at the points where it is holomorphic. -/
theorem eventually_lt_norm_of_not_mdifferentiableAt {x : M}
    (hx : ¬MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t x) (R : ℝ) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t y → R < ‖t y‖ := by
  set e := chartAt ℂ x
  have hnan : ¬AnalyticAt ℂ (t ∘ e.symm) (e x) := fun h =>
    hx ((mdifferentiableAt_iff_analyticAt_chart ht).2 h)
  rcases meromorphicNFAt_iff_analyticAt_or.1 (ht x) with h | ⟨-, hneg, -⟩
  · exact absurd h hnan
  have h1 := (tendsto_norm_atTop_iff_cobounded.2
    (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)).eventually_gt_atTop R
  have h2 : ∀ᶠ y in 𝓝[≠] x, R < ‖t y‖ :=
    (eventually_nhdsNE_iff_of_mem_source e (mem_chart_source ℂ x)).2 h1
  rw [eventually_nhdsWithin_iff] at h2
  filter_upwards [h2] with y hy hyd
  exact hy (fun h => hx (h ▸ hyd))

include hnc

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- A locally nonconstant meromorphic function takes each value only at isolated points. -/
theorem eventually_ne (x : M) (b : ℂ) : ∀ᶠ y in 𝓝[≠] x, t y ≠ b := by
  have hm : MeromorphicAt (fun y => t y - b) x :=
    (ht x).meromorphicAt.sub (meromorphicAt_const b x)
  rcases hm.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (orderAt_eq_top_iff.2 h) (hnc x b)
  · filter_upwards [h] with y hy using sub_ne_zero.1 hy

/-- Points near which `t` fails to be unramified are isolated. -/
theorem eventually_isUnramifiedAt (x : M) : ∀ᶠ y in 𝓝[≠] x, IsUnramifiedAt t y := by
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
  exact isUnramifiedAt_of_mem_atlas (chart_mem_atlas ℂ x) (e.map_target hz3)
    (by rwa [e.right_inv hz3]) (by rwa [e.right_inv hz3])

variable [CompactSpace M]

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- On a compact Riemann surface, each value is taken only finitely often. -/
theorem finite_setOf_eq (b : ℂ) : {x | t x = b}.Finite :=
  finite_of_eventually_nhdsNE_notMem fun x => (eventually_ne ht hnc x b).mono fun _ hy => hy

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem finite_regularFibre (b : ℂ) : (regularFibre t b).Finite :=
  (finite_setOf_eq ht hnc b).subset fun _ hx => hx.2

/-- On a compact Riemann surface, `t` is unramified at all but finitely many points. -/
theorem finite_not_isUnramifiedAt : {x | ¬IsUnramifiedAt t x}.Finite :=
  finite_of_eventually_nhdsNE_notMem fun x =>
    (eventually_isUnramifiedAt ht hnc x).mono fun _ hy h => h hy

/-- On a compact Riemann surface, `t` has finitely many branch values. -/
theorem finite_branchValues : (branchValues t).Finite :=
  (finite_not_isUnramifiedAt ht hnc).image t

omit ht hnc [CompactSpace M] [IsManifold 𝓘(ℂ) 1 M] in
theorem isUnramifiedAt_of_mem_regularFibre {b : ℂ} (hb : b ∉ branchValues t) {x : M}
    (hx : x ∈ regularFibre t b) : IsUnramifiedAt t x := by
  by_contra h
  exact hb ⟨x, h, hx.2⟩

variable [T2Space M]

/-- Over a small disc around a value `b` all of whose holomorphic preimages are unramified, the
holomorphic preimages of every value are given by continuous sections of `t`, one through each
point of the fibre of `b`. -/
theorem exists_local_sections {b : ℂ} (hb : ∀ x ∈ regularFibre t b, IsUnramifiedAt t x) :
    ∃ r > 0, ∃ σ : regularFibre t b → ℂ → M,
      (∀ i, ∀ z ∈ Metric.ball b r, t (σ i z) = z ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t (σ i z)) ∧
      (∀ i, ContinuousOn (σ i) (Metric.ball b r)) ∧ (∀ i, σ i b = i) ∧
      ∀ z ∈ Metric.ball b r,
        regularFibre t z = Set.range (σ · z) ∧ Function.Injective (σ · z) := by
  set F := regularFibre t b with hFdef
  have hF : F.Finite := finite_regularFibre ht hnc b
  have : Finite F := hF.to_subtype
  obtain ⟨U, hU, hUd⟩ := hF.t2_separation
  choose T hTx hTt hTd using fun i : F => hb i i.2
  let T' : F → OpenPartialHomeomorph M ℂ := fun i => (T i).restrOpen (U i) (hU i).2
  have hT'src : ∀ i, (T' i).source = (T i).source ∩ U i := fun i =>
    OpenPartialHomeomorph.restrOpen_source _ _ _
  have hmemsrc : ∀ i y, y ∈ (T' i).source → y ∈ (T i).source ∧ y ∈ U i := fun i y hy => by
    rw [hT'src] at hy; exact hy
  have hT'eq : ∀ i, ∀ y ∈ (T' i).source, t y = T' i y := fun i y hy =>
    hTt i (hmemsrc i y hy).1
  have hxT' : ∀ i : F, (i : M) ∈ (T' i).source := fun i => by
    rw [hT'src]; exact ⟨hTx i, (hU i).1⟩
  have hTi : ∀ i : F, T' i i = b := fun i => by
    rw [← hT'eq i _ (hxT' i)]; exact i.2.2
  have hbT' : ∀ i : F, b ∈ (T' i).target := fun i => by
    rw [← hTi i]; exact (T' i).map_source (hxT' i)
  set O := ⋃ i, (T' i).source with hO
  have hOopen : IsOpen O := isOpen_iUnion fun i => (T' i).open_source
  have hloc : ∀ y : M, ∃ ρ : ℝ, 0 < ρ ∧ ∃ N ∈ 𝓝 y, ∀ y' ∈ N,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t y' → dist (t y') b < ρ → y' ∈ O := by
    intro y
    by_cases hyO : y ∈ O
    · exact ⟨1, one_pos, O, hOopen.mem_nhds hyO, fun y' hy' _ _ => hy'⟩
    by_cases hyd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t y
    · have hne : t y ≠ b := fun h => hyO (mem_iUnion.2 ⟨⟨y, hyd, h⟩, hxT' ⟨y, hyd, h⟩⟩)
      have hpos : 0 < dist (t y) b := dist_pos.2 hne
      refine ⟨dist (t y) b / 2, by positivity, t ⁻¹' Metric.ball (t y) (dist (t y) b / 2),
        hyd.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity)),
        fun y' hy' _ hlt => ?_⟩
      exfalso
      have h3 := dist_triangle (t y) (t y') b
      rw [mem_preimage, Metric.mem_ball, dist_comm] at hy'
      linarith
    · refine ⟨1, one_pos, _, eventually_lt_norm_of_not_mdifferentiableAt ht hyd (‖b‖ + 1),
        fun y' hy' hd hlt => ?_⟩
      exfalso
      have h3 := hy' hd
      have h4 := norm_sub_norm_le (t y') b
      rw [dist_eq_norm] at hlt
      linarith
  choose ρ hρ N hN hNO using hloc
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover N (fun y _ => hN y)
  have hr₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ ∀ y ∈ s, r < ρ y :=
    (show ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r from self_mem_nhdsWithin).and
      ((Finset.eventually_all s).2 fun y _ =>
      nhdsWithin_le_nhds (Iio_mem_nhds (hρ y)))
  obtain ⟨r₁, hr₁pos, hr₁ρ⟩ := hr₁.exists
  have hprop : ∀ y, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t y → dist (t y) b < r₁ → y ∈ O := by
    intro y hyd hlt
    obtain ⟨y₀, hy₀, hyN⟩ := mem_iUnion₂.1 (hs (mem_univ y))
    exact hNO y₀ y hyN hyd (hlt.trans (hr₁ρ y₀ hy₀))
  have hev : ∀ᶠ z in 𝓝 b, z ∈ Metric.ball b r₁ ∧ ∀ i, z ∈ (T' i).target :=
    (show ∀ᶠ z in 𝓝 b, z ∈ Metric.ball b r₁ from Metric.ball_mem_nhds b hr₁pos).and
      (eventually_all.2 fun i =>
      (T' i).open_target.mem_nhds (hbT' i))
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsrcT : ∀ i z, z ∈ Metric.ball b r → (T' i).symm z ∈ (T' i).source := fun i z hz =>
    (T' i).map_target ((hrb z hz).2 i)
  have htσ : ∀ i z, z ∈ Metric.ball b r → t ((T' i).symm z) = z := fun i z hz => by
    rw [hT'eq i _ (hsrcT i z hz), (T' i).right_inv ((hrb z hz).2 i)]
  refine ⟨r, hr, fun i z => (T' i).symm z,
    fun i z hz => ⟨htσ i z hz, hTd i _ (hmemsrc i _ (hsrcT i z hz)).1⟩,
    fun i => ((T' i).continuousOn_symm).mono fun z hz => (hrb z hz).2 i, fun i => ?_,
    fun z hz => ⟨?_, ?_⟩⟩
  · change (T' i).symm b = i
    rw [← hTi i, (T' i).left_inv (hxT' i)]
  · ext y
    constructor
    · rintro ⟨hyd, hyz⟩
      have hyO := hprop y hyd (by rw [hyz]; exact (hrb z hz).1)
      obtain ⟨i, hi⟩ := mem_iUnion.1 hyO
      refine ⟨i, ?_⟩
      change (T' i).symm z = y
      rw [← hyz, hT'eq i y hi, (T' i).left_inv hi]
    · rintro ⟨i, rfl⟩
      exact ⟨hTd i _ (hmemsrc i _ (hsrcT i z hz)).1, htσ i z hz⟩
  · intro i j hij
    by_contra hne
    have hne' : (i : M) ≠ j := fun h => hne (Subtype.ext h)
    have hi := (hmemsrc i _ (hsrcT i z hz)).2
    have hj := (hmemsrc j _ (hsrcT j z hz)).2
    change (T' i).symm z = (T' j).symm z at hij
    rw [hij] at hi
    exact Set.disjoint_left.1 (hUd i.2 j.2 hne') hi hj

/-- Off the branch values, the number of holomorphic preimages lying in a clopen set is locally
constant. -/
theorem eventually_ncard_regularFibre_inter_eq {A : Set M} (hA : IsClopen A) {b : ℂ}
    (hb : b ∉ branchValues t) :
    ∀ᶠ z in 𝓝 b, (regularFibre t z ∩ A).ncard = (regularFibre t b ∩ A).ncard := by
  obtain ⟨r, hr, σ, -, hσc, -, hσF⟩ := exists_local_sections ht hnc
    (fun x hx => isUnramifiedAt_of_mem_regularFibre hb hx)
  have hball : IsPreconnected (Metric.ball b r) := (convex_ball b r).isPreconnected
  have hbmem : b ∈ Metric.ball b r := Metric.mem_ball_self hr
  have hmem : ∀ i, ∀ z ∈ Metric.ball b r, (σ i z ∈ A ↔ σ i b ∈ A) := by
    intro i z hz
    have hpc : IsPreconnected (σ i '' Metric.ball b r) := hball.image _ (hσc i)
    constructor
    · intro hzA
      by_contra hbA
      exact hpc.subset_isClopen hA.compl ⟨σ i b, mem_image_of_mem _ hbmem, hbA⟩
        (mem_image_of_mem _ hz) hzA
    · intro hbA
      exact hpc.subset_isClopen hA ⟨σ i b, mem_image_of_mem _ hbmem, hbA⟩
        (mem_image_of_mem _ hz)
  have hcount : ∀ z ∈ Metric.ball b r,
      (regularFibre t z ∩ A).ncard = {i | σ i b ∈ A}.ncard := by
    intro z hz
    obtain ⟨hF, hinj⟩ := hσF z hz
    have : regularFibre t z ∩ A = (σ · z) '' {i | σ i b ∈ A} := by
      rw [hF]
      ext y
      constructor
      · rintro ⟨⟨i, rfl⟩, hyA⟩
        exact ⟨i, (hmem i z hz).1 hyA, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, rfl⟩, (hmem i z hz).2 hi⟩
    rw [this, ncard_image_of_injective _ hinj]
  filter_upwards [Metric.ball_mem_nhds b hr] with z hz
  rw [hcount z hz, hcount b hbmem]

/-- Off the branch values, the number of holomorphic preimages lying in a clopen set is
constant. -/
theorem exists_forall_ncard_regularFibre_inter_eq {A : Set M} (hA : IsClopen A) :
    ∃ d : ℕ, ∀ b ∉ branchValues t, (regularFibre t b ∩ A).ncard = d := by
  have hfin := finite_branchValues ht hnc
  obtain ⟨b₀, hb₀⟩ := hfin.infinite_compl.nonempty
  refine ⟨(regularFibre t b₀ ∩ A).ncard, fun b hb => ?_⟩
  have hpc : IsPreconnected (branchValues t)ᶜ :=
    (hfin.countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  refine hpc.constant (f := fun z => (regularFibre t z ∩ A).ncard) (fun z hz => ?_) hb hb₀
  exact (continuousAt_const.congr ((eventually_ncard_regularFibre_inter_eq ht hnc hA hz).mono
    fun w hw => hw.symm)).continuousWithinAt

/-- Off the branch values, the number of holomorphic preimages is `fibreDegree t`. -/
theorem ncard_regularFibre_eq_fibreDegree {b : ℂ} (hb : b ∉ branchValues t) :
    (regularFibre t b).ncard = fibreDegree t := by
  obtain ⟨d, hd⟩ := exists_forall_ncard_regularFibre_inter_eq ht hnc (A := univ) isClopen_univ
  simp only [inter_univ] at hd
  rw [hd b hb, fibreDegree_eq_of_eventually
    ((finite_branchValues ht hnc).eventually_cofinite_notMem.mono hd)]

/-- **A meromorphic function on a compact Riemann surface is a finite branched covering.**
Outside a finite set `B` of values, each value `b` has `fibreDegree t` holomorphic preimages, and
over a disc around `b` these are the values of `fibreDegree t` continuous holomorphic sections
of `t`. -/
theorem isBranchedCover :
    ∃ B : Finset ℂ, ∀ b ∉ B, (regularFibre t b).ncard = fibreDegree t ∧
      ∃ r > 0, ∃ σ : Fin (fibreDegree t) → ℂ → M,
        (∀ i, ∀ z ∈ Metric.ball b r, t (σ i z) = z ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) t (σ i z)) ∧
        (∀ i, ContinuousOn (σ i) (Metric.ball b r)) ∧
        (∀ z ∈ Metric.ball b r,
          regularFibre t z = Set.range (σ · z) ∧ Function.Injective (σ · z)) := by
  have hfin := finite_branchValues ht hnc
  refine ⟨hfin.toFinset, fun b hb => ?_⟩
  rw [Finite.mem_toFinset] at hb
  have hdeg := ncard_regularFibre_eq_fibreDegree ht hnc hb
  refine ⟨hdeg, ?_⟩
  obtain ⟨r, hr, σ, hσt, hσc, -, hσF⟩ := exists_local_sections ht hnc
    (fun x hx => isUnramifiedAt_of_mem_regularFibre hb hx)
  have : Finite (regularFibre t b) := (finite_regularFibre ht hnc b).to_subtype
  have hcard : Nat.card (regularFibre t b) = fibreDegree t := by
    rw [Nat.card_coe_set_eq, hdeg]
  let e := (Finite.equivFinOfCardEq hcard).symm
  refine ⟨r, hr, fun i => σ (e i), fun i => hσt (e i), fun i => hσc (e i), fun z hz => ⟨?_, ?_⟩⟩
  · rw [(hσF z hz).1]
    exact (e.surjective.range_comp (fun j => σ j z)).symm
  · exact (hσF z hz).2.comp e.injective

/-- On a nonempty compact Riemann surface, the degree of a locally nonconstant meromorphic
function is positive. -/
theorem fibreDegree_pos [Nonempty M] : 0 < fibreDegree t := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  have := nhdsNE_neBot x₀
  obtain ⟨x, T, hxT, hTt, hTd⟩ := (eventually_isUnramifiedAt ht hnc x₀).exists
  have hfin := finite_branchValues ht hnc
  have hcl : IsClosed (branchValues t \ {T x}) := (hfin.subset sdiff_subset).isClosed
  have hev : ∀ᶠ z in 𝓝[≠] (T x), z ∈ T.target ∧ z ∉ branchValues t := by
    refine (show ∀ᶠ z in 𝓝[≠] (T x), z ∈ T.target from
      nhdsWithin_le_nhds (T.open_target.mem_nhds (T.map_source hxT))).and ?_
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hcl.isOpen_compl.mem_nhds (by simp)] with z hz hzne hzB
    exact hz ⟨hzB, hzne⟩
  obtain ⟨z, hzT, hzB⟩ := hev.exists
  rw [← ncard_regularFibre_eq_fibreDegree ht hnc hzB]
  have hy : T.symm z ∈ regularFibre t z :=
    ⟨hTd _ (T.map_target hzT), by rw [hTt (T.map_target hzT), T.right_inv hzT]⟩
  exact (ncard_pos (finite_regularFibre ht hnc z)).2 ⟨_, hy⟩

end Local

section Subtype

variable (U : TopologicalSpace.Opens M)

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- Holomorphy on an open subset is holomorphy on the ambient surface. -/
theorem mdifferentiableAt_subtype_iff {f : M → ℂ} {x : U} :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y : U => f y) x ↔ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x :=
  (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val f x).symm

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem comp_subtype_val_comp_chartAt_symm_eventuallyEq (f : M → ℂ) (x : U) :
    (fun y : U => f y) ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (chartAt ℂ x x)]
      f ∘ (chartAt ℂ (x : M)).symm := by
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz
  have := (chartAt ℂ (x : M)).subtypeRestr_symm_eqOn ⟨x⟩ hz
  simp only [Function.comp_apply]
  rw [this]
  rfl

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- Meromorphy in normal form on an open subset is meromorphy in normal form on the ambient
surface. -/
theorem meromorphicNFAt_subtype_iff {f : M → ℂ} {x : U} :
    MeromorphicNFAt (fun y : U => f y) x ↔ MeromorphicNFAt f x := by
  unfold MeromorphicNFAt
  rw [meromorphicNFAt_congr (comp_subtype_val_comp_chartAt_symm_eventuallyEq U f x)]
  rfl

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- The order on an open subset is the order on the ambient surface. -/
theorem orderAt_subtype {f : M → ℂ} {x : U} : orderAt (fun y : U => f y) x = orderAt f x := by
  unfold orderAt
  rw [meromorphicOrderAt_congr
    ((comp_subtype_val_comp_chartAt_symm_eventuallyEq U f x).filter_mono nhdsWithin_le_nhds)]
  rfl

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem ncard_regularFibre_subtype (f : M → ℂ) (b : ℂ) :
    (regularFibre (fun y : U => f y) b).ncard = (regularFibre f b ∩ U).ncard := by
  have : regularFibre f b ∩ U = Subtype.val '' regularFibre (fun y : U => f y) b := by
    ext y
    constructor
    · rintro ⟨⟨hd, hy⟩, hU⟩
      exact ⟨⟨y, hU⟩, ⟨(mdifferentiableAt_subtype_iff U).2 hd, hy⟩, rfl⟩
    · rintro ⟨y, ⟨hd, hy⟩, rfl⟩
      exact ⟨⟨(mdifferentiableAt_subtype_iff U).1 hd, hy⟩, y.2⟩
  rw [this, ncard_image_of_injective _ Subtype.val_injective]

variable {U}
variable (ht : ∀ x, MeromorphicNFAt t x) (hnc : ∀ x (c : ℂ), orderAt (fun y => t y - c) x ≠ ⊤)
include ht hnc

/-- The degree of the restriction of `t` to a clopen subset is the eventual number of holomorphic
preimages in that subset. -/
theorem fibreDegree_subtype_eq [CompactSpace M] [T2Space M] (hU : IsClosed (U : Set M)) {b : ℂ}
    (hb : b ∉ branchValues t) :
    fibreDegree (fun y : U => t y) = (regularFibre t b ∩ U).ncard := by
  obtain ⟨d, hd⟩ := exists_forall_ncard_regularFibre_inter_eq ht hnc ⟨hU, U.isOpen⟩
  rw [hd b hb]
  exact fibreDegree_eq_of_eventually ((finite_branchValues ht hnc).eventually_cofinite_notMem.mono
    fun b' hb' => (ncard_regularFibre_subtype U t b').trans (hd b' hb'))

/-- The degree is additive over a splitting of the surface into two clopen subsets. -/
theorem fibreDegree_add_fibreDegree_compl [CompactSpace M] [T2Space M]
    (hU : IsClosed (U : Set M)) :
    fibreDegree (fun y : U => t y) +
      fibreDegree (fun y : (⟨(U : Set M)ᶜ, hU.isOpen_compl⟩ : TopologicalSpace.Opens M) => t y) =
      fibreDegree t := by
  obtain ⟨b, hb⟩ := (finite_branchValues ht hnc).infinite_compl.nonempty
  rw [fibreDegree_subtype_eq ht hnc hU hb,
    fibreDegree_subtype_eq (U := ⟨(U : Set M)ᶜ, hU.isOpen_compl⟩) ht hnc
      U.isOpen.isClosed_compl hb,
    ← ncard_regularFibre_eq_fibreDegree ht hnc hb]
  change (regularFibre t b ∩ U).ncard + (regularFibre t b ∩ (U : Set M)ᶜ).ncard = _
  rw [← sdiff_eq]
  exact ncard_inter_add_ncard_sdiff_eq_ncard _ _ (finite_regularFibre ht hnc b)

end Subtype

end RiemannSurface

end
