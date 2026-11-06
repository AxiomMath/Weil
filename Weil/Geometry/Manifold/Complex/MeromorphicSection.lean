module

public import Weil.Geometry.Manifold.Complex.CechFiniteDimensional
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Algebra.Polynomial.Basis

/-!
# Meromorphic sections of holomorphic line bundles on compact Riemann surfaces

Let `M` be a compact Riemann surface and `g` a holomorphic line bundle on `M`, given by
transition functions `g i j`, holomorphic and nowhere zero on `U i ∩ U j` for an open cover `U`,
with `g i k = g i j * g j k`. We show that `g` has a meromorphic section: meromorphic functions
`s i` on `U i`, vanishing identically near no point, with `s i = g i j * s j` on `U i ∩ U j`
(Theorem K of the Cartan–Serre approach to compact Riemann surfaces).

The proof refines `U` by a finite disc cover `𝔇` with one disc centred at a given point `p` and
`p` outside the closures of all other discs (`RiemannSurface.exists_discCover`). For a
polynomial `P`, the `0`-cochain which is `P (1 / z)` on the disc at `p` (`z` the coordinate
centred at `p`) and `0` on the other discs has a coboundary which is a bounded holomorphic
cocycle on the smallest discs `U''`; this is linear in `P`. Since the bounded cocycles modulo
coboundaries form a finite-dimensional space
(`RiemannSurface.DiscCover.exists_finiteDimensional_sup_range_coboundary`), some
`P = X * Q` with `Q ≠ 0` gives a coboundary `δη` of a bounded holomorphic cochain `η`, and
`η - (P (1 / z) at p)` is a meromorphic section with a pole at `p`. Transporting it back to the
cover `U` gives a section not vanishing identically near `p`. The set where a meromorphic
section vanishes identically is clopen; patching finitely many such sections along these clopen
sets, by compactness, gives a section vanishing identically near no point.

## Main definitions

* `RiemannSurface.IsMeromorphicSplitting U g s`: `s` is a meromorphic section of the line bundle
  `g` on the cover `U`, with pointwise transition relations.
* `RiemannSurface.vanishingLocus U s`: the points near which `s` vanishes identically.
* `RiemannSurface.DiscCover.poleCocycle hp g P`: the coboundary of the principal part
  `P (1 / z)` at the centre `i₀`, as a bounded holomorphic cocycle on the discs `U''`.

## Main results

* `RiemannSurface.isClopen_vanishingLocus`: the vanishing locus of a meromorphic section is
  clopen.
* `RiemannSurface.DiscCover.exists_meromorphic_section_not_eventually_eq_zero`: on a disc cover
  whose `i₀`-th centre lies in no other disc, a line bundle has a meromorphic section not
  vanishing identically near that centre.
* `RiemannSurface.exists_meromorphic_splitting_eq`: every holomorphic line bundle on a compact
  Riemann surface has a meromorphic section of finite order everywhere, with pointwise
  transition relations.
* `RiemannSurface.exists_meromorphic_splitting`: the same, with the transition relations away
  from a discrete set.

## Implementation notes

A section is a family of functions `s i : M → ℂ`, meromorphic on `U i` in the sense of
`RiemannSurface.MeromorphicOn`; its values outside `U i` play no role. Finiteness of the order
everywhere (`RiemannSurface.orderAt (s i) x ≠ ⊤`) is the condition that `s i` vanishes
identically near no point of `U i`; on a disconnected surface this needs a section with a pole on
every component, which is why sections are patched along clopen sets.

## References

* [H. Cartan, J.-P. Serre, *Un théorème de finitude concernant les variétés analytiques
  compactes*][cartanserre1953]
* [O. Forster, *Lectures on Riemann Surfaces*, §14][forster1981]
-/

@[expose] public noncomputable section

open Manifold Set Filter Topology BoundedContinuousFunction

namespace RiemannSurface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

section Splitting

variable {ι : Type*} {U : ι → Set M} {g : ι → ι → M → ℂ} {s t : ι → M → ℂ}

/-- `s` is a meromorphic section, with pointwise transition relations, of the line bundle with
transition functions `g` on the cover `U`. -/
def IsMeromorphicSplitting (U : ι → Set M) (g : ι → ι → M → ℂ) (s : ι → M → ℂ) : Prop :=
  (∀ i, MeromorphicOn (s i) (U i)) ∧ ∀ i j, ∀ x ∈ U i ∩ U j, s i x = g i j x * s j x

/-- The points near which the local representatives of `s` vanish identically. -/
def vanishingLocus (U : ι → Set M) (s : ι → M → ℂ) : Set M :=
  {x | ∀ i, x ∈ U i → ∀ᶠ y in 𝓝[≠] x, s i y = 0}

variable (hU : ∀ i, IsOpen (U i)) (hg0 : ∀ i j, ∀ x ∈ U i ∩ U j, g i j x ≠ 0)
include hU hg0

theorem eventually_eq_zero_iff_of_isMeromorphicSplitting (hs : IsMeromorphicSplitting U g s)
    {i j : ι} {x : M} (hi : x ∈ U i) (hj : x ∈ U j) :
    (∀ᶠ y in 𝓝[≠] x, s i y = 0) ↔ ∀ᶠ y in 𝓝[≠] x, s j y = 0 := by
  have hmem : ∀ᶠ y in 𝓝[≠] x, y ∈ U i ∩ U j :=
    nhdsWithin_le_nhds (((hU i).inter (hU j)).mem_nhds ⟨hi, hj⟩)
  constructor <;> intro h <;> filter_upwards [h, hmem] with y hy hyU
  · rw [hs.2 i j y hyU] at hy
    exact (mul_eq_zero.1 hy).resolve_left (hg0 i j y hyU)
  · rw [hs.2 i j y hyU, hy, mul_zero]

theorem mem_vanishingLocus_iff (hs : IsMeromorphicSplitting U g s) {i : ι} {x : M}
    (hi : x ∈ U i) : x ∈ vanishingLocus U s ↔ ∀ᶠ y in 𝓝[≠] x, s i y = 0 :=
  ⟨fun h => h i hi, fun h _ hj =>
    (eventually_eq_zero_iff_of_isMeromorphicSplitting hU hg0 hs hi hj).1 h⟩

variable (hcov : ⋃ i, U i = univ)
include hcov

theorem isClopen_vanishingLocus [T1Space M] (hs : IsMeromorphicSplitting U g s) :
    IsClopen (vanishingLocus U s) := by
  have hcov' : ∀ x, ∃ i, x ∈ U i := fun x => by
    simpa using (hcov.symm ▸ mem_univ x : x ∈ ⋃ i, U i)
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨i, hi⟩ := hcov' x
    have hne : ∀ᶠ y in 𝓝[≠] x, s i y ≠ 0 := by
      rcases (hs.1 i x hi).eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact absurd ((mem_vanishingLocus_iff hU hg0 hs hi).2 h) hx
      · exact h
    rw [eventually_nhdsWithin_iff] at hne
    filter_upwards [hne.eventually_nhds, (hU i).mem_nhds hi] with y hy hyU
    intro hyZ
    by_cases hyx : y = x
    · exact hx (hyx ▸ hyZ)
    have h1 : ∀ᶠ z in 𝓝[≠] y, s i z = 0 := (mem_vanishingLocus_iff hU hg0 hs hyU).1 hyZ
    have h2 : ∀ᶠ z in 𝓝[≠] y, s i z ≠ 0 :=
      nhdsWithin_le_nhds ((hy.and (isOpen_compl_singleton.mem_nhds
        (mem_compl_singleton_iff.2 hyx))).mono fun z hz => hz.1 hz.2)
    have := nhdsNE_neBot y
    obtain ⟨z, hz⟩ := (h1.and h2).exists
    exact hz.2 hz.1
  · rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨i, hi⟩ := hcov' x
    have h0 := (mem_vanishingLocus_iff hU hg0 hs hi).1 hx
    rw [eventually_nhdsWithin_iff] at h0
    filter_upwards [h0.eventually_nhds, (hU i).mem_nhds hi] with y hy hyU
    by_cases hyx : y = x
    · exact hyx ▸ hx
    refine (mem_vanishingLocus_iff hU hg0 hs hyU).2 ?_
    exact nhdsWithin_le_nhds ((hy.and (isOpen_compl_singleton.mem_nhds
      (mem_compl_singleton_iff.2 hyx))).mono fun z hz => hz.1 hz.2)

theorem exists_isMeromorphicSplitting_vanishingLocus_subset_inter [T1Space M]
    (hs : IsMeromorphicSplitting U g s) (ht : IsMeromorphicSplitting U g t) :
    ∃ u, IsMeromorphicSplitting U g u ∧
      vanishingLocus U u ⊆ vanishingLocus U s ∩ vanishingLocus U t := by
  classical
  have hcov' : ∀ x, ∃ i, x ∈ U i := fun x => by
    simpa using (hcov.symm ▸ mem_univ x : x ∈ ⋃ i, U i)
  set A := (vanishingLocus U s)ᶜ with hAdef
  have hA : IsClopen A := (isClopen_vanishingLocus hU hg0 hcov hs).compl
  set u : ι → M → ℂ := fun i x => if x ∈ A then s i x else t i x with hu
  have hloc : ∀ i x, x ∈ A → u i =ᶠ[𝓝 x] s i := fun i x hx =>
    eventually_of_mem (hA.isOpen.mem_nhds hx) fun y hy => by simp [hu, hy]
  have hloc' : ∀ i x, x ∉ A → u i =ᶠ[𝓝 x] t i := fun i x hx =>
    eventually_of_mem (hA.isClosed.isOpen_compl.mem_nhds hx) fun y hy => by
      simp [hu, show y ∉ A from hy]
  have hus : IsMeromorphicSplitting U g u := by
    refine ⟨fun i x hx => ?_, fun i j x hx => ?_⟩
    · by_cases hxA : x ∈ A
      · exact (hs.1 i x hx).congr ((hloc i x hxA).filter_mono nhdsWithin_le_nhds).symm
      · exact (ht.1 i x hx).congr ((hloc' i x hxA).filter_mono nhdsWithin_le_nhds).symm
    · simp only [hu]
      split_ifs
      exacts [hs.2 i j x hx, ht.2 i j x hx]
  refine ⟨u, hus, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := hcov' x
  rw [mem_vanishingLocus_iff hU hg0 hus hi] at hx
  by_cases hxA : x ∈ A
  · refine absurd ((mem_vanishingLocus_iff hU hg0 hs hi).2 ?_) hxA
    filter_upwards [hx, (hloc i x hxA).filter_mono nhdsWithin_le_nhds] with y h1 h2
    rwa [← h2]
  · refine ⟨not_not.1 hxA, (mem_vanishingLocus_iff hU hg0 ht hi).2 ?_⟩
    filter_upwards [hx, (hloc' i x hxA).filter_mono nhdsWithin_le_nhds] with y h1 h2
    rwa [← h2]

theorem exists_isMeromorphicSplitting_vanishingLocus_eq_empty [CompactSpace M] [T1Space M]
    (h : ∀ p, ∃ s, IsMeromorphicSplitting U g s ∧ p ∉ vanishingLocus U s) :
    ∃ s, IsMeromorphicSplitting U g s ∧ vanishingLocus U s = ∅ := by
  classical
  choose S hS hpS using h
  obtain ⟨P, hP⟩ := isCompact_univ.elim_finite_subcover (fun p => (vanishingLocus U (S p))ᶜ)
    (fun p => (isClopen_vanishingLocus hU hg0 hcov (hS p)).compl.isOpen)
    (fun p _ => mem_iUnion.2 ⟨p, hpS p⟩)
  have key : ∀ Q : Finset M, ∃ s, IsMeromorphicSplitting U g s ∧
      vanishingLocus U s ⊆ ⋂ p ∈ Q, vanishingLocus U (S p) := by
    intro Q
    induction Q using Finset.induction_on with
    | empty =>
      exact ⟨0, ⟨fun i => meromorphicOn_const 0 _, fun i j x _ => by simp⟩, by simp⟩
    | insert q Q hq ih =>
      obtain ⟨s, hs, hsub⟩ := ih
      obtain ⟨u, hu, hsub'⟩ :=
        exists_isMeromorphicSplitting_vanishingLocus_subset_inter hU hg0 hcov hs (hS q)
      refine ⟨u, hu, fun x hx => ?_⟩
      have := hsub' hx
      simp only [Finset.set_biInter_insert, mem_inter_iff]
      exact ⟨this.2, hsub this.1⟩
  obtain ⟨s, hs, hsub⟩ := key P
  refine ⟨s, hs, eq_empty_of_forall_notMem fun x hx => ?_⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hP (mem_univ x))
  exact hxp (mem_iInter₂.1 (hsub hx) p hp)

end Splitting

/-! ### Principal parts on a disc cover -/

namespace DiscCover

variable {ι : Type*} (𝔇 : DiscCover M ι)

/-- The function `x ↦ P ((z x)⁻¹)`, for the coordinate `z` centred at the `i`-th centre: a
principal part at `𝔇.centre i` when `P (0) = 0`. -/
def principalPart (i : ι) (P : Polynomial ℂ) : M → ℂ :=
  fun x => P.eval ((𝔇.chart i x - 𝔇.centreCoord i)⁻¹)

theorem centre_mem_U'' (i : ι) : 𝔇.centre i ∈ 𝔇.U'' i :=
  ⟨mem_chart_source ℂ _, Metric.mem_ball_self (𝔇.r''_pos i)⟩

variable [IsManifold 𝓘(ℂ) 1 M]

theorem mdifferentiableAt_principalPart (i : ι) (P : Polynomial ℂ) {x : M}
    (hx : x ∈ (𝔇.chart i).source) (hne : x ≠ 𝔇.centre i) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (𝔇.principalPart i P) x := by
  have hne' : 𝔇.chart i x - 𝔇.centreCoord i ≠ 0 := sub_ne_zero.2 fun h =>
    hne ((𝔇.chart i).injOn hx (mem_chart_source ℂ _) h)
  have hR : DifferentiableAt ℂ (fun w => P.eval ((w - 𝔇.centreCoord i)⁻¹)) (𝔇.chart i x) :=
    (P.differentiable _).comp _ ((differentiableAt_id.sub_const _).inv hne')
  exact hR.mdifferentiableAt.comp x (mdifferentiableAt_atlas (chart_mem_atlas ℂ _) hx)

theorem meromorphicAt_principalPart (i : ι) (P : Polynomial ℂ) {x : M}
    (hx : x ∈ (𝔇.chart i).source) : MeromorphicAt (𝔇.principalPart i P) x := by
  rw [meromorphicAt_iff_of_mem_atlas (chart_mem_atlas ℂ _) hx]
  have hR : _root_.MeromorphicAt (fun w => P.eval ((w - 𝔇.centreCoord i)⁻¹)) (𝔇.chart i x) := by
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
      exact (hp.add hq).congr (Eventually.of_forall fun w => by simp)
    | monomial n a =>
      exact ((_root_.MeromorphicAt.const a _).mul
        (((_root_.MeromorphicAt.id _).sub (_root_.MeromorphicAt.const (𝔇.centreCoord i) _)).inv.pow
          n)).congr (Eventually.of_forall fun w => by simp)
  apply hR.congr
  filter_upwards [nhdsWithin_le_nhds ((𝔇.chart i).eventually_right_inverse' hx)] with w hw
  simp [principalPart, hw]

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- The coordinate of the `i₀`-th centre stays away from the discs `W j`, `j ≠ i₀`, when the
centre is not in their closures. -/
theorem exists_pos_le_norm_chart_sub [Finite ι] (i₀ : ι)
    (hp : ∀ j, j ≠ i₀ → 𝔇.centre i₀ ∉ closure (𝔇.W j)) :
    ∃ δ > 0, ∀ j, j ≠ i₀ → ∀ x ∈ (𝔇.chart i₀).source ∩ 𝔇.W j,
      δ ≤ ‖𝔇.chart i₀ x - 𝔇.centreCoord i₀‖ := by
  have h1 : ∀ᶠ x in 𝓝 (𝔇.centre i₀), ∀ j, j ≠ i₀ → x ∉ 𝔇.W j := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j = i₀
    · exact Eventually.of_forall fun _ h => absurd hj h
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds (hp j hj)] with x hx _ hxW
    exact hx (subset_closure hxW)
  have hc : Tendsto (𝔇.chart i₀).symm (𝓝 (𝔇.centreCoord i₀)) (𝓝 (𝔇.centre i₀)) := by
    have := ((𝔇.chart i₀).continuousAt_symm
      ((𝔇.chart i₀).map_source (mem_chart_source ℂ _))).tendsto
    rwa [(𝔇.chart i₀).left_inv (mem_chart_source ℂ _)] at this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually h1)
  refine ⟨δ, hδ, fun j hj x hx => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  apply hball (by rwa [dist_eq_norm]) j hj
  rw [(𝔇.chart i₀).left_inv hx.1]
  exact hx.2

variable [DecidableEq ι]

/-- The `0`-cochain which is the principal part `𝔇.principalPart i₀ P` at index `i₀` and zero
elsewhere. -/
def polePart (i₀ : ι) (P : Polynomial ℂ) (i : ι) : M → ℂ :=
  if i = i₀ then 𝔇.principalPart i₀ P else 0

/-- The coboundary of `𝔇.polePart i₀ P`; it is holomorphic and bounded on the discs `U''`,
since the centre of the `i₀`-th disc lies in no other disc. -/
def poleCochain (g : 𝔇.LineCocycle) (i₀ : ι) (P : Polynomial ℂ) (i j : ι) : M → ℂ :=
  fun x => 𝔇.polePart i₀ P i x - g i j x * 𝔇.polePart i₀ P j x

variable {𝔇} {i₀ : ι}

omit [IsManifold 𝓘(ℂ) 1 M] [DecidableEq ι] in
/-- The condition under which `𝔇.polePart i₀ P i` is holomorphic and bounded at `x`. -/
theorem polePart_cond {i j : ι} {x : M} (hx : x ∈ 𝔇.U'' i ∩ 𝔇.U'' j)
    (hij : ¬(i = i₀ ∧ j = i₀)) :
    (i = i₀ → x ∈ 𝔇.U'' i₀ ∧ ∃ k, k ≠ i₀ ∧ x ∈ 𝔇.W k) ∧
      (j = i₀ → x ∈ 𝔇.U'' i₀ ∧ ∃ k, k ≠ i₀ ∧ x ∈ 𝔇.W k) := by
  constructor
  · rintro rfl
    exact ⟨hx.1, j, fun h => hij ⟨rfl, h⟩, 𝔇.U''_subset_W j hx.2⟩
  · rintro rfl
    exact ⟨hx.2, i, fun h => hij ⟨h, rfl⟩, 𝔇.U''_subset_W i hx.1⟩

variable (hp : ∀ j, j ≠ i₀ → 𝔇.centre i₀ ∉ closure (𝔇.W j))
include hp

theorem mdifferentiableAt_polePart (P : Polynomial ℂ) {i : ι} {x : M}
    (h : i = i₀ → x ∈ 𝔇.U'' i₀ ∧ ∃ k, k ≠ i₀ ∧ x ∈ 𝔇.W k) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (𝔇.polePart i₀ P i) x := by
  by_cases hi : i = i₀
  · obtain ⟨hx, k, hk, hxk⟩ := h hi
    simp only [polePart, hi, ↓reduceIte]
    refine 𝔇.mdifferentiableAt_principalPart i₀ P (𝔇.disc_subset_source _ _ hx) ?_
    rintro rfl
    exact hp k hk (subset_closure hxk)
  · simp only [polePart, hi, ↓reduceIte]
    exact mdifferentiableAt_const

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem exists_bound_polePart [Finite ι] (P : Polynomial ℂ) :
    ∃ B, 0 ≤ B ∧ ∀ i x, (i = i₀ → x ∈ 𝔇.U'' i₀ ∧ ∃ k, k ≠ i₀ ∧ x ∈ 𝔇.W k) →
      ‖𝔇.polePart i₀ P i x‖ ≤ B := by
  obtain ⟨δ, hδ, hδle⟩ := 𝔇.exists_pos_le_norm_chart_sub i₀ hp
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) δ⁻¹).exists_bound_of_continuousOn
    (P.continuous (R := ℂ)).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun i x h => ?_⟩
  by_cases hi : i = i₀
  · obtain ⟨hx, k, hk, hxk⟩ := h hi
    simp only [polePart, hi, ↓reduceIte]
    refine (hB _ ?_).trans (le_max_left _ _)
    rw [mem_closedBall_zero_iff, norm_inv]
    exact inv_anti₀ hδ (hδle k hk x ⟨𝔇.disc_subset_source _ _ hx, hxk⟩)
  · simp [polePart, hi]

variable [T2Space M] (g : 𝔇.LineCocycle)

omit [T2Space M] in
theorem mdifferentiableOn_poleCochain (P : Polynomial ℂ) (i j : ι) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (𝔇.poleCochain g i₀ P i j) (𝔇.U'' i ∩ 𝔇.U'' j) := by
  by_cases hij : i = i₀ ∧ j = i₀
  · obtain ⟨rfl, rfl⟩ := hij
    refine (mdifferentiableOn_const (c := (0 : ℂ))).congr fun x hx => ?_
    simp [poleCochain, g.apply_self (𝔇.U''_subset_W _ hx.1)]
  · intro x hx
    obtain ⟨hci, hcj⟩ := polePart_cond hx hij
    have hW : 𝔇.W i ∩ 𝔇.W j ∈ 𝓝 x :=
      ((𝔇.isOpen_W i).inter (𝔇.isOpen_W j)).mem_nhds
        ⟨𝔇.U''_subset_W i hx.1, 𝔇.U''_subset_W j hx.2⟩
    have hg := (g.mdifferentiableOn i j x (mem_of_mem_nhds hW)).mdifferentiableAt hW
    exact ((mdifferentiableAt_polePart hp P hci).sub
      (hg.mul (mdifferentiableAt_polePart hp P hcj))).mdifferentiableWithinAt

omit [IsManifold 𝓘(ℂ) 1 M] in
theorem bddAbove_poleCochain [Finite ι] (P : Polynomial ℂ) (i j : ι) :
    BddAbove ((fun x => ‖𝔇.poleCochain g i₀ P i j x‖) '' (𝔇.U'' i ∩ 𝔇.U'' j)) := by
  by_cases hij : i = i₀ ∧ j = i₀
  · obtain ⟨rfl, rfl⟩ := hij
    refine ⟨0, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    simp [poleCochain, g.apply_self (𝔇.U''_subset_W _ hx.1)]
  · obtain ⟨B, hB0, hB⟩ := exists_bound_polePart hp P
    obtain ⟨C, hC⟩ := g.exists_bound i j
    refine ⟨B + C * B, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hci, hcj⟩ := polePart_cond hx hij
    have hgx := hC x ⟨𝔇.U''_subset_U i hx.1, 𝔇.U''_subset_U j hx.2⟩
    refine (norm_sub_le _ _).trans (add_le_add (hB i x hci) ?_)
    rw [norm_mul]
    exact mul_le_mul hgx (hB j x hcj) (norm_nonneg _) ((norm_nonneg _).trans hgx)

variable [Finite ι]

/-- The coboundary of `𝔇.polePart i₀ P`, as a bounded holomorphic cocycle on the discs `U''`. -/
def poleCocycle (P : Polynomial ℂ) : 𝔇.BddCocycles g 𝔇.U'' :=
  ⟨fun i j => boundedHolomorphic.mk (𝔇.poleCochain g i₀ P i j)
      (mdifferentiableOn_poleCochain hp g P i j) (bddAbove_poleCochain hp g P i j),
    fun i j k x hx => by
      simp only [boundedHolomorphic.mk_apply, poleCochain]
      linear_combination (𝔇.polePart i₀ P k x) * g.mul_eq i j k x
        ⟨⟨𝔇.U''_subset_W i hx.1.1, 𝔇.U''_subset_W j hx.1.2⟩, 𝔇.U''_subset_W k hx.2⟩⟩

theorem poleCocycle_apply (P : Polynomial ℂ) (i j : ι) (x : (𝔇.U'' i ∩ 𝔇.U'' j : Set M)) :
    (((poleCocycle hp g P : 𝔇.BddCocycles g 𝔇.U'') : BddCochains₁ 𝔇.U'') i j :
        (𝔇.U'' i ∩ 𝔇.U'' j : Set M) →ᵇ ℂ) x = 𝔇.poleCochain g i₀ P i j x :=
  rfl

/-- `P ↦ 𝔇.poleCocycle hp g P` is linear. -/
def poleCocycleₗ : Polynomial ℂ →ₗ[ℂ] 𝔇.BddCocycles g 𝔇.U'' where
  toFun := poleCocycle hp g
  map_add' P Q := by
    refine Subtype.ext (funext fun i => funext fun j => Subtype.ext
      (BoundedContinuousFunction.ext fun x => ?_))
    change 𝔇.poleCochain g i₀ (P + Q) i j x =
      𝔇.poleCochain g i₀ P i j x + 𝔇.poleCochain g i₀ Q i j x
    simp only [poleCochain, polePart]
    split_ifs <;> (try simp only [principalPart, Pi.zero_apply, Polynomial.eval_add]) <;> ring
  map_smul' c P := by
    refine Subtype.ext (funext fun i => funext fun j => Subtype.ext
      (BoundedContinuousFunction.ext fun x => ?_))
    change 𝔇.poleCochain g i₀ (c • P) i j x = c • 𝔇.poleCochain g i₀ P i j x
    simp only [poleCochain, polePart]
    split_ifs <;> (try simp only [principalPart, Pi.zero_apply, Polynomial.eval_smul,
      smul_eq_mul]) <;> ring

omit [T2Space M] [Finite ι] in
theorem meromorphicOn_polePart (P : Polynomial ℂ) (i : ι) :
    MeromorphicOn (𝔇.polePart i₀ P i) (𝔇.U'' i) := by
  intro x hx
  by_cases hi : i = i₀
  · subst hi
    simp only [polePart, ↓reduceIte]
    exact 𝔇.meromorphicAt_principalPart _ P (𝔇.disc_subset_source _ _ hx)
  · simp only [polePart, hi, ↓reduceIte]
    exact meromorphicAt_const 0 x

omit [IsManifold 𝓘(ℂ) 1 M] [DecidableEq ι] hp [T2Space M] [Finite ι] in
/-- If `P` has positive degree, the principal part `𝔇.principalPart i₀ P` is not equal to a
function continuous at the centre on a punctured neighbourhood of it. -/
theorem not_eventuallyEq_principalPart {P : Polynomial ℂ} (hP : 0 < P.degree) {F : M → ℂ}
    (hF : ContinuousAt F (𝔇.centre i₀)) :
    ¬ F =ᶠ[𝓝[≠] 𝔇.centre i₀] 𝔇.principalPart i₀ P := by
  intro hFP
  set p := 𝔇.centre i₀
  set e := 𝔇.chart i₀
  have hz : Tendsto (fun y => e y - 𝔇.centreCoord i₀) (𝓝[≠] p) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : ContinuousAt (fun y => e y - 𝔇.centreCoord i₀) p :=
        (e.continuousAt (mem_chart_source ℂ p)).sub continuousAt_const
      have h0 : e p - 𝔇.centreCoord i₀ = 0 := sub_self _
      exact h0 ▸ this.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (e.open_source.mem_nhds (mem_chart_source ℂ p))] with y hy hys
      exact sub_ne_zero.2 fun h => hy (e.injOn hys (mem_chart_source ℂ p) h)
  have h1 : Tendsto (fun y => ‖𝔇.principalPart i₀ P y‖) (𝓝[≠] p) atTop :=
    P.tendsto_norm_atTop hP (tendsto_norm_inv_nhdsNE_zero_atTop.comp hz)
  have h2 : Tendsto (fun y => ‖F y‖) (𝓝[≠] p) (𝓝 ‖F p‖) :=
    (continuous_norm.continuousAt.comp hF).tendsto.mono_left nhdsWithin_le_nhds
  have := nhdsNE_neBot p
  exact not_tendsto_atTop_of_tendsto_nhds h2
    (h1.congr' (hFP.mono fun y hy => by simp [hy]))

omit [DecidableEq ι] in
/-- **Key step.** On a finite disc cover whose `i₀`-th centre lies in no other disc, every line
bundle has a meromorphic section, given on the discs `U''` with pointwise transition relations,
which does not vanish identically near the `i₀`-th centre. -/
theorem exists_meromorphic_section_not_eventually_eq_zero :
    ∃ σ : ι → M → ℂ, (∀ i, MeromorphicOn (σ i) (𝔇.U'' i)) ∧
      (∀ i j, ∀ x ∈ 𝔇.U'' i ∩ 𝔇.U'' j, σ i x = g i j x * σ j x) ∧
      ¬ ∀ᶠ y in 𝓝[≠] 𝔇.centre i₀, σ i₀ y = 0 := by
  classical
  obtain ⟨F₀, hF₀, hsup⟩ := 𝔇.exists_finiteDimensional_sup_range_coboundary g
  set R := LinearMap.range ((𝔇.bddCoboundary g 𝔇.U''_subset_U :
    BddCochains 𝔇.U'' →L[ℂ] 𝔇.BddCocycles g 𝔇.U'') :
      BddCochains 𝔇.U'' →ₗ[ℂ] 𝔇.BddCocycles g 𝔇.U'') with hR
  have hfin : Module.Finite ℂ (𝔇.BddCocycles g 𝔇.U'' ⧸ R) := by
    rw [Module.finite_def, ← (Submodule.map_mkQ_eq_top R F₀).2 hsup]
    exact (Module.Finite.iff_fg.1 hF₀).map _
  set L := R.mkQ ∘ₗ poleCocycleₗ hp g ∘ₗ LinearMap.mulLeft ℂ (Polynomial.X : Polynomial ℂ)
  obtain ⟨Q, hLQ, hQ⟩ : ∃ Q, L Q = 0 ∧ Q ≠ 0 := by
    by_contra h
    push Not at h
    have hinj : Function.Injective L := (injective_iff_map_eq_zero L).2 h
    have := Module.Finite.of_injective L hinj
    have := Module.Finite.finite_basis (Polynomial.basisMonomials ℂ)
    exact not_finite ℕ
  set P := Polynomial.X * Q with hPdef
  have hP : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.1 (by rw [hPdef, Polynomial.natDegree_X_mul hQ]; omega)
  have hmem : poleCocycle hp g P ∈ R := (Submodule.Quotient.mk_eq_zero R).1 hLQ
  obtain ⟨η, hη⟩ := LinearMap.mem_range.1 hmem
  choose F hF _ hFeq using fun i => boundedHolomorphic.exists_eq (η i)
  refine ⟨fun i x => F i x - 𝔇.polePart i₀ P i x, fun i => ?_, fun i j x hx => ?_, ?_⟩
  · exact (meromorphicOn_of_mdifferentiableOn (hF i) (𝔇.isOpen_U'' i)).sub
      (meromorphicOn_polePart hp P i)
  · have h := congrArg (fun ζ : 𝔇.BddCocycles g 𝔇.U'' =>
      ((ζ : BddCochains₁ 𝔇.U'') i j : (𝔇.U'' i ∩ 𝔇.U'' j : Set M) →ᵇ ℂ) ⟨x, hx⟩) hη
    simp only [ContinuousLinearMap.coe_coe, bddCoboundary_apply, poleCocycle_apply,
      poleCochain] at h
    rw [hFeq, hFeq] at h
    linear_combination h
  · intro hz
    have hpU := 𝔇.centre_mem_U'' i₀
    have hcont : ContinuousAt (F i₀) (𝔇.centre i₀) :=
      ((hF i₀) _ hpU).continuousWithinAt.continuousAt ((𝔇.isOpen_U'' i₀).mem_nhds hpU)
    refine not_eventuallyEq_principalPart hP hcont (hz.mono fun y hy => ?_)
    simp only [polePart, ↓reduceIte] at hy
    exact sub_eq_zero.1 hy

end DiscCover


/-! ### Theorem K -/

section TheoremK

variable [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [CompactSpace M]

/-- **Every holomorphic line bundle on a compact Riemann surface has a meromorphic section**,
with pointwise transition relations: for a line-bundle cocycle `g` on an open cover `U` there are
meromorphic functions `s i` on `U i`, of finite order at every point, with
`s i = g i j * s j` on `U i ∩ U j`. -/
theorem exists_meromorphic_splitting_eq {ι : Type*} (U : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) (g : ι → ι → M → ℂ)
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (U i ∩ U j))
    (hg0 : ∀ i j, ∀ x ∈ U i ∩ U j, g i j x ≠ 0)
    (hcoc : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i k x = g i j x * g j k x) :
    ∃ s : ι → M → ℂ, (∀ i, MeromorphicOn (s i) (U i) ∧ ∀ x ∈ U i, orderAt (s i) x ≠ ⊤) ∧
      ∀ i j, ∀ x ∈ U i ∩ U j, s i x = g i j x * s j x := by
  have hkey : ∀ p, ∃ s, IsMeromorphicSplitting U g s ∧ p ∉ vanishingLocus U s := by
    intro p
    classical
    obtain ⟨κ, _, 𝔇, τ, i₀, hW, hc, hpU, hp⟩ := exists_discCover U hU hcov p
    let g' : 𝔇.LineCocycle :=
      { toFun := fun i j => g (τ i) (τ j)
        mdifferentiableOn := fun i j => (hg _ _).mono (inter_subset_inter (hW i) (hW j))
        ne_zero := fun i j x hx => hg0 _ _ x ⟨hW i hx.1, hW j hx.2⟩
        mul_eq := fun i j k x hx =>
          (hcoc _ _ _ x ⟨⟨hW i hx.1.1, hW j hx.1.2⟩, hW k hx.2⟩).symm }
    have hp' : ∀ j, j ≠ i₀ → 𝔇.centre i₀ ∉ closure (𝔇.W j) := by
      rw [hc]
      exact hp
    obtain ⟨σ, hσm, hσs, hσ0⟩ :=
      DiscCover.exists_meromorphic_section_not_eventually_eq_zero hp' g'
    choose idx hidx using 𝔇.exists_mem_U''
    have hWU : ∀ i, 𝔇.U'' i ⊆ U (τ i) := fun i => (𝔇.U''_subset_W i).trans (hW i)
    set s : ι → M → ℂ := fun a x => g a (τ (idx x)) x * σ (idx x) x with hs
    have hloc : ∀ a j x, x ∈ 𝔇.U'' j → x ∈ U a → s a x = g a (τ j) x * σ j x := by
      intro a j x hj ha
      have h1 : σ (idx x) x = g (τ (idx x)) (τ j) x * σ j x := hσs (idx x) j x ⟨hidx x, hj⟩
      have h2 := hcoc a (τ (idx x)) (τ j) x ⟨⟨ha, hWU _ (hidx x)⟩, hWU j hj⟩
      simp only [hs, h1, h2]
      ring
    refine ⟨s, ⟨fun a x hx => ?_, fun a b x hx => ?_⟩, ?_⟩
    · have hj := hidx x
      have hN : 𝔇.U'' (idx x) ∩ U a ∈ 𝓝 x :=
        ((𝔇.isOpen_U'' _).inter (hU a)).mem_nhds ⟨hj, hx⟩
      have hO : IsOpen (U a ∩ U (τ (idx x))) := (hU a).inter (hU _)
      have hgm : MeromorphicAt (g a (τ (idx x))) x :=
        meromorphicAt_of_eventually_mdifferentiableAt
          (eventually_of_mem (hO.mem_nhds ⟨hx, hWU _ hj⟩) fun y hy =>
            (hg a _ y hy).mdifferentiableAt (hO.mem_nhds hy))
      exact (hgm.mul (hσm _ x hj)).congr
        (nhdsWithin_le_nhds (eventually_of_mem hN fun y hy => (hloc a _ y hy.1 hy.2).symm))
    · have h := hcoc a b (τ (idx x)) x ⟨⟨hx.1, hx.2⟩, hWU _ (hidx x)⟩
      simp only [hs, h]
      ring
    · intro hZ
      have hpa : p ∈ U (τ i₀) := hWU i₀ hpU
      apply hσ0
      rw [hc]
      have hN : 𝔇.U'' i₀ ∩ U (τ i₀) ∈ 𝓝 p := ((𝔇.isOpen_U'' _).inter (hU _)).mem_nhds ⟨hpU, hpa⟩
      filter_upwards [hZ (τ i₀) hpa, nhdsWithin_le_nhds hN] with y hy hyN
      rw [hloc _ i₀ y hyN.1 hyN.2] at hy
      exact (mul_eq_zero.1 hy).resolve_left (hg0 _ _ y ⟨hyN.2, hWU i₀ hyN.1⟩)
  obtain ⟨s, hs, hZ⟩ := exists_isMeromorphicSplitting_vanishingLocus_eq_empty hU hg0 hcov hkey
  refine ⟨s, fun i => ⟨hs.1 i, fun x hx htop => ?_⟩, hs.2⟩
  have := (mem_vanishingLocus_iff hU hg0 hs hx).2 (orderAt_eq_top_iff.1 htop)
  rw [hZ] at this
  exact this

/-- **Theorem K** (meromorphic splitting of line bundles): every holomorphic line-bundle cocycle
`g` on an open cover `U` of a compact Riemann surface is split by meromorphic functions `s i` on
`U i`, of finite order everywhere: `s i = g i j * s j` away from a discrete subset of
`U i ∩ U j`. -/
theorem exists_meromorphic_splitting {ι : Type*} (U : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = univ) (g : ι → ι → M → ℂ)
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (U i ∩ U j))
    (hg0 : ∀ i j, ∀ x ∈ U i ∩ U j, g i j x ≠ 0)
    (hcoc : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i k x = g i j x * g j k x) :
    ∃ s : ι → M → ℂ, (∀ i, MeromorphicOn (s i) (U i) ∧ ∀ x ∈ U i, orderAt (s i) x ≠ ⊤) ∧
      ∀ i j, s i =ᶠ[codiscreteWithin (U i ∩ U j)] fun x => g i j x * s j x := by
  obtain ⟨s, hs, heq⟩ := exists_meromorphic_splitting_eq U hU hcov g hg hg0 hcoc
  exact ⟨s, hs, fun i j => eventually_of_mem (self_mem_codiscreteWithin _) (heq i j)⟩

end TheoremK

end RiemannSurface
