module

public import WeilFrontier.Geometry.Manifold.Complex.Meromorphic
public import WeilFrontier.Analysis.Complex.DolbeaultLemma
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Shrinking decomposition of line-bundle cocycles on a Riemann surface

Let `M` be a Riemann surface and `𝔇` a finite *disc cover* of `M`: coordinate discs
`W i ⊇ U i ⊇ U' i ⊇ U'' i` about finitely many centres, with concentric radii in the preferred
chart at each centre, such that the smallest discs `U'' i` cover `M`. A holomorphic line bundle
on the discs `W i` is given by transition functions `g i j`, and a holomorphic `1`-cocycle with
values in it on sets `V i` is a family `ζ i j`, holomorphic on `V i ∩ V j`, with
`ζ i k = ζ i j + g i j * ζ j k`.

The main result is the analytic step in the Cartan–Serre proof that the first cohomology of a
line bundle on a compact Riemann surface is finite dimensional: every bounded cocycle `ζ` on the
smallest discs is cohomologous, on the smallest discs, to (the restriction of) a cocycle `ξ` on
the larger discs `U`, bounded on `U'`, through a bounded holomorphic `0`-cochain `η`:
`ζ i j = ξ i j + (η i - g i j * η j)` on `U'' i ∩ U'' j`.

The proof is Dolbeault's. A smooth partition of unity `ψ` subordinate to `U''` splits `ζ` as
`ζ i j = h i - g i j * h j` with the smooth bounded functions `h i = ∑ k, ψ k * ζ i k`. Since
`ζ` and `g` are holomorphic, the `∂̄`-derivatives of the `h k`, transported to the `i`-th
trivialisation and written in the `i`-th chart, agree on overlaps; glued with `ψ` they form a
smooth function `ω i` on the `i`-th coordinate disc of radius `ρ i`. The local solvability of
`∂u/∂z̄ = ω i` (`Complex.exists_contDiff_dbar_eq_on_ball`) gives smooth `v i` on a neighbourhood
of the closure of `U i` with `∂̄ v i = ω i`, so that `v i - g i k * h k` is holomorphic, and
`ξ i j = v i - g i j * v j`, `η i = h i - v i` are as required.

We also show that every open cover of a compact Riemann surface is refined by a disc cover, which
may be chosen with one disc centred at a given point `p` and `p` outside the closures of all the
other discs.

## Main definitions

* `RiemannSurface.DiscCover M ι`: a disc cover of `M` indexed by `ι`, with the discs
  `W i ⊇ U i ⊇ U' i ⊇ U'' i`.
* `RiemannSurface.DiscCover.LineCocycle`: the transition functions of a holomorphic line bundle
  on the discs `W i`.
* `RiemannSurface.DiscCover.IsCocycleOn g V ζ`: `ζ` is a holomorphic `1`-cocycle on the sets
  `V i` with values in the line bundle `g`.

## Main results

* `RiemannSurface.DiscCover.exists_decomposition`: the shrinking decomposition
  `ζ = ξ + δη` of a bounded cocycle on the smallest discs.
* `RiemannSurface.exists_discCover`: existence of disc covers refining an open cover of a compact
  Riemann surface, adapted to a given point.
* `RiemannSurface.isManifold_real_smooth`: a complex manifold of class `C¹` is a real smooth
  manifold.

## Implementation notes

The `(0,1)`-form `∂̄ h` is never introduced as a geometric object: in each chart `i` we only use
the Wirtinger derivative `Complex.dbar` of functions on open subsets of `ℂ`, applied to the
expressions `g i k * h k` written in the chart `i` itself, so no transformation rule of `∂̄`
under a change of chart is needed. Holomorphy on `M` is `MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)`, and it
is checked in the chart `i` through the Cauchy–Riemann equation `∂̄ = 0`.

Sup norms are used throughout (bounded holomorphic functions), not `L²` norms.

## References

* [O. Forster, *Lectures on Riemann Surfaces*][forster1981], §14.
* [H. Cartan, J.-P. Serre, *Un théorème de finitude concernant les variétés analytiques
  compactes*][cartanserre1953].
-/

@[expose] public noncomputable section

open Manifold Set Filter Topology Metric

universe u

namespace RiemannSurface

/-! ### Wirtinger derivative: local calculus -/

section Dbar

open Complex

private theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  simp only [dbar, h.fderiv_eq]

private theorem dbar_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (fun w => f w - g w) z = dbar f z - dbar g z := by
  simp only [dbar, fderiv_fun_sub hf hg]
  simp only [smul_eq_mul, sub_apply]
  ring

private theorem dbar_mul_of_differentiableAt {c f : ℂ → ℂ} {z : ℂ} (hc : DifferentiableAt ℂ c z)
    (hf : DifferentiableAt ℝ f z) : dbar (fun w => c w * f w) z = c z * dbar f z := by
  have hc' : DifferentiableAt ℝ c z := hc.restrictScalars ℝ
  have h0 := dbar_eq_zero_of_differentiableAt hc
  have := fderiv_mul hc' hf
  simp only [dbar] at h0 ⊢
  rw [show (fun w => c w * f w) = c * f from rfl, this]
  simp only [add_apply, smul_apply, smul_eq_mul] at h0 ⊢
  have h0' : fderiv ℝ c z 1 + I * fderiv ℝ c z I = 0 := by
    have : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h0).resolve_left this
  linear_combination (1 / 2 : ℂ) * f z * h0'

private theorem differentiableAt_of_dbar_eq_zero {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (h : dbar f z = 0) : DifferentiableAt ℂ f z := by
  set L := fderiv ℝ f z with hL
  have hI : L I = I * L 1 := by
    simp only [dbar, smul_eq_mul, ← hL] at h
    have h' : L 1 + I * L I = 0 := by
      have : (1 / 2 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h).resolve_left this
    linear_combination (-I) * h' + (L I) * I_sq
  have hv : ∀ v : ℂ, L v = v * L 1 := by
    intro v
    have hv' : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hv', map_add, map_smul, map_smul, hI]
    conv_rhs => rw [hv']
    simp only [Complex.real_smul, mul_one]
    ring
  refine (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt
    (f' := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (L 1)) ?_).differentiableAt
  ext1 v
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, smul_eq_mul]
  rw [← hL]
  exact (hv v).symm

private theorem contDiffOn_dbar {f : ℂ → ℂ} {s : Set ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (hs : IsOpen s) : ContDiffOn ℝ (⊤ : ℕ∞) (dbar f) s := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) s :=
    hf.fderiv_of_isOpen hs (by simp)
  have h1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have h2 := hd.clm_apply (contDiffOn_const (c := I))
  have h3 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ f w 1 + I * fderiv ℝ f w I) s :=
    h1.add (contDiffOn_const.mul h2)
  have h4 := (contDiffOn_const (c := (1 / 2 : ℂ))).mul h3
  refine h4.congr fun w _ => ?_
  simp [dbar, smul_eq_mul]

end Dbar

/-! ### Calculus in charts -/

section Charts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A function holomorphic on an open set is complex differentiable in every chart. -/
private theorem differentiableOn_comp_symm [IsManifold 𝓘(ℂ) 1 M] {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ atlas ℂ M) {f : M → ℂ} {S : Set M} (hS : IsOpen S)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f S) :
    DifferentiableOn ℂ (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' S) := by
  intro z hz
  have hx := e.map_target hz.1
  have h := (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he hx).1
    ((hf _ hz.2).mdifferentiableAt (hS.mem_nhds hz.2))
  rw [e.right_inv hz.1] at h
  exact h.differentiableWithinAt

/-- A function holomorphic on an open set is real smooth in every chart. -/
private theorem contDiffOn_comp_symm [IsManifold 𝓘(ℂ) 1 M] {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ atlas ℂ M) {f : M → ℂ} {S : Set M} (hS : IsOpen S)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ e.symm) (e.target ∩ e.symm ⁻¹' S) :=
  ((differentiableOn_comp_symm he hS hf).contDiffOn
    (e.isOpen_inter_preimage_symm hS)).restrict_scalars ℝ

/-- A real smooth function on `M` is smooth in the preferred charts. -/
private theorem contDiffOn_comp_chartAt_symm [IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) M] {ψ : M → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) ψ) (c : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ψ ∘ (chartAt ℂ c).symm) (chartAt ℂ c).target := by
  have h := (contMDiff_iff.1 hψ).2 c 0
  simpa [extChartAt, Function.comp_def, chartAt_self_eq] using h

/-- Holomorphy from the Cauchy–Riemann equation in a chart: if `F ∘ e⁻¹` agrees near `e x` with
a real differentiable function `G` with `∂G/∂z̄ = 0` at `e x`, then `F` is holomorphic at `x`. -/
private theorem mdifferentiableAt_of_dbar_eq_zero [IsManifold 𝓘(ℂ) 1 M]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M) {x : M} (hx : x ∈ e.source)
    {F : M → ℂ} {G : ℂ → ℂ} (hFG : F ∘ e.symm =ᶠ[𝓝 (e x)] G) (hG : DifferentiableAt ℝ G (e x))
    (hG0 : Complex.dbar G (e x) = 0) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F x :=
  (mdifferentiableAt_iff_differentiableAt_of_mem_atlas he hx).2
    ((differentiableAt_of_dbar_eq_zero hG hG0).congr_of_eventuallyEq hFG)

/-- A complex manifold of class `C¹` is a real smooth manifold: holomorphic transition maps are
real smooth. -/
theorem isManifold_real_smooth [IsManifold 𝓘(ℂ) 1 M] : IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have h := contDiffOn_transition he' he
  have hs : IsOpen (e.symm.trans e').source := (e.symm.trans e').open_source
  have h' : ContDiffOn ℝ (⊤ : ℕ∞) (e' ∘ e.symm) (e.symm.trans e').source :=
    ((h.differentiableOn one_ne_zero).contDiffOn hs).restrict_scalars ℝ
  simpa using h'

end Charts

/-! ### Disc covers -/

/-- A *disc cover* of a Riemann surface `M`: finitely many (in applications) points `centre i`
with radii `0 < r'' i < r' i < r i < ρ i`, such that the closed disc of radius `ρ i` about
`centre i` in the preferred chart at `centre i` lies in the chart's target, and such that the
smallest discs (radius `r'' i`) cover `M`. The four discs about `centre i` are
`W i ⊇ U i ⊇ U' i ⊇ U'' i`. -/
structure DiscCover (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] (ι : Type*) where
  /-- The centre of the `i`-th disc. -/
  centre : ι → M
  /-- The radius of the largest disc `W i`. -/
  ρ : ι → ℝ
  /-- The radius of the disc `U i`. -/
  r : ι → ℝ
  /-- The radius of the disc `U' i`. -/
  r' : ι → ℝ
  /-- The radius of the smallest disc `U'' i`. -/
  r'' : ι → ℝ
  r''_pos : ∀ i, 0 < r'' i
  r''_lt_r' : ∀ i, r'' i < r' i
  r'_lt_r : ∀ i, r' i < r i
  r_lt_ρ : ∀ i, r i < ρ i
  closedBall_subset_target : ∀ i,
    closedBall (chartAt ℂ (centre i) (centre i)) (ρ i) ⊆ (chartAt ℂ (centre i)).target
  iUnion_eq_univ : ⋃ i, ((chartAt ℂ (centre i)).source ∩
    chartAt ℂ (centre i) ⁻¹' ball (chartAt ℂ (centre i) (centre i)) (r'' i)) = univ

namespace DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {ι : Type*} (𝔇 : DiscCover M ι)

/-- The chart of the `i`-th disc: the preferred chart at its centre. -/
abbrev chart (i : ι) : OpenPartialHomeomorph M ℂ := chartAt ℂ (𝔇.centre i)

/-- The coordinate of the centre of the `i`-th disc. -/
abbrev centreCoord (i : ι) : ℂ := 𝔇.chart i (𝔇.centre i)

/-- The disc of radius `s` about the `i`-th centre, in the `i`-th chart. -/
def disc (i : ι) (s : ℝ) : Set M :=
  (𝔇.chart i).source ∩ 𝔇.chart i ⁻¹' ball (𝔇.centreCoord i) s

/-- The largest disc, of radius `ρ i`. -/
def W (i : ι) : Set M := 𝔇.disc i (𝔇.ρ i)

/-- The disc of radius `r i`. -/
def U (i : ι) : Set M := 𝔇.disc i (𝔇.r i)

/-- The disc of radius `r' i`. -/
def U' (i : ι) : Set M := 𝔇.disc i (𝔇.r' i)

/-- The smallest disc, of radius `r'' i`; these cover `M`. -/
def U'' (i : ι) : Set M := 𝔇.disc i (𝔇.r'' i)

theorem isOpen_disc (i : ι) (s : ℝ) : IsOpen (𝔇.disc i s) :=
  (𝔇.chart i).isOpen_inter_preimage isOpen_ball

theorem disc_mono (i : ι) {s t : ℝ} (h : s ≤ t) : 𝔇.disc i s ⊆ 𝔇.disc i t :=
  inter_subset_inter_right _ (preimage_mono (ball_subset_ball h))

theorem disc_subset_source (i : ι) (s : ℝ) : 𝔇.disc i s ⊆ (𝔇.chart i).source :=
  inter_subset_left

theorem mapsTo_disc (i : ι) (s : ℝ) : MapsTo (𝔇.chart i) (𝔇.disc i s) (ball (𝔇.centreCoord i) s) :=
  fun _ hx => hx.2

theorem isOpen_W (i : ι) : IsOpen (𝔇.W i) := 𝔇.isOpen_disc i _
theorem isOpen_U (i : ι) : IsOpen (𝔇.U i) := 𝔇.isOpen_disc i _
theorem isOpen_U' (i : ι) : IsOpen (𝔇.U' i) := 𝔇.isOpen_disc i _
theorem isOpen_U'' (i : ι) : IsOpen (𝔇.U'' i) := 𝔇.isOpen_disc i _

theorem U''_subset_U' (i : ι) : 𝔇.U'' i ⊆ 𝔇.U' i := 𝔇.disc_mono i (𝔇.r''_lt_r' i).le
theorem U'_subset_U (i : ι) : 𝔇.U' i ⊆ 𝔇.U i := 𝔇.disc_mono i (𝔇.r'_lt_r i).le
theorem U_subset_W (i : ι) : 𝔇.U i ⊆ 𝔇.W i := 𝔇.disc_mono i (𝔇.r_lt_ρ i).le
theorem U''_subset_W (i : ι) : 𝔇.U'' i ⊆ 𝔇.W i :=
  (𝔇.U''_subset_U' i).trans ((𝔇.U'_subset_U i).trans (𝔇.U_subset_W i))
theorem U'_subset_W (i : ι) : 𝔇.U' i ⊆ 𝔇.W i := (𝔇.U'_subset_U i).trans (𝔇.U_subset_W i)

theorem iUnion_U''_eq_univ : ⋃ i, 𝔇.U'' i = univ := 𝔇.iUnion_eq_univ

theorem exists_mem_U'' (x : M) : ∃ i, x ∈ 𝔇.U'' i := by
  simpa using (𝔇.iUnion_U''_eq_univ.symm ▸ mem_univ x : x ∈ ⋃ i, 𝔇.U'' i)

theorem closedBall_subset_target' (i : ι) {s : ℝ} (hs : s ≤ 𝔇.ρ i) :
    closedBall (𝔇.centreCoord i) s ⊆ (𝔇.chart i).target :=
  (closedBall_subset_closedBall hs).trans (𝔇.closedBall_subset_target i)

theorem ball_subset_target (i : ι) : ball (𝔇.centreCoord i) (𝔇.ρ i) ⊆ (𝔇.chart i).target :=
  ball_subset_closedBall.trans (𝔇.closedBall_subset_target i)

/-- The image of a closed coordinate disc of radius `s ≤ ρ i` is compact. -/
theorem isCompact_symm_image_closedBall (i : ι) {s : ℝ} (hs : s ≤ 𝔇.ρ i) :
    IsCompact ((𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) s) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((𝔇.chart i).continuousOn_symm.mono (𝔇.closedBall_subset_target' i hs))

theorem disc_subset_symm_image_closedBall (i : ι) (s : ℝ) :
    𝔇.disc i s ⊆ (𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) s :=
  fun x hx => ⟨𝔇.chart i x, ball_subset_closedBall hx.2, (𝔇.chart i).left_inv hx.1⟩

theorem symm_image_closedBall_subset_W (i : ι) {s : ℝ} (hs : s < 𝔇.ρ i) :
    (𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) s ⊆ 𝔇.W i := by
  rintro _ ⟨z, hz, rfl⟩
  have hzt := 𝔇.closedBall_subset_target' i hs.le hz
  refine ⟨(𝔇.chart i).map_target hzt, ?_⟩
  simp only [mem_preimage, (𝔇.chart i).right_inv hzt]
  exact closedBall_subset_ball hs hz

include 𝔇 in
/-- A space with a finite disc cover is compact. -/
theorem compactSpace [Finite ι] : CompactSpace M := by
  refine ⟨?_⟩
  have h : (univ : Set M) ⊆ ⋃ i, (𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) (𝔇.r'' i) := by
    rw [← 𝔇.iUnion_U''_eq_univ]
    exact iUnion_mono fun i => 𝔇.disc_subset_symm_image_closedBall i _
  exact (isCompact_iUnion fun i => 𝔇.isCompact_symm_image_closedBall i
    ((𝔇.r''_lt_r' i).trans ((𝔇.r'_lt_r i).trans (𝔇.r_lt_ρ i))).le).of_isClosed_subset
    isClosed_univ h

/-! ### Line-bundle cocycles and cochains -/

/-- A holomorphic line bundle on the discs `W i` of a disc cover, given by its transition
functions: `g i j` is holomorphic and nowhere zero on `W i ∩ W j`, and
`g i j * g j k = g i k` on triple overlaps. A section is given in the `i`-th trivialisation by
`s i`, with `s i = g i j * s j`. -/
structure LineCocycle where
  /-- The transition function from the `j`-th to the `i`-th trivialisation. -/
  toFun : ι → ι → M → ℂ
  mdifferentiableOn : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (toFun i j) (𝔇.W i ∩ 𝔇.W j)
  ne_zero : ∀ i j, ∀ x ∈ 𝔇.W i ∩ 𝔇.W j, toFun i j x ≠ 0
  mul_eq : ∀ i j k, ∀ x ∈ 𝔇.W i ∩ 𝔇.W j ∩ 𝔇.W k, toFun i j x * toFun j k x = toFun i k x

namespace LineCocycle

variable {𝔇}

instance : CoeFun 𝔇.LineCocycle (fun _ => ι → ι → M → ℂ) := ⟨toFun⟩

theorem apply_self (g : 𝔇.LineCocycle) {i : ι} {x : M} (hx : x ∈ 𝔇.W i) : g i i x = 1 := by
  have h := g.mul_eq i i i x ⟨⟨hx, hx⟩, hx⟩
  have h0 := g.ne_zero i i x ⟨hx, hx⟩
  have : g i i x * (g i i x - 1) = 0 := by
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h0)

end LineCocycle

/-- `ζ` is a holomorphic `1`-cocycle on the sets `V i` with values in the line bundle `g`:
`ζ i j` (written in the `i`-th trivialisation) is holomorphic on `V i ∩ V j`, and
`ζ i k = ζ i j + g i j * ζ j k` on `V i ∩ V j ∩ V k`. The coboundary of a `0`-cochain `η` is
`(i, j) ↦ η i - g i j * η j`. -/
structure IsCocycleOn (g : 𝔇.LineCocycle) (V : ι → Set M) (ζ : ι → ι → M → ℂ) : Prop where
  mdifferentiableOn : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ζ i j) (V i ∩ V j)
  add_eq : ∀ i j k, ∀ x ∈ V i ∩ V j ∩ V k, ζ i k x = ζ i j x + g i j x * ζ j k x

variable {𝔇} in
theorem IsCocycleOn.mono {g : 𝔇.LineCocycle} {V V' : ι → Set M} {ζ : ι → ι → M → ℂ}
    (h : 𝔇.IsCocycleOn g V ζ) (hV : ∀ i, V' i ⊆ V i) : 𝔇.IsCocycleOn g V' ζ where
  mdifferentiableOn i j := (h.mdifferentiableOn i j).mono (inter_subset_inter (hV i) (hV j))
  add_eq i j k x hx := h.add_eq i j k x ⟨⟨hV i hx.1.1, hV j hx.1.2⟩, hV k hx.2⟩

end DiscCover

/-! ### The shrinking decomposition -/

section Decomposition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {ι : Type*} [Fintype ι]
  (𝔇 : DiscCover M ι)

namespace DiscCover

/-- The smooth splitting `h i = ∑ k, ψ k * ζ i k` of a cochain `ζ` along a partition of
unity `ψ`. -/
private def split (ψ : ι → M → ℝ) (ζ : ι → ι → M → ℂ) (i : ι) (x : M) : ℂ :=
  ∑ k, (ψ k x : ℂ) * ζ i k x

/-- The splitting of `ζ` in the `k`-th trivialisation, transported to the `i`-th one and written
in the `i`-th chart. -/
private def chartExpr (g : 𝔇.LineCocycle) (ψ : ι → M → ℝ) (ζ : ι → ι → M → ℂ) (i k : ι)
    (z : ℂ) : ℂ :=
  g i k ((𝔇.chart i).symm z) * split ψ ζ k ((𝔇.chart i).symm z)

/-- The `∂̄` of the splitting, written in the `i`-th trivialisation and the `i`-th chart. -/
private def form (g : 𝔇.LineCocycle) (ψ : ι → M → ℝ) (ζ : ι → ι → M → ℂ) (i : ι) (z : ℂ) : ℂ :=
  ∑ k, (ψ k ((𝔇.chart i).symm z) : ℂ) * Complex.dbar (chartExpr 𝔇 g ψ ζ i k) z

variable {𝔇}

private theorem split_sub {g : 𝔇.LineCocycle} {ζ : ι → ι → M → ℂ} (hζ : 𝔇.IsCocycleOn g 𝔇.U'' ζ)
    {ψ : ι → M → ℝ} (hsum : ∀ x, ∑ k, ψ k x = 1) (hsupp : ∀ k, tsupport (ψ k) ⊆ 𝔇.U'' k)
    {i j : ι} {x : M} (hx : x ∈ 𝔇.U'' i ∩ 𝔇.U'' j) :
    ζ i j x = split ψ ζ i x - g i j x * split ψ ζ j x := by
  unfold split
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have h1 : ζ i j x = ∑ k, (ψ k x : ℂ) * ζ i j x := by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_mul]
  rw [h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ψ k x = 0
  · simp [hk]
  have hxk : x ∈ 𝔇.U'' k := hsupp k (subset_tsupport _ hk)
  rw [hζ.add_eq i j k x ⟨hx, hxk⟩]
  ring

private theorem exists_norm_split_le {ζ : ι → ι → M → ℂ}
    (hb : ∀ i j, ∃ C, ∀ x ∈ 𝔇.U'' i ∩ 𝔇.U'' j, ‖ζ i j x‖ ≤ C) {ψ : ι → M → ℝ}
    (hψ0 : ∀ k x, 0 ≤ ψ k x) (hψ1 : ∀ k x, ψ k x ≤ 1) (hsupp : ∀ k, tsupport (ψ k) ⊆ 𝔇.U'' k)
    (i : ι) : ∃ C, ∀ x ∈ 𝔇.U'' i, ‖split ψ ζ i x‖ ≤ C := by
  choose C hC using hb
  refine ⟨∑ k, max (C i k) 0, fun x hx => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  by_cases hk : ψ k x = 0
  · simp [hk]
  have hxk : x ∈ 𝔇.U'' k := hsupp k (subset_tsupport _ hk)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hψ0 k x)]
  calc ψ k x * ‖ζ i k x‖ ≤ 1 * max (C i k) 0 :=
        mul_le_mul (hψ1 k x) ((hC i k x ⟨hx, hxk⟩).trans (le_max_left _ _)) (norm_nonneg _)
          zero_le_one
    _ = max (C i k) 0 := one_mul _

omit [ChartedSpace ℂ M] in
/-- A function `ψ` vanishing off its closed support vanishes near every point, in a chart, whose
preimage lies off the support. -/
private theorem comp_symm_eventually_eq_zero {ψ : M → ℝ} {e : OpenPartialHomeomorph M ℂ} {z : ℂ}
    (hz : z ∈ e.target) (hψ : e.symm z ∉ tsupport ψ) : ∀ᶠ w in 𝓝 z, ψ (e.symm w) = 0 := by
  have h := (e.continuousAt_symm hz).preimage_mem_nhds
    ((isClosed_tsupport ψ).isOpen_compl.mem_nhds hψ)
  filter_upwards [h] with w hw
  exact image_eq_zero_of_notMem_tsupport hw

variable [IsManifold 𝓘(ℂ) 1 M] [IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) M]

private theorem contDiffOn_split_comp_symm {g : 𝔇.LineCocycle} {ζ : ι → ι → M → ℂ}
    (hζ : 𝔇.IsCocycleOn g 𝔇.U'' ζ) {ψ : ι → M → ℝ}
    (hψs : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (ψ k)) (hsupp : ∀ k, tsupport (ψ k) ⊆ 𝔇.U'' k)
    (c : M) (k : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => split ψ ζ k ((chartAt ℂ c).symm z))
      ((chartAt ℂ c).target ∩ (chartAt ℂ c).symm ⁻¹' 𝔇.U'' k) := by
  set e := chartAt ℂ c
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' 𝔇.U'' k) := e.isOpen_inter_preimage_symm (𝔇.isOpen_U'' k)
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  unfold split
  apply ContDiffAt.sum
  intro l _
  by_cases hl : e.symm z ∈ 𝔇.U'' l
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (ψ l (e.symm w) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z
        ((contDiffOn_comp_chartAt_symm (hψs l) c).contDiffAt (e.open_target.mem_nhds hz.1))
    have hO' : IsOpen (𝔇.U'' k ∩ 𝔇.U'' l) := (𝔇.isOpen_U'' k).inter (𝔇.isOpen_U'' l)
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => ζ k l (e.symm w)) z :=
      (contDiffOn_comp_symm (chart_mem_atlas ℂ c) hO' (hζ.mdifferentiableOn k l)).contDiffAt
        ((e.isOpen_inter_preimage_symm hO').mem_nhds ⟨hz.1, hz.2, hl⟩)
    exact h1.mul h2
  · have hnot : e.symm z ∉ tsupport (ψ l) := fun h => hl (hsupp l h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [comp_symm_eventually_eq_zero hz.1 hnot] with w hw
    simp [hw]

private theorem contDiffOn_chartExpr {g : 𝔇.LineCocycle} {ζ : ι → ι → M → ℂ}
    (hζ : 𝔇.IsCocycleOn g 𝔇.U'' ζ) {ψ : ι → M → ℝ}
    (hψs : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (ψ k)) (hsupp : ∀ k, tsupport (ψ k) ⊆ 𝔇.U'' k)
    (i k : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (chartExpr 𝔇 g ψ ζ i k)
      ((𝔇.chart i).target ∩ (𝔇.chart i).symm ⁻¹' (𝔇.W i ∩ 𝔇.U'' k)) := by
  have hg := contDiffOn_comp_symm (chart_mem_atlas ℂ (𝔇.centre i))
    ((𝔇.isOpen_W i).inter (𝔇.isOpen_W k)) (g.mdifferentiableOn i k)
  have hh := contDiffOn_split_comp_symm hζ hψs hsupp (𝔇.centre i) k
  refine (hg.mono ?_).mul (hh.mono ?_)
  · exact fun z hz => ⟨hz.1, hz.2.1, 𝔇.U''_subset_W k hz.2.2⟩
  · exact fun z hz => ⟨hz.1, hz.2.2⟩

omit [Fintype ι] [IsManifold 𝓘(ℂ) 1 M] [IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) M] in
private theorem isOpen_chartExpr_domain (i k : ι) :
    IsOpen ((𝔇.chart i).target ∩ (𝔇.chart i).symm ⁻¹' (𝔇.W i ∩ 𝔇.U'' k)) :=
  (𝔇.chart i).isOpen_inter_preimage_symm ((𝔇.isOpen_W i).inter (𝔇.isOpen_U'' k))

omit [Fintype ι] [IsManifold 𝓘(ℂ) 1 M] [IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) M] in
private theorem mem_chartExpr_domain {i k : ι} {y : M} (hy : y ∈ 𝔇.W i ∩ 𝔇.U'' k) :
    𝔇.chart i y ∈ (𝔇.chart i).target ∩ (𝔇.chart i).symm ⁻¹' (𝔇.W i ∩ 𝔇.U'' k) := by
  have hys : y ∈ (𝔇.chart i).source := 𝔇.disc_subset_source i _ hy.1
  refine ⟨(𝔇.chart i).map_source hys, ?_⟩
  simpa [(𝔇.chart i).left_inv hys] using hy

/-- On overlaps the chart expressions differ by a holomorphic function, so they have the same
`∂̄`. -/
private theorem dbar_chartExpr_eq {g : 𝔇.LineCocycle} {ζ : ι → ι → M → ℂ}
    (hζ : 𝔇.IsCocycleOn g 𝔇.U'' ζ) {ψ : ι → M → ℝ} (hsum : ∀ x, ∑ k, ψ k x = 1)
    (hψs : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (ψ k)) (hsupp : ∀ k, tsupport (ψ k) ⊆ 𝔇.U'' k)
    {i k l : ι} {y : M} (hy : y ∈ 𝔇.W i ∩ (𝔇.U'' k ∩ 𝔇.U'' l)) :
    Complex.dbar (chartExpr 𝔇 g ψ ζ i k) (𝔇.chart i y) =
      Complex.dbar (chartExpr 𝔇 g ψ ζ i l) (𝔇.chart i y) := by
  set e := 𝔇.chart i
  have he : e ∈ atlas ℂ M := chart_mem_atlas ℂ _
  have hys : y ∈ e.source := 𝔇.disc_subset_source i _ hy.1
  set z := e y
  have hSo : IsOpen (𝔇.W i ∩ (𝔇.U'' k ∩ 𝔇.U'' l)) :=
    (𝔇.isOpen_W i).inter ((𝔇.isOpen_U'' k).inter (𝔇.isOpen_U'' l))
  have hN : e.target ∩ e.symm ⁻¹' (𝔇.W i ∩ (𝔇.U'' k ∩ 𝔇.U'' l)) ∈ 𝓝 z := by
    refine (e.isOpen_inter_preimage_symm hSo).mem_nhds ⟨e.map_source hys, ?_⟩
    simpa [z, e.left_inv hys] using hy
  set B : ℂ → ℂ := fun w => g i k (e.symm w) * ζ k l (e.symm w)
  have hB : DifferentiableAt ℂ B z := by
    have hWW : IsOpen (𝔇.W i ∩ 𝔇.W k) := (𝔇.isOpen_W i).inter (𝔇.isOpen_W k)
    have hUU : IsOpen (𝔇.U'' k ∩ 𝔇.U'' l) := (𝔇.isOpen_U'' k).inter (𝔇.isOpen_U'' l)
    have h1 := (differentiableOn_comp_symm he hWW (g.mdifferentiableOn i k)).differentiableAt
      (mem_of_superset hN fun w hw => ⟨hw.1, hw.2.1, 𝔇.U''_subset_W k hw.2.2.1⟩)
    have h2 := (differentiableOn_comp_symm he hUU (hζ.mdifferentiableOn k l)).differentiableAt
      (mem_of_superset hN fun w hw => ⟨hw.1, hw.2.2⟩)
    exact h1.mul h2
  have hA : DifferentiableAt ℝ (chartExpr 𝔇 g ψ ζ i k) z :=
    ((contDiffOn_chartExpr hζ hψs hsupp i k).differentiableOn (by simp)).differentiableAt
      ((isOpen_chartExpr_domain i k).mem_nhds (mem_chartExpr_domain ⟨hy.1, hy.2.1⟩))
  have hev : chartExpr 𝔇 g ψ ζ i l =ᶠ[𝓝 z] fun w => chartExpr 𝔇 g ψ ζ i k w - B w := by
    filter_upwards [hN] with w hw
    obtain ⟨hwt, hwi, hwk, hwl⟩ := hw
    have hsub := split_sub hζ hsum hsupp (i := k) (j := l) ⟨hwk, hwl⟩
    have hmul := g.mul_eq i k l (e.symm w)
      ⟨⟨hwi, 𝔇.U''_subset_W k hwk⟩, 𝔇.U''_subset_W l hwl⟩
    simp only [chartExpr, B]
    rw [hsub, ← hmul]
    change _ = g.toFun i k (e.symm w) * split ψ ζ k (e.symm w) -
      g.toFun i k (e.symm w) * (split ψ ζ k (e.symm w) - g.toFun k l (e.symm w) *
        split ψ ζ l (e.symm w))
    ring
  rw [dbar_congr hev, dbar_sub hA (hB.restrictScalars ℝ),
    Complex.dbar_eq_zero_of_differentiableAt hB,
    sub_zero]

/-- The form `form 𝔇 g ψ ζ i` is the `∂̄` of each chart expression on its domain. -/
private theorem form_eq {g : 𝔇.LineCocycle} {ζ : ι → ι → M → ℂ}
    (hζ : 𝔇.IsCocycleOn g 𝔇.U'' ζ) {ψ : ι → M → ℝ} (hsum : ∀ x, ∑ k, ψ k x = 1)
    (hψs : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (ψ k)) (hsupp : ∀ k, tsupport (ψ k) ⊆ 𝔇.U'' k)
    {i l : ι} {y : M} (hy : y ∈ 𝔇.W i ∩ 𝔇.U'' l) :
    form 𝔇 g ψ ζ i (𝔇.chart i y) = Complex.dbar (chartExpr 𝔇 g ψ ζ i l) (𝔇.chart i y) := by
  have hys : y ∈ (𝔇.chart i).source := 𝔇.disc_subset_source i _ hy.1
  unfold form
  rw [(𝔇.chart i).left_inv hys]
  have h1 : Complex.dbar (chartExpr 𝔇 g ψ ζ i l) (𝔇.chart i y) =
      ∑ k, (ψ k y : ℂ) * Complex.dbar (chartExpr 𝔇 g ψ ζ i l) (𝔇.chart i y) := by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum, Complex.ofReal_one, one_mul]
  rw [h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ψ k y = 0
  · simp [hk]
  have hyk : y ∈ 𝔇.U'' k := hsupp k (subset_tsupport _ hk)
  rw [dbar_chartExpr_eq hζ hsum hψs hsupp ⟨hy.1, hyk, hy.2⟩]

/-- The form is smooth on the largest coordinate disc. -/
private theorem contDiffOn_form {g : 𝔇.LineCocycle} {ζ : ι → ι → M → ℂ}
    (hζ : 𝔇.IsCocycleOn g 𝔇.U'' ζ) {ψ : ι → M → ℝ}
    (hψs : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (ψ k)) (hsupp : ∀ k, tsupport (ψ k) ⊆ 𝔇.U'' k)
    (i : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (form 𝔇 g ψ ζ i) (ball (𝔇.centreCoord i) (𝔇.ρ i)) := by
  set e := 𝔇.chart i
  intro z hz
  have hzt : z ∈ e.target := 𝔇.ball_subset_target i hz
  have hyW : e.symm z ∈ 𝔇.W i := by
    refine ⟨e.map_target hzt, ?_⟩
    change e (e.symm z) ∈ ball (𝔇.centreCoord i) (𝔇.ρ i)
    rw [e.right_inv hzt]
    exact hz
  apply ContDiffAt.contDiffWithinAt
  unfold form
  apply ContDiffAt.sum
  intro k _
  by_cases hk : e.symm z ∈ 𝔇.U'' k
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (ψ k (e.symm w) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z
        ((contDiffOn_comp_chartAt_symm (hψs k) _).contDiffAt (e.open_target.mem_nhds hzt))
    have hD := (contDiffOn_dbar (contDiffOn_chartExpr hζ hψs hsupp i k)
      (isOpen_chartExpr_domain i k))
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (Complex.dbar (chartExpr 𝔇 g ψ ζ i k)) z :=
      hD.contDiffAt ((isOpen_chartExpr_domain i k).mem_nhds ⟨hzt, hyW, hk⟩)
    exact h1.mul h2
  · have hnot : e.symm z ∉ tsupport (ψ k) := fun h => hk (hsupp k h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [comp_symm_eventually_eq_zero hzt hnot] with w hw
    change (ψ k (e.symm w) : ℂ) * _ = 0
    rw [hw]
    simp

end DiscCover

end Decomposition

private theorem bddAbove_image_iff' {α : Type*} {f : α → ℝ} {s : Set α} :
    BddAbove (f '' s) ↔ ∃ C, ∀ x ∈ s, f x ≤ C :=
  ⟨fun ⟨C, hC⟩ => ⟨C, fun x hx => hC (mem_image_of_mem _ hx)⟩,
    fun ⟨C, hC⟩ => ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩⟩

namespace DiscCover

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {ι : Type*}

/-- A function continuous on the coordinate disc of radius `ρ i` is bounded on the disc of
radius `s < ρ i`, read in the chart. -/
private theorem exists_bound_comp_chart (𝔇 : DiscCover M ι) {u : ℂ → ℂ} (hu : Continuous u)
    (i : ι) (s : ℝ) : ∃ C, ∀ x ∈ 𝔇.disc i s, ‖u (𝔇.chart i x)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (𝔇.centreCoord i) s).exists_bound_of_continuousOn
    hu.continuousOn
  exact ⟨C, fun x hx => hC _ (ball_subset_closedBall hx.2)⟩

/-- A transition function is bounded on the overlap of two smaller discs. -/
private theorem exists_bound_lineCocycle [T2Space M] {𝔇 : DiscCover M ι} (g : 𝔇.LineCocycle)
    (i j : ι) : ∃ C, ∀ x ∈ 𝔇.U' i ∩ 𝔇.U' j, ‖g i j x‖ ≤ C := by
  have hr : ∀ k, 𝔇.r' k < 𝔇.ρ k := fun k => (𝔇.r'_lt_r k).trans (𝔇.r_lt_ρ k)
  set K := (𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) (𝔇.r' i) ∩
    (𝔇.chart j).symm '' closedBall (𝔇.centreCoord j) (𝔇.r' j)
  have hK : IsCompact K := (𝔇.isCompact_symm_image_closedBall i (hr i).le).inter_right
    (𝔇.isCompact_symm_image_closedBall j (hr j).le).isClosed
  have hKW : K ⊆ 𝔇.W i ∩ 𝔇.W j := inter_subset_inter (𝔇.symm_image_closedBall_subset_W i (hr i))
    (𝔇.symm_image_closedBall_subset_W j (hr j))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((g.mdifferentiableOn i j).continuousOn.mono hKW)
  exact ⟨C, fun x hx => hC x ⟨𝔇.disc_subset_symm_image_closedBall i _ hx.1,
    𝔇.disc_subset_symm_image_closedBall j _ hx.2⟩⟩

/-- **Shrinking decomposition of a bounded line-bundle cocycle.** Let `g` be a holomorphic line
bundle on a finite disc cover `𝔇` of a Riemann surface, and `ζ` a bounded holomorphic
`1`-cocycle with values in `g` on the smallest discs `U''`. Then `ζ = ξ + δη` on `U''`, where
`ξ` is a holomorphic `1`-cocycle on the larger discs `U`, bounded on the discs `U'`, and `η` is
a bounded holomorphic `0`-cochain on `U''` (with `(δη) i j = η i - g i j * η j`). -/
theorem exists_decomposition [IsManifold 𝓘(ℂ) 1 M] [T2Space M] [Finite ι] (𝔇 : DiscCover M ι)
    (g : 𝔇.LineCocycle) {ζ : ι → ι → M → ℂ} (hζ : 𝔇.IsCocycleOn g 𝔇.U'' ζ)
    (hb : ∀ i j, BddAbove ((fun x => ‖ζ i j x‖) '' (𝔇.U'' i ∩ 𝔇.U'' j))) :
    ∃ (ξ : ι → ι → M → ℂ) (η : ι → M → ℂ), 𝔇.IsCocycleOn g 𝔇.U ξ ∧
      (∀ i j, BddAbove ((fun x => ‖ξ i j x‖) '' (𝔇.U' i ∩ 𝔇.U' j))) ∧
      (∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (η i) (𝔇.U'' i) ∧
        BddAbove ((fun x => ‖η i x‖) '' 𝔇.U'' i)) ∧
      ∀ i j, ∀ x ∈ 𝔇.U'' i ∩ 𝔇.U'' j, ζ i j x = ξ i j x + (η i x - g i j x * η j x) := by
  cases nonempty_fintype ι
  have := 𝔇.compactSpace
  have : IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) M := isManifold_real_smooth
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ 𝔇.U''
    𝔇.isOpen_U'' (by rw [𝔇.iUnion_U''_eq_univ])
  set ψf : ι → M → ℝ := fun k => ψ k
  have hsum : ∀ x, ∑ k, ψf k x = 1 := fun x => by
    rw [← finsum_eq_sum_of_fintype]
    exact ψ.sum_eq_one (mem_univ x)
  have hψs : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) (⊤ : ℕ∞) (ψf k) := fun k => (ψ k).contMDiff
  have hsupp : ∀ k, tsupport (ψf k) ⊆ 𝔇.U'' k := hψ
  have hb' : ∀ i j, ∃ C, ∀ x ∈ 𝔇.U'' i ∩ 𝔇.U'' j, ‖ζ i j x‖ ≤ C :=
    fun i j => bddAbove_image_iff'.1 (hb i j)
  have hex : ∀ i, ∃ u : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u ∧
      ∀ z ∈ ball (𝔇.centreCoord i) (𝔇.r i), Complex.dbar u z = form 𝔇 g ψf ζ i z :=
    fun i => Complex.exists_contDiff_dbar_eq_on_ball le_top (𝔇.r_lt_ρ i)
      (contDiffOn_form hζ hψs hsupp i)
  choose u hu hdu using hex
  set h := split ψf ζ
  set v : ι → M → ℂ := fun i x => u i (𝔇.chart i x)
  -- the key holomorphy statement
  have key : ∀ i l, ∀ x ∈ 𝔇.U i ∩ 𝔇.U'' l,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => v i y - g i l y * h l y) x := by
    intro i l x hx
    set e := 𝔇.chart i
    have hxs : x ∈ e.source := 𝔇.disc_subset_source i _ hx.1
    have hxW : x ∈ 𝔇.W i ∩ 𝔇.U'' l := ⟨𝔇.U_subset_W i hx.1, hx.2⟩
    have hA : DifferentiableAt ℝ (chartExpr 𝔇 g ψf ζ i l) (e x) :=
      ((contDiffOn_chartExpr hζ hψs hsupp i l).differentiableOn (by simp)).differentiableAt
        ((isOpen_chartExpr_domain i l).mem_nhds (mem_chartExpr_domain hxW))
    have hU : DifferentiableAt ℝ (u i) (e x) := ((hu i).differentiable (by simp)) _
    refine mdifferentiableAt_of_dbar_eq_zero (chart_mem_atlas ℂ _) hxs
      (G := fun w => u i w - chartExpr 𝔇 g ψf ζ i l w) ?_ (hU.sub hA) ?_
    · filter_upwards [e.open_target.mem_nhds (e.map_source hxs)] with w hw
      simp only [Function.comp_apply, v, chartExpr, h]
      change u i (e (e.symm w)) - _ = _
      rw [e.right_inv hw]
    · rw [dbar_sub hU hA, hdu i _ hx.1.2, form_eq hζ hsum hψs hsupp hxW, sub_self]
  refine ⟨fun i j x => v i x - g i j x * v j x, fun i x => h i x - v i x, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- `ξ` is holomorphic on `U i ∩ U j`
    intro i j x hx
    obtain ⟨l, hl⟩ := 𝔇.exists_mem_U'' x
    have hO : IsOpen (𝔇.W i ∩ 𝔇.W j ∩ 𝔇.W l) :=
      ((𝔇.isOpen_W i).inter (𝔇.isOpen_W j)).inter (𝔇.isOpen_W l)
    have hxO : x ∈ 𝔇.W i ∩ 𝔇.W j ∩ 𝔇.W l :=
      ⟨⟨𝔇.U_subset_W i hx.1, 𝔇.U_subset_W j hx.2⟩, 𝔇.U''_subset_W l hl⟩
    have hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (g i j) x :=
      (g.mdifferentiableOn i j x hxO.1).mdifferentiableAt
        (((𝔇.isOpen_W i).inter (𝔇.isOpen_W j)).mem_nhds hxO.1)
    have H := (key i l x ⟨hx.1, hl⟩).sub (hg.mul (key j l x ⟨hx.2, hl⟩))
    refine (H.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
    filter_upwards [hO.mem_nhds hxO] with y hy
    have hm := g.mul_eq i j l y hy
    simp only [Pi.sub_apply, Pi.mul_apply]
    change _ = _ - g.toFun i j y * (_ - g.toFun j l y * _)
    rw [← hm]
    ring
  · -- the cocycle identity
    intro i j k x hx
    have hm := g.mul_eq i j k x
      ⟨⟨𝔇.U_subset_W i hx.1.1, 𝔇.U_subset_W j hx.1.2⟩, 𝔇.U_subset_W k hx.2⟩
    change v i x - g.toFun i k x * v k x =
      (v i x - g.toFun i j x * v j x) + g.toFun i j x * (v j x - g.toFun j k x * v k x)
    rw [← hm]
    ring
  · -- `ξ` is bounded on `U' i ∩ U' j`
    intro i j
    obtain ⟨Ci, hCi⟩ := 𝔇.exists_bound_comp_chart (hu i).continuous i (𝔇.r' i)
    obtain ⟨Cj, hCj⟩ := 𝔇.exists_bound_comp_chart (hu j).continuous j (𝔇.r' j)
    obtain ⟨Cg, hCg⟩ := exists_bound_lineCocycle g i j
    refine bddAbove_image_iff'.2 ⟨Ci + Cg * Cj, fun x hx => ?_⟩
    have h1 := hCi x hx.1
    have h2 := hCj x hx.2
    have h3 := hCg x hx
    calc ‖v i x - g i j x * v j x‖ ≤ ‖v i x‖ + ‖g i j x‖ * ‖v j x‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ Ci + Cg * Cj := by
          refine add_le_add h1 (mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3))
  · -- `η` is holomorphic and bounded on `U'' i`
    intro i
    refine ⟨fun x hx => ?_, ?_⟩
    · have hxW : x ∈ 𝔇.W i := 𝔇.U''_subset_W i hx
      have H := (key i i x ⟨𝔇.U'_subset_U i (𝔇.U''_subset_U' i hx), hx⟩).neg
      refine (H.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
      filter_upwards [(𝔇.isOpen_W i).mem_nhds hxW] with y hy
      simp only [Pi.neg_apply]
      change h i y - v i y = -(v i y - g.toFun i i y * h i y)
      rw [g.apply_self hy]
      ring
    · obtain ⟨Ch, hCh⟩ := exists_norm_split_le hb' (fun k x => ψ.nonneg k x)
        (fun k x => ψ.le_one k x) hsupp i
      obtain ⟨Cv, hCv⟩ := 𝔇.exists_bound_comp_chart (hu i).continuous i (𝔇.r'' i)
      refine bddAbove_image_iff'.2 ⟨Ch + Cv, fun x hx => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add (hCh x hx) (hCv x hx))
  · -- the decomposition
    intro i j x hx
    rw [split_sub hζ hsum hsupp hx]
    ring

end DiscCover

/-- **Existence of disc covers.** On a compact Riemann surface, every open cover `V` is refined
by a finite disc cover, and for any point `p` the disc cover may be chosen with one disc centred
at `p` and with `p` outside the closure of every other disc. -/
theorem exists_discCover {M : Type u} [TopologicalSpace M] [ChartedSpace ℂ M] [CompactSpace M]
    [T2Space M] {ι₀ : Type*} (V : ι₀ → Set M) (hV : ∀ i, IsOpen (V i)) (hcov : ⋃ i, V i = univ)
    (p : M) :
    ∃ (ι : Type u) (_ : Fintype ι) (𝔇 : DiscCover M ι) (τ : ι → ι₀) (i₀ : ι),
      (∀ i, 𝔇.W i ⊆ V (τ i)) ∧ 𝔇.centre i₀ = p ∧ p ∈ 𝔇.U'' i₀ ∧
        ∀ j, j ≠ i₀ → p ∉ closure (𝔇.W j) := by
  classical
  have hτ : ∀ x, ∃ a, x ∈ V a := fun x => by
    simpa using (hcov.symm ▸ mem_univ x : x ∈ ⋃ i, V i)
  choose τ hτ using hτ
  set S : M → Set M := fun x => V (τ x) ∩ (if x = p then univ else {p}ᶜ)
  have hS : ∀ x, IsOpen (S x) := fun x => by
    refine (hV _).inter ?_
    split_ifs
    · exact isOpen_univ
    · exact isOpen_compl_singleton
  have hρ : ∀ x, ∃ ρ > 0, closedBall (chartAt ℂ x x) ρ ⊆
      (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' S x := by
    intro x
    have hmem : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' S x := by
      refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
      simp only [mem_preimage, (chartAt ℂ x).left_inv (mem_chart_source ℂ x), S]
      refine ⟨hτ x, ?_⟩
      split_ifs with h
      · exact mem_univ _
      · exact fun h' => h h'
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      ((chartAt ℂ x).isOpen_inter_preimage_symm (hS x)) _ hmem
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose ρ hρpos hρ using hρ
  set D : M → Set M := fun x =>
    (chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball (chartAt ℂ x x) (ρ x / 8)
  have hDo : ∀ x, IsOpen (D x) := fun x => (chartAt ℂ x).isOpen_inter_preimage isOpen_ball
  have hDx : ∀ x, x ∈ D x := fun x =>
    ⟨mem_chart_source ℂ x, mem_ball_self (by linarith [hρpos x])⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover D hDo
    (fun x _ => mem_iUnion.2 ⟨x, hDx x⟩)
  let 𝔇 : DiscCover M ↥(insert p t) :=
    { centre := Subtype.val
      ρ := fun i => ρ i
      r := fun i => ρ i / 2
      r' := fun i => ρ i / 4
      r'' := fun i => ρ i / 8
      r''_pos := fun i => by have := hρpos i.1; positivity
      r''_lt_r' := fun i => by have := hρpos i.1; linarith
      r'_lt_r := fun i => by have := hρpos i.1; linarith
      r_lt_ρ := fun i => by have := hρpos i.1; linarith
      closedBall_subset_target := fun i => (hρ i.1).trans inter_subset_left
      iUnion_eq_univ := by
        refine eq_univ_of_forall fun y => ?_
        obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht (mem_univ y))
        exact mem_iUnion.2 ⟨⟨x, Finset.mem_insert_of_mem hxt⟩, hyx⟩ }
  have hWsub : ∀ i, (𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) (𝔇.ρ i) ⊆ S i.1 := by
    rintro i _ ⟨z, hz, rfl⟩
    exact (hρ i.1 hz).2
  have hW : ∀ i, 𝔇.W i ⊆ (𝔇.chart i).symm '' closedBall (𝔇.centreCoord i) (𝔇.ρ i) :=
    fun i => 𝔇.disc_subset_symm_image_closedBall i _
  refine ⟨↥(insert p t), inferInstance, 𝔇, fun i => τ i.1, ⟨p, Finset.mem_insert_self p t⟩,
    fun i => (hW i).trans ((hWsub i).trans inter_subset_left), rfl, ?_, ?_⟩
  · exact ⟨mem_chart_source ℂ p, mem_ball_self (𝔇.r''_pos _)⟩
  · intro j hj hpj
    have hK := (𝔇.isCompact_symm_image_closedBall j le_rfl).isClosed
    have h1 := closure_minimal (hW j) hK hpj
    have h2 := (hWsub j h1).2
    have hjp : j.1 ≠ p := fun h => hj (Subtype.ext h)
    simp [hjp] at h2

end RiemannSurface
