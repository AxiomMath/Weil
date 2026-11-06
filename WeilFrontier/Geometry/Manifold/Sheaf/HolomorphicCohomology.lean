module

public import WeilFrontier.Geometry.Manifold.Sheaf.Holomorphic
public import WeilFrontier.Geometry.Manifold.Sheaf.SmoothSoft
public import WeilFrontier.Geometry.Manifold.Complex.Meromorphic
public import WeilFrontier.Geometry.Manifold.Complex.CechDolbeaultShrinking
public import WeilFrontier.Analysis.Complex.DolbeaultLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# The Dolbeault resolution and the cohomology of the structure sheaf of a Riemann surface

Let `M` be a Riemann surface, i.e. a complex manifold of dimension one (charted on `ℂ` with
holomorphic transition maps). Viewed as a real manifold it is `C^∞`, and besides the sheaf `𝒪_M`
of holomorphic functions it carries the sheaf `ℰ_M` of real smooth functions `U → ℂ` and the sheaf
`ℰ_M^{0,1}` of smooth `(0,1)`-forms. The Cauchy–Riemann operator `∂̄ : ℰ_M → ℰ_M^{0,1}` reads
`f ↦ ∂(f ∘ z⁻¹)/∂z̄ dz̄` in a chart `z`; since transition maps are holomorphic, the coefficients
of `∂̄f` in two charts differ by the nowhere vanishing factor `conj τ'`, `τ` the transition map.

The *Dolbeault sequence* `0 ⟶ 𝒪_M ⟶ ℰ_M ⟶ ℰ_M^{0,1} ⟶ 0` is a short exact sequence of
abelian sheaves:
* a real smooth function with `∂̄f = 0` is holomorphic (Cauchy–Riemann), so the kernel of `∂̄`
  is `𝒪_M`;
* `∂̄` is locally surjective: a smooth `(0,1)`-form is locally `∂̄` of a smooth function.

Both `ℰ_M` and `ℰ_M^{0,1}` are sheaves of modules over the sheaf of real smooth functions, hence
acyclic when `M` is compact (partitions of unity make them soft). The long exact cohomology
sequence then gives `Hᵠ(M, 𝒪_M) = 0` for `q ≥ 2` and identifies `H¹(M, 𝒪_M)` with the cokernel
of `∂̄` on global sections.

## Main definitions

* `RiemannSurface.dbarCoeff g x`: the coefficient of `∂̄g` at `x` with respect to `dz̄`, `z` the
  preferred chart at `x`.
* `RiemannSurface.dbarForms M U`: the smooth `(0,1)`-forms on `U`, as a module over the real
  smooth functions on `U`; `RiemannSurface.dbarFormsSheaf M` is the corresponding sheaf of modules
  over `RiemannSurface.smoothRingSheaf M`.
* `RiemannSurface.smoothFunctionsSheafAb M`, `RiemannSurface.dbarFormsSheafAb M`: the abelian
  sheaves `ℰ_M` and `ℰ_M^{0,1}`.
* `RiemannSurface.holomorphicToSmooth M : 𝒪_M ⟶ ℰ_M` and
  `RiemannSurface.dbarSheafHom M : ℰ_M ⟶ ℰ_M^{0,1}`, and the short complex
  `RiemannSurface.dolbeaultSequence M`.
* `RiemannSurface.dolbeaultConnecting M : Γ(M, ℰ_M^{0,1}) →+ H¹(M, 𝒪_M)`.

## Main results

* `RiemannSurface.dbar_comp_of_differentiableAt`: the chain rule for `∂/∂z̄` under a holomorphic
  change of variables, and `RiemannSurface.dbarCoeff_eq_of_mem_atlas`, the change of chart for
  `∂̄`.
* `RiemannSurface.contMDiff_iff_mdifferentiable`: on a Riemann surface the complex `C^∞`
  functions (the sections of `𝒪_M`) are exactly the holomorphic ones.
* `RiemannSurface.contMDiffAt_of_eventually_dbarCoeff_eq_zero`: the Cauchy–Riemann equation.
* `RiemannSurface.exists_dbarCoeff_eq_mul`: local solvability of `∂̄h = a ∂̄g`.
* `RiemannSurface.dolbeaultSequence_shortExact`: the Dolbeault sequence is short exact.
* `RiemannSurface.subsingleton_H_holomorphicSheafAb`: `Hᵠ(M, 𝒪_M) = 0` for `q ≥ 2`, `M` compact.
* `RiemannSurface.dolbeaultConnecting_surjective`,
  `RiemannSurface.dolbeaultConnecting_eq_zero_iff`: `H¹(M, 𝒪_M) ≅ Γ(M, ℰ^{0,1}) / ∂̄ Γ(M, ℰ)`.

## Implementation notes

A `(0,1)`-form `ω` on `U` is recorded by the function `x ↦ ω_x(∂/∂x)` of its coefficients in the
preferred charts `chartAt ℂ x`; this function is not continuous in general, as the preferred chart
jumps. Smoothness of the form is encoded by asking that `ω` be, near every point, `∂̄` of a real
smooth function. By the Dolbeault lemma (`Complex.exists_contDiff_dbar_eq_on_half_ball`) this is
the usual notion: in a chart `z`, `φ dz̄` with `φ` smooth is locally `∂̄u` for `∂u/∂z̄ = φ`. With
this model the sheaf property is a local predicate, `∂̄` is locally surjective by definition, and
the Dolbeault lemma is what makes the forms a module over the smooth functions.

Holomorphic functions are the complex `C^∞` functions of `ComplexManifold.holomorphicSheafAb`;
only `C¹` holomorphic transition maps are assumed, the real `C^∞` structure being
`RiemannSurface.isManifold_real_smooth`.

## References

* [O. Forster, *Lectures on Riemann Surfaces*][forster1981], §§13–15.
* [L. Hörmander, *An introduction to complex analysis in several variables*][hormander1966].
-/

@[expose] public section

open Set Filter Topology Complex
open scoped Manifold ContDiff ComplexConjugate

noncomputable section

namespace RiemannSurface

/-! ### The Wirtinger derivative and holomorphic changes of variables -/

section Dbar

theorem dbar_congr' {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  simp only [dbar, h.fderiv_eq]

theorem dbar_add' {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  simp only [dbar, fderiv_fun_add hf hg]
  simp only [smul_eq_mul, add_apply]
  ring

theorem dbar_neg' (f : ℂ → ℂ) (z : ℂ) : dbar (fun w => -f w) z = -dbar f z := by
  simp only [dbar, fderiv_fun_neg]
  simp only [smul_eq_mul, neg_apply]
  ring

theorem dbar_const' (c z : ℂ) : dbar (fun _ => c) z = 0 := by
  simp [dbar]

/-- A real-linear map `ℂ → ℂ` is determined by its values at `1` and `I`. -/
theorem clm_apply_eq_re_im' (L : ℂ →L[ℝ] ℂ) (v : ℂ) : L v = v.re * L 1 + v.im * L I := by
  have hv : v = (v.re : ℝ) • (1 : ℂ) + (v.im : ℝ) • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hv, map_add, map_smul, map_smul]
  simp [Complex.real_smul]

/-- **Chain rule for `∂/∂z̄` under a holomorphic change of variables**:
`∂(h ∘ τ)/∂z̄ (p) = conj (τ' p) · ∂h/∂z̄ (τ p)` for `τ` complex differentiable at `p`. -/
theorem dbar_comp_of_differentiableAt {h τ : ℂ → ℂ} {p : ℂ} (hτ : DifferentiableAt ℂ τ p)
    (hh : DifferentiableAt ℝ h (τ p)) :
    dbar (h ∘ τ) p = conj (deriv τ p) * dbar h (τ p) := by
  have hτ' : HasFDerivAt τ ((fderiv ℂ τ p).restrictScalars ℝ) p :=
    hτ.hasFDerivAt.restrictScalars ℝ
  rw [dbar, dbar, fderiv_comp p hh hτ'.differentiableAt, hτ'.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', smul_eq_mul]
  have h1 : fderiv ℂ τ p 1 = deriv τ p := rfl
  have hI : fderiv ℂ τ p I = I * deriv τ p := by
    rw [← h1, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [h1, hI, clm_apply_eq_re_im' _ (deriv τ p), clm_apply_eq_re_im' _ (I * deriv τ p)]
  have hre : (I * deriv τ p).re = -(deriv τ p).im := by simp
  have him : (I * deriv τ p).im = (deriv τ p).re := by simp
  rw [hre, him]
  have hc : conj (deriv τ p) = ((deriv τ p).re : ℂ) - ((deriv τ p).im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hc]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- Holomorphy from the Cauchy–Riemann equation `∂f/∂z̄ = 0`. -/
theorem differentiableAt_of_dbar_eq_zero' {f : ℂ → ℂ} {z : ℂ}
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
    rw [clm_apply_eq_re_im' L v, hI]
    conv_rhs => rw [show v = (v.re : ℂ) + (v.im : ℂ) * I from (re_add_im v).symm]
    ring
  refine (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt
    (f' := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (L 1)) ?_).differentiableAt
  ext1 v
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, smul_eq_mul]
  rw [← hL]
  exact (hv v).symm

theorem contDiffOn_dbar' {f : ℂ → ℂ} {s : Set ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
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


/-! ### `∂̄` on a Riemann surface, in the preferred charts -/

section Charts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The coefficient of `∂̄g` at `x` with respect to `dz̄`, `z` being the preferred chart at `x`:
`∂(g ∘ z⁻¹)/∂z̄ (z x)`. -/
def dbarCoeff (g : M → ℂ) (x : M) : ℂ :=
  dbar (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

/-- Smoothness of a `ℂ`-valued function on a manifold modelled on `ℂ` (over `𝕜 = ℝ` or `ℂ`) is
smoothness in the preferred chart. -/
theorem contMDiffAt_iff_contDiffAt_chartAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedAlgebra 𝕜 ℂ] {n : ℕ∞ω} {f : M → ℂ} {x : M} :
    ContMDiffAt 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) n f x ↔
      ContinuousAt f x ∧ ContDiffAt 𝕜 n (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
  rw [contMDiffAt_iff]
  simp [extChartAt, contDiffWithinAt_univ, Function.comp_def, chartAt_self_eq]

/-- A holomorphic function is real smooth. -/
theorem ContMDiffAt.real_of_complex {n : ℕ∞ω} {f : M → ℂ} {x : M}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n f x) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f x := by
  rw [contMDiffAt_iff_contDiffAt_chartAt] at hf ⊢
  exact ⟨hf.1, hf.2.restrict_scalars ℝ⟩

/-- A holomorphic function has vanishing `∂̄`. -/
theorem dbarCoeff_eq_zero_of_contMDiffAt {n : ℕ∞ω} (hn : n ≠ 0) {f : M → ℂ} {x : M}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n f x) : dbarCoeff f x = 0 := by
  rw [contMDiffAt_iff_contDiffAt_chartAt] at hf
  exact dbar_eq_zero_of_differentiableAt (hf.2.differentiableAt hn)

theorem differentiableAt_chartAt_of_contMDiffAt {f : M → ℂ} {x : M}
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x) :
    DifferentiableAt ℝ (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  ((contMDiffAt_iff_contDiffAt_chartAt.1 hf).2).differentiableAt (by simp)

theorem dbarCoeff_add {f g : M → ℂ} {x : M} (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x)
    (hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g x) :
    dbarCoeff (f + g) x = dbarCoeff f x + dbarCoeff g x :=
  dbar_add' (differentiableAt_chartAt_of_contMDiffAt hf)
    (differentiableAt_chartAt_of_contMDiffAt hg)

theorem dbarCoeff_neg (f : M → ℂ) (x : M) : dbarCoeff (-f) x = -dbarCoeff f x :=
  dbar_neg' _ _

theorem dbarCoeff_zero (x : M) : dbarCoeff (0 : M → ℂ) x = 0 :=
  dbar_const' 0 _

theorem dbarCoeff_congr {f g : M → ℂ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    dbarCoeff f x = dbarCoeff g x := by
  apply dbar_congr'
  have hc : Tendsto (chartAt ℂ x).symm (𝓝 (chartAt ℂ x x)) (𝓝 x) := by
    have := (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    rwa [ContinuousAt, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at this
  exact hc.eventually h

variable [IsManifold 𝓘(ℂ) 1 M]

/-- A real smooth function is real smooth in every chart of the atlas. -/
theorem contDiffAt_comp_symm_of_contMDiffAt {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ atlas ℂ M) {f : M → ℂ} {y : M} (hy : y ∈ e.source)
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f y) : ContDiffAt ℝ ∞ (f ∘ e.symm) (e y) := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_smooth
  have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.symm (e y) :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) (e.map_source hy)
  rw [← e.left_inv hy] at hf
  exact contMDiffAt_iff_contDiffAt.1 (hf.comp (e y) h1)

/-- A function real smooth in a chart is real smooth on the manifold. -/
theorem contMDiffAt_comp_of_contDiffAt {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ atlas ℂ M) {u : ℂ → ℂ} {y : M} (hy : y ∈ e.source)
    (hu : ContDiffAt ℝ ∞ u (e y)) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (u ∘ e) y := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_smooth
  exact hu.contMDiffAt.comp y
    (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy)

/-- **Change of chart for `∂̄`**: in a chart `e` of the atlas, the coefficient of `∂̄g` at `x`
is `conj τ' · ∂(g ∘ e⁻¹)/∂z̄ (e x)`, where `τ` is the transition map from the preferred chart at
`x` to `e`. -/
theorem dbarCoeff_eq_of_mem_atlas {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    {g : M → ℂ} {x : M} (hx : x ∈ e.source)
    (hg : DifferentiableAt ℝ (g ∘ e.symm) (e x)) :
    dbarCoeff g x =
      conj (deriv (e ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) * dbar (g ∘ e.symm) (e x) := by
  have hx' := mem_chart_source ℂ x
  rw [dbarCoeff, dbar_congr' (comp_symm_eventuallyEq hx hx' g)]
  have hτ := (analyticAt_transition he (chart_mem_atlas ℂ x) hx hx').differentiableAt
  rw [dbar_comp_of_differentiableAt hτ, transition_apply hx']
  rwa [transition_apply hx']

/-- The transition factor in `dbarCoeff_eq_of_mem_atlas` does not vanish. -/
theorem conj_deriv_transition_ne_zero {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M)
    {x : M} (hx : x ∈ e.source) :
    conj (deriv (e ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) ≠ 0 := by
  rw [map_ne_zero]
  exact deriv_transition_ne_zero he (chart_mem_atlas ℂ x) hx (mem_chart_source ℂ x)

/-- **Cauchy–Riemann on a Riemann surface**: a real smooth function with `∂̄g = 0` near `x` is
holomorphic at `x`. -/
theorem contMDiffAt_of_eventually_dbarCoeff_eq_zero {g : M → ℂ} {x : M}
    (hg : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g y ∧ dbarCoeff g y = 0) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ g x := by
  have hmd : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g y := by
    filter_upwards [hg] with y hy
    exact (mdifferentiableAt_iff_differentiableAt_of_mem_atlas (chart_mem_atlas ℂ y)
      (mem_chart_source ℂ y)).2
      (differentiableAt_of_dbar_eq_zero' (differentiableAt_chartAt_of_contMDiffAt hy.1) hy.2)
  have ha := analyticAt_comp_symm_of_eventually_mdifferentiableAt (chart_mem_atlas ℂ x)
    (mem_chart_source ℂ x) hmd
  rw [contMDiffAt_iff_contDiffAt_chartAt]
  exact ⟨hmd.self_of_nhds.continuousAt, ha.contDiffAt⟩

/-- **Holomorphic functions are smooth**: on a complex manifold of dimension one, a
complex differentiable function is complex `C^∞`. -/
theorem contMDiffAt_of_eventually_mdifferentiableAt {g : M → ℂ} {x : M}
    (hg : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g y) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ g x := by
  have ha := analyticAt_comp_symm_of_eventually_mdifferentiableAt (chart_mem_atlas ℂ x)
    (mem_chart_source ℂ x) hg
  rw [contMDiffAt_iff_contDiffAt_chartAt]
  exact ⟨hg.self_of_nhds.continuousAt, ha.contDiffAt⟩

/-- On a Riemann surface the sections of the holomorphic structure sheaf, the complex `C^∞`
functions, are exactly the holomorphic (complex differentiable) functions. -/
theorem contMDiff_iff_mdifferentiable {g : M → ℂ} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ g ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g :=
  ⟨fun h => h.mdifferentiable (by simp),
    fun h x => contMDiffAt_of_eventually_mdifferentiableAt (Eventually.of_forall h)⟩

/-- **Local solvability of `∂̄h = a ∂̄g`.** Given functions `a`, `g` real smooth near `x`, there
is `h` real smooth near `x` with `∂̄h = a · ∂̄g` near `x`. -/
theorem exists_dbarCoeff_eq_mul {a g : M → ℂ} {x : M}
    (ha : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ a y)
    (hg : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g y) :
    ∃ h : M → ℂ, (∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ h y) ∧
      ∀ᶠ y in 𝓝 x, dbarCoeff h y = a y * dbarCoeff g y := by
  set e := chartAt ℂ x with he_def
  have he : e ∈ atlas ℂ M := chart_mem_atlas ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.1 (ha.and hg)
  set S : Set ℂ := e.target ∩ e.symm ⁻¹' V with hS_def
  have hSo : IsOpen S := e.isOpen_inter_preimage_symm hVo
  have hxS : e x ∈ S := ⟨e.map_source hx, by rw [mem_preimage, e.left_inv hx]; exact hxV⟩
  have hsm : ∀ z ∈ S, ContDiffAt ℝ ∞ (a ∘ e.symm) z ∧ ContDiffAt ℝ ∞ (g ∘ e.symm) z := by
    intro z hz
    have hzs : e.symm z ∈ e.source := e.map_target hz.1
    have h1 := contDiffAt_comp_symm_of_contMDiffAt he hzs (hV hz.2).1
    have h2 := contDiffAt_comp_symm_of_contMDiffAt he hzs (hV hz.2).2
    rw [e.right_inv hz.1] at h1 h2
    exact ⟨h1, h2⟩
  set G : ℂ → ℂ := fun z => a (e.symm z) * dbar (g ∘ e.symm) z with hG_def
  have hGS : ContDiffOn ℝ (⊤ : ℕ∞) G S := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (a ∘ e.symm) S := fun z hz =>
      (hsm z hz).1.contDiffWithinAt
    have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (g ∘ e.symm) S := fun z hz =>
      (hsm z hz).2.contDiffWithinAt
    exact h1.mul (contDiffOn_dbar' h2 hSo)
  obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hSo (e x) hxS
  obtain ⟨u, hu, hdu⟩ := exists_contDiff_dbar_eq_on_half_ball (n := ⊤) le_top (hGS.mono hrS)
  refine ⟨u ∘ e, ?_, ?_⟩
  · filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact contMDiffAt_comp_of_contDiffAt he hy hu.contDiffAt
  · have hball : e.source ∩ e ⁻¹' Metric.ball (e x) (r / 2) ∈ 𝓝 x :=
      (e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hx, Metric.mem_ball_self (by linarith)⟩
    filter_upwards [hball, hVo.mem_nhds hxV] with y hy hyV
    have hey : e y ∈ S := ⟨e.map_source hy.1, by rw [mem_preimage, e.left_inv hy.1]; exact hyV⟩
    have hloc : (u ∘ e) ∘ e.symm =ᶠ[𝓝 (e y)] u := by
      filter_upwards [e.open_target.mem_nhds (e.map_source hy.1)] with z hz
      simp [e.right_inv hz]
    have hdiff : DifferentiableAt ℝ ((u ∘ e) ∘ e.symm) (e y) :=
      ((hu.differentiable (by simp)) (e y)).congr_of_eventuallyEq hloc
    rw [dbarCoeff_eq_of_mem_atlas he hy.1 hdiff,
      dbarCoeff_eq_of_mem_atlas he hy.1 ((hsm _ hey).2.differentiableAt (by simp)),
      dbar_congr' hloc, hdu _ hy.2]
    simp only [hG_def, e.left_inv hy.1]
    ring

end Charts

/-! ### The Dolbeault sequence of sheaves -/

section Sheaves

open CategoryTheory TopologicalSpace Opposite TopCat

variable (M : Type) [TopologicalSpace M]

open Classical in
/-- Extension by zero of a function on an open subset. -/
def extendByZero {U : Opens M} (f : U → ℂ) : M → ℂ :=
  fun y => if h : y ∈ U then f ⟨y, h⟩ else 0

variable {M} in
theorem extendByZero_of_mem {U : Opens M} (f : U → ℂ) {y : M} (hy : y ∈ U) :
    extendByZero M f y = f ⟨y, hy⟩ := by
  simp [extendByZero, hy]

variable {M} in
theorem extendByZero_comp_val {U : Opens M} (f : U → ℂ) :
    (fun y : U => extendByZero M f y) = f :=
  funext fun y => extendByZero_of_mem f y.2

variable {M} in
theorem extendByZero_eventuallyEq {U : Opens M} (f : U → ℂ) {y : M} (hy : y ∈ U) (g : M → ℂ)
    (hfg : ∀ z : U, f z = g z) : extendByZero M f =ᶠ[𝓝 y] g := by
  filter_upwards [U.isOpen.mem_nhds hy] with z hz
  rw [extendByZero_of_mem f hz, hfg]

variable {M} in
theorem extendByZero_add {U : Opens M} (f g : U → ℂ) :
    extendByZero M (f + g) = extendByZero M f + extendByZero M g := by
  funext z
  by_cases hz : z ∈ U <;> simp [extendByZero, hz]

variable [ChartedSpace ℂ M]

variable {M} in
theorem contMDiffAt_extendByZero {𝕜 : Type} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {n : ℕ∞ω} {U : Opens M} {f : U → ℂ} {x : U}
    (hf : ContMDiffAt 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) n f x) :
    ContMDiffAt 𝓘(𝕜, ℂ) 𝓘(𝕜, ℂ) n (extendByZero M f) x :=
  contMDiffAt_subtype_iff.1 (by rwa [extendByZero_comp_val])

/-- The sheaf of rings of real `C^∞` functions `U → ℂ` on a Riemann surface. -/
abbrev smoothRingSheaf : Sheaf (Opens.grothendieckTopology (TopCat.of M)) RingCat.{0} :=
  (sheafCompose (Opens.grothendieckTopology (TopCat.of M)) (forget₂ CommRingCat RingCat)).obj
    (smoothSheafCommRing 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) M ℂ)

/-- The local predicate defining smooth `(0,1)`-forms: a function `φ : U → ℂ` (the coefficient
of the form with respect to `dz̄`, `z` the preferred chart at each point) is near every point the
`∂̄` of a real smooth function. -/
def dbarFormPredicate : LocalPredicate (fun _ : TopCat.of M => ℂ) where
  pred {U} φ := ∀ x : U, ∃ g : M → ℂ, ∀ᶠ y in 𝓝 (x : M),
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g y ∧ ∀ hy : y ∈ U, φ ⟨y, hy⟩ = dbarCoeff g y
  res {U V} i φ h x := by
    obtain ⟨g, hg⟩ := h ⟨x.1, i.le x.2⟩
    exact ⟨g, hg.mono fun y hy => ⟨hy.1, fun hyU => hy.2 (i.le hyU)⟩⟩
  locality {U} φ h x := by
    obtain ⟨V, hxV, i, hV⟩ := h x
    obtain ⟨g, hg⟩ := hV ⟨x, hxV⟩
    refine ⟨g, ?_⟩
    filter_upwards [hg, V.isOpen.mem_nhds hxV] with y hy hyV
    exact ⟨hy.1, fun hyU => hy.2 hyV⟩

variable {M}

/-- Smooth functions act on functions `U → ℂ` by pointwise multiplication. -/
@[reducible] def smoothFunctionsModule (U : Opens M) :
    Module C^∞⟮𝓘(ℝ, ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ (U → ℂ) :=
  Module.compHom _ (ContMDiffMap.coeFnRingHom (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)) (n := ∞))

attribute [local instance] smoothFunctionsModule

variable [IsManifold 𝓘(ℂ) 1 M]

variable (M) in
/-- The smooth `(0,1)`-forms on an open subset `U` of a Riemann surface, as a module over the
smooth functions on `U`. A form is recorded by its coefficient with respect to `dz̄`, `z` the
preferred chart at each point. -/
def dbarForms (U : Opens M) : Submodule C^∞⟮𝓘(ℝ, ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ (U → ℂ) where
  carrier := {φ | (dbarFormPredicate M).pred (U := U) φ}
  zero_mem' x := ⟨0, Eventually.of_forall fun y =>
    ⟨contMDiffAt_const, fun _ => (dbarCoeff_zero y).symm⟩⟩
  add_mem' {φ ψ} hφ hψ x := by
    obtain ⟨g, hg⟩ := hφ x
    obtain ⟨h, hh⟩ := hψ x
    refine ⟨g + h, ?_⟩
    filter_upwards [hg, hh] with y hy hy'
    refine ⟨hy.1.add hy'.1, fun hyU => ?_⟩
    rw [dbarCoeff_add hy.1 hy'.1, ← hy.2 hyU, ← hy'.2 hyU]
    rfl
  smul_mem' a {φ} hφ x := by
    obtain ⟨g, hg⟩ := hφ x
    have ha : ∀ᶠ y in 𝓝 (x : M), ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (extendByZero M a) y := by
      filter_upwards [U.isOpen.mem_nhds x.2] with y hy
      exact contMDiffAt_extendByZero (x := ⟨y, hy⟩) (a.contMDiff _)
    obtain ⟨h, hh, hdh⟩ := exists_dbarCoeff_eq_mul ha (hg.mono fun y hy => hy.1)
    refine ⟨h, ?_⟩
    filter_upwards [hh, hdh, hg] with y hy hy' hy''
    refine ⟨hy, fun hyU => ?_⟩
    rw [hy', ← hy''.2 hyU, extendByZero_of_mem _ hyU]
    rfl

variable (M) in
/-- The presheaf of smooth `(0,1)`-forms, as a presheaf of abelian groups. -/
def dbarFormsPresheaf : (Opens (TopCat.of M))ᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj U := AddCommGrpCat.of (dbarForms M U.unop)
  map {_ _} i := AddCommGrpCat.ofHom
    { toFun := fun φ => ⟨fun x => φ.1 ⟨x.1, i.unop.le x.2⟩,
        (dbarFormPredicate M).res i.unop φ.1 φ.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ((smoothRingSheaf M).obj.obj U) ((dbarFormsPresheaf M).obj U) :=
  inferInstanceAs (Module C^∞⟮𝓘(ℝ, ℂ), U.unop; 𝓘(ℝ, ℂ), ℂ⟯ (dbarForms M U.unop))

variable (M) in
/-- The presheaf of smooth `(0,1)`-forms, as a presheaf of modules over the smooth functions. -/
def dbarFormsPresheafOfModules : PresheafOfModules (smoothRingSheaf M).obj :=
  PresheafOfModules.ofPresheaf (dbarFormsPresheaf M) (fun _ _ _ _ _ => rfl)

/-- The underlying presheaf of types of `dbarFormsPresheaf` is the presheaf of functions
satisfying `dbarFormPredicate`. -/
def dbarFormsPresheafForgetIso :
    dbarFormsPresheaf M ⋙ CategoryTheory.forget AddCommGrpCat ≅
      subpresheafToTypes (dbarFormPredicate M).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ => Equiv.toIso
    { toFun := fun φ => ⟨φ.1, φ.2⟩
      invFun := fun φ => ⟨φ.1, φ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (fun _ => rfl)

variable (M) in
/-- The sheaf of smooth `(0,1)`-forms on a Riemann surface, as a sheaf of modules over the
sheaf of smooth functions. -/
def dbarFormsSheaf : SheafOfModules (smoothRingSheaf M) where
  val := dbarFormsPresheafOfModules M
  isSheaf := by
    change Presheaf.IsSheaf _ (dbarFormsPresheaf M)
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat),
      CategoryTheory.Presheaf.isSheaf_of_iso_iff dbarFormsPresheafForgetIso]
    exact (subsheafToTypes (dbarFormPredicate M)).property

variable (M) in
/-- The sheaf of real `C^∞` functions with values in `ℂ`, as an abelian sheaf (the underlying
abelian sheaf of the free module of rank one over `smoothRingSheaf M`). -/
abbrev smoothFunctionsSheafAb :
    Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (smoothRingSheaf M)).obj (SheafOfModules.unit (smoothRingSheaf M))

variable (M) in
/-- The sheaf of smooth `(0,1)`-forms, as an abelian sheaf. -/
abbrev dbarFormsSheafAb : Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (smoothRingSheaf M)).obj (dbarFormsSheaf M)

/-- The inclusion of holomorphic functions on `U` into real smooth functions. -/
def holomorphicToSmoothHom (U : Opens M) :
    C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂ⟯ →+ C^∞⟮𝓘(ℝ, ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun f := ⟨f, fun x => ContMDiffAt.real_of_complex (f.contMDiff x)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (M) in
/-- The inclusion of holomorphic functions into real smooth functions. -/
def holomorphicToSmooth :
    ComplexManifold.holomorphicSheafAb 𝓘(ℂ) M ⟶ smoothFunctionsSheafAb M :=
  ObjectProperty.homMk
  { app := fun U => AddCommGrpCat.ofHom (holomorphicToSmoothHom U.unop)
    naturality := fun _ _ _ => rfl }

/-- `∂̄` on the smooth functions on `U`. -/
def dbarHom (U : Opens M) : C^∞⟮𝓘(ℝ, ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ →+ dbarForms M U where
  toFun f := ⟨fun y => dbarCoeff (extendByZero M f) y, fun x => ⟨extendByZero M f, by
      filter_upwards [U.isOpen.mem_nhds x.2] with y hy
      exact ⟨contMDiffAt_extendByZero (x := ⟨y, hy⟩) (f.contMDiff _), fun _ => rfl⟩⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext y
    have : extendByZero M (0 : U → ℂ) = 0 := by
      funext z
      by_cases hz : z ∈ U <;> simp [extendByZero, hz]
    change dbarCoeff (extendByZero M (0 : U → ℂ)) y = 0
    rw [this, dbarCoeff_zero]
  map_add' f g := by
    apply Subtype.ext
    funext y
    change dbarCoeff (extendByZero M (⇑f + ⇑g)) y =
      dbarCoeff (extendByZero M f) y + dbarCoeff (extendByZero M g) y
    rw [extendByZero_add]
    exact dbarCoeff_add (contMDiffAt_extendByZero (f.contMDiff y))
      (contMDiffAt_extendByZero (g.contMDiff y))

theorem dbarHom_apply (U : Opens M) (f : C^∞⟮𝓘(ℝ, ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯) (y : U) :
    (dbarHom U f).1 y = dbarCoeff (extendByZero M f) y := rfl

variable (M) in
/-- The Cauchy–Riemann operator `∂̄` from smooth functions to smooth `(0,1)`-forms, as a
morphism of abelian sheaves. -/
def dbarSheafHom : smoothFunctionsSheafAb M ⟶ dbarFormsSheafAb M :=
  ObjectProperty.homMk
  { app := fun U => AddCommGrpCat.ofHom (dbarHom U.unop)
    naturality := fun U V i => by
      ext f
      apply Subtype.ext
      funext y
      let f' : C^∞⟮𝓘(ℝ, ℂ), U.unop; 𝓘(ℝ, ℂ), ℂ⟯ := f
      change dbarCoeff (extendByZero M (fun z : V.unop => f' ⟨z.1, i.unop.le z.2⟩)) y =
        dbarCoeff (extendByZero M f') y
      exact dbarCoeff_congr (extendByZero_eventuallyEq _ y.2 _
        fun z => (extendByZero_of_mem f' _).symm) }

variable (M) in
theorem holomorphicToSmooth_comp_dbarSheafHom : holomorphicToSmooth M ≫ dbarSheafHom M = 0 := by
  ext U f
  apply Subtype.ext
  funext y
  let f' : C^∞⟮𝓘(ℂ), U.unop; 𝓘(ℂ), ℂ⟯ := f
  change dbarCoeff (extendByZero M f') y = 0
  exact dbarCoeff_eq_zero_of_contMDiffAt (by simp) (contMDiffAt_extendByZero (f'.contMDiff y))

variable (M) in
/-- The **Dolbeault sequence** `0 ⟶ 𝒪_M ⟶ ℰ_M ⟶ ℰ_M^{0,1} ⟶ 0` of a Riemann surface: holomorphic
functions, real smooth functions and smooth `(0,1)`-forms, the second map being `∂̄`. -/
def dolbeaultSequence :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0}) :=
  ShortComplex.mk (holomorphicToSmooth M) (dbarSheafHom M) (holomorphicToSmooth_comp_dbarSheafHom M)

variable (M) in
/-- The inclusion of holomorphic functions into smooth functions is a monomorphism. -/
instance mono_holomorphicToSmooth : Mono (holomorphicToSmooth M) := by
  have : Mono ((sheafToPresheaf _ _).map (holomorphicToSmooth M)) := by
    have hU : ∀ U, Mono (((sheafToPresheaf _ _).map (holomorphicToSmooth M)).app U) := by
      intro U
      rw [AddCommGrpCat.mono_iff_injective]
      intro f g hfg
      let f' : C^∞⟮𝓘(ℂ), U.unop; 𝓘(ℂ), ℂ⟯ := f
      let g' : C^∞⟮𝓘(ℂ), U.unop; 𝓘(ℂ), ℂ⟯ := g
      change f' = g'
      have h : holomorphicToSmoothHom U.unop f' = holomorphicToSmoothHom U.unop g' := hfg
      exact ContMDiffMap.ext fun x =>
        congrArg (fun k : C^∞⟮𝓘(ℝ, ℂ), U.unop; 𝓘(ℝ, ℂ), ℂ⟯ => k x) h
    exact NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

variable (M) in
/-- `∂̄` is an epimorphism of sheaves: every smooth `(0,1)`-form is locally `∂̄` of a smooth
function. -/
instance epi_dbarSheafHom : Epi (dbarSheafHom M) := by
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi (X := TopCat.of M) (dbarSheafHom M)).mp ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  let t' : dbarForms M U := t
  obtain ⟨g, hg⟩ := t'.2 ⟨x, hx⟩
  obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.1 hg
  let V : Opens M := U ⊓ ⟨W, hWo⟩
  refine ⟨V, inf_le_left, ⟨(⟨fun y : V => g y, fun y => ?_⟩ : C^∞⟮𝓘(ℝ, ℂ), V; 𝓘(ℝ, ℂ), ℂ⟯), ?_⟩,
    ⟨hx, hxW⟩⟩
  · exact contMDiffAt_subtype_iff.2 (hW y.2.2).1
  · apply Subtype.ext
    funext y
    change dbarCoeff (extendByZero M (fun y : V => g y)) y = t'.1 ⟨y.1, y.2.1⟩
    rw [(hW y.2.2).2 y.2.1]
    exact dbarCoeff_congr (extendByZero_eventuallyEq _ y.2 _ fun _ => rfl)

variable (M) in
theorem dolbeaultSequence_exact : (dolbeaultSequence M).Exact := by
  apply TopCat.Sheaf.exact_of_exists_local_preimage
  intro U s hs x hx
  let s' : C^∞⟮𝓘(ℝ, ℂ), U; 𝓘(ℝ, ℂ), ℂ⟯ := s
  have hs' : ∀ y : U, dbarCoeff (extendByZero M s') y = 0 := fun y =>
    congrFun (congrArg Subtype.val hs) y
  have hhol : ∀ y : U, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ s' y := by
    intro y
    rw [← extendByZero_comp_val s']
    refine contMDiffAt_subtype_iff.2 (contMDiffAt_of_eventually_dbarCoeff_eq_zero ?_)
    filter_upwards [U.isOpen.mem_nhds y.2] with z hz
    exact ⟨contMDiffAt_extendByZero (x := ⟨z, hz⟩) (s'.contMDiff _), hs' ⟨z, hz⟩⟩
  refine ⟨U, le_rfl, hx, (⟨s', hhol⟩ : C^∞⟮𝓘(ℂ), U; 𝓘(ℂ), ℂ⟯), ?_⟩
  rfl

variable (M) in
/-- **The Dolbeault sequence is short exact**: `𝒪_M ⟶ ℰ_M` is injective, its image is the kernel
of `∂̄` (Cauchy–Riemann), and `∂̄` is locally surjective (Dolbeault lemma). -/
theorem dolbeaultSequence_shortExact : (dolbeaultSequence M).ShortExact :=
  ShortComplex.ShortExact.mk' (dolbeaultSequence_exact M) (mono_holomorphicToSmooth M)
    (epi_dbarSheafHom M)

end Sheaves

/-! ### Cohomology of the holomorphic structure sheaf -/

section Cohomology

universe w'

open CategoryTheory TopologicalSpace Opposite Abelian

variable (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] [T2Space M]
  [CompactSpace M]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0})]

/-- On a compact Riemann surface the sheaf of real smooth functions is acyclic. -/
theorem subsingleton_H_smoothFunctionsSheafAb (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H.{w'} (smoothFunctionsSheafAb M) n) := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_smooth
  exact SheafOfModules.subsingleton_H_toSheaf_smoothSheafCommRing 𝓘(ℝ, ℂ) M ℂ _ n hn

/-- On a compact Riemann surface the sheaf of smooth `(0,1)`-forms is acyclic. -/
theorem subsingleton_H_dbarFormsSheafAb (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H.{w'} (dbarFormsSheafAb M) n) := by
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := isManifold_real_smooth
  exact SheafOfModules.subsingleton_H_toSheaf_smoothSheafCommRing 𝓘(ℝ, ℂ) M ℂ _ n hn

/-- **`H^q(M, 𝒪_M) = 0` for `q ≥ 2`** on a compact Riemann surface `M`. -/
theorem subsingleton_H_holomorphicSheafAb (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w'} (ComplexManifold.holomorphicSheafAb 𝓘(ℂ) M) q) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  have hS := dolbeaultSequence_shortExact M
  have h₂ := subsingleton_H_smoothFunctionsSheafAb.{w'} M (p + 1) (by omega)
  have h₃ := subsingleton_H_dbarFormsSheafAb.{w'} M p (by omega)
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS x (@Subsingleton.elim _ h₂ _ _) rfl
  have h0 : x₃ = 0 := @Subsingleton.elim _ h₃ x₃ 0
  rw [← hx₃, h0]
  exact Ext.zero_comp _ _ hS.extClass _ _

/-- The connecting map `H⁰(M, ℰ^{0,1}) ⟶ H¹(M, 𝒪_M)` of the Dolbeault sequence, on global
`(0,1)`-forms. -/
def dolbeaultConnecting :
    (dbarFormsSheafAb M).obj.obj (op ⊤) →+
      Sheaf.H.{w'} (ComplexManifold.holomorphicSheafAb 𝓘(ℂ) M) 1 :=
  ((dolbeaultSequence_shortExact M).extClass.postcomp _ (zero_add 1)).comp
    (Sheaf.H.equiv₀ (dbarFormsSheafAb M) Limits.isTerminalTop).symm.toAddMonoidHom

/-- **`H¹(M, 𝒪_M)` is the cokernel of `∂̄` on global sections, I**: every class in `H¹(M, 𝒪_M)`
comes from a global smooth `(0,1)`-form. -/
theorem dolbeaultConnecting_surjective : Function.Surjective (dolbeaultConnecting.{w'} M) := by
  intro x
  have hS := dolbeaultSequence_shortExact M
  have h₂ := subsingleton_H_smoothFunctionsSheafAb.{w'} M 1 one_pos
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ _ hS x (@Subsingleton.elim _ h₂ _ _) rfl
  let y : Sheaf.H.{w'} (dbarFormsSheafAb M) 0 := x₃
  refine ⟨Sheaf.H.equiv₀ (dbarFormsSheafAb M) Limits.isTerminalTop y, ?_⟩
  change (hS.extClass.postcomp _ (zero_add 1))
    ((Sheaf.H.equiv₀ (dbarFormsSheafAb M) Limits.isTerminalTop).symm
      (Sheaf.H.equiv₀ (dbarFormsSheafAb M) Limits.isTerminalTop y)) = x
  exact (congrArg _ (AddEquiv.symm_apply_apply _ y)).trans hx₃

omit [T2Space M] [CompactSpace M] in
/-- **`H¹(M, 𝒪_M)` is the cokernel of `∂̄` on global sections, II**: a global smooth
`(0,1)`-form has zero image in `H¹(M, 𝒪_M)` if and only if it is `∂̄` of a global smooth
function. -/
theorem dolbeaultConnecting_eq_zero_iff (η : (dbarFormsSheafAb M).obj.obj (op ⊤)) :
    dolbeaultConnecting.{w'} M η = 0 ↔
      ∃ f : (smoothFunctionsSheafAb M).obj.obj (op ⊤), (dbarSheafHom M).hom.app (op ⊤) f = η := by
  have hS := dolbeaultSequence_shortExact M
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS _ (zero_add 1) h
    refine ⟨Sheaf.H.equiv₀ (smoothFunctionsSheafAb M) Limits.isTerminalTop x₂, ?_⟩
    have key := Sheaf.H.equiv₀_naturality
      (Limits.isTerminalTop (α := Opens (TopCat.of M))) (dbarSheafHom M)
      (show Sheaf.H.{w'} (smoothFunctionsSheafAb M) 0 from x₂)
    refine key.trans ?_
    rw [Sheaf.H.map_apply]
    change Sheaf.H.equiv₀ (dbarFormsSheafAb M) Limits.isTerminalTop
      (x₂.comp (Ext.mk₀ (dolbeaultSequence M).g) (add_zero 0)) = η
    rw [hx₂]
    exact AddEquiv.apply_symm_apply _ _
  · rintro ⟨f, rfl⟩
    have key := Sheaf.H.equiv₀_symm_naturality
      (Limits.isTerminalTop (α := Opens (TopCat.of M))) (dbarSheafHom M) f
    change (hS.extClass.postcomp _ (zero_add 1))
      ((Sheaf.H.equiv₀ (dbarFormsSheafAb M) Limits.isTerminalTop).symm
        ((dbarSheafHom M).hom.app (op ⊤) f)) = 0
    rw [← key, Sheaf.H.map_apply]
    change (((Sheaf.H.equiv₀ (smoothFunctionsSheafAb M) Limits.isTerminalTop).symm f).comp
      (Ext.mk₀ (dolbeaultSequence M).g) (add_zero 0)).comp hS.extClass (zero_add 1) = 0
    rw [Ext.comp_assoc_of_second_deg_zero]
    erw [hS.comp_extClass]
    exact Ext.comp_zero _ _ _ _ _

end Cohomology

end RiemannSurface

end
