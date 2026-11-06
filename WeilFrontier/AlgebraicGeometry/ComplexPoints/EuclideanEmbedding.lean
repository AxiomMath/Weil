module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ProjectiveLineCharts
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.SmoothRegularZeroSet
public import WeilFrontier.Geometry.Manifold.Instances.ProjectiveSpaceHermitian
public import WeilFrontier.Analysis.Calculus.ImmersionRegularZeroSet
public import WeilFrontier.Analysis.Calculus.NeighborhoodRetract
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Complex points of smooth projective schemes as regular zero sets in Euclidean space

Let `Y` be a smooth projective scheme over `ℂ`. We show that `Y(ℂ)`, with the analytic topology,
is homeomorphic to a compact subset `K` of a Euclidean space `ℝ^M` which is, near each of its
points, the zero set of a `C²` map with surjective derivative. In particular `Y(ℂ)` is a
Euclidean neighbourhood retract.

The embedding is the classical one. A closed immersion `Y → ℙⁿ` induces a closed embedding
`Y(ℂ) → ℙⁿ(ℂ)`, and `ℙⁿ(ℂ)` embeds into the matrices by `[v] ↦ v vᴴ / ‖v‖²`; on the standard
chart `Tᵢ ≠ 0` this map is `z ↦ Φ(1, z)`, which is well defined because two standard charts
parametrize the same point only at proportional homogeneous coordinates. As `ℙⁿ(ℂ)` is compact,
this is a closed embedding.

For the local structure, fix `p ∈ Y(ℂ)` in the chart `Tᵢ ≠ 0`. By the Jacobian criterion there
are an affine open `U ∋ p` and coordinates `s` on `U` identifying `U(ℂ)` near `p` with a regular
zero set `{G = 0}` in `ℂ^{c+d}`; the inverse function theorem parametrizes it by an open subset
of `ker G'(s(p))`. Near `p` the affine coordinates `t = (T_j / Tᵢ)_j` of `ℙⁿ` restricted to `Y`
are holomorphic functions `T₁` of `s`, and conversely `s = T₂ ∘ t`, since on a common basic open
`D(f) ⊆ U ∩ Y_{Tᵢ ≠ 0}` every regular function is a fraction `a / fᵐ` and the regular functions
on `U` (resp. on `Y_{Tᵢ ≠ 0}`) are polynomials in `s` (resp. in `t`). Composing the
parametrization with `T₁` and the chart `z ↦ Φ(1, z)` gives a `C²` map `ψ` onto a neighbourhood
of the image of `p` in `K`, with the left inverse `π ∘ T₂ ∘ (M ↦ (M_{ji} / M_{ii})_j)`, hence an
injective derivative and an inducing map. The image of such an immersion is locally a regular
zero set.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.hermitianEmbedding`: the Hermitian embedding
  `ℙⁿ(ℂ) → Mat_{n+1}(ℂ)`, on the model `Proj ℂ[T₀, …, Tₙ]`.
* `AlgebraicGeometry.Scheme.ComplexPoints.chartCoords`: the affine coordinates `T_j / Tᵢ` on the
  preimage of a standard open under a morphism to `ℙⁿ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.euclideanEmbedding`: the induced map `Y(ℂ) → ℝ^M`.

## Main results

* `exists_contDiffOn_param_of_surjective_fderiv`: a regular level set is locally parametrized by
  the kernel of the derivative, with a continuous linear left inverse of the parametrization.
* `AlgebraicGeometry.Scheme.ComplexPoints.injective_hermitianEmbedding`,
  `AlgebraicGeometry.Scheme.ComplexPoints.continuous_hermitianEmbedding`: the Hermitian
  embedding of `ℙⁿ(ℂ)` is a continuous injection.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_contDiffOn_coords_eq`: change of coordinates
  between affine opens.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_regularZeroSet_euclideanEmbedding`: for `Y`
  smooth with a closed immersion into `ℙⁿ`, the image of `Y(ℂ)` is locally a regular zero set.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_homeomorph_isCompact_regularZeroSet`: `Y(ℂ)`
  of a smooth projective `Y` is homeomorphic to a compact regular zero set in `ℝ^M`.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_homeomorph_isOpen_retraction`: such a `Y(ℂ)` is
  a Euclidean neighbourhood retract.

## Implementation notes

The local equations are only `C²`, as needed for the neighbourhood retraction; the construction
gives real analytic data. Projective space is the model `Proj ℂ[T₀, …, Tₙ]`; a closed immersion
into `ℙⁿ_ℂ = ℙⁿ_ℤ ×_ℤ Spec ℂ` is transported along the comparison isomorphism. The matrices
`Mat_{n+1}(ℂ)` are identified with `ℝ^M`, `M = 2(n+1)²`, by `toEuclidean`.

## References

* [GH] P. Griffiths, J. Harris, *Principles of Algebraic Geometry*, Ch. 1, §2.
* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

/-! ### Local parametrization of a regular zero set -/

section Parametrization

variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A map with a left inverse continuous on its image is inducing on its domain. -/
theorem isInducing_restrict_of_leftInvOn {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {ψ : A → B} {ℓ : B → A} {V : Set A} (hψ : ContinuousOn ψ V) (hℓ : ContinuousOn ℓ (ψ '' V))
    (h : ∀ v ∈ V, ℓ (ψ v) = v) : IsInducing (fun x : V => ψ x) := by
  let f₁ : V → ψ '' V := fun x => ⟨ψ x, Set.mem_image_of_mem ψ x.2⟩
  have hf₁ : Continuous f₁ := hψ.domRestrict.subtype_mk _
  have hg : Continuous ((ψ '' V).domRestrict ℓ) := hℓ.domRestrict
  have hgf : (ψ '' V).domRestrict ℓ ∘ f₁ = Subtype.val := funext fun x => h x.1 x.2
  have : IsInducing f₁ := IsInducing.of_comp hf₁ hg (hgf ▸ IsInducing.subtypeVal)
  exact IsInducing.subtypeVal.comp this

/-- **A regular level set is locally parametrized by the kernel of the derivative.** Let
`G : X → Z` be `Cⁿ` (`1 ≤ n`) with surjective derivative `D` at `x₀`. There are an open
`O ∋ x₀`, an open `V ⊆ ker D`, a map `φ : ker D → X`, `Cⁿ` on `V`, and a continuous linear
`π : X → ker D` with `π ∘ φ = id` on `V`, such that `φ '' V = {x ∈ O | G x = G x₀}`. The map
`φ` is the inverse of `x ↦ (G x, π x)` (inverse function theorem), restricted to `{G x₀} × V`,
where `π` is a linear projection onto `ker D`. -/
theorem exists_contDiffOn_param_of_surjective_fderiv {n : WithTop ℕ∞} (hn : 1 ≤ n) {G : X → Z}
    (hG : ContDiff ℝ n G) {x₀ : X} (hs : Function.Surjective (fderiv ℝ G x₀)) :
    ∃ (O : Set X) (V : Set (LinearMap.ker (fderiv ℝ G x₀ : X →ₗ[ℝ] Z)))
      (φ : LinearMap.ker (fderiv ℝ G x₀ : X →ₗ[ℝ] Z) → X)
      (π : X →L[ℝ] LinearMap.ker (fderiv ℝ G x₀ : X →ₗ[ℝ] Z)),
      IsOpen O ∧ x₀ ∈ O ∧ IsOpen V ∧ ContDiffOn ℝ n φ V ∧ (∀ v ∈ V, π (φ v) = v) ∧
        φ '' V = {x ∈ O | G x = G x₀} := by
  set D := fderiv ℝ G x₀
  set K₀ := LinearMap.ker (D : X →ₗ[ℝ] Z)
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  obtain ⟨C, hC⟩ := K₀.exists_isCompl
  let π : X →L[ℝ] K₀ := LinearMap.toContinuousLinearMap (K₀.projectionOnto C hC)
  have hπK : ∀ v : K₀, π v = v := fun v => K₀.projectionOnto_apply_left hC v
  have hDπ : ∀ x, D (π x) = 0 := fun x => (π x).2
  let Φ : X → Z × K₀ := fun x => (G x, π x)
  let Φ' : X →L[ℝ] Z × K₀ := D.prod π
  have hbij : Function.Bijective Φ' := by
    refine ⟨fun u v huv => ?_, fun ⟨z, k⟩ => ?_⟩
    · have h1 : D (u - v) = 0 := by
        rw [map_sub, sub_eq_zero]; exact congrArg Prod.fst huv
      have h2 : π (u - v) = 0 := by
        rw [map_sub, sub_eq_zero]; exact congrArg Prod.snd huv
      have h3 := hπK ⟨u - v, h1⟩
      rw [h2] at h3
      exact sub_eq_zero.1 (congrArg Subtype.val h3).symm
    · obtain ⟨v, hv⟩ := hs z
      refine ⟨v - π v + k, Prod.ext ?_ ?_⟩
      · change D (v - π v + k) = z
        rw [map_add, map_sub, hv, hDπ, show D k = 0 from k.2, sub_zero, add_zero]
      · change π (v - π v + k) = k
        rw [map_add, map_sub, hπK, hπK, sub_self, zero_add]
  let eΦ : X ≃L[ℝ] Z × K₀ :=
    (LinearEquiv.ofBijective (Φ' : X →ₗ[ℝ] Z × K₀) hbij).toContinuousLinearEquiv
  have heΦ : (eΦ : X →L[ℝ] Z × K₀) = Φ' := rfl
  have hΦ : ContDiff ℝ n Φ := hG.prodMk π.contDiff
  have hΦ' : HasFDerivAt Φ (eΦ : X →L[ℝ] Z × K₀) x₀ := by
    rw [heΦ]
    exact ((hG.differentiable hn0) x₀).hasFDerivAt.prodMk π.hasFDerivAt
  let P : Set X := fderiv ℝ Φ ⁻¹' Set.range (ContinuousLinearEquiv.toContinuousLinearMap (R₁ := ℝ))
  have hP : IsOpen P :=
    (hΦ.continuous_fderiv hn0).isOpen_preimage _ ContinuousLinearEquiv.isOpen
  let h := hΦ.contDiffAt.toOpenPartialHomeomorph Φ hΦ' hn0
  have hh : (h : X → Z × K₀) = Φ := rfl
  let O := h.source ∩ P
  have hO : IsOpen O := h.open_source.inter hP
  have hx₀O : x₀ ∈ O :=
    ⟨hΦ.contDiffAt.mem_toOpenPartialHomeomorph_source hΦ' hn0, ⟨eΦ, hΦ'.fderiv.symm⟩⟩
  have hOs : O ⊆ h.source := Set.inter_subset_left
  have key : ∀ x ∈ O, ContDiffAt ℝ n h.symm (h x) := by
    intro x hx
    obtain ⟨ψ', hψ'⟩ := hx.2
    have hd : HasFDerivAt h (ψ' : X →L[ℝ] Z × K₀) (h.symm (h x)) := by
      rw [h.left_inv (hOs hx), hh, hψ']
      exact (hΦ.differentiable hn0 x).hasFDerivAt
    refine h.contDiffAt_symm (h.map_source (hOs hx)) hd ?_
    rw [h.left_inv (hOs hx), hh]
    exact hΦ.contDiffAt
  let ι₀ : K₀ → Z × K₀ := fun k => (G x₀, k)
  have hι₀ : ContDiff ℝ n ι₀ := contDiff_const.prodMk contDiff_id
  refine ⟨O, ι₀ ⁻¹' (h '' O), fun k => h.symm (ι₀ k), π, hO, hx₀O,
    (h.isOpen_image_of_subset_source hO hOs).preimage hι₀.continuous, ?_, ?_, ?_⟩
  · rintro k ⟨x, hx, hxk⟩
    refine ContDiffAt.contDiffWithinAt ?_
    have := key x hx
    rw [hxk] at this
    exact this.comp k hι₀.contDiffAt
  · rintro k ⟨x, hx, hxk⟩
    change π (h.symm (ι₀ k)) = k
    rw [← hxk, h.left_inv (hOs hx)]
    exact congrArg Prod.snd hxk
  · ext x
    constructor
    · rintro ⟨k, ⟨x', hx', hxk⟩, rfl⟩
      change h.symm (ι₀ k) ∈ _
      rw [← hxk, h.left_inv (hOs hx')]
      exact ⟨hx', congrArg Prod.fst hxk⟩
    · rintro ⟨hx, hGx⟩
      refine ⟨π x, ⟨x, hx, ?_⟩, ?_⟩
      · change Φ x = ι₀ (π x)
        exact Prod.ext hGx rfl
      · change h.symm (ι₀ (π x)) = x
        rw [show ι₀ (π x) = h x from Prod.ext hGx.symm rfl, h.left_inv (hOs hx)]

end Parametrization

namespace AlgebraicGeometry.Scheme.ComplexPoints

open HomogeneousLocalization Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ)

/-! ### The Hermitian embedding of `ℙⁿ(ℂ)` -/

theorem chartEval_frac_eq_chartVec (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (j : Fin (n + 1)) : chartEval n i z (frac n i j) = ComplexProjectiveSpace.chartVec i z j := by
  by_cases h : j = i
  · subst h
    rw [frac_self, map_one, ComplexProjectiveSpace.chartVec_self]
  · rw [show j = ((⟨j, h⟩ : {j : Fin (n + 1) // j ≠ i}) : Fin (n + 1)) from rfl,
      ComplexProjectiveSpace.chartVec_of_ne i z ⟨j, h⟩]
    exact chartEval_frac n i z ⟨j, h⟩

variable {n} in
/-- Two standard charts parametrize the same point only at proportional homogeneous
coordinates. -/
theorem exists_chartVec_eq_smul_of_chartParam_eq {i k : Fin (n + 1)}
    {z : {j : Fin (n + 1) // j ≠ i} → ℂ} {w : {j : Fin (n + 1) // j ≠ k} → ℂ}
    (h : chartParam n i z = chartParam n k w) :
    ∃ c : ℂ, c ≠ 0 ∧
      ComplexProjectiveSpace.chartVec k w = c • ComplexProjectiveSpace.chartVec i z := by
  have hh : Spec.map (CommRingCat.ofHom (chartEval n k w)) ≫ chartι n k =
      Spec.map (CommRingCat.ofHom (chartEval n i z)) ≫ chartι n i :=
    (congrArg ComplexPoints.hom h).symm
  let x : MvPolynomial (Fin (n + 1)) ℂ := MvPolynomial.X k * MvPolynomial.X i
  let e := Proj.pullbackAwayιIso (polyGrading ℂ n) (X_mem_one ℂ n k) one_pos (X_mem_one ℂ n i)
    one_pos (rfl : x = _)
  let ℓ := Limits.pullback.lift _ _ hh ≫ e.hom
  let χ := Spec.preimage ℓ
  have hχ : Spec.map χ = ℓ := Spec.map_preimage ℓ
  have hk : ∀ a, χ.hom (awayMap (polyGrading ℂ n) (X_mem_one ℂ n i) (rfl : x = _) a) =
      chartEval n k w a := by
    have : CommRingCat.ofHom (awayMap (polyGrading ℂ n) (X_mem_one ℂ n i) (rfl : x = _)) ≫ χ =
        CommRingCat.ofHom (chartEval n k w) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hχ]
      simp only [ℓ, e, Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left]
      exact Limits.pullback.lift_fst _ _ _
    intro a
    exact congrArg (fun f => f.hom a) this
  have hi : ∀ a, χ.hom (awayMap (polyGrading ℂ n) (X_mem_one ℂ n k)
      (mul_comm (MvPolynomial.X k) (MvPolynomial.X i)) a) = chartEval n i z a := by
    have : CommRingCat.ofHom (awayMap (polyGrading ℂ n) (X_mem_one ℂ n k)
        (mul_comm (MvPolynomial.X k) (MvPolynomial.X i))) ≫ χ =
        CommRingCat.ofHom (chartEval n i z) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hχ]
      simp only [ℓ, e, Category.assoc, Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right]
      exact Limits.pullback.lift_snd _ _ _
    intro a
    exact congrArg (fun f => f.hom a) this
  have hrel : ∀ j, ComplexProjectiveSpace.chartVec i z j * ComplexProjectiveSpace.chartVec k w i =
      ComplexProjectiveSpace.chartVec k w j := by
    intro j
    have := congrArg χ.hom (awayMap_frac_mul_awayMap_frac n k i j)
    rw [map_mul, hi, hk, hk] at this
    rwa [chartEval_frac_eq_chartVec, chartEval_frac_eq_chartVec, chartEval_frac_eq_chartVec] at this
  refine ⟨ComplexProjectiveSpace.chartVec k w i, fun h0 => ?_, funext fun j => ?_⟩
  · have := hrel k
    rw [h0, mul_zero, ComplexProjectiveSpace.chartVec_self] at this
    exact zero_ne_one this
  · rw [Pi.smul_apply, smul_eq_mul, mul_comm, hrel j]

/-- The **Hermitian embedding** `ℙⁿ(ℂ) → Mat_{n+1}(ℂ)`, `[v] ↦ v vᴴ / ‖v‖²`, on the model
`Proj ℂ[T₀, …, Tₙ]`: a point is written in some standard chart and sent to the image of its
homogeneous coordinates under `ComplexProjectiveSpace.hermitianEmbedding`. -/
noncomputable def hermitianEmbedding (r : ComplexPoints (projToSpecCoeff ℂ n)) :
    Fin (n + 1) → Fin (n + 1) → ℂ :=
  ComplexProjectiveSpace.hermitianEmbedding
    (ComplexProjectiveSpace.chartVec (exists_chartParam n r).choose
      (exists_chartParam n r).choose_spec.choose)

theorem hermitianEmbedding_chartParam (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    hermitianEmbedding n (chartParam n i z) =
      ComplexProjectiveSpace.hermitianEmbedding (ComplexProjectiveSpace.chartVec i z) := by
  have h := (exists_chartParam n (chartParam n i z)).choose_spec.choose_spec.2
  obtain ⟨c, hc, he⟩ := exists_chartVec_eq_smul_of_chartParam_eq h
  exact (ComplexProjectiveSpace.hermitianEmbedding_eq_iff
    (ComplexProjectiveSpace.chartVec_ne_zero i z)).2 ⟨c, hc, he⟩

theorem continuous_hermitianEmbedding : Continuous (hermitianEmbedding n) := by
  refine continuous_iff_continuousAt.2 fun r => ?_
  obtain ⟨i, z, -, rfl⟩ := exists_chartParam n r
  have h : hermitianEmbedding n ∘ chartParam n i =
      fun z => ComplexProjectiveSpace.hermitianEmbedding (ComplexProjectiveSpace.chartVec i z) :=
    funext (hermitianEmbedding_chartParam n i)
  rw [← (isOpenEmbedding_chartParam n i).continuousAt_iff, h]
  exact (ComplexProjectiveSpace.contDiff_hermitianEmbedding_chartVec (n := 0) i).continuous
    |>.continuousAt

theorem injective_hermitianEmbedding : Function.Injective (hermitianEmbedding n) := by
  intro r r' hrr'
  obtain ⟨i, z, -, rfl⟩ := exists_chartParam n r
  obtain ⟨k, w, -, rfl⟩ := exists_chartParam n r'
  rw [hermitianEmbedding_chartParam, hermitianEmbedding_chartParam,
    ComplexProjectiveSpace.hermitianEmbedding_eq_iff
      (ComplexProjectiveSpace.chartVec_ne_zero k w)] at hrr'
  obtain ⟨c, hc, he⟩ := hrr'
  have hval : ∀ j, chartEval n k w (frac n k j) = c * ComplexProjectiveSpace.chartVec i z j :=
    fun j => by rw [chartEval_frac_eq_chartVec, he, Pi.smul_apply, smul_eq_mul]
  have hai : chartEval n k w (frac n k i) ≠ 0 := by
    rw [hval, ComplexProjectiveSpace.chartVec_self, mul_one]
    exact hc
  have := chartPoint_eq_chartParam n k i (chartEval n k w) (chartEval_coeffToAway n k w) hai
  change _ = chartPoint n k (chartEval n k w) (chartEval_coeffToAway n k w)
  rw [this]
  congr 1
  funext j
  rw [hval, hval, ComplexProjectiveSpace.chartVec_self, mul_one,
    show (j : Fin (n + 1)) = j.1 from rfl, ComplexProjectiveSpace.chartVec_of_ne i z j]
  field_simp
/-! ### Affine coordinates on a projective scheme -/

/-- A function on the `i`-th standard chart `Spec ℂ[T]_{(Tᵢ)}`, as a regular function on the
`i`-th standard open of `Proj ℂ[T₀, …, Tₙ]`. -/
noncomputable def chartSection (i : Fin (n + 1)) (a : Away (polyGrading ℂ n) (MvPolynomial.X i)) :
    Γ(Proj (polyGrading ℂ n), chartι n i ''ᵁ ⊤) :=
  ((chartι n i).appIso ⊤).inv
    ((Scheme.ΓSpecIso (.of (Away (polyGrading ℂ n) (MvPolynomial.X i)))).inv a)

theorem chartParam_mem (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (chartParam n i z).Mem (chartι n i ''ᵁ ⊤) := by
  rw [chartParam_eq_map, map_mem_iff, (chartι n i).preimage_image_eq]
  exact mem_top _

theorem exists_chartParam_eq_of_mem {i : Fin (n + 1)} {r : ComplexPoints (projToSpecCoeff ℂ n)}
    (hr : r.Mem (chartι n i ''ᵁ ⊤)) : ∃ z, chartParam n i z = r := by
  rw [Scheme.Hom.image_top_eq_opensRange] at hr
  obtain ⟨P, rfl⟩ : r ∈ Set.range (map (chartι n i) (chartι_comp n i)) := by
    rw [range_map_of_isOpenImmersion]
    exact hr
  exact ⟨chartCoord n i P, by rw [chartParam_eq_map, chartSpecPoint_chartCoord]⟩

theorem eval_chartSection (i : Fin (n + 1)) (a : Away (polyGrading ℂ n) (MvPolynomial.X i))
    (z : {j : Fin (n + 1) // j ≠ i} → ℂ) (h : (chartParam n i z).Mem (chartι n i ''ᵁ ⊤)) :
    eval (chartSection n i a) (chartParam n i z) h = chartEval n i z a := by
  have h' : (chartSpecPoint n i z).Mem (chartι n i ⁻¹ᵁ chartι n i ''ᵁ ⊤) := h
  refine (eval_map_point (chartι n i) (chartι_comp n i) (chartSection n i a)
    (chartSpecPoint n i z) h).trans ?_
  rw [chartSection, eval_app_appIso_inv _ ⊤ _ _ h' (mem_top _), chartSpecPoint, eval_ofSpecMap]
  simp

variable {n} {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} (ι : Y ⟶ Proj (polyGrading ℂ n))
  (hι : ι ≫ projToSpecCoeff ℂ n = y)

/-- The affine coordinates `T_j / Tᵢ` on the preimage of the `i`-th standard open under a
morphism to `Proj ℂ[T₀, …, Tₙ]`. -/
noncomputable def chartCoords (i : Fin (n + 1)) (j : {j : Fin (n + 1) // j ≠ i}) :
    Γ(Y, ι ⁻¹ᵁ (chartι n i ''ᵁ ⊤)) :=
  ι.app _ (chartSection n i (frac n i j))

include hι in
/-- A point of `Y(ℂ)` over the `i`-th standard open is sent to the point of the `i`-th chart
with coordinates its affine coordinates. -/
theorem map_eq_chartParam_coords (i : Fin (n + 1)) (q : ComplexPoints y)
    (hq : q.Mem (ι ⁻¹ᵁ (chartι n i ''ᵁ ⊤))) :
    map ι hι q = chartParam n i (coords y (chartCoords ι i) ⟨q, hq⟩) := by
  obtain ⟨z, hz⟩ := exists_chartParam_eq_of_mem n ((map_mem_iff ι hι q _).2 hq)
  rw [← hz]
  congr 1
  funext j
  change z j = eval (ι.app _ (chartSection n i (frac n i j))) q hq
  rw [← eval_map_point ι hι _ q ((map_mem_iff ι hι q _).2 hq)]
  have h2 : (chartParam n i z).Mem (chartι n i ''ᵁ ⊤) := chartParam_mem n i z
  calc z j = eval (chartSection n i (frac n i j)) (chartParam n i z) h2 := by
        rw [eval_chartSection, chartEval_frac]
    _ = _ := by congr 1

include hι in
/-- Every regular function on the preimage of the `i`-th standard open under a closed immersion
is, at complex points, a polynomial function of the affine coordinates. -/
theorem exists_eval_eq_mvPolynomial_chartCoords [IsClosedImmersion ι] (i : Fin (n + 1))
    (a : Γ(Y, ι ⁻¹ᵁ (chartι n i ''ᵁ ⊤))) :
    ∃ P : MvPolynomial {j : Fin (n + 1) // j ≠ i} ℂ, ∀ (q : ComplexPoints y) (hq),
      eval a q hq = MvPolynomial.eval (coords y (chartCoords ι i) ⟨q, hq⟩) P := by
  obtain ⟨b, rfl⟩ :=
    ι.app_surjective _ ((isAffineOpen_top _).image_of_isOpenImmersion (chartι n i)) a
  set a' := (Scheme.ΓSpecIso (.of (Away (polyGrading ℂ n) (MvPolynomial.X i)))).hom
    (((chartι n i).appIso ⊤).hom b)
  have hb : chartSection n i a' = b := by simp [chartSection, a']
  refine ⟨(chartEquiv ℂ n i).symm a', fun q hq => ?_⟩
  rw [← eval_map_point ι hι _ q ((map_mem_iff ι hι q _).2 hq)]
  have h1 := map_eq_chartParam_coords ι hι i q hq
  have h2 : (chartParam n i (coords y (chartCoords ι i) ⟨q, hq⟩)).Mem (chartι n i ''ᵁ ⊤) :=
    chartParam_mem n i _
  calc eval b (map ι hι q) ((map_mem_iff ι hι q _).2 hq) =
        eval b (chartParam n i (coords y (chartCoords ι i) ⟨q, hq⟩)) h2 := by
        congr 1
    _ = _ := by rw [← hb, eval_chartSection]; rfl
/-! ### Change of coordinates between affine opens -/

section ChangeOfCoordinates

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-- **Change of coordinates.** Let `U`, `V` be affine opens of `Y`, let `s` be functions on `U`
such that every regular function on `U` is, at complex points, a polynomial in the `s i`, and
let `t` be functions on `V`. Near a point `p ∈ U(ℂ) ∩ V(ℂ)`, the coordinates `t` are a
holomorphic function of the coordinates `s`: there are an open `Ω ∋ s(p)` and `T` holomorphic on
`Ω` such that every `q ∈ U(ℂ)` with `s(q) ∈ Ω` lies in `V(ℂ)` with `t(q) = T(s(q))`. The set `Ω`
is the locus where a function `f` on `U` with `p ∈ D(f) ⊆ V` does not vanish, and on `D(f)` each
`t k` is a fraction `a / fᵐ` with `a` regular on `U`. -/
theorem exists_contDiffOn_coords_eq {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (s : ι → Γ(Y, U)) (t : κ → Γ(Y, V))
    (hs : ∀ a : Γ(Y, U), ∃ P : MvPolynomial ι ℂ, ∀ (q : ComplexPoints y) (hq : q.Mem U),
      eval a q hq = MvPolynomial.eval (coords y s ⟨q, hq⟩) P)
    {p : ComplexPoints y} (hpU : p.Mem U) (hpV : p.Mem V) :
    ∃ (Ω : Set (ι → ℂ)) (T : (ι → ℂ) → κ → ℂ), IsOpen Ω ∧ coords y s ⟨p, hpU⟩ ∈ Ω ∧
      ContDiffOn ℂ ⊤ T Ω ∧ ∀ (q : ComplexPoints y) (hq : q.Mem U), coords y s ⟨q, hq⟩ ∈ Ω →
        ∃ hqV : q.Mem V, coords y t ⟨q, hqV⟩ = T (coords y s ⟨q, hq⟩) := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨f, g, hfg, hpf⟩ := exists_basicOpen_le_affine_inter hU hV (p.hom.base pt)
    ⟨(mem_iff pt).1 hpU, (mem_iff pt).1 hpV⟩
  have hDV : Y.basicOpen f ≤ V := hfg ▸ Y.basicOpen_le g
  have hDU : Y.basicOpen f ≤ U := Y.basicOpen_le f
  let := (Y.presheaf.map (homOfLE hDU).op).hom.toAlgebra
  have := hU.isLocalization_basicOpen f
  have hloc : ∀ k, ∃ (a : Γ(Y, U)) (m : ℕ), ∀ (q : ComplexPoints y) (hq : q.Mem U),
      ∀ hqD : q.Mem (Y.basicOpen f), eval (t k) q (Mem.mono hDV hqD) * eval f q hq ^ m =
        eval a q hq := by
    intro k
    obtain ⟨⟨a, b, m, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers f)
      (Y.presheaf.map (homOfLE hDV).op (t k))
    refine ⟨a, m, fun q hq hqD => ?_⟩
    have h' := congrArg (evalHom q hqD) h
    simp only [map_mul, map_pow, RingHom.algebraMap_toAlgebra, evalHom_apply, eval_map] at h'
    convert h' using 2
  choose a m ha using hloc
  choose A hA using fun k => hs (a k)
  obtain ⟨Q, hQ⟩ := hs f
  refine ⟨{x | MvPolynomial.eval x Q ≠ 0}, fun x k => MvPolynomial.eval x (A k) /
      MvPolynomial.eval x Q ^ m k,
    isOpen_ne_fun (MvPolynomial.continuous_eval Q) continuous_const, ?_, ?_, ?_⟩
  · change MvPolynomial.eval _ Q ≠ 0
    rw [← hQ, ← mem_basicOpen_iff hpU]
    exact (mem_iff pt).2 hpf
  · intro x hx
    refine ContDiffAt.contDiffWithinAt (contDiffAt_pi.2 fun k => ?_)
    exact ((AnalyticOnNhd.eval_mvPolynomial (A k)).contDiff.contDiffAt).div
      (((AnalyticOnNhd.eval_mvPolynomial Q).contDiff.contDiffAt).pow _) (pow_ne_zero _ hx)
  · intro q hq hqΩ
    have hqD : q.Mem (Y.basicOpen f) := by
      rw [mem_basicOpen_iff hq, hQ]
      exact hqΩ
    refine ⟨Mem.mono hDV hqD, funext fun k => ?_⟩
    have hf0 : eval f q hq ≠ 0 := (mem_basicOpen_iff hq).1 hqD
    change eval (t k) q _ = MvPolynomial.eval _ (A k) / MvPolynomial.eval _ Q ^ m k
    rw [← hA, ← hQ, ← ha k q hq hqD, mul_div_assoc, div_self (pow_ne_zero _ hf0), mul_one]

end ChangeOfCoordinates
/-! ### The Euclidean embedding of a projective scheme -/

section Embedding

variable {n : ℕ} {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)} (ι : Y ⟶ Proj (polyGrading ℂ n))
  (hι : ι ≫ projToSpecCoeff ℂ n = y)

/-- The Euclidean space `ℝ^M` of real dimension `M = 2(n+1)²` receiving `ℙⁿ(ℂ)`. -/
abbrev HermitianSpace (n : ℕ) : Type :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ (Fin (n + 1) → Fin (n + 1) → ℂ)))

/-- The embedding `Y(ℂ) → ℝ^M` of the complex points of `Y` given by a morphism `ι` to
`ℙⁿ = Proj ℂ[T₀, …, Tₙ]` followed by the Hermitian embedding of `ℙⁿ(ℂ)`. -/
noncomputable def euclideanEmbedding (q : ComplexPoints y) : HermitianSpace n :=
  toEuclidean (hermitianEmbedding n (map ι hι q))

theorem isClosedEmbedding_euclideanEmbedding [IsClosedImmersion ι] :
    IsClosedEmbedding (euclideanEmbedding ι hι) := by
  have h1 : IsClosedEmbedding (hermitianEmbedding n) :=
    (continuous_hermitianEmbedding n).isClosedEmbedding (injective_hermitianEmbedding n)
  exact (toEuclidean.toHomeomorph.isClosedEmbedding.comp h1).comp
    (isClosedEmbedding_map_of_isClosedImmersion ι hι)

theorem euclideanEmbedding_eq_of_mem (i : Fin (n + 1)) (q : ComplexPoints y)
    (hq : q.Mem (ι ⁻¹ᵁ (chartι n i ''ᵁ ⊤))) :
    euclideanEmbedding ι hι q = toEuclidean (ComplexProjectiveSpace.hermitianEmbedding
      (ComplexProjectiveSpace.chartVec i (coords y (chartCoords ι i) ⟨q, hq⟩))) := by
  rw [euclideanEmbedding, map_eq_chartParam_coords ι hι i q hq, hermitianEmbedding_chartParam]

/-- **Near every point, the Euclidean image of a smooth scheme with a closed immersion into `ℙⁿ`
is a regular zero set.** For `Y` smooth over `ℂ` and `ι : Y → ℙⁿ` a closed immersion, every
point of the image `K` of `Y(ℂ)` in `ℝ^M` has an open neighbourhood `V` and a `C²` map
`g : ℝ^M → ℝᵐ` with surjective derivative on `V` such that `K ∩ V = {x ∈ V | g x = 0}`. -/
theorem exists_regularZeroSet_euclideanEmbedding [IsClosedImmersion ι] [Smooth y]
    (p : ComplexPoints y) :
    ∃ V : Set (HermitianSpace n), IsOpen V ∧ euclideanEmbedding ι hι p ∈ V ∧
      ∃ (m : ℕ) (g : HermitianSpace n → EuclideanSpace ℝ (Fin m)), ContDiffOn ℝ 2 g V ∧
        (∀ x ∈ V, Function.Surjective (fderiv ℝ g x)) ∧
        Set.range (euclideanEmbedding ι hι) ∩ V = {x ∈ V | g x = 0} := by
  classical
  have hemb := isClosedEmbedding_euclideanEmbedding ι hι
  -- a standard chart of `ℙⁿ` containing the image of `p`, and its affine coordinates on `Y`
  obtain ⟨i, z₀, -, hz₀⟩ := exists_chartParam n (map ι hι p)
  have hpi : p.Mem (ι ⁻¹ᵁ (chartι n i ''ᵁ ⊤)) :=
    (map_mem_iff ι hι p _).1 (hz₀ ▸ chartParam_mem n i z₀)
  have hUi : IsAffineOpen (ι ⁻¹ᵁ (chartι n i ''ᵁ ⊤)) := IsAffineHom.isAffine_preimage _
    ((isAffineOpen_top _).image_of_isOpenImmersion (chartι n i))
  set t := chartCoords ι i
  -- the Jacobian criterion at `p`
  obtain ⟨U, hU, hpU, c, d, s, hs, F, W, hW, hpW, hF, heq⟩ := exists_range_coords_eq_of_smooth p
  have hsP : ∀ a : Γ(Y, U), ∃ P : MvPolynomial (Fin (c + d)) ℂ, ∀ (q : ComplexPoints y)
      (hq : q.Mem U), eval a q hq = MvPolynomial.eval (coords y s ⟨q, hq⟩) P := fun a => by
    obtain ⟨P, rfl⟩ := hs a
    exact ⟨P, fun q hq => eval_presentationHom s P q hq⟩
  -- the two changes of coordinates
  obtain ⟨Ω₁, T₁, hΩ₁, hpΩ₁, hT₁, hT₁eq⟩ := exists_contDiffOn_coords_eq hU hUi s t hsP hpU hpi
  obtain ⟨Ω₂, T₂, hΩ₂, hpΩ₂, hT₂, hT₂eq⟩ := exists_contDiffOn_coords_eq hUi hU t s
    (exists_eval_eq_mvPolynomial_chartCoords ι hι i) hpi hpU
  have hT₁' : ContDiffOn ℝ 2 T₁ Ω₁ := (hT₁.restrict_scalars ℝ).of_le le_top
  have hT₂' : ContDiffOn ℝ 2 T₂ Ω₂ := (hT₂.restrict_scalars ℝ).of_le le_top
  -- the regular equations in the coordinates `s`, and a local parametrization
  set G : (Fin (c + d) → ℂ) → (Fin c → ℂ) := fun z j => MvPolynomial.eval z (F j)
  set x₀ := coords y s ⟨p, hpU⟩
  have hGC : ContDiff ℂ ⊤ G := MvPolynomial.contDiff_eval_pi F
  have hG : ContDiff ℝ 2 G := (hGC.restrict_scalars ℝ).of_le le_top
  have hGs : Function.Surjective (fderiv ℝ G x₀) := by
    rw [(hGC.differentiable (by simp) x₀).fderiv_restrictScalars ℝ]
    exact hF x₀ hpW
  have hmem_range : ∀ x, x ∈ Set.range (coords y s) ↔ x ∈ W ∧ G x = 0 := fun x => by
    rw [heq]
    simp only [Set.mem_ofPred_eq, G, funext_iff, Pi.zero_apply]
  have hGx₀ : G x₀ = 0 := ((hmem_range x₀).1 ⟨_, rfl⟩).2
  obtain ⟨O, V₀, φ, π, hO, hx₀O, hV₀, hφ, hπφ, himg⟩ :=
    exists_contDiffOn_param_of_surjective_fderiv (n := 2) (by norm_num) hG hGs
  rw [hGx₀] at himg
  set Ω := O ∩ W ∩ (Ω₁ ∩ T₁ ⁻¹' Ω₂)
  have hΩ : IsOpen Ω := (hO.inter hW).inter (hT₁'.continuousOn.isOpen_inter_preimage hΩ₁ hΩ₂)
  set V := V₀ ∩ φ ⁻¹' Ω
  have hV : IsOpen V := hφ.continuousOn.isOpen_inter_preimage hV₀ hΩ
  -- the parametrization of `K` near `p`
  set A : ({j : Fin (n + 1) // j ≠ i} → ℂ) → HermitianSpace n := fun z =>
    toEuclidean (ComplexProjectiveSpace.hermitianEmbedding (ComplexProjectiveSpace.chartVec i z))
  have hA : ContDiff ℝ 2 A :=
    toEuclidean.contDiff.comp (ComplexProjectiveSpace.contDiff_hermitianEmbedding_chartVec i)
  set ψ := fun v => A (T₁ (φ v))
  have hpt : ∀ (q : ComplexPoints y) (hq : q.Mem U), coords y s ⟨q, hq⟩ ∈ Ω₁ →
      euclideanEmbedding ι hι q = A (T₁ (coords y s ⟨q, hq⟩)) := by
    intro q hq h
    obtain ⟨hqi, ht⟩ := hT₁eq q hq h
    rw [euclideanEmbedding_eq_of_mem ι hι i q hqi, ht]
  have hround : ∀ (q : ComplexPoints y) (hq : q.Mem U), coords y s ⟨q, hq⟩ ∈ Ω₁ →
      T₁ (coords y s ⟨q, hq⟩) ∈ Ω₂ → T₂ (T₁ (coords y s ⟨q, hq⟩)) = coords y s ⟨q, hq⟩ := by
    intro q hq h1 h2
    obtain ⟨hqi, ht⟩ := hT₁eq q hq h1
    rw [← ht] at h2 ⊢
    obtain ⟨hqU, hs'⟩ := hT₂eq q hqi h2
    exact hs'.symm
  have hφV : ∀ v ∈ V, ∃ (q : ComplexPoints y) (hq : q.Mem U), coords y s ⟨q, hq⟩ = φ v := by
    intro v hv
    have h1 : φ v ∈ φ '' V₀ := Set.mem_image_of_mem φ hv.1
    rw [himg] at h1
    obtain ⟨⟨q, hq⟩, hqv⟩ := (hmem_range (φ v)).2 ⟨hv.2.1.2, h1.2⟩
    exact ⟨q, hq, hqv⟩
  have hψ : ContDiffOn ℝ 2 ψ V := by
    intro v hv
    refine ContDiffAt.contDiffWithinAt ?_
    have h1 : ContDiffAt ℝ 2 φ v := hφ.contDiffAt (hV₀.mem_nhds hv.1)
    have h2 : ContDiffAt ℝ 2 T₁ (φ v) := hT₁'.contDiffAt (hΩ₁.mem_nhds hv.2.2.1)
    exact hA.contDiffAt.comp v (h2.comp v h1)
  -- a left inverse of `ψ`
  set ℓ := fun e : HermitianSpace n => π (T₂ (ComplexProjectiveSpace.chartCoord i
    (toEuclidean.symm e)))
  have hℓψ : ∀ v ∈ V, ℓ (ψ v) = v := by
    intro v hv
    obtain ⟨q, hq, hqv⟩ := hφV v hv
    simp only [ℓ, ψ, A, ContinuousLinearEquiv.symm_apply_apply,
      ComplexProjectiveSpace.chartCoord_hermitianEmbedding_chartVec]
    rw [← hqv, hround q hq (hqv ▸ hv.2.2.1) (hqv ▸ hv.2.2.2), hqv]
    exact hπφ v hv.1
  have hℓd : ∀ v ∈ V, DifferentiableAt ℝ ℓ (ψ v) := by
    intro v hv
    have h1 : DifferentiableAt ℝ (ComplexProjectiveSpace.chartCoord i)
        (toEuclidean.symm (ψ v)) := by
      simp only [ψ, A, ContinuousLinearEquiv.symm_apply_apply]
      exact (ComplexProjectiveSpace.contDiffAt_chartCoord (n := 1) i
        (ComplexProjectiveSpace.hermitianEmbedding_chartVec_apply_self_ne_zero i _)
        ).differentiableAt one_ne_zero
    have h2 : DifferentiableAt ℝ T₂
        (ComplexProjectiveSpace.chartCoord i (toEuclidean.symm (ψ v))) := by
      simp only [ψ, A, ContinuousLinearEquiv.symm_apply_apply,
        ComplexProjectiveSpace.chartCoord_hermitianEmbedding_chartVec]
      exact (hT₂'.contDiffAt (hΩ₂.mem_nhds hv.2.2.2)).differentiableAt two_ne_zero
    exact π.differentiableAt.comp (ψ v)
      (h2.comp (ψ v) (h1.comp (ψ v) toEuclidean.symm.differentiableAt))
  have hinj : ∀ v ∈ V, Function.Injective (fderiv ℝ ψ v) := by
    intro v hv
    have hψd : DifferentiableAt ℝ ψ v :=
      (hψ.contDiffAt (hV.mem_nhds hv)).differentiableAt two_ne_zero
    have hcomp := (hℓd v hv).hasFDerivAt.comp v hψd.hasFDerivAt
    have hid : HasFDerivAt (ℓ ∘ ψ) (ContinuousLinearMap.id ℝ _) v :=
      (hasFDerivAt_id v).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hV.mem_nhds hv) fun w hw => hℓψ w hw)
    have := hcomp.unique hid
    intro a b hab
    have := congrArg (fun L => L a) this
    have h' := congrArg (fun L => L b) (hcomp.unique hid)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this h'
    rw [← this, ← h', hab]
  have hind : IsInducing (fun x : V => ψ x) := by
    refine isInducing_restrict_of_leftInvOn hψ.continuousOn ?_ hℓψ
    rintro _ ⟨v, hv, rfl⟩
    exact (hℓd v hv).continuousAt.continuousWithinAt
  -- `K ∩ U' = ψ '' V` for an open `U'`
  set S : Set (ComplexPoints y) := Subtype.val '' (coords y s ⁻¹' Ω)
  have hS : IsOpen S := (isOpen_setOf_mem U).isOpenMap_subtype_val _
    ((continuous_coords s hU).isOpen_preimage _ hΩ)
  obtain ⟨U', hU', hU'S⟩ := hemb.isInducing.isOpen_iff.1 hS
  have himgS : ψ '' V = euclideanEmbedding ι hι '' S := by
    ext e
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨q, hq, hqv⟩ := hφV v hv
      refine ⟨q, ⟨⟨q, hq⟩, by rw [Set.mem_preimage, hqv]; exact hv.2, rfl⟩, ?_⟩
      rw [hpt q hq (hqv ▸ hv.2.2.1), hqv]
    · rintro ⟨_, ⟨⟨q, hq⟩, hqΩ, rfl⟩, rfl⟩
      have hx : coords y s ⟨q, hq⟩ ∈ φ '' V₀ := by
        rw [himg]
        exact ⟨hqΩ.1.1, ((hmem_range _).1 ⟨_, rfl⟩).2⟩
      obtain ⟨v, hv, hvq⟩ := hx
      refine ⟨v, ⟨hv, by rw [Set.mem_preimage, hvq]; exact hqΩ⟩, ?_⟩
      change A (T₁ (φ v)) = _
      rw [hvq, hpt q hq hqΩ.2.1]
  have hKU : Set.range (euclideanEmbedding ι hι) ∩ U' = ψ '' V := by
    rw [himgS, ← hU'S, Set.image_preimage_eq_range_inter]
  have hpS : p ∈ S := by
    refine ⟨⟨p, hpU⟩, ⟨⟨hx₀O, hpW⟩, hpΩ₁, ?_⟩, rfl⟩
    obtain ⟨hpi', ht⟩ := hT₁eq p hpU hpΩ₁
    rw [Set.mem_preimage, ← ht]
    exact hpΩ₂
  exact exists_inter_eq_regularZeroSet_of_inter_eq_image (n := 2) (by norm_num) hV hψ hind hinj
    hU' hKU _ (himgS ▸ Set.mem_image_of_mem _ hpS)

end Embedding
/-! ### Smooth projective schemes -/

section Projective

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-- **The complex points of a smooth projective scheme over `ℂ` are a compact regular zero set in
Euclidean space.** For `y : Y → Spec ℂ` smooth and projective there are `M`, a compact
`K ⊆ ℝ^M` and a homeomorphism `Y(ℂ) ≃ K`, where `K` is near each of its points the zero set of a
`C²` map with surjective derivative: every `p ∈ K` has an open neighbourhood `V` and
`g : ℝ^M → ℝᵐ`, `C²` on `V` with surjective derivative on `V`, with `K ∩ V = {x ∈ V | g x = 0}`. -/
theorem exists_homeomorph_isCompact_regularZeroSet [Smooth y] (hy : IsProjective y) :
    ∃ (M : ℕ) (K : Set (EuclideanSpace ℝ (Fin M))), IsCompact K ∧
      (∀ p ∈ K, ∃ V : Set (EuclideanSpace ℝ (Fin M)), IsOpen V ∧ p ∈ V ∧
        ∃ (m : ℕ) (g : EuclideanSpace ℝ (Fin M) → EuclideanSpace ℝ (Fin m)),
          ContDiffOn ℝ 2 g V ∧ (∀ x ∈ V, Function.Surjective (fderiv ℝ g x)) ∧
            K ∩ V = {x ∈ V | g x = 0}) ∧
      Nonempty (ComplexPoints y ≃ₜ K) := by
  obtain ⟨N, i, hi, hiy⟩ := isProjectiveMorphism_of_isProjective_of_isAffine y hy
  have := compactSpace_of_isProjective hy
  let ι : Y ⟶ Proj (polyGrading ℂ N) := i ≫ inv (projCompare ℂ N)
  have hι : ι ≫ projToSpecCoeff ℂ N = y := by
    simp only [ι, Category.assoc, inv_projCompare_comp, hiy]
  have : IsClosedImmersion ι := inferInstance
  have hemb := isClosedEmbedding_euclideanEmbedding ι hι
  refine ⟨_, Set.range (euclideanEmbedding ι hι), isCompact_range hemb.continuous, ?_,
    ⟨hemb.isEmbedding.toHomeomorph⟩⟩
  rintro _ ⟨p, rfl⟩
  exact exists_regularZeroSet_euclideanEmbedding ι hι p

/-- **The complex points of a smooth projective scheme over `ℂ` are a Euclidean neighbourhood
retract**: `Y(ℂ)` is homeomorphic to a compact `K ⊆ ℝ^M` which is a retract of an open
`T ⊇ K`. -/
theorem exists_homeomorph_isOpen_retraction [Smooth y] (hy : IsProjective y) :
    ∃ (M : ℕ) (K : Set (EuclideanSpace ℝ (Fin M))) (_ : Nonempty (ComplexPoints y ≃ₜ K))
      (T : Set (EuclideanSpace ℝ (Fin M))) (_ : IsOpen T) (hKT : K ⊆ T) (r : C(T, K)),
      ∀ x : K, r (Set.inclusion hKT x) = x := by
  obtain ⟨M, K, hK, hloc, he⟩ := exists_homeomorph_isCompact_regularZeroSet hy
  obtain ⟨T, hT, hKT, r, hr⟩ := hK.exists_isOpen_retraction_of_regularZeroSet hloc
  exact ⟨M, K, he, T, hT, hKT, r, hr⟩

end Projective

end AlgebraicGeometry.Scheme.ComplexPoints
