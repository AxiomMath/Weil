module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic

/-!
# Complex projective space as a submanifold of Hermitian matrices

For a finite index type `ι`, the map
`Φ : ℂ^ι → Mat_ι(ℂ)`, `Φ v = v vᴴ / ‖v‖²`, i.e. `Φ v a b = v a · conj (v b) / ∑ₖ |v k|²`,
is constant on the orbits of `ℂˣ` acting on `ℂ^ι ∖ {0}` and separates them: for `v, w ≠ 0`,
`Φ v = Φ w` if and only if `w = c v` for some `c ≠ 0`. Hence `Φ` induces an injective map from
complex projective space `ℙ(ℂ^ι)` into the real vector space of Hermitian matrices, which is the
classical embedding of `ℙⁿ(ℂ)` into Euclidean space.

On the standard chart `v i = 1` of `ℙ(ℂ^ι)`, parametrized by `z ∈ ℂ^{ι ∖ {i}}`, the composite
`z ↦ Φ(1, z)` is real analytic (in particular `C^∞`), and it has the left inverse
`M ↦ (M j i / M i i)_{j ≠ i}`, which is smooth on the open set `M i i ≠ 0` containing its image.
Consequently the chart composite is an immersion (its real derivative is injective at every point)
and a topological embedding of `ℂ^{ι ∖ {i}}`. Its image is the part of the image of `Φ` where the
entry `(i, i)` does not vanish, which is open in the image, and these images cover it.

Finally the image of `Φ` is the image of the unit sphere `∑ₖ |v k|² = 1`, hence compact, and
`Φ : ℂ^ι ∖ {0} → Φ(ℂ^ι ∖ {0})` is a quotient map; as its fibres are the `ℂˣ`-orbits, it
identifies the image of `Φ` with the quotient `(ℂ^ι ∖ {0}) / ℂˣ` as a topological space.

## Main definitions

* `ComplexProjectiveSpace.sqNorm`: `v ↦ ∑ₖ ‖v k‖²`.
* `ComplexProjectiveSpace.hermitianEmbedding`: the map `Φ v = v vᴴ / ‖v‖²`, with values in
  `ι → ι → ℂ` (that is, matrices).
* `ComplexProjectiveSpace.chartVec`: the point `(1, z)` of the `i`-th standard chart.
* `ComplexProjectiveSpace.chartCoord`: the left inverse `M ↦ (M j i / M i i)_{j ≠ i}`.

## Main results

* `ComplexProjectiveSpace.hermitianEmbedding_eq_iff`: `Φ v = Φ w ↔ ∃ c ≠ 0, w = c • v` for
  `v, w ≠ 0`.
* `ComplexProjectiveSpace.contDiff_hermitianEmbedding_chartVec`: `z ↦ Φ (chartVec i z)` is `C^n`
  over `ℝ` for every `n` (including `ω`).
* `ComplexProjectiveSpace.injective_fderiv_hermitianEmbedding_chartVec`: its real derivative is
  injective at every point.
* `ComplexProjectiveSpace.isEmbedding_hermitianEmbedding_chartVec`: it is a topological
  embedding.
* `ComplexProjectiveSpace.range_hermitianEmbedding_chartVec`: its image is
  `Φ '' {v | v ≠ 0} ∩ {M | M i i ≠ 0}`.
* `ComplexProjectiveSpace.iUnion_range_hermitianEmbedding_chartVec`: the chart images cover
  `Φ '' {v | v ≠ 0}`.
* `ComplexProjectiveSpace.isCompact_image_hermitianEmbedding`: `Φ '' {v | v ≠ 0}` is compact.
* `ComplexProjectiveSpace.isQuotientMap_hermitianEmbedding`: `Φ` is a quotient map from
  `ℂ^ι ∖ {0}` onto its image.

## Implementation notes

Matrices are written as functions `ι → ι → ℂ`, which carry the product norm and the real normed
space structure of `Pi`, so that calculus applies without choosing a matrix norm; this type is
definitionally `Matrix ι ι ℂ`. A real linear identification with a Euclidean space
`EuclideanSpace ℝ (Fin M)` is given by `toEuclidean`. The definition of `Φ` uses `0⁻¹ = 0`, so
`Φ 0 = 0`; all statements about `Φ` concern nonzero vectors.

## References

* [GH] P. Griffiths, J. Harris, *Principles of Algebraic Geometry*, Ch. 1, §2.
-/

@[expose] public section

open Function Set Topology

namespace ComplexProjectiveSpace

variable {ι : Type*} [Fintype ι]

/-! ### The squared norm -/

/-- The squared Hermitian norm `∑ₖ ‖v k‖²` of a vector `v ∈ ℂ^ι`. -/
noncomputable def sqNorm (v : ι → ℂ) : ℝ := ∑ k, ‖v k‖ ^ 2

theorem sqNorm_nonneg (v : ι → ℂ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_le_sqNorm (v : ι → ℂ) (k : ι) : ‖v k‖ ^ 2 ≤ sqNorm v :=
  Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)

theorem sqNorm_eq_zero_iff {v : ι → ℂ} : sqNorm v = 0 ↔ v = 0 := by
  refine ⟨fun h => funext fun k => ?_, fun h => by simp [h, sqNorm]⟩
  have := norm_sq_le_sqNorm v k
  rw [h] at this
  simpa using le_antisymm this (sq_nonneg _)

theorem sqNorm_ne_zero {v : ι → ℂ} (hv : v ≠ 0) : sqNorm v ≠ 0 :=
  fun h => hv (sqNorm_eq_zero_iff.1 h)

theorem sqNorm_smul (c : ℂ) (v : ι → ℂ) : sqNorm (c • v) = ‖c‖ ^ 2 * sqNorm v := by
  simp [sqNorm, Finset.mul_sum, mul_pow]

/-- `∑ₖ conj (v k) · v k = ‖v‖²`. -/
theorem sum_conj_mul_self (v : ι → ℂ) : ∑ k, starRingEnd ℂ (v k) * v k = (sqNorm v : ℂ) := by
  simp [sqNorm, Complex.conj_mul']

theorem contDiff_sqNorm {n : WithTop ℕ∞} : ContDiff ℝ n (sqNorm : (ι → ℂ) → ℝ) := by
  unfold sqNorm
  exact ContDiff.sum fun k _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ k)

/-! ### The map `Φ` -/

/-- The map `Φ v = v vᴴ / ‖v‖²` from `ℂ^ι` to the `ι × ι` complex matrices, the matrix of the
orthogonal projection onto the line `ℂ v` when `v ≠ 0`. -/
noncomputable def hermitianEmbedding (v : ι → ℂ) : ι → ι → ℂ :=
  fun a b => (sqNorm v)⁻¹ • (v a * starRingEnd ℂ (v b))

theorem hermitianEmbedding_apply (v : ι → ℂ) (a b : ι) :
    hermitianEmbedding v a b = ((sqNorm v)⁻¹ : ℂ) * (v a * starRingEnd ℂ (v b)) := by
  simp [hermitianEmbedding, Complex.real_smul]

/-- `Φ v` is a Hermitian matrix. -/
theorem hermitianEmbedding_apply_swap (v : ι → ℂ) (a b : ι) :
    hermitianEmbedding v b a = starRingEnd ℂ (hermitianEmbedding v a b) := by
  simp only [hermitianEmbedding_apply, map_mul, map_inv₀, Complex.conj_ofReal,
    Complex.conj_conj]
  ring

/-- `Φ` is constant on the orbits of `ℂˣ`. -/
theorem hermitianEmbedding_smul {c : ℂ} (hc : c ≠ 0) (v : ι → ℂ) :
    hermitianEmbedding (c • v) = hermitianEmbedding v := by
  funext a b
  have hc' : (‖c‖ : ℂ) ≠ 0 := by simpa using hc
  simp only [hermitianEmbedding_apply, sqNorm_smul, Pi.smul_apply, smul_eq_mul, map_mul,
    Complex.ofReal_mul, Complex.ofReal_pow]
  rw [show c * v a * (starRingEnd ℂ c * starRingEnd ℂ (v b)) =
    (c * starRingEnd ℂ c) * (v a * starRingEnd ℂ (v b)) by ring, Complex.mul_conj', mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ (pow_ne_zero 2 hc'), one_mul]

/-- `Φ v` applied to a vector `w`: `Φ v w = (⟨v, w⟩ / ‖v‖²) v`. -/
theorem sum_hermitianEmbedding_mul (v w : ι → ℂ) (a : ι) :
    ∑ b, hermitianEmbedding v a b * w b =
      (((sqNorm v)⁻¹ : ℂ) * ∑ b, starRingEnd ℂ (v b) * w b) * v a := by
  simp only [hermitianEmbedding_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `Φ v` fixes `v`: it is the projection onto `ℂ v`. -/
theorem sum_hermitianEmbedding_mul_self {v : ι → ℂ} (hv : v ≠ 0) (a : ι) :
    ∑ b, hermitianEmbedding v a b * v b = v a := by
  rw [sum_hermitianEmbedding_mul, sum_conj_mul_self,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (sqNorm_ne_zero hv)), one_mul]

/-- **`Φ` separates the `ℂˣ`-orbits**: for nonzero `v, w`, `Φ v = Φ w` if and only if `w` is a
nonzero multiple of `v`. -/
theorem hermitianEmbedding_eq_iff {v w : ι → ℂ} (hw : w ≠ 0) :
    hermitianEmbedding v = hermitianEmbedding w ↔ ∃ c : ℂ, c ≠ 0 ∧ w = c • v := by
  refine ⟨fun h => ?_, ?_⟩
  · set c : ℂ := ((sqNorm v)⁻¹ : ℂ) * ∑ b, starRingEnd ℂ (v b) * w b
    have hwc : w = c • v := funext fun a => by
      rw [← sum_hermitianEmbedding_mul_self hw a, ← h, sum_hermitianEmbedding_mul]
      rfl
    refine ⟨c, fun hc => hw ?_, hwc⟩
    rw [hwc, hc, zero_smul]
  · rintro ⟨c, hc, rfl⟩
    exact (hermitianEmbedding_smul hc v).symm

theorem hermitianEmbedding_apply_self (v : ι → ℂ) (a : ι) :
    hermitianEmbedding v a a = ((‖v a‖ ^ 2 / sqNorm v : ℝ) : ℂ) := by
  rw [hermitianEmbedding_apply, Complex.mul_conj']
  push_cast
  ring

theorem hermitianEmbedding_apply_self_ne_zero_iff {v : ι → ℂ} (hv : v ≠ 0) (a : ι) :
    hermitianEmbedding v a a ≠ 0 ↔ v a ≠ 0 := by
  rw [hermitianEmbedding_apply_self, Ne, Complex.ofReal_eq_zero, div_eq_zero_iff, not_or,
    pow_eq_zero_iff two_ne_zero, norm_eq_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, sqNorm_ne_zero hv⟩⟩

theorem contDiffAt_hermitianEmbedding {n : WithTop ℕ∞} {v : ι → ℂ} (hv : v ≠ 0) :
    ContDiffAt ℝ n hermitianEmbedding v := by
  have hinv : ContDiffAt ℝ n (fun v : ι → ℂ => (sqNorm v)⁻¹) v :=
    contDiff_sqNorm.contDiffAt.inv (sqNorm_ne_zero hv)
  refine contDiffAt_pi.2 fun a => contDiffAt_pi.2 fun b => ?_
  exact hinv.smul (((contDiff_apply ℝ ℂ a).mul
    (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ b))).contDiffAt)

theorem contDiffOn_hermitianEmbedding {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (hermitianEmbedding : (ι → ℂ) → ι → ι → ℂ) {v | v ≠ 0} :=
  fun _ hv => (contDiffAt_hermitianEmbedding hv).contDiffWithinAt

theorem continuousOn_hermitianEmbedding :
    ContinuousOn (hermitianEmbedding : (ι → ℂ) → ι → ι → ℂ) {v | v ≠ 0} :=
  (contDiffOn_hermitianEmbedding (n := 0)).continuousOn

/-! ### The standard charts -/

variable [DecidableEq ι]

/-- The point `(1, z)` of the `i`-th standard chart: coordinate `1` at `i` and `z j` at `j ≠ i`. -/
def chartVec (i : ι) (z : {j : ι // j ≠ i} → ℂ) : ι → ℂ :=
  fun j => if h : j = i then 1 else z ⟨j, h⟩

omit [Fintype ι] in
@[simp] theorem chartVec_self (i : ι) (z : {j : ι // j ≠ i} → ℂ) : chartVec i z i = 1 := by
  simp [chartVec]

omit [Fintype ι] in
@[simp] theorem chartVec_of_ne (i : ι) (z : {j : ι // j ≠ i} → ℂ) (j : {j : ι // j ≠ i}) :
    chartVec i z j = z j := by
  simp [chartVec, j.2]

omit [Fintype ι] in
theorem chartVec_ne_zero (i : ι) (z : {j : ι // j ≠ i} → ℂ) : chartVec i z ≠ 0 :=
  fun h => one_ne_zero ((chartVec_self i z).symm.trans (congrFun h i))

theorem contDiff_chartVec {n : WithTop ℕ∞} (i : ι) : ContDiff ℝ n (chartVec i) := by
  refine contDiff_pi.2 fun j => ?_
  by_cases h : j = i
  · simp only [chartVec, h, dite_true]
    exact contDiff_const
  · simp only [chartVec, h, dite_false]
    exact contDiff_apply ℝ ℂ (⟨j, h⟩ : {j : ι // j ≠ i})

/-- The left inverse `M ↦ (M j i / M i i)_{j ≠ i}` of the `i`-th chart of `Φ`. -/
noncomputable def chartCoord (i : ι) (M : ι → ι → ℂ) : {j : ι // j ≠ i} → ℂ :=
  fun j => M j i / M i i

theorem chartCoord_hermitianEmbedding_chartVec (i : ι) (z : {j : ι // j ≠ i} → ℂ) :
    chartCoord i (hermitianEmbedding (chartVec i z)) = z := by
  funext j
  have hr : (sqNorm (chartVec i z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (sqNorm_ne_zero (chartVec_ne_zero i z))
  simp only [chartCoord, hermitianEmbedding_apply, chartVec_self, chartVec_of_ne, map_one,
    mul_one]
  field_simp

theorem leftInverse_chartCoord (i : ι) :
    LeftInverse (chartCoord i) (fun z => hermitianEmbedding (chartVec i z)) :=
  chartCoord_hermitianEmbedding_chartVec i

theorem injective_hermitianEmbedding_chartVec (i : ι) :
    Injective fun z : {j : ι // j ≠ i} → ℂ => hermitianEmbedding (chartVec i z) :=
  (leftInverse_chartCoord i).injective

theorem contDiffAt_chartCoord {n : WithTop ℕ∞} (i : ι) {M : ι → ι → ℂ} (hM : M i i ≠ 0) :
    ContDiffAt ℝ n (chartCoord i) M := by
  refine contDiffAt_pi.2 fun j => ?_
  simp only [chartCoord, div_eq_mul_inv]
  exact (contDiff_apply_apply ℝ ℂ j.1 i).contDiffAt.mul
    ((contDiff_apply_apply ℝ ℂ i i).contDiffAt.inv hM)

omit [Fintype ι] [DecidableEq ι] in
theorem continuousOn_chartCoord (i : ι) :
    ContinuousOn (chartCoord i) {M : ι → ι → ℂ | M i i ≠ 0} := fun M (hM : M i i ≠ 0) =>
  (continuousAt_pi.2 fun j : {j : ι // j ≠ i} =>
    (((continuous_apply_apply j.1 i).continuousAt (x := M)).div
    (continuous_apply_apply i i).continuousAt hM)).continuousWithinAt

theorem hermitianEmbedding_chartVec_apply_self_ne_zero (i : ι) (z : {j : ι // j ≠ i} → ℂ) :
    hermitianEmbedding (chartVec i z) i i ≠ 0 :=
  (hermitianEmbedding_apply_self_ne_zero_iff (chartVec_ne_zero i z) i).2 (by simp)

/-- **The charts of `Φ` are smooth**: `z ↦ Φ (chartVec i z)` is `C^n` over `ℝ` for every `n`,
including `n = ω` (real analytic). -/
theorem contDiff_hermitianEmbedding_chartVec {n : WithTop ℕ∞} (i : ι) :
    ContDiff ℝ n fun z : {j : ι // j ≠ i} → ℂ => hermitianEmbedding (chartVec i z) :=
  contDiff_iff_contDiffAt.2 fun z =>
    (contDiffAt_hermitianEmbedding (chartVec_ne_zero i z)).comp z (contDiff_chartVec i).contDiffAt

/-- The derivative of `chartCoord i` at `Φ (chartVec i z)` is a left inverse of the derivative of
`z ↦ Φ (chartVec i z)` at `z`. -/
theorem fderiv_chartCoord_comp_fderiv (i : ι) (z : {j : ι // j ≠ i} → ℂ) :
    (fderiv ℝ (chartCoord i) (hermitianEmbedding (chartVec i z))).comp
        (fderiv ℝ (fun z => hermitianEmbedding (chartVec i z)) z) =
      ContinuousLinearMap.id ℝ _ := by
  have hf : DifferentiableAt ℝ (fun z => hermitianEmbedding (chartVec i z)) z :=
    (contDiff_hermitianEmbedding_chartVec (n := 1) i).differentiable one_ne_zero z
  have hψ : DifferentiableAt ℝ (chartCoord i) (hermitianEmbedding (chartVec i z)) :=
    (contDiffAt_chartCoord (n := 1) i
      (hermitianEmbedding_chartVec_apply_self_ne_zero i z)).differentiableAt one_ne_zero
  rw [← fderiv_comp z hψ hf]
  have hid : chartCoord i ∘ (fun z => hermitianEmbedding (chartVec i z)) = id :=
    funext (leftInverse_chartCoord i)
  rw [hid, fderiv_id]

/-- **The charts of `Φ` are immersions**: the real derivative of `z ↦ Φ (chartVec i z)` is
injective at every point. -/
theorem injective_fderiv_hermitianEmbedding_chartVec (i : ι) (z : {j : ι // j ≠ i} → ℂ) :
    Injective (fderiv ℝ (fun z => hermitianEmbedding (chartVec i z)) z) := by
  have h := fderiv_chartCoord_comp_fderiv i z
  refine LeftInverse.injective
    (g := fderiv ℝ (chartCoord i) (hermitianEmbedding (chartVec i z))) fun x => ?_
  simpa using DFunLike.congr_fun h x

/-- **The charts of `Φ` are topological embeddings.** -/
theorem isEmbedding_hermitianEmbedding_chartVec (i : ι) :
    IsEmbedding fun z : {j : ι // j ≠ i} → ℂ => hermitianEmbedding (chartVec i z) := by
  set S : Set (ι → ι → ℂ) := {M | M i i ≠ 0}
  let g : ({j : ι // j ≠ i} → ℂ) → S := fun z =>
    ⟨hermitianEmbedding (chartVec i z), hermitianEmbedding_chartVec_apply_self_ne_zero i z⟩
  have hg : Continuous g :=
    ((contDiff_hermitianEmbedding_chartVec (n := 0) i).continuous).subtype_mk _
  have hψ : Continuous fun M : S => chartCoord i M :=
    (continuousOn_chartCoord i).domRestrict
  have he : IsEmbedding g :=
    LeftInverse.isEmbedding (f := fun M : S => chartCoord i M)
      (fun z => leftInverse_chartCoord i z) hψ hg
  exact IsEmbedding.subtypeVal.comp he

theorem range_hermitianEmbedding_chartVec (i : ι) :
    range (fun z : {j : ι // j ≠ i} → ℂ => hermitianEmbedding (chartVec i z)) =
      hermitianEmbedding '' {v | v ≠ 0} ∩ {M | M i i ≠ 0} := by
  ext M
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨_, chartVec_ne_zero i z, rfl⟩, hermitianEmbedding_chartVec_apply_self_ne_zero i z⟩
  · rintro ⟨⟨v, hv, rfl⟩, hM⟩
    have hvi : v i ≠ 0 := (hermitianEmbedding_apply_self_ne_zero_iff hv i).1 hM
    refine ⟨fun j => v j / v i, ?_⟩
    have : chartVec i (fun j => v j / v i) = (v i)⁻¹ • v := by
      funext j
      by_cases h : j = i
      · subst h
        simp [hvi]
      · simp [chartVec, h, div_eq_inv_mul]
    change hermitianEmbedding (chartVec i _) = _
    rw [this, hermitianEmbedding_smul (inv_ne_zero hvi)]

/-- The images of the charts are open in the image of `Φ`. -/
theorem isOpen_range_hermitianEmbedding_chartVec (i : ι) :
    ∃ U : Set (ι → ι → ℂ), IsOpen U ∧
      range (fun z : {j : ι // j ≠ i} → ℂ => hermitianEmbedding (chartVec i z)) =
        hermitianEmbedding '' {v | v ≠ 0} ∩ U :=
  ⟨{M | M i i ≠ 0}, isOpen_ne_fun (continuous_apply_apply i i) continuous_const,
    range_hermitianEmbedding_chartVec i⟩

/-- The images of the charts cover the image of `Φ`. -/
theorem iUnion_range_hermitianEmbedding_chartVec :
    ⋃ i : ι, range (fun z : {j : ι // j ≠ i} → ℂ => hermitianEmbedding (chartVec i z)) =
      hermitianEmbedding '' {v | v ≠ 0} := by
  simp only [range_hermitianEmbedding_chartVec, ← inter_iUnion]
  refine inter_eq_left.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  exact mem_iUnion.2 ⟨i, (hermitianEmbedding_apply_self_ne_zero_iff hv i).2 hi⟩

/-! ### The image of `Φ` -/

omit [DecidableEq ι]

/-- The unit sphere `∑ₖ |v k|² = 1` of `ℂ^ι`, the sphere `S^{2|ι| - 1}`. -/
def unitSphere (ι : Type*) [Fintype ι] : Set (ι → ℂ) := {v | sqNorm v = 1}

theorem isCompact_unitSphere : IsCompact (unitSphere ι) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_eq (contDiff_sqNorm (n := 0)).continuous continuous_const)
    ((Metric.isBounded_closedBall (x := (0 : ι → ℂ)) (r := 1)).subset fun v hv => ?_)
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  have := norm_sq_le_sqNorm v k
  rw [show sqNorm v = 1 from hv] at this
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 this

theorem unitSphere_subset : unitSphere ι ⊆ {v | v ≠ 0} := fun v hv h => by
  simp [unitSphere, h, sqNorm] at hv

/-- The normalization `v ↦ v / ‖v‖` of a nonzero vector. -/
noncomputable def normalize (v : ι → ℂ) : ι → ℂ := ((Real.sqrt (sqNorm v))⁻¹ : ℂ) • v

theorem normalize_mem_unitSphere {v : ι → ℂ} (hv : v ≠ 0) : normalize v ∈ unitSphere ι := by
  have h0 := sqNorm_ne_zero hv
  have hs : Real.sqrt (sqNorm v) ^ 2 = sqNorm v := Real.sq_sqrt (sqNorm_nonneg v)
  change sqNorm (normalize v) = 1
  rw [normalize, sqNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, hs]
  exact inv_mul_cancel₀ h0

theorem hermitianEmbedding_normalize {v : ι → ℂ} (hv : v ≠ 0) :
    hermitianEmbedding (normalize v) = hermitianEmbedding v := by
  refine hermitianEmbedding_smul (inv_ne_zero ?_) v
  exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2
    (lt_of_le_of_ne (sqNorm_nonneg v) (sqNorm_ne_zero hv).symm))

theorem continuousOn_normalize : ContinuousOn (normalize : (ι → ℂ) → ι → ℂ) {v | v ≠ 0} := by
  have h1 : Continuous fun v : ι → ℂ => ((Real.sqrt (sqNorm v) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (contDiff_sqNorm (n := 0)).continuous)
  refine (h1.continuousOn.inv₀ fun v hv => ?_).smul continuousOn_id
  exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2
    (lt_of_le_of_ne (sqNorm_nonneg v) (sqNorm_ne_zero hv).symm))

theorem image_unitSphere_hermitianEmbedding :
    hermitianEmbedding '' unitSphere ι = hermitianEmbedding '' {v | v ≠ 0} := by
  refine (image_mono unitSphere_subset).antisymm ?_
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨normalize v, normalize_mem_unitSphere hv, hermitianEmbedding_normalize hv⟩

/-- **The image of `Φ` is compact**: it is the image of the unit sphere. -/
theorem isCompact_image_hermitianEmbedding :
    IsCompact (hermitianEmbedding '' {v : ι → ℂ | v ≠ 0}) := by
  rw [← image_unitSphere_hermitianEmbedding]
  exact isCompact_unitSphere.image_of_continuousOn
    (continuousOn_hermitianEmbedding.mono unitSphere_subset)

/-- `Φ` as a map from `ℂ^ι ∖ {0}` onto its image. -/
noncomputable def hermitianEmbeddingImage (ι : Type*) [Fintype ι] :
    {v : ι → ℂ // v ≠ 0} → hermitianEmbedding '' {v : ι → ℂ | v ≠ 0} :=
  fun v => ⟨hermitianEmbedding v.1, v.1, v.2, rfl⟩

theorem continuous_hermitianEmbeddingImage : Continuous (hermitianEmbeddingImage ι) :=
  continuousOn_hermitianEmbedding.domRestrict.subtype_mk _

theorem surjective_hermitianEmbeddingImage : Surjective (hermitianEmbeddingImage ι) := by
  rintro ⟨_, v, hv, rfl⟩
  exact ⟨⟨v, hv⟩, rfl⟩

theorem hermitianEmbeddingImage_eq_iff (v w : {v : ι → ℂ // v ≠ 0}) :
    hermitianEmbeddingImage ι v = hermitianEmbeddingImage ι w ↔
      ∃ c : ℂ, c ≠ 0 ∧ w.1 = c • v.1 := by
  rw [← hermitianEmbedding_eq_iff w.2]
  exact Subtype.ext_iff

/-- **`Φ` identifies its image with `(ℂ^ι ∖ {0}) / ℂˣ`**: the map from `ℂ^ι ∖ {0}` onto the image
of `Φ` is a quotient map, whose fibres are the `ℂˣ`-orbits (`hermitianEmbeddingImage_eq_iff`). -/
theorem isQuotientMap_hermitianEmbedding : IsQuotientMap (hermitianEmbeddingImage ι) := by
  have : T2Space (hermitianEmbedding '' {v : ι → ℂ | v ≠ 0}) := inferInstance
  have : CompactSpace (unitSphere ι) := isCompact_iff_compactSpace.1 isCompact_unitSphere
  let incl : unitSphere ι → {v : ι → ℂ // v ≠ 0} := fun v => ⟨v.1, unitSphere_subset v.2⟩
  have hincl : Continuous incl := continuous_subtype_val.subtype_mk _
  refine IsQuotientMap.of_comp hincl continuous_hermitianEmbeddingImage ?_
  have hc : Continuous (hermitianEmbeddingImage ι ∘ incl) :=
    continuous_hermitianEmbeddingImage.comp hincl
  refine hc.isClosedMap.isQuotientMap hc ?_
  rintro ⟨_, v, hv, rfl⟩
  exact ⟨⟨normalize v, normalize_mem_unitSphere hv⟩,
    Subtype.ext (hermitianEmbedding_normalize hv)⟩

end ComplexProjectiveSpace
