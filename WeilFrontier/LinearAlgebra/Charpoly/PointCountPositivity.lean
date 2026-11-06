module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Pure Frobenius with natural point counts acts on the top cohomology by `Q ^ d`

Let `φᵢ` be endomorphisms of finite-dimensional vector spaces `Vᵢ` (`0 ≤ i ≤ 2d`) over a field
`K` with an embedding `ι : K →+* ℂ`, such that every eigenvalue of `φᵢ` has absolute value
`Q ^ (i / 2)` along `ι` and `V_{2d}` is a line. If the alternating sums of traces
`∑ᵢ (-1) ^ i Tr(φᵢ ^ N)` are natural numbers for every `N ≥ 1`, then `φ_{2d}` is multiplication
by `Q ^ d`, and these alternating sums are nonzero for all large `N`.

This is the elementary "Lang–Weil" step of the Weil conjectures: with `Vᵢ` the `ℓ`-adic
cohomology of a smooth projective variety of dimension `d` over `𝔽_Q` and `φᵢ` the Frobenius, the
trace formula identifies the alternating sums with the numbers of points over `𝔽_{Q ^ N}`, and
purity bounds the contribution of the cohomology below the top degree.

The analytic input is: if `‖c‖ = Q`, `‖e N‖ ≤ C R ^ N` with `0 ≤ R < Q`, and `c ^ N + e N` is a
nonnegative real number for every `N ≥ 1`, then `c = Q`. Indeed `|c ^ N - Q ^ N| ≤ 2 ‖e N‖`,
hence `Q ^ N |c - Q| = |c ^ (N + 1) - Q c ^ N| = O(R ^ N)`.

## Main results

* `Complex.eq_of_forall_pow_add_eq_ofReal_nonneg`: the analytic input above.
* `Complex.exists_forall_pow_add_ne_zero`: under `‖e N‖ ≤ C R ^ N`, `c ^ N + e N ≠ 0` for all
  large `N`.
* `Module.End.trace_pow_eq_sum_roots_charpoly_pow`: over an algebraically closed field, the trace
  of `f ^ N` is the sum of the `N`-th powers of the roots of the characteristic polynomial.
* `Matrix.trace_pow_eq_sum_roots_charpoly_pow`: the same for matrices.
* `LinearMap.map_trace_pow_eq_sum_roots_charpoly_map_pow`: the same along a ring homomorphism into
  an algebraically closed field.
* `LinearMap.norm_map_trace_pow_le`: the bound `‖ι (Tr φ ^ N)‖ ≤ dim V · R ^ N` when the roots
  have absolute value at most `R`.
* `LinearMap.charpoly_smul_id_of_finrank_eq_one`: the characteristic polynomial of `μ • id` on a
  line.
* `Module.End.eq_pow_smul_id_of_isPure_of_alternating_trace_eq_natCast`,
  `Module.End.charpoly_eq_X_sub_C_of_isPure_of_alternating_trace_eq_natCast`: the top
  endomorphism is multiplication by `Q ^ d`.
* `Module.End.exists_forall_alternating_trace_pow_ne_zero_of_isPure`: the alternating sums of
  traces are eventually nonzero.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

@[expose] public section

open Polynomial Filter Topology

/-! ### The analytic input -/

namespace Complex

/-- If `‖c‖ = Q` and `c ^ N + e N` is a nonnegative real number for every `N ≥ 1`, where
`‖e N‖ ≤ C R ^ N` with `0 ≤ R < Q`, then `c = Q`. -/
theorem eq_of_forall_pow_add_eq_ofReal_nonneg {c : ℂ} {Q R C : ℝ} {e : ℕ → ℂ} (hR : 0 ≤ R)
    (hRQ : R < Q) (hc : ‖c‖ = Q) (he : ∀ N, ‖e N‖ ≤ C * R ^ N)
    (hreal : ∀ N ≥ 1, ∃ a : ℝ, 0 ≤ a ∧ c ^ N + e N = a) : c = Q := by
  have hQ : 0 < Q := hR.trans_lt hRQ
  -- `|c ^ N - Q ^ N| ≤ 2 ‖e N‖` for `N ≥ 1`
  have key : ∀ N ≥ 1, ‖c ^ N - (Q : ℂ) ^ N‖ ≤ 2 * (C * R ^ N) := by
    intro N hN
    obtain ⟨a, ha, hca⟩ := hreal N hN
    have h1 : ‖c ^ N - a‖ = ‖e N‖ := by
      rw [← hca]; simp
    have h2 : ‖(a : ℂ) - (Q : ℂ) ^ N‖ ≤ ‖e N‖ := by
      have hn : ‖(a : ℂ)‖ - ‖c ^ N‖ = (a : ℂ) - (Q : ℂ) ^ N := by
        rw [norm_pow, hc, Complex.norm_real, Real.norm_of_nonneg ha]; push_cast; ring
      have : (a : ℂ) - (Q : ℂ) ^ N = ((a - Q ^ N : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
      have h3 : |‖(a : ℂ)‖ - ‖c ^ N‖| ≤ ‖(a : ℂ) - c ^ N‖ := abs_norm_sub_norm_le _ _
      rw [norm_pow, hc, Complex.norm_real, Real.norm_of_nonneg ha, norm_sub_rev, h1] at h3
      exact h3
    calc ‖c ^ N - (Q : ℂ) ^ N‖ = ‖(c ^ N - a) + ((a : ℂ) - (Q : ℂ) ^ N)‖ := by ring_nf
      _ ≤ ‖c ^ N - a‖ + ‖(a : ℂ) - (Q : ℂ) ^ N‖ := norm_add_le _ _
      _ ≤ ‖e N‖ + ‖e N‖ := by rw [h1]; gcongr
      _ ≤ 2 * (C * R ^ N) := by linarith [he N]
  -- hence `‖c - Q‖ ≤ 2 C (R + Q) (R / Q) ^ N`
  have bound : ∀ N ≥ 1, ‖c - Q‖ ≤ 2 * C * (R + Q) * (R / Q) ^ N := by
    intro N hN
    have hQN : 0 < Q ^ N := pow_pos hQ N
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hQN]
    have hid : c ^ N * (c - Q) =
        (c ^ (N + 1) - (Q : ℂ) ^ (N + 1)) - (Q : ℂ) * (c ^ N - (Q : ℂ) ^ N) := by ring
    have hnorm : ‖c - Q‖ * Q ^ N = ‖c ^ N * (c - Q)‖ := by
      rw [norm_mul, norm_pow, hc, mul_comm]
    rw [hnorm, hid]
    calc ‖(c ^ (N + 1) - (Q : ℂ) ^ (N + 1)) - (Q : ℂ) * (c ^ N - (Q : ℂ) ^ N)‖
        ≤ ‖c ^ (N + 1) - (Q : ℂ) ^ (N + 1)‖ + ‖(Q : ℂ) * (c ^ N - (Q : ℂ) ^ N)‖ :=
          norm_sub_le _ _
      _ = ‖c ^ (N + 1) - (Q : ℂ) ^ (N + 1)‖ + Q * ‖c ^ N - (Q : ℂ) ^ N‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hQ.le]
      _ ≤ 2 * (C * R ^ (N + 1)) + Q * (2 * (C * R ^ N)) := by
          gcongr
          · exact key (N + 1) (by omega)
          · exact key N hN
      _ = 2 * C * (R + Q) * R ^ N := by ring
  have hlim : Tendsto (fun N : ℕ => 2 * C * (R + Q) * (R / Q) ^ N) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hQ.le)
      ((div_lt_one hQ).2 hRQ)
    simpa using this.const_mul (2 * C * (R + Q))
  have hle : ‖c - Q‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => bound N hN⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- If `‖c‖ = Q` and `‖e N‖ ≤ C R ^ N` with `0 ≤ R < Q`, then `c ^ N + e N ≠ 0` for all
large `N`. -/
theorem exists_forall_pow_add_ne_zero {c : ℂ} {Q R C : ℝ} {e : ℕ → ℂ} (hR : 0 ≤ R)
    (hRQ : R < Q) (hc : ‖c‖ = Q) (he : ∀ N, ‖e N‖ ≤ C * R ^ N) :
    ∃ N₀, ∀ N ≥ N₀, c ^ N + e N ≠ 0 := by
  have hQ : 0 < Q := hR.trans_lt hRQ
  have hlim : Tendsto (fun N : ℕ => C * (R / Q) ^ N) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hQ.le)
      ((div_lt_one hQ).2 hRQ)
    simpa using this.const_mul C
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨N₀, fun N hN h0 => ?_⟩
  have hQN : 0 < Q ^ N := pow_pos hQ N
  have h1 : C * R ^ N < Q ^ N := by
    have := hN₀ N hN
    rwa [div_pow, ← mul_div_assoc, div_lt_one hQN] at this
  have h2 : ‖c ^ N‖ ≤ ‖e N‖ := by
    rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
  rw [norm_pow, hc] at h2
  linarith [he N]

end Complex

/-! ### Traces of powers and roots of the characteristic polynomial -/

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Over an algebraically closed field, the trace of `f ^ N` is the sum of the `N`-th powers of
the roots of the characteristic polynomial of `f`, counted with multiplicity. -/
theorem trace_pow_eq_sum_roots_charpoly_pow [IsAlgClosed K] (f : Module.End K V) (N : ℕ) :
    LinearMap.trace K V (f ^ N) = (f.charpoly.roots.map (· ^ N)).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hf : ∀ μ, Set.MapsTo (f ^ N) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right N)
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hf]
  have key : ∀ μ, LinearMap.trace K _ ((f ^ N).restrict (hf μ)) =
      (f.charpoly.rootMultiplicity μ : K) * μ ^ N := by
    intro μ
    have h1 := f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
    rw [← LinearMap.finrank_maxGenEigenspace_eq, ← Module.End.pow_restrict N h1]
    have hnil := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    induction N with
    | zero => simp [LinearMap.trace_one]
    | succ n ih =>
      rw [pow_succ, Module.End.mul_eq_comp,
        LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
          ((Commute.refl _).pow_left n) hnil, ih (f.mapsTo_maxGenEigenspace_of_comm
            ((Commute.refl f).pow_right n))]
      ring
  rw [Finset.sum_congr rfl fun μ _ => key μ, Finset.sum_multiset_map_count]
  have hne : f.charpoly ≠ 0 := f.charpoly_monic.ne_zero
  have hset : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Multiset.mem_toFinset, mem_roots hne, ne_eq,
      ← Submodule.finrank_eq_zero, LinearMap.finrank_maxGenEigenspace_eq,
      ← rootMultiplicity_pos hne]
    omega
  rw [hset]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, nsmul_eq_mul]

end Module.End

namespace Matrix

/-- Over an algebraically closed field, the trace of `A ^ N` is the sum of the `N`-th powers of
the roots of the characteristic polynomial of `A`, counted with multiplicity. -/
theorem trace_pow_eq_sum_roots_charpoly_pow {K n : Type*} [Field K] [IsAlgClosed K] [Fintype n]
    [DecidableEq n] (A : Matrix n n K) (N : ℕ) :
    (A ^ N).trace = (A.charpoly.roots.map (· ^ N)).sum := by
  rw [← Matrix.charpoly_toLin', ← Module.End.trace_pow_eq_sum_roots_charpoly_pow,
    ← Matrix.toLin'_pow, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K n),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

end Matrix

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Along a ring homomorphism `ι` into an algebraically closed field, the image of the trace of
`φ ^ N` is the sum of the `N`-th powers of the roots of the image of the characteristic polynomial
of `φ`. -/
theorem map_trace_pow_eq_sum_roots_charpoly_map_pow {L : Type*} [Field L] [IsAlgClosed L]
    (ι : K →+* L) (φ : Module.End K V) (N : ℕ) :
    ι (LinearMap.trace K V (φ ^ N)) = (((φ.charpoly.map ι).roots).map (· ^ N)).sum := by
  set b := Module.finBasis K V
  rw [LinearMap.trace_eq_matrix_trace K b, ← LinearMap.toMatrix_pow, ← charpoly_toMatrix φ b,
    ← Matrix.charpoly_map, ← Matrix.trace_pow_eq_sum_roots_charpoly_pow, ← Matrix.map_pow,
    Matrix.trace, Matrix.trace, map_sum]
  rfl

/-- If every root of the image of the characteristic polynomial of `φ` in `ℂ` has absolute value
at most `R`, then `‖ι (Tr (φ ^ N))‖ ≤ dim V · R ^ N`. -/
theorem norm_map_trace_pow_le (ι : K →+* ℂ) (φ : Module.End K V) {R : ℝ}
    (hroots : ∀ z, (φ.charpoly.map ι).IsRoot z → ‖z‖ ≤ R) (N : ℕ) :
    ‖ι (LinearMap.trace K V (φ ^ N))‖ ≤ Module.finrank K V * R ^ N := by
  rw [map_trace_pow_eq_sum_roots_charpoly_map_pow]
  have hne : φ.charpoly.map ι ≠ 0 := (φ.charpoly_monic.map ι).ne_zero
  have hR : ∀ z ∈ (φ.charpoly.map ι).roots, ‖z ^ N‖ ≤ R ^ N := fun z hz => by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hroots z ((mem_roots hne).1 hz)) N
  calc ‖(((φ.charpoly.map ι).roots).map (· ^ N)).sum‖
      ≤ (((φ.charpoly.map ι).roots).map fun z => ‖z ^ N‖).sum := by
        simpa [Multiset.map_map] using norm_multiset_sum_le (((φ.charpoly.map ι).roots).map (· ^ N))
    _ ≤ (((φ.charpoly.map ι).roots).map fun _ => R ^ N).sum :=
        Multiset.sum_map_le_sum_map _ _ hR
    _ = ((φ.charpoly.map ι).roots.card : ℝ) * R ^ N := by
        simp [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    _ = Module.finrank K V * R ^ N := by
        rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map, charpoly_natDegree]

/-- The characteristic polynomial of `μ • id` on a line is `X - C μ`. -/
theorem charpoly_smul_id_of_finrank_eq_one (h : Module.finrank K V = 1) (μ : K) :
    (μ • LinearMap.id : Module.End K V).charpoly = X - C μ := by
  have hmon := (μ • LinearMap.id : Module.End K V).charpoly_monic
  have hdeg : (μ • LinearMap.id : Module.End K V).charpoly.natDegree = 1 := by
    rw [charpoly_natDegree, h]
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hroot : (μ • LinearMap.id : Module.End K V).charpoly.IsRoot μ := by
    rw [← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simp), hv⟩
  rw [hmon.eq_X_add_C hdeg] at hroot ⊢
  have : (μ • LinearMap.id : Module.End K V).charpoly.coeff 0 = -μ := by
    simp only [IsRoot, eval_add, eval_X, eval_C] at hroot
    linear_combination hroot
  rw [this, C_neg, sub_eq_add_neg]

end LinearMap

/-! ### Pure endomorphisms with natural alternating traces -/

namespace Module.End

variable {K : Type*} [Field K] {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
  [∀ i, FiniteDimensional K (V i)]

/-- For a family `φᵢ`, `0 ≤ i ≤ 2d`, pure of weight `i` along `ι` with `V_{2d}` a line,
`φ_{2d} = μ • id` with `‖ι μ‖ = Q ^ d`, and the alternating sum of the traces of `φᵢ ^ N` differs
from `μ ^ N` by `O(Q ^ ((2d - 1) / 2 · N))` along `ι`. -/
theorem exists_eq_smul_id_and_norm_map_alternating_trace_pow_sub_le (ι : K →+* ℂ) {Q : ℕ}
    (hQ : 1 < Q) {d : ℕ} (φ : ∀ i, Module.End K (V i))
    (hpure : ∀ i ≤ 2 * d, ∀ z, ((φ i).charpoly.map ι).IsRoot z → ‖z‖ = (Q : ℝ) ^ ((i : ℝ) / 2))
    (hline : Module.finrank K (V (2 * d)) = 1) :
    ∃ μ : K, φ (2 * d) = μ • LinearMap.id ∧ ‖ι μ‖ = (Q : ℝ) ^ d ∧ ∃ C : ℝ, ∀ N,
      ‖ι (∑ i ∈ Finset.range (2 * d + 1), (-1 : K) ^ i * LinearMap.trace K (V i) (φ i ^ N)) -
        ι μ ^ N‖ ≤ C * ((Q : ℝ) ^ (((2 * d : ℝ) - 1) / 2)) ^ N := by
  obtain ⟨μ, hμ, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hline (φ (2 * d))
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.le
  refine ⟨μ, hμ, ?_, ∑ i ∈ Finset.range (2 * d), (Module.finrank K (V i) : ℝ), fun N => ?_⟩
  · have hroot : ((φ (2 * d)).charpoly.map ι).IsRoot (ι μ) := by
      rw [hμ, LinearMap.charpoly_smul_id_of_finrank_eq_one hline]
      simp
    rw [hpure (2 * d) le_rfl _ hroot, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  · rw [Finset.sum_range_succ, hμ, smul_pow, map_smul, ← Module.End.one_eq_id, one_pow,
      LinearMap.trace_one, hline, (Even.neg_one_pow ⟨d, two_mul d⟩ : (-1 : K) ^ (2 * d) = 1)]
    simp only [Nat.cast_one, smul_eq_mul, mul_one, one_mul, map_add, map_pow, add_sub_cancel_right]
    rw [map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hi' : i < 2 * d := Finset.mem_range.1 hi
    rw [map_mul, norm_mul, map_pow, map_neg, map_one, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    refine (LinearMap.norm_map_trace_pow_le ι (φ i)
      (fun z hz => (hpure i hi'.le z hz).le) N).trans ?_
    gcongr
    have : (i : ℝ) + 1 ≤ 2 * d := by exact_mod_cast hi'
    linarith

/-- **Lang–Weil-lite.** Let `φᵢ` (`0 ≤ i ≤ 2d`) be endomorphisms of finite-dimensional
`K`-vector spaces whose eigenvalues have absolute value `Q ^ (i / 2)` along `ι : K →+* ℂ`, with
`V_{2d}` a line. If the alternating sums `∑ᵢ (-1) ^ i Tr(φᵢ ^ N)` are natural numbers for all
`N ≥ 1`, then `φ_{2d}` is multiplication by `Q ^ d`. -/
theorem eq_pow_smul_id_of_isPure_of_alternating_trace_eq_natCast (ι : K →+* ℂ) {Q : ℕ}
    (hQ : 1 < Q) {d : ℕ} (φ : ∀ i, Module.End K (V i))
    (hpure : ∀ i ≤ 2 * d, ∀ z, ((φ i).charpoly.map ι).IsRoot z → ‖z‖ = (Q : ℝ) ^ ((i : ℝ) / 2))
    (hline : Module.finrank K (V (2 * d)) = 1)
    (hcount : ∀ N ≥ 1, ∃ a : ℕ,
      ∑ i ∈ Finset.range (2 * d + 1), (-1 : K) ^ i * LinearMap.trace K (V i) (φ i ^ N) = a) :
    φ (2 * d) = (Q : K) ^ d • LinearMap.id := by
  obtain ⟨μ, hμ, hnorm, C, hC⟩ :=
    exists_eq_smul_id_and_norm_map_alternating_trace_pow_sub_le ι hQ φ hpure hline
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hR : (Q : ℝ) ^ (((2 * d : ℝ) - 1) / 2) < (Q : ℝ) ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt hQ1 (by linarith)
  have key := Complex.eq_of_forall_pow_add_eq_ofReal_nonneg (Real.rpow_nonneg (by positivity) _)
    hR hnorm (e := fun N => ι (∑ i ∈ Finset.range (2 * d + 1),
      (-1 : K) ^ i * LinearMap.trace K (V i) (φ i ^ N)) - ι μ ^ N) hC (fun N hN => by
        obtain ⟨a, ha⟩ := hcount N hN
        exact ⟨a, a.cast_nonneg, by simp [ha]⟩)
  have : μ = (Q : K) ^ d := ι.injective (by rw [key]; simp)
  rw [hμ, this]

/-- Under the hypotheses of `eq_pow_smul_id_of_isPure_of_alternating_trace_eq_natCast`, the
characteristic polynomial of `φ_{2d}` is `X - Q ^ d`. -/
theorem charpoly_eq_X_sub_C_of_isPure_of_alternating_trace_eq_natCast (ι : K →+* ℂ) {Q : ℕ}
    (hQ : 1 < Q) {d : ℕ} (φ : ∀ i, Module.End K (V i))
    (hpure : ∀ i ≤ 2 * d, ∀ z, ((φ i).charpoly.map ι).IsRoot z → ‖z‖ = (Q : ℝ) ^ ((i : ℝ) / 2))
    (hline : Module.finrank K (V (2 * d)) = 1)
    (hcount : ∀ N ≥ 1, ∃ a : ℕ,
      ∑ i ∈ Finset.range (2 * d + 1), (-1 : K) ^ i * LinearMap.trace K (V i) (φ i ^ N) = a) :
    (φ (2 * d)).charpoly = X - C ((Q : K) ^ d) := by
  rw [eq_pow_smul_id_of_isPure_of_alternating_trace_eq_natCast ι hQ φ hpure hline hcount,
    LinearMap.charpoly_smul_id_of_finrank_eq_one hline]

/-- For a family `φᵢ` (`0 ≤ i ≤ 2d`) pure of weight `i` along `ι : K →+* ℂ` with `V_{2d}` a
line, the alternating sums `∑ᵢ (-1) ^ i Tr(φᵢ ^ N)` are nonzero for all large `N`. -/
theorem exists_forall_alternating_trace_pow_ne_zero_of_isPure (ι : K →+* ℂ) {Q : ℕ}
    (hQ : 1 < Q) {d : ℕ} (φ : ∀ i, Module.End K (V i))
    (hpure : ∀ i ≤ 2 * d, ∀ z, ((φ i).charpoly.map ι).IsRoot z → ‖z‖ = (Q : ℝ) ^ ((i : ℝ) / 2))
    (hline : Module.finrank K (V (2 * d)) = 1) :
    ∃ N₀, ∀ N ≥ N₀,
      ∑ i ∈ Finset.range (2 * d + 1), (-1 : K) ^ i * LinearMap.trace K (V i) (φ i ^ N) ≠ 0 := by
  obtain ⟨μ, -, hnorm, C, hC⟩ :=
    exists_eq_smul_id_and_norm_map_alternating_trace_pow_sub_le ι hQ φ hpure hline
  have hQ1 : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hR : (Q : ℝ) ^ (((2 * d : ℝ) - 1) / 2) < (Q : ℝ) ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt hQ1 (by linarith)
  obtain ⟨N₀, hN₀⟩ := Complex.exists_forall_pow_add_ne_zero
    (Real.rpow_nonneg (by positivity) _) hR hnorm (e := fun N => ι (∑ i ∈ Finset.range (2 * d + 1),
      (-1 : K) ^ i * LinearMap.trace K (V i) (φ i ^ N)) - ι μ ^ N) hC
  refine ⟨N₀, fun N hN h0 => hN₀ N hN ?_⟩
  simp [h0]

end Module.End
