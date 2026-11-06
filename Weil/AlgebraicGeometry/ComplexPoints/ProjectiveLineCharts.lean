/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.AlgebraicGeometry.ComplexPoints.Compact
public import Weil.Topology.Covering.BranchedCover

/-!
# The complex projective line as a Riemann sphere

The complex points `ℙ¹(ℂ)` of the projective line, with the analytic topology, are covered by the
two standard charts `T₀ ≠ 0` and `T₁ ≠ 0`. Each chart is the spectrum of the polynomial ring
`ℂ[T₁ / T₀]`, resp. `ℂ[T₀ / T₁]`, so its complex points are identified with `ℂ` by the value of
the affine coordinate. On the overlap the two coordinates are inverse to each other, and the point
`[0 : 1]` lies only in the second chart. This presents `ℙ¹(ℂ)` as the Riemann sphere.

More generally, for every `n`, the complex points of the `i`-th standard chart of
`Proj ℂ[T₀, …, Tₙ]` are an open subspace of `ℙⁿ(ℂ)` homeomorphic to `ℂⁿ` by the affine
coordinates `T_j / Tᵢ`, `j ≠ i`.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.projectiveLineCharts`: the two standard charts
  `ℂ → ℙ¹(ℂ)`, as `Weil.RiemannSphereCharts`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.isOpenEmbedding_chartParam`: the parametrization of a
  standard chart of `ℙⁿ(ℂ)` by `ℂⁿ` is an open embedding.
* `AlgebraicGeometry.Scheme.ComplexPoints.chartPoint_eq_chartParam`: a point of the `k`-th chart
  at which `T_i / T_k` does not vanish is the point of the `i`-th chart with coordinates
  `(T_j / T_k) / (T_i / T_k)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.homeomorphProjectiveSpaceOver`: the complex points of the
  model `Proj ℂ[T₀, …, Tₙ]` and of `ℙⁿ_ℂ = ℙⁿ_ℤ ×_ℤ Spec ℂ` are homeomorphic.
* `AlgebraicGeometry.Scheme.ComplexPoints.t2Space_projectiveSpaceOver`: `ℙⁿ(ℂ)` is Hausdorff.

## Implementation notes

The charts are built on the model `Proj ℂ[T₀, T₁]`, whose standard charts are the spectra of the
polynomial rings `ℂ[T_j / T_i]`, and transported to `ℙ¹_ℂ = ℙ¹_ℤ ×_ℤ Spec ℂ` along the
comparison isomorphism of the two models. That the point at infinity `[0 : 1]` of the first chart
is not in its range is deduced from compactness: otherwise the first chart would be a
homeomorphism from `ℂ` onto the compact space `ℙ¹(ℂ)`.

## References

* [Stacks] The Stacks Project, Tag 01MB.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.Scheme.ComplexPoints

open HomogeneousLocalization Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ)

/-! ### The standard charts of `ℙⁿ(ℂ)` -/

/-- The point of `Spec ℂ[T]_{(Tᵢ)}` with affine coordinates `z`. -/
noncomputable def chartSpecPoint (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    ComplexPoints (Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i))) :=
  ofSpecMap (CommRingCat.ofHom (chartEval n i z)) (by ext r; exact chartEval_coeffToAway n i z r)

theorem chartParam_eq_map (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    chartParam n i z = map (chartι n i) (chartι_comp n i) (chartSpecPoint n i z) := rfl

/-- The affine coordinates `T_j / Tᵢ` of a point of `Spec ℂ[T]_{(Tᵢ)}`. -/
noncomputable def chartCoord (i : Fin (n + 1))
    (p : ComplexPoints (Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i))))
    (j : {j : Fin (n + 1) // j ≠ i}) : ℂ :=
  eval ((Scheme.ΓSpecIso (.of (Away (polyGrading ℂ n) (MvPolynomial.X i)))).inv (frac n i j)) p
    (mem_top p)

theorem continuous_chartCoord (i : Fin (n + 1)) : Continuous (chartCoord n i) := by
  refine continuous_pi fun j => ?_
  have h := continuous_eval (y := Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i)))
    (isAffineOpen_top (Spec (.of (Away (polyGrading ℂ n) (MvPolynomial.X i)))))
    ((Scheme.ΓSpecIso (.of (Away (polyGrading ℂ n) (MvPolynomial.X i)))).inv (frac n i j))
  have h2 : Continuous fun p : ComplexPoints (Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i))) =>
      (⟨p, mem_top p⟩ :
        {q : ComplexPoints (Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i))) // q.Mem ⊤}) :=
    continuous_id.subtype_mk _
  have h3 := h.comp h2
  refine h3.congr fun p => ?_
  simp only [Function.comp_apply]
  rfl

theorem chartCoord_chartSpecPoint (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    chartCoord n i (chartSpecPoint n i z) = z := by
  funext j
  rw [chartCoord, chartSpecPoint, eval_ofSpecMap]
  simp only [Iso.inv_hom_id_apply, CommRingCat.hom_ofHom]
  exact chartEval_frac n i z j

/-- A ring homomorphism `ℂ[T]_{(Tᵢ)} → ℂ` over `ℂ` is the evaluation at its values on the
`T_j / Tᵢ`. -/
theorem chartEval_eq (i : Fin (n + 1)) (φ : Away (polyGrading ℂ n) (MvPolynomial.X i) →+* ℂ)
    (hφ : ∀ r, φ (coeffToAway ℂ n i r) = r) :
    chartEval n i (fun j : {j : Fin (n + 1) // j ≠ i} => φ (frac n i j)) = φ := by
  apply RingHom.ext
  intro w
  obtain ⟨P, rfl⟩ := chartHom_surjective ℂ n i w
  rw [← RingHom.comp_apply, ← RingHom.comp_apply φ]
  congr 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
  · simp only [RingHom.comp_apply, chartHom_C, chartEval_coeffToAway, hφ]
  · simp only [RingHom.comp_apply, chartHom_X]
    exact chartEval_frac n i _ j

theorem chartSpecPoint_chartCoord (i : Fin (n + 1))
    (p : ComplexPoints (Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i)))) :
    chartSpecPoint n i (chartCoord n i p) = p := by
  set φ := Spec.preimage p.hom
  have hφ : CommRingCat.ofHom (coeffToAway ℂ n i) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, p.hom_comp, Spec.map_id]
  have hp : p = ofSpecMap φ hφ :=
    ext (by change p.hom = Spec.map φ; exact (Spec.map_preimage _).symm)
  have hc : chartCoord n i p = fun j : {j : Fin (n + 1) // j ≠ i} => φ.hom (frac n i j) := by
    funext j
    rw [chartCoord]
    conv_lhs => rw [hp]
    rw [eval_ofSpecMap]
    simp only [Iso.inv_hom_id_apply]
  have hφ' : ∀ r, φ.hom (coeffToAway ℂ n i r) = r := fun r =>
    congrArg (fun f => f.hom r) hφ
  apply ext
  rw [hc]
  change Spec.map (CommRingCat.ofHom (chartEval n i _)) = p.hom
  rw [chartEval_eq n i φ.hom hφ']
  exact Spec.map_preimage _

/-- The complex points of `Spec ℂ[T]_{(Tᵢ)}` are homeomorphic to `ℂⁿ` by the affine
coordinates. -/
noncomputable def chartSpecHomeomorph (i : Fin (n + 1)) :
    ({j : Fin (n + 1) // j ≠ i} → ℂ) ≃ₜ
      ComplexPoints (Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i))) where
  toFun := chartSpecPoint n i
  invFun := chartCoord n i
  left_inv := chartCoord_chartSpecPoint n i
  right_inv := chartSpecPoint_chartCoord n i
  continuous_toFun := continuous_ofSpecMap _ _ fun r =>
    MvPolynomial.continuous_eval ((chartEquiv ℂ n i).symm r)
  continuous_invFun := continuous_chartCoord n i

/-- **The parametrization of a standard chart of `ℙⁿ(ℂ)` by `ℂⁿ` is an open embedding.** -/
theorem isOpenEmbedding_chartParam (i : Fin (n + 1)) : IsOpenEmbedding (chartParam n i) := by
  have h : chartParam n i = map (chartι n i) (chartι_comp n i) ∘ chartSpecHomeomorph n i := rfl
  rw [h]
  exact (isOpenEmbedding_map_of_isOpenImmersion (chartι n i) (chartι_comp n i)).comp
    (chartSpecHomeomorph n i).isOpenEmbedding

/-- **Change of chart.** A point of the `k`-th standard chart at which `T_i / T_k` does not
vanish is the point of the `i`-th chart with coordinates `(T_j / T_k) / (T_i / T_k)`. -/
theorem chartPoint_eq_chartParam (k i : Fin (n + 1))
    (φ : Away (polyGrading ℂ n) (MvPolynomial.X k) →+* ℂ)
    (hφ : ∀ r, φ (coeffToAway ℂ n k r) = r) (hai : φ (frac n k i) ≠ 0) :
    chartPoint n k φ hφ = chartParam n i fun j => φ (frac n k j) / φ (frac n k i) := by
  set a : Fin (n + 1) → ℂ := fun j => φ (frac n k j) with ha
  -- the localization `ℂ[T]_{(TₖTᵢ)} = ℂ[T]_{(Tₖ)}[(Tᵢ/Tₖ)⁻¹]`
  let x : MvPolynomial (Fin (n + 1)) ℂ := MvPolynomial.X k * MvPolynomial.X i
  let ιk := awayMap (polyGrading ℂ n) (X_mem_one ℂ n i) (rfl : x = _)
  let ιi := awayMap (polyGrading ℂ n) (X_mem_one ℂ n k) (mul_comm _ _ : x = _)
  let := ιk.toAlgebra
  have := Away.isLocalization_mul (X_mem_one ℂ n k) (X_mem_one ℂ n i) (rfl : x = _) one_ne_zero
  have he : Away.isLocalizationElem (X_mem_one ℂ n k) (X_mem_one ℂ n i) = frac n k i := by
    ext
    simp [Away.val_mk]
  have hunit : IsUnit (φ (Away.isLocalizationElem (X_mem_one ℂ n k) (X_mem_one ℂ n i))) := by
    rw [he]
    exact hai.isUnit
  let φ'' : Away (polyGrading ℂ n) x →+* ℂ := IsLocalization.Away.lift _ hunit
  have hφ'' : φ''.comp ιk = φ := IsLocalization.Away.lift_comp _ hunit
  have hφ''a : ∀ w, φ'' (ιk w) = φ w := fun w => by rw [← RingHom.comp_apply, hφ'']
  let φ' := φ''.comp ιi
  have hφ' : ∀ r, φ' (coeffToAway ℂ n i r) = r := by
    intro r
    have : ιi (coeffToAway ℂ n i r) = ιk (coeffToAway ℂ n k r) := by
      simp only [ιi, ιk, coeffToAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_eq,
        awayMap_fromZeroRingHom]
      rfl
    simp only [φ', RingHom.comp_apply, this, hφ''a, hφ]
  have hpts : chartPoint n k φ hφ = chartPoint n i φ' hφ' := by
    apply ext
    rw [chartPoint_hom, chartPoint_hom, ← hφ'']
    simp only [φ', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ιk, ιi]
    rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]
  have hval : ∀ j, φ' (frac n i j) = a j / a i := by
    intro j
    have := congrArg φ'' (awayMap_frac_mul_awayMap_frac n k i j)
    rw [map_mul] at this
    change φ' (frac n i j) * φ'' (ιk (frac n k i)) = φ'' (ιk (frac n k j)) at this
    rw [hφ''a, hφ''a] at this
    exact eq_div_of_mul_eq hai this
  rw [hpts]
  have hev : chartEval n i (fun j => a j / a i) = φ' := by
    rw [← chartEval_eq n i φ' hφ']
    congr 1
    funext j
    exact (hval j).symm
  exact ext (by rw [chartParam, chartPoint_hom, chartPoint_hom, hev])

/-! ### The two models of `ℙⁿ` -/

theorem projCompare_comp :
    projCompare ℂ n ≫ (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) =
      projToSpecCoeff ℂ n := projCompare_fst ℂ n

theorem inv_projCompare_comp : inv (projCompare ℂ n) ≫ projToSpecCoeff ℂ n =
    (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) := by
  rw [← projCompare_comp, IsIso.inv_hom_id_assoc]

/-- The map `Proj ℂ[T₀, …, Tₙ](ℂ) → ℙⁿ(ℂ)` induced by the comparison isomorphism. -/
noncomputable def toProjectiveSpaceOver :
    ComplexPoints (projToSpecCoeff ℂ n) →
      ComplexPoints (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) :=
  map _ (projCompare_comp n)

/-- The map `ℙⁿ(ℂ) → Proj ℂ[T₀, …, Tₙ](ℂ)` induced by the comparison isomorphism. -/
noncomputable def ofProjectiveSpaceOver :
    ComplexPoints (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) →
      ComplexPoints (projToSpecCoeff ℂ n) :=
  map _ (inv_projCompare_comp n)

/-- The complex points of the model `Proj ℂ[T₀, …, Tₙ]` and of `ℙⁿ_ℂ = ℙⁿ_ℤ ×_ℤ Spec ℂ` are
homeomorphic, along the comparison isomorphism of the two models. -/
noncomputable def homeomorphProjectiveSpaceOver :
    ComplexPoints (projToSpecCoeff ℂ n) ≃ₜ
      ComplexPoints (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) where
  toFun := toProjectiveSpaceOver n
  invFun := ofProjectiveSpaceOver n
  left_inv p := ext (by
    simp only [toProjectiveSpaceOver, ofProjectiveSpaceOver, map_hom, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id])
  right_inv p := ext (by
    simp only [toProjectiveSpaceOver, ofProjectiveSpaceOver, map_hom, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id])
  continuous_toFun := continuous_map _ (projCompare_comp n)
  continuous_invFun := continuous_map _ (inv_projCompare_comp n)

/-! ### The Riemann sphere -/

instance unique_ne_zero : Unique {j : Fin (1 + 1) // j ≠ 0} :=
  ⟨⟨⟨1, by decide⟩⟩, fun ⟨j, hj⟩ => Subtype.ext (by revert hj; revert j; decide)⟩

instance unique_ne_one : Unique {j : Fin (1 + 1) // j ≠ 1} :=
  ⟨⟨⟨0, by decide⟩⟩, fun ⟨j, hj⟩ => Subtype.ext (by revert hj; revert j; decide)⟩

/-- The `i`-th standard chart `ℂ → ℙ¹(ℂ)`, in the model `Proj ℂ[T₀, T₁]`. -/
noncomputable def lineChart (i : Fin (1 + 1)) [Unique {j : Fin (1 + 1) // j ≠ i}] (w : ℂ) :
    ComplexPoints (projToSpecCoeff ℂ 1) :=
  chartParam 1 i fun _ => w

theorem isOpenEmbedding_lineChart (i : Fin (1 + 1)) [Unique {j : Fin (1 + 1) // j ≠ i}] :
    IsOpenEmbedding (lineChart i) :=
  (isOpenEmbedding_chartParam 1 i).comp (Homeomorph.funUnique _ ℂ).symm.isOpenEmbedding

theorem lineChart_zero_eq (w : ℂ) (hw : w ≠ 0) : lineChart 0 w = lineChart 1 w⁻¹ := by
  have h1 : chartEval 1 0 (fun _ => w) (frac 1 0 1) = w :=
    chartEval_frac 1 0 (fun _ => w) ⟨1, by decide⟩
  have h0 : chartEval 1 0 (fun _ => w) (frac 1 0 0) = 1 := by rw [frac_self, map_one]
  rw [lineChart, chartParam, chartPoint_eq_chartParam 1 0 1 _ _ (by rw [h1]; exact hw), lineChart]
  congr 1
  funext j
  obtain rfl : j = ⟨0, by decide⟩ := Subsingleton.elim _ _
  rw [h0, h1, one_div]

theorem range_lineChart_union : Set.range (lineChart 0) ∪ Set.range (lineChart 1) = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  obtain ⟨i, z, -, rfl⟩ := exists_chartParam 1 p
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · left
    exact ⟨z default, by
      rw [lineChart]; exact congrArg _ (funext fun j => congrArg z (Subsingleton.elim _ _))⟩
  · right
    exact ⟨z default, by
      rw [lineChart]; exact congrArg _ (funext fun j => congrArg z (Subsingleton.elim _ _))⟩

/-- The point at infinity `[0 : 1]` is not in the first chart: otherwise the first chart would
be a homeomorphism from `ℂ` onto the compact space `ℙ¹(ℂ)`. -/
theorem lineChart_one_zero_notMem : lineChart 1 0 ∉ Set.range (lineChart 0) := by
  rintro ⟨w₀, hw₀⟩
  have hrange : Set.range (lineChart 0) = Set.univ := by
    refine Set.eq_univ_of_forall fun p => ?_
    rcases (Set.ext_iff.1 range_lineChart_union p).2 trivial with h | ⟨u, rfl⟩
    · exact h
    · by_cases hu : u = 0
      · exact ⟨w₀, hu ▸ hw₀⟩
      · exact ⟨u⁻¹, by rw [lineChart_zero_eq _ (inv_ne_zero hu), inv_inv]⟩
  have he := isOpenEmbedding_lineChart 0
  have : IsClosedEmbedding (lineChart 0) :=
    ⟨he.isEmbedding, by rw [hrange]; exact isClosed_univ⟩
  have := this.compactSpace
  exact not_compactSpace_iff.2 inferInstance this

/-- **`ℙ¹(ℂ)` is a Riemann sphere**: the two standard charts `ℂ → ℙ¹(ℂ)` of
`ℙ¹_ℂ = ℙ¹_ℤ ×_ℤ Spec ℂ`, with affine coordinates `T₁ / T₀` and `T₀ / T₁`. -/
noncomputable def projectiveLineCharts :
    Weil.RiemannSphereCharts
      (ComplexPoints (projectiveSpaceOver 1 (Spec (.of ℂ)) ↘ Spec (.of ℂ))) where
  φ₀ := homeomorphProjectiveSpaceOver 1 ∘ lineChart 0
  φ₁ := homeomorphProjectiveSpaceOver 1 ∘ lineChart 1
  isOpenEmbedding_φ₀ := (homeomorphProjectiveSpaceOver 1).isOpenEmbedding.comp
    (isOpenEmbedding_lineChart 0)
  isOpenEmbedding_φ₁ := (homeomorphProjectiveSpaceOver 1).isOpenEmbedding.comp
    (isOpenEmbedding_lineChart 1)
  range_union := by
    rw [Set.range_comp, Set.range_comp, ← Set.image_union, range_lineChart_union,
      Set.image_univ, Homeomorph.range_coe]
  φ₁_zero_notMem := by
    rw [Set.range_comp, Function.comp_apply,
      (homeomorphProjectiveSpaceOver 1).injective.mem_set_image]
    exact lineChart_one_zero_notMem
  transition w hw := by
    simp only [Function.comp_apply, lineChart_zero_eq w hw]

theorem projectiveLineCharts_φ₀ (w : ℂ) :
    projectiveLineCharts.φ₀ w = homeomorphProjectiveSpaceOver 1 (lineChart 0 w) := rfl

theorem projectiveLineCharts_φ₁ (w : ℂ) :
    projectiveLineCharts.φ₁ w = homeomorphProjectiveSpaceOver 1 (lineChart 1 w) := rfl

/-- **`ℙⁿ(ℂ)` is Hausdorff** (an instance already, since `ℙⁿ_ℂ` is separated over `ℂ`). -/
theorem t2Space_projectiveSpaceOver :
    T2Space (ComplexPoints (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ))) :=
  inferInstance

end AlgebraicGeometry.Scheme.ComplexPoints
