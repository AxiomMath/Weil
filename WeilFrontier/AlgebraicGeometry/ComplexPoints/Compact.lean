module

public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Functoriality
public import Weil.Attr

/-!
# Complex points of separated and projective schemes

Let `Y` be a scheme over `ℂ`, and give `Y(ℂ)` the analytic topology. If `Y` is separated, `Y(ℂ)`
is Hausdorff: two points of one affine open are separated by a regular function, and for points
`p ∈ U \ W`, `q ∈ W \ U` of affine opens `U`, `W`, the surjectivity of
`Γ(Y, U) ⊗ Γ(Y, W) → Γ(Y, U ∩ W)` gives a tensor `∑ aᵢ ⊗ bᵢ` vanishing on `U ∩ W` with
`∑ aᵢ(p) bᵢ(q) ≠ 0`; the function `(s, t) ↦ ∑ aᵢ(s) bᵢ(t)` then separates `p` from `q`.

If `Y` is projective, `Y(ℂ)` is moreover compact. It is a closed subspace of `ℙⁿ(ℂ)`, and
`ℙⁿ(ℂ)` is covered by the images of the `n + 1` closed unit polydiscs of the standard charts: a
point with homogeneous coordinates `[a₀ : ⋯ : aₙ]` lies in the polydisc of the chart `Tᵢ ≠ 0`
for which `|aᵢ|` is maximal.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.t2Space_of_isSeparated`: `Y(ℂ)` is Hausdorff for `Y`
  separated over `ℂ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.compactSpace_projectiveSpaceOver`: `ℙⁿ(ℂ)` is
  compact.
* `AlgebraicGeometry.Scheme.ComplexPoints.compactSpace_of_isProjective`: `Y(ℂ)` is compact for
  `Y` projective over `ℂ`.
* `AlgebraicGeometry.Scheme.ComplexPoints.t2Space_of_isProjective`: and Hausdorff.

## Implementation notes

Projectivity is `AlgebraicGeometry.IsProjective` (Stacks, Tag 01W8), a closed immersion into the
projective bundle of a quasi-coherent module of finite type; over the affine base `Spec ℂ` it
gives a closed immersion into `ℙⁿ_ℂ = ℙⁿ_ℤ ×_ℤ Spec ℂ`. Compactness of `ℙⁿ(ℂ)` is proved on the
isomorphic model `Proj ℂ[T₀, …, Tₙ]`, whose standard charts are the spectra of the polynomial
rings `ℂ[T_j / Tᵢ]`.

## References

* [SGA1] A. Grothendieck, *Revêtements étales et groupe fondamental*, Exposé XII, §2.
* [Stacks] The Stacks Project, Tags 01KP, 01W8.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {Y : Scheme.{0}} {y : Y ⟶ Spec (.of ℂ)}

/-! ### Separation -/

/-- Two distinct points of one affine open have disjoint neighbourhoods. -/
theorem exists_disjoint_of_mem {U : Y.Opens} (hU : IsAffineOpen U) {p q : ComplexPoints y}
    (hp : p.Mem U) (hq : q.Mem U) (hpq : p ≠ q) :
    ∃ u v : Set (ComplexPoints y), IsOpen u ∧ IsOpen v ∧ p ∈ u ∧ q ∈ v ∧ Disjoint u v := by
  obtain ⟨g, hg⟩ : ∃ g : Γ(Y, U), eval g p hp ≠ eval g q hq := by
    by_contra! h
    exact hpq (eq_of_eval_eq hU hp hq h)
  obtain ⟨A, B, hA, hB, hpA, hqB, hAB⟩ := t2_separation hg
  refine ⟨basicSet U g A, basicSet U g B, isOpen_basicSet hU g hA, isOpen_basicSet hU g hB,
    ⟨hp, hpA⟩, ⟨hq, hqB⟩, Set.disjoint_left.2 ?_⟩
  rintro r ⟨hr, hrA⟩ ⟨hr', hrB⟩
  exact Set.disjoint_left.1 hAB hrA hrB

section Tensor

variable {U W : Y.Opens}

/-- The evaluation `Γ(Y, U) ⊗ Γ(Y, W) → ℂ`, `a ⊗ b ↦ a(s) b(t)`, at a pair of points. -/
noncomputable def evalTensor (s t : ComplexPoints y) (hs : s.Mem U) (ht : t.Mem W) :
    Γ(Y, U) ⊗[ℤ] Γ(Y, W) →ₐ[ℤ] ℂ :=
  Algebra.TensorProduct.productMap (evalHom s hs).toIntAlgHom (evalHom t ht).toIntAlgHom

theorem evalTensor_tmul (s t : ComplexPoints y) (hs : s.Mem U) (ht : t.Mem W) (a : Γ(Y, U))
    (b : Γ(Y, W)) : evalTensor s t hs ht (a ⊗ₜ b) = eval a s hs * eval b t ht :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ a b

/-- On the diagonal, the evaluation of a tensor is the value of its image on `U ∩ W`. -/
theorem evalTensor_self (r : ComplexPoints y) (hU : r.Mem U) (hW : r.Mem W)
    (hUW : r.Mem (U ⊓ W)) (k : Γ(Y, U) ⊗[ℤ] Γ(Y, W)) :
    evalTensor r r hU hW k = eval (sectionTensorMap Y U W k) r hUW := by
  induction k using TensorProduct.induction_on with
  | zero => simp
  | add k₁ k₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, eval_add]
  | tmul a b =>
    rw [evalTensor_tmul, Algebra.TensorProduct.lift_tmul, eval_mul]
    exact congrArg₂ (· * ·) (eval_map inf_le_left a r hUW).symm (eval_map inf_le_right b r hUW).symm

/-- The evaluation of a fixed tensor is continuous in the pair of points. -/
theorem continuous_evalTensor (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (k : Γ(Y, U) ⊗[ℤ] Γ(Y, W)) :
    Continuous fun st : {p : ComplexPoints y // p.Mem U} × {p : ComplexPoints y // p.Mem W} =>
      evalTensor st.1.1 st.2.1 st.1.2 st.2.2 k := by
  induction k using TensorProduct.induction_on with
  | zero => simpa using continuous_const
  | add k₁ k₂ h₁ h₂ => simp only [map_add]; exact h₁.add h₂
  | tmul a b =>
    simp only [evalTensor_tmul]
    exact ((continuous_eval hU a).comp continuous_fst).mul ((continuous_eval hW b).comp
      continuous_snd)

end Tensor

/-- **The complex points of a separated scheme over `ℂ` form a Hausdorff space.** -/
instance t2Space_of_isSeparated [IsSeparated y] : T2Space (ComplexPoints y) := by
  refine ⟨fun p q hpq => ?_⟩
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
    (show p.hom.base pt ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨W, hW, hxW, -⟩ := (Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens)
    (show q.hom.base pt ∈ (⊤ : Y.Opens) from trivial)
  have hpU : p.Mem U := (mem_iff pt).2 hxU
  have hqW : q.Mem W := (mem_iff pt).2 hxW
  by_cases hqU : q.Mem U
  · exact exists_disjoint_of_mem hU hpU hqU hpq
  by_cases hpW : p.Mem W
  · exact exists_disjoint_of_mem hW hpW hqW hpq
  have hUW : IsAffineOpen (U ⊓ W) := isAffineOpen_inf_of_isSeparated y hU hW
  have hsurj := sectionTensorMap_surjective_of_isSeparated y U W hU hW ⊤
    (isAffineOpen_top _) (by simp) (by simp)
  obtain ⟨k, hk, hkpq⟩ : ∃ k ∈ RingHom.ker (sectionTensorMap Y U W).toRingHom,
      evalTensor p q hpU hqW k ≠ 0 := by
    by_contra! h
    let F := (sectionTensorMap Y U W).toRingHom
    let χ : Γ(Y, U ⊓ W) →+* ℂ := F.liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj)
      ⟨(evalTensor p q hpU hqW).toRingHom, fun k hk => (RingHom.mem_ker).2 (h k hk)⟩
    have hχ : ∀ k, χ (F k) = evalTensor p q hpU hqW k := fun k =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ k
    have hres : ∀ a : Γ(Y, U), χ (Y.presheaf.map (homOfLE inf_le_left).op a) = eval a p hpU := by
      intro a
      have := hχ (a ⊗ₜ 1)
      rw [evalTensor_tmul, eval_one, mul_one] at this
      rw [← this]
      congr 1
      simp [F, sectionTensorMap]
    have hc : ∀ c, χ (constHom (y := y) (U ⊓ W) c) = c := by
      intro c
      rw [← map_constHom (inf_le_left : U ⊓ W ≤ U), hres, eval_constHom]
    have hr := ofRingHom_mem hUW hc
    have hrp : ofRingHom hUW hc = p := eq_of_eval_eq hU (hr.mono inf_le_left) hpU fun a => by
      rw [← eval_map inf_le_left a _ hr, eval_ofRingHom, hres]
    exact hpW (hrp ▸ hr.mono inf_le_right)
  have hF := continuous_evalTensor (y := y) hU hW k
  have hO : IsOpen {st : {p : ComplexPoints y // p.Mem U} × {p : ComplexPoints y // p.Mem W} |
      evalTensor st.1.1 st.2.1 st.1.2 st.2.2 k ≠ 0} := isOpen_ne_fun hF continuous_const
  obtain ⟨A, B, hA, hB, hpA, hqB, hAB⟩ := isOpen_prod_iff.1 hO ⟨p, hpU⟩ ⟨q, hqW⟩ hkpq
  refine ⟨Subtype.val '' A, Subtype.val '' B, (isOpen_setOf_mem U).isOpenMap_subtype_val _ hA,
    (isOpen_setOf_mem W).isOpenMap_subtype_val _ hB, ⟨_, hpA, rfl⟩, ⟨_, hqB, rfl⟩,
    Set.disjoint_left.2 ?_⟩
  rintro _ ⟨a, ha, rfl⟩ ⟨⟨b, hb'⟩, hb, hab⟩
  change b = a.1 at hab
  subst hab
  apply hAB (show (a, ⟨a.1, hb'⟩) ∈ A ×ˢ B from ⟨ha, hb⟩)
  have hUW' : a.1.Mem (U ⊓ W) := (mem_iff pt).2 ⟨(mem_iff pt).1 a.2, (mem_iff pt).1 hb'⟩
  change evalTensor a.1 a.1 a.2 hb' k = 0
  rw [evalTensor_self a.1 a.2 hb' hUW', show sectionTensorMap Y U W k = 0 from hk, eval_zero]


/-! ### Points of affine schemes -/

/-- The complex point `Spec ℂ ⟶ Spec R` of a ring homomorphism `φ : R → ℂ` over `c : ℂ → R`. -/
noncomputable def ofSpecMap {R : CommRingCat.{0}} {c : CommRingCat.of ℂ ⟶ R}
    (φ : R ⟶ CommRingCat.of ℂ) (hφ : c ≫ φ = 𝟙 _) : ComplexPoints (Spec.map c) :=
  ⟨Spec.map φ, by rw [← Spec.map_comp, hφ, Spec.map_id]⟩

theorem eval_ofSpecMap {R : CommRingCat.{0}} {c : CommRingCat.of ℂ ⟶ R}
    (φ : R ⟶ CommRingCat.of ℂ) (hφ : c ≫ φ = 𝟙 _) (g : Γ(Spec R, ⊤))
    (h : (ofSpecMap φ hφ).Mem ⊤) :
    eval g (ofSpecMap φ hφ) h = φ ((Scheme.ΓSpecIso R).hom g) := by
  change (Scheme.ΓSpecIso (.of ℂ)).hom ((Spec.map φ).appLE ⊤ ⊤ (Spec.map φ).preimage_top.ge g) = _
  rw [appLE_top_top_eq_appTop, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

/-- A family of ring homomorphisms `R → ℂ` over `ℂ` depending continuously on a parameter gives a
continuous family of complex points of `Spec R`. -/
theorem continuous_ofSpecMap {R : CommRingCat.{0}} {c : CommRingCat.of ℂ ⟶ R} {X : Type*}
    [TopologicalSpace X] (φ : X → (R ⟶ CommRingCat.of ℂ)) (hφ : ∀ x, c ≫ φ x = 𝟙 _)
    (hc : ∀ r : R, Continuous fun x => φ x r) :
    Continuous fun x => ofSpecMap (φ x) (hφ x) := by
  have hi := isInducing_evalMap (y := Spec.map c) (isAffineOpen_top _)
  have : Continuous fun x => (⟨ofSpecMap (φ x) (hφ x), mem_top _⟩ :
      {p : ComplexPoints (Spec.map c) // p.Mem ⊤}) := by
    rw [hi.continuous_iff]
    refine continuous_pi fun g => ?_
    simp only [Function.comp_apply, evalMap, eval_ofSpecMap]
    exact hc _
  exact continuous_subtype_val.comp this

/-! ### Projective space -/

section ProjectiveSpace

open HomogeneousLocalization Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ)

/-- The standard chart `Spec ℂ[T]_{(Tᵢ)} ⟶ Proj ℂ[T₀, …, Tₙ]`. -/
noncomputable abbrev chartι (i : Fin (n + 1)) :
    Spec (.of (Away (polyGrading ℂ n) (MvPolynomial.X i))) ⟶ Proj (polyGrading ℂ n) :=
  Proj.awayι (polyGrading ℂ n) (MvPolynomial.X i) (X_mem_one ℂ n i) one_pos

theorem chartι_comp (i : Fin (n + 1)) :
    chartι n i ≫ projToSpecCoeff ℂ n = Spec.map (CommRingCat.ofHom (coeffToAway ℂ n i)) := by
  rw [projToSpecCoeff, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [MvPolynomial.algebraMap_eq, RingHom.coe_comp, Function.comp_apply,
    val_fromZeroRingHom, GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply]
  rw [DirectSum.decompose_of_mem_same]
  · rw [coeffToAway_eq_mk, Away.val_mk]
    exact congrArg (Localization.mk _) (Subtype.ext (pow_zero _).symm)
  · exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ _)


/-- The fraction `T_j / T_i` on the `i`-th standard chart. -/
noncomputable abbrev frac (i j : Fin (n + 1)) : Away (polyGrading ℂ n) (MvPolynomial.X i) :=
  Away.mk (polyGrading ℂ n) (X_mem_one ℂ n i) 1 (MvPolynomial.X j) (X_mem_smul ℂ n j)

theorem frac_self (i : Fin (n + 1)) : frac n i i = 1 := by
  ext
  simp [Away.val_mk]

/-- `(T_j / T_i) · (T_i / T_k) = T_j / T_k` on the intersection of the `k`-th and `i`-th charts. -/
theorem awayMap_frac_mul_awayMap_frac (k i j : Fin (n + 1)) :
    awayMap (polyGrading ℂ n) (X_mem_one ℂ n k)
        (mul_comm (MvPolynomial.X k) (MvPolynomial.X i)) (frac n i j) *
      awayMap (polyGrading ℂ n) (X_mem_one ℂ n i) rfl (frac n k i) =
    awayMap (polyGrading ℂ n) (X_mem_one ℂ n i) rfl (frac n k j) := by
  simp only [frac, awayMap_mk]
  ext
  simp only [val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The point of `Proj ℂ[T₀, …, Tₙ]` in the `i`-th standard chart attached to a ring
homomorphism `ℂ[T]_{(Tᵢ)} → ℂ` over `ℂ`. -/
noncomputable def chartPoint (i : Fin (n + 1))
    (φ : Away (polyGrading ℂ n) (MvPolynomial.X i) →+* ℂ)
    (hφ : ∀ r, φ (coeffToAway ℂ n i r) = r) : ComplexPoints (projToSpecCoeff ℂ n) :=
  map (chartι n i) (chartι_comp n i)
    (ofSpecMap (CommRingCat.ofHom φ) (by ext r; exact hφ r))

theorem chartPoint_hom (i : Fin (n + 1)) (φ : Away (polyGrading ℂ n) (MvPolynomial.X i) →+* ℂ)
    (hφ : ∀ r, φ (coeffToAway ℂ n i r) = r) :
    (chartPoint n i φ hφ).hom = Spec.map (CommRingCat.ofHom φ) ≫ chartι n i := rfl

/-- The ring homomorphism `ℂ[T]_{(Tᵢ)} → ℂ` sending `T_j / T_i` to `z j`. -/
noncomputable def chartEval (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    Away (polyGrading ℂ n) (MvPolynomial.X i) →+* ℂ :=
  (MvPolynomial.eval z).comp (chartEquiv ℂ n i).symm.toRingHom

theorem chartEval_coeffToAway (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) (r : ℂ) :
    chartEval n i z (coeffToAway ℂ n i r) = r := by
  have : (chartEquiv ℂ n i).symm (coeffToAway ℂ n i r) = MvPolynomial.C r := by
    rw [RingEquiv.symm_apply_eq, chartEquiv_apply, chartHom_C]
  simp [chartEval, this]

theorem chartEval_frac (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ)
    (j : {j : Fin (n + 1) // j ≠ i}) : chartEval n i z (frac n i j) = z j := by
  have : (chartEquiv ℂ n i).symm (frac n i j) = MvPolynomial.X j := by
    rw [RingEquiv.symm_apply_eq, chartEquiv_apply, chartHom_X]
    rfl
  simp [chartEval, this]

/-- The parametrization of the `i`-th standard chart by `ℂⁿ`. -/
noncomputable def chartParam (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    ComplexPoints (projToSpecCoeff ℂ n) :=
  chartPoint n i (chartEval n i z) (chartEval_coeffToAway n i z)

theorem continuous_chartParam (i : Fin (n + 1)) : Continuous (chartParam n i) :=
  (continuous_map _ _).comp (continuous_ofSpecMap _ _ fun r =>
    MvPolynomial.continuous_eval ((chartEquiv ℂ n i).symm r))


/-- **Every complex point of `ℙⁿ` lies in a closed polydisc of a standard chart.** If `p` has
homogeneous coordinates `[a₀ : ⋯ : aₙ]` and `|aᵢ|` is maximal, then `p` is the point of the
`i`-th chart with affine coordinates `a_j / aᵢ`, all of absolute value at most one. -/
theorem exists_chartParam (p : ComplexPoints (projToSpecCoeff ℂ n)) :
    ∃ (i : Fin (n + 1)) (z : {j : Fin (n + 1) // j ≠ i} → ℂ),
      (∀ j, ‖z j‖ ≤ 1) ∧ chartParam n i z = p := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  have hx : p.hom.base pt ∈ (⊤ : (Proj (polyGrading ℂ n)).Opens) := trivial
  rw [← iSup_basicOpen_X_eq_top ℂ n] at hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hpk : p.Mem (chartι n k).opensRange := by
    rw [Proj.opensRange_awayι]
    exact (mem_iff pt).2 hk
  obtain ⟨q, rfl⟩ : p ∈ Set.range (map (chartι n k) (chartι_comp n k)) := by
    rw [range_map_of_isOpenImmersion]
    exact hpk
  set φ := Spec.preimage q.hom
  have hφ : ∀ r, φ.hom (coeffToAway ℂ n k r) = r := by
    have h1 : Spec.map (CommRingCat.ofHom (coeffToAway ℂ n k) ≫ φ) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, Spec.map_preimage, q.hom_comp, Spec.map_id]
    intro r
    exact congrArg (fun f => f.hom r) (Spec.map_injective h1)
  have hq : map (chartι n k) (chartι_comp n k) q = chartPoint n k φ.hom hφ :=
    ext (by rw [chartPoint_hom, map_hom, CommRingCat.ofHom_hom, Spec.map_preimage])
  rw [hq]
  set a : Fin (n + 1) → ℂ := fun j => φ.hom (frac n k j) with ha
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖a j‖
  have hak : a k = 1 := by simp [a, frac_self]
  have hai : a i ≠ 0 := by
    intro h
    have := hi k
    rw [hak, h] at this
    norm_num at this
  -- the localization `ℂ[T]_{(TₖTᵢ)} = ℂ[T]_{(Tₖ)}[(Tᵢ/Tₖ)⁻¹]`
  let x : MvPolynomial (Fin (n + 1)) ℂ := MvPolynomial.X k * MvPolynomial.X i
  let ιk := awayMap (polyGrading ℂ n) (X_mem_one ℂ n i) (rfl : x = _)
  let ιi := awayMap (polyGrading ℂ n) (X_mem_one ℂ n k) (mul_comm _ _ : x = _)
  let := ιk.toAlgebra
  have := Away.isLocalization_mul (X_mem_one ℂ n k) (X_mem_one ℂ n i) (rfl : x = _) one_ne_zero
  have he : Away.isLocalizationElem (X_mem_one ℂ n k) (X_mem_one ℂ n i) = frac n k i := by
    ext
    simp [Away.val_mk]
  have hunit : IsUnit (φ.hom (Away.isLocalizationElem (X_mem_one ℂ n k) (X_mem_one ℂ n i))) := by
    rw [he]
    exact hai.isUnit
  let φ'' : Away (polyGrading ℂ n) x →+* ℂ := IsLocalization.Away.lift _ hunit
  have hφ'' : φ''.comp ιk = φ.hom := IsLocalization.Away.lift_comp _ hunit
  have hφ''a : ∀ w, φ'' (ιk w) = φ.hom w := fun w => by rw [← RingHom.comp_apply, hφ'']
  let φ' := φ''.comp ιi
  have hφ' : ∀ r, φ' (coeffToAway ℂ n i r) = r := by
    intro r
    have : ιi (coeffToAway ℂ n i r) = ιk (coeffToAway ℂ n k r) := by
      simp only [ιi, ιk, coeffToAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_eq,
        awayMap_fromZeroRingHom]
      rfl
    simp only [φ', RingHom.comp_apply, this, hφ''a, hφ]
  have hpts : chartPoint n k φ.hom hφ = chartPoint n i φ' hφ' := by
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
  refine ⟨i, fun j => a j / a i, fun j => ?_, ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ (hi j) (norm_nonneg _)
  · rw [hpts]
    have hev : chartEval n i (fun j => a j / a i) = φ' := by
      apply RingHom.ext
      intro w
      obtain ⟨P, rfl⟩ := chartHom_surjective ℂ n i w
      rw [← RingHom.comp_apply, ← RingHom.comp_apply φ']
      congr 1
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
      · simp only [RingHom.comp_apply, chartHom_C, chartEval_coeffToAway, hφ']
      · simp only [RingHom.comp_apply, chartHom_X]
        exact (chartEval_frac n i _ j).trans (hval j).symm
    exact ext (by rw [chartParam, chartPoint_hom, chartPoint_hom, hev])


/-- **`ℙⁿ(ℂ)` is compact**, in the model `Proj ℂ[T₀, …, Tₙ]`: it is the union of the images of
the `n + 1` closed unit polydiscs of the standard charts. -/
instance compactSpace_proj : CompactSpace (ComplexPoints (projToSpecCoeff ℂ n)) := by
  rw [← isCompact_univ_iff]
  have : (Set.univ : Set (ComplexPoints (projToSpecCoeff ℂ n))) =
      ⋃ i, chartParam n i '' Set.univ.pi fun _ => Metric.closedBall 0 1 := by
    refine (Set.eq_univ_of_forall fun p => ?_).symm
    obtain ⟨i, z, hz, rfl⟩ := exists_chartParam n p
    exact Set.mem_iUnion.2 ⟨i, z, fun j _ => by simpa using hz j, rfl⟩
  rw [this]
  exact isCompact_iUnion fun i =>
    (isCompact_univ_pi fun _ => isCompact_closedBall 0 1).image (continuous_chartParam n i)

/-- **`ℙⁿ(ℂ)` is compact**, for projective space `ℙⁿ_ℂ = ℙⁿ_ℤ ×_ℤ Spec ℂ`. -/
instance compactSpace_projectiveSpaceOver :
    CompactSpace (ComplexPoints (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ))) := by
  have hf : projCompare ℂ n ≫ (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) =
      projToSpecCoeff ℂ n := projCompare_fst ℂ n
  have hg : inv (projCompare ℂ n) ≫ projToSpecCoeff ℂ n =
      (projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ)) := by
    rw [← hf, IsIso.inv_hom_id_assoc]
  refine Function.Surjective.compactSpace (continuous_map _ hf) fun p => ⟨map _ hg p, ?_⟩
  rw [← map_comp]
  exact ext (by simp)

end ProjectiveSpace

/-- **The complex points of a projective scheme over `ℂ` form a compact space.** -/
theorem compactSpace_of_isProjective (hy : IsProjective y) : CompactSpace (ComplexPoints y) := by
  obtain ⟨n, i, hi, hiy⟩ := isProjectiveMorphism_of_isProjective_of_isAffine y hy
  exact (isClosedEmbedding_map_of_isClosedImmersion i hiy).compactSpace

/-- The complex points of a projective scheme over `ℂ` form a Hausdorff space. -/
theorem t2Space_of_isProjective (hy : IsProjective y) : T2Space (ComplexPoints y) :=
  have := hy.isSeparated
  inferInstance

end AlgebraicGeometry.Scheme.ComplexPoints
