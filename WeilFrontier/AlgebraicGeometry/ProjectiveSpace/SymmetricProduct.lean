module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.PolynomialModel
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Glue
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistPinnedChart.Pinning
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The symmetric-product morphism `(ℙ¹)^d ⟶ ℙ^d`

Let `k` be a field. A point `((a₁ : b₁), …, (a_d : b_d))` of the `d`-fold fibre power
`(ℙ¹_k)^d = ℙ¹_k ×_k ⋯ ×_k ℙ¹_k` determines the binary form `∏ᵢ (bᵢ X - aᵢ Y)` of degree `d`,
well defined up to a unit, and its `d + 1` coefficients are a point of `ℙ^d_k`. This file
constructs the resulting morphism `σ : (ℙ¹_k)^d ⟶ ℙ^d_k` and proves that it is proper, finite and
surjective, the last two over an infinite field.

On the product chart `∏ᵢ D₊(X_{εᵢ})`, `ε : Fin d → Fin 2`, the factor `bᵢ X - aᵢ Y` is the
polynomial `tᵢ X - 1` or `X - tᵢ` in the chart coordinate `tᵢ`, and the morphism of the chart is
`AlgebraicGeometry.Proj.fromOfGlobalSections` of the coefficients of the product. On an overlap
the two products differ by a unit, so the chart morphisms glue.

* *Properness*: `(ℙ¹_k)^d` is proper over `k` and `ℙ^d_k` is separated.
* *Finiteness*: a proper affine morphism is finite. For `λ ∈ k` the hyperplane
  `F(λ, 1) ≠ 0` of `ℙ^d_k` pulls back to `∏ᵢ (ℙ¹ ∖ {(λ : 1)})`, a product of affine opens, and
  `d + 1` distinct values of `λ` give hyperplanes covering `ℙ^d_k` (Vandermonde).
* *Surjectivity*: the image is closed. Over the chart `F(1, 0) ≠ 0` the generic point
  `(t₁, …, t_d)` of `(𝔸¹)^d` maps to the coefficients of `∏ᵢ (X + tᵢ)`, the elementary symmetric
  polynomials, which are algebraically independent; so the image contains a dense subset of that
  chart, hence the chart, hence everything, `ℙ^d_k` being irreducible.

## Main definitions

* `AlgebraicGeometry.SymmetricProduct.fiberPower`: the `d`-fold fibre power of an `S`-scheme,
  `X^{d+1} = X ×_S X^d`, with its projections `fiberPowerπ`.
* `AlgebraicGeometry.SymmetricProduct.linePower`: `(ℙ¹_k)^d`, with `ℙ¹_k = Proj k[X₀, X₁]`.
* `AlgebraicGeometry.SymmetricProduct.symmetricProductPoly`: `σ` into `Proj k[c₀, …, c_d]`.
* `AlgebraicGeometry.SymmetricProduct.symmetricProduct`: `σ` into
  `AlgebraicGeometry.projectiveSpaceOver d (Spec k)`.

## Main results

* `AlgebraicGeometry.SymmetricProduct.symmetricProduct_comp_fst`: `σ` lies over `Spec k`.
* `AlgebraicGeometry.SymmetricProduct.isProper_symmetricProduct`: `σ` is proper.
* `AlgebraicGeometry.SymmetricProduct.isFinite_symmetricProduct_of_injective`: `σ` is finite as
  soon as `k` has `d + 1` distinct elements; `isFinite_symmetricProduct` for infinite `k`.
* `AlgebraicGeometry.SymmetricProduct.surjective_symmetricProduct`: `σ` is surjective for
  infinite `k`.
* `AlgebraicGeometry.SymmetricProduct.symmetricProductPoly_preimage_basicOpen`: the preimage of
  the hyperplane chart `D₊(F(λ, 1))` is `∏ᵢ (ℙ¹ ∖ {(λ : 1)})`.

## Implementation notes

The factors of the source are the polynomial model `Proj k[X₀, X₁]` of `ℙ¹_k`; the target is
given both in the polynomial model and, through
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`, in the base-change model
`projectiveSpaceOver d (Spec k)`. The point `(a : b)` corresponds to the form `b X - a Y`, whose
dehomogenized coefficient vector `(c₀, …, c_d)` lists the coefficients of `X⁰, …, X^d`.

Finiteness and surjectivity are proved over a field with at least `d + 1` elements, resp. an
infinite field: both arguments use `k`-rational points of `ℙ¹` (the hyperplane charts) or the
infinitude of `k` (a polynomial vanishing on `k^{d+1}` is zero).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace AlgebraicGeometry.SymmetricProduct

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The coordinate `X_{1-a}/X_a` on the chart `D₊(X_a)` of `ℙ¹`. -/
noncomputable def lineCoord (a : Fin 2) : HomogeneousLocalization.Away (polyGrading k 1)
    (MvPolynomial.X a) :=
  HomogeneousLocalization.Away.mk (polyGrading k 1) (X_mem_one k 1 a) 1
    (MvPolynomial.X (1 - a)) (by simpa using X_mem_one k 1 (1 - a))

theorem awayMap_lineCoord_mul :
    HomogeneousLocalization.awayMap (polyGrading k 1) (X_mem_one k 1 1)
        (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = _)
        (lineCoord k 0) *
      HomogeneousLocalization.awayMap (polyGrading k 1) (X_mem_one k 1 0)
        (mul_comm _ _ : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = _)
        (lineCoord k 1) = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [lineCoord, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring


/-! ### Algebra of products of linear factors -/

section Algebra

open _root_.Polynomial

variable {R : Type*} [CommRing R]

/-- The linear factor attached to a point of `ℙ¹` in the chart `D₊(X_a)` with coordinate `T`:
`T X - 1` on `D₊(X₀)` and `X - T` on `D₊(X₁)`. -/
noncomputable def linearFactor (a : Fin 2) (T : R) : R[X] :=
  if a = 0 then C T * Polynomial.X - 1 else Polynomial.X - C T

theorem linearFactor_map {S : Type*} [CommRing S] (φ : R →+* S) (a : Fin 2) (T : R) :
    (linearFactor a T).map φ = linearFactor a (φ T) := by
  unfold linearFactor; split_ifs <;> simp

theorem natDegree_linearFactor_le (a : Fin 2) (T : R) : (linearFactor a T).natDegree ≤ 1 := by
  unfold linearFactor; split_ifs
  · exact (natDegree_sub_le _ _).trans (by
      rw [natDegree_one]
      exact max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  · exact (natDegree_sub_le _ _).trans (by simpa using natDegree_X_le)

theorem linearFactor_ne_zero [Nontrivial R] (a : Fin 2) (T : R) : linearFactor a T ≠ 0 := by
  unfold linearFactor; split_ifs
  · intro h
    have := congrArg (coeff · 0) h
    simp at this
  · exact X_sub_C_ne_zero T

/-- Two linear factors of the same point in two charts differ by a unit. -/
theorem exists_unit_linearFactor_eq (a a' : Fin 2) (T T' : R) (h : a ≠ a' → T * T' = 1)
    (h' : a = a' → T = T') : ∃ u : Rˣ, linearFactor a T = C (u : R) * linearFactor a' T' := by
  by_cases haa : a = a'
  · subst haa; obtain rfl := h' rfl; exact ⟨1, by simp⟩
  · have hTT := h haa
    fin_cases a <;> fin_cases a'
    · exact absurd rfl haa
    · refine ⟨⟨T, T', hTT, by rw [mul_comm]; exact hTT⟩, ?_⟩
      simp [linearFactor]
      rw [mul_sub, ← C_mul, hTT, C_1]
    · refine ⟨⟨T, T', hTT, by rw [mul_comm]; exact hTT⟩, ?_⟩
      simp [linearFactor]
      rw [mul_sub, ← mul_assoc, ← C_mul, hTT, C_1, one_mul, mul_one]
    · exact absurd rfl haa

theorem natDegree_prod_linearFactor_le {d : ℕ} (a : Fin d → Fin 2) (T : Fin d → R) :
    (∏ i, linearFactor (a i) (T i)).natDegree ≤ d := by
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ i, (linearFactor (a i) (T i)).natDegree ≤ ∑ _i : Fin d, 1 :=
        Finset.sum_le_sum fun i _ => natDegree_linearFactor_le _ _
    _ = d := by simp

/-- The coefficients of a product of `d` linear factors span the unit ideal. -/
theorem span_coeff_prod_linearFactor {d : ℕ} (a : Fin d → Fin 2) (T : Fin d → R) :
    Ideal.span (Set.range fun j : Fin (d + 1) => (∏ i, linearFactor (a i) (T i)).coeff j) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  let φ := Ideal.Quotient.mk M
  let := Ideal.Quotient.field M
  have hprod : (∏ i, linearFactor (a i) (T i)).map φ ≠ 0 := by
    rw [Polynomial.map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by
      rw [linearFactor_map]; exact linearFactor_ne_zero _ _
  obtain ⟨j, hj⟩ := Polynomial.ext_iff.not.1 hprod |> not_forall.1
  rw [coeff_map, coeff_zero] at hj
  have hjd : j ≤ d := by
    by_contra hjd
    apply hj
    rw [coeff_eq_zero_of_natDegree_lt ((natDegree_prod_linearFactor_le a T).trans_lt
      (by omega)), map_zero]
  apply hj
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hle (Ideal.subset_span ⟨⟨j, by omega⟩, rfl⟩)


end Algebra

open MvPolynomial in
/-- The coefficients of the generic monic polynomial `∏ᵢ (X + tᵢ)` of degree `d`: a homogeneous
form in the coefficients vanishing on them is zero. -/
theorem eq_zero_of_eval₂_coeff_prod_X_add_C {k : Type*} [Field k] [Infinite k] {d n : ℕ}
    {p : MvPolynomial (Fin (d + 1)) k} (hp : p.IsHomogeneous n)
    (h : eval₂ C (fun j : Fin (d + 1) =>
      (∏ i : Fin d, (Polynomial.X + Polynomial.C (X i : MvPolynomial (Fin d) k))).coeff j) p = 0) :
    p = 0 := by
  classical
  -- dehomogenize at `c_d` and reindex
  let δ : MvPolynomial (Fin (d + 1)) k →ₐ[k] MvPolynomial (Fin d) k :=
    aeval fun j => if hj : (j : ℕ) < d then X ⟨d - 1 - j, by omega⟩ else 1
  have hδ : ((esymmAlgHom (Fin d) k d) (δ p)).val = 0 := by
    rw [esymmAlgHom_apply, ← h, ← AlgHom.comp_apply]
    change (aeval _ |>.comp δ) p = (aeval _ : MvPolynomial (Fin (d + 1)) k →ₐ[k] _) p
    congr 1
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [AlgHom.comp_apply, δ, aeval_X]
    have hjd : (j : ℕ) ≤ Fintype.card (Fin d) := by simpa using Nat.lt_succ_iff.mp j.2
    rw [MvPolynomial.prod_X_add_C_coeff (σ := Fin d) (R := k) (j : ℕ) hjd]
    split_ifs with hj
    · simp only [aeval_X, Fintype.card_fin]
      congr 1; omega
    · have : (j : ℕ) = d := by omega
      simp [this]
  have hδ0 : δ p = 0 := by
    have := esymmAlgHom_injective (σ := Fin d) k (n := d) (by simp)
    exact this (Subtype.ext (by simpa using hδ))
  -- conclude by evaluation, `k` being infinite
  have hXp : X (Fin.last d) * p = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x (Fin.last d) = 0
    · rw [hx, zero_mul]
    · rw [mul_eq_zero]; right
      have hsc : x = fun j => x (Fin.last d) * ((x (Fin.last d))⁻¹ * x j) := by
        funext j; rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
      rw [hsc]
      change (eval₂Hom (RingHom.id k) _) p = 0
      rw [MvPolynomial.IsHomogeneous.eval₂Hom_const_mul hp]
      refine mul_eq_zero_of_right _ ?_
      have : (eval₂Hom (RingHom.id k) fun j => (x (Fin.last d))⁻¹ * x j) p =
          eval (fun i : Fin d => (x (Fin.last d))⁻¹ * x ⟨d - 1 - i, by omega⟩) (δ p) := by
        change _ = ((eval (fun i : Fin d => (x (Fin.last d))⁻¹ * x ⟨d - 1 - i, by omega⟩)).comp
          (δ : MvPolynomial (Fin (d + 1)) k →+* MvPolynomial (Fin d) k)) p
        congr 1
        refine MvPolynomial.ringHom_ext (fun c => ?_) fun j => ?_
        · simp [δ]
        · simp only [RingHom.comp_apply, δ, AlgHom.coe_toRingHom, aeval_X, coe_eval₂Hom, eval₂_X]
          split_ifs with hj
          · simp only [eval_X]; congr 2; ext; simp; omega
          · have : j = Fin.last d := Fin.ext (by simp; omega)
            subst this; simp [hx]
      rw [this, hδ0, map_zero]
  exact (mul_eq_zero.mp hXp).resolve_left (X_ne_zero _)




/-! ### Fibre powers -/

section FiberPower

variable {S : Scheme.{u}}

/-- The `d`-fold fibre power `X ×_S ⋯ ×_S X` of an `S`-scheme, built as
`X^{d+1} = X ×_S X^d`. -/
noncomputable def fiberPower (X : Over S) : ℕ → Over S
  | 0 => Over.mk (𝟙 S)
  | d + 1 => Over.mk (pullback.snd X.hom (fiberPower X d).hom ≫ (fiberPower X d).hom)

/-- The projections of the fibre power onto its factors. -/
noncomputable def fiberPowerπ (X : Over S) : (d : ℕ) → Fin d → ((fiberPower X d).left ⟶ X.left)
  | d + 1, i => Fin.cases (pullback.fst X.hom (fiberPower X d).hom)
      (fun j => pullback.snd X.hom (fiberPower X d).hom ≫ fiberPowerπ X d j) i

@[simp] theorem fiberPowerπ_zero (X : Over S) (d : ℕ) :
    fiberPowerπ X (d + 1) 0 = pullback.fst X.hom (fiberPower X d).hom := rfl

@[simp] theorem fiberPowerπ_succ (X : Over S) (d : ℕ) (j : Fin d) :
    fiberPowerπ X (d + 1) j.succ = pullback.snd X.hom (fiberPower X d).hom ≫ fiberPowerπ X d j :=
  rfl

end FiberPower

/-! ### The charts of `(ℙ¹)^d` -/

/-- The projective line, in the polynomial model `Proj k[X₀, X₁]`. -/
noncomputable abbrev line : Scheme.{u} := Proj (polyGrading k 1)

/-- The projective line as a scheme over `Spec k`. -/
noncomputable abbrev lineOver : Over (Spec (CommRingCat.of k)) := Over.mk (projToSpecCoeff k 1)

/-- The `d`-fold fibre power of the projective line over `Spec k`. -/
noncomputable abbrev linePower (d : ℕ) : Over (Spec (CommRingCat.of k)) :=
  fiberPower (lineOver k) d

/-- The standard chart `D₊(X_a)` of `ℙ¹`. -/
noncomputable abbrev lineChart (a : Fin 2) : (line k).Opens :=
  Proj.basicOpen (polyGrading k 1) (MvPolynomial.X a)

/-- The coordinate `X_{1-a}/X_a`, as a function on the chart `D₊(X_a)`. -/
noncomputable def lineChartCoord (a : Fin 2) : Γ((lineChart k a).toScheme, ⊤) :=
  (lineChart k a).topIso.inv.hom
    ((Proj.awayToSection (polyGrading k 1) (MvPolynomial.X a)).hom (lineCoord k a))

/-- On any open contained in both charts the two coordinates are inverse to each other. -/
theorem lineChartCoord_mul_eq_one {W : (line k).Opens} (h0 : W ≤ lineChart k 0)
    (h1 : W ≤ lineChart k 1) :
    ((line k).homOfLE h0).appTop.hom (lineChartCoord k 0) *
      ((line k).homOfLE h1).appTop.hom (lineChartCoord k 1) = 1 := by
  set B := Proj.basicOpen (polyGrading k 1)
    (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) with hB
  have hWB : W ≤ B := by rw [hB, Proj.basicOpen_mul]; exact le_inf h0 h1
  have hB0 : B ≤ lineChart k 0 := Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩
  have hB1 : B ≤ lineChart k 1 := Proj.basicOpen_mono _ _ _ ⟨_, mul_comm _ _⟩
  rw [← Scheme.homOfLE_homOfLE (line k) hWB hB0, ← Scheme.homOfLE_homOfLE (line k) hWB hB1,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply,
    ← map_mul]
  convert map_one ((line k).homOfLE hWB).appTop.hom
  rw [lineChartCoord, lineChartCoord, homOfLE_appTop_topIso_inv, homOfLE_appTop_topIso_inv,
    ← map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Proj.awayMap_awayToSection (polyGrading k 1) (f := MvPolynomial.X 0) (X_mem_one k 1 1)
      (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = _),
    ← Proj.awayMap_awayToSection (polyGrading k 1) (f := MvPolynomial.X 1) (X_mem_one k 1 0)
      (mul_comm _ _ : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k) = _),
    CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul]
  erw [awayMap_lineCoord_mul]
  rw [map_one, map_one]


/-! ### Charts and coordinates on `(ℙ¹)^d` -/

variable {k}

/-- The `i`-th projection `(ℙ¹)^d ⟶ ℙ¹`. -/
noncomputable abbrev linePowerπ {d : ℕ} (i : Fin d) : (linePower k d).left ⟶ line k :=
  fiberPowerπ (lineOver k) d i

/-- The product chart `∏ᵢ D₊(X_{εᵢ})` of `(ℙ¹)^d`. -/
noncomputable def powChart {d : ℕ} (ε : Fin d → Fin 2) : (linePower k d).left.Opens :=
  ⨅ i, linePowerπ i ⁻¹ᵁ lineChart k (ε i)

theorem powChart_le {d : ℕ} (ε : Fin d → Fin 2) (i : Fin d) :
    powChart (k := k) ε ≤ linePowerπ i ⁻¹ᵁ lineChart k (ε i) :=
  iInf_le (fun i => linePowerπ (k := k) i ⁻¹ᵁ lineChart k (ε i)) i

/-- The point of `(ℙ¹)^d` lies in the product chart given by the chart of each coordinate. -/
theorem iSup_powChart {d : ℕ} : ⨆ ε : Fin d → Fin 2, powChart (k := k) ε = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  have hx : ∀ i : Fin d, ∃ a : Fin 2, linePowerπ (k := k) i x ∈ lineChart k a := by
    intro i
    have hmem : linePowerπ (k := k) i x ∈ (⨆ a : Fin 2, lineChart k a) := by
      rw [iSup_basicOpen_X_eq_top]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hmem
  choose ε hε using hx
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨ε, ?_⟩
  rw [powChart, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  exact hε

/-- The `i`-th coordinate on an open `W` mapped by the `i`-th projection into `D₊(X_a)`. -/
noncomputable def coordOn {d : ℕ} {W : (linePower k d).left.Opens} (i : Fin d) (a : Fin 2)
    (h : W ≤ linePowerπ i ⁻¹ᵁ lineChart k a) : Γ(W.toScheme, ⊤) :=
  ((linePowerπ i).resLE (lineChart k a) W h).appTop.hom (lineChartCoord k a)

theorem coordOn_congr {d : ℕ} {W : (linePower k d).left.Opens} (i : Fin d) {a a' : Fin 2}
    (haa : a = a') (h : W ≤ linePowerπ i ⁻¹ᵁ lineChart k a)
    (h' : W ≤ linePowerπ i ⁻¹ᵁ lineChart k a') : coordOn i a h = coordOn i a' h' := by
  subst haa; rfl

theorem appTop_homOfLE_coordOn {d : ℕ} {W W' : (linePower k d).left.Opens} (hW : W' ≤ W)
    (i : Fin d) (a : Fin 2) (h : W ≤ linePowerπ i ⁻¹ᵁ lineChart k a) :
    ((linePower k d).left.homOfLE hW).appTop.hom (coordOn i a h) = coordOn i a (hW.trans h) := by
  rw [coordOn, coordOn, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Scheme.Hom.map_resLE]

theorem coordOn_mul_coordOn {d : ℕ} {W : (linePower k d).left.Opens} (i : Fin d)
    (h0 : W ≤ linePowerπ i ⁻¹ᵁ lineChart k 0) (h1 : W ≤ linePowerπ i ⁻¹ᵁ lineChart k 1) :
    coordOn i 0 h0 * coordOn i 1 h1 = 1 := by
  have h : W ≤ linePowerπ i ⁻¹ᵁ (lineChart k 0 ⊓ lineChart k 1) := le_inf h0 h1
  have e0 := Scheme.Hom.resLE_map (linePowerπ (k := k) i) h (inf_le_left :
    lineChart k 0 ⊓ lineChart k 1 ≤ lineChart k 0)
  have e1 := Scheme.Hom.resLE_map (linePowerπ (k := k) i) h (inf_le_right :
    lineChart k 0 ⊓ lineChart k 1 ≤ lineChart k 1)
  rw [coordOn, coordOn, ← e0, ← e1, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul,
    lineChartCoord_mul_eq_one, map_one]

/-- The binary form `∏ᵢ ℓᵢ` (dehomogenized) attached to a point of the product chart `ε`, on an
open `W` contained in it. -/
noncomputable def chartPoly {d : ℕ} (ε : Fin d → Fin 2) {W : (linePower k d).left.Opens}
    (h : W ≤ powChart ε) : Polynomial Γ(W.toScheme, ⊤) :=
  ∏ i, linearFactor (ε i) (coordOn i (ε i) (h.trans (powChart_le ε i)))

theorem map_chartPoly {d : ℕ} (ε : Fin d → Fin 2) {W W' : (linePower k d).left.Opens}
    (hW : W' ≤ W) (h : W ≤ powChart ε) :
    (chartPoly ε h).map ((linePower k d).left.homOfLE hW).appTop.hom =
      chartPoly ε (hW.trans h) := by
  rw [chartPoly, chartPoly, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [linearFactor_map, appTop_homOfLE_coordOn]

/-- On an open in two product charts, the two binary forms differ by a unit. -/
theorem exists_unit_chartPoly_eq {d : ℕ} (ε ε' : Fin d → Fin 2) {W : (linePower k d).left.Opens}
    (h : W ≤ powChart ε) (h' : W ≤ powChart ε') :
    ∃ u : Γ(W.toScheme, ⊤)ˣ,
      chartPoly ε h = Polynomial.C (u : Γ(W.toScheme, ⊤)) * chartPoly ε' h' := by
  have key : ∀ i, ∃ u : Γ(W.toScheme, ⊤)ˣ,
      linearFactor (ε i) (coordOn i (ε i) (h.trans (powChart_le ε i))) =
        Polynomial.C (u : Γ(W.toScheme, ⊤)) *
          linearFactor (ε' i) (coordOn i (ε' i) (h'.trans (powChart_le ε' i))) := by
    intro i
    refine exists_unit_linearFactor_eq _ _ _ _ (fun hne => ?_) (fun heq => coordOn_congr i heq _ _)
    have hcases : (ε i = 0 ∧ ε' i = 1) ∨ (ε i = 1 ∧ ε' i = 0) := by omega
    rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [coordOn_congr i h0 _ (h.trans ((powChart_le ε i).trans (by rw [h0]))),
        coordOn_congr i h1 _ (h'.trans ((powChart_le ε' i).trans (by rw [h1])))]
      exact coordOn_mul_coordOn i _ _
    · rw [coordOn_congr i h0 _ (h.trans ((powChart_le ε i).trans (by rw [h0]))),
        coordOn_congr i h1 _ (h'.trans ((powChart_le ε' i).trans (by rw [h1]))), mul_comm]
      exact coordOn_mul_coordOn i _ _
  choose u hu using key
  refine ⟨∏ i, u i, ?_⟩
  rw [chartPoly, chartPoly, Finset.prod_congr rfl fun i _ => hu i, Finset.prod_mul_distrib,
    ← map_prod, Units.coe_prod]


/-! ### The chart morphisms and their gluing -/

open Stacks.ProjectiveSpaceChartRatio in
theorem appTop_comp_baseRingHom {Y Z : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ Spec (CommRingCat.of k)) :
    f.appTop.hom.comp (baseRingHom g) = baseRingHom (f ≫ g) := by
  simp only [baseRingHom, Scheme.Hom.comp_appTop]
  rfl

open Stacks.ProjectiveSpaceChartRatio in
/-- The ring homomorphism `k[c₀, …, c_d] → Γ(W, 𝒪)` sending `c_j` to the `j`-th coefficient of the
binary form of the product chart `ε`. -/
noncomputable def chartHom {d : ℕ} (ε : Fin d → Fin 2) {W : (linePower k d).left.Opens}
    (h : W ≤ powChart ε) : MvPolynomial (Fin (d + 1)) k →+* Γ(W.toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (baseRingHom (W.ι ≫ (linePower k d).hom))
    (fun j => (chartPoly ε h).coeff j)

theorem span_coeff_chartPoly {d : ℕ} (ε : Fin d → Fin 2) {W : (linePower k d).left.Opens}
    (h : W ≤ powChart ε) :
    Ideal.span (Set.range fun j : Fin (d + 1) => (chartPoly ε h).coeff j) = ⊤ :=
  span_coeff_prod_linearFactor _ _

theorem appTop_homOfLE_comp_chartHom {d : ℕ} (ε : Fin d → Fin 2)
    {W W' : (linePower k d).left.Opens} (hW : W' ≤ W) (h : W ≤ powChart ε) :
    ((linePower k d).left.homOfLE hW).appTop.hom.comp (chartHom ε h) =
      chartHom ε (hW.trans h) := by
  rw [chartHom, MvPolynomial.comp_eval₂Hom, chartHom, appTop_comp_baseRingHom,
    Scheme.homOfLE_ι_assoc]
  congr 1
  funext j
  rw [← Polynomial.coeff_map, map_chartPoly]

open Stacks.ProjectiveSpaceChartRatio in
theorem map_irrelevant_chartHom {d : ℕ} (ε : Fin d → Fin 2) {W : (linePower k d).left.Opens}
    (h : W ≤ powChart ε) :
    (HomogeneousIdeal.irrelevant (polyGrading k d)).toIdeal.map (chartHom ε h) = ⊤ :=
  map_irrelevant_eval₂Hom_eq_top _ _ (span_coeff_chartPoly ε h)

/-- The morphism `∏ᵢ D₊(X_{εᵢ}) ⟶ ℙ^d` of the product chart `ε`. -/
noncomputable def chartMorphism {d : ℕ} (ε : Fin d → Fin 2) :
    (powChart (k := k) ε).toScheme ⟶ Proj (polyGrading k d) :=
  Proj.fromOfGlobalSections (polyGrading k d) (chartHom ε le_rfl) (map_irrelevant_chartHom ε le_rfl)

theorem homOfLE_comp_chartMorphism {d : ℕ} (ε : Fin d → Fin 2) {W : (linePower k d).left.Opens}
    (h : W ≤ powChart ε) :
    (linePower k d).left.homOfLE h ≫ chartMorphism ε =
      Proj.fromOfGlobalSections (polyGrading k d) (chartHom ε h) (map_irrelevant_chartHom ε h) :=
  (Proj.comp_fromOfGlobalSections _ _ _ _
    (Proj.map_irrelevant_comp_appTop_eq_top _ _ _ (map_irrelevant_chartHom ε le_rfl))).trans
    (Proj.fromOfGlobalSections_congr (appTop_homOfLE_comp_chartHom ε h le_rfl) _ _)

open Stacks.ProjectiveSpaceChartRatio in
/-- **The chart morphisms agree on overlaps.** -/
theorem homOfLE_comp_chartMorphism_eq {d : ℕ} (ε ε' : Fin d → Fin 2)
    {W : (linePower k d).left.Opens} (h : W ≤ powChart ε) (h' : W ≤ powChart ε') :
    (linePower k d).left.homOfLE h ≫ chartMorphism ε =
      (linePower k d).left.homOfLE h' ≫ chartMorphism ε' := by
  rw [homOfLE_comp_chartMorphism, homOfLE_comp_chartMorphism]
  obtain ⟨u, hu⟩ := exists_unit_chartPoly_eq ε ε' h h'
  refine (Proj.fromOfGlobalSections_congr_unit _ _ _ u (fun n a ha => ?_) _ _).symm
  have hr : (fun j : Fin (d + 1) => (chartPoly ε h).coeff j) =
      fun j : Fin (d + 1) => (u : Γ(W.toScheme, ⊤)) * (chartPoly ε' h').coeff j := by
    funext j; rw [hu, Polynomial.coeff_C_mul]
  rw [chartHom, chartHom, hr]
  exact ((MvPolynomial.mem_homogeneousSubmodule n a).1 ha).eval₂Hom_const_mul _ _ _

/-- The cover of `(ℙ¹)^d` by its `2^d` product charts. -/
noncomputable def powChartCover (d : ℕ) : (linePower k d).left.OpenCover :=
  (linePower k d).left.openCoverOfIsOpenCover (fun ε : Fin d → Fin 2 => powChart ε) iSup_powChart

/-- **The symmetric-product morphism `(ℙ¹)^d ⟶ ℙ^d`**, in the polynomial model of `ℙ^d`: a point
`((a₁ : b₁), …, (a_d : b_d))` goes to the coefficients of `∏ᵢ (bᵢ X - aᵢ Y)`. -/
noncomputable def symmetricProductPoly (d : ℕ) : (linePower k d).left ⟶ Proj (polyGrading k d) :=
  (powChartCover d).glueMorphisms (fun ε => chartMorphism ε) fun ε ε' => by
    change pullback.fst (powChart (k := k) ε).ι (powChart ε').ι ≫ _ =
      pullback.snd (powChart (k := k) ε).ι (powChart ε').ι ≫ _
    rw [← cancel_epi (isPullback_opens_inf (powChart (k := k) ε) (powChart ε')).isoPullback.hom,
      ← Category.assoc, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
    exact homOfLE_comp_chartMorphism_eq ε ε' inf_le_left inf_le_right

@[reassoc (attr := simp)]
theorem powChart_ι_symmetricProductPoly {d : ℕ} (ε : Fin d → Fin 2) :
    (powChart (k := k) ε).ι ≫ symmetricProductPoly d = chartMorphism ε :=
  (powChartCover d).ι_glueMorphisms _ _ ε

open Stacks.ProjectiveSpaceChartRatio in
/-- The symmetric-product morphism is a morphism over `Spec k`. -/
@[reassoc (attr := simp)]
theorem symmetricProductPoly_comp_projToSpecCoeff (d : ℕ) :
    symmetricProductPoly (k := k) d ≫ projToSpecCoeff k d = (linePower k d).hom := by
  refine (powChartCover d).hom_ext _ _ fun ε => ?_
  obtain ε : Fin d → Fin 2 := ε
  change (powChart (k := k) ε).ι ≫ _ = (powChart (k := k) ε).ι ≫ _
  rw [powChart_ι_symmetricProductPoly_assoc, chartMorphism]
  exact (fromOfGlobalSections_comp_projToSpecCoeff _ _ (span_coeff_chartPoly ε le_rfl)).trans
    (toSpecΓ_SpecMap_baseRingHom _)

/-! ### Properness -/

section Proper

variable {S : Scheme.{u}}

@[reassoc (attr := simp)]
theorem fiberPowerπ_comp_hom (X : Over S) (d : ℕ) (i : Fin d) :
    fiberPowerπ X d i ≫ X.hom = (fiberPower X d).hom := by
  induction d with
  | zero => exact i.elim0
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact pullback.condition
    · change (pullback.snd X.hom (fiberPower X d).hom ≫ fiberPowerπ X d j) ≫ X.hom =
        pullback.snd X.hom (fiberPower X d).hom ≫ (fiberPower X d).hom
      rw [Category.assoc, ih]

theorem isProper_fiberPower_hom (X : Over S) [IsProper X.hom] (d : ℕ) :
    IsProper (fiberPower X d).hom := by
  induction d with
  | zero => change IsProper (𝟙 S); infer_instance
  | succ d ih =>
    change IsProper (pullback.snd X.hom (fiberPower X d).hom ≫ (fiberPower X d).hom)
    infer_instance

end Proper

instance isProper_linePower_hom (d : ℕ) : IsProper (linePower k d).hom := by
  have : IsProper (lineOver k).hom :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  exact isProper_fiberPower_hom _ d

/-- **The symmetric-product morphism is proper.** -/
instance isProper_symmetricProductPoly (d : ℕ) : IsProper (symmetricProductPoly (k := k) d) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k d
  have : IsProper (symmetricProductPoly (k := k) d ≫ projToSpecCoeff k d) := by
    rw [symmetricProductPoly_comp_projToSpecCoeff]; infer_instance
  exact IsProper.of_comp _ (projToSpecCoeff k d)

/-! ### The preimages of the hyperplane charts -/

variable (k) in
/-- The linear form `λ X₁ - X₀` on `ℙ¹`, vanishing exactly at the point `(λ : 1)`. -/
noncomputable def pointForm (l : k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.C l * MvPolynomial.X 1 - MvPolynomial.X 0

theorem pointForm_mem (l : k) : pointForm k l ∈ polyGrading k 1 1 := by
  refine Submodule.sub_mem _ ?_ (X_mem_one k 1 0)
  simpa using (MvPolynomial.isHomogeneous_C_mul_X l (1 : Fin 2))

variable (k) in
/-- The constant `λ` in the degree-zero localization at `X_a`. -/
noncomputable def lineConst (a : Fin 2) (l : k) : HomogeneousLocalization.Away (polyGrading k 1)
    (MvPolynomial.X a) :=
  HomogeneousLocalization.fromZeroRingHom (polyGrading k 1) _
    ((GradedRing.projZeroRingHom' (polyGrading k 1)) (algebraMap k _ l))

theorem val_lineConst (a : Fin 2) (l : k) :
    (lineConst k a l).val = Localization.mk (MvPolynomial.C l) 1 := by
  have hC : (MvPolynomial.C l : MvPolynomial (Fin 2) k) ∈ polyGrading k 1 0 :=
    MvPolynomial.isHomogeneous_C _ l
  have h0 : ((GradedRing.projZeroRingHom' (polyGrading k 1)) (algebraMap k _ l) :
      MvPolynomial (Fin 2) k) = MvPolynomial.C l := by
    rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
      MvPolynomial.algebraMap_eq, DirectSum.decompose_of_mem_same _ hC]
  rw [lineConst, HomogeneousLocalization.fromZeroRingHom]
  erw [HomogeneousLocalization.val_mk]
  rw [← h0]
  rfl

theorem lineConst_mul_lineCoord_zero (l : k) :
    lineConst k 0 l * lineCoord k 0 - 1 =
      HomogeneousLocalization.Away.mk (polyGrading k 1) (X_mem_one k 1 0) 1 (pointForm k l)
        (by simpa using pointForm_mem l) := by
  rw [sub_eq_iff_eq_add]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_one, val_lineConst, lineCoord,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul, pointForm]
  rw [← Localization.mk_one, Localization.add_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem lineConst_sub_lineCoord_one (l : k) :
    lineConst k 1 l - lineCoord k 1 =
      HomogeneousLocalization.Away.mk (polyGrading k 1) (X_mem_one k 1 1) 1 (pointForm k l)
        (by simpa using pointForm_mem l) := by
  rw [sub_eq_iff_eq_add]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, val_lineConst, lineCoord,
    HomogeneousLocalization.Away.val_mk, pointForm]
  rw [Localization.add_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

open Stacks.ProjectiveSpaceChartRatio in
theorem baseRingHom_toSpecΓ_SpecMap {X : Scheme.{u}} (U : X.Opens)
    (ψ : CommRingCat.of k ⟶ Γ(X, U)) :
    baseRingHom (U.toSpecΓ ≫ Spec.map ψ) = (ψ ≫ U.topIso.inv).hom := by
  simp only [baseRingHom, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
  rw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]

open Stacks.ProjectiveSpaceChartRatio in
/-- The constants on the chart `D₊(X_a)` of `ℙ¹` are the degree-zero constants. -/
theorem baseRingHom_lineChart (a : Fin 2) (l : k) :
    baseRingHom ((lineChart k a).ι ≫ projToSpecCoeff k 1) l =
      (lineChart k a).topIso.inv.hom
        ((Proj.awayToSection (polyGrading k 1) (MvPolynomial.X a)).hom (lineConst k a l)) := by
  have h := Proj.awayι_toSpecZero (polyGrading k 1) (MvPolynomial.X a) (X_mem_one k 1 a)
    Nat.one_pos
  rw [← Proj.basicOpenIsoSpec_inv_ι, Category.assoc, Iso.inv_comp_eq,
    Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec] at h
  have e : (lineChart k a).ι ≫ projToSpecCoeff k 1 = (lineChart k a).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' (polyGrading k 1)).comp
            (algebraMap k _)) ≫ CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
          (polyGrading k 1) _) ≫ Proj.awayToSection (polyGrading k 1) (MvPolynomial.X a)) := by
    rw [projToSpecCoeff, reassoc_of% h]
    simp only [Category.assoc, Spec.map_comp]
  rw [e, baseRingHom_toSpecΓ_SpecMap]
  rfl

/-- The fraction `(λ X₁ - X₀) / X_a` on the chart `D₊(X_a)` of `ℙ¹`. -/
noncomputable def pointFraction (a : Fin 2) (l : k) :
    HomogeneousLocalization.Away (polyGrading k 1) (MvPolynomial.X a) :=
  HomogeneousLocalization.Away.mk (polyGrading k 1) (X_mem_one k 1 a) 1 (pointForm k l)
    (by simpa using pointForm_mem l)

theorem lineConst_linearFactor (a : Fin 2) (l : k) :
    (linearFactor a (lineCoord k a)).eval (lineConst k a l) = pointFraction a l := by
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [linearFactor, ite_eq_left_iff.mpr (fun h => absurd rfl h), Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one, mul_comm]
    exact lineConst_mul_lineCoord_zero l
  · rw [linearFactor, ite_eq_right_iff.mpr (fun h => absurd h (by decide)), Polynomial.eval_sub,
      Polynomial.eval_C,
      Polynomial.eval_X]
    exact lineConst_sub_lineCoord_one l

/-- The constant `λ` on an open of `(ℙ¹)^d`. -/
noncomputable def constOn {d : ℕ} (W : (linePower k d).left.Opens) : k →+* Γ(W.toScheme, ⊤) :=
  Stacks.ProjectiveSpaceChartRatio.baseRingHom (W.ι ≫ (linePower k d).hom)

theorem constOn_eq {d : ℕ} {W : (linePower k d).left.Opens} (i : Fin d) (a : Fin 2)
    (h : W ≤ linePowerπ i ⁻¹ᵁ lineChart k a) (l : k) :
    constOn W l = ((linePowerπ i).resLE (lineChart k a) W h).appTop.hom
      ((lineChart k a).topIso.inv.hom
        ((Proj.awayToSection (polyGrading k 1) (MvPolynomial.X a)).hom (lineConst k a l))) := by
  rw [← baseRingHom_lineChart, ← RingHom.comp_apply, appTop_comp_baseRingHom,
    Scheme.Hom.resLE_comp_ι_assoc, constOn]
  congr 2
  rw [← fiberPowerπ_comp_hom (lineOver k) d i]
  rfl

/-- The value at `λ` of the `i`-th linear factor, as a pulled-back fraction. -/
theorem eval_constOn_linearFactor {d : ℕ} {W : (linePower k d).left.Opens} (i : Fin d)
    (a : Fin 2) (h : W ≤ linePowerπ i ⁻¹ᵁ lineChart k a) (l : k) :
    (linearFactor a (coordOn i a h)).eval (constOn W l) =
      ((linePowerπ i).resLE (lineChart k a) W h).appTop.hom
        ((lineChart k a).topIso.inv.hom
          ((Proj.awayToSection (polyGrading k 1) (MvPolynomial.X a)).hom (pointFraction a l))) := by
  rw [← lineConst_linearFactor, constOn_eq i a h, coordOn, lineChartCoord]
  let φ := ((linePowerπ i).resLE (lineChart k a) W h).appTop.hom.comp
    ((lineChart k a).topIso.inv.hom.comp
      (Proj.awayToSection (polyGrading k 1) (MvPolynomial.X a)).hom)
  change (linearFactor a (φ (lineCoord k a))).eval (φ (lineConst k a l)) =
    φ ((linearFactor a (lineCoord k a)).eval (lineConst k a l))
  rw [← linearFactor_map, Polynomial.eval_map, Polynomial.eval₂_hom]

/-- **The nonvanishing locus of the `i`-th linear factor at `λ`** is the preimage of
`D₊(λ X₁ - X₀)` under the `i`-th projection. -/
theorem basicOpen_eval_linearFactor {d : ℕ} {W : (linePower k d).left.Opens} (i : Fin d)
    (a : Fin 2) (h : W ≤ linePowerπ i ⁻¹ᵁ lineChart k a) (l : k) :
    W.toScheme.basicOpen ((linearFactor a (coordOn i a h)).eval (constOn W l)) =
      W.ι ⁻¹ᵁ (linePowerπ i ⁻¹ᵁ Proj.basicOpen (polyGrading k 1) (pointForm k l)) := by
  rw [eval_constOn_linearFactor, ← Scheme.preimage_basicOpen_top]
  have hV : (lineChart k a).toScheme.basicOpen ((lineChart k a).topIso.inv.hom
      ((Proj.awayToSection (polyGrading k 1) (MvPolynomial.X a)).hom (pointFraction a l))) =
      (lineChart k a).ι ⁻¹ᵁ Proj.basicOpen (polyGrading k 1) (pointForm k l) := by
    rw [← Scheme.Hom.preimage_image_eq (lineChart k a).ι (Scheme.basicOpen _ _),
      Scheme.Opens.ι_image_basicOpen_topIso_inv, pointFraction,
      Stacks.ProjChartBasicOpen.basicOpen_awayToSection_mk _ (X_mem_one k 1 a) Nat.one_pos]
    ext x
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      TopologicalSpace.Opens.mem_inf, Proj.mem_basicOpen, and_iff_right_iff_imp]
    exact fun _ => x.2
  rw [hV, ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_preimage]

variable (k) in
/-- The linear form `F ↦ F(λ, 1) = ∑ⱼ λʲ cⱼ` on `ℙ^d`, evaluating a binary form at `(λ : 1)`. -/
noncomputable def evalForm (d : ℕ) (l : k) : MvPolynomial (Fin (d + 1)) k :=
  ∑ j : Fin (d + 1), MvPolynomial.C (l ^ (j : ℕ)) * MvPolynomial.X j

theorem evalForm_mem (d : ℕ) (l : k) : evalForm k d l ∈ polyGrading k d 1 :=
  Submodule.sum_mem _ fun j _ => by
    simpa using (MvPolynomial.isHomogeneous_C_mul_X (l ^ (j : ℕ)) j)

theorem chartHom_evalForm {d : ℕ} (ε : Fin d → Fin 2) {W : (linePower k d).left.Opens}
    (h : W ≤ powChart ε) (l : k) :
    chartHom ε h (evalForm k d l) =
      ∏ i, (linearFactor (ε i) (coordOn i (ε i) (h.trans (powChart_le ε i)))).eval
        (constOn W l) := by
  rw [← Polynomial.eval_prod, evalForm, map_sum,
    Polynomial.eval_eq_sum_range' (n := d + 1)
      ((natDegree_prod_linearFactor_le _ _).trans_lt (Nat.lt_succ_self d)),
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chartHom, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', map_pow, mul_comm]
  rfl

theorem basicOpen_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (f : ι → Γ(X, ⊤)) :
    X.basicOpen (∏ i ∈ s, f i) = s.inf fun i => X.basicOpen (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, Finset.inf_insert]

theorem preimage_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} [Finite ι] (U : ι → Y.Opens) :
    f ⁻¹ᵁ (⨅ i, U i) = ⨅ i, f ⁻¹ᵁ U i := by
  ext x
  simp [TopologicalSpace.Opens.coe_iInf]

/-- On a product chart, the nonvanishing locus of the pulled-back form `evalForm λ` is the
product of the complements of `(λ : 1)`. -/
theorem basicOpen_chartHom_evalForm {d : ℕ} (ε : Fin d → Fin 2)
    {W : (linePower k d).left.Opens} (h : W ≤ powChart ε) (l : k) :
    W.toScheme.basicOpen (chartHom ε h (evalForm k d l)) =
      W.ι ⁻¹ᵁ ⨅ i, linePowerπ i ⁻¹ᵁ Proj.basicOpen (polyGrading k 1) (pointForm k l) := by
  rw [chartHom_evalForm, basicOpen_prod, preimage_iInf, Finset.inf_univ_eq_iInf]
  exact iInf_congr fun i => basicOpen_eval_linearFactor i (ε i) _ l

/-- **The preimage of the hyperplane chart `D₊(evalForm λ)` under the symmetric-product morphism**
is the product `∏ᵢ (ℙ¹ ∖ {(λ : 1)})`. -/
theorem symmetricProductPoly_preimage_basicOpen (d : ℕ) (l : k) :
    symmetricProductPoly (k := k) d ⁻¹ᵁ Proj.basicOpen (polyGrading k d) (evalForm k d l) =
      ⨅ i, linePowerπ i ⁻¹ᵁ Proj.basicOpen (polyGrading k 1) (pointForm k l) := by
  have key : ∀ ε : Fin d → Fin 2, (powChart (k := k) ε).ι ⁻¹ᵁ
      (symmetricProductPoly d ⁻¹ᵁ Proj.basicOpen (polyGrading k d) (evalForm k d l)) =
      (powChart (k := k) ε).ι ⁻¹ᵁ
        ⨅ i, linePowerπ i ⁻¹ᵁ Proj.basicOpen (polyGrading k 1) (pointForm k l) := by
    intro ε
    rw [← Scheme.Hom.comp_preimage, powChart_ι_symmetricProductPoly, chartMorphism,
      Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos (evalForm_mem d l),
      basicOpen_chartHom_evalForm]
  ext x
  obtain ⟨ε, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_powChart (k := k) (d := d)).ge (Set.mem_univ x))
  have := congrArg (fun U => (⟨x, hx⟩ : powChart (k := k) ε) ∈ U) (key ε)
  exact Iff.of_eq this

/-! ### Finiteness -/

/-- In a fibre product over an affine scheme, the product of two affine opens is affine. -/
theorem isAffineOpen_pullback_inf {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let p : pullback (U.ι ≫ f) (V.ι ≫ g) ⟶ pullback f g :=
    pullback.map _ _ _ _ U.ι V.ι (𝟙 S) (by simp) (by simp)
  convert isAffineOpen_opensRange p
  ext1
  simp [p, Scheme.Pullback.range_map]

theorem iInf_fiberPowerπ_succ {S : Scheme.{u}} (X : Over S) (d : ℕ) (U : X.left.Opens) :
    ⨅ i, fiberPowerπ X (d + 1) i ⁻¹ᵁ U = pullback.fst X.hom (fiberPower X d).hom ⁻¹ᵁ U ⊓
      pullback.snd X.hom (fiberPower X d).hom ⁻¹ᵁ ⨅ i, fiberPowerπ X d i ⁻¹ᵁ U := by
  rw [preimage_iInf]
  apply le_antisymm
  · refine le_inf (iInf_le (fun i => fiberPowerπ X (d + 1) i ⁻¹ᵁ U) 0) (le_iInf fun j => ?_)
    refine (iInf_le (fun i => fiberPowerπ X (d + 1) i ⁻¹ᵁ U) j.succ).trans_eq ?_
    rfl
  · refine le_iInf fun i => ?_
    refine Fin.cases inf_le_left (fun j => ?_) i
    refine inf_le_right.trans ((iInf_le _ j).trans_eq ?_)
    rfl

/-- A product `∏ᵢ U` of an affine open of `X` is affine in the fibre power over an affine base. -/
theorem isAffineOpen_iInf_fiberPowerπ {S : Scheme.{u}} [IsAffine S] (X : Over S) {U : X.left.Opens}
    (hU : IsAffineOpen U) (d : ℕ) : IsAffineOpen (⨅ i, fiberPowerπ X d i ⁻¹ᵁ U) := by
  induction d with
  | zero =>
    have : IsAffine (fiberPower X 0).left := ‹IsAffine S›
    convert isAffineOpen_top (fiberPower X 0).left
    exact iInf_of_empty _
  | succ d ih =>
    rw [iInf_fiberPowerπ_succ]
    exact isAffineOpen_pullback_inf _ _ hU ih

/-- **The hyperplane charts at `d + 1` distinct points cover `ℙ^d`**: the forms `evalForm λᵣ` span
the linear forms, by the invertibility of the Vandermonde matrix. -/
theorem iSup_basicOpen_evalForm {d : ℕ} (l : Fin (d + 1) → k) (hl : Function.Injective l) :
    ⨆ r, Proj.basicOpen (polyGrading k d) (evalForm k d (l r)) = ⊤ := by
  refine Proj.iSup_basicOpen_eq_top _ _ ((irrelevant_le_span_X k d).trans ?_)
  rw [Ideal.span_le]
  rintro - ⟨j, rfl⟩
  set V := Matrix.vandermonde l
  have hV : IsUnit V.det := (Matrix.det_vandermonde_ne_zero_iff.mpr hl).isUnit
  have hX : MvPolynomial.X j = ∑ r, MvPolynomial.C (V⁻¹ j r) * evalForm k d (l r) := by
    simp only [evalForm, Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    have : ∀ m : Fin (d + 1), ∑ r, V⁻¹ j r * l r ^ (m : ℕ) = (V⁻¹ * V) j m := by
      intro m; rw [Matrix.mul_apply]; rfl
    simp_rw [← Finset.sum_mul, ← map_sum, this, Matrix.nonsing_inv_mul V hV, Matrix.one_apply]
    simp
  rw [SetLike.mem_coe, hX]
  exact Ideal.sum_mem _ fun r _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r, rfl⟩)

/-- **The symmetric-product morphism is affine**, for a field with at least `d + 1` elements. -/
theorem isAffineHom_symmetricProductPoly {d : ℕ} (l : Fin (d + 1) → k)
    (hl : Function.Injective l) : IsAffineHom (symmetricProductPoly (k := k) d) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
  obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_evalForm l hl).ge (Set.mem_univ y))
  refine ⟨_, hr, Proj.isAffineOpen_basicOpen _ _ (evalForm_mem d (l r)) Nat.one_pos, ?_⟩
  rw [symmetricProductPoly_preimage_basicOpen]
  exact isAffineOpen_iInf_fiberPowerπ (lineOver k)
    (Proj.isAffineOpen_basicOpen _ _ (pointForm_mem (l r)) Nat.one_pos) d

/-- **The symmetric-product morphism is finite**, for a field with at least `d + 1` elements. -/
theorem isFinite_symmetricProductPoly {d : ℕ} (l : Fin (d + 1) → k)
    (hl : Function.Injective l) : IsFinite (symmetricProductPoly (k := k) d) := by
  have := isAffineHom_symmetricProductPoly l hl
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, this⟩,
    inferInstance⟩

/-! ### In the base-change model `ℙ^d_k = projectiveSpaceOver d (Spec k)` -/

variable (k) in
/-- **The symmetric-product morphism `(ℙ¹_k)^d ⟶ ℙ^d_k`** into the base-change model
`AlgebraicGeometry.projectiveSpaceOver d (Spec k)` of projective space: a point
`((a₁ : b₁), …, (a_d : b_d))` goes to the coefficients of the binary form `∏ᵢ (bᵢ X - aᵢ Y)`. -/
noncomputable def symmetricProduct (d : ℕ) :
    (linePower k d).left ⟶ projectiveSpaceOver d (Spec (CommRingCat.of k)) :=
  symmetricProductPoly d ≫
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k d).iso.inv

/-- The symmetric-product morphism lies over `Spec k`. -/
@[reassoc (attr := simp)]
theorem symmetricProduct_comp_fst (d : ℕ) :
    symmetricProduct k d ≫ pullback.fst _ _ = (linePower k d).hom := by
  rw [symmetricProduct, Category.assoc,
    ← Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff k d,
    Iso.inv_hom_id_assoc, symmetricProductPoly_comp_projToSpecCoeff]

instance isProper_symmetricProduct (d : ℕ) : IsProper (symmetricProduct k d) := by
  rw [symmetricProduct]; infer_instance

/-- **The symmetric-product morphism `(ℙ¹_k)^d ⟶ ℙ^d_k` is finite**, over a field with at least
`d + 1` elements. -/
theorem isFinite_symmetricProduct_of_injective {d : ℕ} (l : Fin (d + 1) → k)
    (hl : Function.Injective l) : IsFinite (symmetricProduct k d) := by
  have := isFinite_symmetricProductPoly l hl
  rw [symmetricProduct]; infer_instance

/-- **The symmetric-product morphism `(ℙ¹_k)^d ⟶ ℙ^d_k` is finite** over an infinite field. -/
instance isFinite_symmetricProduct [Infinite k] (d : ℕ) : IsFinite (symmetricProduct k d) :=
  isFinite_symmetricProduct_of_injective _
    ((Infinite.natEmbedding k).injective.comp Fin.val_injective)

/-! ### Surjectivity -/

section Surjective

open Stacks.ProjectiveSpaceChartRatio Stacks.ProjGlobalSectionsAppTop

variable {Y : Scheme.{u}} (κ : k →+* Γ(Y, ⊤))

theorem span_range_pair_one (a : Γ(Y, ⊤)) : Ideal.span (Set.range ![a, 1]) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨1, rfl⟩) isUnit_one

/-- The `Y`-point `(a : 1)` of `ℙ¹`. -/
noncomputable def linePoint (a : Γ(Y, ⊤)) : Y ⟶ line k :=
  Proj.fromOfGlobalSections (polyGrading k 1) (MvPolynomial.eval₂Hom κ ![a, 1])
    (map_irrelevant_eval₂Hom_eq_top κ _ (span_range_pair_one a))

theorem linePoint_comp (a : Γ(Y, ⊤)) :
    linePoint κ a ≫ projToSpecCoeff k 1 = Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ) :=
  fromOfGlobalSections_comp_projToSpecCoeff κ _ (span_range_pair_one a)

theorem linePoint_preimage (a : Γ(Y, ⊤)) : linePoint κ a ⁻¹ᵁ lineChart k 1 = ⊤ := by
  rw [linePoint, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos (X_mem_one k 1 1),
    MvPolynomial.eval₂Hom_X']
  exact Scheme.basicOpen_one Y

/-- The `Y`-point `((a₁ : 1), …, (a_m : 1))` of `(ℙ¹)^m`. -/
noncomputable def powerPoint : (m : ℕ) → (Fin m → Γ(Y, ⊤)) →
    {f : Y ⟶ (linePower k m).left //
      f ≫ (linePower k m).hom = Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ)}
  | 0, _ => ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom κ), Category.comp_id _⟩
  | m + 1, a => ⟨pullback.lift (linePoint κ (a 0)) (powerPoint m fun i => a i.succ).1
      ((linePoint_comp κ _).trans (powerPoint m fun i => a i.succ).2.symm), by
        change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
        rw [pullback.lift_snd_assoc, (powerPoint m fun i => a i.succ).2]⟩

theorem powerPoint_π {m : ℕ} (a : Fin m → Γ(Y, ⊤)) (i : Fin m) :
    (powerPoint κ m a).1 ≫ linePowerπ i = linePoint κ (a i) := by
  induction m with
  | zero => exact i.elim0
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact pullback.lift_fst _ _ _
    · change pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ linePowerπ j = _
      rw [pullback.lift_snd_assoc, ih]

theorem powerPoint_preimage_powChart {m : ℕ} (a : Fin m → Γ(Y, ⊤)) :
    (powerPoint κ m a).1 ⁻¹ᵁ powChart (k := k) (fun _ => 1) = ⊤ := by
  rw [powChart, preimage_iInf]
  simp_rw [← Scheme.Hom.comp_preimage, powerPoint_π, linePoint_preimage]
  exact iInf_top

theorem resTop_top_apply (x : Γ(Y, ⊤)) : resTop (⊤ : Y.Opens) x = x := by
  simp [resTop]

/-- Pulling the chart coordinate back along `powerPoint`. -/
theorem powerPoint_appTop_coordOn {m : ℕ} (a : Fin m → Γ(Y, ⊤)) (i : Fin m)
    (h : powChart (k := k) (fun _ => 1) ≤ linePowerπ i ⁻¹ᵁ lineChart k 1) :
    ((powerPoint κ m a).1.resLE (powChart (fun _ => 1)) ⊤
        (powerPoint_preimage_powChart κ a).ge).appTop.hom (coordOn i 1 h) =
      (⊤ : Y.Opens).topIso.inv.hom (a i) := by
  rw [coordOn, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.Hom.resLE_comp_resLE,
    lineChartCoord, ← CommRingCat.comp_apply, topIso_inv_resLE_appTop, CommRingCat.comp_apply]
  congr 1
  have hV : (⊤ : Y.Opens) ≤
      Y.basicOpen ((MvPolynomial.eval₂Hom κ ![a i, 1]) (MvPolynomial.X 1)) := by
    rw [MvPolynomial.eval₂Hom_X']; exact (Scheme.basicOpen_one Y).ge
  rw [Stacks.AlgebraicGeometry.ProjTwistPinnedChart.appLE_awayToSection_fromOfGlobalSections
    (polyGrading k 1) _ _ Nat.one_pos (X_mem_one k 1 1) ((powerPoint_π κ a i).trans rfl) _ hV,
    lineCoord, projAwayHom_apply_mk_of_mul_eq_one (v := 1) _ _ _ _ _ _
      (by rw [mul_one, MvPolynomial.eval₂Hom_X']; exact map_one _),
    one_pow, mul_one, resTop_resTop, resTop_top_apply]
  simp

/-- `powerPoint` as a morphism into the chart `∏ᵢ D₊(X₁)`. -/
noncomputable def powerPointChart {m : ℕ} (a : Fin m → Γ(Y, ⊤)) :
    (⊤ : Y.Opens).toScheme ⟶ (powChart (k := k) (fun _ : Fin m => 1)).toScheme :=
  (powerPoint κ m a).1.resLE _ ⊤ (powerPoint_preimage_powChart κ a).ge

theorem powerPointChart_appTop_comp_chartHom {m : ℕ} (a : Fin m → Γ(Y, ⊤)) :
    (powerPointChart κ a).appTop.hom.comp (chartHom (k := k) (fun _ => 1) le_rfl) =
      (⊤ : Y.Opens).topIso.inv.hom.comp (MvPolynomial.eval₂Hom κ
        fun j : Fin (m + 1) => (∏ i, linearFactor 1 (a i)).coeff j) := by
  rw [chartHom, MvPolynomial.comp_eval₂Hom, MvPolynomial.comp_eval₂Hom, appTop_comp_baseRingHom,
    powerPointChart, Scheme.Hom.resLE_comp_ι_assoc, (powerPoint κ m a).2, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_top, baseRingHom_toSpecΓ_SpecMap]
  congr 1
  funext j
  rw [← Polynomial.coeff_map, chartPoly, Polynomial.map_prod, ← Polynomial.coeff_map,
    Polynomial.map_prod]
  refine congrArg (Polynomial.coeff · j) (Finset.prod_congr rfl fun i _ => ?_)
  rw [linearFactor_map, linearFactor_map, ← powerPoint_appTop_coordOn κ a i]

/-- **Surjectivity from one test point.** If `Y` is nonempty and the binary form
`∏ᵢ (X - aᵢ)` over `Γ(Y, 𝒪)` has coefficients satisfying no nonzero homogeneous relation, then
the symmetric-product morphism is surjective. -/
theorem surjective_symmetricProductPoly_of_test {d : ℕ} [IsAffine Y] [Nonempty Y]
    (a : Fin d → Γ(Y, ⊤))
    (hE : ∀ (n : ℕ) (p : MvPolynomial (Fin (d + 1)) k), p ∈ polyGrading k d n →
      MvPolynomial.eval₂Hom κ (fun j : Fin (d + 1) => (∏ i, linearFactor 1 (a i)).coeff j) p = 0 →
        p = 0) :
    Function.Surjective (symmetricProductPoly (k := k) d) := by
  classical
  let E := MvPolynomial.eval₂Hom κ fun j : Fin (d + 1) => (∏ i, linearFactor 1 (a i)).coeff j
  let G := (⊤ : Y.Opens).topIso.inv.hom.comp E
  have hGeq : (powerPointChart κ a).appTop.hom.comp (chartHom (k := k) (fun _ => 1) le_rfl) = G :=
    powerPointChart_appTop_comp_chartHom κ a
  have hGirr : (HomogeneousIdeal.irrelevant (polyGrading k d)).toIdeal.map G = ⊤ := by
    rw [← hGeq]
    exact Proj.map_irrelevant_comp_appTop_eq_top _ _ _ (map_irrelevant_chartHom _ le_rfl)
  set t : MvPolynomial (Fin (d + 1)) k := MvPolynomial.X (Fin.last d) with ht_def
  have ht : t ∈ polyGrading k d 1 := X_mem_one k d _
  have hmonic : (∏ i, linearFactor (1 : Fin 2) (a i)).Monic := by
    refine Polynomial.monic_prod_of_monic _ _ fun i _ => ?_
    simpa [linearFactor] using Polynomial.monic_X_sub_C (a i)
  have hcoeff : (∏ i, linearFactor (1 : Fin 2) (a i)).coeff d = 1 := by
    rcases subsingleton_or_nontrivial Γ(Y, ⊤) with hs | hs
    · exact Subsingleton.elim _ _
    · have hdeg : (∏ i, linearFactor (1 : Fin 2) (a i)).natDegree = d := by
        rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => by
          simpa [linearFactor] using Polynomial.monic_X_sub_C (a i)]
        simp [linearFactor]
      have h1 := hmonic.coeff_natDegree
      rwa [hdeg] at h1
  have hG1 : G t = 1 := by
    simp only [G, E, RingHom.comp_apply, ht_def, MvPolynomial.eval₂Hom_X', Fin.val_last]
    rw [hcoeff, map_one]
  let Φ := Proj.fromOfGlobalSections (polyGrading k d) G hGirr
  have hΦ : Φ = (⊤ : Y.Opens).ι ≫ (powerPoint κ d a).1 ≫ symmetricProductPoly d := by
    have h1 := Proj.comp_fromOfGlobalSections (polyGrading k d) (powerPointChart κ a)
      (chartHom (k := k) (fun _ => 1) le_rfl) (map_irrelevant_chartHom _ le_rfl)
      (Proj.map_irrelevant_comp_appTop_eq_top _ _ _ (map_irrelevant_chartHom _ le_rfl))
    rw [← Scheme.Hom.resLE_comp_ι_assoc (powerPoint κ d a).1
      (powerPoint_preimage_powChart κ a).ge, powChart_ι_symmetricProductPoly]
    exact (Proj.fromOfGlobalSections_congr hGeq.symm _ _).trans h1.symm
  -- the chart `D₊(c_d)` of `ℙ^d` lies in the image
  let Yt := (⊤ : Y.Opens).toScheme
  have hB : Yt.basicOpen (G t) = ⊤ := by rw [hG1]; exact Scheme.basicOpen_one _
  have hYaff : IsAffine Yt := isAffineOpen_top Y
  have hBaff : IsAffineOpen (Yt.basicOpen (G t)) := (isAffineOpen_top Yt).basicOpen _
  have hsq := Stacks.ProjGlobalSectionsAppTop.ι_comp_fromOfGlobalSections (polyGrading k d) G
    hGirr Nat.one_pos ht
  have hsq2 := toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom (polyGrading k d) G
    Nat.one_pos ht
  set φ := projAwayHom (polyGrading k d) G (t := t) with hφ
  -- `φ` is injective
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (polyGrading k d) ht z
    rw [projAwayHom_apply_mk_of_mul_eq_one (v := 1) _ _ _ _ _ _
      (by rw [mul_one, hG1]; exact map_one _), one_pow, mul_one] at hz
    have h0 := congrArg (Yt.presheaf.map (homOfLE hB.ge).op).hom hz
    rw [resTop_resTop, resTop_top_apply, map_zero] at h0
    have hEp : E p = 0 := by
      have h1 : (⊤ : Y.Opens).topIso.inv.hom (E p) = 0 := h0
      have := congrArg (⊤ : Y.Opens).topIso.hom.hom h1
      rwa [map_zero, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] at this
    have hp0 := hE _ p hp hEp
    subst hp0
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, Localization.mk_zero]
  have hdense : DenseRange (Spec.map (CommRingCat.ofHom φ)) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hφinj]; exact bot_le)
  have hsurjB : Function.Surjective (Yt.basicOpen (G t)).toSpecΓ := by
    rw [← hBaff.isoSpec_hom]; exact (hBaff.isoSpec.hom).surjective
  -- every point of `D₊(c_d)` is in the image
  have key : (Yt.basicOpen (G t)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (polyGrading k d) t ht Nat.one_pos =
      (Yt.basicOpen (G t)).ι ≫ (⊤ : Y.Opens).ι ≫ (powerPoint κ d a).1 ≫
        symmetricProductPoly d := by
    have h2 := congrArg (· ≫ (Proj.basicOpenIsoSpec (polyGrading k d) t ht Nat.one_pos).inv ≫
      (Proj.basicOpen (polyGrading k d) t).ι) hsq2
    simp only [Category.assoc, Iso.hom_inv_id_assoc] at h2
    rw [← hΦ, hsq, h2, Proj.basicOpenIsoSpec_inv_ι]
    rfl
  have hcl : IsClosed (Set.range (symmetricProductPoly (k := k) d)) :=
    (symmetricProductPoly (k := k) d).isClosedMap.isClosed_range
  have hD : (Proj.basicOpen (polyGrading k d) t : Set (Proj (polyGrading k d))) ⊆
      Set.range (symmetricProductPoly (k := k) d) := by
    rw [← Proj.opensRange_awayι (polyGrading k d) t ht Nat.one_pos, Scheme.Hom.coe_opensRange]
    rintro _ ⟨y, rfl⟩
    have hy : Proj.awayι (polyGrading k d) t ht Nat.one_pos y ∈
        closure (Proj.awayι (polyGrading k d) t ht Nat.one_pos ''
          Set.range (Spec.map (CommRingCat.ofHom φ))) :=
      image_closure_subset_closure_image (Proj.awayι (polyGrading k d) t ht Nat.one_pos).continuous
        ⟨y, by rw [hdense.closure_range]; trivial, rfl⟩
    refine closure_minimal ?_ hcl hy
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨b, rfl⟩ := hsurjB x
    refine ⟨(powerPoint κ d a).1 ((⊤ : Y.Opens).ι ((Yt.basicOpen (G t)).ι b)), ?_⟩
    have h := congrArg (fun f => f b) key
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  -- `D₊(c_d)` is a nonempty open of the irreducible scheme `ℙ^d`
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  let y0 : Yt := ⟨y, trivial⟩
  have hy0 : y0 ∈ Φ ⁻¹ᵁ Proj.basicOpen (polyGrading k d) t := by
    rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos ht, hB]; trivial
  have hdenseD := (Proj.basicOpen (polyGrading k d) t).isOpen.dense ⟨Φ y0, hy0⟩
  intro z
  have hz : z ∈ closure (Proj.basicOpen (polyGrading k d) t : Set (Proj (polyGrading k d))) := by
    rw [hdenseD.closure_eq]; trivial
  exact closure_minimal hD hcl hz


/-- **The symmetric-product morphism is surjective**, over an infinite field. -/
theorem surjective_symmetricProductPoly [Infinite k] (d : ℕ) :
    Function.Surjective (symmetricProductPoly (k := k) d) := by
  classical
  let R := MvPolynomial (Fin d) k
  let ι := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let κ : k →+* Γ(Spec (CommRingCat.of R), ⊤) := ι.comp (algebraMap k R)
  let a : Fin d → Γ(Spec (CommRingCat.of R), ⊤) := fun i => ι (-MvPolynomial.X i)
  refine surjective_symmetricProductPoly_of_test κ a fun n p hp hEp => ?_
  have hEι : MvPolynomial.eval₂Hom κ (fun j : Fin (d + 1) =>
      (∏ i, linearFactor 1 (a i)).coeff j) = ι.comp (MvPolynomial.eval₂Hom MvPolynomial.C
        fun j : Fin (d + 1) =>
          (∏ i : Fin d, (Polynomial.X + Polynomial.C (MvPolynomial.X i : R))).coeff j) := by
    rw [MvPolynomial.comp_eval₂Hom]
    congr 1
    funext j
    rw [← Polynomial.coeff_map, Polynomial.map_prod]
    refine congrArg (Polynomial.coeff · j) (Finset.prod_congr rfl fun i _ => ?_)
    simp [linearFactor, a, sub_eq_add_neg]
  refine eq_zero_of_eval₂_coeff_prod_X_add_C hp ?_
  rw [hEι, RingHom.comp_apply] at hEp
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom hEp
  simpa [ι] using this

instance surjective_symmetricProductPoly_inst [Infinite k] (d : ℕ) :
    Surjective (symmetricProductPoly (k := k) d) :=
  ⟨surjective_symmetricProductPoly d⟩

/-- **The symmetric-product morphism `(ℙ¹_k)^d ⟶ ℙ^d_k` is surjective** over an infinite field. -/
instance surjective_symmetricProduct [Infinite k] (d : ℕ) : Surjective (symmetricProduct k d) := by
  rw [symmetricProduct]; infer_instance

/-- **The symmetric-product morphism `(ℙ¹_k)^d ⟶ ℙ^d_k` is finite and surjective** over an
infinite field, and it lies over `Spec k`. -/
theorem isFinite_surjective_symmetricProduct [Infinite k] (d : ℕ) :
    IsFinite (symmetricProduct k d) ∧ Surjective (symmetricProduct k d) ∧
      symmetricProduct k d ≫ pullback.fst _ _ = (linePower k d).hom :=
  ⟨inferInstance, inferInstance, symmetricProduct_comp_fst d⟩

end Surjective

end AlgebraicGeometry.SymmetricProduct

end
