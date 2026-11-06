module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharPowerSeriesCharpoly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusPoincarePairing
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusCharpolyFieldOfConstants
public import Weil.Attr

/-!
# The Frobenius over a subfield of the field of constants

Let `X` be a separated scheme of finite type over a finite field `k` whose structure morphism
`f = g ≫ (Spec k' ⟶ Spec k)` factors through a finite extension `k'` of `k` of degree `r`, and let
`F` be an ℓ-adic sheaf on `X`, `ℓ ≠ p`. The L-function of `F` over `k` is the one over `k'`
evaluated at `T ^ r`: the closed points of `X` and the Frobenius actions on the stalks there do not
depend on the base, and the degree of a closed point over `k` is `r` times its degree over `k'`.
By the determinant formula for the L-function ([Stacks, Tag 03V0]) over `k` and over `k'`,

`∏ᵢ det(1 - F_k T | Hⁱ_c)^{(-1)^{i+1}} = ∏ᵢ det(1 - F_{k'} T ^ r | Hⁱ_c)^{(-1)^{i+1}}`.

When the cohomology is pure, `Hⁱ_c` of weight `i` over `k` and over `k'`, the roots of the factor in
degree `i` on either side all have absolute value `#k ^ (-i / 2)`; distinct degrees have distinct
absolute values, so no cancellation happens between degrees, and the factors agree degree by
degree: `det(1 - F_k T | Hⁱ_c) = det(1 - F_{k'} T ^ r | Hⁱ_c)` for every `i`.

## Main results

* `Weil.LAdicSheaf.rationalLFunction_comp_specAlgebraMap`: `L(X/k, F)(T) = L(X/k', F)(T ^ r)`.
* `Weil.Polynomial.eq_of_alternating_prod_eq`: complex polynomials with constant coefficient `1`
  whose roots in each degree have one absolute value, distinct for distinct degrees, are
  determined degree by degree by their alternating product.
* `Weil.LAdicSheaf.reverse_charpoly_rationalGeometricCompactlySupportedFrobenius_eq_comp_of_pure`:
  for pure cohomology, the reverse characteristic polynomial of the Frobenius over `k` in degree
  `i` is that of the Frobenius over `k'` evaluated at `T ^ r`.

## Implementation notes

The degree-by-degree identity is proved from the L-function and the weights, not from the
decomposition `X ⊗_k k̄ = ⨆_{τ : k' → k̄} X ⊗_{k', τ} k̄` of the geometric fibre, which would give
it without the purity hypotheses: the comparison of the compactly supported cohomology of the
geometric fibre over `k` with the cohomology of its open and closed pieces, compatibly with the
geometric Frobenius, is not available. For `X` smooth and proper the purity hypotheses are
Deligne's theorem over `k` and over `k'`. The two algebraic closures `k̄` of `k` and `k̄'` of `k'`
are arbitrary; no compatibility between them is needed.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
* [Stacks Project, Tag 03UX](https://stacks.math.columbia.edu/tag/03UX)
-/

@[expose] public noncomputable section

open Polynomial Stacks.EtaleCohomology

universe u

namespace Weil

/-! ### Local factors at `T ^ d` -/

variable {Λ : Type*} [CommRing Λ]

/-- `det(1 - A T ^ d)` is `det(1 - A T)` evaluated at `T ^ d`. -/
theorem localCharSeries_eq_expand {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n Λ)
    (d : ℕ) (hd : d ≠ 0) :
    localCharSeries A d = PowerSeries.expand d hd (localCharSeries A 1) := by
  rw [localCharSeries, localCharSeries, ← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext i j
  rw [localCharMatrix, localCharMatrix, RingHom.mapMatrix_apply, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp [PowerSeries.expand_C, PowerSeries.expand_X]
  · simp [hij, PowerSeries.expand_C, PowerSeries.expand_X]

/-- `det(1 - φ T ^ d)` is `det(1 - φ T)` evaluated at `T ^ d`. -/
theorem charPowerSeries_eq_expand {M : Type*} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
    [Module.Free Λ M] (φ : M →ₗ[Λ] M) (d : ℕ) (hd : d ≠ 0) :
    charPowerSeries φ d = PowerSeries.expand d hd (charPowerSeries φ 1) := by
  classical
  let b := Module.Free.chooseBasis Λ M
  rw [charPowerSeries_eq_localCharSeries b, charPowerSeries_eq_localCharSeries b,
    localCharSeries_eq_expand _ d hd]

/-- Expanding a polynomial commutes with reading it as a power series. -/
theorem coe_expand (P : Λ[X]) (d : ℕ) (hd : d ≠ 0) :
    ((expand Λ d P : Λ[X]) : PowerSeries Λ) = PowerSeries.expand d hd (P : PowerSeries Λ) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp [PowerSeries.expand_monomial, Polynomial.coe_monomial, mul_comm]

/-- Expanding a power series with constant coefficient `1` commutes with inversion. -/
theorem expand_invOfUnit (φ : PowerSeries Λ) (hφ : PowerSeries.constantCoeff φ = 1) (d : ℕ)
    (hd : d ≠ 0) :
    PowerSeries.expand d hd (PowerSeries.invOfUnit φ 1) =
      PowerSeries.invOfUnit (PowerSeries.expand d hd φ) 1 := by
  have h1 : PowerSeries.constantCoeff (PowerSeries.expand d hd φ) = 1 := by
    rw [PowerSeries.constantCoeff_expand, hφ]
  have hu : φ * PowerSeries.invOfUnit φ 1 = 1 :=
    PowerSeries.mul_invOfUnit φ 1 (by simp [hφ])
  have hu' : PowerSeries.expand d hd φ * PowerSeries.invOfUnit (PowerSeries.expand d hd φ) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ 1 (by simp [h1])
  have h2 : PowerSeries.expand d hd φ *
      PowerSeries.expand d hd (PowerSeries.invOfUnit φ 1) = 1 := by
    rw [← map_mul, hu, map_one]
  have hunit : IsUnit (PowerSeries.expand d hd φ) := IsUnit.of_mul_eq_one _ h2
  exact hunit.mul_left_cancel (h2.trans hu'.symm)

section ResidueDegree

open AlgebraicGeometry CategoryTheory

/-- The map `k → κ(x)` of `X` over `k` through `k'` is `k → k' → κ(x)`. -/
theorem fieldToResidue_comp_specAlgebraMap {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k')) (x : X) :
    fieldToResidue (g ≫ Stacks.Frobenius.specAlgebraMap k k') x =
      CommRingCat.ofHom (algebraMap k k') ≫ fieldToResidue g x := by
  simp only [fieldToResidue, fieldToStalk, Scheme.Hom.comp_appTop, Category.assoc]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k k'))
  rw [← Category.assoc (Scheme.ΓSpecIso (.of k)).inv]
  erw [← h]
  rfl

/-- The degree of a point over `k` is `[k' : k]` times its degree over `k'`. -/
theorem residueDegree_comp_specAlgebraMap {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k')) (x : X) :
    residueDegree (g ≫ Stacks.Frobenius.specAlgebraMap k k') x =
      Module.finrank k k' * residueDegree g x := by
  let _ : Algebra k' (X.residueField x) := (fieldToResidue g x).hom.toAlgebra
  let _ : Algebra k (X.residueField x) :=
    (fieldToResidue (g ≫ Stacks.Frobenius.specAlgebraMap k k') x).hom.toAlgebra
  have : IsScalarTower k k' (X.residueField x) := IsScalarTower.of_algebraMap_eq fun c => by
    change (fieldToResidue (g ≫ Stacks.Frobenius.specAlgebraMap k k') x).hom c = _
    rw [fieldToResidue_comp_specAlgebraMap]
    rfl
  change Module.finrank k (X.residueField x) = _
  rw [← Module.finrank_mul_finrank k k' (X.residueField x)]
  rfl

end ResidueDegree

section LFunction

open AlgebraicGeometry CategoryTheory

/-- `det(1 - A T ^ (r d)) ⁻¹` is `det(1 - A T ^ d) ⁻¹` evaluated at `T ^ r`. -/
theorem localEulerFactor_mul_eq_expand {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Λ) {r d : ℕ} (hr : r ≠ 0) (hd : d ≠ 0) :
    localEulerFactor A (r * d) = PowerSeries.expand r hr (localEulerFactor A d) := by
  have h : localCharSeries A (r * d) = PowerSeries.expand r hr (localCharSeries A d) := by
    rw [localCharSeries_eq_expand A d hd, localCharSeries_eq_expand A (r * d) (by positivity),
      PowerSeries.expand_mul r hr d hd]
  rw [localEulerFactor, localEulerFactor, expand_invOfUnit _ (constantCoeff_localCharSeries A hd),
    h]

/-- **The L-function over a subfield of the field of constants.** For a family of Frobenius
matrices on `X` over `k'` and the same family read over `k ⊆ k'` with `[k' : k] = r`, the
L-function over `k` is the one over `k'` evaluated at `T ^ r`. -/
theorem FrobeniusMatrices.lFunction_comp_specAlgebraMap {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [Finite k] [Finite k'] {X : Scheme.{u}} (g : X ⟶ Spec (.of k'))
    [LocallyOfFiniteType g] [QuasiCompact g]
    (D : FrobeniusMatrices g Λ) (hr : Module.finrank k k' ≠ 0) :
    (⟨D.rank, D.matrix⟩ :
        FrobeniusMatrices (g ≫ Stacks.Frobenius.specAlgebraMap k k') Λ).lFunction =
      PowerSeries.expand _ hr D.lFunction := by
  set r := Module.finrank k k'
  set f := g ≫ Stacks.Frobenius.specAlgebraMap k k'
  set D' : FrobeniusMatrices f Λ := ⟨D.rank, D.matrix⟩
  have hfac : ∀ x, D'.localFactor x = PowerSeries.expand r hr (D.localFactor x) := fun x => by
    change localEulerFactor (D.matrix x) (residueDegree f x.1) =
      PowerSeries.expand r hr (localEulerFactor (D.matrix x) (residueDegree g x.1))
    rw [residueDegree_comp_specAlgebraMap]
    exact localEulerFactor_mul_eq_expand _ hr (residueDegree_pos g x.1 x.2).ne'
  ext n
  rw [PowerSeries.coeff_expand, FrobeniusMatrices.lFunction,
    D'.eulerSystem.coeff_eulerProduct_eq (t := D'.eulerSystem.support n) subset_rfl]
  have hprod : ∏ x ∈ D'.eulerSystem.support n, D'.eulerSystem.factor x =
      PowerSeries.expand r hr (∏ x ∈ D'.eulerSystem.support n, D.localFactor x) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun x _ => hfac x
  rw [hprod, PowerSeries.coeff_expand]
  split_ifs with h
  · rw [FrobeniusMatrices.lFunction,
      D.eulerSystem.coeff_eulerProduct_eq (t := D'.eulerSystem.support n) ?_]
    · rfl
    intro x hx
    rw [EulerSystem.mem_support] at hx ⊢
    change residueDegree f x.1 ≤ n
    change residueDegree g x.1 ≤ n / r at hx
    rw [residueDegree_comp_specAlgebraMap]
    obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr)] at hx
    exact Nat.mul_le_mul_left _ hx
  · rfl

section LAdic

open AlgebraicGeometry.SmallEtale CategoryTheory.Limits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **The L-function of a `ℚ_ℓ`-sheaf over a subfield of the field of constants.** If the
structure morphism of `X` over `k` factors through `Spec k'` for a finite extension `k'` of
degree `r`, then `L(X/k, F)(T) = L(X/k', F)(T ^ r)`: the closed points and their Frobenius
actions are the same, and the degree of a closed point over `k` is `r` times its degree over
`k'`. -/
theorem LAdicSheaf.rationalLFunction_comp_specAlgebraMap (F : LAdicSheaf B X ℓ)
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [Finite k] [Finite k']
    (g : X.1 ⟶ Spec (.of k')) [LocallyOfFiniteType g] [QuasiCompact g]
    (hr : Module.finrank k k' ≠ 0) :
    LAdicSheaf.rationalLFunction B X ℓ F (g ≫ Stacks.Frobenius.specAlgebraMap k k') =
      PowerSeries.expand _ hr (LAdicSheaf.rationalLFunction B X ℓ F g) :=
  FrobeniusMatrices.lFunction_comp_specAlgebraMap g (LAdicSheaf.frobeniusMatrices B X ℓ F g) hr

end LAdic

end LFunction

/-! ### Separation of cohomological degrees by weights -/

/-- Two complex polynomials with constant coefficient `1` and the same roots are equal. -/
theorem Polynomial.eq_of_roots_eq_of_coeff_zero_eq_one {P Q : ℂ[X]} (hP : P.coeff 0 = 1)
    (hQ : Q.coeff 0 = 1) (h : P.roots = Q.roots) : P = Q := by
  have hP0 : P ≠ 0 := fun h0 => by simp [h0] at hP
  have hQ0 : Q ≠ 0 := fun h0 => by simp [h0] at hQ
  have eP := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := P))
  have eQ := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := ℂ) (p := Q))
  set R := (Q.roots.map fun a => Polynomial.X - C a).prod
  rw [h] at eP
  have h0P := congrArg (fun F => F.coeff 0) eP
  have h0Q := congrArg (fun F => F.coeff 0) eQ
  simp only [coeff_C_mul] at h0P h0Q
  rw [hP] at h0P
  rw [hQ] at h0Q
  have hR : R.coeff 0 ≠ 0 := fun h0 => by rw [h0, mul_zero] at h0P; exact one_ne_zero h0P.symm
  have hl : P.leadingCoeff = Q.leadingCoeff := mul_right_cancel₀ hR (h0P.trans h0Q.symm)
  calc P = C P.leadingCoeff * R := eP.symm
    _ = Q := by rw [hl, eQ]

/-- **Separation by weights.** Let `P i`, `Q i` (`i ∈ s`) be complex polynomials with constant
coefficient `1` whose roots all have absolute value `c i`, the `c i` being pairwise distinct.
If the alternating products `∏ P_i ^ {(-1) ^ (i + 1)}` and `∏ Q_i ^ {(-1) ^ (i + 1)}` agree,
written without denominators, then `P i = Q i` for every `i`. -/
theorem Polynomial.eq_of_alternating_prod_eq {s : Finset ℤ} (P Q : ℤ → ℂ[X]) (c : ℤ → ℝ)
    (hc : Set.InjOn c s) (hP0 : ∀ i ∈ s, (P i).coeff 0 = 1) (hQ0 : ∀ i ∈ s, (Q i).coeff 0 = 1)
    (hPr : ∀ i ∈ s, ∀ z ∈ (P i).roots, ‖z‖ = c i) (hQr : ∀ i ∈ s, ∀ z ∈ (Q i).roots, ‖z‖ = c i)
    (h : ∏ i ∈ s, (if Even i then Q i else P i) = ∏ i ∈ s, (if Even i then P i else Q i)) :
    ∀ i ∈ s, P i = Q i := by
  classical
  set A : ℤ → ℂ[X] := fun i => if Even i then Q i else P i
  set B : ℤ → ℂ[X] := fun i => if Even i then P i else Q i
  have hA0 : ∀ i ∈ s, (A i).coeff 0 = 1 := fun i hi => by
    simp only [A]; split_ifs <;> simp [hP0 i hi, hQ0 i hi]
  have hB0 : ∀ i ∈ s, (B i).coeff 0 = 1 := fun i hi => by
    simp only [B]; split_ifs <;> simp [hP0 i hi, hQ0 i hi]
  have hAr : ∀ i ∈ s, ∀ z ∈ (A i).roots, ‖z‖ = c i := fun i hi z hz => by
    simp only [A] at hz; split_ifs at hz
    exacts [hQr i hi z hz, hPr i hi z hz]
  have hBr : ∀ i ∈ s, ∀ z ∈ (B i).roots, ‖z‖ = c i := fun i hi z hz => by
    simp only [B] at hz; split_ifs at hz
    exacts [hPr i hi z hz, hQr i hi z hz]
  have hne : ∀ (F : ℤ → ℂ[X]), (∀ i ∈ s, (F i).coeff 0 = 1) → ∀ i ∈ s, F i ≠ 0 :=
    fun F hF i hi h0 => by simpa [h0] using hF i hi
  -- the roots of `A i₀` are the roots of the product of norm `c i₀`
  have key : ∀ (F : ℤ → ℂ[X]), (∀ i ∈ s, (F i).coeff 0 = 1) →
      (∀ i ∈ s, ∀ z ∈ (F i).roots, ‖z‖ = c i) → ∀ i₀ ∈ s, ∀ z : ℂ, ‖z‖ = c i₀ →
        (∏ i ∈ s, F i).roots.count z = (F i₀).roots.count z := by
    intro F hF hFr i₀ hi₀ z hz
    rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.2 (hne F hF)), Multiset.count_bind,
      ← Finset.sum_eq_multiset_sum, Finset.sum_eq_single i₀]
    · intro i hi hii₀
      rw [Multiset.count_eq_zero]
      intro hzi
      exact hii₀ (hc hi hi₀ ((hFr i hi z hzi).symm.trans hz))
    · intro h; exact absurd hi₀ h
  have hAB : ∀ i ∈ s, (A i).roots = (B i).roots := by
    intro i hi
    ext z
    by_cases hz : ‖z‖ = c i
    · rw [← key A hA0 hAr i hi z hz, ← key B hB0 hBr i hi z hz, h]
    · rw [Multiset.count_eq_zero.2 fun hm => hz (hAr i hi z hm),
        Multiset.count_eq_zero.2 fun hm => hz (hBr i hi z hm)]
  intro i hi
  have := hAB i hi
  simp only [A, B] at this
  split_ifs at this
  · exact Polynomial.eq_of_roots_eq_of_coeff_zero_eq_one (hP0 i hi) (hQ0 i hi) this.symm
  · exact Polynomial.eq_of_roots_eq_of_coeff_zero_eq_one (hP0 i hi) (hQ0 i hi) this

section Purity

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The roots of `det (1 - φ T)` read in `ℂ` along `ι` are the inverses of the complex
eigenvalues of `φ`: if `φ` is pure of weight `w` they have absolute value `q ^ (- w / 2)`. -/
theorem norm_eq_of_mem_roots_map_reverse_charpoly {q : ℕ} {ι : K →+* ℂ} {w : ℤ}
    {φ : Module.End K V} (hφ : IsCharpolyPureOfWeight q ι w φ) {z : ℂ}
    (hz : z ∈ (φ.charpoly.reverse.map ι).roots) :
    ‖z‖ = ((q : ℝ) ^ ((w : ℝ) / 2))⁻¹ := by
  have hne : φ.charpoly.reverse.map ι ≠ 0 := fun h0 => by
    have := congrArg (fun F => F.coeff 0) h0
    simp [coeff_map, coeff_zero_reverse, (LinearMap.charpoly_monic φ).leadingCoeff] at this
  have hroot := (mem_roots hne).1 hz
  rw [IsRoot, eval_map] at hroot
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [eval₂_at_zero, coeff_zero_reverse, (LinearMap.charpoly_monic φ).leadingCoeff,
      map_one] at hroot
    exact one_ne_zero hroot
  let _ : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have h := eval₂_reverse_eq_zero_iff ι z⁻¹ φ.charpoly
  rw [invOf_eq_inv, inv_inv] at h
  have hw := hφ z⁻¹ (by rw [IsRoot, eval_map]; exact h.1 hroot)
  rw [← hw.norm_eq, norm_inv, inv_inv]

/-- The roots of `det (1 - φ T ^ r)` read in `ℂ` along `ι`, for `φ` pure of weight `w` relative
to `q ^ r`, have absolute value `q ^ (- w / 2)`. -/
theorem norm_eq_of_mem_roots_map_expand_reverse_charpoly {q r : ℕ} (hr : r ≠ 0) {ι : K →+* ℂ}
    {w : ℤ} {φ : Module.End K V} (hφ : IsCharpolyPureOfWeight (q ^ r) ι w φ) {z : ℂ}
    (hz : z ∈ ((expand K r φ.charpoly.reverse).map ι).roots) :
    ‖z‖ = ((q : ℝ) ^ ((w : ℝ) / 2))⁻¹ := by
  have hne : (expand K r φ.charpoly.reverse).map ι ≠ 0 := fun h0 => by
    have := congrArg (fun F => F.coeff 0) h0
    simp only [coeff_map, coeff_expand (Nat.pos_of_ne_zero hr), dvd_zero, ite_true,
      Nat.zero_div, coeff_zero_reverse, (LinearMap.charpoly_monic φ).leadingCoeff, map_one,
      coeff_zero] at this
    exact one_ne_zero this
  have hroot := (mem_roots hne).1 hz
  rw [Polynomial.map_expand, IsRoot, expand_eval] at hroot
  have hne' : φ.charpoly.reverse.map ι ≠ 0 := fun h0 => by
    have := congrArg (fun F => F.coeff 0) h0
    simp [coeff_map, coeff_zero_reverse, (LinearMap.charpoly_monic φ).leadingCoeff] at this
  have h := norm_eq_of_mem_roots_map_reverse_charpoly hφ ((mem_roots hne').2 hroot)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hpow : ((q : ℝ) ^ r) ^ ((w : ℝ) / 2) = ((q : ℝ) ^ ((w : ℝ) / 2)) ^ r := by
    rw [← Real.rpow_natCast (q : ℝ) r, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq,
      Real.rpow_natCast]
  rw [norm_pow, Nat.cast_pow, hpow, ← inv_pow] at h
  exact (pow_left_inj₀ (norm_nonneg z) (inv_nonneg.2 (Real.rpow_nonneg hq _)) hr).1 h

/-- For `q > 1` the absolute values `q ^ (- w / 2)` of different weights are different. -/
theorem injective_inv_rpow_half {q : ℕ} (hq : 1 < q) :
    Function.Injective fun w : ℤ => ((q : ℝ) ^ ((w : ℝ) / 2))⁻¹ := by
  intro a b h
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have h' : (q : ℝ) ^ ((a : ℝ) / 2) = (q : ℝ) ^ ((b : ℝ) / 2) := inv_injective h
  have hmono : StrictMono fun x : ℝ => (q : ℝ) ^ x := fun x y hxy =>
    Real.rpow_lt_rpow_of_exponent_lt hq' hxy
  have := hmono.injective h'
  have : (a : ℝ) = b := by linarith
  exact_mod_cast this

end Purity

/-! ### The Frobenius characteristic polynomials over the field of constants -/

section Main

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]

/-- Outside a finite set of degrees the cohomology over `k` and over `k'` vanishes. -/
theorem exists_finset_subsingleton_rationalGeometricCompactlySupportedCohomology
    {k k' : Type u} [Field k] [Fintype k] [Field k'] [Fintype k']
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    (g : X.1 ⟶ Spec (.of k')) [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (jg : CompactificationOf (Over.mk g)) (kbar' : Type u) [Field kbar'] [Algebra k' kbar']
    [IsAlgClosure k' kbar'] (p q q' : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    (hcard : Fintype.card k = p ^ q) (hcard' : Fintype.card k' = p ^ q') (hℓp : ℓ ≠ p)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    ∃ s : Finset ℤ, ∀ i ∉ s,
      Subsingleton (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) ∧
      Subsingleton
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ g jg kbar' F i) := by
  have hf := (LAdicSheaf.traceFormula B X ℓ f j kbar p q hcard hℓp F).2.1
  have hg := (LAdicSheaf.traceFormula B X ℓ g jg kbar' p q' hcard' hℓp F).2.1
  by_cases hd : ∃ d : ℕ, topologicalKrullDim X.1 = d
  · obtain ⟨d, hd⟩ := hd
    refine ⟨Finset.Icc 0 (2 * (d : ℤ)), fun i hi => ⟨?_, ?_⟩⟩ <;>
    · rw [← not_nontrivial_iff_subsingleton]
      intro hn
      obtain ⟨h0, d', hd', hi'⟩ := (by first | exact hf i hn | exact hg i hn)
      rw [hd] at hd'
      have : d = d' := by exact_mod_cast hd'
      subst this
      exact hi (Finset.mem_Icc.2 ⟨h0, hi'⟩)
  · refine ⟨∅, fun i _ => ⟨?_, ?_⟩⟩ <;>
    · rw [← not_nontrivial_iff_subsingleton]
      intro hn
      obtain ⟨_, d', hd', _⟩ := (by first | exact hf i hn | exact hg i hn)
      exact hd ⟨d', hd'⟩

/-- `gradedCharSeries` as a finite product of characteristic polynomials and their inverses. -/
theorem gradedCharSeries_eq_prod_reverse_charpoly {K : Type*} [Field K] (V : ℤ → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, FiniteDimensional K (V i)]
    (φ : ∀ i, V i →ₗ[K] V i) (s : Finset ℤ) (hs : ∀ i ∉ s, Subsingleton (V i)) :
    gradedCharSeries V φ = ∏ i ∈ s, if Even i then
      PowerSeries.invOfUnit (((φ i).charpoly.reverse : K[X]) : PowerSeries K) 1
      else (((φ i).charpoly.reverse : K[X]) : PowerSeries K) := by
  rw [Stacks.EtaleCohomology.gradedCharSeries_eq_prod V φ s hs]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gradedCharFactor, charPowerSeries_one_eq_reverse_charpoly]

/-- On the zero space `det(1 - φ T) = 1`. -/
theorem reverse_charpoly_eq_one_of_subsingleton {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Subsingleton V] (φ : Module.End K V) :
    φ.charpoly.reverse = 1 := by
  have hc : φ.charpoly = 1 := by
    apply Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    rw [LinearMap.charpoly_natDegree, Module.finrank_zero_of_subsingleton]
  rw [hc, ← C_1, reverse_C, C_1]

/-- `det(1 - φ T)` has constant coefficient `1`. -/
theorem coeff_zero_reverse_charpoly {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (φ : Module.End K V) :
    φ.charpoly.reverse.coeff 0 = 1 := by
  rw [coeff_zero_reverse, (LinearMap.charpoly_monic φ).leadingCoeff]

/-- **The Frobenius over a subfield of the field of constants, for pure cohomology.** Let the
structure morphism `f = g ≫ (Spec k' ⟶ Spec k)` of a separated scheme `X` of finite type over a
finite field `k` factor through a finite extension `k'` of degree `r`, and let `F` be an ℓ-adic
sheaf, `ℓ ≠ p`. If for some embedding `ι : ℚ_ℓ → ℂ` the geometric Frobenius on
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` over `k` is pure of weight `i` (relative to `#k`) and the one over `k'` is
pure of weight `i` (relative to `#k'`), in every degree `i`, then
`det(1 - F_k T | Hⁱ_c) = det(1 - F_{k'} T ^ r | Hⁱ_c)` in every degree. -/
theorem LAdicSheaf.reverse_charpoly_rationalGeometricCompactlySupportedFrobenius_eq_comp_of_pure
    {k k' : Type u} [Field k] [Fintype k] [Field k'] [Fintype k'] [Algebra k k']
    (g : X.1 ⟶ Spec (.of k')) [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (j : CompactificationOf (Over.mk (g ≫ Stacks.Frobenius.specAlgebraMap k k')))
    (jg : CompactificationOf (Over.mk g))
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (kbar' : Type u) [Field kbar'] [Algebra k' kbar'] [IsAlgClosure k' kbar']
    (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p] (hcard : Fintype.card k = p ^ q)
    (hcard' : Fintype.card k' = p ^ (q * Module.finrank k k')) (hℓp : ℓ ≠ p)
    (F : LAdicSheaf.{u, u + 1} B X ℓ)
    [∀ i, FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      (g ≫ Stacks.Frobenius.specAlgebraMap k k') j kbar F i)]
    [∀ i, FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ g jg kbar' F i)]
    (ι : ℚ_[ℓ] →+* ℂ)
    (hpure : ∀ i : ℤ, IsCharpolyPureOfWeight (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ
        (g ≫ Stacks.Frobenius.specAlgebraMap k k') j kbar p q hcard F i).hom)
    (hpure' : ∀ i : ℤ, IsCharpolyPureOfWeight (p ^ (q * Module.finrank k k')) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ g jg kbar' p
        (q * Module.finrank k k') hcard' F i).hom)
    (i : ℤ) :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ
        (g ≫ Stacks.Frobenius.specAlgebraMap k k') j kbar p q hcard F i).hom.charpoly.reverse =
      ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ g jg kbar' p
        (q * Module.finrank k k') hcard' F i).hom.charpoly.reverse).comp
        (Polynomial.X ^ Module.finrank k k') := by
  classical
  have hr : Module.finrank k k' ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨s, hs⟩ := exists_finset_subsingleton_rationalGeometricCompactlySupportedCohomology B X ℓ
    (g ≫ Stacks.Frobenius.specAlgebraMap k k') j kbar g jg kbar' p q (q * Module.finrank k k')
    hcard hcard' hℓp F
  set P : ℤ → ℚ_[ℓ][X] := fun i =>
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ
      (g ≫ Stacks.Frobenius.specAlgebraMap k k') j kbar p q hcard F
      i).hom.charpoly.reverse with hP_def
  set Q : ℤ → ℚ_[ℓ][X] := fun i => expand ℚ_[ℓ] (Module.finrank k k')
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ g jg kbar' p
      (q * Module.finrank k k') hcard' F
      i).hom.charpoly.reverse with hQ_def
  have hP1 : ∀ i, (P i).coeff 0 = 1 := fun i => coeff_zero_reverse_charpoly _
  have hQ1 : ∀ i, (Q i).coeff 0 = 1 := fun i => by
    simp only [Q, coeff_expand (Nat.pos_of_ne_zero hr), dvd_zero, ite_true, Nat.zero_div,
      coeff_zero_reverse_charpoly]
  have hcP : ∀ i, PowerSeries.constantCoeff ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) = 1 :=
    fun i => by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP1]
  have hcQ : ∀ i, PowerSeries.constantCoeff ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) = 1 :=
    fun i => by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hQ1]
  -- the L-functions over `k` and over `k'`
  have hL := LAdicSheaf.rationalLFunction_comp_specAlgebraMap B X ℓ F g hr
  have e₁ :=
    Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius
      B X ℓ (g ≫ Stacks.Frobenius.specAlgebraMap k k') j kbar p q hcard hℓp F
  have e₂ :=
    Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius
      B X ℓ g jg kbar' p (q * Module.finrank k k') hcard' hℓp F
  rw [e₁, e₂,
    gradedCharSeries_eq_prod_reverse_charpoly _ _ s (fun i hi => (hs i hi).1),
    gradedCharSeries_eq_prod_reverse_charpoly _ _ s (fun i hi => (hs i hi).2), map_prod] at hL
  have hL' : (∏ i ∈ s, if Even i then PowerSeries.invOfUnit ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) 1
      else ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ])) =
      ∏ i ∈ s, if Even i then PowerSeries.invOfUnit ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) 1
      else ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) := by
    refine hL.trans (Finset.prod_congr rfl fun i _ => ?_)
    have hc' : PowerSeries.constantCoeff (((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius
        B X ℓ g jg kbar' p (q * Module.finrank k k') hcard' F i).hom.charpoly.reverse : ℚ_[ℓ][X]) :
          PowerSeries ℚ_[ℓ]) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        coeff_zero_reverse_charpoly]
    split_ifs
    · rw [expand_invOfUnit _ hc', ← coe_expand]
    · rw [← coe_expand]
  -- clearing denominators
  set A : ℤ → ℚ_[ℓ][X] := fun i => if Even i then Q i else P i
  set A' : ℤ → ℚ_[ℓ][X] := fun i => if Even i then P i else Q i
  set e : ℤ → PowerSeries ℚ_[ℓ] := fun i => if Even i then
    ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) * ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) else 1
  have hinvP : ∀ i, PowerSeries.invOfUnit ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) 1 *
      ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) = 1 := fun i =>
    PowerSeries.invOfUnit_mul _ 1 (by simp [hcP i])
  have hinvQ : ∀ i, PowerSeries.invOfUnit ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) 1 *
      ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) = 1 := fun i =>
    PowerSeries.invOfUnit_mul _ 1 (by simp [hcQ i])
  have hAA' : ∏ i ∈ s, A i = ∏ i ∈ s, A' i := by
    have hcoe : ∀ G : ℤ → ℚ_[ℓ][X], ((∏ i ∈ s, G i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) =
        ∏ i ∈ s, ((G i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) := fun G =>
      map_prod Polynomial.coeToPowerSeries.ringHom G s
    rw [← Polynomial.coe_inj, hcoe, hcoe]
    have h1 : ∀ i, ((A i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) = (if Even i then
        PowerSeries.invOfUnit ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) 1
        else ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ])) * e i := fun i => by
      simp only [A, e]; split_ifs
      · rw [← mul_assoc, hinvP, one_mul]
      · rw [mul_one]
    have h2 : ∀ i, ((A' i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) = (if Even i then
        PowerSeries.invOfUnit ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]) 1
        else ((Q i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ])) * e i := fun i => by
      simp only [A', e]; split_ifs
      · rw [mul_comm ((P i : ℚ_[ℓ][X]) : PowerSeries ℚ_[ℓ]), ← mul_assoc, hinvQ, one_mul]
      · rw [mul_one]
    simp_rw [h1, h2]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hL']
  -- separation by weights in `ℂ`
  have hpq : 1 < p ^ q := by
    have hq : q ≠ 0 := by
      rintro rfl
      have := Fintype.one_lt_card (α := k)
      rw [hcard, pow_zero] at this
      exact lt_irrefl _ this
    exact Nat.one_lt_pow hq (Fact.out : p.Prime).one_lt
  have hsep := Polynomial.eq_of_alternating_prod_eq (s := s) (fun i => (P i).map ι)
    (fun i => (Q i).map ι) (fun w : ℤ => (((p ^ q : ℕ) : ℝ) ^ ((w : ℝ) / 2))⁻¹)
    ((injective_inv_rpow_half hpq).injOn)
    (fun i _ => by rw [coeff_map, hP1, map_one]) (fun i _ => by rw [coeff_map, hQ1, map_one])
    (fun i _ z hz => norm_eq_of_mem_roots_map_reverse_charpoly (hpure i) hz)
    (fun i _ z hz => norm_eq_of_mem_roots_map_expand_reverse_charpoly hr
      (by rw [← pow_mul]; exact hpure' i) hz)
    (by
      have := congrArg (Polynomial.map ι) hAA'
      rw [Polynomial.map_prod, Polynomial.map_prod] at this
      convert this using 2 with i _ i _ <;> simp only [A, A'] <;> split_ifs <;> rfl)
  change P i = Q i
  by_cases hi : i ∈ s
  · exact Polynomial.map_injective ι ι.injective (hsep i hi)
  · have h1 := (hs i hi).1
    have h2 := (hs i hi).2
    simp only [P, Q, reverse_charpoly_eq_one_of_subsingleton, map_one]

end Main
end Weil
