module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Descent.Module.AugmentedDescentComplex
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Exactness of the Amitsur complex of a split ring homomorphism

Let `A → B` be a homomorphism of commutative rings admitting an `A`-linear section
`s : B → A`, i.e. `s (algebraMap A B a) = a`, and let `M` be an `A`-module. Then the Amitsur
complex `0 → M → B ⊗[A] M → B ⊗[A] B ⊗[A] M → ⋯` is exact.

The proof is the classical contracting homotopy: the maps
`b₀ ⊗ b₁ ⊗ ⋯ ⊗ bₙ ⊗ m ↦ s(b₀) • (b₁ ⊗ ⋯ ⊗ bₙ ⊗ m)` satisfy `h d + d h = id` in every degree,
and `h d = id` on `M`.

## Main definitions

* `Algebra.amitsurContraction s n`: the contracting map
  `B^{⊗(n + 2)} ⊗[A] M → B^{⊗(n + 1)} ⊗[A] M`.
* `Algebra.amitsurAugmentationContraction s`: the contracting map `B ⊗[A] M → M`.

## Main results

* `Algebra.amitsurComplex_d_zero_one_injective`: the first map `M → B ⊗[A] M` is injective.
* `Algebra.amitsurComplex_acyclic_of_linear_section`: the Amitsur complex is exact.

## Implementation notes

Only `s 1 = 1` is used, which is how the auxiliary lemmas are stated. The section is
only `A`-linear, as in the source; Stacks Lemma 023L
(`AlgebraicTopology.amitsurExtendedCochainComplex_acyclic_of_section`) assumes an algebra
section and is stated for a universe-lifted variant of the complex.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 023L](https://stacks.math.columbia.edu/tag/023L)
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Stacks.Descent
open scoped TensorProduct

universe u v

namespace Algebra

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {M : Type (max u v)} [AddCommGroup M] [Module A M]

/-- The `A`-linear map `B ⊗[A] N → N`, `b ⊗ n ↦ s b • n`, induced by an `A`-linear map
`s : B → A`. -/
noncomputable def sectionContract (s : B →ₗ[A] A) (N : Type*) [AddCommGroup N] [Module A N] :
    B ⊗[A] N →ₗ[A] N :=
  (_root_.TensorProduct.lid A N).toLinearMap ∘ₗ s.rTensor N

@[simp]
lemma sectionContract_tmul (s : B →ₗ[A] A) {N : Type*} [AddCommGroup N] [Module A N]
    (b : B) (x : N) : sectionContract s N (b ⊗ₜ[A] x) = s b • x :=
  rfl

variable (M) in
/-- The `A`-linear map `δᵢ ⊗ id_M : B^{⊗(n + 1)} ⊗[A] M → B^{⊗(n + 2)} ⊗[A] M`. -/
noncomputable abbrev amitsurInsert (n : ℕ) (i : Fin (n + 2)) :
    (tensorPowerAlg A B n : Type u) ⊗[A] M →ₗ[A] (tensorPowerAlg A B (n + 1) : Type u) ⊗[A] M :=
  ((tensorModuleFunctor A M).map (tensorInsertOne A B n i)).hom

variable (M) in
/-- The alternating sum `∑ᵢ (-1)ⁱ δᵢ ⊗ id_M`, the differential of the Amitsur complex on
`B^{⊗(n + 1)} ⊗[A] M`. -/
noncomputable def amitsurDiff (n : ℕ) :
    (tensorPowerAlg A B n : Type u) ⊗[A] M →ₗ[A] (tensorPowerAlg A B (n + 1) : Type u) ⊗[A] M :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • amitsurInsert M n i

variable (M) in
/-- The contracting map `b₀ ⊗ x ⊗ m ↦ s b₀ • (x ⊗ m)` from `B^{⊗(n + 2)} ⊗[A] M` to
`B^{⊗(n + 1)} ⊗[A] M`. -/
noncomputable def amitsurContraction (s : B →ₗ[A] A) (n : ℕ) :
    (tensorPowerAlg A B (n + 1) : Type u) ⊗[A] M →ₗ[A] (tensorPowerAlg A B n : Type u) ⊗[A] M :=
  sectionContract s _ ∘ₗ
    (_root_.TensorProduct.assoc A B (tensorPowerAlg A B n : Type u) M).toLinearMap

variable (M) in
/-- The contracting map `b ⊗ m ↦ s b • m` from `B ⊗[A] M` to `M`. -/
noncomputable def amitsurAugmentationContraction (s : B →ₗ[A] A) :
    (tensorPowerAlg A B 0 : Type u) ⊗[A] M →ₗ[A] M :=
  sectionContract s M

lemma amitsurContraction_tmul (s : B →ₗ[A] A) (n : ℕ) (b : B)
    (x : (tensorPowerAlg A B n : Type u)) (m : M) :
    amitsurContraction M s n
        (((b ⊗ₜ[A] x : B ⊗[A] (tensorPowerAlg A B n : Type u)) :
          (tensorPowerAlg A B (n + 1) : Type u)) ⊗ₜ[A] m) =
      s b • (x ⊗ₜ[A] m) :=
  rfl

lemma amitsurInsert_tmul (n : ℕ) (i : Fin (n + 2)) (x : (tensorPowerAlg A B n : Type u))
    (m : M) : amitsurInsert M n i (x ⊗ₜ[A] m) = (tensorInsertOne A B n i).hom x ⊗ₜ[A] m :=
  rfl

/-- Step 1: the contraction is a retraction of `m ↦ 1 ⊗ m`. -/
lemma amitsurAugmentationContraction_one_tmul (s : B →ₗ[A] A) (hs : s 1 = 1) (m : M) :
    amitsurAugmentationContraction M s ((1 : (tensorPowerAlg A B 0 : Type u)) ⊗ₜ[A] m) = m := by
  change s 1 • m = m
  rw [hs, one_smul]

/-- Step 2, `i = 0`: `h ∘ δ₀ = id`. -/
lemma amitsurContraction_comp_insert_zero (s : B →ₗ[A] A) (hs : s 1 = 1) (n : ℕ) :
    amitsurContraction M s (n + 1) ∘ₗ amitsurInsert M (n + 1) 0 = LinearMap.id := by
  refine _root_.TensorProduct.ext' fun x m => ?_
  rw [LinearMap.comp_apply, amitsurInsert_tmul, tensorInsertOne_zero_apply,
    amitsurContraction_tmul, hs, one_smul, LinearMap.id_apply]

/-- Step 2, `i ≥ 1`: `h ∘ δᵢ₊₁ = δᵢ ∘ h`. -/
lemma amitsurContraction_comp_insert_succ (s : B →ₗ[A] A) (n : ℕ) (i : Fin (n + 2)) :
    amitsurContraction M s (n + 1) ∘ₗ amitsurInsert M (n + 1) i.succ =
      amitsurInsert M n i ∘ₗ amitsurContraction M s n := by
  refine _root_.TensorProduct.ext_threefold (R := A) (M := B)
    (N := (tensorPowerAlg A B n : Type u)) (P := M) fun b y m => ?_
  change amitsurContraction M s (n + 1)
      ((tensorInsertOne A B (n + 1) i.succ).hom
        ((b ⊗ₜ[A] y : B ⊗[A] (tensorPowerAlg A B n : Type u)) :
          (tensorPowerAlg A B (n + 1) : Type u)) ⊗ₜ[A] m) =
    amitsurInsert M n i (s b • (y ⊗ₜ[A] m))
  rw [tensorInsertOne_succ_tmul, amitsurContraction_tmul, map_smul, amitsurInsert_tmul]

/-- Step 3 in degree zero: `h₀ ∘ d₀ + d₋₁ ∘ h₋₁ = id` on `B ⊗[A] M`. -/
lemma amitsurContraction_zero_homotopy (s : B →ₗ[A] A) (hs : s 1 = 1)
    (x : (tensorPowerAlg A B 0 : Type u) ⊗[A] M) :
    amitsurContraction M s 0 (amitsurDiff M 0 x) +
        (1 : (tensorPowerAlg A B 0 : Type u)) ⊗ₜ[A] amitsurAugmentationContraction M s x = x := by
  induction x using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul b m =>
    rw [amitsurDiff, Fin.sum_univ_two, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, amitsurInsert_tmul, amitsurInsert_tmul, tensorInsertOne_zero_apply,
      tensorInsertOne_zero_one_apply]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, map_add,
      map_neg]
    change s 1 • ((b : B) ⊗ₜ[A] m : B ⊗[A] M) + -(s b • ((1 : B) ⊗ₜ[A] m : B ⊗[A] M)) +
      ((1 : B) ⊗ₜ[A] (s b • m) : B ⊗[A] M) = ((b : B) ⊗ₜ[A] m : B ⊗[A] M)
    rw [hs, one_smul, ← _root_.TensorProduct.tmul_smul, neg_add_cancel_right]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, _root_.TensorProduct.tmul_add]
    conv_rhs => rw [← hx, ← hy]
    abel

/-- Step 3 in positive degree: `hₙ₊₁ ∘ dₙ₊₁ + dₙ ∘ hₙ = id`. -/
lemma amitsurContraction_succ_homotopy (s : B →ₗ[A] A) (hs : s 1 = 1) (n : ℕ)
    (x : (tensorPowerAlg A B (n + 1) : Type u) ⊗[A] M) :
    amitsurContraction M s (n + 1) (amitsurDiff M (n + 1) x) +
        amitsurDiff M n (amitsurContraction M s n x) = x := by
  have h0 (y : (tensorPowerAlg A B (n + 1) : Type u) ⊗[A] M) :
      amitsurContraction M s (n + 1) (amitsurInsert M (n + 1) 0 y) = y :=
    LinearMap.congr_fun (amitsurContraction_comp_insert_zero s hs n) y
  have hS (i : Fin (n + 2)) (y : (tensorPowerAlg A B (n + 1) : Type u) ⊗[A] M) :
      amitsurContraction M s (n + 1) (amitsurInsert M (n + 1) i.succ y) =
        amitsurInsert M n i (amitsurContraction M s n y) :=
    LinearMap.congr_fun (amitsurContraction_comp_insert_succ s n i) y
  rw [amitsurDiff, LinearMap.sum_apply, map_sum, Fin.sum_univ_succ, amitsurDiff,
    LinearMap.sum_apply]
  have hsum : ∑ i : Fin (n + 2), amitsurContraction M s (n + 1)
      (((-1 : ℤ) ^ ((i.succ : Fin (n + 3)) : ℕ) • amitsurInsert M (n + 1) i.succ) x) =
      -∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ) • amitsurInsert M n i)
        (amitsurContraction M s n x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, map_zsmul, hS, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      LinearMap.smul_apply]
  rw [hsum, Fin.val_zero, pow_zero, one_smul, h0, add_assoc, neg_add_cancel, add_zero]

/-- The differential of the Amitsur complex, transported to `B^{⊗(n + 1)} ⊗[A] M`. -/
lemma amitsurComplex_d_succ_apply (n : ℕ) (x : (tensorPowerAlg A B n : Type u) ⊗[A] M) :
    (amitsurComplex A B M).d (n + 1) (n + 2) ((amitsurComplexXIso A B M n).hom x) =
      (amitsurComplexXIso A B M (n + 1)).hom (amitsurDiff M n x) := by
  change ((amitsurComplexXIso A B M n).hom ≫ (amitsurComplex A B M).d (n + 1) (n + 2)) x = _
  rw [amitsurComplex_d_succ]
  have hsum : (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (tensorModuleFunctor A M).map (tensorInsertOne A B n i)).hom = amitsurDiff M n := by
    rw [ModuleCat.hom_sum, amitsurDiff]
    simp only [ModuleCat.hom_zsmul]
    rfl
  exact congrArg (fun y => (amitsurComplexXIso A B M (n + 1)).hom y) (LinearMap.congr_fun hsum x)

/-- The first map of the Amitsur complex has the retraction `b ⊗ m ↦ s b • m`. -/
lemma amitsurAugmentationContraction_d_zero_one (s : B →ₗ[A] A) (hs : s 1 = 1) (m : M) :
    amitsurAugmentationContraction M s
      ((amitsurComplexXIso A B M 0).inv ((amitsurComplex A B M).d 0 1 m)) = m := by
  rw [amitsurComplex_d_zero_one, Iso.hom_inv_id_apply,
    amitsurAugmentationContraction_one_tmul s hs]

/-- **The first map `M → B ⊗[A] M` of the Amitsur complex of a split ring homomorphism is
injective.** -/
@[weil "lem_fka3_amitsur_complex_split_case"]
theorem amitsurComplex_d_zero_one_injective (s : B →ₗ[A] A)
    (hs : ∀ a : A, s (algebraMap A B a) = a) :
    Function.Injective ((amitsurComplex A B M).d 0 1 : M → (amitsurComplex A B M).X 1) := by
  have hs1 : s 1 = 1 := by simpa using hs 1
  intro m m' h
  rw [← amitsurAugmentationContraction_d_zero_one s hs1 m,
    ← amitsurAugmentationContraction_d_zero_one s hs1 m']
  exact congrArg _ (congrArg _ h)

/-- **The Amitsur complex of a split ring homomorphism is exact.** If `A → B` has an `A`-linear
section `s`, then for every `A`-module `M` the Amitsur complex
`0 → M → B ⊗[A] M → B ⊗[A] B ⊗[A] M → ⋯` is exact. -/
@[weil "lem_fka3_amitsur_complex_split_case"]
theorem amitsurComplex_acyclic_of_linear_section (s : B →ₗ[A] A)
    (hs : ∀ a : A, s (algebraMap A B a) = a) :
    (amitsurComplex A B M).Acyclic := by
  have hs1 : s 1 = 1 := by simpa using hs 1
  set K := amitsurComplex A B M
  rw [HomologicalComplex.acyclic_iff]
  intro k
  rcases k with _ | n
  · rw [HomologicalComplex.exactAt_iff' K 0 0 1 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    change K.d 0 1 x = 0 at hx
    have h0 : x = 0 := amitsurComplex_d_zero_one_injective s hs (hx.trans (map_zero _).symm)
    exact ⟨0, by rw [h0]; rfl⟩
  · rw [HomologicalComplex.exactAt_iff' K n (n + 1) (n + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    change K.d (n + 1) (n + 2) x = 0 at hx
    change ∃ y, K.d n (n + 1) y = x
    obtain ⟨x, rfl⟩ := (amitsurComplexXIso A B M n).toLinearEquiv.surjective x
    change K.d (n + 1) (n + 2) ((amitsurComplexXIso A B M n).hom x) = 0 at hx
    rw [amitsurComplex_d_succ_apply] at hx
    have hD : amitsurDiff M n x = 0 :=
      (amitsurComplexXIso A B M (n + 1)).toLinearEquiv.injective (hx.trans (map_zero _).symm)
    change ∃ y, K.d n (n + 1) y = (amitsurComplexXIso A B M n).hom x
    rcases n with _ | n
    · refine ⟨amitsurAugmentationContraction M s x, ?_⟩
      have := amitsurContraction_zero_homotopy s hs1 x
      rw [hD, map_zero, zero_add] at this
      rw [amitsurComplex_d_zero_one, this]
    · refine ⟨(amitsurComplexXIso A B M n).hom (amitsurContraction M s n x), ?_⟩
      have := amitsurContraction_succ_homotopy s hs1 n x
      rw [hD, map_zero, zero_add] at this
      rw [amitsurComplex_d_succ_apply, this]

end Algebra

/-! ### The descent lemma in the split case -/

/-!
# The descent lemma in the split case

Let `j : A → B` be a homomorphism of commutative rings admitting an `A`-linear section, that is
an `A`-linear map `s : B → A` with `s ∘ j = id_A`, and let `M` be an `A`-module. Then the
beginning of the Amitsur sequence

`0 → M → M ⊗[A] B → M ⊗[A] B ⊗[A] B`,

with maps `m ↦ m ⊗ 1` and `m ⊗ b ↦ m ⊗ 1 ⊗ b - m ⊗ b ⊗ 1`, is exact. No flatness hypothesis is
needed: the section provides a retraction `m ⊗ b ↦ s(b) m` of the first map and a contracting
homotopy `m ⊗ b ⊗ b' ↦ s(b) m ⊗ b'` in degree zero.

## Main definitions

* `TensorProduct.amitsurAugmentation A B M`: the map `M → M ⊗[A] B`, `m ↦ m ⊗ 1`.
* `TensorProduct.amitsurDiffZero A B M`: the map `M ⊗[A] B → M ⊗[A] (B ⊗[A] B)`,
  `m ⊗ b ↦ m ⊗ (1 ⊗ b) - m ⊗ (b ⊗ 1)`.

## Main results

* `TensorProduct.amitsurAugmentation_injective_of_section`: the first map is injective.
* `TensorProduct.exact_amitsurAugmentation_amitsurDiffZero_of_section`: the sequence is exact
  at `M ⊗[A] B`.

## Implementation notes

The section is only assumed `A`-linear, as in the source, rather than an `A`-algebra map. The
triple tensor product `M ⊗ B ⊗ B` is bracketed as `M ⊗[A] (B ⊗[A] B)`, so the second map is
`id_M ⊗ (b ↦ 1 ⊗ b - b ⊗ 1)`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 023L](https://stacks.math.columbia.edu/tag/023L)
-/

@[expose] public section

open scoped TensorProduct

namespace TensorProduct

variable (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
  (M : Type*) [AddCommGroup M] [Module A M]

/-- The augmentation `M → M ⊗[A] B`, `m ↦ m ⊗ 1`, of the Amitsur sequence. -/
noncomputable def amitsurAugmentation : M →ₗ[A] M ⊗[A] B :=
  (TensorProduct.mk A M B).flip 1

@[simp]
lemma amitsurAugmentation_apply (m : M) : amitsurAugmentation A B M m = m ⊗ₜ[A] (1 : B) :=
  rfl

/-- The first differential `M ⊗[A] B → M ⊗[A] (B ⊗[A] B)`,
`m ⊗ b ↦ m ⊗ (1 ⊗ b) - m ⊗ (b ⊗ 1)`, of the Amitsur sequence. -/
noncomputable def amitsurDiffZero : M ⊗[A] B →ₗ[A] M ⊗[A] (B ⊗[A] B) :=
  LinearMap.lTensor M
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap -
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap)

@[simp]
lemma amitsurDiffZero_tmul (m : M) (b : B) :
    amitsurDiffZero A B M (m ⊗ₜ[A] b) =
      m ⊗ₜ[A] ((1 : B) ⊗ₜ[A] b) - m ⊗ₜ[A] (b ⊗ₜ[A] (1 : B)) := by
  simp [amitsurDiffZero]

lemma amitsurDiffZero_comp_amitsurAugmentation :
    amitsurDiffZero A B M ∘ₗ amitsurAugmentation A B M = 0 := by
  ext m
  simp

variable {A B M}

/-- The retraction `m ⊗ b ↦ s(b) m` of the augmentation given by a section `s`. -/
private noncomputable def retraction (s : B →ₗ[A] A) : M ⊗[A] B →ₗ[A] M :=
  (TensorProduct.rid A M).toLinearMap ∘ₗ LinearMap.lTensor M s

private lemma retraction_tmul (s : B →ₗ[A] A) (m : M) (b : B) :
    retraction s (m ⊗ₜ[A] b) = s b • m := by
  simp [retraction]

/-- The homotopy `m ⊗ (b ⊗ b') ↦ m ⊗ s(b) b'` given by a section `s`. -/
private noncomputable def homotopy (s : B →ₗ[A] A) : M ⊗[A] (B ⊗[A] B) →ₗ[A] M ⊗[A] B :=
  LinearMap.lTensor M ((TensorProduct.lid A B).toLinearMap ∘ₗ LinearMap.rTensor B s)

private lemma homotopy_tmul (s : B →ₗ[A] A) (m : M) (b b' : B) :
    homotopy s (m ⊗ₜ[A] (b ⊗ₜ[A] b')) = m ⊗ₜ[A] (s b • b') := by
  simp [homotopy]

private lemma section_one (s : B →ₗ[A] A) (hs : s ∘ₗ Algebra.linearMap A B = LinearMap.id) :
    s 1 = 1 := by
  simpa using LinearMap.congr_fun hs 1

private lemma retraction_comp_amitsurAugmentation (s : B →ₗ[A] A)
    (hs : s ∘ₗ Algebra.linearMap A B = LinearMap.id) :
    retraction s ∘ₗ amitsurAugmentation A B M = LinearMap.id := by
  ext m
  simp [retraction_tmul, section_one s hs]

private lemma homotopy_identity (s : B →ₗ[A] A)
    (hs : s ∘ₗ Algebra.linearMap A B = LinearMap.id) :
    amitsurAugmentation A B M ∘ₗ retraction s + homotopy s ∘ₗ amitsurDiffZero A B M =
      LinearMap.id := by
  refine TensorProduct.ext' fun m b => ?_
  simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [retraction_tmul, amitsurAugmentation_apply, amitsurDiffZero_tmul, map_sub, homotopy_tmul,
    homotopy_tmul, section_one s hs, one_smul, ← TensorProduct.smul_tmul]
  abel

/-- **Descent lemma, split case, injectivity.** If `A → B` has an `A`-linear section, then
`m ↦ m ⊗ 1` is injective on every `A`-module `M`. -/
@[weil "lem_fka3_descent_lemma_split_case"]
theorem amitsurAugmentation_injective_of_section (s : B →ₗ[A] A)
    (hs : s ∘ₗ Algebra.linearMap A B = LinearMap.id) :
    Function.Injective (amitsurAugmentation A B M) :=
  Function.LeftInverse.injective (g := retraction s)
    (LinearMap.congr_fun (retraction_comp_amitsurAugmentation s hs))

/-- **Descent lemma, split case, exactness.** If `A → B` has an `A`-linear section, then for
every `A`-module `M` the sequence `M → M ⊗[A] B → M ⊗[A] (B ⊗[A] B)`, `m ↦ m ⊗ 1`,
`m ⊗ b ↦ m ⊗ (1 ⊗ b) - m ⊗ (b ⊗ 1)`, is exact at `M ⊗[A] B`. -/
@[weil "lem_fka3_descent_lemma_split_case"]
theorem exact_amitsurAugmentation_amitsurDiffZero_of_section (s : B →ₗ[A] A)
    (hs : s ∘ₗ Algebra.linearMap A B = LinearMap.id) :
    Function.Exact (amitsurAugmentation A B M) (amitsurDiffZero A B M) := by
  intro x
  constructor
  · intro hx
    refine ⟨retraction s x, ?_⟩
    have := LinearMap.congr_fun (homotopy_identity (M := M) s hs) x
    simpa [hx] using this
  · rintro ⟨m, rfl⟩
    exact LinearMap.congr_fun (amitsurDiffZero_comp_amitsurAugmentation A B M) m

end TensorProduct
