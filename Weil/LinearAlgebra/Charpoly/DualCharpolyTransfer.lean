module

public import Weil.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.CharP.Algebra

/-!
# Dual characteristic polynomials

Let `K` be a field, `L` an algebraically closed extension of `K` and `c ∈ K`. We say that `ψ` is
`c`-dual to `χ` over `L` if `ψ = ∏ (X - c / μ)` in `L[X]`, `μ` running over the roots of `χ` in `L`
with multiplicity. This is the relation between the characteristic polynomials of the two
endomorphisms `f`, `g` of a `c`-duality `B (f x) (g y) = c • B x y`.

We show that this relation is stable under products, and that it descends along the substitution
`T ↦ T ^ r` in the reversed polynomials: if `reverse χ = (reverse χ') (T ^ r)` and
`reverse ψ = (reverse ψ') (T ^ r)` (as for `det (1 - T F)` and `det (1 - T ^ r F ^ r)`), and `ψ'` is
`c ^ r`-dual to `χ'`, then `ψ` is `c`-dual to `χ`. In characteristic zero the roots of `χ` are
then the `r`-th roots of those of `χ'`, and the multiplicity of `γ ≠ 0` as a root of `χ` is that of
`γ ^ r` as a root of `χ'`.

## Main definitions

* `Weil.Polynomial.IsCharpolyDual L c χ ψ`: `ψ` is `c`-dual to `χ` over `L`.

## Main results

* `Weil.Polynomial.isCharpolyDual_iff_rootMultiplicity`: for `ψ` monic and `c ≠ 0`, the relation
  says that the multiplicity of `γ` in `ψ` is that of `c / γ` in `χ`.
* `Weil.Polynomial.eq_comp_X_pow_of_reverse_eq`: `reverse χ = (reverse χ') (X ^ r)` gives
  `χ = χ' (X ^ r)` when both constant coefficients are nonzero.
* `Weil.Polynomial.rootMultiplicity_comp_X_pow`: in characteristic zero, the multiplicity of
  `γ` in `p (X ^ r)` is that of `γ ^ r` in `p`, when `p 0 ≠ 0`.
* `Weil.Polynomial.IsCharpolyDual.of_reverse_eq_comp_X_pow`: descent of the relation.
* `Weil.Polynomial.even_natDegree_of_reverse_eq_comp_X_pow`,
  `Weil.Polynomial.even_rootMultiplicity_of_reverse_eq_comp_X_pow`: descent of parities.
* `Weil.Polynomial.IsCharpolyDual.prod`, `Weil.Polynomial.even_natDegree_prod`,
  `Weil.Polynomial.even_rootMultiplicity_prod`: products.
* `LinearMap.IsFrobeniusDuality.isCharpolyDual`: the characteristic polynomials of a `c`-duality.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

open Polynomial

namespace Weil.Polynomial

section Def

variable {K : Type*} (L : Type*) [Field K] [Field L] [Algebra K L]

@[expose] public section

/-- `ψ` is `c`-dual to `χ` over `L`: `ψ = ∏ (X - c / μ)` in `L[X]`, `μ` running over the roots of
`χ` in `L` with multiplicity. -/
def IsCharpolyDual (c : K) (χ ψ : K[X]) : Prop :=
  ψ.map (algebraMap K L) =
    ((χ.map (algebraMap K L)).roots.map fun μ => X - C (algebraMap K L c / μ)).prod

end

end Def

public section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A polynomial with nonzero constant coefficient does not vanish at `0` after base change. -/
theorem rootMultiplicity_zero_map_eq_zero {χ : K[X]} (hχ : χ.coeff 0 ≠ 0) :
    rootMultiplicity 0 (χ.map (algebraMap K L)) = 0 := by
  refine rootMultiplicity_eq_zero fun h => hχ ?_
  rwa [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, map_eq_zero] at h

/-- For `ψ` monic and `c ≠ 0`, `ψ` is `c`-dual to `χ` if and only if the multiplicity of every
`γ` as a root of `ψ` is that of `c / γ` as a root of `χ`. -/
theorem isCharpolyDual_iff_rootMultiplicity [IsAlgClosed L] {c : K} (hc : c ≠ 0) {χ ψ : K[X]}
    (hψ : ψ.Monic) :
    IsCharpolyDual L c χ ψ ↔ ∀ γ : L, rootMultiplicity γ (ψ.map (algebraMap K L)) =
      rootMultiplicity (algebraMap K L c / γ) (χ.map (algebraMap K L)) := by
  classical
  have hc' : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  set g : L → L := fun μ => algebraMap K L c / μ with hg
  have hinv : Function.Involutive g := fun μ => div_div_cancel₀ hc'
  have hcount : ∀ γ : L, ((χ.map (algebraMap K L)).roots.map g).count γ =
      rootMultiplicity (g γ) (χ.map (algebraMap K L)) := by
    intro γ
    conv_lhs => rw [← hinv γ]
    rw [Multiset.count_map_eq_count' _ _ hinv.injective, count_roots]
  constructor
  · intro h γ
    have h' : ψ.map (algebraMap K L) =
        (((χ.map (algebraMap K L)).roots.map g).map fun a => X - C a).prod := by
      rw [Multiset.map_map]; exact h
    rw [h', ← count_roots, roots_multiset_prod_X_sub_C, hcount]
  · intro h
    have hroots : (ψ.map (algebraMap K L)).roots = (χ.map (algebraMap K L)).roots.map g := by
      ext γ
      rw [count_roots, h γ, hcount]
    rw [IsCharpolyDual, (IsAlgClosed.splits _).eq_prod_roots_of_monic (hψ.map _), hroots,
      Multiset.map_map]
    rfl

/-- If `reverse χ = (reverse χ') (X ^ r)` and both constant coefficients are nonzero, then
`χ = χ' (X ^ r)`. -/
theorem eq_comp_X_pow_of_reverse_eq [Infinite K] {r : ℕ} {χ χ' : K[X]} (hχ0 : χ.coeff 0 ≠ 0)
    (hχ'0 : χ'.coeff 0 ≠ 0) (h : χ.reverse = χ'.reverse.comp (X ^ r)) :
    χ = χ'.comp (X ^ r) := by
  have htr : ∀ p : K[X], p.coeff 0 ≠ 0 → p.reverse.natDegree = p.natDegree := fun p hp => by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hp), Nat.sub_zero]
  have hdeg : χ.natDegree = χ'.natDegree * r := by
    rw [← htr χ hχ0, h, natDegree_comp, natDegree_X_pow, htr χ' hχ'0]
  refine eq_of_infinite_eval_eq _ _ (Set.infinite_of_finite_compl ?_)
  refine (Set.finite_singleton (0 : K)).subset fun x hx => ?_
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx
  by_contra hx0
  apply hx
  let : Invertible x := invertibleOfNonzero hx0
  let : Invertible (x ^ r) := invertibleOfNonzero (pow_ne_zero r hx0)
  have e1 := eval₂_reverse_mul_pow (RingHom.id K) x χ
  have e2 := eval₂_reverse_mul_pow (RingHom.id K) (x ^ r) χ'
  simp only [eval₂_id] at e1 e2
  rw [eval_comp, eval_pow, eval_X, ← e1, ← e2, h, eval_comp, eval_pow, eval_X, hdeg, pow_mul',
    invOf_pow]

/-- The roots of `X ^ r - β`, `β ≠ 0`, in characteristic zero are simple. -/
theorem count_roots_X_pow_sub_C [CharZero L] [DecidableEq L] {r : ℕ} (hr : 0 < r) {β : L}
    (hβ : β ≠ 0) (γ : L) :
    ((X ^ r - C β : L[X]).roots.count γ) = if γ ^ r = β then 1 else 0 := by
  have hmem : γ ∈ (X ^ r - C β : L[X]).roots ↔ γ ^ r = β := by
    rw [mem_roots (X_pow_sub_C_ne_zero hr β), IsRoot, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero]
  split_ifs with h
  · exact le_antisymm
      (count_roots_le_one (separable_X_pow_sub_C β (Nat.cast_ne_zero.mpr hr.ne') hβ) γ)
      (Multiset.one_le_count_iff_mem.mpr (hmem.mpr h))
  · exact Multiset.count_eq_zero.mpr (hmem.not.mpr h)

/-- In characteristic zero, over an algebraically closed field, the multiplicity of `γ` as a root
of `p (X ^ r)` is that of `γ ^ r` as a root of `p`, when `p 0 ≠ 0`. -/
theorem rootMultiplicity_comp_X_pow [CharZero L] [IsAlgClosed L] {r : ℕ} (hr : 0 < r) {p : L[X]}
    (hp : p.coeff 0 ≠ 0) (γ : L) :
    rootMultiplicity γ (p.comp (X ^ r)) = rootMultiplicity (γ ^ r) p := by
  classical
  have hp0 : p ≠ 0 := fun h => hp (by simp [h])
  have hroots0 : ∀ β ∈ p.roots, β ≠ 0 := by
    rintro β hβ rfl
    exact hp (by rwa [mem_roots hp0, IsRoot, ← coeff_zero_eq_eval_zero] at hβ)
  have hfac := (IsAlgClosed.splits p).eq_prod_roots
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  rw [← count_roots, ← count_roots]
  conv_lhs => rw [hfac]
  rw [mul_comp, C_comp, multiset_prod_comp, roots_C_mul _ hlc, Multiset.map_map,
    roots_multiset_prod]
  · generalize p.roots = S at hroots0 ⊢
    induction S using Multiset.induction_on with
    | empty => simp
    | cons β s ih =>
      rw [Multiset.map_cons, Multiset.cons_bind, Multiset.count_add, Multiset.count_cons,
        ih fun b hb => hroots0 b (Multiset.mem_cons_of_mem hb)]
      rw [add_comm]
      congr 1
      simpa using count_roots_X_pow_sub_C hr (hroots0 β (Multiset.mem_cons_self _ _)) γ
  · simp only [Multiset.mem_map, Function.comp_apply, sub_comp, X_comp, C_comp, not_exists,
      not_and]
    exact fun β _ h => X_pow_sub_C_ne_zero hr β h

/-- The relation `reverse χ = (reverse χ') (X ^ r)` gives, in characteristic zero and for
`γ ≠ 0`, that the multiplicity of `γ` in `χ` is that of `γ ^ r` in `χ'`. -/
theorem rootMultiplicity_map_eq_of_reverse_eq_comp_X_pow [CharZero K] [IsAlgClosed L] {r : ℕ}
    (hr : 0 < r) {χ χ' : K[X]} (hχ0 : χ.coeff 0 ≠ 0) (hχ'0 : χ'.coeff 0 ≠ 0)
    (h : χ.reverse = χ'.reverse.comp (X ^ r)) (γ : L) :
    rootMultiplicity γ (χ.map (algebraMap K L)) =
      rootMultiplicity (γ ^ r) (χ'.map (algebraMap K L)) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  rw [eq_comp_X_pow_of_reverse_eq hχ0 hχ'0 h, Polynomial.map_comp, Polynomial.map_pow, map_X]
  refine rootMultiplicity_comp_X_pow hr ?_ γ
  rwa [coeff_map, ne_eq, map_eq_zero]

/-- **Descent of the dual relation along `T ↦ T ^ r`.** If `reverse χ = (reverse χ') (X ^ r)` and
`reverse ψ = (reverse ψ') (X ^ r)`, and `ψ'` is `c ^ r`-dual to `χ'`, then `ψ` is `c`-dual to
`χ`. -/
theorem IsCharpolyDual.of_reverse_eq_comp_X_pow [CharZero K] [IsAlgClosed L] {c : K} (hc : c ≠ 0)
    {r : ℕ} (hr : 0 < r) {χ χ' ψ ψ' : K[X]} (hψm : ψ.Monic) (hψ'm : ψ'.Monic)
    (hχ0 : χ.coeff 0 ≠ 0) (hχ'0 : χ'.coeff 0 ≠ 0) (hψ0 : ψ.coeff 0 ≠ 0) (hψ'0 : ψ'.coeff 0 ≠ 0)
    (hχ : χ.reverse = χ'.reverse.comp (X ^ r)) (hψ : ψ.reverse = ψ'.reverse.comp (X ^ r))
    (h : IsCharpolyDual L (c ^ r) χ' ψ') : IsCharpolyDual L c χ ψ := by
  rw [isCharpolyDual_iff_rootMultiplicity (pow_ne_zero r hc) hψ'm] at h
  rw [isCharpolyDual_iff_rootMultiplicity hc hψm]
  intro γ
  rcases eq_or_ne γ 0 with rfl | hγ
  · rw [div_zero, rootMultiplicity_zero_map_eq_zero hψ0, rootMultiplicity_zero_map_eq_zero hχ0]
  rw [rootMultiplicity_map_eq_of_reverse_eq_comp_X_pow hr hψ0 hψ'0 hψ,
    rootMultiplicity_map_eq_of_reverse_eq_comp_X_pow hr hχ0 hχ'0 hχ, h, map_pow, div_pow]

/-- Under `reverse χ = (reverse χ') (X ^ r)` with nonzero constant coefficients,
`natDegree χ = r * natDegree χ'`. -/
theorem natDegree_eq_mul_of_reverse_eq_comp_X_pow {r : ℕ} {χ χ' : K[X]} (hχ0 : χ.coeff 0 ≠ 0)
    (hχ'0 : χ'.coeff 0 ≠ 0) (h : χ.reverse = χ'.reverse.comp (X ^ r)) :
    χ.natDegree = r * χ'.natDegree := by
  have htr : ∀ p : K[X], p.coeff 0 ≠ 0 → p.reverse.natDegree = p.natDegree := fun p hp => by
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr hp), Nat.sub_zero]
  rw [← htr χ hχ0, h, natDegree_comp, natDegree_X_pow, htr χ' hχ'0, mul_comm]

/-- Descent of the parity of the degree along `T ↦ T ^ r`. -/
theorem even_natDegree_of_reverse_eq_comp_X_pow {r : ℕ} {χ χ' : K[X]} (hχ0 : χ.coeff 0 ≠ 0)
    (hχ'0 : χ'.coeff 0 ≠ 0) (h : χ.reverse = χ'.reverse.comp (X ^ r))
    (he : Even χ'.natDegree) : Even χ.natDegree := by
  rw [natDegree_eq_mul_of_reverse_eq_comp_X_pow hχ0 hχ'0 h]
  exact he.mul_left r

/-- Descent along `T ↦ T ^ r` of the parity of the multiplicities of the square roots of `c`. -/
theorem even_rootMultiplicity_of_reverse_eq_comp_X_pow [CharZero K] [IsAlgClosed L] {c : K}
    {r : ℕ} (hr : 0 < r) {χ χ' : K[X]} (hχ0 : χ.coeff 0 ≠ 0) (hχ'0 : χ'.coeff 0 ≠ 0)
    (h : χ.reverse = χ'.reverse.comp (X ^ r))
    (he : ∀ γ' : L, γ' ^ 2 = algebraMap K L (c ^ r) →
      Even (rootMultiplicity γ' (χ'.map (algebraMap K L)))) :
    ∀ γ : L, γ ^ 2 = algebraMap K L c → Even (rootMultiplicity γ (χ.map (algebraMap K L))) := by
  intro γ hγ
  rw [rootMultiplicity_map_eq_of_reverse_eq_comp_X_pow hr hχ0 hχ'0 h]
  exact he _ (by rw [← pow_mul, mul_comm, pow_mul, hγ, map_pow])

/-- The dual relation is multiplicative. -/
theorem IsCharpolyDual.mul {c : K} {χ₁ χ₂ ψ₁ ψ₂ : K[X]} (hχ₁ : χ₁ ≠ 0) (hχ₂ : χ₂ ≠ 0)
    (h₁ : IsCharpolyDual L c χ₁ ψ₁) (h₂ : IsCharpolyDual L c χ₂ ψ₂) :
    IsCharpolyDual L c (χ₁ * χ₂) (ψ₁ * ψ₂) := by
  rw [IsCharpolyDual] at h₁ h₂ ⊢
  rw [Polynomial.map_mul, Polynomial.map_mul, roots_mul, Multiset.map_add, Multiset.prod_add, h₁,
    h₂]
  exact mul_ne_zero ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hχ₁)
    ((Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hχ₂)

/-- The dual relation is stable under finite products. -/
theorem IsCharpolyDual.prod {ι : Type*} {c : K} {s : Finset ι} {χ ψ : ι → K[X]}
    (hχ : ∀ j ∈ s, χ j ≠ 0) (h : ∀ j ∈ s, IsCharpolyDual L c (χ j) (ψ j)) :
    IsCharpolyDual L c (∏ j ∈ s, χ j) (∏ j ∈ s, ψ j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsCharpolyDual]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine IsCharpolyDual.mul (hχ a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero_iff.mpr fun j hj => hχ j (Finset.mem_insert_of_mem hj))
      (h a (Finset.mem_insert_self a s)) (ih (fun j hj => hχ j (Finset.mem_insert_of_mem hj))
        fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The degree of a product of polynomials of even degree is even. -/
theorem even_natDegree_prod {ι : Type*} {s : Finset ι} {χ : ι → K[X]} (hχ : ∀ j ∈ s, χ j ≠ 0)
    (he : ∀ j ∈ s, Even (χ j).natDegree) : Even (∏ j ∈ s, χ j).natDegree := by
  rw [natDegree_prod _ _ hχ]
  exact Finset.even_sum _ he

/-- A root of even multiplicity in every factor has even multiplicity in the product. -/
theorem even_rootMultiplicity_prod {ι : Type*} {s : Finset ι} {χ : ι → K[X]}
    (hχ : ∀ j ∈ s, χ j ≠ 0) (γ : L)
    (he : ∀ j ∈ s, Even (rootMultiplicity γ ((χ j).map (algebraMap K L)))) :
    Even (rootMultiplicity γ ((∏ j ∈ s, χ j).map (algebraMap K L))) := by
  classical
  have hχ' : ∀ j ∈ s, (χ j).map (algebraMap K L) ≠ 0 := fun j hj =>
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr (hχ j hj)
  rw [Polynomial.map_prod, ← count_roots, roots_prod _ _ (Finset.prod_ne_zero_iff.mpr hχ'),
    Multiset.count_bind]
  exact Finset.even_sum (s := s) (fun j => ((χ j).map (algebraMap K L)).roots.count γ)
    fun j hj => by rw [count_roots]; exact he j hj

/-- The square roots of `c` have even multiplicity in a product if they do in every factor. -/
theorem even_rootMultiplicity_prod_of_sq_eq {ι : Type*} {c : K} {s : Finset ι} {χ : ι → K[X]}
    (hχ : ∀ j ∈ s, χ j ≠ 0)
    (he : ∀ j ∈ s, ∀ γ : L, γ ^ 2 = algebraMap K L c →
      Even (rootMultiplicity γ ((χ j).map (algebraMap K L)))) :
    ∀ γ : L, γ ^ 2 = algebraMap K L c →
      Even (rootMultiplicity γ ((∏ j ∈ s, χ j).map (algebraMap K L))) :=
  fun γ hγ => even_rootMultiplicity_prod hχ γ fun j hj => he j hj γ hγ

end

end Weil.Polynomial

public section

namespace LinearMap.IsFrobeniusDuality

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {B : V →ₗ[K] W →ₗ[K] K} {f : Module.End K V} {g : Module.End K W} {c : Kˣ}

/-- The characteristic polynomial of `g` is `c`-dual to that of `f`, for a `c`-duality. -/
theorem isCharpolyDual [FiniteDimensional K V] [FiniteDimensional K W]
    (h : B.IsFrobeniusDuality f g c) (L : Type*) [Field L] [Algebra K L] [IsAlgClosed L] :
    Weil.Polynomial.IsCharpolyDual L (c : K) f.charpoly g.charpoly :=
  h.charpoly_map_eq_prod_roots L

end LinearMap.IsFrobeniusDuality

end
