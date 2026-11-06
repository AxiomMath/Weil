module

public import WeilFrontier.Defs.LinearAlgebra.PerfectPairing.Basic
public import Weil.Attr
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The endomorphism of a twisted-equivariant duality is invertible

Let `B : V × W → K` be a `c`-duality for `(f, g)`, i.e. both maps `V → W*` and `W → V*` induced
by `B` are injective and `B (f x) (g y) = c * B x y`. If `f x = 0`, then
`c * B x y = B (f x) (g y) = 0` for every `y`, so `B x = 0` since `c ≠ 0`, hence `x = 0`. Thus `f`
is injective, and when `V` is finite-dimensional `f` is invertible.

## Main results

* `LinearMap.IsFrobeniusDuality.injective_left_endomorphism`: `f` is injective.
* `LinearMap.IsFrobeniusDuality.isUnit_left`: in finite dimension `f` is a unit of `Module.End K V`.
* `LinearMap.IsFrobeniusDuality.bijective_left`: in finite dimension `f` is bijective.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

public section

namespace LinearMap.IsFrobeniusDuality

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {B : V →ₗ[K] W →ₗ[K] K} {f : Module.End K V} {g : Module.End K W} {c : Kˣ}

/-- The endomorphism `f` of a `c`-duality for `(f, g)` is injective. -/
theorem injective_left_endomorphism (h : B.IsFrobeniusDuality f g c) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine h.eq_zero_of_forall_left fun y => ?_
  have := h.map_map x y
  rw [hx, map_zero, LinearMap.zero_apply] at this
  exact (mul_eq_zero.mp this.symm).resolve_left c.ne_zero

/-- In finite dimension, the endomorphism `f` of a `c`-duality for `(f, g)` is invertible. -/
@[weil "lem_fk401_duality_endomorphism_invertible"]
theorem isUnit_left [FiniteDimensional K V] (h : B.IsFrobeniusDuality f g c) : IsUnit f :=
  (Module.End.isUnit_iff f).mpr ⟨h.injective_left_endomorphism,
    LinearMap.injective_iff_surjective.mp h.injective_left_endomorphism⟩

/-- In finite dimension, the endomorphism `f` of a `c`-duality for `(f, g)` is bijective. -/
theorem bijective_left [FiniteDimensional K V] (h : B.IsFrobeniusDuality f g c) :
    Function.Bijective f :=
  (Module.End.isUnit_iff f).mp h.isUnit_left

end LinearMap.IsFrobeniusDuality

/-! ### Both sides of a twisted-equivariant duality have the same dimension -/

/-!
# Both sides of a twisted-equivariant duality have the same dimension

If `B : V × W → K` is a `c`-duality for `(f, g)` (`LinearMap.IsFrobeniusDuality`) and `V` is
finite-dimensional, then `W` is finite-dimensional and `dim V = dim W`: the injections
`V → W*` and `W → V*` give `dim V ≤ dim W* = dim W` and `dim W ≤ dim V* = dim V`.

## Main results

* `LinearMap.IsFrobeniusDuality.finiteDimensional_right`: `W` is finite-dimensional.
* `LinearMap.IsFrobeniusDuality.finrank_eq`: `finrank K V = finrank K W`.

## Implementation notes

Only finite-dimensionality of `V` is assumed; that of `W` follows from the injection `W → V*`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

public section

namespace LinearMap.IsFrobeniusDuality

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {B : V →ₗ[K] W →ₗ[K] K} {f : Module.End K V} {g : Module.End K W} {c : Kˣ}

/-- The right-hand space of a `c`-duality with finite-dimensional left-hand space is
finite-dimensional. -/
theorem finiteDimensional_right [FiniteDimensional K V] (h : B.IsFrobeniusDuality f g c) :
    FiniteDimensional K W :=
  Module.Finite.of_injective B.flip h.injective_right

/-- Both sides of a `c`-duality have the same dimension. -/
@[weil "lem_fk401_duality_dimension_equal"]
theorem finrank_eq [FiniteDimensional K V] (h : B.IsFrobeniusDuality f g c) :
    Module.finrank K V = Module.finrank K W := by
  have := h.finiteDimensional_right
  exact le_antisymm
    ((LinearMap.finrank_le_finrank_of_injective h.injective_left).trans
      (Subspace.dual_finrank_eq).le)
    ((LinearMap.finrank_le_finrank_of_injective h.injective_right).trans
      (Subspace.dual_finrank_eq).le)

end LinearMap.IsFrobeniusDuality

/-! ### Characteristic polynomials of the two sides of a twisted-equivariant duality -/

/-!
# Characteristic polynomials of the two sides of a twisted-equivariant duality

Let `B : V × W → K` be a `c`-duality for `(f, g)` (`LinearMap.IsFrobeniusDuality`), with `V`
finite-dimensional, and let `L` be an algebraically closed extension of `K`. If
`λ₁, …, λ_b ∈ L` are the eigenvalues of `f` (with multiplicity), then all `λᵢ` are nonzero and
the characteristic polynomial of `g` is `∏ᵢ (T - c / λᵢ)`.

Choosing a basis `(eᵢ)` of `V` and the basis `(e'ⱼ)` of `W` dual to it under `B`, the
equation `B (f x) (g y) = c * B x y` reads `Aᵀ D = c` for the matrices `A` of `f` and `D` of `g`.
For `t ≠ 0` one has `Aᵀ (t - D) = -t (c / t - Aᵀ)`; taking determinants and comparing the
values at the infinitely many nonzero `t ∈ L` gives the claim.

## Main results

* `Matrix.charpoly_eq_prod_roots_of_transpose_mul_eq`: if `Mᵀ N = c • 1` with `c ≠ 0` over an
  algebraically closed field, then `N.charpoly = ∏_{μ} (X - c / μ)`, `μ` running over the roots of
  `M.charpoly` with multiplicity.
* `LinearMap.IsFrobeniusDuality.charpoly_map_eq_prod_roots`: the characteristic polynomial of `g`
  over `L` is `∏ (X - c / λ)`, `λ` running over the eigenvalues of `f` in `L` with multiplicity.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

public section

open Polynomial

/-- If `Mᵀ * N = c • 1` with `c ≠ 0` over an algebraically closed field, then the characteristic
polynomial of `N` is `∏ (X - c / μ)`, `μ` running over the roots of `M.charpoly` with
multiplicity. -/
theorem Matrix.charpoly_eq_prod_roots_of_transpose_mul_eq {n L : Type*} [Fintype n] [DecidableEq n]
    [Field L] [IsAlgClosed L] {M N : Matrix n n L} {c : L} (hc : c ≠ 0)
    (h : M.transpose * N = c • 1) :
    N.charpoly = (M.charpoly.roots.map fun μ => X - C (c / μ)).prod := by
  have hdet : M.det * N.det = c ^ Fintype.card n := by
    rw [← Matrix.det_transpose M, ← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  have hM : M.det ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hdet; exact pow_ne_zero _ hc hdet.symm
  have hroots : M.charpoly.roots.prod = M.det := (Matrix.det_eq_prod_roots_charpoly M).symm
  have hcard : M.charpoly.roots.card = Fintype.card n := by
    rw [(splits_iff_card_roots.mp (IsAlgClosed.splits _)), Matrix.charpoly_natDegree_eq_dim]
  have hne : ∀ μ ∈ M.charpoly.roots, μ ≠ 0 := fun μ hμ h0 => by
    rw [← hroots] at hM; exact hM (Multiset.prod_eq_zero (h0 ▸ hμ))
  apply eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := {t : L | t ≠ 0}) ?_ ?_
  · intro t ht
    simp only [Set.mem_ofPred_eq] at ht ⊢
    have key : M.transpose * (Matrix.scalar n t - N) =
        (-t) • (Matrix.scalar n (c / t) - M.transpose) := by
      rw [Matrix.mul_sub, h, smul_sub, Matrix.scalar_apply, Matrix.scalar_apply]
      ext i j
      simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.one_apply,
        Matrix.diagonal_apply, Matrix.transpose_apply, smul_eq_mul]
      split_ifs <;> field_simp <;> ring
    have hd := congrArg Matrix.det key
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_transpose, ← Matrix.eval_charpoly,
      ← Matrix.eval_charpoly, Matrix.charpoly_transpose,
      (IsAlgClosed.splits M.charpoly).eval_eq_prod_roots_of_monic (Matrix.charpoly_monic M)] at hd
    rw [eval_multiset_prod, Multiset.map_map]
    apply mul_left_cancel₀ hM
    rw [hd, ← hroots, ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const',
      ← Multiset.prod_map_mul,
      show M.charpoly.roots.prod = (M.charpoly.roots.map id).prod by rw [Multiset.map_id],
      ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun μ hμ => ?_)
    have := hne μ hμ
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, id]
    field_simp
    ring
  · exact Set.infinite_of_finite_compl (by simp)

namespace LinearMap.IsFrobeniusDuality

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {B : V →ₗ[K] W →ₗ[K] K} {f : Module.End K V} {g : Module.End K W} {c : Kˣ}

/-- **Eigenvalues of the two sides of a `c`-duality.** If `B` is a `c`-duality for `(f, g)` with
`V` finite-dimensional and `L` is an algebraically closed extension of `K`, then the
characteristic polynomial of `g` over `L` is `∏ (X - c / λ)`, `λ` running over the eigenvalues of
`f` in `L` (the roots of its characteristic polynomial) with multiplicity. -/
@[weil "lem_fk401_duality_charpoly_inverse_roots"]
theorem charpoly_map_eq_prod_roots [FiniteDimensional K V] [FiniteDimensional K W]
    (h : B.IsFrobeniusDuality f g c) (L : Type*) [Field L] [Algebra K L] [IsAlgClosed L] :
    g.charpoly.map (algebraMap K L) =
      ((f.charpoly.map (algebraMap K L)).roots.map
        fun μ => X - C (algebraMap K L c / μ)).prod := by
  classical
  have := h.isPerfPair
  let b := Module.finBasis K V
  let δ : W ≃ₗ[K] Module.Dual K V :=
    LinearEquiv.ofBijective B.flip (LinearMap.IsPerfPair.bijective_right B)
  let e : Module.Basis (Fin (Module.finrank K V)) K W := b.dualBasis.map δ.symm
  have hB : LinearMap.toMatrix₂ b e B = 1 := by
    ext i j
    have : B (b i) (e j) = b.dualBasis j (b i) := by
      change δ (e j) (b i) = _
      simp [e]
    rw [LinearMap.toMatrix₂_apply, this, Module.Basis.dualBasis_apply_self, Matrix.one_apply]
  have hcompl : B.compl₁₂ f g = c • B := by
    ext x y
    simp [h.map_map, Units.smul_def]
  have hAD : (LinearMap.toMatrix b b f).transpose * LinearMap.toMatrix e e g = (c : K) • 1 := by
    have := LinearMap.toMatrix₂_compl₁₂ b e b e B f g
    rw [hcompl, hB, Matrix.mul_one, Units.smul_def, LinearEquiv.map_smul, hB] at this
    exact this.symm
  have hc : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).mpr c.ne_zero
  rw [← LinearMap.charpoly_toMatrix g e, ← LinearMap.charpoly_toMatrix f b,
    ← Matrix.charpoly_map, ← Matrix.charpoly_map]
  refine Matrix.charpoly_eq_prod_roots_of_transpose_mul_eq hc ?_
  rw [← Matrix.transpose_map, ← Matrix.map_mul, hAD, Matrix.map_smul',
    Matrix.map_one _ (map_zero _) (map_one _)]
  exact map_mul _

end LinearMap.IsFrobeniusDuality
