module

public import Weil.Attr
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The `ℓ`-adic rank of an inverse system of `ℤ_ℓ`-modules

Let `ℓ` be a prime and let `A = (A_m)_{m ∈ ℕ}` be an inverse system of `ℤ_ℓ`-modules. Its
*rational limit* is `ℚ_ℓ ⊗_{ℤ_ℓ} lim_m A_m`; for `A_m = Hⁱ(X, ℤ/ℓ^{m+1})` this is the
`ℓ`-adic cohomology `Hⁱ(X, ℚ_ℓ)`.

This file proves two facts about the rational limit.

* **Transport.** If the levels of two inverse systems are isomorphic as abelian groups,
  compatibly with the transition maps, and the levels of the first are killed by `ℓ^{m+1}`, then
  the rational limits are isomorphic. An additive map out of a `ℤ_ℓ`-module killed by `ℓ^N` is
  `ℤ_ℓ`-linear, because `c ∈ ℤ_ℓ` acts there as any integer congruent to `c` modulo `ℓ^N`.
  An inverse system of abelian groups whose `m`-th level is killed by `ℓ^{m+1}` is an inverse
  system of `ℤ_ℓ`-modules in a canonical way.
* **Rank.** Let `H`, `H'` be finitely generated abelian groups, and suppose that there are exact
  sequences `0 → H/ℓ^{m+1}H → A_m → H'[ℓ^{m+1}]`, compatible with the transition maps, where the
  transition maps act on `H/ℓ^{m+1}H` as the quotient maps and on the `ℓ`-power torsion of `H'`
  as multiplication by `ℓ` (the shape of the Bockstein sequences of a space with coefficients
  `ℤ/ℓ^{m+1}`). Then `dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim A = rank_ℤ H`.

## Main definitions

* `PadicInt.rationalLimit`: `ℚ_ℓ ⊗_{ℤ_ℓ} lim A` for `A : ℕᵒᵖ ⥤ ModuleCat ℤ_[ℓ]`.
* `PadicInt.moduleOfTorsion`: the `ℤ_ℓ`-module structure of an abelian group killed by `ℓ^N`.
* `PadicInt.inverseSystemOfTorsion`: an inverse system of abelian groups whose `m`-th level is
  killed by `ℓ^{m+1}`, as an inverse system of `ℤ_ℓ`-modules.

## Main results

* `PadicInt.map_smul_of_pow_smul_eq_zero`: an additive map out of a `ℤ_ℓ`-module killed by `ℓ^N`
  is `ℤ_ℓ`-linear.
* `PadicInt.rationalLimitIsoOfAddEquiv`, `PadicInt.finrank_rationalLimit_eq_of_addEquiv`: the
  transport of the rational limit along levelwise additive isomorphisms.
* `PadicInt.finrank_rationalLimit`: `dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim A = rank_{ℤ_ℓ} lim A`.
* `PadicInt.finrank_rationalLimit_eq_finrank_of_bockstein`: the rank of the rational limit of a
  system of Bockstein shape is the rank of `H`.

## Implementation notes

The rational limit is literally the construction used for the rational `ℓ`-adic cohomology of
`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomology`: the limit in
`ModuleCat ℤ_[ℓ]` of a functor `ℕᵒᵖ ⥤ ModuleCat ℤ_[ℓ]`, followed by
`ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])`. The results are stated for an arbitrary
`HasLimit` instance, so that they apply to it whichever instance the caller has.

In the rank statement, the exactness at `H'[ℓ^{m+1}]` (surjectivity onto the torsion) is not
needed and not assumed: only `ker (A_m → H') = H/ℓ^{m+1}H` and that the image is killed by
`ℓ^{m+1}` enter. The limit `lim H'[ℓ^{m+1}]` along multiplication by `ℓ` vanishes because the
`ℓ`-power torsion of a finitely generated abelian group has bounded exponent; hence
`lim A = lim H/ℓ^{m+1}H`, which contains `ℤ_ℓ^r` (`r = rank H`) with cokernel killed by the
order of the torsion of `H`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v

/-! ### Rank of a module containing a free module with torsion cokernel -/

/-- Over a domain, a module containing `Rⁿ` with cokernel killed by a nonzero element has rank
`n`. -/
theorem Module.finrank_eq_of_injective_of_smul_mem_range {R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] {n : ℕ} (f : (Fin n → R) →ₗ[R] M)
    (hf : Function.Injective f) {d : R} (hd : d ≠ 0) (hM : ∀ x : M, ∃ c, d • x = f c) :
    Module.finrank R M = n := by
  have h1 : Module.rank R (M ⧸ LinearMap.range f) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨c, hc⟩ := hM x
    refine ⟨d, hd, ?_⟩
    rw [← Submodule.Quotient.mk_smul, hc, Submodule.Quotient.mk_eq_zero]
    exact ⟨c, rfl⟩
  have h2 : Module.rank R (LinearMap.range f) = n := by
    have := (LinearEquiv.ofInjective f hf).lift_rank_eq
    rwa [rank_fin_fun, Cardinal.lift_natCast, eq_comm, Cardinal.lift_eq_nat_iff] at this
  have := rank_quotient_add_rank_of_isDomain (LinearMap.range f)
  rw [h1, h2, zero_add] at this
  exact Module.finrank_eq_of_rank_eq this.symm

/-! ### Finitely generated abelian groups -/

namespace AddCommGroup

/-- The torsion subgroup of a finitely generated abelian group is finite. -/
theorem finite_torsion (G : Type*) [AddCommGroup G] [Module.Finite ℤ G] :
    Finite (Submodule.torsion ℤ G) :=
  Module.finite_of_fg_torsion _ Submodule.torsion_isTorsion

/-- A finitely generated abelian group `H` of rank `n` has elements `e₁, …, eₙ` and a linear map
`π : H → ℤⁿ` with `π (∑ vₖ eₖ) = v`, and a positive integer `d` with `d h = d ∑ π(h)ₖ eₖ`:
lift a basis of `H` modulo torsion, and take for `d` the order of the torsion subgroup. -/
theorem exists_basis_mod_torsion (H : Type*) [AddCommGroup H] [Module.Finite ℤ H] :
    ∃ (n : ℕ) (e : Fin n → H) (π : H →ₗ[ℤ] (Fin n → ℤ)) (d : ℕ), d ≠ 0 ∧
      (∀ v, π (∑ k, v k • e k) = v) ∧ (∀ h, d • h = d • ∑ k, π h k • e k) ∧
      Module.finrank ℤ H = n := by
  set T := Submodule.torsion ℤ H
  have : Module.Free ℤ (H ⧸ T) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ (H ⧸ T)
  choose e he using fun k => Submodule.mkQ_surjective T (b k)
  let π : H →ₗ[ℤ] (Fin _ → ℤ) := b.equivFun.toLinearMap ∘ₗ T.mkQ
  have := finite_torsion H
  have hmk : ∀ v : Fin _ → ℤ, T.mkQ (∑ k, v k • e k) = b.equivFun.symm v := by
    intro v
    simp [map_sum, he, Module.Basis.equivFun_symm_apply]
  have hπ : ∀ v, π (∑ k, v k • e k) = v := by
    intro v
    simp only [π, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hmk,
      LinearEquiv.apply_symm_apply]
  have hT : ∀ h, h - ∑ k, π h k • e k ∈ T := by
    intro h
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hmk, sub_eq_zero]
    simp [π]
  have hd : ∀ h, Nat.card T • h = Nat.card T • ∑ k, π h k • e k := by
    intro h
    rw [← sub_eq_zero, ← smul_sub]
    exact congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨_, hT h⟩ : T)))
  refine ⟨_, e, π, Nat.card T, Nat.card_pos.ne', hπ, hd, ?_⟩
  refine Module.finrank_eq_of_injective_of_smul_mem_range (Fintype.linearCombination ℤ e) ?_
    (d := (Nat.card T : ℤ)) (by exact_mod_cast Nat.card_pos.ne')
    fun h => ⟨(Nat.card T : ℤ) • π h, ?_⟩
  · intro v w hvw
    rw [← hπ v, ← hπ w]
    simp only [Fintype.linearCombination_apply] at hvw
    rw [hvw]
  · rw [map_smul, Fintype.linearCombination_apply, natCast_zsmul, natCast_zsmul, hd]

/-- In a finitely generated abelian group, a sequence `tₘ` with `tₘ = ℓ tₘ₊₁` and
`ℓ^{m+1} tₘ = 0` is zero: the limit of the `ℓ^{m+1}`-torsion along multiplication by `ℓ`
vanishes. -/
theorem eq_zero_of_eq_smul_succ {G : Type*} [AddCommGroup G] [Module.Finite ℤ G] {ℓ : ℕ}
    (hℓ : ℓ.Prime) (t : ℕ → G) (ht : ∀ m, t m = ℓ • t (m + 1))
    (htor : ∀ m, ℓ ^ (m + 1) • t m = 0) (m : ℕ) : t m = 0 := by
  have := finite_torsion G
  set D := Nat.card (Submodule.torsion ℤ G)
  have hpow : ∀ k, t m = ℓ ^ k • t (m + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [ih, ht (m + k), ← mul_nsmul', ← pow_succ, ← add_assoc]
  set x := t (m + D)
  have hx : x ∈ Submodule.torsion ℤ G := by
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨(ℓ : ℤ) ^ (m + D + 1), mem_nonZeroDivisors_of_ne_zero
      (pow_ne_zero _ (by exact_mod_cast hℓ.ne_zero))⟩, ?_⟩
    change ((ℓ : ℤ) ^ (m + D + 1)) • x = 0
    rw [← Nat.cast_pow, natCast_zsmul]
    exact htor _
  have hD : D • x = 0 := congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨x, hx⟩ :
    Submodule.torsion ℤ G)))
  have hDpos : 0 < D := Nat.card_pos
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hℓ).1 (addOrderOf_dvd_of_nsmul_eq_zero (htor (m + D)))
  have hjD : ℓ ^ j ∣ D := hj ▸ addOrderOf_dvd_of_nsmul_eq_zero hD
  have hjlt : j < D := by
    have h1 : ℓ ^ j ≤ D := Nat.le_of_dvd hDpos hjD
    have h2 : D < ℓ ^ D := Nat.lt_pow_self hℓ.one_lt
    exact (Nat.pow_lt_pow_iff_right hℓ.one_lt).1 (lt_of_le_of_lt h1 h2)
  rw [hpow D]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (hj ▸ pow_dvd_pow ℓ hjlt.le)

end AddCommGroup

namespace PadicInt

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-! ### `ℤ_ℓ` acting on `ℓ^N`-torsion -/

/-- Every `ℓ`-adic integer is congruent to an integer modulo `ℓ^N`. -/
theorem exists_eq_intCast_add_pow_mul (c : ℤ_[ℓ]) (N : ℕ) :
    ∃ (z : ℤ) (w : ℤ_[ℓ]), c = z + (ℓ : ℤ_[ℓ]) ^ N * w := by
  have : NeZero (ℓ ^ N) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  have hmem : c - ((toZModPow N c).val : ℤ_[ℓ]) ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ N} := by
    rw [← ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨(toZModPow N c).val, w, ?_⟩
  rw [mul_comm, hw]
  push_cast
  ring

/-- For a `ℤ_ℓ`-module, the action of `ℓ^N ∈ ℤ_ℓ` is the `N`-fold multiple by `ℓ`. -/
theorem pow_smul_eq_nsmul {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] (N : ℕ) (x : M) :
    (ℓ : ℤ_[ℓ]) ^ N • x = ℓ ^ N • x := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- On an element killed by `ℓ^N`, an `ℓ`-adic integer `c ≡ z (mod ℓ^N)` acts as the integer
`z`. -/
theorem smul_eq_zsmul_of_eq_add_pow_mul {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    {c : ℤ_[ℓ]} {z : ℤ} {w : ℤ_[ℓ]} {N : ℕ} (hc : c = z + (ℓ : ℤ_[ℓ]) ^ N * w) {x : M}
    (hx : ℓ ^ N • x = 0) : c • x = z • x := by
  rw [← pow_smul_eq_nsmul] at hx
  rw [hc, add_smul, mul_comm, mul_smul, hx, smul_zero, add_zero, Int.cast_smul_eq_zsmul]

/-- **An additive map out of a `ℤ_ℓ`-module killed by `ℓ^N` is `ℤ_ℓ`-linear.** -/
theorem map_smul_of_pow_smul_eq_zero {M N : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    [AddCommGroup N] [Module ℤ_[ℓ] N] (f : M →+ N) {K : ℕ} (hM : ∀ x : M, ℓ ^ K • x = 0)
    (c : ℤ_[ℓ]) (x : M) : f (c • x) = c • f x := by
  obtain ⟨z, w, hc⟩ := exists_eq_intCast_add_pow_mul c K
  have hfx : ℓ ^ K • f x = 0 := by rw [← map_nsmul, hM x, map_zero]
  rw [smul_eq_zsmul_of_eq_add_pow_mul hc (hM x), smul_eq_zsmul_of_eq_add_pow_mul hc hfx,
    map_zsmul]

/-- An additive map out of a `ℤ_ℓ`-module killed by `ℓ^K`, as a `ℤ_ℓ`-linear map. -/
def linearMapOfTorsion {M N : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    [AddCommGroup N] [Module ℤ_[ℓ] N] (f : M →+ N) {K : ℕ} (hM : ∀ x : M, ℓ ^ K • x = 0) :
    M →ₗ[ℤ_[ℓ]] N :=
  { f with map_smul' := map_smul_of_pow_smul_eq_zero f hM }

@[simp]
theorem linearMapOfTorsion_apply {M N : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    [AddCommGroup N] [Module ℤ_[ℓ] N] (f : M →+ N) {K : ℕ} (hM : ∀ x : M, ℓ ^ K • x = 0)
    (x : M) : linearMapOfTorsion f hM x = f x :=
  rfl

/-- An additive isomorphism out of a `ℤ_ℓ`-module killed by `ℓ^K`, as a `ℤ_ℓ`-linear
isomorphism. -/
def linearEquivOfTorsion {M N : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    [AddCommGroup N] [Module ℤ_[ℓ] N] (e : M ≃+ N) {K : ℕ} (hM : ∀ x : M, ℓ ^ K • x = 0) :
    M ≃ₗ[ℤ_[ℓ]] N :=
  e.toLinearEquiv (map_smul_of_pow_smul_eq_zero e.toAddMonoidHom hM)

@[simp]
theorem linearEquivOfTorsion_apply {M N : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    [AddCommGroup N] [Module ℤ_[ℓ] N] (e : M ≃+ N) {K : ℕ} (hM : ∀ x : M, ℓ ^ K • x = 0)
    (x : M) : linearEquivOfTorsion e hM x = e x :=
  rfl

/-- The canonical `ℤ_ℓ`-module structure of an abelian group killed by `ℓ^N`: through
`ℤ_ℓ → ℤ/ℓ^N`. -/
abbrev moduleOfTorsion {G : Type*} [AddCommGroup G] (N : ℕ) (h : ∀ x : G, ℓ ^ N • x = 0) :
    Module ℤ_[ℓ] G :=
  haveI : NeZero (ℓ ^ N) := ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  letI := AddCommGroup.zmodModule h
  Module.compHom G (toZModPow N)

/-! ### Inverse systems and their rational limits -/

/-- An inverse system of abelian groups whose `m`-th level is killed by `ℓ^{m+1}`, as an inverse
system of `ℤ_ℓ`-modules: each level with its canonical `ℤ_ℓ`-module structure
(`PadicInt.moduleOfTorsion`), the transition maps being those of `G`. -/
def inverseSystemOfTorsion (G : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    (hG : ∀ (m : ℕ) (x : G.obj (op m)), ℓ ^ (m + 1) • x = 0) : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ] :=
  letI (m : ℕ) : Module ℤ_[ℓ] (G.obj (op m)) := moduleOfTorsion (m + 1) (hG m)
  Functor.ofOpSequence (X := fun m => ModuleCat.of ℤ_[ℓ] (G.obj (op m)))
    (fun m => ModuleCat.ofHom
      (linearMapOfTorsion (G.map (homOfLE (m.le_add_right 1)).op).hom (hG (m + 1))))

/-- The `m`-th level of `PadicInt.inverseSystemOfTorsion G hG` is the `m`-th level of `G`. -/
theorem inverseSystemOfTorsion_obj (G : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    (hG : ∀ (m : ℕ) (x : G.obj (op m)), ℓ ^ (m + 1) • x = 0) (m : ℕ) :
    ((inverseSystemOfTorsion G hG).obj (op m) : Type v) = G.obj (op m) :=
  rfl

/-- The transition maps of `PadicInt.inverseSystemOfTorsion G hG` are those of `G`. -/
theorem inverseSystemOfTorsion_map_succ_apply (G : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    (hG : ∀ (m : ℕ) (x : G.obj (op m)), ℓ ^ (m + 1) • x = 0) (m : ℕ)
    (x : (inverseSystemOfTorsion G hG).obj (op (m + 1))) :
    (inverseSystemOfTorsion G hG).map (homOfLE (m.le_add_right 1)).op x =
      G.map (homOfLE (m.le_add_right 1)).op (show G.obj (op (m + 1)) from x) := by
  simp only [inverseSystemOfTorsion, Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- **The rational limit** `ℚ_ℓ ⊗_{ℤ_ℓ} lim_m A_m` of an inverse system of `ℤ_ℓ`-modules: the
limit in `ModuleCat ℤ_[ℓ]` followed by extension of scalars along `ℤ_ℓ → ℚ_ℓ`, exactly as in
`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomology`. -/
abbrev rationalLimit (A : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) [HasLimit A] : ModuleCat.{v} ℚ_[ℓ] :=
  (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj (limit A)

/-- `dim_{ℚ_ℓ} ℚ_ℓ ⊗_{ℤ_ℓ} M = rank_{ℤ_ℓ} M`. -/
theorem finrank_extendScalars (M : ModuleCat.{v} ℤ_[ℓ]) :
    Module.finrank ℚ_[ℓ] ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj M) =
      Module.finrank ℤ_[ℓ] M := by
  change Module.finrank ℚ_[ℓ] (TensorProduct ℤ_[ℓ] ℚ_[ℓ] M) = _
  rw [IsFractionRing.finrank_right_eq (R := ℤ_[ℓ]) (S := ℚ_[ℓ])]
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] M 1) :=
    (isLocalizedModule_iff_isBaseChange _ ℚ_[ℓ] _).2 (TensorProduct.isBaseChange _ _ _)
  exact IsLocalizedModule.finrank_eq _ (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] M 1) le_rfl

/-- `dim_{ℚ_ℓ} ℚ_ℓ ⊗ lim A = rank_{ℤ_ℓ} lim A`. -/
theorem finrank_rationalLimit (A : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) [HasLimit A] :
    Module.finrank ℚ_[ℓ] (rationalLimit A) = Module.finrank ℤ_[ℓ] (limit A : ModuleCat.{v} ℤ_[ℓ]) :=
  finrank_extendScalars _

/-! ### Transport along levelwise additive isomorphisms -/

section Transport

/-- Levelwise additive isomorphisms commuting with the transition maps, out of an inverse system
of `ℤ_ℓ`-modules whose `m`-th level is killed by `ℓ^{m+1}`, form an isomorphism of inverse
systems of `ℤ_ℓ`-modules. -/
def inverseSystemIsoOfAddEquiv (A A' : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])
    (e : ∀ m : ℕ, A.obj (op m) ≃+ A'.obj (op m))
    (hA : ∀ (m : ℕ) (x : A.obj (op m)), ℓ ^ (m + 1) • x = 0)
    (he : ∀ (m : ℕ) (x : A.obj (op (m + 1))),
      e m (A.map (homOfLE (m.le_add_right 1)).op x) =
        A'.map (homOfLE (m.le_add_right 1)).op (e (m + 1) x)) : A ≅ A' :=
  NatIso.ofComponents
    (fun j => (linearEquivOfTorsion (e j.unop) (hA j.unop)).toModuleIso)
    (fun {_ _} f => (NatTrans.ofOpSequence (F := A) (G := A')
        (fun m => ModuleCat.ofHom (linearEquivOfTorsion (e m) (hA m)).toLinearMap)
        (fun m => by
          ext x
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
            LinearEquiv.coe_coe, linearEquivOfTorsion_apply]
          exact he m x)).naturality f)

/-- **Transport.** Levelwise additive isomorphisms commuting with the transition maps, out of an
inverse system of `ℤ_ℓ`-modules whose `m`-th level is killed by `ℓ^{m+1}`, induce an
isomorphism of the rational limits. -/
def rationalLimitIsoOfAddEquiv (A A' : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])
    (e : ∀ m : ℕ, A.obj (op m) ≃+ A'.obj (op m))
    (hA : ∀ (m : ℕ) (x : A.obj (op m)), ℓ ^ (m + 1) • x = 0)
    (he : ∀ (m : ℕ) (x : A.obj (op (m + 1))),
      e m (A.map (homOfLE (m.le_add_right 1)).op x) =
        A'.map (homOfLE (m.le_add_right 1)).op (e (m + 1) x))
    [HasLimit A] [HasLimit A'] : rationalLimit A ≅ rationalLimit A' :=
  (ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).mapIso
    (HasLimit.isoOfNatIso (inverseSystemIsoOfAddEquiv A A' e hA he))

/-- **Transport.** Under levelwise additive isomorphisms commuting with the transition maps, out
of an inverse system whose `m`-th level is killed by `ℓ^{m+1}`, the rational limits have the
same dimension. -/
theorem finrank_rationalLimit_eq_of_addEquiv (A A' : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])
    (e : ∀ m : ℕ, A.obj (op m) ≃+ A'.obj (op m))
    (hA : ∀ (m : ℕ) (x : A.obj (op m)), ℓ ^ (m + 1) • x = 0)
    (he : ∀ (m : ℕ) (x : A.obj (op (m + 1))),
      e m (A.map (homOfLE (m.le_add_right 1)).op x) =
        A'.map (homOfLE (m.le_add_right 1)).op (e (m + 1) x))
    [HasLimit A] [HasLimit A'] :
    Module.finrank ℚ_[ℓ] (rationalLimit A) = Module.finrank ℚ_[ℓ] (rationalLimit A') :=
  (rationalLimitIsoOfAddEquiv A A' e hA he).toLinearEquiv.finrank_eq

end Transport

/-- **Transport to an inverse system of abelian groups.** Levelwise additive isomorphisms from
an inverse system of `ℤ_ℓ`-modules whose `m`-th level is killed by `ℓ^{m+1}` to an inverse
system of abelian groups, commuting with the transition maps, induce an isomorphism of the
rational limits, the abelian groups carrying their canonical `ℤ_ℓ`-module structure. -/
def rationalLimitIsoOfAddEquivOfTorsion (A : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])
    (G : ℕᵒᵖ ⥤ AddCommGrpCat.{v}) (hG : ∀ (m : ℕ) (x : G.obj (op m)), ℓ ^ (m + 1) • x = 0)
    (e : ∀ m : ℕ, A.obj (op m) ≃+ G.obj (op m))
    (hA : ∀ (m : ℕ) (x : A.obj (op m)), ℓ ^ (m + 1) • x = 0)
    (he : ∀ (m : ℕ) (x : A.obj (op (m + 1))),
      e m (A.map (homOfLE (m.le_add_right 1)).op x) =
        G.map (homOfLE (m.le_add_right 1)).op (e (m + 1) x))
    [HasLimit A] [HasLimit (inverseSystemOfTorsion G hG)] :
    rationalLimit A ≅ rationalLimit (inverseSystemOfTorsion G hG) :=
  rationalLimitIsoOfAddEquiv A (inverseSystemOfTorsion G hG) e hA
    (fun m x => by rw [inverseSystemOfTorsion_map_succ_apply]; exact he m x)

/-! ### The rank of a system of Bockstein shape -/

/-- An `ℓ`-adic integer divisible by every power of `ℓ` is zero. -/
theorem eq_zero_of_forall_pow_dvd {x : ℤ_[ℓ]} (hx : ∀ m : ℕ, (ℓ : ℤ_[ℓ]) ^ (m + 1) ∣ x) :
    x = 0 := by
  refine IsHausdorff.haus' (I := IsLocalRing.maximalIdeal ℤ_[ℓ]) x fun n => ?_
  simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, sub_zero,
    maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (pow_dvd_pow _ n.le_succ).trans (hx n)

/-- A sequence of integers with `zₘ₊₁ ≡ zₘ (mod ℓ^{m+1})` converges in `ℤ_ℓ`: there is
`c ∈ ℤ_ℓ` with `c ≡ zₘ (mod ℓ^{m+1})` for every `m`. -/
theorem exists_forall_eq_add_pow_mul (z : ℕ → ℤ)
    (hz : ∀ m, (ℓ : ℤ) ^ (m + 1) ∣ z (m + 1) - z m) :
    ∃ c : ℤ_[ℓ], ∀ m, ∃ w : ℤ_[ℓ], c = z m + (ℓ : ℤ_[ℓ]) ^ (m + 1) * w := by
  have hle : ∀ m n, m ≤ n → (ℓ : ℤ) ^ (m + 1) ∣ z n - z m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : z (n + 1) - z m = (z (n + 1) - z n) + (z n - z m) := by ring
      rw [this]
      exact dvd_add ((pow_dvd_pow _ (by lia)).trans (hz n)) ih
  have hcast : ∀ m n, m ≤ n → (ℓ : ℤ_[ℓ]) ^ (m + 1) ∣ (z n : ℤ_[ℓ]) - z m := by
    intro m n hmn
    have := map_dvd (Int.castRingHom ℤ_[ℓ]) (hle m n hmn)
    simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal ℤ_[ℓ])
    (M := ℤ_[ℓ]) inferInstance (f := fun m => (z m : ℤ_[ℓ])) (fun {m n} hmn => by
      simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem,
        maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rw [← neg_sub, dvd_neg]
      exact (pow_dvd_pow _ m.le_succ).trans (hcast m n hmn))
  refine ⟨L, fun m => ?_⟩
  have h1 := hL (m + 1)
  simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem,
    maximalIdeal_eq_span_p, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  have h2 := hcast m (m + 1) m.le_succ
  have : L - z m = -(((z (m + 1) : ℤ_[ℓ])) - L) + ((z (m + 1) : ℤ_[ℓ]) - z m) := by ring
  obtain ⟨w, hw⟩ : (ℓ : ℤ_[ℓ]) ^ (m + 1) ∣ L - z m := by
    rw [this]; exact dvd_add (dvd_neg.2 h1) h2
  exact ⟨w, by rw [← hw]; ring⟩

/-- **The `ℓ`-adic rank of an inverse system of Bockstein shape.** Let `H`, `H'` be finitely
generated abelian groups and `A` an inverse system of `ℤ_ℓ`-modules with additive maps
`iₘ : H → Aₘ` and `pₘ : Aₘ → H'` such that

* `ker iₘ = ℓ^{m+1} H`, `ker pₘ = im iₘ`, and `ℓ^{m+1}` kills the image of `pₘ` (that is,
  `0 → H/ℓ^{m+1}H → Aₘ → H'[ℓ^{m+1}]` is exact);
* the transition map `Aₘ₊₁ → Aₘ` is compatible with the reduction `H/ℓ^{m+2}H → H/ℓ^{m+1}H` and
  with multiplication by `ℓ` on `H'`.

Then `dim_{ℚ_ℓ} ℚ_ℓ ⊗_{ℤ_ℓ} lim A = rank_ℤ H`. -/
theorem finrank_rationalLimit_eq_finrank_of_bockstein {H H' : Type*} [AddCommGroup H]
    [AddCommGroup H'] [Module.Finite ℤ H] [Module.Finite ℤ H']
    (A : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) [HasLimit A]
    (i : ∀ m : ℕ, H →+ A.obj (op m)) (p : ∀ m : ℕ, A.obj (op m) →+ H')
    (hi : ∀ (m : ℕ) (h : H), i m h = 0 ↔ ∃ y, h = ℓ ^ (m + 1) • y)
    (hip : ∀ (m : ℕ) (x : A.obj (op m)), p m x = 0 ↔ ∃ h, i m h = x)
    (hp : ∀ (m : ℕ) (x : A.obj (op m)), ℓ ^ (m + 1) • p m x = 0)
    (hi_succ : ∀ (m : ℕ) (h : H), A.map (homOfLE (m.le_add_right 1)).op (i (m + 1) h) = i m h)
    (hp_succ : ∀ (m : ℕ) (x : A.obj (op (m + 1))),
      p m (A.map (homOfLE (m.le_add_right 1)).op x) = ℓ • p (m + 1) x) :
    Module.finrank ℚ_[ℓ] (rationalLimit A) = Module.finrank ℤ H := by
  obtain ⟨n, e, π, d, hd, hπ, hdπ, hrank⟩ := AddCommGroup.exists_basis_mod_torsion H
  rw [hrank, finrank_rationalLimit]
  have hik : ∀ m h, ℓ ^ (m + 1) • i m h = 0 := fun m h => by
    rw [← map_nsmul, (hi m _).2 ⟨h, rfl⟩]
  -- the map `ℤ_ℓⁿ → lim A`, `c ↦ (∑ₖ cₖ iₘ(eₖ))ₘ`
  let ψ : ∀ m : ℕ, (Fin n → ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] A.obj (op m) := fun m =>
    Fintype.linearCombination ℤ_[ℓ] (fun k => i m (e k))
  let cone : Cone A :=
    { pt := ModuleCat.of ℤ_[ℓ] (ULift.{v} (Fin n → ℤ_[ℓ]))
      π := NatTrans.ofOpSequence
        (fun m => ModuleCat.ofHom (ψ m ∘ₗ ULift.moduleEquiv.toLinearMap)) (fun m => by
        ext c
        simp [ψ, Fintype.linearCombination_apply, map_sum, map_smul, hi_succ]) }
  let Ψ : (Fin n → ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] (limit A : ModuleCat.{v} ℤ_[ℓ]) :=
    (limit.lift A cone).hom ∘ₗ ULift.moduleEquiv.symm.toLinearMap
  have hΨ : ∀ c m, limit.π A (op m) (Ψ c) = ∑ k, c k • i m (e k) := fun c m => by
    change limit.π A (op m) (limit.lift A cone (ULift.moduleEquiv.symm c)) = _
    rw [limit.lift_π_apply]
    simp [cone, ψ, Fintype.linearCombination_apply]
  refine Module.finrank_eq_of_injective_of_smul_mem_range Ψ ?_ (d := (d : ℤ_[ℓ]))
    (by exact_mod_cast hd) ?_
  · -- injectivity
    rw [injective_iff_map_eq_zero]
    intro c hc
    funext k
    refine eq_zero_of_forall_pow_dvd fun m => ?_
    choose z w hzw using fun k => exists_eq_intCast_add_pow_mul (c k) (m + 1)
    have h0 : i m (∑ k, z k • e k) = 0 := by
      have := hΨ c m
      rw [hc, map_zero] at this
      rw [map_sum, this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, smul_eq_zsmul_of_eq_add_pow_mul (hzw k) (hik m (e k))]
    obtain ⟨y, hy⟩ := (hi m _).1 h0
    have hz : z = ℓ ^ (m + 1) • π y := by rw [← map_nsmul, ← hy, hπ]
    have hzk : (z k : ℤ_[ℓ]) = (ℓ : ℤ_[ℓ]) ^ (m + 1) * (π y k : ℤ_[ℓ]) := by
      rw [hz, Pi.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [hzw k, hzk, ← mul_add]
    exact dvd_mul_right _ _
  · -- the cokernel is killed by `d`
    intro a
    set am : ∀ m : ℕ, A.obj (op m) := fun m => limit.π A (op m) a with ham
    have hcompat : ∀ m, A.map (homOfLE (m.le_add_right 1)).op (am (m + 1)) = am m := fun m =>
      limit.w_apply A (homOfLE (m.le_add_right 1)).op a
    have ht : ∀ m, p m (am m) = 0 := AddCommGroup.eq_zero_of_eq_smul_succ hℓ.out
      (fun m => p m (am m)) (fun m => by rw [← hcompat m, hp_succ]) (fun m => hp m _)
    choose h hh using fun m => (hip m (am m)).1 (ht m)
    have hy : ∀ m, ∃ y, h (m + 1) - h m = ℓ ^ (m + 1) • y := fun m => by
      refine (hi m _).1 ?_
      rw [map_sub, hh, ← hi_succ, hh, hcompat, sub_self]
    choose y hy using hy
    have hzk : ∀ k m, (ℓ : ℤ) ^ (m + 1) ∣ π (h (m + 1)) k - π (h m) k := fun k m => by
      rw [← Pi.sub_apply, ← map_sub, hy, map_nsmul, Pi.smul_apply, nsmul_eq_mul]
      push_cast
      exact dvd_mul_right _ _
    choose c hc using fun k => exists_forall_eq_add_pow_mul (fun m => π (h m) k) (hzk k)
    refine ⟨(d : ℤ_[ℓ]) • c, Concrete.limit_ext A _ _ fun j => ?_⟩
    induction j with | op m => ?_
    simp only [map_smul, hΨ c m]
    change (d : ℤ_[ℓ]) • am m = _
    have hsum : ∑ k, c k • i m (e k) = i m (∑ k, π (h m) k • e k) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      obtain ⟨w, hw⟩ := hc k m
      rw [map_zsmul, smul_eq_zsmul_of_eq_add_pow_mul hw (hik m (e k))]
    rw [hsum, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← map_nsmul (i m), ← hdπ,
      map_nsmul (i m), hh]

end PadicInt
