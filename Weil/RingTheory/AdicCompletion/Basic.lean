module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.NumberTheory.Padics.RingHoms
public import Weil.Defs.CategoryTheory.ObjectProperty.LAdicSystem
public import Weil.Defs.RingTheory.AdicCompletion.Basic
public import Weil.Attr

/-!
# The projective system of a finitely generated module is `l`-adic

Let `Λ` be a commutative ring and `l ∈ Λ` such that `Λ / l Λ` is an Artinian ring (for instance
`Λ = ℤ_l`, where `Λ / l Λ = 𝔽_l`). For a finitely generated `Λ`-module `M`, the projective
system `S(M) = (M / l^{n+1} M)_n` is an `l`-adic system: its transition maps
`M / l^{n+2} M → M / l^{n+1} M` are surjective with kernel `l^{n+1} M / l^{n+2} M`, and each
`M / l^{n+1} M` has finite length, by induction on `n` from the exact sequences
`M / l M → M / l^{k+1} M → M / l^k M → 0`, the first map being multiplication by `l^k`.

## Main results

* `CategoryTheory.ProjectiveSystem.isFiniteLength_quotient_pow_smul_top`: for `M` finitely
  generated and `Λ / l Λ` Artinian, `M / l^k M` has finite length.
* `CategoryTheory.ProjectiveSystem.isLAdicSystem_ofModule`: `S(M)` is an `l`-adic system.
* `CategoryTheory.ProjectiveSystem.isLAdicSystem_ofModule_padicInt`: the case `Λ = ℤ_[p]`.

## Implementation notes

The source fixes `Λ = ℤ_l`, where `Λ / l^{n+1} Λ` is finite. The result is stated for any
commutative ring `Λ` with `Λ / l Λ` Artinian; the source's case is
`CategoryTheory.ProjectiveSystem.isLAdicSystem_ofModule_padicInt`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite Pointwise TensorProduct

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- If `Λ / l Λ` is Artinian, then `M / l M` is an Artinian `Λ`-module for every finitely
generated `M`. -/
lemma isArtinian_quotient_smul_top [IsArtinianRing (Λ ⧸ Ideal.span {l})] (M : Type*)
    [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] :
    IsArtinian Λ (M ⧸ (l • ⊤ : Submodule Λ M)) := by
  have hfin : Module.Finite (Λ ⧸ Ideal.span {l}) ((Λ ⧸ Ideal.span {l}) ⊗[Λ] M) :=
    inferInstance
  have : IsArtinian (Λ ⧸ Ideal.span {l}) ((Λ ⧸ Ideal.span {l}) ⊗[Λ] M) :=
    ((IsArtinianRing.tfae (Λ ⧸ Ideal.span {l}) ((Λ ⧸ Ideal.span {l}) ⊗[Λ] M)).out 1 3).mp hfin
  have : IsArtinian Λ ((Λ ⧸ Ideal.span {l}) ⊗[Λ] M) :=
    isArtinian_of_surjective_algebraMap (R := Λ ⧸ Ideal.span {l})
      Ideal.Quotient.mk_surjective
  have e := TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {l})
  rw [Submodule.ideal_span_singleton_smul] at e
  exact isArtinian_of_linearEquiv e

lemma pow_succ_smul_top_le_pow_smul_top (l : Λ) (M : Type*) [AddCommGroup M] [Module Λ M]
    (k : ℕ) : (l ^ (k + 1) • ⊤ : Submodule Λ M) ≤ l ^ k • ⊤ := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨l • x, Submodule.mem_top, by simpa [pow_succ, mul_smul] using smul_comm l (l ^ k) x⟩

lemma smul_top_le_comap_pow_smul (l : Λ) (M : Type*) [AddCommGroup M] [Module Λ M] (k : ℕ) :
    (l • ⊤ : Submodule Λ M) ≤
      (l ^ (k + 1) • ⊤ : Submodule Λ M).comap (l ^ k • LinearMap.id) := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨x, Submodule.mem_top, by simpa [pow_succ, mul_smul] using (smul_comm l (l ^ k) x).symm⟩

/-- The kernel of `M / l^{k+1} M → M / l^k M` is the image of `M / l M` under multiplication by
`l^k`. -/
lemma range_mapQ_pow_smul_eq_ker (l : Λ) (M : Type*) [AddCommGroup M] [Module Λ M] (k : ℕ) :
    LinearMap.range (Submodule.mapQ _ _ _ (smul_top_le_comap_pow_smul l M k)) =
      LinearMap.ker (Submodule.factor (pow_succ_smul_top_le_pow_smul_top l M k)) := by
  ext y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Submodule.factor, Submodule.mapQ_apply,
    LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hx
    obtain ⟨z, -, hz⟩ := hx
    refine ⟨x - l • z, Submodule.mem_top, ?_⟩
    simp only [DistribSMul.toLinearMap_apply] at hz ⊢
    rw [smul_sub, smul_smul, ← pow_succ, hz, LinearMap.smul_apply, LinearMap.id_apply,
      sub_sub_cancel]
  · rintro ⟨x, -, rfl⟩
    refine ⟨Submodule.Quotient.mk x, ?_⟩
    rw [Submodule.mapQ_apply]
    rfl

/-- The kernel of the transition map `M / l^{k+1} M → M / l^k M` is `l^k (M / l^{k+1} M)`. -/
lemma ker_factorPow_span_singleton (l : Λ) (M : Type*) [AddCommGroup M] [Module Λ M] (k : ℕ) :
    LinearMap.ker (Submodule.factorPow (Ideal.span {l}) M (Nat.le_succ k)) =
      LinearMap.range (l ^ k • LinearMap.id :
        M ⧸ ((Ideal.span {l}) ^ (k + 1) • ⊤ : Submodule Λ M) →ₗ[Λ]
          M ⧸ ((Ideal.span {l}) ^ (k + 1) • ⊤ : Submodule Λ M)) := by
  ext y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [LinearMap.mem_ker, LinearMap.mem_range, Submodule.factorPow, Submodule.factor,
    Submodule.mapQ_apply, LinearMap.id_apply]
  rw [Submodule.Quotient.mk_eq_zero, span_singleton_pow_smul_top,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨x, -, rfl⟩
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.smul_apply, LinearMap.id_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq, span_singleton_pow_smul_top,
      Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨z, -, hz⟩ := hx
    refine ⟨x - l • z, Submodule.mem_top, ?_⟩
    rw [smul_sub, smul_smul, ← pow_succ, hz, sub_sub_cancel]

/-- If `Λ / l Λ` is Artinian and `M` is finitely generated, then `M / l^k M` is Artinian. -/
lemma isArtinian_quotient_pow_smul_top [IsArtinianRing (Λ ⧸ Ideal.span {l})] (M : Type*)
    [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (k : ℕ) :
    IsArtinian Λ (M ⧸ (l ^ k • ⊤ : Submodule Λ M)) := by
  induction k with
  | zero =>
    have : Subsingleton (M ⧸ (l ^ 0 • ⊤ : Submodule Λ M)) := by
      rw [pow_zero, one_smul]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    have : Finite (M ⧸ (l ^ 0 • ⊤ : Submodule Λ M)) := Finite.of_subsingleton
    infer_instance
  | succ k ih =>
    have := isArtinian_quotient_smul_top (l := l) M
    exact isArtinian_of_range_eq_ker _ _ (range_mapQ_pow_smul_eq_ker l M k)

/-- If `Λ / l Λ` is Artinian and `M` is finitely generated, then `M / l^k M` is a `Λ`-module of
finite length. -/
theorem isFiniteLength_quotient_pow_smul_top [IsArtinianRing (Λ ⧸ Ideal.span {l})] (M : Type*)
    [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (k : ℕ) :
    IsFiniteLength Λ (M ⧸ (l ^ k • ⊤ : Submodule Λ M)) := by
  have := isArtinian_quotient_pow_smul_top (l := l) M k
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨isNoetherian_of_finite_isArtinian _, this⟩

/-- For a finitely generated `Λ`-module `M`, with `Λ / l Λ` Artinian, the projective system
`S(M) = (M / l^{n+1} M)_n` is an `l`-adic system. -/
@[weil "lem_fk112_l_adic_system_of_module_is_l_adic"]
theorem isLAdicSystem_ofModule [IsArtinianRing (Λ ⧸ Ideal.span {l})] (M : ModuleCat.{v} Λ)
    [Module.Finite Λ M] : IsLAdicSystem ((ofModule l).obj M) where
  isZero_of_neg _ hn := isZero_ofModule_term M hn
  pow_smul_eq_zero n x := pow_smul_eq_zero_of_quotient l M (n + 1) x
  surjective n y := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  ker_eq n := by
    exact ker_factorPow_span_singleton l M (n + 1)
  isFiniteLength n := by
    rcases lt_or_ge n 0 with hn | hn
    · have : Subsingleton (((ofModule l).obj M).term n) :=
        ModuleCat.subsingleton_of_isZero (isZero_ofModule_term M hn)
      exact IsFiniteLength.of_subsingleton
    · exact (isFiniteLength_quotient_pow_smul_top (l := l) M (n.toNat + 1)).of_surjective
        (ofModuleTermEquiv l M hn).symm.surjective

/-- `ℤ_[p] / p ℤ_[p]` is a field, hence an Artinian ring. -/
lemma isArtinianRing_padicInt_quotient_span_p (p : ℕ) [Fact p.Prime] :
    IsArtinianRing (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  have : (Ideal.span {(p : ℤ_[p])}).IsMaximal := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    exact IsLocalRing.maximalIdeal.isMaximal _
  let := Ideal.Quotient.field (Ideal.span {(p : ℤ_[p])})
  infer_instance

/-- The source's case `Λ = ℤ_l`: for a finitely generated `ℤ_l`-module `M`, `S(M)` is an
`l`-adic system. -/
theorem isLAdicSystem_ofModule_padicInt {p : ℕ} [Fact p.Prime] (M : ModuleCat.{v} ℤ_[p])
    [Module.Finite ℤ_[p] M] : IsLAdicSystem ((ofModule (p : ℤ_[p])).obj M) :=
  have := isArtinianRing_padicInt_quotient_span_p p
  isLAdicSystem_ofModule M

end ProjectiveSystem

end CategoryTheory
