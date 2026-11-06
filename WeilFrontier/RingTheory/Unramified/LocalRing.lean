module

public import WeilFrontier.Defs.RingTheory.QuasiFinite.Basic
public import WeilFrontier.Defs.RingTheory.Unramified.LocalRing
public import Weil.Attr
public import WeilFrontier.RingTheory.EssentialFiniteness
public import WeilFrontier.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Unramified local homomorphisms are quasi-finite

Let `A → B` be an unramified local homomorphism of local rings. Then `𝔪(A) B = 𝔪(B)`, so the
closed fibre `B ⧸ 𝔪(A) B` is the residue field of `B`, which is a finite extension of the residue
field of `A`. Hence `A → B` is a quasi-finite local homomorphism.

## Main results

* `Algebra.IsQuasiFiniteLocalHom.of_isUnramifiedLocal`: an unramified local homomorphism of local
  rings is a quasi-finite local homomorphism.

## Implementation notes

The source assumes `A` and `B` noetherian; the argument does not use it, so it is not assumed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

open IsLocalRing

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]

/-- An unramified local homomorphism of local rings is a quasi-finite local homomorphism. -/
@[weil "lem_fk101_unramified_is_quasi_finite"]
theorem IsQuasiFiniteLocalHom.of_isUnramifiedLocal [IsUnramifiedLocal A B] :
    IsQuasiFiniteLocalHom A B := by
  have : Module.Finite A (ResidueField B) := Module.Finite.trans (ResidueField A) _
  have : Module.Finite A (B ⧸ maximalIdeal B) := ‹Module.Finite A (ResidueField B)›
  have : Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    .equiv (Ideal.quotientEquivAlgOfEq A
      (IsUnramifiedLocal.map_maximalIdeal (R := A) (S := B))).symm.toLinearEquiv
  exact .of_finite_restrictScalars

end Algebra

end

/-! ### The Jacobian criterion for unramified local homomorphisms -/

/-!
# The Jacobian criterion for unramified local homomorphisms

Let `A` be a commutative ring, `P_μ ∈ A[X_ν]` (`μ ∈ ι`, `ν ∈ σ`, both finite) polynomials,
`C = A[X] ⧸ (P_μ)` and `𝔮` a prime of `C` lying over the prime `𝔭₀` of `A`; write `𝔭` for the
preimage of `𝔮` in `A[X]`. Then `A_𝔭₀ → C_𝔮` is an unramified local homomorphism if and only if
the maximal minors (of size `|σ|`) of the Jacobian matrix `(∂P_μ/∂X_ν)` generate the unit ideal
of `A[X]_𝔭`.

The proof: by the Kähler criterion `A_𝔭₀ → C_𝔮` is unramified iff `Ω[C_𝔮 ⁄ A_𝔭₀] = (Ω[C ⁄ A])_𝔮`
vanishes. If some maximal minor `Δ` is a unit at `𝔭`, multiplying the relations
`∑_ν ∂P_μ/∂X_ν dX_ν = 0` by the adjugate of the corresponding square submatrix gives
`Δ · dX_ν = 0`, so `(Ω[C ⁄ A])_𝔮 = 0`. Conversely, if all maximal minors lie in `𝔭`, the Jacobian
matrix over the residue field `κ(𝔮)` has a non-zero kernel vector `w`; the derivation
`A[X] → κ(𝔮)`, `X_ν ↦ w_ν`, kills the ideal `(P_μ)` and so, through the conormal sequence,
defines a `C`-linear map `Ω[C ⁄ A] → κ(𝔮)` which does not vanish after localization at `𝔮`.

## Main definitions

* `MvPolynomial.jacobianMatrix`: the Jacobian matrix `(∂P_μ/∂X_ν)` of a family of polynomials.

## Main results

* `MvPolynomial.derivation_eq_sum_pderiv`: a derivation of `A[X]` is `∑_ν ∂/∂X_ν · D(X_ν)`.
* `Matrix.exists_mulVec_eq_zero_of_forall_det_submatrix_eq_zero`: a matrix over a field all of
  whose maximal minors vanish has a non-zero kernel vector.
* `Algebra.isUnramifiedLocal_localization_quotient_iff`: the Jacobian criterion, for a prime of
  `C = A[X] ⧸ (P_μ)`.
* `Algebra.isUnramifiedLocal_localization_quotient_iff_of_le`: the same, for a prime of `A[X]`
  containing the `P_μ`.

## Implementation notes

The source assumes `A` noetherian; the criterion holds for every commutative ring. The maximal
minors are indexed by embeddings `σ ↪ ι` (row selections in every order); they agree with the
minors of increasing row selections up to sign, so they generate the same ideal. When `|ι| < |σ|`
there are no embeddings and the ideal is `0`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

open TensorProduct KaehlerDifferential

namespace MvPolynomial

variable {σ A : Type*} [CommRing A]

/-- The Jacobian matrix `(∂P_μ/∂X_ν)_{μ,ν}` of a family `P` of polynomials. -/
noncomputable def jacobianMatrix {ι : Type*} (P : ι → MvPolynomial σ A) :
    Matrix ι σ (MvPolynomial σ A) :=
  Matrix.of fun μ ν ↦ pderiv ν (P μ)

@[simp]
lemma jacobianMatrix_apply {ι : Type*} (P : ι → MvPolynomial σ A) (μ : ι) (ν : σ) :
    jacobianMatrix P μ ν = pderiv ν (P μ) := rfl

/-- A derivation `D` of a polynomial ring in finitely many variables is
`f ↦ ∑_ν (∂f/∂X_ν) • D(X_ν)`. -/
lemma derivation_eq_sum_pderiv [Fintype σ] {M : Type*} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    (δ : Derivation A (MvPolynomial σ A) M) (f : MvPolynomial σ A) :
    δ f = ∑ ν, pderiv ν f • δ (X ν) := by
  rw [← δ.liftKaehlerDifferential_comp_D f, ← (mvPolynomialBasis A σ).sum_repr (D A _ f)]
  simp [map_sum, map_smul]

end MvPolynomial

namespace Matrix

/-- A matrix over a field all of whose maximal minors (of size the number of columns) vanish has a
non-zero vector in its kernel. -/
lemma exists_mulVec_eq_zero_of_forall_det_submatrix_eq_zero {ι σ K : Type*} [Finite ι]
    [Fintype σ] [DecidableEq σ] [Field K] (M : Matrix ι σ K)
    (h : ∀ f : σ ↪ ι, (M.submatrix f id).det = 0) : ∃ w : σ → K, w ≠ 0 ∧ M *ᵥ w = 0 := by
  by_contra! H
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hw0
    exact H w hw0 hw
  have hrank : M.rank = Fintype.card σ := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
  have hspan : Submodule.span K (Set.range M.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hspan', hli⟩ := exists_linearIndependent' K M.row
  have : Finite κ := Finite.of_injective a ha
  let b := Module.Basis.mk hli (by rw [hspan', hspan])
  have hcard : Nat.card σ = Nat.card κ := by
    rw [← Module.finrank_eq_nat_card_basis b, Module.finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card]
  obtain ⟨e⟩ := Finite.card_eq.mp hcard
  let f : σ ↪ ι := ⟨a ∘ e, ha.comp e.injective⟩
  have hli' : LinearIndependent K (M.submatrix f id).row := hli.comp e e.injective
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at hli'
  exact hli'.ne_zero (h f)

end Matrix

namespace Algebra

open MvPolynomial

variable {A σ ι : Type*} [CommRing A] [Fintype σ] [DecidableEq σ] [Finite ι]
  (P : ι → MvPolynomial σ A)

/-- In a localization at a prime `𝔭`, a family of elements of the ring generates the unit ideal iff
one of them lies outside `𝔭`. -/
lemma span_range_algebraMap_localization_eq_top_iff {R κ : Type*} [CommRing R] (𝔭 : Ideal R)
    [𝔭.IsPrime] (g : κ → R) :
    Ideal.span (Set.range fun k ↦ algebraMap R (Localization.AtPrime 𝔭) (g k)) = ⊤ ↔
      ∃ k, g k ∉ 𝔭 := by
  constructor
  · intro htop
    by_contra! hall
    have hle : Ideal.span (Set.range fun k ↦ algebraMap R (Localization.AtPrime 𝔭) (g k)) ≤
        IsLocalRing.maximalIdeal _ := by
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔭]
      exact fun h ↦ h (hall k)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ hle))
  · rintro ⟨k, hk⟩
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k, rfl⟩)
      ((IsLocalization.AtPrime.isUnit_to_map_iff _ 𝔭 _).mpr hk)

variable {S : Type*} [CommRing S] [Algebra A S] [Algebra (MvPolynomial σ A) S]
  [IsScalarTower A (MvPolynomial σ A) S]

omit [DecidableEq σ] [Finite ι] in
/-- For an algebra `S` over `A[X]`, `d(ḡ) = ∑_ν (∂g/∂X_ν)‾ dX̄_ν` in `Ω[S ⁄ A]`. -/
lemma D_algebraMap_eq_sum_pderiv (g : MvPolynomial σ A) :
    D A S (algebraMap _ S g) =
      ∑ ν, algebraMap _ S (pderiv ν g) • D A S (algebraMap _ S (X ν : MvPolynomial σ A)) := by
  rw [show D A S (algebraMap _ S g) = ((D A S).compAlgebraMap (MvPolynomial σ A)) g from rfl,
    MvPolynomial.derivation_eq_sum_pderiv]
  simp only [algebraMap_smul]
  rfl

omit [Finite ι] in
/-- If a maximal minor of the Jacobian matrix maps outside `𝔮`, then `(Ω[S ⁄ A])_𝔮 = 0`. -/
lemma subsingleton_localizedModule_kaehlerDifferential_of_det_notMem
    (hS : Function.Surjective (algebraMap (MvPolynomial σ A) S))
    (hP : ∀ μ, algebraMap (MvPolynomial σ A) S (P μ) = 0) (q : Ideal S) [q.IsPrime] (f : σ ↪ ι)
    (hf : algebraMap _ S ((jacobianMatrix P).submatrix f _root_.id).det ∉ q) :
    Subsingleton (LocalizedModule q.primeCompl Ω[S⁄A]) := by
  set N := ((jacobianMatrix P).submatrix f _root_.id).map (algebraMap (MvPolynomial σ A) S)
  set v : σ → Ω[S⁄A] := fun ν ↦ D A S (algebraMap _ S (X ν : MvPolynomial σ A))
  have hrow : ∀ i, ∑ ν, N i ν • v ν = 0 := by
    intro i
    simp only [N, v, Matrix.map_apply, Matrix.submatrix_apply, jacobianMatrix_apply, _root_.id]
    rw [← D_algebraMap_eq_sum_pderiv, hP, map_zero]
  have hdet : N.det = algebraMap _ S ((jacobianMatrix P).submatrix f _root_.id).det :=
    by rw [RingHom.map_det]; rfl
  have hv : ∀ k, N.det • v k = 0 := by
    intro k
    have h1 : N.det • v k = ∑ ν, (N.adjugate * N) k ν • v ν := by
      rw [Matrix.adjugate_mul]
      simp [Matrix.smul_apply, Matrix.one_apply, ite_smul]
    rw [h1]
    simp_rw [Matrix.mul_apply, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, hrow, smul_zero, Finset.sum_const_zero]
  have hall : ∀ x : Ω[S⁄A], N.det • x = 0 := by
    intro x
    have hx : x ∈ Submodule.span S (Set.range (D A S)) := by
      rw [span_range_derivation]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨g, rfl⟩ := hS c
      rw [D_algebraMap_eq_sum_pderiv, Finset.smul_sum]
      refine Finset.sum_eq_zero fun ν _ ↦ ?_
      rw [smul_comm, show N.det • D A S (algebraMap _ S (X ν : MvPolynomial σ A)) = 0 from hv ν,
        smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul c y _ hy => rw [smul_comm, hy, smul_zero]
  refine ⟨fun a b ↦ ?_⟩
  suffices H : ∀ y : LocalizedModule q.primeCompl Ω[S⁄A], y = 0 by rw [H a, H b]
  intro y
  induction y using LocalizedModule.induction_on with
  | h m s =>
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    refine ⟨⟨N.det, hdet ▸ hf⟩, ?_⟩
    simp [hall]

/-- If `(Ω[S ⁄ A])_𝔮 = 0`, then some maximal minor of the Jacobian matrix maps outside `𝔮`. -/
lemma exists_det_notMem_of_subsingleton_localizedModule_kaehlerDifferential
    (hS : Function.Surjective (algebraMap (MvPolynomial σ A) S))
    (hker : RingHom.ker (algebraMap (MvPolynomial σ A) S) = Ideal.span (Set.range P))
    (q : Ideal S) [q.IsPrime] [Subsingleton (LocalizedModule q.primeCompl Ω[S⁄A])] :
    ∃ f : σ ↪ ι, algebraMap _ S ((jacobianMatrix P).submatrix f _root_.id).det ∉ q := by
  by_contra! hall
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_of_forall_det_submatrix_eq_zero
    ((jacobianMatrix P).map (algebraMap (MvPolynomial σ A) q.ResidueField)) fun f ↦ by
      rw [Matrix.submatrix_map, show ∀ M : Matrix σ σ (MvPolynomial σ A),
          (M.map (algebraMap (MvPolynomial σ A) q.ResidueField)).det =
            algebraMap (MvPolynomial σ A) q.ResidueField M.det from
          fun M ↦ by rw [RingHom.map_det]; rfl,
        IsScalarTower.algebraMap_apply (MvPolynomial σ A) S q.ResidueField,
        Ideal.algebraMap_residueField_eq_zero]
      exact hall f
  let δ : Derivation A (MvPolynomial σ A) q.ResidueField := mkDerivation A w
  have hK : ∀ x : MvPolynomial σ A, x ∈ Ideal.span (Set.range P) →
      algebraMap (MvPolynomial σ A) q.ResidueField x = 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply (MvPolynomial σ A) S q.ResidueField,
      show algebraMap (MvPolynomial σ A) S x = 0 from hker.ge hx, map_zero]
  have hδ : ∀ x, x ∈ Ideal.span (Set.range P) → δ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨μ, rfl⟩ := hy
      rw [MvPolynomial.derivation_eq_sum_pderiv]
      have := congr_fun hw μ
      simpa [δ, Matrix.mulVec, dotProduct, Algebra.smul_def] using this
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
    | smul r y hy' hy =>
      rw [smul_eq_mul, Derivation.leibniz, hy, smul_zero, zero_add, Algebra.smul_def, hK y hy',
        zero_mul]
  let l : S ⊗[MvPolynomial σ A] Ω[MvPolynomial σ A⁄A] →ₗ[S] q.ResidueField :=
    δ.liftKaehlerDifferential.liftBaseChange S
  have hl : ∀ y, mapBaseChange A (MvPolynomial σ A) S y = 0 → l y = 0 := by
    intro y hy
    obtain ⟨z, rfl⟩ := (exact_kerCotangentToTensor_mapBaseChange A (MvPolynomial σ A) S
      hS y).mp hy
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ z
    simp only [l, kerCotangentToTensor_toCotangent, LinearMap.liftBaseChange_tmul,
      Derivation.liftKaehlerDifferential_comp_D, one_smul]
    exact hδ x.1 (hker.le x.2)
  apply hw0
  funext ν
  have h0 : LocalizedModule.mk (D A S (algebraMap _ S (X ν : MvPolynomial σ A)))
      (1 : q.primeCompl) = 0 :=
    Subsingleton.elim _ _
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h0
  obtain ⟨⟨u, hu⟩, hu'⟩ := h0
  simp only [one_smul, smul_zero] at hu'
  have := hl (u ⊗ₜ D A _ (X ν)) (by rw [mapBaseChange_tmul, map_D]; exact hu')
  simp only [l, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    δ, mkDerivation_X, Algebra.smul_def] at this
  have hu0 : algebraMap S q.ResidueField u ≠ 0 := by
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact hu
  exact (mul_eq_zero.mp this).resolve_left hu0

/-- Let `S` be a quotient of `A[X]` by the ideal `(P_μ)`. The localized differentials `(Ω[S ⁄ A])_𝔮`
vanish iff some maximal minor of the Jacobian matrix of `P` maps outside `𝔮`. -/
theorem subsingleton_localizedModule_kaehlerDifferential_iff_exists_det_notMem
    (hS : Function.Surjective (algebraMap (MvPolynomial σ A) S))
    (hker : RingHom.ker (algebraMap (MvPolynomial σ A) S) = Ideal.span (Set.range P))
    (q : Ideal S) [q.IsPrime] :
    Subsingleton (LocalizedModule q.primeCompl Ω[S⁄A]) ↔
      ∃ f : σ ↪ ι, algebraMap _ S ((jacobianMatrix P).submatrix f _root_.id).det ∉ q :=
  ⟨fun _ ↦ exists_det_notMem_of_subsingleton_localizedModule_kaehlerDifferential P hS hker q,
    fun ⟨f, hf⟩ ↦ subsingleton_localizedModule_kaehlerDifferential_of_det_notMem P hS
      (fun μ ↦ hker.ge (Ideal.subset_span ⟨μ, rfl⟩)) q f hf⟩

omit [Fintype σ] [DecidableEq σ] [Finite ι] in
/-- The image of a prime of `A[X]` containing the `P_μ` is a prime of `A[X] ⧸ (P_μ)`. -/
lemma isPrime_map_quotientMk_of_le (𝔭 : Ideal (MvPolynomial σ A)) [𝔭.IsPrime]
    (h𝔭 : Ideal.span (Set.range P) ≤ 𝔭) :
    (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

omit [Fintype σ] [DecidableEq σ] [Finite ι] in
/-- The preimage in `A[X]` of the image of an ideal `𝔭 ⊇ (P_μ)` in `A[X] ⧸ (P_μ)` is `𝔭`. -/
lemma under_map_quotientMk_of_le (𝔭 : Ideal (MvPolynomial σ A))
    (h𝔭 : Ideal.span (Set.range P) ≤ 𝔭) :
    (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))).under (MvPolynomial σ A) = 𝔭 := by
  rw [Ideal.under, Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective'
    _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr h𝔭]

omit [Fintype σ] [DecidableEq σ] [Finite ι] in
/-- The image of a prime `𝔭` of `A[X]` containing the `P_μ` lies over `𝔭 ∩ A`. -/
lemma liesOver_map_quotientMk_of_le (𝔭 : Ideal (MvPolynomial σ A)) [𝔭.IsPrime]
    (h𝔭 : Ideal.span (Set.range P) ≤ 𝔭) :
    haveI := isPrime_map_quotientMk_of_le P 𝔭 h𝔭
    (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P)))).LiesOver (𝔭.under A) := by
  refine ⟨?_⟩
  change Ideal.comap _ 𝔭 = Ideal.comap _ _
  rw [IsScalarTower.algebraMap_eq A (MvPolynomial σ A) (MvPolynomial σ A ⧸ _),
    ← Ideal.comap_comap]
  exact congrArg _ (under_map_quotientMk_of_le P 𝔭 h𝔭).symm

/-- The Jacobian criterion. Let `𝔮` be a prime of `C = A[X] ⧸ (P_μ)` lying over the prime `𝔭₀` of
`A`, and `𝔭` its preimage in `A[X]`. Then `A_𝔭₀ → C_𝔮` is an unramified local homomorphism iff the
maximal minors of the Jacobian matrix `(∂P_μ/∂X_ν)` generate the unit ideal of `A[X]_𝔭`. -/
@[weil "prop_fk101_jacobian_criterion_unramified"]
theorem isUnramifiedLocal_localization_quotient_iff (p₀ : Ideal A) [p₀.IsPrime]
    (q : Ideal (MvPolynomial σ A ⧸ Ideal.span (Set.range P))) [q.IsPrime] [q.LiesOver p₀]
    [Algebra (Localization.AtPrime p₀) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p₀ q] :
    IsUnramifiedLocal (Localization.AtPrime p₀) (Localization.AtPrime q) ↔
      Ideal.span (Set.range fun f : σ ↪ ι ↦
        algebraMap (MvPolynomial σ A) (Localization.AtPrime (q.under (MvPolynomial σ A)))
          ((jacobianMatrix P).submatrix f _root_.id).det) = ⊤ := by
  have : EssFiniteType (Localization.AtPrime p₀) (Localization.AtPrime q) :=
    (isFinitelyGeneratedLocal_localization_atPrime p₀ q).2
  rw [isUnramifiedLocal_iff_formallyUnramified,
    show FormallyUnramified (Localization.AtPrime p₀) (Localization.AtPrime q) ↔
        Subsingleton Ω[Localization.AtPrime q⁄Localization.AtPrime p₀] from
      ⟨fun h ↦ h.subsingleton_kaehlerDifferential, fun h ↦ ⟨h⟩⟩,
    (KaehlerDifferential.localizationAtPrimeEquiv p₀ q).toEquiv.subsingleton_congr,
    subsingleton_localizedModule_kaehlerDifferential_iff_exists_det_notMem P
      Ideal.Quotient.mk_surjective (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]),
    span_range_algebraMap_localization_eq_top_iff]
  rfl

/-- The Jacobian criterion in the form of the source. Let `𝔭` be a prime of `A[X]` containing the
`P_μ`, `𝔭₀ = 𝔭 ∩ A` and `B = (A[X] ⧸ (P_μ))_𝔭`. Then `A_𝔭₀ → B` is an unramified local
homomorphism iff the maximal minors of the Jacobian matrix `(∂P_μ/∂X_ν)` generate the unit ideal
of `A[X]_𝔭`. -/
@[weil "prop_fk101_jacobian_criterion_unramified"]
theorem isUnramifiedLocal_localization_quotient_iff_of_le (𝔭 : Ideal (MvPolynomial σ A))
    [𝔭.IsPrime] (h𝔭 : Ideal.span (Set.range P) ≤ 𝔭) :
    haveI := isPrime_map_quotientMk_of_le P 𝔭 h𝔭
    haveI := liesOver_map_quotientMk_of_le P 𝔭 h𝔭
    letI := Localization.AtPrime.algebraOfLiesOver (𝔭.under A)
      (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P))))
    IsUnramifiedLocal (Localization.AtPrime (𝔭.under A))
        (Localization.AtPrime (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P))))) ↔
      Ideal.span (Set.range fun f : σ ↪ ι ↦ algebraMap (MvPolynomial σ A) (Localization.AtPrime 𝔭)
        ((jacobianMatrix P).submatrix f _root_.id).det) = ⊤ := by
  have := isPrime_map_quotientMk_of_le P 𝔭 h𝔭
  have := liesOver_map_quotientMk_of_le P 𝔭 h𝔭
  let := Localization.AtPrime.algebraOfLiesOver (𝔭.under A)
    (𝔭.map (Ideal.Quotient.mk (Ideal.span (Set.range P))))
  rw [isUnramifiedLocal_localization_quotient_iff P (𝔭.under A),
    span_range_algebraMap_localization_eq_top_iff, span_range_algebraMap_localization_eq_top_iff,
    under_map_quotientMk_of_le P 𝔭 h𝔭]

end Algebra
