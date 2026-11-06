module

public import Weil.Attr
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilFrontier.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import WeilFrontier.Defs.RingTheory.EssentialFiniteness
public import WeilFrontier.Defs.RingTheory.Unramified.LocalRing

/-!
# Unramified local homomorphisms are quotients of local-étale ones

Let `A → B` be a local homomorphism of local rings, with `A` noetherian, which is unramified and
essentially of finite type. Then there is a local-étale `A`-algebra `B'` (a noetherian local ring
with `A → B'` flat, unramified and essentially of finite type) together with a surjective local
`A`-algebra homomorphism `B' → B`.

The algebra `B'` is obtained from the local structure theorem for unramified algebras: writing
`B` as the localization `S_Q` of a finitely generated `A`-algebra `S`, there are `f ∉ Q` and a
standard étale `A`-algebra `P` surjecting onto `S[1/f]`; then `B'` is the localization of `P` at
the preimage of the maximal ideal of `B`.

## Main results

* `Algebra.IsUnramifiedLocal.exists_isEtaleLocalHom_surjective`: an unramified local
  homomorphism essentially of finite type out of a noetherian local ring is a quotient of a
  local-étale one.

## Implementation notes

The source proves this through a Jacobian presentation of `B` as a quotient of a localized
polynomial ring; the proof here instead uses
`Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`, which gives the étale cover directly.
The source assumes `B` noetherian; this is not needed. The algebra `B'` is produced in the
universe of `A`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

public section

universe u v

open IsLocalRing

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]

/-- An unramified local homomorphism `A → B` essentially of finite type, with `A` noetherian, is
the composite of a local-étale homomorphism `A → B'` and a surjective local homomorphism
`B' → B`. -/
@[weil "lem_fk101_unramified_local_is_quotient_of_local_etale"]
theorem IsUnramifiedLocal.exists_isEtaleLocalHom_surjective [EssFiniteType A B]
    [IsUnramifiedLocal A B] :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra A B') (_ : IsNoetherianRing B')
      (_ : IsLocalRing B') (_ : IsLocalHom (algebraMap A B')),
      (algebraMap A B').IsEtaleLocalHom ∧
      ∃ φ : B' →ₐ[A] B, Function.Surjective φ ∧ IsLocalHom (φ : B' →+* B) := by
  obtain ⟨S₀, M, hft, hloc⟩ := (essFiniteType_iff_exists_subalgebra A B).mp ‹_›
  let Q : Ideal S₀ := (maximalIdeal B).comap (algebraMap S₀ B)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hlocQ : IsLocalization Q.primeCompl B := by
    refine IsLocalization.of_le M Q.primeCompl ?_ ?_
    · intro m hm hq
      exact (mem_maximalIdeal _).mp hq (IsLocalization.map_units B ⟨m, hm⟩)
    · intro r hr
      by_contra hu
      exact hr ((mem_maximalIdeal _).mpr hu)
  let e : Localization.AtPrime Q ≃ₐ[A] B :=
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) B).restrictScalars A
  have : FormallyUnramified A B := inferInstance
  have : IsUnramifiedAt A Q := FormallyUnramified.of_equiv e.symm
  obtain ⟨f, hfQ, P, φ, hφ⟩ := IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := A) Q
  -- the map `S₀[1/f] → B`
  have hfu : ∀ y : Submonoid.powers f, IsUnit (IsScalarTower.toAlgHom A S₀ B y) := by
    rintro ⟨y, n, rfl⟩
    have : IsUnit (algebraMap S₀ B f) := by
      by_contra h
      exact hfQ ((mem_maximalIdeal _).mpr h)
    simpa using this.pow n
  let g : Localization.Away f →ₐ[A] B := IsLocalization.liftAlgHom hfu
  have hg : ∀ s : S₀, g (algebraMap S₀ _ s) = algebraMap S₀ B s := fun s ↦
    IsLocalization.lift_eq _ s
  let ψ : P.Ring →ₐ[A] B := g.comp φ
  let 𝔪 : Ideal P.Ring := (maximalIdeal B).comap ψ
  have : 𝔪.IsPrime := Ideal.comap_isPrime _ _
  let B' := Localization.AtPrime 𝔪
  -- `B'` is noetherian
  have : FiniteType A P.Ring := inferInstance
  have : IsNoetherianRing P.Ring := FiniteType.isNoetherianRing A P.Ring
  have : IsNoetherianRing B' := IsLocalization.isNoetherianRing 𝔪.primeCompl B' inferInstance
  -- `A → B'` is local
  have hloc' : IsLocalHom (algebraMap A B') := by
    refine ⟨fun x hx ↦ ?_⟩
    by_contra hxu
    have hxm : x ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hxu
    have h1 : algebraMap A P.Ring x ∈ 𝔪 := by
      change ψ (algebraMap A P.Ring x) ∈ maximalIdeal B
      rw [AlgHom.commutes]
      exact map_nonunit (algebraMap A B) x hxm
    have h2 : algebraMap P.Ring B' (algebraMap A P.Ring x) ∈ maximalIdeal B' :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff B' 𝔪 _).mpr h1
    rw [← IsScalarTower.algebraMap_apply] at h2
    exact (mem_maximalIdeal _).mp h2 hx
  -- `A → B'` is local-étale
  have het : (algebraMap A B').IsEtaleLocalHom := by
    have : Module.Flat P.Ring B' := IsLocalization.flat B' 𝔪.primeCompl
    have : Module.Flat A B' := Module.Flat.trans A P.Ring B'
    have : FormallyUnramified P.Ring B' :=
      FormallyUnramified.of_isLocalization 𝔪.primeCompl
    have : FormallyUnramified A B' := FormallyUnramified.comp A P.Ring B'
    have : EssFiniteType P.Ring B' := EssFiniteType.of_isLocalization B' 𝔪.primeCompl
    have : EssFiniteType A B' := EssFiniteType.comp A P.Ring B'
    exact ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
      RingHom.formallyUnramified_algebraMap.mpr inferInstance,
      RingHom.essFiniteType_algebraMap.mpr inferInstance⟩
  -- the map `B' → B`
  have hψu : ∀ y : 𝔪.primeCompl, IsUnit (ψ y) := fun y ↦ by
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr h)
  let θ : B' →ₐ[A] B := IsLocalization.liftAlgHom hψu
  have hθ : ∀ a : P.Ring, θ (algebraMap P.Ring B' a) = ψ a := fun a ↦
    IsLocalization.lift_eq _ a
  have hθs : Function.Surjective θ := by
    intro b
    obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj Q.primeCompl b
    obtain ⟨a, ha⟩ := hφ (algebraMap S₀ _ s)
    obtain ⟨c, hc⟩ := hφ (algebraMap S₀ _ (t : S₀))
    have hψa : ψ a = algebraMap S₀ B s := by
      change g (φ a) = _
      rw [ha, hg]
    have hψc : ψ c = algebraMap S₀ B t := by
      change g (φ c) = _
      rw [hc, hg]
    have hc𝔪 : c ∈ 𝔪.primeCompl := by
      intro hc'
      apply t.2
      change algebraMap S₀ B t ∈ maximalIdeal B
      rw [← hψc]
      exact hc'
    refine ⟨IsLocalization.mk' B' a ⟨c, hc𝔪⟩, ?_⟩
    have hu : IsUnit (algebraMap S₀ B t) := by
      by_contra h
      exact t.2 ((mem_maximalIdeal _).mpr h)
    apply hu.mul_right_cancel
    have := IsLocalization.mk'_spec B' a ⟨c, hc𝔪⟩
    rw [← hψc, ← hθ c, ← map_mul, this, hθ, hψa, hθ, hψc]
    exact hst.symm
  exact ⟨B', inferInstance, inferInstance, inferInstance, inferInstance, hloc', het, θ, hθs,
    IsLocalHom.of_surjective _ hθs⟩

end Algebra

/-! ### A Jacobian presentation of an unramified local homomorphism -/

/-!
# A Jacobian presentation of an unramified local homomorphism

Let `A → B` be a homomorphism to a local ring `B` with `Ω[B⁄A] = 0` (e.g. an unramified local
homomorphism essentially of finite type), let `R = A[X₁, …, Xₙ]`, let `π : R → B` be an
`A`-algebra homomorphism and `𝔪 = π⁻¹(𝔪_B)`, and assume that the induced map `R_𝔪 → B` is
surjective. Then there are `P₁, …, Pₙ ∈ ker π` whose Jacobian determinant `det (∂Pμ/∂Xν)` is a
unit of `R_𝔪`.

## Main results

* `MvPolynomial.exists_isUnit_det_pderiv_of_formallyUnramified`: the statement for a formally
  unramified `A`-algebra `B`.
* `Algebra.IsUnramifiedLocal.exists_isUnit_det_pderiv`: the statement for an unramified,
  finitely generated local homomorphism `A → B` of local rings.

## Implementation notes

Instead of the conormal sequence `I/I² → Ω_{R_𝔪/A} ⊗ B → Ω_{B/A} → 0`, the proof uses
derivations: if the vectors `(∂P/∂Xν mod 𝔪_B)_ν`, `P ∈ ker π`, did not span `κ(B)ⁿ`, a nonzero
linear form `c` on `κ(B)ⁿ` vanishing on them gives a ring homomorphism `R → κ(B)[ε]`,
`Xν ↦ π(Xν) + c(eν) ε`, which extends to `R_𝔪`, kills the kernel of `R_𝔪 → B`, and so descends to
`B`; its `ε`-component is a nonzero `A`-derivation `B → κ(B)`, contradicting `Ω[B⁄A] = 0`.
Noetherianity of `A` and `B`, assumed in the source, is not needed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.1.
-/

@[expose] public section

open IsLocalRing TrivSqZeroExt

namespace MvPolynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B] {n : ℕ}

/-- Elements outside `π⁻¹(𝔪_B)` map to units of the local ring `B`. -/
lemma isUnit_of_mem_primeCompl_comap_maximalIdeal (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (s : ((maximalIdeal B).comap π).primeCompl) : IsUnit (π.toRingHom s) :=
  IsLocalRing.notMem_maximalIdeal.mp s.2

variable [Algebra.FormallyUnramified A B]

/-- Over a formally unramified `A`-algebra `B` with residue field `κ`, the residues of the
gradients of the polynomials in `ker π` span `κⁿ`, provided `R_𝔪 → B` is surjective. -/
lemma span_residue_pderiv_eq_top (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπ : Function.Surjective (IsLocalization.lift (M := ((maximalIdeal B).comap π).primeCompl)
      (S := Localization.AtPrime ((maximalIdeal B).comap π)) (g := π.toRingHom)
      (isUnit_of_mem_primeCompl_comap_maximalIdeal π))) :
    Submodule.span (ResidueField B)
      {w | ∃ P, π P = 0 ∧ (fun ν ↦ residue B (π (pderiv ν P))) = w} = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hWf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set c : Fin n → ResidueField B := fun i ↦ f (Pi.single i 1) with hc
  let r : B →+* DualNumber (ResidueField B) := (inlHom _ _).comp (residue B)
  let φ : MvPolynomial (Fin n) A →+* DualNumber (ResidueField B) :=
    eval₂Hom (r.comp (algebraMap A B)) (fun i ↦ r (π (X i)) + inr (c i))
  have hφ : ∀ P, φ P = r (π P) + inr (f (fun ν ↦ residue B (π (pderiv ν P)))) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp [φ, r, ← Pi.zero_def]
    | add p q hp hq =>
      have hv : (fun ν ↦ residue B (π (pderiv ν (p + q)))) =
          (fun ν ↦ residue B (π (pderiv ν p))) + (fun ν ↦ residue B (π (pderiv ν q))) := by
        ext ν; simp
      rw [map_add, hp, hq, hv, map_add]
      ext
      · simp
      · simp; ring
    | mul_X p i hp =>
      have hv : (fun ν ↦ residue B (π (pderiv ν (p * X i)))) =
          residue B (π (X i)) • (fun ν ↦ residue B (π (pderiv ν p))) +
            residue B (π p) • Pi.single i 1 := by
        ext ν
        by_cases h : ν = i
        · subst h; simp [Derivation.leibniz]; ring
        · simp [Derivation.leibniz, h, Ne.symm h]
      rw [map_mul, hp, hv]
      ext
      · simp [φ, r, c]
      · simp [φ, r, c]; ring
  have hfst : ∀ P, (φ P).fst = residue B (π P) := fun P ↦ by simp [hφ, r]
  have hunit : ∀ s : ((maximalIdeal B).comap π).primeCompl, IsUnit (φ s) := fun s ↦ by
    rw [isUnit_iff_isUnit_fst, hfst]
    exact (isUnit_of_mem_primeCompl_comap_maximalIdeal π s).map (residue B)
  let L : Localization.AtPrime ((maximalIdeal B).comap π) →+* B :=
    IsLocalization.lift (M := ((maximalIdeal B).comap π).primeCompl) (g := π.toRingHom)
      (isUnit_of_mem_primeCompl_comap_maximalIdeal π)
  let φ' : Localization.AtPrime ((maximalIdeal B).comap π) →+* DualNumber (ResidueField B) :=
    IsLocalization.lift (M := ((maximalIdeal B).comap π).primeCompl) hunit
  have hker : RingHom.ker L ≤ RingHom.ker φ' := by
    intro x hx
    obtain ⟨⟨P, s⟩, rfl⟩ := IsLocalization.mk'_surjective ((maximalIdeal B).comap π).primeCompl x
    rw [RingHom.mem_ker] at hx ⊢
    rw [IsLocalization.lift_mk'_spec, mul_zero] at hx ⊢
    have h0 : π P = 0 := hx
    have hv : f (fun ν ↦ residue B (π (pderiv ν P))) = 0 :=
      hWf (Submodule.subset_span ⟨P, h0, rfl⟩)
    rw [hφ, h0, hv]
    simp
  let Ψ : B →+* DualNumber (ResidueField B) := L.liftOfSurjective hπ ⟨φ', hker⟩
  have hΨ : ∀ P, Ψ (π P) = φ P := fun P ↦ by
    have : π P = L (algebraMap _ (Localization.AtPrime ((maximalIdeal B).comap π)) P) :=
      (IsLocalization.lift_eq _ P).symm
    rw [this, RingHom.liftOfSurjective_comp_apply]
    exact IsLocalization.lift_eq _ P
  have hΨfst : ∀ b, (Ψ b).fst = residue B b := by
    have : (fstHom ℕ _ _).toRingHom.comp Ψ = residue B := by
      refine (RingHom.cancel_right hπ).mp
        (IsLocalization.ringHom_ext ((maximalIdeal B).comap π).primeCompl ?_)
      refine RingHom.ext fun P ↦ ?_
      have h1 : L (algebraMap _ (Localization.AtPrime ((maximalIdeal B).comap π)) P) = π P :=
        IsLocalization.lift_eq _ P
      change (Ψ (L (algebraMap _ _ P))).fst = residue B (L (algebraMap _ _ P))
      rw [h1, hΨ, hfst]
    intro b
    exact congr($this b)
  have hΨalg : ∀ a : A, Ψ (algebraMap A B a) = r (algebraMap A B a) := fun a ↦ by
    rw [← π.commutes, MvPolynomial.algebraMap_eq, hΨ]
    simp [φ]
  let D : Derivation A B (ResidueField B) := Derivation.mk'
    { toFun := fun b ↦ (Ψ b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun a b ↦ by
        simp only [Algebra.smul_def, map_mul, snd_mul, hΨfst, hΨalg, RingHom.id_apply]
        simp only [r, RingHom.comp_apply, fst_inl, snd_inl, inlHom_apply, smul_zero, add_zero,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [IsScalarTower.algebraMap_apply A B (ResidueField B),
          IsLocalRing.ResidueField.algebraMap_eq] }
    (fun a b ↦ by
      simp [snd_mul, hΨfst, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq]
      ring)
  have hD : D = 0 := (KaehlerDifferential.linearMapEquivDerivation A B).symm.injective
    (LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, map_zero])
  apply hf0
  refine (Pi.basisFun (ResidueField B) (Fin n)).ext fun i ↦ ?_
  have := congr($hD (π (X i)))
  change (Ψ (π (X i))).snd = 0 at this
  rw [hΨ] at this
  simpa [φ, r, c] using this

/-- Let `B` be a formally unramified `A`-algebra which is a local ring, let
`π : A[X₁, …, Xₙ] → B` be an `A`-algebra homomorphism, `𝔪 = π⁻¹(𝔪_B)`, and assume the induced map
`R_𝔪 → B` is surjective. Then there are `P₁, …, Pₙ` in the kernel of `π` whose Jacobian
determinant `det (∂Pμ/∂Xν)` is a unit of `R_𝔪`. -/
theorem exists_isUnit_det_pderiv_of_formallyUnramified (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπ : Function.Surjective (IsLocalization.lift (M := ((maximalIdeal B).comap π).primeCompl)
      (S := Localization.AtPrime ((maximalIdeal B).comap π)) (g := π.toRingHom)
      (isUnit_of_mem_primeCompl_comap_maximalIdeal π))) :
    ∃ P : Fin n → MvPolynomial (Fin n) A, (∀ μ, π (P μ) = 0) ∧
      IsUnit (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime ((maximalIdeal B).comap π))
        (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det) := by
  classical
  obtain ⟨b, hbW, hspan, hli⟩ := exists_linearIndependent (ResidueField B)
    {w | ∃ P, π P = 0 ∧ (fun ν ↦ residue B (π (pderiv ν P))) = w}
  rw [span_residue_pderiv_eq_top π hπ] at hspan
  let β := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan])
  let e : Fin n ≃ b := (Pi.basisFun (ResidueField B) (Fin n)).indexEquiv β
  choose P hP hPv using fun μ ↦ hbW (e μ).2
  refine ⟨P, hP, ?_⟩
  refine IsLocalization.map_units (M := ((maximalIdeal B).comap π).primeCompl) _ ⟨_, ?_⟩
  have hrows : LinearIndependent (ResidueField B)
      (fun μ ↦ (Matrix.of fun μ ν ↦ residue B (π (pderiv ν (P μ)))) μ) := by
    have h := hli.comp e e.injective
    have hfun : ((↑) : b → _) ∘ e =
        fun μ ↦ (Matrix.of fun μ ν ↦ residue B (π (pderiv ν (P μ)))) μ :=
      funext fun μ ↦ (hPv μ).symm
    rwa [hfun] at h
  have hdet := Matrix.isUnit_iff_isUnit_det _ |>.mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)
  have hmap : (Matrix.of fun μ ν ↦ residue B (π (pderiv ν (P μ)))).det =
      ((residue B).comp π.toRingHom) (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det := by
    rw [RingHom.map_det]
    rfl
  rw [hmap] at hdet
  have hu : IsUnit (π.toRingHom (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det) :=
    IsUnit.of_map (residue B) _ hdet
  exact IsLocalRing.notMem_maximalIdeal.mpr hu

end MvPolynomial

namespace Algebra.IsUnramifiedLocal

open MvPolynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] {n : ℕ}

/-- Let `A → B` be an unramified (`Algebra.IsUnramifiedLocal`) and finitely generated
(`Algebra.IsFinitelyGeneratedLocal`) local homomorphism of local rings, let `R = A[X₁, …, Xₙ]`,
let `π : R → B` be an `A`-algebra homomorphism, `𝔪 = π⁻¹(𝔪_B)`, and assume the induced map
`R_𝔪 → B` is surjective. Then there are `P₁, …, Pₙ ∈ R` with `π(Pμ) = 0` such that
`det (∂Pμ/∂Xν)` is a unit of `R_𝔪`. -/
@[weil "lem_fk101_unramified_local_presentation_jacobian"]
theorem exists_isUnit_det_pderiv [IsUnramifiedLocal A B] (hfg : IsFinitelyGeneratedLocal A B)
    (π : MvPolynomial (Fin n) A →ₐ[A] B)
    (hπ : Function.Surjective (IsLocalization.lift (M := ((maximalIdeal B).comap π).primeCompl)
      (S := Localization.AtPrime ((maximalIdeal B).comap π)) (g := π.toRingHom)
      (isUnit_of_mem_primeCompl_comap_maximalIdeal π))) :
    ∃ P : Fin n → MvPolynomial (Fin n) A, (∀ μ, π (P μ) = 0) ∧
      IsUnit (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime ((maximalIdeal B).comap π))
        (Matrix.of fun μ ν ↦ pderiv ν (P μ)).det) :=
  have : EssFiniteType A B := hfg.2
  exists_isUnit_det_pderiv_of_formallyUnramified π hπ

end Algebra.IsUnramifiedLocal
