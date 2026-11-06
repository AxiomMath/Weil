module

public import Weil.Attr
public import WeilFrontier.Defs.HenselizationAndStrictHenselization
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.FiniteType

/-!
# Common targets in the category of `φ`-diagrams

Let `A` be a noetherian local ring and `φ : A → k` a local homomorphism to a field. Any two
objects `(B₁, ψ₁)`, `(B₂, ψ₂)` of the category `𝒟(A, φ)` of `φ`-diagrams admit morphisms to a
common object `(B₃, ψ₃)`. One takes for `B₃` the localization of `B₁ ⊗[A] B₂` at the kernel `𝔭`
of the homomorphism `χ : B₁ ⊗[A] B₂ → k`, `b₁ ⊗ b₂ ↦ ψ₁(b₁) ψ₂(b₂)`; `ψ₃` is the map induced
by `χ`. The homomorphism `A → B₃` is flat, formally unramified and essentially of finite type,
as each of these properties is stable under tensor products and localizations, so it is
local-étale.

## Main results

* `Algebra.exists_algEquiv_localization_atPrime_mvPolynomial_quotient`: a local `R`-algebra
  essentially of finite type is `R`-isomorphic to `(R[X₁, …, Xₙ] / I)_q` for some `n`, an ideal
  `I` and a prime `q`.
* `HenselizationDiagram.exists_algEquiv_of_isEtaleLocalHom`: a local-étale `A`-algebra `B` with
  a local homomorphism `ψ : B → k` restricting to `φ` underlies a `φ`-diagram.
* `HenselizationDiagram.exists_algHom_of_formallyUnramified`: the localization of a flat,
  formally unramified `A`-algebra `T` of essentially finite type at the kernel of a homomorphism
  `χ : T → k` restricting to `φ` underlies a `φ`-diagram receiving `T`.
* `HenselizationDiagram.exists_algHom_and_algHom`: two such algebras map compatibly to a common
  `φ`-diagram, through their tensor product.
* `HenselizationDiagram.exists_hom_and_hom`: any two `φ`-diagrams map to a common one.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

open CategoryTheory IsLocalRing TensorProduct

universe u v w

namespace Algebra

/-- A local `R`-algebra essentially of finite type is `R`-isomorphic to the localization
`(R[X₁, …, Xₙ] / I)_q` of a quotient of a polynomial ring at a prime ideal. -/
theorem exists_algEquiv_localization_atPrime_mvPolynomial_quotient {R : Type u} {B : Type v}
    [CommRing R] [CommRing B] [Algebra R B] [IsLocalRing B] [EssFiniteType R B] :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) (q : Ideal (MvPolynomial (Fin n) R ⧸ I))
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] B) := by
  obtain ⟨C, _, _, _, q, _, ⟨e⟩⟩ :=
    essFiniteType_iff_exists_algEquiv_localization_atPrime.mp ‹EssFiniteType R B›
  obtain ⟨n, f, hf⟩ := FiniteType.iff_quotient_mvPolynomial''.mp ‹FiniteType R C›
  let g := Ideal.quotientKerAlgEquivOfSurjective hf
  exact ⟨n, RingHom.ker f, q.comap g, Ideal.comap_isPrime _ _,
    ⟨(Localization.localAlgEquiv _ q g rfl).trans e⟩⟩

end Algebra

namespace HenselizationDiagram

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {k : Type v} [Field k] {φ : A →+* k}

variable (φ) in
/-- A local-étale `A`-algebra `B` together with a local homomorphism `ψ : B → k` restricting to
`φ` on `A` underlies a `φ`-diagram: there is a `φ`-diagram `D` with an `A`-algebra isomorphism
`D.Ring ≃ₐ[A] B` carrying `D.ψ` to `ψ`. -/
theorem exists_algEquiv_of_isEtaleLocalHom (B : Type u) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    (hB : (algebraMap A B).IsEtaleLocalHom) (ψ : B →+* k) [IsLocalHom ψ]
    (hψ : ψ.comp (algebraMap A B) = φ) :
    ∃ (D : HenselizationDiagram A φ) (e : D.Ring ≃ₐ[A] B), D.ψ = ψ.comp e.toRingHom := by
  obtain ⟨hflat, hunr, hft⟩ := hB
  rw [RingHom.flat_algebraMap_iff] at hflat
  rw [RingHom.formallyUnramified_algebraMap] at hunr
  rw [RingHom.essFiniteType_algebraMap] at hft
  obtain ⟨n, I, q, _, ⟨e⟩⟩ := Algebra.exists_algEquiv_localization_atPrime_mvPolynomial_quotient
    (R := A) (B := B)
  have hcomp : (ψ.comp e.toRingHom).comp (algebraMap A (Localization.AtPrime q)) = φ := by
    rw [← hψ]
    ext a
    simp
  have : IsLocalHom φ := by
    rw [← hψ]
    infer_instance
  have : IsLocalHom ((ψ.comp e.toRingHom).comp (algebraMap A (Localization.AtPrime q))) := by
    rw [hcomp]
    infer_instance
  have : IsLocalHom (algebraMap A (Localization.AtPrime q)) :=
    isLocalHom_of_comp _ (ψ.comp e.toRingHom)
  have : Module.Flat A (Localization.AtPrime q) := Module.Flat.of_linearEquiv e.toLinearEquiv
  have : Algebra.FormallyUnramified A (Localization.AtPrime q) := .of_equiv e.symm
  have : Algebra.EssFiniteType A (Localization.AtPrime q) :=
    .of_surjective e.symm.toAlgHom e.symm.surjective
  have : IsLocalHom (ψ.comp e.toRingHom) := by
    have : IsLocalHom e.toRingHom := ⟨fun x hx => by
      simpa using hx.map e.symm.toRingEquiv.toRingHom⟩
    infer_instance
  refine ⟨{ n := n, I := I, q := q
            isEtaleLocalHom := ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
              RingHom.formallyUnramified_algebraMap.mpr inferInstance,
              RingHom.essFiniteType_algebraMap.mpr inferInstance⟩
            ψ := ψ.comp e.toRingHom
            ψ_comp_algebraMap := hcomp }, e, rfl⟩

variable (φ) in
/-- Let `T` be a flat, formally unramified `A`-algebra essentially of finite type, and
`χ : T → k` a homomorphism restricting to `φ` on `A`. Then the localization of `T` at the prime
`ker χ` underlies a `φ`-diagram `D`, and the canonical map `T → D.Ring` is compatible with `χ`
and `D.ψ`. -/
theorem exists_algHom_of_formallyUnramified (T : Type u) [CommRing T] [Algebra A T]
    [Module.Flat A T] [Algebra.FormallyUnramified A T] [Algebra.EssFiniteType A T]
    [IsLocalHom φ] (χ : T →+* k) (hχ : χ.comp (algebraMap A T) = φ) :
    ∃ (D : HenselizationDiagram A φ) (u : T →ₐ[A] D.Ring), ∀ x, D.ψ (u x) = χ x := by
  let p : Ideal T := RingHom.ker χ
  have : p.IsPrime := RingHom.ker_isPrime _
  let ψ₃ : Localization.AtPrime p →+* k :=
    IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p) (g := χ)
      (fun y => isUnit_iff_ne_zero.mpr y.2)
  have hψ₃ : ∀ x, ψ₃ (algebraMap T (Localization.AtPrime p) x) = χ x :=
    fun x => IsLocalization.lift_eq _ _
  have : IsLocalHom ψ₃ := by
    refine ⟨fun x hx => ?_⟩
    by_contra h
    have hm : x ∈ maximalIdeal (Localization.AtPrime p) := h
    rw [← Localization.AtPrime.map_eq_maximalIdeal] at hm
    have hle : p.map (algebraMap T (Localization.AtPrime p)) ≤ RingHom.ker ψ₃ := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap, RingHom.mem_ker, hψ₃]
      exact ha
    have h0 : ψ₃ x = 0 := hle hm
    rw [h0] at hx
    exact not_isUnit_zero hx
  have hcomp : ψ₃.comp (algebraMap A (Localization.AtPrime p)) = φ := by
    rw [← hχ]
    ext a
    simp only [RingHom.comp_apply, IsScalarTower.algebraMap_apply A T (Localization.AtPrime p),
      hψ₃]
  have : IsLocalHom (ψ₃.comp (algebraMap A (Localization.AtPrime p))) := by
    rw [hcomp]
    infer_instance
  have : IsLocalHom (algebraMap A (Localization.AtPrime p)) := isLocalHom_of_comp _ ψ₃
  have : Algebra.EssFiniteType T (Localization.AtPrime p) :=
    .of_isLocalization (Localization.AtPrime p) p.primeCompl
  have : Algebra.EssFiniteType A (Localization.AtPrime p) :=
    Algebra.EssFiniteType.comp A T (Localization.AtPrime p)
  have : IsNoetherianRing (Localization.AtPrime p) :=
    Algebra.EssFiniteType.isNoetherianRing A (Localization.AtPrime p)
  have : Algebra.FormallyUnramified T (Localization.AtPrime p) := .of_isLocalization p.primeCompl
  have : Algebra.FormallyUnramified A (Localization.AtPrime p) :=
    Algebra.FormallyUnramified.comp A T (Localization.AtPrime p)
  have : Module.Flat T (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) p.primeCompl
  have : Module.Flat A (Localization.AtPrime p) := Module.Flat.trans A T (Localization.AtPrime p)
  have hB : (algebraMap A (Localization.AtPrime p)).IsEtaleLocalHom :=
    ⟨RingHom.flat_algebraMap_iff.mpr inferInstance,
      RingHom.formallyUnramified_algebraMap.mpr inferInstance,
      RingHom.essFiniteType_algebraMap.mpr inferInstance⟩
  obtain ⟨D, e, hD⟩ := exists_algEquiv_of_isEtaleLocalHom φ _ hB ψ₃ hcomp
  refine ⟨D, e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A T (Localization.AtPrime p)),
    fun x => ?_⟩
  rw [hD]
  simp [hψ₃]

variable (φ) in
/-- Let `B₁`, `B₂` be flat, formally unramified `A`-algebras essentially of finite type, with
homomorphisms `ψᵢ : Bᵢ → k` restricting to `φ` on `A`. Then there are a `φ`-diagram `D` and
`A`-algebra homomorphisms `uᵢ : Bᵢ → D.Ring` with `D.ψ ∘ uᵢ = ψᵢ`. -/
theorem exists_algHom_and_algHom (B₁ B₂ : Type u) [CommRing B₁] [CommRing B₂] [Algebra A B₁]
    [Algebra A B₂] [Module.Flat A B₁] [Module.Flat A B₂] [Algebra.FormallyUnramified A B₁]
    [Algebra.FormallyUnramified A B₂] [Algebra.EssFiniteType A B₁] [Algebra.EssFiniteType A B₂]
    [IsLocalHom φ] (ψ₁ : B₁ →+* k) (ψ₂ : B₂ →+* k) (h₁ : ψ₁.comp (algebraMap A B₁) = φ)
    (h₂ : ψ₂.comp (algebraMap A B₂) = φ) :
    ∃ (D : HenselizationDiagram A φ) (u₁ : B₁ →ₐ[A] D.Ring) (u₂ : B₂ →ₐ[A] D.Ring),
      (∀ x, D.ψ (u₁ x) = ψ₁ x) ∧ ∀ x, D.ψ (u₂ x) = ψ₂ x := by
  have : Algebra.EssFiniteType A (B₁ ⊗[A] B₂) := Algebra.EssFiniteType.comp A B₁ (B₁ ⊗[A] B₂)
  have : Algebra.FormallyUnramified A (B₁ ⊗[A] B₂) :=
    Algebra.FormallyUnramified.comp A B₁ (B₁ ⊗[A] B₂)
  let _ : Algebra A k := φ.toAlgebra
  let χ₁ : B₁ →ₐ[A] k := { ψ₁ with commutes' := fun a => RingHom.congr_fun h₁ a }
  let χ₂ : B₂ →ₐ[A] k := { ψ₂ with commutes' := fun a => RingHom.congr_fun h₂ a }
  let χ : B₁ ⊗[A] B₂ →ₐ[A] k := Algebra.TensorProduct.lift χ₁ χ₂ (fun _ _ => Commute.all _ _)
  obtain ⟨D, u, hu⟩ := exists_algHom_of_formallyUnramified φ (B₁ ⊗[A] B₂) χ.toRingHom
    (by ext a; exact χ.commutes a)
  refine ⟨D, u.comp Algebra.TensorProduct.includeLeft, u.comp Algebra.TensorProduct.includeRight,
    fun x => ?_, fun x => ?_⟩
  · simp [hu, χ, χ₁, χ₂]
  · simp [hu, χ, χ₁, χ₂]

/-- **Common targets in `𝒟(A, φ)`.** For any two `φ`-diagrams `D₁`, `D₂` there are a `φ`-diagram
`D₃` and morphisms `D₁ ⟶ D₃`, `D₂ ⟶ D₃`. -/
@[weil "lem_fk101_henselization_diagram_common_target"]
theorem exists_hom_and_hom (D₁ D₂ : HenselizationDiagram A φ) :
    ∃ D₃ : HenselizationDiagram A φ, Nonempty (D₁ ⟶ D₃) ∧ Nonempty (D₂ ⟶ D₃) := by
  have : Module.Flat A D₁.Ring := RingHom.flat_algebraMap_iff.mp D₁.isEtaleLocalHom.1
  have : Algebra.FormallyUnramified A D₁.Ring :=
    RingHom.formallyUnramified_algebraMap.mp D₁.isEtaleLocalHom.2.1
  have : Algebra.EssFiniteType A D₁.Ring :=
    RingHom.essFiniteType_algebraMap.mp D₁.isEtaleLocalHom.2.2
  have : Module.Flat A D₂.Ring := RingHom.flat_algebraMap_iff.mp D₂.isEtaleLocalHom.1
  have : Algebra.FormallyUnramified A D₂.Ring :=
    RingHom.formallyUnramified_algebraMap.mp D₂.isEtaleLocalHom.2.1
  have : Algebra.EssFiniteType A D₂.Ring :=
    RingHom.essFiniteType_algebraMap.mp D₂.isEtaleLocalHom.2.2
  have : IsLocalHom φ := D₁.isLocalHom_φ
  obtain ⟨D₃, u₁, u₂, hu₁, hu₂⟩ := exists_algHom_and_algHom φ D₁.Ring D₂.Ring D₁.ψ D₂.ψ
    D₁.ψ_comp_algebraMap D₂.ψ_comp_algebraMap
  exact ⟨D₃, ⟨homMk u₁ hu₁⟩, ⟨homMk u₂ hu₂⟩⟩

end HenselizationDiagram
