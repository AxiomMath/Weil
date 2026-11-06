module

public import Weil.Attr
public import Weil.Defs.HenselizationAndStrictHenselization
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The category of `φ`-diagrams is filtered

Let `A` be a noetherian local ring and `φ : A → k` a local homomorphism to a field. The category
`𝒟(A, φ)` of `φ`-diagrams (`HenselizationDiagram A φ`) is filtered:

* it is nonempty, since it contains `A` itself with `ψ = φ`;
* any two objects `(B₁, ψ₁)`, `(B₂, ψ₂)` map to the localization of `B₁ ⊗[A] B₂` at the kernel
  of `ψ₁ ⊗ ψ₂`, which is again local-étale over `A`;
* between two objects there is at most one morphism: two `A`-algebra maps `u, v : B₁ → B₂`
  compatible with the maps to `k` assemble into `B₁ ⊗[A] B₁ → B₂`, and the diagonal element of
  `B₁ ⊗[A] B₁` attached to the unramified algebra `B₁` (`Algebra.FormallyUnramified.elem`) is
  sent to a unit, which forces `u = v`.

## Main results

* `HenselizationDiagram.subsingleton_hom`: there is at most one morphism between two objects.
* `HenselizationDiagram.exists_hom_hom`: any two objects map to a common object.
* `HenselizationDiagram.nonempty`: `𝒟(A, φ)` is nonempty when `φ` is local.
* `HenselizationDiagram.isFiltered`: `𝒟(A, φ)` is filtered.

## Implementation notes

Objects of `𝒟(A, φ)` are constructed by `HenselizationDiagram.ofKer`, from a homomorphism
`g : A[X₁, …, Xₙ] / I → k` extending `φ`, localizing at `ker g`. The general statement
`HenselizationDiagram.exists_algHom_of_forall_exists_mul_eq` produces an object receiving a map
from any flat, formally unramified, essentially finite type `A`-algebra `T` with a map to `k`,
provided `T` is a localization of the image of a polynomial ring over `A`; both the object
`(A, φ)` and the common target of two objects are instances of it.

Filteredness without nonemptiness (`HenselizationDiagram.isFilteredOrEmpty`) holds for any `φ`;
the existence of an object forces `φ` to be local (`HenselizationDiagram.isLocalHom_φ`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.1
-/

@[expose] public section

open CategoryTheory IsLocalRing TensorProduct

universe u v

namespace HenselizationDiagram

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
  {k : Type v} [Field k] {φ : A →+* k}

section Unique

variable (D : HenselizationDiagram A φ)

/-- The ring of a `φ`-diagram is essentially of finite type over `A`. -/
instance essFiniteType : Algebra.EssFiniteType A D.Ring :=
  RingHom.essFiniteType_algebraMap.1 D.isEtaleLocalHom.2.2

/-- The ring of a `φ`-diagram is formally unramified over `A`. -/
instance formallyUnramified : Algebra.FormallyUnramified A D.Ring :=
  RingHom.formallyUnramified_algebraMap.1 D.isEtaleLocalHom.2.1

/-- The ring of a `φ`-diagram is flat over `A`. -/
instance flat : Module.Flat A D.Ring :=
  RingHom.flat_algebraMap_iff.1 D.isEtaleLocalHom.1

/-- Two `A`-algebra homomorphisms `B₁ → B₂` between `φ`-diagrams compatible with the maps to `k`
coincide. -/
theorem algHom_eq_of_ψ_comp {D₁ D₂ : HenselizationDiagram A φ} (f g : D₁.Ring →ₐ[A] D₂.Ring)
    (hf : ∀ x, D₂.ψ (f x) = D₁.ψ x) (hg : ∀ x, D₂.ψ (g x) = D₁.ψ x) : f = g := by
  set θ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) with hθ
  set e := Algebra.FormallyUnramified.elem A D₁.Ring with he
  have hcomm : ∀ t, D₂.ψ (θ t) = D₁.ψ (Algebra.TensorProduct.lmul' A t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hθ, hf, hg]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hunit : IsUnit (θ e) := by
    by_contra h
    have h1 : D₂.ψ (θ e) = 0 := by
      rw [← RingHom.mem_ker, ker_ψ]; exact h
    have h2 := Algebra.FormallyUnramified.lmul_elem (R := A) (S := D₁.Ring)
    rw [hcomm, he] at h1
    erw [h2] at h1
    rw [map_one] at h1
    exact one_ne_zero h1
  refine AlgHom.ext fun x => ?_
  have key := congrArg θ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) (S := D₁.Ring) x)
  simp only [map_mul, hθ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at key
  exact (hunit.mul_right_cancel key).symm

/-- Between two `φ`-diagrams there is at most one morphism. -/
instance subsingleton_hom (D₁ D₂ : HenselizationDiagram A φ) : Subsingleton (D₁ ⟶ D₂) :=
  ⟨fun f g => hom_ext (algHom_eq_of_ψ_comp _ _ f.ψ_apply g.ψ_apply)⟩

end Unique

section Construction

variable {R : Type u} [CommRing R] (g : R →+* k) [(RingHom.ker g).IsPrime]

/-- The map `R_q → k` induced by a homomorphism `g : R → k` to a field, where `q = ker g`. -/
noncomputable def liftKer : Localization.AtPrime (RingHom.ker g) →+* k :=
  IsLocalization.lift (M := (RingHom.ker g).primeCompl) (S := Localization.AtPrime (RingHom.ker g))
    (g := g) fun y => isUnit_iff_ne_zero.2 fun h => y.2 (RingHom.mem_ker.2 h)

/-- The map `R_q → k` induced by `g` restricts to `g` on `R`. -/
@[simp]
theorem liftKer_algebraMap (r : R) :
    liftKer g (algebraMap R (Localization.AtPrime (RingHom.ker g)) r) = g r :=
  IsLocalization.lift_eq _ r

/-- The map `R_q → k` induced by `g` is a local homomorphism. -/
instance isLocalHom_liftKer : IsLocalHom (liftKer g) where
  map_nonunit x hx := by
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker g).primeCompl x
    have hspec := IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker g)) r s
    have hs : g s ≠ 0 := fun h => s.2 (RingHom.mem_ker.2 h)
    have hr : r ∈ (RingHom.ker g).primeCompl := by
      intro hr
      have h1 := congrArg (liftKer g) hspec
      rw [map_mul, liftKer_algebraMap, liftKer_algebraMap, RingHom.mem_ker.1 hr] at h1
      exact hx.ne_zero (by simpa [hs] using h1)
    have hu : IsUnit (algebraMap R (Localization.AtPrime (RingHom.ker g)) r) :=
      IsLocalization.map_units _ (⟨r, hr⟩ : (RingHom.ker g).primeCompl)
    rw [← hspec] at hu
    exact isUnit_of_mul_isUnit_left hu

variable [IsLocalHom φ] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) A))
  (g : MvPolynomial (Fin n) A ⧸ I →+* k) [(RingHom.ker g).IsPrime]

/-- The `φ`-diagram `((A[X₁, …, Xₙ] / I)_q, ψ)` attached to a homomorphism
`g : A[X₁, …, Xₙ] / I → k` extending `φ`, with `q = ker g`, when `A → (A[X₁, …, Xₙ] / I)_q` is
flat, formally unramified and essentially of finite type. -/
noncomputable def ofKer (hg : ∀ a, g (algebraMap A _ a) = φ a)
    [Module.Flat A (Localization.AtPrime (RingHom.ker g))]
    [Algebra.FormallyUnramified A (Localization.AtPrime (RingHom.ker g))]
    [Algebra.EssFiniteType A (Localization.AtPrime (RingHom.ker g))] :
    HenselizationDiagram A φ :=
  have hcomp : (liftKer g).comp (algebraMap A (Localization.AtPrime (RingHom.ker g))) = φ :=
    RingHom.ext fun a => by
      simp [IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A ⧸ I)
        (Localization.AtPrime (RingHom.ker g)), hg]
  have : IsLocalHom ((liftKer g).comp
      (algebraMap A (Localization.AtPrime (RingHom.ker g)))) := by
    rw [hcomp]; infer_instance
  haveI := isLocalHom_of_comp (algebraMap A (Localization.AtPrime (RingHom.ker g))) (liftKer g)
  { n := n
    I := I
    q := RingHom.ker g
    isEtaleLocalHom := ⟨RingHom.flat_algebraMap_iff.2 inferInstance,
      RingHom.formallyUnramified_algebraMap.2 inferInstance,
      RingHom.essFiniteType_algebraMap.2 inferInstance⟩
    ψ := liftKer g
    ψ_comp_algebraMap := hcomp }

omit [IsLocalHom φ] in
/-- Every flat, formally unramified, essentially finite type `A`-algebra `T` with a map
`χ : T → k` extending `φ`, which is a localization of the image of a polynomial ring over `A`,
maps to a `φ`-diagram compatibly with the maps to `k`. -/
theorem exists_algHom_of_forall_exists_mul_eq [IsLocalHom φ] {T : Type u} [CommRing T]
    [Algebra A T] [Module.Flat A T] [Algebra.FormallyUnramified A T] [Algebra.EssFiniteType A T]
    (χ : T →+* k) (hχ : ∀ a, χ (algebraMap A T a) = φ a) {n : ℕ}
    (ρ : MvPolynomial (Fin n) A →ₐ[A] T)
    (hρ : ∀ t, ∃ a m, IsUnit (ρ m) ∧ t * ρ m = ρ a) :
    ∃ (D : HenselizationDiagram A φ) (u : T →ₐ[A] D.Ring), ∀ t, D.ψ (u t) = χ t := by
  let R := MvPolynomial (Fin n) A ⧸ RingHom.ker ρ
  let ρ' : R →ₐ[A] T := Ideal.kerLiftAlg ρ
  have hρ' : ∀ p, ρ' (Ideal.Quotient.mk _ p) = ρ p := Ideal.kerLiftAlg_mk ρ
  have hinj : Function.Injective ρ' := Ideal.kerLiftAlg_injective ρ
  let g : R →+* k := χ.comp ρ'.toRingHom
  have : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  let : Algebra R T := ρ'.toRingHom.toAlgebra
  have halg : ∀ r, algebraMap R T r = ρ' r := fun _ => rfl
  have : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq fun a => (ρ'.commutes a).symm
  let M : Submonoid R := (IsUnit.submonoid T).comap ρ'.toRingHom
  have : IsLocalization M T :=
    { map_units := fun y => y.2
      surj := fun z => by
        obtain ⟨a, m, hm, h⟩ := hρ z
        refine ⟨(Ideal.Quotient.mk _ a, ⟨Ideal.Quotient.mk _ m, ?_⟩), ?_⟩
        · change IsUnit (ρ' _); rwa [hρ']
        · simp only [halg, hρ']; exact h
      exists_of_eq := fun {x y} h => ⟨1, by rw [hinj h]⟩ }
  let N := (RingHom.ker g).primeCompl
  have hle : M ≤ N := fun m hm h =>
    (hm.map χ).ne_zero (RingHom.mem_ker.1 h)
  let B := Localization.AtPrime (RingHom.ker g)
  let : Algebra T B := IsLocalization.localizationAlgebraOfSubmonoidLe T B M N hle
  have : IsScalarTower R T B :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T B M N hle
  have : IsLocalization (Algebra.algebraMapSubmonoid T N) B :=
    IsLocalization.isLocalization_of_submonoid_le T B M N hle
  have : IsScalarTower A T B := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A R B, IsScalarTower.algebraMap_apply A R T,
      ← IsScalarTower.algebraMap_apply R T B]
  have : Module.Flat T B := IsLocalization.flat B (Algebra.algebraMapSubmonoid T N)
  have : Module.Flat A B := Module.Flat.trans A T B
  have : Algebra.FormallyUnramified T B :=
    .of_isLocalization (Algebra.algebraMapSubmonoid T N)
  have : Algebra.FormallyUnramified A B := .comp A T B
  have : Algebra.EssFiniteType T B := .of_isLocalization B (Algebra.algebraMapSubmonoid T N)
  have : Algebra.EssFiniteType A B := .comp A T B
  have hg : ∀ a, g (algebraMap A R a) = φ a := fun a => by
    simp only [g, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AlgHom.commutes, hχ]
  have hψ : (liftKer g).comp (algebraMap T B) = χ :=
    IsLocalization.ringHom_ext M <| RingHom.ext fun r => by
      simp only [RingHom.coe_comp, Function.comp_apply, ← IsScalarTower.algebraMap_apply]
      exact liftKer_algebraMap g r
  exact ⟨ofKer n (RingHom.ker ρ) g hg, IsScalarTower.toAlgHom A T B,
    fun t => RingHom.congr_fun hψ t⟩

end Construction

section Filtered

open MvPolynomial

/-- The source's object `(A, φ)`: `𝒟(A, φ)` is nonempty when `φ` is a local homomorphism. -/
theorem nonempty [IsLocalHom φ] : Nonempty (HenselizationDiagram A φ) := by
  obtain ⟨D, -, -⟩ := exists_algHom_of_forall_exists_mul_eq (T := A) φ (fun _ => rfl)
    (MvPolynomial.aeval (Fin.elim0 : Fin 0 → A))
    fun t => ⟨C t, 1, by simp, by simp⟩
  exact ⟨D⟩

/-- The tensor product `B₁ ⊗[A] B₂` of the rings of two `φ`-diagrams, with the module structures
coming from the algebra structures. -/
abbrev TensorRing (D₁ D₂ : HenselizationDiagram A φ) : Type u :=
  (fun (B C : Type u) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] => B ⊗[A] C)
    D₁.Ring D₂.Ring

/-- `B₁ ⊗[A] B₂` is formally unramified over `A`. -/
instance formallyUnramified_tensorProduct (D₁ D₂ : HenselizationDiagram A φ) :
    Algebra.FormallyUnramified A (D₁.TensorRing D₂) :=
  .comp A D₁.Ring _

/-- `B₁ ⊗[A] B₂` is essentially of finite type over `A`. -/
instance essFiniteType_tensorProduct (D₁ D₂ : HenselizationDiagram A φ) :
    Algebra.EssFiniteType A (D₁.TensorRing D₂) :=
  .comp A D₁.Ring _

/-- Any two `φ`-diagrams map to a common one, namely the localization of `B₁ ⊗[A] B₂` at the
kernel of `ψ₁ ⊗ ψ₂`. -/
theorem exists_hom_hom (D₁ D₂ : HenselizationDiagram A φ) :
    ∃ (D₃ : HenselizationDiagram A φ) (_ : D₁ ⟶ D₃) (_ : D₂ ⟶ D₃), True := by
  have := D₁.isLocalHom_φ
  let : Algebra A k := φ.toAlgebra
  let ψ₁ : D₁.Ring →ₐ[A] k := { D₁.ψ with commutes' := D₁.ψ_algebraMap }
  let ψ₂ : D₂.Ring →ₐ[A] k := { D₂.ψ with commutes' := D₂.ψ_algebraMap }
  let χ : (D₁.TensorRing D₂) →ₐ[A] k := Algebra.TensorProduct.lift ψ₁ ψ₂ fun _ _ => Commute.all _ _
  let e₁ : Fin D₁.n → (D₁.TensorRing D₂) := fun i =>
    algebraMap _ D₁.Ring (Ideal.Quotient.mk D₁.I (X i)) ⊗ₜ (1 : D₂.Ring)
  let e₂ : Fin D₂.n → (D₁.TensorRing D₂) := fun j =>
    (1 : D₁.Ring) ⊗ₜ algebraMap _ D₂.Ring (Ideal.Quotient.mk D₂.I (X j))
  let ρ : MvPolynomial (Fin (D₁.n + D₂.n)) A →ₐ[A] (D₁.TensorRing D₂) := aeval (Fin.append e₁ e₂)
  have h₁ : ∀ p, ρ (rename (Fin.castAdd D₂.n) p) =
      algebraMap _ D₁.Ring (Ideal.Quotient.mk D₁.I p) ⊗ₜ (1 : D₂.Ring) := by
    intro p
    have : ρ.comp (rename (Fin.castAdd D₂.n)) =
        (Algebra.TensorProduct.includeLeft (S := A)).comp
          ((IsScalarTower.toAlgHom A _ D₁.Ring).comp (Ideal.Quotient.mkₐ A D₁.I)) :=
      algHom_ext fun i => by simp [ρ, e₁, Fin.append_left]
    simpa using AlgHom.congr_fun this p
  have h₂ : ∀ p, ρ (rename (Fin.natAdd D₁.n) p) =
      (1 : D₁.Ring) ⊗ₜ algebraMap _ D₂.Ring (Ideal.Quotient.mk D₂.I p) := by
    intro p
    have : ρ.comp (rename (Fin.natAdd D₁.n)) =
        (Algebra.TensorProduct.includeRight).comp
          ((IsScalarTower.toAlgHom A _ D₂.Ring).comp (Ideal.Quotient.mkₐ A D₂.I)) :=
      algHom_ext fun i => by simp [ρ, e₂, Fin.append_right]
    simpa using AlgHom.congr_fun this p
  have hloc : ∀ (D : HenselizationDiagram A φ) (x : D.Ring), ∃ p p',
      IsUnit (algebraMap _ D.Ring (Ideal.Quotient.mk D.I p')) ∧
        x * algebraMap _ D.Ring (Ideal.Quotient.mk D.I p') =
          algebraMap _ D.Ring (Ideal.Quotient.mk D.I p) := by
    intro D x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective D.q.primeCompl x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨p', hp'⟩ := Ideal.Quotient.mk_surjective (s : MvPolynomial (Fin D.n) A ⧸ D.I)
    refine ⟨p, p', ?_, ?_⟩
    · rw [hp']; exact IsLocalization.map_units _ s
    · rw [hp']; exact IsLocalization.mk'_spec _ _ _
  have hρ : ∀ t, ∃ a m, IsUnit (ρ m) ∧ t * ρ m = ρ a := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, 1, by simp, by simp⟩
    | tmul x y =>
      obtain ⟨p₁, p₁', hu₁, hx⟩ := hloc D₁ x
      obtain ⟨p₂, p₂', hu₂, hy⟩ := hloc D₂ y
      refine ⟨rename (Fin.castAdd D₂.n) p₁ * rename (Fin.natAdd D₁.n) p₂,
        rename (Fin.castAdd D₂.n) p₁' * rename (Fin.natAdd D₁.n) p₂', ?_, ?_⟩
      · rw [map_mul, h₁, h₂]
        exact (hu₁.map (Algebra.TensorProduct.includeLeft (S := A) (B := D₂.Ring))).mul
          (hu₂.map (Algebra.TensorProduct.includeRight (A := D₁.Ring)))
      · rw [map_mul, map_mul, h₁, h₁, h₂, h₂]
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hx, hy]
    | add x y hx hy =>
      obtain ⟨a, m, hm, h⟩ := hx
      obtain ⟨a', m', hm', h'⟩ := hy
      refine ⟨a * m' + a' * m, m * m', by rw [map_mul]; exact hm.mul hm', ?_⟩
      rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']
      ring
  obtain ⟨D₃, u, hu⟩ := exists_algHom_of_forall_exists_mul_eq χ.toRingHom (fun a => χ.commutes a)
    ρ hρ
  exact ⟨D₃, homMk (u.comp Algebra.TensorProduct.includeLeft) (fun x => by simp [hu, χ, ψ₁]),
    homMk (u.comp Algebra.TensorProduct.includeRight) (fun x => by simp [hu, χ, ψ₂]), trivial⟩

/-- Any two objects of `𝒟(A, φ)` map to a common object, and parallel morphisms are equal. -/
instance isFilteredOrEmpty : IsFilteredOrEmpty (HenselizationDiagram A φ) where
  cocone_objs D₁ D₂ := exists_hom_hom D₁ D₂
  cocone_maps {_ Y} _ _ := ⟨Y, 𝟙 Y, Subsingleton.elim _ _⟩

/-- **The category `𝒟(A, φ)` of `φ`-diagrams is filtered**, for a local homomorphism `φ` from a
noetherian local ring `A` to a field. -/
@[weil "lem_fk101_henselization_diagram_category_filtered"]
instance isFiltered [IsLocalHom φ] : IsFiltered (HenselizationDiagram A φ) where
  nonempty := nonempty

end Filtered

end HenselizationDiagram
