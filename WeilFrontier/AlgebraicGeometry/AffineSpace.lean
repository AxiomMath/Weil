module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Weil.Attr

/-!
# Factoring an affine morphism of finite type into morphisms of relative dimension one

Let `A` be a commutative ring and `f : X ⟶ Spec A` an affine morphism of finite type. Then `X`
is affine, `Γ(X, ⊤)` is a finitely generated `A`-algebra, and a choice of `n` generators gives a
closed immersion `f₀ : X ⟶ 𝔸ⁿ_A = Spec A[x₁, …, xₙ]` over `Spec A`. Hence `f` factors as
`f = f₁ ∘ f₂ ∘ ⋯ ∘ fₙ ∘ f₀`, where `f_v : 𝔸^v_A ⟶ 𝔸^{v-1}_A` is the projection forgetting the
last coordinate. Each projection is affine of finite type, and its fibre over any point
`Spec Ω ⟶ 𝔸^{v-1}_A` with values in a field `Ω` is the affine line `𝔸¹_Ω`, of dimension `1`;
the fibres of the closed immersion `f₀` are empty or a single point, of dimension `≤ 0`.

## Main definitions

* `AlgebraicGeometry.mvPolynomialSpecProjLast A v`: the projection
  `Spec A[x₀, …, x_v] ⟶ Spec A[x₀, …, x_{v-1}]` forgetting the last coordinate.
* `AlgebraicGeometry.mvPolynomialSpecProjChain A n`: the composite of these projections
  `Spec A[x₀, …, x_{n-1}] ⟶ ⋯ ⟶ Spec A[∅] ⟶ Spec A`.

## Main results

* `AlgebraicGeometry.mvPolynomialSpecProjChain_eq`: the composite of the projections is the
  structure morphism of affine `n`-space.
* `AlgebraicGeometry.topologicalKrullDim_pullback_mvPolynomialSpecProjLast`: every fibre of a
  coordinate projection over a field-valued point has dimension `1`.
* `AlgebraicGeometry.topologicalKrullDim_pullback_le_zero_of_isClosedImmersion`: every fibre of
  a closed immersion over a field-valued point has dimension `≤ 0`.
* `AlgebraicGeometry.exists_isClosedImmersion_comp_mvPolynomialSpecProjChain`: the
  factorization of an affine morphism of finite type to `Spec A`.

## Implementation notes

Affine `v`-space over `A` is the affine scheme `Spec A[x₀, …, x_{v-1}]`
(`MvPolynomial (Fin v) A`), which Mathlib's `AlgebraicGeometry.AffineSpace` identifies with
`𝔸(Fin v; Spec A)`. The space `𝔸⁰_A = Spec A[∅]` is not literally `Spec A`: the chain of
projections ends with the isomorphism `Spec A[∅] ⟶ Spec A` (`mvPolynomialSpecProjChain A 0`),
so the source's `f₁ : 𝔸¹_A ⟶ 𝔸⁰_A = S` is here `mvPolynomialSpecProjLast A 0` followed by that
isomorphism. The dimension of a scheme is the Krull dimension of its underlying space. The fibre
statements are proved for points with values in an arbitrary field, in particular for all
geometric points.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.8.8, p. 94.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- The projection `𝔸^{v+1}_A = Spec A[x₀, …, x_v] ⟶ 𝔸^v_A = Spec A[x₀, …, x_{v-1}]` forgetting
the last coordinate; it corresponds to the inclusion `A[x₀, …, x_{v-1}] ⊆ A[x₀, …, x_v]`. -/
noncomputable def mvPolynomialSpecProjLast (v : ℕ) :
    Spec (.of (MvPolynomial (Fin (v + 1)) A)) ⟶ Spec (.of (MvPolynomial (Fin v) A)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := A) Fin.castSucc).toRingHom)

/-- The composite `𝔸ⁿ_A ⟶ 𝔸ⁿ⁻¹_A ⟶ ⋯ ⟶ 𝔸⁰_A ⟶ Spec A` of the projections forgetting the last
coordinate, ending with the isomorphism `Spec A[∅] ⟶ Spec A`. -/
noncomputable def mvPolynomialSpecProjChain :
    (n : ℕ) → Spec (.of (MvPolynomial (Fin n) A)) ⟶ Spec (.of A)
  | 0 => Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin 0) A)))
  | n + 1 => mvPolynomialSpecProjLast A n ≫ mvPolynomialSpecProjChain n

/-- The composite of the coordinate projections is the structure morphism `𝔸ⁿ_A ⟶ Spec A`. -/
theorem mvPolynomialSpecProjChain_eq (n : ℕ) :
    mvPolynomialSpecProjChain A n =
      Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mvPolynomialSpecProjChain, ih, mvPolynomialSpecProjLast, ← Spec.map_comp]
    congr 1
    ext a
    simp [MvPolynomial.algebraMap_eq]

instance isIso_mvPolynomialSpecProjChain_zero : IsIso (mvPolynomialSpecProjChain A 0) := by
  have h : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin 0) A)) =
      (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv.toCommRingCatIso.hom := by
    ext a
    simp [MvPolynomial.algebraMap_eq]
  rw [mvPolynomialSpecProjChain, h]
  infer_instance

instance isAffineHom_mvPolynomialSpecProjLast (v : ℕ) :
    IsAffineHom (mvPolynomialSpecProjLast A v) :=
  isAffineHom_of_isAffine _

instance locallyOfFiniteType_mvPolynomialSpecProjLast (v : ℕ) :
    LocallyOfFiniteType (mvPolynomialSpecProjLast A v) := by
  rw [mvPolynomialSpecProjLast, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap A (MvPolynomial (Fin v) A)) ?_
  have : (MvPolynomial.rename (R := A) (Fin.castSucc (n := v))).toRingHom.comp
      (algebraMap A (MvPolynomial (Fin v) A)) = algebraMap A (MvPolynomial (Fin (v + 1)) A) := by
    ext a
    simp [MvPolynomial.algebraMap_eq]
  simp only [CommRingCat.hom_ofHom]
  rw [this]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The Krull dimension of the underlying space of `Spec R` is the Krull dimension of `R`. -/
private theorem topologicalKrullDim_Spec_of (R : Type u) [CommRing R] :
    topologicalKrullDim (Spec (.of R)) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

/-- `A[x₀, …, x_v]` is the polynomial ring in one variable over `A[x₀, …, x_{v-1}]`, the last
variable `x_v` becoming the new variable. -/
noncomputable def mvPolynomialFinSuccEquivLast (v : ℕ) :
    MvPolynomial (Fin (v + 1)) A ≃+* Polynomial (MvPolynomial (Fin v) A) :=
  ((MvPolynomial.renameEquiv A (finRotate (v + 1))).trans
    (MvPolynomial.finSuccEquiv A v)).toRingEquiv

theorem mvPolynomialFinSuccEquivLast_rename_castSucc (v : ℕ) (p : MvPolynomial (Fin v) A) :
    mvPolynomialFinSuccEquivLast A v (MvPolynomial.rename Fin.castSucc p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [mvPolynomialFinSuccEquivLast, MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    have : finRotate (v + 1) i.castSucc = i.succ := by
      ext; rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]; simp
    simp [mvPolynomialFinSuccEquivLast, this, MvPolynomial.finSuccEquiv_X_succ]

/-- Every fibre of the coordinate projection `𝔸^{v+1}_A ⟶ 𝔸^v_A` over a point with values in a
field `Ω` is `𝔸¹_Ω`, of dimension `1`. -/
theorem topologicalKrullDim_pullback_mvPolynomialSpecProjLast (v : ℕ) (Ω : Type u) [Field Ω]
    (y : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin v) A))) :
    topologicalKrullDim ↥(pullback (mvPolynomialSpecProjLast A v) y) = 1 := by
  obtain ⟨φ, rfl⟩ : ∃ φ : MvPolynomial (Fin v) A →+* Ω, y = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage y).hom, by simp⟩
  set P := MvPolynomial (Fin v) A
  set Q := MvPolynomial (Fin (v + 1)) A
  let : Algebra P Ω := φ.toAlgebra
  let : Algebra P Q := (MvPolynomial.rename (R := A) (Fin.castSucc (n := v))).toRingHom.toAlgebra
  let e : Q ≃ₐ[P] Polynomial P :=
    AlgEquiv.ofRingEquiv (f := mvPolynomialFinSuccEquivLast A v)
      (mvPolynomialFinSuccEquivLast_rename_castSucc A v)
  let e' : Q ⊗[P] Ω ≃ₐ[P] Polynomial Ω :=
    ((Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      (Algebra.TensorProduct.comm P (Polynomial P) Ω)).trans (polyEquivTensor P Ω).symm
  have hiso := pullbackSpecIso P Q Ω
  change topologicalKrullDim ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap P Q)))
    (Spec.map (CommRingCat.ofHom (algebraMap P Ω)))) = 1
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso hiso).isHomeomorph,
    topologicalKrullDim_Spec_of, ringKrullDim_eq_of_ringEquiv e'.toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

/-- Every fibre of a closed immersion over a point with values in a field has dimension `≤ 0`
(it is empty or a single point). -/
theorem topologicalKrullDim_pullback_le_zero_of_isClosedImmersion {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsClosedImmersion g] (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ Y) :
    topologicalKrullDim ↥(pullback g y) ≤ 0 := by
  calc topologicalKrullDim ↥(pullback g y)
      ≤ topologicalKrullDim (Spec (.of Ω)) :=
        (pullback.snd g y).isClosedEmbedding.isInducing.topologicalKrullDim_le
    _ = 0 := by rw [topologicalKrullDim_Spec_of, ringKrullDim_eq_zero_of_field]

variable {A} in
/-- An affine morphism of finite type `f : X ⟶ Spec A` factors as `f = f₁ ∘ ⋯ ∘ fₙ ∘ f₀` with
`f₀ : X ⟶ 𝔸ⁿ_A` a closed immersion, affine with all fibres over field-valued points of dimension
`≤ 0`, and `f_v : 𝔸^v_A ⟶ 𝔸^{v-1}_A` (`v ≥ 1`) the projections forgetting the last coordinate,
affine of finite type with all fibres over field-valued points of dimension `1`. -/
@[weil "lem_fk108_affine_factor_relative_dim_one"]
theorem exists_isClosedImmersion_comp_mvPolynomialSpecProjChain {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsAffineHom f] [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (f₀ : X ⟶ Spec (.of (MvPolynomial (Fin n) A))),
      IsClosedImmersion f₀ ∧ IsAffineHom f₀ ∧ f = f₀ ≫ mvPolynomialSpecProjChain A n ∧
      (∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin n) A))),
        topologicalKrullDim ↥(pullback f₀ y) ≤ 0) ∧
      ∀ v : ℕ, IsAffineHom (mvPolynomialSpecProjLast A v) ∧
        LocallyOfFiniteType (mvPolynomialSpecProjLast A v) ∧
        ∀ (Ω : Type u) [Field Ω] (y : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin v) A))),
          topologicalKrullDim ↥(pullback (mvPolynomialSpecProjLast A v) y) = 1 := by
  have := isAffine_of_isAffineHom f
  let ψ : A →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom
  let : Algebra A Γ(X, ⊤) := ψ.toAlgebra
  have hft : Algebra.FiniteType A Γ(X, ⊤) := by
    have h := (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := f)).mp
      inferInstance
    have : ψ = f.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom := rfl
    change ψ.FiniteType
    rw [this]
    exact h.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  refine ⟨n, X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, isAffineHom_of_isAffine _,
    ?_, fun Ω _ y ↦ ?_, fun v ↦ ⟨inferInstance, inferInstance,
      topologicalKrullDim_pullback_mvPolynomialSpecProjLast A v⟩⟩
  · have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
    infer_instance
  · have h1 : f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
        ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    rw [mvPolynomialSpecProjChain_eq, Category.assoc, ← Spec.map_comp]
    refine h1.trans ?_
    congr 2
    ext a
    exact (φ.commutes a).symm
  · have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
    exact topologicalKrullDim_pullback_le_zero_of_isClosedImmersion _ Ω y

end AlgebraicGeometry
