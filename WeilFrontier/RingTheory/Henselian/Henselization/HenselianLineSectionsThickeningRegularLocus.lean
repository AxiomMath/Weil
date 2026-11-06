module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Quotient
public import WeilFrontier.AlgebraicGeometry.Properties.Regular
public import WeilFrontier.RingTheory.Henselian.Henselization.HenselianPolynomialRing

/-!
# Sections of the thickenings of the closed fibre of the henselian line over the regular locus

Let `A` be an excellent normal henselian local domain, `R = A{t}` the Henselization of `A[t]` at
`(𝔪(A), t)`, `q : X = Spec R → Y = Spec A` the structure morphism, `V ⊆ Y` the regular locus (an
open subscheme, since `A` is excellent), and for `v ≥ 0` let `X_v = Spec (R / t^{v+1} R)`, a
closed subscheme of `X`, and `U_v = (q|_{X_v})⁻¹(V)`.

Since `A[t] / (t^{v+1}) → R / t^{v+1} R` is bijective, `R / t^{v+1} R ≅ A[t] / (t^{v+1})` as
`A`-algebras; this is a free `A`-module of rank `v + 1`. Hence `q|_{X_v} : X_v → Y` is finite and
flat, and an isomorphism for `v = 0`; so is its restriction `U_v → V`. By flat base change for
global sections (the regular locus `V` is quasi-compact and quasi-separated), the restriction
`Γ(X_v, 𝒪) → Γ(U_v, 𝒪)` is the base change along `A → R / t^{v+1} R` of the restriction
`A = Γ(Y, 𝒪) → Γ(V, 𝒪)`, which is an isomorphism for a normal excellent domain. Therefore
`R / t^{v+1} R → Γ(U_v, 𝒪_{U_v})` is an isomorphism. All these isomorphisms are compatible with
the transition maps `R / t^{v+2} R → R / t^{v+1} R`.

## Main definitions

* `MvPolynomial.finOneAlgEquivPolynomial`: the polynomial ring in the variables `Fin 1` is the
  polynomial ring `A[X]`.
* `MvPolynomial.IsHenselianPolynomialRing.quotientSpanPowAlgEquiv`: for the henselian line
  `R = A{t}`, the isomorphism `R / t^n R ≃ₐ[A] A[X] / (X^n)`.

## Main results

* `AlgebraicGeometry.isIso_presheaf_map_preimage_of_flat`: for a flat morphism `f : T → S` of
  affine schemes and a quasi-compact quasi-separated open `V ⊆ S` such that `Γ(S, ⊤) → Γ(S, V)`
  is an isomorphism, `Γ(T, ⊤) → Γ(T, f⁻¹ V)` is an isomorphism.
* `MvPolynomial.IsHenselianPolynomialRing.quotientSpanPowAlgEquiv_factor`: the isomorphisms
  `R / t^{v+1} R ≅ A[X] / (X^{v+1})` are compatible with the projections.
* `MvPolynomial.IsHenselianPolynomialRing.isFinite_morphismRestrict`: `U_v → V` is finite.
* `MvPolynomial.IsHenselianPolynomialRing.isIso_morphismRestrict_zero`: `U_0 → V` is an
  isomorphism.
* `MvPolynomial.IsHenselianPolynomialRing.isIso_presheaf_map_preimage_regularLocus`: the
  restriction `Γ(X_v, 𝒪) = R / t^{v+1} R → Γ(U_v, 𝒪)` is an isomorphism.
* `MvPolynomial.presheaf_map_comp_appLE_factor`: these restriction maps are compatible with the
  projections `R / t^{v+2} R → R / t^{v+1} R` and the restrictions
  `Γ(U_{v+1}, 𝒪) → Γ(U_v, 𝒪)`.

## Implementation notes

The ring `A{t}` is any `B` with `IsHenselianPolynomialRing A (Fin 1) B`, and `t` is the image of
`X 0`. The morphism `q|_{X_v}` is written as the composite of `Spec` of the quotient map
`R → R / t^{v+1} R` with `Spec` of `A → R`, and `U_v` as its preimage of the regular locus. The
restriction map `R / t^{v+1} R → Γ(U_v, 𝒪)` is the restriction `Γ(X_v, ⊤) → Γ(X_v, U_v)`, through
the identification `Γ(Spec C, ⊤) ≅ C`. The source deduces the section computation from the
description of `q_* 𝒪_{X_v}` as a free `𝒪_Y`-module; it is obtained here from flat base change
of global sections, which needs only that `R / t^{v+1} R` is flat over `A`. The finiteness
statements use only that `A` is henselian (and excellent, for the openness of `V`); the section
computation uses in addition that `A` is a normal domain.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Limits IsLocalRing

universe u

namespace AlgebraicGeometry

lemma Scheme.isIso_presheaf_map_le_top_congr (X : Scheme.{u}) {U W : X.Opens} (e : U = W) :
    IsIso (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) ↔
      IsIso (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
  subst e; rfl

/-- **Flat base change of the restriction to an open.** Let `f : T → S` be a flat morphism of
affine schemes and `V ⊆ S` a quasi-compact quasi-separated open such that the restriction
`Γ(S, ⊤) → Γ(S, V)` is an isomorphism. Then `Γ(T, ⊤) → Γ(T, f⁻¹ V)` is an isomorphism. -/
theorem isIso_presheaf_map_preimage_of_flat {S T : Scheme.{u}} (f : T ⟶ S) [Flat f]
    [IsAffine S] [IsAffine T] (V : S.Opens) (hV : IsCompact (V : Set S))
    (hV' : IsQuasiSeparated (V : Set S))
    (hiso : IsIso (S.presheaf.map (homOfLE le_top : V ⟶ ⊤).op)) :
    IsIso (T.presheaf.map (homOfLE le_top : f ⁻¹ᵁ V ⟶ ⊤).op) := by
  have H := isPullback_morphismRestrict f V
  have hc : IsCompact (X := V.toScheme) (⊤ : V.toScheme.Opens) := by
    have : CompactSpace V := isCompact_iff_compactSpace.mp hV
    exact isCompact_univ
  have hq : IsQuasiSeparated (α := V.toScheme) (⊤ : V.toScheme.Opens) := by
    have : QuasiSeparatedSpace V := (isQuasiSeparated_iff_quasiSeparatedSpace _ V.2).mp hV'
    exact isQuasiSeparated_univ
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤)
    (UX := ⊤) (UY := ⊤) (by simp) (by simp) (by simp) (isAffineOpen_top S) (isAffineOpen_top T)
    hc hq
  replace h := (isIso_pushoutSection_iff ..).mp h
  have h1 : ∀ e, IsIso (V.ι.appLE ⊤ ⊤ e) := fun e => by
    rw [Scheme.Opens.ι_appLE]
    exact (S.isIso_presheaf_map_le_top_congr (by simp)).mp hiso
  have h2 : ∀ e, IsIso ((f ⁻¹ᵁ V).ι.appLE ⊤ ⊤ e) →
      IsIso (T.presheaf.map (homOfLE le_top : f ⁻¹ᵁ V ⟶ ⊤).op) := fun e he => by
    rw [Scheme.Opens.ι_appLE] at he
    exact (T.isIso_presheaf_map_le_top_congr (by simp)).mp he
  exact h2 _ (h.isIso_inr_of_isIso (h1 _))

end AlgebraicGeometry

namespace Polynomial

variable {A : Type u} [CommRing A]

/-- `A[X] / (X^n)` is a free `A`-module. -/
lemma free_quotient_span_X_pow (n : ℕ) :
    Module.Free A (A[X] ⧸ Ideal.span {(X : A[X]) ^ n}) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_X_pow n)).basis

/-- `A[X] / (X^n)` is a finite `A`-module. -/
lemma finite_quotient_span_X_pow (n : ℕ) :
    Module.Finite A (A[X] ⧸ Ideal.span {(X : A[X]) ^ n}) :=
  (AdjoinRoot.powerBasis' (monic_X_pow n)).finite

end Polynomial

namespace MvPolynomial

variable (A : Type u) [CommRing A]

/-- The polynomial ring in the variables `Fin 1` is the polynomial ring `A[X]`, with `X 0 ↦ X`. -/
noncomputable def finOneAlgEquivPolynomial : MvPolynomial (Fin 1) A ≃ₐ[A] Polynomial A :=
  AlgEquiv.ofAlgHom (aeval fun _ => Polynomial.X) (Polynomial.aeval (X 0))
    (Polynomial.algHom_ext (by simp)) (algHom_ext fun i => by fin_cases i; simp)

variable {A}

@[simp]
lemma finOneAlgEquivPolynomial_X (i : Fin 1) :
    finOneAlgEquivPolynomial A (X i) = Polynomial.X := by
  simp [finOneAlgEquivPolynomial]

lemma idealOfVars_fin_one_pow (n : ℕ) :
    idealOfVars (Fin 1) A ^ n = Ideal.span {X 0 ^ n} := by
  rw [idealOfVars, Set.range_unique, Ideal.span_singleton_pow]
  rfl

lemma map_span_X_pow_finOneAlgEquivPolynomial (n : ℕ) :
    (Ideal.span {(X 0 : MvPolynomial (Fin 1) A) ^ n}).map
      (finOneAlgEquivPolynomial A : MvPolynomial (Fin 1) A →+* Polynomial A) =
      Ideal.span {Polynomial.X ^ n} := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]
  simp

lemma map_span_X_pow {B : Type*} [CommRing B] [Algebra (MvPolynomial (Fin 1) A) B] (n : ℕ) :
    (Ideal.span {(X 0 : MvPolynomial (Fin 1) A) ^ n}).map (algebraMap (MvPolynomial (Fin 1) A) B) =
      Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ n} := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]

/-- `Spec (B / t^n B) → Spec B → Spec A` is `Spec` of the structure map of the `A`-algebra
`B / t^n B`. -/
lemma SpecMap_comp_SpecMap_algebraMap {B : Type u} [CommRing B]
    [Algebra (MvPolynomial (Fin 1) A) B] [Algebra A B] (n : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ n}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A
        (B ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ n}))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- With `t` the image of `X 0` in `B` and `U_v ⊆ Spec (B / t^{v+1} B)` the preimage of the
regular locus of `Spec A`, the closed immersion `Spec (B / t^{v+1} B) → Spec (B / t^{v+2} B)` maps
`U_v` into `U_{v+1}`. -/
lemma preimage_le_preimage_factor {B : Type u} [CommRing B] [Algebra (MvPolynomial (Fin 1) A) B]
    [Algebra A B] (hA : IsExcellent A) (v : ℕ) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ
        ⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩ ≤
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow
          (algebraMap (MvPolynomial (Fin 1) A) B (X 0)) (Nat.le_succ (v + 1)))))) ⁻¹ᵁ
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1 + 1)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ
        ⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩) := by
  have e : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow
          (algebraMap (MvPolynomial (Fin 1) A) B (X 0)) (Nat.le_succ (v + 1)))))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1 + 1)}))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  rw [← e]
  exact le_rfl

/-- **Compatibility of the section isomorphisms with the transition maps.** With `t` the image of
`X 0` in `B`, `X_v = Spec (B / t^{v+1} B)` and `U_v ⊆ X_v` the preimage of the regular locus of
`Spec A`, the restriction maps `B / t^{v+1} B = Γ(X_v, ⊤) → Γ(X_v, U_v)` commute with the
projection `B / t^{v+2} B → B / t^{v+1} B` and the restriction `Γ(U_{v+1}, 𝒪) → Γ(U_v, 𝒪)` along
the closed immersion `X_v → X_{v+1}`. -/
@[weil "lem_fk107_henselian_line_sections_thickening_regular_locus"]
theorem presheaf_map_comp_appLE_factor {B : Type u} [CommRing B]
    [Algebra (MvPolynomial (Fin 1) A) B] [Algebra A B] (hA : IsExcellent A) (v : ℕ) :
    (Scheme.ΓSpecIso (.of (B ⧸ Ideal.span
        {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1 + 1)}))).inv ≫
      (Spec (.of (B ⧸ Ideal.span
        {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1 + 1)}))).presheaf.map
        (homOfLE le_top : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1 + 1)}))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ
          ⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩ ⟶ ⊤).op ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow
          (algebraMap (MvPolynomial (Fin 1) A) B (X 0)) (Nat.le_succ (v + 1))))))).appLE _ _
        (preimage_le_preimage_factor hA v) =
    CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow
          (algebraMap (MvPolynomial (Fin 1) A) B (X 0)) (Nat.le_succ (v + 1))))) ≫
      (Scheme.ΓSpecIso (.of (B ⧸ Ideal.span
        {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))).inv ≫
      (Spec (.of (B ⧸ Ideal.span
        {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))).presheaf.map
        (homOfLE le_top : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ
          ⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩ ⟶ ⊤).op := by
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.map_appLE]
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

namespace IsHenselianPolynomialRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] {B : Type u} [CommRing B]
  [IsLocalRing B] [Algebra (LocalizationAtOrigin A (Fin 1)) B] [Algebra (MvPolynomial (Fin 1) A) B]
  [IsScalarTower (MvPolynomial (Fin 1) A) (LocalizationAtOrigin A (Fin 1)) B]

/-- For the henselian line `B = A{t}` (with `t` the image of `X 0`), the canonical map
`A[t] / (t^n) → B / t^n B` is bijective. -/
lemma quotientMap_span_X_pow_bijective (h : IsHenselianPolynomialRing A (Fin 1) B) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap
      (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ n})
      (algebraMap (MvPolynomial (Fin 1) A) B)
      (Ideal.map_le_iff_le_comap.mp (map_span_X_pow n).le)) := by
  have hb := h.quotientMap_bijective n
  rw [idealOfVars_fin_one_pow] at hb
  convert (Ideal.quotEquivOfEq (map_span_X_pow (A := A) (B := B) n)).bijective.comp hb using 1
  funext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

variable [Algebra A B] [IsScalarTower A (MvPolynomial (Fin 1) A) B]

/-- **The thickenings of the closed fibre of the henselian line.** For the henselian line
`B = A{t}` over a henselian local ring `A`, the `A`-algebra `B / t^n B` is isomorphic to
`A[X] / (X^n)`, by the isomorphism sending `t` to `X`
(`MvPolynomial.IsHenselianPolynomialRing.quotientSpanPowAlgEquiv_mk`). -/
@[weil "lem_fk107_henselian_line_sections_thickening_regular_locus"]
noncomputable def quotientSpanPowAlgEquiv (h : IsHenselianPolynomialRing A (Fin 1) B) (n : ℕ) :
    (B ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ n}) ≃ₐ[A]
      Polynomial A ⧸ Ideal.span {(Polynomial.X : Polynomial A) ^ n} :=
  (AlgEquiv.ofBijective (Ideal.quotientMapₐ _ (IsScalarTower.toAlgHom A (MvPolynomial (Fin 1) A) B)
    (Ideal.map_le_iff_le_comap.mp (map_span_X_pow n).le))
    (quotientMap_span_X_pow_bijective h n)).symm.trans
    (Ideal.quotientEquivAlg _ _ (finOneAlgEquivPolynomial A)
      (map_span_X_pow_finOneAlgEquivPolynomial n).symm)

lemma quotientSpanPowAlgEquiv_mk (h : IsHenselianPolynomialRing A (Fin 1) B) (n : ℕ)
    (p : MvPolynomial (Fin 1) A) :
    quotientSpanPowAlgEquiv h n (Ideal.Quotient.mk _ (algebraMap _ B p)) =
      Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial A) ^ n})
        (finOneAlgEquivPolynomial A p) := by
  rw [quotientSpanPowAlgEquiv, AlgEquiv.trans_apply]
  have : (AlgEquiv.ofBijective (Ideal.quotientMapₐ _
      (IsScalarTower.toAlgHom A (MvPolynomial (Fin 1) A) B)
      (Ideal.map_le_iff_le_comap.mp (map_span_X_pow n).le))
      (quotientMap_span_X_pow_bijective h n)).symm (Ideal.Quotient.mk _ (algebraMap _ B p)) =
      Ideal.Quotient.mk _ p := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

/-- The isomorphisms `B / t^{v+1} B ≅ A[X] / (X^{v+1})` are compatible with the projections
`B / t^{v+2} B → B / t^{v+1} B` and `A[X] / (X^{v+2}) → A[X] / (X^{v+1})`. -/
@[weil "lem_fk107_henselian_line_sections_thickening_regular_locus"]
lemma quotientSpanPowAlgEquiv_factor (h : IsHenselianPolynomialRing A (Fin 1) B) (v : ℕ)
    (x : B ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1 + 1)}) :
    quotientSpanPowAlgEquiv h (v + 1) (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ _))) x) =
      Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ _)))
        (quotientSpanPowAlgEquiv h (v + 1 + 1) x) := by
  obtain ⟨y, rfl⟩ := (quotientMap_span_X_pow_bijective h (v + 1 + 1)).2 x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  change quotientSpanPowAlgEquiv h (v + 1) (Ideal.Quotient.factor _
      (Ideal.Quotient.mk _ (algebraMap _ B p))) = Ideal.Quotient.factor _
      (quotientSpanPowAlgEquiv h (v + 1 + 1) (Ideal.Quotient.mk _ (algebraMap _ B p)))
  rw [Ideal.Quotient.factor_mk, quotientSpanPowAlgEquiv_mk, quotientSpanPowAlgEquiv_mk,
    Ideal.Quotient.factor_mk]

/-- `B / t^n B` is a finite `A`-module. -/
lemma finite_quotient (h : IsHenselianPolynomialRing A (Fin 1) B) (n : ℕ) :
    Module.Finite A (B ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ n}) :=
  have := Polynomial.finite_quotient_span_X_pow (A := A) n
  Module.Finite.equiv (quotientSpanPowAlgEquiv h n).symm.toLinearEquiv

/-- `B / t^n B` is a flat `A`-module. -/
lemma flat_quotient (h : IsHenselianPolynomialRing A (Fin 1) B) (n : ℕ) :
    Module.Flat A (B ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ n}) :=
  have := Polynomial.free_quotient_span_X_pow (A := A) n
  Module.Flat.of_linearEquiv (quotientSpanPowAlgEquiv h n).toLinearEquiv

/-- `A → B / t B` is bijective. -/
lemma bijective_algebraMap_quotient_one (h : IsHenselianPolynomialRing A (Fin 1) B) :
    Function.Bijective (algebraMap A
      (B ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (0 + 1)})) := by
  let E := ((quotientSpanPowAlgEquiv h (0 + 1)).trans (Ideal.quotientEquivAlgOfEq A
    (by simp : Ideal.span {(Polynomial.X : Polynomial A) ^ (0 + 1)} =
      Ideal.span {Polynomial.X - Polynomial.C 0}))).trans (Polynomial.quotientSpanXSubCAlgEquiv 0)
  have : ⇑(algebraMap A _) = E.symm := by
    funext a
    rw [← E.symm.commutes a]
    rfl
  rw [this]
  exact E.symm.bijective

/-- **Finiteness over the regular locus.** For the henselian line `B = A{t}` over an excellent
henselian local ring `A`, with `V` the regular locus of `Spec A`, the morphism
`q|_{X_v} : X_v = Spec (B / t^{v+1} B) → Spec A` restricts to a finite morphism
`U_v = (q|_{X_v})⁻¹ V → V`. -/
@[weil "lem_fk107_henselian_line_sections_thickening_regular_locus"]
theorem isFinite_morphismRestrict (hA : IsExcellent A) (h : IsHenselianPolynomialRing A (Fin 1) B)
    (v : ℕ) :
    IsFinite ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) ∣_
      ⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [SpecMap_comp_SpecMap_algebraMap, IsFinite.SpecMap_iff]
    have := finite_quotient h (v + 1)
    exact RingHom.finite_algebraMap.mpr this
  infer_instance

/-- **The case `v = 0`.** The restriction `U_0 → V` of `q|_{X_0} : X_0 = Spec (B / t B) → Spec A`
over the regular locus `V` is an isomorphism. -/
@[weil "lem_fk107_henselian_line_sections_thickening_regular_locus"]
theorem isIso_morphismRestrict_zero (hA : IsExcellent A)
    (h : IsHenselianPolynomialRing A (Fin 1) B) :
    IsIso ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (0 + 1)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) ∣_
      ⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩) := by
  have : IsIso (CommRingCat.ofHom (algebraMap A
      (B ⧸ Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (0 + 1)}))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_algebraMap_quotient_one h)
  rw [SpecMap_comp_SpecMap_algebraMap]
  infer_instance

/-- **Sections of the thickenings over the regular locus.** Let `A` be an excellent normal
henselian local domain, `B = A{t}` the henselian line, `V` the regular locus of `Spec A`,
`X_v = Spec (B / t^{v+1} B)` and `U_v = (q|_{X_v})⁻¹ V`. Then the restriction map
`B / t^{v+1} B = Γ(X_v, 𝒪) → Γ(U_v, 𝒪_{U_v})` is an isomorphism. -/
@[weil "lem_fk107_henselian_line_sections_thickening_regular_locus"]
theorem isIso_presheaf_map_preimage_regularLocus [IsDomain A] [IsIntegrallyClosed A]
    (hA : IsExcellent A) (h : IsHenselianPolynomialRing A (Fin 1) B) (v : ℕ) :
    IsIso ((Spec (.of (B ⧸ Ideal.span
        {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))).presheaf.map
      (homOfLE le_top : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) ⁻¹ᵁ
        ⟨regularLocus (Spec (.of A)), isOpen_regularLocus_of_isExcellent hA⟩ ⟶ ⊤).op) := by
  have : IsNoetherianRing A := hA.1.1
  have := flat_quotient h (v + 1)
  have : Flat (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {algebraMap (MvPolynomial (Fin 1) A) B (X 0) ^ (v + 1)}))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [SpecMap_comp_SpecMap_algebraMap, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr this
  exact isIso_presheaf_map_preimage_of_flat _ _ (TopologicalSpace.NoetherianSpace.isCompact _)
    (IsQuasiSeparated.of_quasiSeparatedSpace _) (isIso_presheaf_map_regularLocus hA)

end IsHenselianPolynomialRing

end MvPolynomial
