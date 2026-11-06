module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Weil.Attr
public import Weil.Defs.Algebra.Homology.DerivedCategory.InjectiveResolutionFunctor

/-!
# Precomposition with a quasi-isomorphism into a K-injective complex

Let `C` be an abelian category and `s : X' ⟶ X` a quasi-isomorphism in the homotopy category
`K(C)` of cochain complexes indexed by `ℤ`. If `L` is a K-injective cochain complex (for example
a bounded-below complex of injective objects), then precomposition with `s` induces a bijection
`Hom_{K(C)}(X, L) ≃ Hom_{K(C)}(X', L)`.

## Main results

* `CochainComplex.IsKInjective.bijective_precomp_of_quasiIso`: the bijection for a K-injective
  target and a quasi-isomorphism in the homotopy category.
* `CochainComplex.bijective_precomp_of_quasiIso_of_injective`: the case of a bounded-below
  complex of injective objects.
* `CochainComplex.bijective_precomp_quotient_map_of_quasiIso_of_injective`: the same, for the
  class of a quasi-isomorphism of cochain complexes.

## Implementation notes

The proof passes to the derived category: by
`CochainComplex.IsKInjective.Qh_map_bijective`, the functor `DerivedCategory.Qh` is bijective on
morphisms into a K-injective complex, and it sends a quasi-isomorphism to an isomorphism, so
precomposition with `s` corresponds to precomposition with an isomorphism.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.
-/

@[expose] public section

universe v u

open CategoryTheory DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex

/-- Precomposition with a quasi-isomorphism `s : X' ⟶ X` of the homotopy category is a bijection
`(X ⟶ L) → (X' ⟶ L)` when `L` is K-injective. -/
lemma IsKInjective.bijective_precomp_of_quasiIso
    {X' X : HomotopyCategory C (ComplexShape.up ℤ)} (s : X' ⟶ X)
    (hs : HomotopyCategory.quasiIso C _ s) (L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Bijective
      (fun g : X ⟶ (HomotopyCategory.quotient _ _).obj L => s ≫ g) := by
  let := HasDerivedCategory.standard C
  have : IsIso (Qh.map s) := Localization.inverts Qh (HomotopyCategory.quasiIso C _) s hs
  have hcomp : (DerivedCategory.Qh.map :
        (X' ⟶ (HomotopyCategory.quotient _ _).obj L) → _) ∘
        (fun g : X ⟶ (HomotopyCategory.quotient _ _).obj L => s ≫ g) =
      (fun h => Qh.map s ≫ h) ∘ (DerivedCategory.Qh.map :
        (X ⟶ (HomotopyCategory.quotient _ _).obj L) → _) := by
    funext g
    simp
  have hpre : Function.Bijective
      (fun h : Qh.obj X ⟶ Qh.obj ((HomotopyCategory.quotient _ _).obj L) => Qh.map s ≫ h) :=
    ⟨fun _ _ h => (cancel_epi (Qh.map s)).1 h, fun h => ⟨inv (Qh.map s) ≫ h, by simp⟩⟩
  rw [← Function.Bijective.of_comp_iff' (IsKInjective.Qh_map_bijective X' L), hcomp]
  exact hpre.comp (IsKInjective.Qh_map_bijective X L)

/-- Let `s : X' ⟶ X` be a quasi-isomorphism in the homotopy category and `I` a bounded-below
complex of injective objects. Then `g ↦ g ∘ s` is a bijection
`Hom_{K(C)}(X, I) → Hom_{K(C)}(X', I)`. -/
@[weil "lem_fka2_qis_precomposition_bijective_into_injective"]
theorem bijective_precomp_of_quasiIso_of_injective
    {X' X : HomotopyCategory C (ComplexShape.up ℤ)} (s : X' ⟶ X)
    (hs : HomotopyCategory.quasiIso C _ s) (I : CochainComplex C ℤ) (d : ℤ)
    [I.IsStrictlyGE d] [∀ n, Injective (I.X n)] :
    Function.Bijective
      (fun g : X ⟶ (HomotopyCategory.quotient _ _).obj I => s ≫ g) :=
  have := isKInjective_of_injective I d
  IsKInjective.bijective_precomp_of_quasiIso s hs I

/-- Let `s : X' ⟶ X` be a quasi-isomorphism of cochain complexes and `I` a bounded-below complex
of injective objects. Then `g ↦ g ∘ [s]` is a bijection `Hom_{K(C)}(X, I) → Hom_{K(C)}(X', I)`. -/
theorem bijective_precomp_quotient_map_of_quasiIso_of_injective
    {X' X : CochainComplex C ℤ} (s : X' ⟶ X) [QuasiIso s]
    (I : CochainComplex C ℤ) (d : ℤ) [I.IsStrictlyGE d] [∀ n, Injective (I.X n)] :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient _ _).obj X ⟶ (HomotopyCategory.quotient _ _).obj I =>
        (HomotopyCategory.quotient _ _).map s ≫ g) :=
  bijective_precomp_of_quasiIso_of_injective _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 (by
      simpa [HomologicalComplex.quasiIso] using (inferInstance : QuasiIso s))) I d

end CochainComplex

end

/-! ### Existence and uniqueness of injective-resolution functors -/

/-!
# Existence and uniqueness of injective-resolution functors

Let `C` be an abelian category and let `c` be a choice of injective resolutions `(I(X), i_X)`
on the bounded below derived category `D⁺(C)`. There is exactly one injective-resolution functor
`ρ : D⁺(C) ⥤ K(C)` for `c`.

Indeed, each `Q(i_X)` is an isomorphism, since `i_X` is a quasi-isomorphism. For a morphism
`φ : X ⟶ Y` of `D⁺(C)`, the compatibility condition on `ρ(φ)` says
`Q(ρ φ) = Q(i_X)⁻¹ ≫ φ ≫ Q(i_Y)`. As `I(Y)` is a bounded below complex of injectives, it is
K-injective, so `Q : Hom_{K(C)}(I(X), I(Y)) → Hom_{D(C)}(I(X), I(Y))` is bijective, and there is
exactly one such `ρ(φ)`. Functoriality follows from the injectivity of `Q` on these Hom sets.

## Main definitions

* `CochainComplex.InjectiveResolutionFunctor.mk'`: the injective-resolution functor of a choice
  of injective resolutions.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.instUnique`: for every choice `c` of injective
  resolutions there is exactly one injective-resolution functor for `c`.
* `CochainComplex.InjectiveResolutionFunctor.Qh_map_map`: the image in the derived category of
  `ρ(φ)` is `Q(i_X)⁻¹ ≫ φ ≫ Q(i_Y)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II,
  p. 296.
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionFunctor

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {c : ChoiceOfInjectiveResolutions C}

/-- The image `Q(i_X)` in the derived category of the resolution `i_X` chosen by `c`. -/
noncomputable abbrev resolutionMap (c : ChoiceOfInjectiveResolutions C) (X : PlusComplexes C) :
    Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1) ⟶
      Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex) :=
  Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
    (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι)

instance (X : PlusComplexes C) : IsIso (resolutionMap c X) := by
  dsimp only [resolutionMap]
  rw [isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff]
  infer_instance

/-- The bijection `Q : Hom_{K(C)}(I(X), I(Y)) ≃ Hom_{D(C)}(I(X), I(Y))`, the target `I(Y)` being
K-injective. -/
noncomputable def homEquiv (c : ChoiceOfInjectiveResolutions C) (X Y : PlusComplexes C) :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex) ≃
      (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex) ⟶
      Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex)) :=
  Equiv.ofBijective _ (IsKInjective.Qh_map_bijective _ _)

@[simp]
lemma homEquiv_apply {X Y : PlusComplexes C} (f) : homEquiv c X Y f = Qh.map f := rfl

/-- The image in the derived category of `ρ(φ)` is `Q(i_X)⁻¹ ≫ φ ≫ Q(i_Y)`. -/
lemma Qh_map_map (ρ : InjectiveResolutionFunctor c) {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    Qh.map (ρ.map φ) = inv (resolutionMap c X) ≫ φ.hom ≫ resolutionMap c Y := by
  rw [IsIso.eq_inv_comp]
  exact ρ.comm φ

/-- The action on morphisms of an injective-resolution functor is determined by the choice of
injective resolutions. -/
lemma map_eq (ρ : InjectiveResolutionFunctor c) {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    ρ.map φ = (homEquiv c X Y).symm (inv (resolutionMap c X) ≫ φ.hom ≫ resolutionMap c Y) := by
  rw [Equiv.eq_symm_apply, homEquiv_apply, Qh_map_map]

variable (c) in
/-- The injective-resolution functor of a choice `c` of injective resolutions: `ρ(φ)` is the
unique morphism of `K(C)` with `Q(ρ φ) = Q(i_X)⁻¹ ≫ φ ≫ Q(i_Y)`. -/
noncomputable def mk' : InjectiveResolutionFunctor c where
  map {X Y} φ := (homEquiv c X Y).symm (inv (resolutionMap c X) ≫ φ.hom ≫ resolutionMap c Y)
  map_id X := by
    rw [Equiv.symm_apply_eq, homEquiv_apply, CategoryTheory.Functor.map_id]
    simp
  map_comp {X Y Z} φ ψ := by
    rw [Equiv.symm_apply_eq, homEquiv_apply, CategoryTheory.Functor.map_comp]
    have h₁ := (homEquiv c X Y).apply_symm_apply
      (inv (resolutionMap c X) ≫ φ.hom ≫ resolutionMap c Y)
    have h₂ := (homEquiv c Y Z).apply_symm_apply
      (inv (resolutionMap c Y) ≫ ψ.hom ≫ resolutionMap c Z)
    rw [homEquiv_apply] at h₁ h₂
    rw [h₁, h₂]
    simp
  comm {X Y} φ := by
    have h := (homEquiv c X Y).apply_symm_apply
      (inv (resolutionMap c X) ≫ φ.hom ≫ resolutionMap c Y)
    rw [homEquiv_apply] at h
    change resolutionMap c X ≫ Qh.map _ = φ.hom ≫ resolutionMap c Y
    rw [h, IsIso.hom_inv_id_assoc]

/-- For every choice `c` of injective resolutions on `D⁺(C)` there is exactly one
injective-resolution functor for `c`. -/
@[weil "lem_fka2_injective_resolution_functor_exists_unique"]
noncomputable instance instUnique : Unique (InjectiveResolutionFunctor c) where
  default := mk' c
  uniq ρ := by
    ext X Y φ
    rw [map_eq ρ φ, map_eq (mk' c) φ]

end InjectiveResolutionFunctor

end CochainComplex
