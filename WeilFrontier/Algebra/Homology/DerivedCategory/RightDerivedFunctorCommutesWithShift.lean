module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import WeilFrontier.Algebra.Homology.DerivedCategory.Basic
public import WeilFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionUniqueUpToHomotopy
public import WeilFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilFrontier.Algebra.Homology.HomotopyCategory.Shift
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.InjectiveResolutionFunctor
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Weil.Attr

/-!
# The right derived functor of a choice of injective resolutions commutes with shifts

Let `F : C ⥤ D` be an additive functor between abelian categories, `(I(X), i_X)` a choice of
injective resolutions on the bounded below derived category `D⁺(C)`, `ρ` the corresponding
injective-resolution functor and `RF` the right derived functor, so that `RF(X) = F(I(X))`.

Let `T = [n]` be a shift. For `X` in `D⁺(C)`, the shifted complex `T(I(X))` is a bounded below
complex of injectives and `T(i_X) : TX ⟶ T(I(X))` is a quasi-isomorphism, so `(T(I(X)), T(i_X))`
is an injective resolution of `TX`. Hence there is a unique morphism `c^T_X : I(TX) ⟶ T(I(X))` of
the homotopy category `K(C)` with `c^T_X ∘ i_{TX} = T(i_X)`, and it is an isomorphism. The
morphisms `Q(F(c^T_X)) : RF(TX) ⟶ Q(F(T(I(X)))) = T(RF(X))` form an isomorphism of functors
`RF ∘ T ≅ T ∘ RF` on `D⁺(C)`.

## Main definitions

* `DerivedCategory.PlusComplexes.shift`: the shift functor `[n]` on the bounded below derived
  category presented by complexes, `K ↦ K⟦n⟧`.
* `CochainComplex.shiftResolutionComparison`: the morphism `c^T_X : I(X⟦n⟧) ⟶ I(X)⟦n⟧` of
  `K(C)`.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorShiftIso`: the isomorphism of
  functors `[n] ⋙ RF ≅ RF ⋙ [n]`.

## Main results

* `CochainComplex.existsUnique_shiftResolutionComparison`: existence and uniqueness of `c^T_X`.
* `CochainComplex.isIso_shiftResolutionComparison`: `c^T_X` is an isomorphism of `K(C)`.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorShiftIso_hom_app`: the component
  at `X` of `rightDerivedFunctorShiftIso` is `Q(F(c^T_X))` followed by the identification
  `Q(F(I(X)⟦n⟧)) ≅ Q(F(I(X)))⟦n⟧`.

## Implementation notes

The source states the result for `T = [1]`; it is proved here for every shift `[n]`, `n : ℤ`.
The identification `F(T(I(X))) = T(F(I(X)))`, an equality of complexes, becomes in the derived
category the commutation isomorphism of the composite
`F.mapHomologicalComplex ⋙ quotient ⋙ Qh` with the shift; its component is the image of the
`eqToHom` of `CategoryTheory.Functor.mapHomologicalComplex_obj_shift`
(`CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_eq_eqToHom`) followed by the
commutation of `quotient ⋙ Qh` with the shift. The shift on `D⁺(C)` is transported along these
commutation isomorphisms of `quotient ⋙ Qh`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4.
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

namespace DerivedCategory.PlusComplexes

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The shift functor `[n]` on the bounded below derived category presented by complexes: it
sends the complex `K` to `K⟦n⟧`, and a morphism `φ` of `D(C)` to its shift, transported along
the commutation of `quotient ⋙ Qh` with the shift. -/
noncomputable def shift (n : ℤ) : PlusComplexes C ⥤ PlusComplexes C where
  obj X := ⟨(X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1⟦n⟧, by
    obtain ⟨a, ha⟩ := (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).2
    exact ⟨a - n, (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1.isGE_shift a n (a - n)
      (by lia)⟩⟩
  map {X Y} φ := InducedCategory.homMk
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).hom.app
        (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫ φ.hom⟦n⟧' ≫
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).inv.app
        (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)
  map_id X := by
    ext
    simp
  map_comp φ ψ := by
    ext
    simp

variable {C}

@[simp]
lemma shift_obj_coe (n : ℤ) (X : PlusComplexes C) :
    (((shift C n).obj X : PlusComplexes C) : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 =
      (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1⟦n⟧ :=
  rfl

@[simp]
lemma shift_map_hom (n : ℤ) {X Y : PlusComplexes C} (φ : X ⟶ Y) :
    ((shift C n).map φ).hom =
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).hom.app
          (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 ≫ φ.hom⟦n⟧' ≫
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).inv.app
          (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 :=
  rfl

end DerivedCategory.PlusComplexes

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ] [HasShift B ℤ] (L : A ⥤ B)
  [L.CommShift ℤ]

/-- Let `L` commute with the shifts. If `L(a) ≫ L(g) = f ≫ L(b)`, then the shift of `f`,
transported along the commutation isomorphisms of `L`, satisfies
`f⟦n⟧ ≫ L(b⟦n⟧) = L(a⟦n⟧) ≫ L(g⟦n⟧)`. -/
lemma commShiftIso_conj_shift_comp_map_shift {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y')
    (g : X' ⟶ Y') (f : L.obj X ⟶ L.obj Y) (h : L.map a ≫ L.map g = f ≫ L.map b) (n : ℤ) :
    ((L.commShiftIso n).hom.app X ≫ f⟦n⟧' ≫ (L.commShiftIso n).inv.app Y) ≫ L.map (b⟦n⟧') =
      L.map (a⟦n⟧') ≫ L.map (g⟦n⟧') := by
  rw [← cancel_mono ((L.commShiftIso n).hom.app Y')]
  have h₁ := L.commShiftIso_hom_naturality b n
  have h₂ := L.commShiftIso_hom_naturality (a ≫ g) n
  simp only [Category.assoc, h₁, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
] at h₂ ⊢
  rw [h₂, ← h]
  simp only [Functor.map_comp]

end CategoryTheory.Functor

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]


/-- For an injective resolution `R` of `K`, precomposition with the class of a quasi-isomorphism
`s` is a bijection on morphisms of `K(C)` into the shifted complex of injectives `R⟦n⟧`. -/
lemma InjectiveResolutionPlus.bijective_precomp_quotient_map_shift {K : CochainComplex C ℤ}
    (R : InjectiveResolutionPlus K) (n : ℤ) {X' X : CochainComplex C ℤ} (s : X' ⟶ X)
    [QuasiIso s] :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (R.cocomplex⟦n⟧) =>
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s ≫ g) := by
  obtain ⟨d, hd⟩ := R.exists_isStrictlyGE
  have : (R.cocomplex⟦n⟧).IsStrictlyGE (d - n) := R.cocomplex.isStrictlyGE_shift d n (d - n)
    (by lia)
  have : ∀ p, Injective ((R.cocomplex⟦n⟧).X p) := fun p =>
    inferInstanceAs (Injective (R.cocomplex.X (p + n)))
  exact bijective_precomp_quotient_map_of_quasiIso_of_injective s _ (d - n)

/-- For an injective resolution `R` of `K`, precomposition with the class of a quasi-isomorphism
`s` is a bijection on morphisms of `K(C)` into the complex of injectives of `R`. -/
lemma InjectiveResolutionPlus.bijective_precomp_quotient_map {K : CochainComplex C ℤ}
    (R : InjectiveResolutionPlus K) {X' X : CochainComplex C ℤ} (s : X' ⟶ X) [QuasiIso s] :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X ⟶
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex =>
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s ≫ g) := by
  obtain ⟨d, hd⟩ := R.exists_isStrictlyGE
  exact bijective_precomp_quotient_map_of_quasiIso_of_injective s _ d

/-- For an injective resolution `R` of `K`, the localization functor `Qh` is injective on
morphisms of `K(C)` into the shifted complex of injectives `R⟦n⟧`. -/
lemma InjectiveResolutionPlus.Qh_map_injective_shift [HasDerivedCategory C]
    {K : CochainComplex C ℤ} (R : InjectiveResolutionPlus K) (n : ℤ)
    (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    Function.Injective (Qh.map :
      (X ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (R.cocomplex⟦n⟧)) → _) := by
  obtain ⟨d, hd⟩ := R.exists_isStrictlyGE
  have : (R.cocomplex⟦n⟧).IsStrictlyGE (d - n) := R.cocomplex.isStrictlyGE_shift d n (d - n)
    (by lia)
  have : ∀ p, Injective ((R.cocomplex⟦n⟧).X p) := fun p =>
    inferInstanceAs (Injective (R.cocomplex.X (p + n)))
  have := isKInjective_of_injective (R.cocomplex⟦n⟧) (d - n)
  exact (IsKInjective.Qh_map_bijective X _).1

variable [HasDerivedCategory C] (c : ChoiceOfInjectiveResolutions C)

open DerivedCategory.PlusComplexes

/-- `(I(X)⟦n⟧, i_X⟦n⟧)` is an injective resolution of `X⟦n⟧`, so there is a unique morphism
`c^T_X : I(X⟦n⟧) ⟶ I(X)⟦n⟧` of the homotopy category with `c^T_X ∘ i_{X⟦n⟧} = i_X⟦n⟧`. -/
lemma existsUnique_shiftResolutionComparison (n : ℤ) (X : PlusComplexes C) :
    ∃! g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c ((shift C n).obj X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          ((shift C n).obj X).2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex⟦n⟧),
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          (c ((shift C n).obj X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
            ((shift C n).obj X).2).ι ≫ g =
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
          ((c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι⟦n⟧') :=
  (InjectiveResolutionPlus.bijective_precomp_quotient_map_shift
    (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2) n _).existsUnique _

/-- The morphism `c^T_X : I(X⟦n⟧) ⟶ I(X)⟦n⟧` of the homotopy category, characterized by
`c^T_X ∘ i_{X⟦n⟧} = i_X⟦n⟧` (`shiftResolutionComparison_spec`). -/
noncomputable def shiftResolutionComparison (n : ℤ) (X : PlusComplexes C) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c ((shift C n).obj X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          ((shift C n).obj X).2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex⟦n⟧) :=
  (existsUnique_shiftResolutionComparison c n X).exists.choose

@[reassoc]
lemma shiftResolutionComparison_spec (n : ℤ) (X : PlusComplexes C) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c ((shift C n).obj X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          ((shift C n).obj X).2).ι ≫ shiftResolutionComparison c n X =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι⟦n⟧') :=
  (existsUnique_shiftResolutionComparison c n X).exists.choose_spec

/-- `Q(c^T_X ≫ g) ∘ Q(i_{X⟦n⟧}) = Q(g) ∘ Q(i_X⟦n⟧)` in the derived category. -/
@[reassoc]
lemma Qh_map_shiftResolutionComparison_spec (n : ℤ) (X : PlusComplexes C)
    {Z : HomotopyCategory C (ComplexShape.up ℤ)}
    (g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex⟦n⟧) ⟶ Z) :
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c ((shift C n).obj X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
          ((shift C n).obj X).2).ι) ≫ Qh.map (shiftResolutionComparison c n X ≫ g) =
      Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι⟦n⟧')) ≫ Qh.map g := by
  rw [← Functor.map_comp, ← Functor.map_comp, shiftResolutionComparison_spec_assoc]
  rfl

omit [HasDerivedCategory C] in
/-- Let `R` be an injective resolution of `K` and `R'` one of `K⟦n⟧`. A morphism
`g : R' ⟶ R⟦n⟧` of the homotopy category with `g ∘ [R'.ι] = [R.ι⟦n⟧]` is an isomorphism. -/
lemma InjectiveResolutionPlus.isIso_of_comp_eq_shift {K : CochainComplex C ℤ} (n : ℤ)
    (R : InjectiveResolutionPlus K) (R' : InjectiveResolutionPlus (K⟦n⟧))
    (g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R'.cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (R.cocomplex⟦n⟧))
    (hg : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι ≫ g =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (R.ι⟦n⟧')) :
    IsIso g := by
  obtain ⟨g', hg'⟩ := (R'.bijective_precomp_quotient_map (R.ι⟦n⟧')).2
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R'.ι)
  simp only at hg'
  refine ⟨g', ?_, ?_⟩
  · apply (R'.bijective_precomp_quotient_map R'.ι).1
    simp only [Category.comp_id]
    rw [reassoc_of% hg, hg']
  · apply (R.bijective_precomp_quotient_map_shift n (R.ι⟦n⟧')).1
    simp only [Category.comp_id]
    rw [reassoc_of% hg', hg]

/-- `c^T_X : I(X⟦n⟧) ⟶ I(X)⟦n⟧` is an isomorphism of the homotopy category. -/
instance isIso_shiftResolutionComparison (n : ℤ) (X : PlusComplexes C) :
    IsIso (shiftResolutionComparison c n X) :=
  InjectiveResolutionPlus.isIso_of_comp_eq_shift n _ _ _ (shiftResolutionComparison_spec c n X)

namespace InjectiveResolutionFunctor

variable {c} (ρ : InjectiveResolutionFunctor c) (F : C ⥤ D) [F.Additive] [HasDerivedCategory D]

/-- The image `Q(F(c^T_X)) : RF(X⟦n⟧) ⟶ Q(F(I(X)⟦n⟧))` of `c^T_X` in `D(D)`, followed by the
identification `Q(F(I(X)⟦n⟧)) ≅ Q(F(I(X)))⟦n⟧ = RF(X)⟦n⟧`. -/
noncomputable def rightDerivedFunctorShiftIsoApp (n : ℤ) (X : PlusComplexes C) :
    (ρ.rightDerivedFunctor F).obj ((shift C n).obj X) ≅
      ((ρ.rightDerivedFunctor F).obj X)⟦n⟧ :=
  (Qh.mapIso ((F.mapHomotopyCategory (ComplexShape.up ℤ)).mapIso
      (@asIso _ _ _ _ (shiftResolutionComparison c n X)
        (isIso_shiftResolutionComparison c n X)))) ≪≫
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomotopyCategory.quotient D (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).app
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex

lemma rightDerivedFunctorShiftIsoApp_hom (n : ℤ) (X : PlusComplexes C) :
    (ρ.rightDerivedFunctorShiftIsoApp F n X).hom =
      Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (shiftResolutionComparison c n X)) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient D (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).hom.app
            (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex :=
  Iso.trans_hom _ _

/-- The isomorphism of functors `[n] ⋙ RF ≅ RF ⋙ [n]` on `D⁺(C)` whose components are the
images `Q(F(c^T_X))` of the comparison morphisms `c^T_X : I(X⟦n⟧) ⟶ I(X)⟦n⟧`, followed by the
identification `Q(F(I(X)⟦n⟧)) = RF(X)⟦n⟧` (`rightDerivedFunctorShiftIso_hom_app`). -/
@[weil "lem_fka2_right_derived_functor_commutes_with_shift"]
noncomputable def rightDerivedFunctorShiftIso (n : ℤ) :
    shift C n ⋙ ρ.rightDerivedFunctor F ≅
      ρ.rightDerivedFunctor F ⋙ CategoryTheory.shiftFunctor (DerivedCategory D) n :=
  NatIso.ofComponents (ρ.rightDerivedFunctorShiftIsoApp F n) (fun {X Y} φ ↦ by
    obtain ⟨r, hr⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective (ρ.map φ)
    -- the commutation in `K(C)`: `ρ(Tφ) ≫ c^T_Y = c^T_X ≫ [r⟦n⟧]`
    have key : ρ.map ((shift C n).map φ) ≫ shiftResolutionComparison c n Y =
        shiftResolutionComparison c n X ≫
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (r⟦n⟧') := by
      apply (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).Qh_map_injective_shift n
      rw [← cancel_epi (resolutionMap c ((shift C n).obj X))]
      have h₁ : Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
            (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι) ≫
            Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r) =
          φ.hom ≫ Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
            (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).ι) := by
        rw [hr]; exact ρ.comm φ
      simp only [resolutionMap]
      rw [Functor.map_comp, ρ.comm_assoc, ← Functor.map_comp, shiftResolutionComparison_spec,
        Qh_map_shiftResolutionComparison_spec, shift_map_hom]
      exact Functor.commShiftIso_conj_shift_comp_map_shift
        (HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh) _ _ _ _ h₁ n
    rw [rightDerivedFunctorShiftIsoApp_hom, rightDerivedFunctorShiftIsoApp_hom]
    change Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (ρ.map ((shift C n).map φ))) ≫ _ =
      _ ≫ (Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρ.map φ)))⟦n⟧'
    have e : Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (ρ.map ((shift C n).map φ))) ≫
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (shiftResolutionComparison c n Y)) =
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (shiftResolutionComparison c n X)) ≫
        Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (r⟦n⟧'))) := by
      simp only [← Functor.map_comp, key]
    have natur : Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (r⟦n⟧'))) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient D (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).hom.app
            (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex =
        ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient D (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).hom.app
            (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ≫
        (Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρ.map φ)))⟦n⟧' := by
      rw [← hr]
      exact (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomotopyCategory.quotient D (ComplexShape.up ℤ) ⋙ Qh).commShiftIso_hom_naturality r n
    exact ((reassoc_of% e) _).trans ((congrArg (fun t ↦ Qh.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (shiftResolutionComparison c n X)) ≫ t)
      natur).trans (Category.assoc _ _ _).symm))

/-- The component at `X` of `rightDerivedFunctorShiftIso` is `Q(F(c^T_X))`, followed by the
identification `Q(F(I(X)⟦n⟧)) ≅ Q(F(I(X)))⟦n⟧` of the commutation of `F` with the shift. -/
@[weil "lem_fka2_right_derived_functor_commutes_with_shift"]
theorem rightDerivedFunctorShiftIso_hom_app (n : ℤ) (X : PlusComplexes C) :
    (ρ.rightDerivedFunctorShiftIso F n).hom.app X =
      Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (shiftResolutionComparison c n X)) ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient D (ComplexShape.up ℤ) ⋙ Qh).commShiftIso n).hom.app
            (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex := by
  simp only [rightDerivedFunctorShiftIso, NatIso.ofComponents_hom_app]
  exact ρ.rightDerivedFunctorShiftIsoApp_hom F n X

end InjectiveResolutionFunctor

end CochainComplex
