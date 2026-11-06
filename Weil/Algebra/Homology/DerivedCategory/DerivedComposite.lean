module

public import Weil.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Weil.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.CategoryTheory.Abelian.RightDerived
public import Weil.Attr

/-!
# The derived functor of a composite

Let `F : A ⥤ B` and `G : B ⥤ C` be additive functors of abelian categories, let `(I(X), i_X)` be a
choice of injective resolutions on `D⁺(A)` with injective-resolution functor `ρ_A`, and
`(I_B(Y), i_Y)` one on `D⁺(B)` with injective-resolution functor `ρ_B`. Let `RF`, `R(G ∘ F)` be
the derived functors for the first choice and `RG` the one for the second.

Since `I(X)` is a bounded below complex, so is `RF(X) = F(I(X))`, so `RF` is a functor
`D⁺(A) ⥤ D⁺(B)`. The morphisms `Q(G(i_{F(I(X))})) : R(G ∘ F)(X) = G(F(I(X))) ⟶ RG(RF(X))` form a
natural transformation `R(G ∘ F) ⟶ RG ∘ RF`. If `B` has enough injectives and `F(M)` is
`G`-acyclic for every injective object `M` of `A`, it is an isomorphism, since `F(I(X))` is then
a bounded below complex of `G`-acyclic objects, which computes `RG`.

## Main definitions

* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorPlusComplexes`: the derived
  functor `RF` with values in `D⁺(B)`, presented by complexes.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorCompNatTrans`: the natural
  transformation `R(G ∘ F) ⟶ RG ∘ RF` with components `Q(G(i_{F(I(X))}))`.
* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorCompIso`: the isomorphism
  `R(G ∘ F) ≅ RG ∘ RF`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.isIso_rightDerivedFunctorCompNatTrans`: the
  transformation is an isomorphism when `F` sends injective objects to `G`-acyclic ones.
* `isIso_rightDerivedFunctorCompNatTrans_of_rightAcyclic_homology` (same namespace): the
  same under the source's hypothesis that every `R^ν F(M[0])`, `M` injective, is `G`-acyclic,
  for a left exact `F`.

## Implementation notes

The source assumes that `R^ν F(M[0])` is `G`-acyclic for every `ν`; only `ν = 0` is used, through
`F(M) ≅ R⁰F(M[0])` for a left exact `F`. The main statement assumes directly that `F(M)` is
`G`-acyclic for every injective `M`, which needs neither left exactness of `F` or `G` nor enough
injectives in `A`; the source's form is the corollary
`isIso_rightDerivedFunctorCompNatTrans_of_rightAcyclic_homology`. The choice-free form of this
result, for Mathlib's `Functor.rightDerivedFunctorPlus`, is
`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective` [Stacks, Tag 015M].

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4.
* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

-- Instance search for the right derived functor otherwise times out; the cheap instance coming
-- from `EnoughInjectives` is tried first, as in StacksFrontier's derived-category files.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CochainComplex

namespace InjectiveResolutionFunctor

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]

section

variable {cA : ChoiceOfInjectiveResolutions A} (ρA : InjectiveResolutionFunctor cA)
  (F : A ⥤ B) [F.Additive]

omit [HasDerivedCategory B] in
/-- The complex `F(I(X))` is bounded below. -/
lemma exists_isGE_mapHomologicalComplex_obj (cA : ChoiceOfInjectiveResolutions A)
    (X : PlusComplexes A) :
    ∃ n : ℤ, CochainComplex.IsGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex) n := by
  obtain ⟨n, hn⟩ :=
    (cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).exists_isStrictlyGE
  refine ⟨n, ?_⟩
  have : CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex) n :=
    (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi ↦ F.map_isZero
      ((cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1
        X.2).cocomplex.isZero_of_isStrictlyGE n i hi)
  infer_instance

/-- The derived functor `RF(X) = F(I(X))` with values in the bounded below derived category of
`B`, presented by complexes: `F(I(X))` is a bounded below complex. -/
@[weil "prop_fka2_derived_composite"]
noncomputable def rightDerivedFunctorPlusComplexes : PlusComplexes A ⥤ PlusComplexes B where
  obj X := (⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex,
    exists_isGE_mapHomologicalComplex_obj F cA X⟩ : {K : CochainComplex B ℤ // ∃ n : ℤ, K.IsGE n})
  map φ := InducedCategory.homMk ((ρA.rightDerivedFunctor F).map φ)
  map_id X := by
    ext
    exact (ρA.rightDerivedFunctor F).map_id X
  map_comp φ ψ := by
    ext
    exact (ρA.rightDerivedFunctor F).map_comp φ ψ

/-- Composing `RF : D⁺(A) ⥤ D⁺(B)` with the inclusion `D⁺(B) ⥤ D(B)` gives back `RF`. -/
lemma rightDerivedFunctorPlusComplexes_comp_inducedFunctor :
    ρA.rightDerivedFunctorPlusComplexes F ⋙ inducedFunctor _ = ρA.rightDerivedFunctor F :=
  rfl

@[simp]
lemma rightDerivedFunctorPlusComplexes_map_hom {X Y : PlusComplexes A} (φ : X ⟶ Y) :
    ((ρA.rightDerivedFunctorPlusComplexes F).map φ).hom = (ρA.rightDerivedFunctor F).map φ :=
  rfl

end

variable {cA : ChoiceOfInjectiveResolutions A} (ρA : InjectiveResolutionFunctor cA)
  {cB : ChoiceOfInjectiveResolutions B} (ρB : InjectiveResolutionFunctor cB)
  (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]

/-- The resolution `i_{F(I(X))} : F(I(X)) ⟶ I_B(F(I(X)))` of the second choice. -/
noncomputable abbrev compι (X : PlusComplexes A) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (cB ((ρA.rightDerivedFunctorPlusComplexes F).obj X :
        {K : CochainComplex B ℤ // ∃ n : ℤ, K.IsGE n}).1
        ((ρA.rightDerivedFunctorPlusComplexes F).obj X).2).cocomplex :=
  (cB ((ρA.rightDerivedFunctorPlusComplexes F).obj X :
    {K : CochainComplex B ℤ // ∃ n : ℤ, K.IsGE n}).1
    ((ρA.rightDerivedFunctorPlusComplexes F).obj X).2).ι

omit [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] in
lemma mapHomotopyCategory_comp_map {K L : HomotopyCategory A (ComplexShape.up ℤ)} (f : K ⟶ L) :
    ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ)).map f =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map f) := by
  obtain ⟨K⟩ := K
  obtain ⟨L⟩ := L
  rw [← HomotopyCategory.quotient_map_out f]
  rfl

/-- In the homotopy category of `B`:
`F(ρ_A(φ)) ≫ i_{F(I(Y))} = i_{F(I(X))} ≫ ρ_B(RF(φ))`. -/
lemma mapHomotopyCategory_map_comp_quotient_map_compι {X Y : PlusComplexes A} (φ : X ⟶ Y) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρA.map φ) ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (compι ρA F (cB := cB) Y) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (compι ρA F (cB := cB) X) ≫
        ρB.map ((ρA.rightDerivedFunctorPlusComplexes F).map φ) := by
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ _).1
  refine (Qh.map_comp _ _).trans (Eq.trans ?_ (Qh.map_comp _ _).symm)
  exact (ρB.comm ((ρA.rightDerivedFunctorPlusComplexes F).map φ)).symm

/-- The natural transformation `R(G ∘ F) ⟶ RG ∘ RF` whose component at `X` is
`Q(G(i_{F(I(X))})) : G(F(I(X))) ⟶ G(I_B(F(I(X))))`. -/
@[weil "prop_fka2_derived_composite"]
noncomputable def rightDerivedFunctorCompNatTrans :
    ρA.rightDerivedFunctor (F ⋙ G) ⟶
      ρA.rightDerivedFunctorPlusComplexes F ⋙ ρB.rightDerivedFunctor G where
  app X := Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map (compι ρA F (cB := cB) X)))
  naturality {X Y} φ := by
    change Qh.map (((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ)).map (ρA.map φ)) ≫ _ =
      _ ≫ Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (ρB.map ((ρA.rightDerivedFunctorPlusComplexes F).map φ)))
    rw [mapHomotopyCategory_comp_map]
    have h := congrArg (fun f ↦ Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map f))
      (mapHomotopyCategory_map_comp_quotient_map_compι ρA ρB F φ)
    refine Eq.trans ?_ (h.trans ?_)
    · exact (Qh.map_comp _ _).symm.trans (congrArg Qh.map ((G.mapHomotopyCategory _).map_comp
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρA.map φ))
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map (compι ρA F (cB := cB) Y))).symm)
    · exact (congrArg Qh.map ((G.mapHomotopyCategory _).map_comp _ _)).trans (Qh.map_comp _ _)

@[simp]
lemma rightDerivedFunctorCompNatTrans_app (X : PlusComplexes A) :
    (ρA.rightDerivedFunctorCompNatTrans ρB F G).app X =
      Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map (compι ρA F (cB := cB) X))) :=
  rfl

/-- **The derived functor of a composite.** If `B` has enough injectives and `F` sends injective
objects to `G`-acyclic objects, the morphisms `Q(G(i_{F(I(X))})) : R(G ∘ F)(X) ⟶ RG(RF(X))`
form an isomorphism of functors `R(G ∘ F) ≅ RG ∘ RF` on `D⁺(A)`. -/
@[weil "prop_fka2_derived_composite"]
theorem isIso_rightDerivedFunctorCompNatTrans [EnoughInjectives B]
    (hFG : ∀ M : A, Injective M → G.rightAcyclic (F.obj M)) :
    IsIso (ρA.rightDerivedFunctorCompNatTrans ρB F G) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨n, hn⟩ :=
    (cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).exists_isStrictlyGE
  have hK : ∃ n : ℤ, CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex) n :=
    ⟨n, (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi ↦ F.map_isZero
      ((cA (X : {K : CochainComplex A ℤ // ∃ n : ℤ, K.IsGE n}).1
        X.2).cocomplex.isZero_of_isStrictlyGE n i hi)⟩
  exact ρB.isIso_Qh_map_map_ι_of_rightAcyclic G _ hK (fun k ↦ hFG _ inferInstance)

/-- For a left exact `F`, an object `M` of `A` with `R⁰F(M[0])` right acyclic for `G` is such that
`F(M)` is right acyclic for `G`, as `F(M) ≅ R⁰F(M[0])`. -/
lemma rightAcyclic_obj_of_rightAcyclic_homology_zero [EnoughInjectives A] [EnoughInjectives B]
    [PreservesFiniteLimits F] (M : A)
    (hM : G.rightAcyclic ((homologyFunctor B 0).obj
      ((ρA.rightDerivedFunctor F).obj (PlusComplexes.singleZero M)))) :
    G.rightAcyclic (F.obj M) := by
  have : IsIso (ρA.degreeZeroMap F M) := by
    have := isIso_homologyMap_map_choiceOfInjectiveResolutions_single_zero F cA M
    exact IsIso.comp_isIso' inferInstance this
  exact G.rightAcyclic.prop_of_iso
    (asIso (ρA.degreeZeroMap F M) ≪≫
      ((ρA.rightDerivedFunctorCompHomologyIso F 0).app (PlusComplexes.singleZero M)).symm).symm hM

/-- **The derived functor of a composite**, under the source's hypothesis. Let `A` and `B` have
enough injectives, let `F` be left exact, and assume that `R^ν F(M[0])` is `G`-acyclic for every
injective object `M` of `A` and every `ν`. Then the morphisms
`Q(G(i_{F(I(X))})) : R(G ∘ F)(X) ⟶ RG(RF(X))` form an isomorphism of functors
`R(G ∘ F) ≅ RG ∘ RF` on `D⁺(A)`. -/
@[weil "prop_fka2_derived_composite"]
theorem isIso_rightDerivedFunctorCompNatTrans_of_rightAcyclic_homology [EnoughInjectives A]
    [EnoughInjectives B] [PreservesFiniteLimits F]
    (hFG : ∀ M : A, Injective M → ∀ ν : ℤ, G.rightAcyclic ((homologyFunctor B ν).obj
      ((ρA.rightDerivedFunctor F).obj (PlusComplexes.singleZero M)))) :
    IsIso (ρA.rightDerivedFunctorCompNatTrans ρB F G) :=
  ρA.isIso_rightDerivedFunctorCompNatTrans ρB F G fun M hM ↦
    ρA.rightAcyclic_obj_of_rightAcyclic_homology_zero F G M (hFG M hM 0)

/-- The isomorphism `R(G ∘ F) ≅ RG ∘ RF` of `isIso_rightDerivedFunctorCompNatTrans`. -/
@[weil "prop_fka2_derived_composite"]
noncomputable def rightDerivedFunctorCompIso [EnoughInjectives B]
    (hFG : ∀ M : A, Injective M → G.rightAcyclic (F.obj M)) :
    ρA.rightDerivedFunctor (F ⋙ G) ≅
      ρA.rightDerivedFunctorPlusComplexes F ⋙ ρB.rightDerivedFunctor G :=
  haveI := ρA.isIso_rightDerivedFunctorCompNatTrans ρB F G hFG
  asIso (ρA.rightDerivedFunctorCompNatTrans ρB F G)

end InjectiveResolutionFunctor

end CochainComplex
