module

public import Weil.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor
public import Weil.Attr
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import Weil.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The classical derived functors are the cohomology of the total derived functor

Let `F : C ⥤ D` be an additive functor between abelian categories, `ρ` an
injective-resolution functor for a choice `X ↦ (I(X), i_X)` of injective resolutions on the
bounded below derived category `D⁺(C)`, and `RF : D⁺(C) ⥤ D(D)` the corresponding derived
functor, so that `RF(X) = Q(F(I(X)))` and `RF(φ) = Q(F(r))` for any morphism of complexes `r`
representing `ρ(φ)`. Since the cohomology functor `H^ν : D(D) ⥤ D` satisfies `H^ν ∘ Q = H^ν`,
the cohomology `H^ν(F(r))` of `F(r)` is identified with `H^ν(RF(φ))`, through the canonical
isomorphisms `H^ν(F(I(X))) ≅ H^ν(RF(X))`. In particular `H^ν(F(r))` does not depend on the
representative `r`, and the functor `X ↦ H^ν(F(I(X)))` is isomorphic to the composite of
functors `RF ⋙ H^ν`.

## Main definitions

* `CochainComplex.InjectiveResolutionFunctor.rightDerivedFunctorCompHomologyIso`: the natural
  isomorphism `RF ⋙ H^ν ≅ ρ.classicalRightDerived F ν`, whose component at `X` is the
  canonical isomorphism `H^ν(RF(X)) ≅ H^ν(F(I(X)))`.

## Main results

* `homologyMap_mapHomologicalComplex_eq_homologyFunctor_map`
  (in `CochainComplex.InjectiveResolutionFunctor`): for every representative `r` of `ρ(φ)`,
  `H^ν(F(r))` is `H^ν(RF(φ))`, conjugated by the canonical isomorphisms.

## Implementation notes

The objects `H^ν(F(I(X)))` and `H^ν(RF(X))` are canonically isomorphic, not equal, so the
equality `H^ν(F(r)) = H^ν(RF(φ))` is stated up to these isomorphisms, which form the natural
isomorphism `rightDerivedFunctorCompHomologyIso`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4.
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionFunctor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

/-- The composite `RF ⋙ H^ν` of the derived functor of `F` defined by `ρ` with the `ν`-th
cohomology functor of `D(D)` is the functor `X ↦ H^ν(F(I(X)))`; the component at `X` is the
canonical isomorphism `H^ν(Q(F(I(X)))) ≅ H^ν(F(I(X)))`. -/
@[weil "lem_fka2_classical_derived_functor_is_cohomology_of_derived"]
noncomputable def rightDerivedFunctorCompHomologyIso (ν : ℤ) :
    ρ.rightDerivedFunctor F ⋙ homologyFunctor D ν ≅ ρ.classicalRightDerived F ν :=
  Functor.isoWhiskerLeft (ρ.functor ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ))
      (homologyFunctorFactorsh D ν) ≪≫
    (ρ.classicalRightDerivedIsoHomotopyCategory F ν).symm

/-- For every morphism `φ` of `D⁺(C)` and every morphism of complexes `r` representing
`ρ(φ)`, the cohomology `H^ν(F(r))` is `H^ν(RF(φ))`, up to the canonical isomorphisms
`H^ν(F(I(X))) ≅ H^ν(RF(X))`. In particular it does not depend on `r`. -/
@[weil "lem_fka2_classical_derived_functor_is_cohomology_of_derived"]
theorem homologyMap_mapHomologicalComplex_eq_homologyFunctor_map (ν : ℤ)
    {X Y : PlusComplexes C} (φ : X ⟶ Y)
    (r : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r = ρ.map φ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r) ν =
      ((ρ.rightDerivedFunctorCompHomologyIso F ν).app X).inv ≫
        (homologyFunctor D ν).map ((ρ.rightDerivedFunctor F).map φ) ≫
          ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Y).hom := by
  rw [Iso.app_inv, Iso.app_hom]
  exact ((NatIso.naturality_1 (ρ.rightDerivedFunctorCompHomologyIso F ν) φ).trans
    (ρ.classicalRightDerived_map_eq F ν φ r hr)).symm

/-- `H^ν(RF(φ))` is `H^ν(F(r))` for every representative `r` of `ρ(φ)`, up to the canonical
isomorphisms `H^ν(F(I(X))) ≅ H^ν(RF(X))`. -/
theorem homologyFunctor_map_rightDerivedFunctor_map_eq (ν : ℤ)
    {X Y : PlusComplexes C} (φ : X ⟶ Y)
    (r : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r = ρ.map φ) :
    (homologyFunctor D ν).map ((ρ.rightDerivedFunctor F).map φ) =
      ((ρ.rightDerivedFunctorCompHomologyIso F ν).app X).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r) ν ≫
          ((ρ.rightDerivedFunctorCompHomologyIso F ν).app Y).inv := by
  rw [← ρ.classicalRightDerived_map_eq F ν φ r hr, Iso.app_inv, Iso.app_hom]
  exact (NatIso.naturality_2 (ρ.rightDerivedFunctorCompHomologyIso F ν) φ).symm

end InjectiveResolutionFunctor

end CochainComplex

/-! ### Naturality of the degree-zero comparison map `F(M) ⟶ R⁰F(M[0])` -/

/-!
# Naturality of the degree-zero comparison map `F(M) ⟶ R⁰F(M[0])`

Let `F : C ⥤ D` be an additive functor between abelian categories, let `(I(X), i_X)` be a
choice of injective resolutions on the bounded below derived category and `ρ` an
injective-resolution functor for it, so that `R⁰F(X) = H⁰(F(I(X)))`. For an object `M` of `C`,
regarded as the complex `M[0]` concentrated in degree `0`, the resolution map
`i_{M[0]} : M[0] ⟶ I(M[0])` induces `H⁰(F(i_{M[0]})) : F(M) = H⁰(F(M[0])) ⟶ R⁰F(M[0])`.
This map is natural in `M`: for every morphism `f : M ⟶ N` of `C`,
`R⁰F(Q(f[0])) ∘ H⁰(F(i_{M[0]})) = H⁰(F(i_{N[0]})) ∘ F(f)`.

## Main definitions

* `DerivedCategory.PlusComplexes.singleZero`: the object `M[0]` of the bounded below derived
  category presented by complexes, and `DerivedCategory.PlusComplexes.singleZeroMap` the morphism
  `Q(f[0])`.
* `CochainComplex.InjectiveResolutionFunctor.degreeZeroMap`: the map
  `F(M) ⟶ R⁰F(M[0])` induced by `i_{M[0]}`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.homologyMap_ι_comp_classicalRightDerived_map`:
  `H⁰(F(i_{M[0]})) ≫ R⁰F(Q(f[0])) = H⁰(F(f[0])) ≫ H⁰(F(i_{N[0]}))`.
* `CochainComplex.InjectiveResolutionFunctor.degreeZeroMap_naturality`:
  `degreeZeroMap M ≫ R⁰F(Q(f[0])) = F(f) ≫ degreeZeroMap N`.

## Implementation notes

The identification `F(M) = H⁰(F(M[0]))` of the source is the isomorphism obtained from
`F(M[0]) ≅ F(M)[0]` (`HomologicalComplex.singleMapHomologicalComplex`) and
`H⁰(F(M)[0]) ≅ F(M)` (`HomologicalComplex.homologyFunctorSingleIso`); the first statement is
the identity before this identification, which is how it is proved.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II, p. 298.
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

namespace PlusComplexes

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The object `M[0]` of the bounded below derived category presented by complexes: the
complex with `M` in degree `0` and `0` elsewhere. -/
noncomputable def singleZero (M : C) : PlusComplexes C :=
  ⟨(HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M, 0, inferInstance⟩

/-- The morphism `Q(f[0]) : M[0] ⟶ N[0]` of the bounded below derived category induced by a
morphism `f : M ⟶ N` of `C`. -/
noncomputable def singleZeroMap {M N : C} (f : M ⟶ N) : singleZero M ⟶ singleZero N :=
  InducedCategory.homMk (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f)))

end PlusComplexes

end DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionFunctor

open DerivedCategory DerivedCategory.PlusComplexes

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

/-- The resolution map `i_{M[0]} : M[0] ⟶ I(M[0])` of the chosen injective resolution of
`M[0]`. -/
noncomputable abbrev singleZeroι (M : C) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M ⟶
      (c (singleZero M : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1
        (singleZero M).2).cocomplex :=
  (c (singleZero M : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 (singleZero M).2).ι

omit [F.Additive] in
include ρ in
/-- `ρ(Q(f[0])) ∘ i_{M[0]} = i_{N[0]} ∘ f[0]` in the homotopy category. -/
lemma quotient_map_singleZeroι_comp_map {M N : C} (f : M ⟶ N) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (singleZeroι (c := c) M) ≫
        ρ.map (singleZeroMap f) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f ≫ singleZeroι (c := c) N) := by
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ _).1
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  exact (ρ.comm (singleZeroMap f) :)

/-- `H⁰(F(i_{M[0]})) ≫ R⁰F(Q(f[0])) = H⁰(F(f[0])) ≫ H⁰(F(i_{N[0]}))`. -/
@[weil "lem_fka2_derived_functor_degree_zero_natural"]
lemma homologyMap_ι_comp_classicalRightDerived_map {M N : C} (f : M ⟶ N) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (singleZeroι (c := c) M)) 0 ≫
        (ρ.classicalRightDerived F 0).map (singleZeroMap f) =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f)) 0 ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (singleZeroι (c := c) N)) 0 := by
  rw [ρ.classicalRightDerived_map_eq F 0 (singleZeroMap f) (ρ.mapRep (singleZeroMap f))
    (ρ.quotient_map_mapRep _)]
  refine (HomologicalComplex.homologyMap_comp _ _ 0).symm.trans
    (Eq.trans ?_ (HomologicalComplex.homologyMap_comp _ _ 0))
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply homologyMap_mapHomologicalComplex_eq
  rw [Functor.map_comp, quotient_map_mapRep, quotient_map_singleZeroι_comp_map ρ f]

/-- The identification `F(M) ≅ H⁰(F(M[0]))`. -/
noncomputable def homologyZeroMapSingleIso (M : C) :
    F.obj M ≅ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)).homology 0 :=
  ((HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0).app (F.obj M)).symm ≪≫
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M).symm

omit [HasDerivedCategory C] in
lemma homologyZeroMapSingleIso_hom_naturality {M N : C} (f : M ⟶ N) :
    F.map f ≫ (homologyZeroMapSingleIso F N).hom =
      (homologyZeroMapSingleIso F M).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f)) 0 := by
  have h₁ := ((HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0).inv.naturality
    (F.map f))
  have h₂ := (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).congr_map
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.naturality f)
  simp only [Functor.map_comp] at h₂
  dsimp at h₁ h₂
  change F.map f ≫ ((HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0).inv.app
      (F.obj N) ≫ (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app N)) =
    ((HomologicalComplex.homologyFunctorSingleIso D (ComplexShape.up ℤ) 0).inv.app
      (F.obj M) ≫ (HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app M)) ≫ _
  rw [reassoc_of% h₁, h₂]
  exact (Category.assoc _ _ _).symm

/-- The map `H⁰(F(i_{M[0]})) : F(M) = H⁰(F(M[0])) ⟶ R⁰F(M[0])`. -/
noncomputable def degreeZeroMap (M : C) :
    F.obj M ⟶ (ρ.classicalRightDerived F 0).obj (singleZero M) :=
  (homologyZeroMapSingleIso F M).hom ≫
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (singleZeroι (c := c) M)) 0

/-- Naturality of `H⁰(F(i_{M[0]})) : F(M) ⟶ R⁰F(M[0])`: for every morphism `f : M ⟶ N`,
`R⁰F(Q(f[0])) ∘ H⁰(F(i_{M[0]})) = H⁰(F(i_{N[0]})) ∘ F(f)`. -/
@[weil "lem_fka2_derived_functor_degree_zero_natural"]
lemma degreeZeroMap_naturality {M N : C} (f : M ⟶ N) :
    ρ.degreeZeroMap F M ≫ (ρ.classicalRightDerived F 0).map (singleZeroMap f) =
      F.map f ≫ ρ.degreeZeroMap F N := by
  refine (Category.assoc _ _ _).trans ?_
  erw [homologyMap_ι_comp_classicalRightDerived_map]
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [← homologyZeroMapSingleIso_hom_naturality]
  exact Category.assoc _ _ _

end InjectiveResolutionFunctor

end CochainComplex

/-! ### The long exact sequence of derived functors of a short exact sequence of complexes -/

/-!
# The long exact sequence of derived functors of a short exact sequence of complexes

Let `F : C ⥤ D` be an additive functor between abelian categories, `C` with enough injectives,
let `RF : D⁺(C) ⥤ D⁺(D)` be its right derived functor and `R^νF = H^ν ∘ RF`. Let
`0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` be a short exact sequence of bounded below complexes, with maps `u` and
`v`, and let `w : Q(Z) ⟶ Q(X)⟦1⟧` be its connecting morphism in the derived category. Then the
sequence
`⋯ ⟶ R^νF(X) ⟶ R^νF(Y) ⟶ R^νF(Z) ⟶ R^{ν+1}F(X) ⟶ R^{ν+1}F(Y) ⟶ ⋯`
whose first two maps are `R^νF(Q u)` and `R^νF(Q v)` and whose third map is
`H^ν(c ∘ RF(w))`, for the commutation isomorphism `c : RF(X⟦1⟧) ≅ RF(X)⟦1⟧`, is exact.

More generally, the same holds for every admissible triangle `(X, Y, Z; u, v, w)` of `D⁺(C)`
(a triangle such that `(u, v, -w)` is distinguished).

## Main definitions

* `CategoryTheory.Functor.rightDerivedFunctorPlusHomologyδ`: for `w : X ⟶ Y⟦1⟧` in `D⁺(C)`,
  the morphism `H^{n₀}(c ∘ RF(w)) : R^{n₀}F(X) ⟶ R^{n₁}F(Y)`, where `n₀ + 1 = n₁`.
* `DerivedCategory.Plus.preimageShift`: a morphism `X ⟶ Y⟦1⟧` of `D(C)` between objects of
  `D⁺(C)`, as a morphism of `D⁺(C)`.

## Main results

* `CategoryTheory.Functor.rightDerivedFunctorPlusHomology_exact₂`,
  `CategoryTheory.Functor.rightDerivedFunctorPlusHomology_exact₃` and
  `CategoryTheory.Functor.rightDerivedFunctorPlusHomology_exact₁`: exactness at `R^νF(Y)`, at
  `R^νF(Z)` and at `R^{ν+1}F(X)` of the long sequence of a short exact sequence of bounded below
  complexes.
* `CategoryTheory.Functor.rightDerivedFunctorPlusHomology_exact₂_of_admissible` and its
  variants `exact₃`, `exact₁`: the same for an admissible triangle of `D⁺(C)`.
* `DerivedCategory.mk_neg_preimageShift_mem_distTriang`: the triangle `(Q u, Q v, -w)` of
  `D⁺(C)` attached to a short exact sequence of bounded below complexes is distinguished.

## Implementation notes

The short exact sequence is a short complex `S` of `CochainComplex.Plus C`, short exact as a
short complex of cochain complexes. The connecting morphism `w` is characterized as in
`DerivedCategory.mk_mem_admissibleTriangles_of_comp_eq_fst`, by `w ∘ Q(φ) = Q(π_u)` for the
cone-to-quotient map `φ : Cone(u) ⟶ Z` and the projection `π_u : Cone(u) ⟶ X⟦1⟧`; with
Mathlib's sign conventions it is `-DerivedCategory.triangleOfSESδ`. The commutation of `RF` with
the shift is the one given by the universal property of `RF`
(`CategoryTheory.Functor.commShiftRightDerivedFunctorPlus`), for which `RF` is a triangulated
functor; the exactness then follows from the long exact homology sequence of a homological
functor applied to a distinguished triangle.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988],
  Appendix A II.
-/

/- The `_of_admissible` lemmas are the long exact sequence of derived functors (FK A II),
stated on `D⁺(C)`. FK's connecting morphism `w` is the one
with `w ∘ Q(φ) = Q(π_u)` (as in `mk_mem_admissibleTriangles_of_comp_eq_fst`), i.e.
`-triangleOfSESδ`. -/

@[expose] public section

open CategoryTheory Limits Pretriangulated CochainComplex HomComplex

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A morphism `ι(X) ⟶ ι(Y)⟦1⟧` of `D(C)` between objects of `D⁺(C)`, as a morphism
`X ⟶ Y⟦1⟧` of `D⁺(C)`. -/
noncomputable def preimageShift {X Y : DerivedCategory.Plus C} (w : ι.obj X ⟶ (ι.obj Y)⟦(1 : ℤ)⟧) :
    X ⟶ Y⟦(1 : ℤ)⟧ :=
  ι.preimage (w ≫ (ι.commShiftIso (1 : ℤ)).inv.app Y)

@[simp]
lemma ι_map_preimageShift {X Y : DerivedCategory.Plus C} (w : ι.obj X ⟶ (ι.obj Y)⟦(1 : ℤ)⟧) :
    ι.map (preimageShift w) ≫ (ι.commShiftIso (1 : ℤ)).hom.app Y = w := by
  rw [preimageShift, Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id w

/-- The image in `D⁺(C)` of a short complex of bounded below complexes is a complex. -/
lemma Q_map_f_comp_Q_map_g (S : ShortComplex (CochainComplex.Plus C)) :
    Plus.Q.map S.f ≫ Plus.Q.map S.g = 0 :=
  ι.map_injective (by
    rw [Functor.map_comp, Functor.map_zero]
    change DerivedCategory.Q.map S.f.hom ≫ DerivedCategory.Q.map S.g.hom = 0
    have h₀ : S.f.hom ≫ S.g.hom = 0 := (S.map (CochainComplex.Plus.ι C)).zero
    rw [← Functor.map_comp, h₀, Functor.map_zero])

end DerivedCategory.Plus

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {S : ShortComplex (CochainComplex C ℤ)}

/-- `-triangleOfSESδ` satisfies the characterization `w ∘ Q(φ) = Q(π_u)` of the connecting
morphism, with the projection `π_u : Cone(u) ⟶ X⟦1⟧`, `(x, y) ↦ x`. -/
lemma comp_descShortComplex_neg_triangleOfSESδ (hS : S.ShortExact) :
    Q.map (mappingCone.descShortComplex S) ≫ (-triangleOfSESδ hS) =
      Q.map (Cocycle.homOf ((mappingCone.fst S.f).rightShift 1 0 (zero_add 1))) ≫
        (Q.commShiftIso (1 : ℤ)).hom.app S.X₁ :=
  (isConnectingMorphism_iff_fst _).1 (isConnectingMorphism_triangleOfSESδ hS)

/-- For a short exact sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` of bounded below complexes, with maps `u`
and `v` and connecting morphism `w` (`w ∘ Q(φ) = Q(π_u)`), the triangle `(Q u, Q v, -w)` of
`D⁺(C)` is distinguished. -/
lemma mk_neg_preimageShift_mem_distTriang {S : ShortComplex (CochainComplex.Plus C)}
    (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact)
    (w : Q.obj S.X₃.obj ⟶ (Q.obj S.X₁.obj)⟦(1 : ℤ)⟧)
    (hw : Q.map (mappingCone.descShortComplex (S.map (CochainComplex.Plus.ι C))) ≫ w =
      Q.map (Cocycle.homOf ((mappingCone.fst (S.map (CochainComplex.Plus.ι C)).f).rightShift 1 0
        (zero_add 1))) ≫ (Q.commShiftIso (1 : ℤ)).hom.app S.X₁.obj) :
    Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g)
        (-Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w) ∈
      distTriang (DerivedCategory.Plus C) := by
  have hT := (mem_admissibleTriangles_iff _).1 (mk_mem_admissibleTriangles_of_comp_eq_fst hS w hw)
  have h₃ : Plus.ι.map (-Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w) ≫
      (Plus.ι.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj S.X₁) = -w := by
    rw [Functor.map_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg
      (Plus.ι_map_preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w)
  change Plus.ι.mapTriangle.obj _ ∈ distTriang (DerivedCategory C)
  rw [Functor.mapTriangle_obj]
  exact (congrArg (Triangle.mk (Q.map (S.map (CochainComplex.Plus.ι C)).f)
    (Q.map (S.map (CochainComplex.Plus.ι C)).g)) h₃).symm ▸ hT

end DerivedCategory

namespace CategoryTheory.Functor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- For a morphism `w : X ⟶ Y⟦1⟧` of `D⁺(C)` and `n₀ + 1 = n₁`, the morphism
`H^{n₀}(c ∘ RF(w)) : R^{n₀}F(X) ⟶ R^{n₁}F(Y)`, where `c : RF(Y⟦1⟧) ≅ RF(Y)⟦1⟧` is the
commutation of `RF` with the shift and `H^{n₀}(RF(Y)⟦1⟧)` is identified with `H^{n₁}(RF(Y))`. -/
noncomputable def rightDerivedFunctorPlusHomologyδ {X Y : DerivedCategory.Plus C}
    (w : X ⟶ Y⟦(1 : ℤ)⟧)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.rightDerivedFunctorPlusHomology n₀).obj X ⟶ (F.rightDerivedFunctorPlusHomology n₁).obj Y :=
  (Plus.homologyFunctor D 0).shiftMap
    (F.rightDerivedFunctorPlus.map w ≫ (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app Y)
    n₀ n₁ (by omega)

lemma rightDerivedFunctorPlusHomologyδ_neg {X Y : DerivedCategory.Plus C} (w : X ⟶ Y⟦(1 : ℤ)⟧)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    F.rightDerivedFunctorPlusHomologyδ (-w) n₀ n₁ h =
      -F.rightDerivedFunctorPlusHomologyδ w n₀ n₁ h := by
  simp only [rightDerivedFunctorPlusHomologyδ, Functor.map_neg, Preadditive.neg_comp,
    Functor.shiftMap]
  rfl


/-- The negation `-𝟙` of the identity, as an automorphism. -/
private noncomputable def negIdIso {A : Type*} [Category* A] [Preadditive A] (X : A) : X ≅ X where
  hom := -𝟙 X
  inv := -𝟙 X

private lemma exact_mk_of_eq_neg_f {A : Type*} [Category* A] [Abelian A] {X₁ X₂ X₃ : A}
    {f f' : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (hfg : f ≫ g = 0) (hfg' : f' ≫ g = 0) (hf : f' = -f)
    (h : (ShortComplex.mk f' g hfg').Exact) : (ShortComplex.mk f g hfg).Exact := by
  subst hf
  exact (ShortComplex.exact_iff_of_iso (S₁ := ShortComplex.mk (-f) g hfg')
    (S₂ := ShortComplex.mk f g hfg)
    (ShortComplex.isoMk (negIdIso X₁) (Iso.refl _) (Iso.refl _)
      (by simp [negIdIso]) (by simp))).1 h

private lemma exact_mk_of_eq_neg_g {A : Type*} [Category* A] [Abelian A] {X₁ X₂ X₃ : A}
    {f : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃} (hfg : f ≫ g = 0) (hfg' : f ≫ g' = 0) (hg : g' = -g)
    (h : (ShortComplex.mk f g' hfg').Exact) : (ShortComplex.mk f g hfg).Exact := by
  subst hg
  exact (ShortComplex.exact_iff_of_iso (S₁ := ShortComplex.mk f (-g) hfg')
    (S₂ := ShortComplex.mk f g hfg)
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (negIdIso X₃)
      (by simp) (by simp [negIdIso]))).1 h

section Triangle

variable {T : Triangle (DerivedCategory.Plus C)}
  (hT : Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang (DerivedCategory.Plus C))
include hT

lemma rightDerivedFunctorPlusHomology_map_mor₁_comp_map_mor₂ (n : ℤ) :
    (F.rightDerivedFunctorPlusHomology n).map T.mor₁ ≫
      (F.rightDerivedFunctorPlusHomology n).map T.mor₂ = 0 := by
  have h₀ : T.mor₁ ≫ T.mor₂ = 0 :=
    comp_distTriang_mor_zero₁₂ (Triangle.mk T.mor₁ T.mor₂ (-T.mor₃)) hT
  rw [← Functor.map_comp, h₀, Functor.map_zero]

lemma rightDerivedFunctorPlusHomology_map_mor₂_comp_δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (F.rightDerivedFunctorPlusHomology n₀).map T.mor₂ ≫
      F.rightDerivedFunctorPlusHomologyδ T.mor₃ n₀ n₁ h = 0 := by
  have h₁ : (F.rightDerivedFunctorPlusHomology n₀).map T.mor₂ ≫
      F.rightDerivedFunctorPlusHomologyδ (-T.mor₃) n₀ n₁ h = 0 :=
    (Plus.homologyFunctor D 0).comp_homologySequenceδ _
      (F.rightDerivedFunctorPlus.map_distinguished _ hT) n₀ n₁ h
  rwa [rightDerivedFunctorPlusHomologyδ_neg, Preadditive.comp_neg, neg_eq_zero] at h₁

lemma rightDerivedFunctorPlusHomology_δ_comp_map_mor₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    F.rightDerivedFunctorPlusHomologyδ T.mor₃ n₀ n₁ h ≫
      (F.rightDerivedFunctorPlusHomology n₁).map T.mor₁ = 0 := by
  have h₁ : F.rightDerivedFunctorPlusHomologyδ (-T.mor₃) n₀ n₁ h ≫
      (F.rightDerivedFunctorPlusHomology n₁).map T.mor₁ = 0 :=
    (Plus.homologyFunctor D 0).homologySequenceδ_comp _
      (F.rightDerivedFunctorPlus.map_distinguished _ hT) n₀ n₁ h
  rwa [rightDerivedFunctorPlusHomologyδ_neg, Preadditive.neg_comp, neg_eq_zero] at h₁

/-- Exactness at `R^nF(Y)` of the long sequence of an admissible triangle `(X, Y, Z; u, v, w)`
of `D⁺(C)`. -/
lemma rightDerivedFunctorPlusHomology_exact₂_of_admissible (n : ℤ) :
    (ShortComplex.mk _ _
      (F.rightDerivedFunctorPlusHomology_map_mor₁_comp_map_mor₂ hT n)).Exact :=
  (Plus.homologyFunctor D 0).homologySequence_exact₂ _
    (F.rightDerivedFunctorPlus.map_distinguished _ hT) n

/-- Exactness at `R^{n₀}F(Z)` of the long sequence of an admissible triangle
`(X, Y, Z; u, v, w)` of `D⁺(C)`. -/
lemma rightDerivedFunctorPlusHomology_exact₃_of_admissible (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (F.rightDerivedFunctorPlusHomology_map_mor₂_comp_δ hT n₀ n₁ h)).Exact :=
  exact_mk_of_eq_neg_g _ _ (F.rightDerivedFunctorPlusHomologyδ_neg T.mor₃ n₀ n₁ h)
    ((Plus.homologyFunctor D 0).homologySequence_exact₃ _
      (F.rightDerivedFunctorPlus.map_distinguished _ hT) n₀ n₁ h)

/-- Exactness at `R^{n₁}F(X)` of the long sequence of an admissible triangle
`(X, Y, Z; u, v, w)` of `D⁺(C)`. -/
lemma rightDerivedFunctorPlusHomology_exact₁_of_admissible (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (F.rightDerivedFunctorPlusHomology_δ_comp_map_mor₁ hT n₀ n₁ h)).Exact :=
  exact_mk_of_eq_neg_f _ _ (F.rightDerivedFunctorPlusHomologyδ_neg T.mor₃ n₀ n₁ h)
    ((Plus.homologyFunctor D 0).homologySequence_exact₁ _
      (F.rightDerivedFunctorPlus.map_distinguished _ hT) n₀ n₁ h)

end Triangle

section ShortExact

variable {S : ShortComplex (CochainComplex.Plus C)}
  (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact)
include hS

/-- **Long exact sequence of derived functors, exactness at `R^nF(Y)`.** For a short exact
sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` of bounded below complexes, with maps `u` and `v`, the sequence
`R^nF(X) ⟶ R^nF(Y) ⟶ R^nF(Z)` of the maps `R^nF(Q u)` and `R^nF(Q v)` is exact. -/
@[weil "lem_fka2_ses_derived_functors_long_exact"]
theorem rightDerivedFunctorPlusHomology_exact₂_of_shortExact (n : ℤ) :
    (ShortComplex.mk ((F.rightDerivedFunctorPlusHomology n).map (Plus.Q.map S.f))
      ((F.rightDerivedFunctorPlusHomology n).map (Plus.Q.map S.g)) (by
        rw [← Functor.map_comp, Plus.Q_map_f_comp_Q_map_g, Functor.map_zero])).Exact :=
  F.rightDerivedFunctorPlusHomology_exact₂_of_admissible
    (T := Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g)
      (Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) (-triangleOfSESδ hS)))
    (mk_neg_preimageShift_mem_distTriang hS _ (comp_descShortComplex_neg_triangleOfSESδ hS)) n

variable (w : Q.obj S.X₃.obj ⟶ (Q.obj S.X₁.obj)⟦(1 : ℤ)⟧)
  (hw : Q.map (mappingCone.descShortComplex (S.map (CochainComplex.Plus.ι C))) ≫ w =
    Q.map (Cocycle.homOf ((mappingCone.fst (S.map (CochainComplex.Plus.ι C)).f).rightShift 1 0
      (zero_add 1))) ≫ (Q.commShiftIso (1 : ℤ)).hom.app S.X₁.obj)
include hw

/-- **Long exact sequence of derived functors, exactness at `R^{n₀}F(Z)`.** For a short exact
sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` of bounded below complexes, with maps `u` and `v` and connecting
morphism `w : Q(Z) ⟶ Q(X)⟦1⟧`, and `n₀ + 1 = n₁`, the sequence
`R^{n₀}F(Y) ⟶ R^{n₀}F(Z) ⟶ R^{n₁}F(X)` of the maps `R^{n₀}F(Q v)` and `H^{n₀}(c ∘ RF(w))` is
exact. -/
@[weil "lem_fka2_ses_derived_functors_long_exact"]
theorem rightDerivedFunctorPlusHomology_exact₃_of_shortExact (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk ((F.rightDerivedFunctorPlusHomology n₀).map (Plus.Q.map S.g))
      (F.rightDerivedFunctorPlusHomologyδ
        (Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w) n₀ n₁ h)
      (F.rightDerivedFunctorPlusHomology_map_mor₂_comp_δ
        (T := Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g)
          (Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w))
        (mk_neg_preimageShift_mem_distTriang hS w hw) n₀ n₁ h)).Exact :=
  F.rightDerivedFunctorPlusHomology_exact₃_of_admissible
    (T := Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g)
      (Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w))
    (mk_neg_preimageShift_mem_distTriang hS w hw) n₀ n₁ h

/-- **Long exact sequence of derived functors, exactness at `R^{n₁}F(X)`.** For a short exact
sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` of bounded below complexes, with maps `u` and `v` and connecting
morphism `w : Q(Z) ⟶ Q(X)⟦1⟧`, and `n₀ + 1 = n₁`, the sequence
`R^{n₀}F(Z) ⟶ R^{n₁}F(X) ⟶ R^{n₁}F(Y)` of the maps `H^{n₀}(c ∘ RF(w))` and `R^{n₁}F(Q u)` is
exact. -/
@[weil "lem_fka2_ses_derived_functors_long_exact"]
theorem rightDerivedFunctorPlusHomology_exact₁_of_shortExact (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk
      (F.rightDerivedFunctorPlusHomologyδ
        (Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w) n₀ n₁ h)
      ((F.rightDerivedFunctorPlusHomology n₁).map (Plus.Q.map S.f))
      (F.rightDerivedFunctorPlusHomology_δ_comp_map_mor₁
        (T := Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g)
          (Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w))
        (mk_neg_preimageShift_mem_distTriang hS w hw) n₀ n₁ h)).Exact :=
  F.rightDerivedFunctorPlusHomology_exact₁_of_admissible
    (T := Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g)
      (Plus.preimageShift (X := Plus.Q.obj S.X₃) (Y := Plus.Q.obj S.X₁) w))
    (mk_neg_preimageShift_mem_distTriang hS w hw) n₀ n₁ h

end ShortExact

end CategoryTheory.Functor
