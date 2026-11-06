module

public import Weil.Algebra.Homology.DerivedCategory.InjectiveResolutionComparisonIsIso
public import Weil.Algebra.Homology.DerivedCategory.InjectiveResolutionUniqueUpToHomotopy
public import Weil.Defs.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Weil.Attr
public import Weil.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective

/-!
# The right derived functor computed by any injective resolution

Let `F : C ⥤ D` be an additive functor between abelian categories, `ρ` an injective-resolution
functor for a choice `(I(X), i_X)` of injective resolutions on `D⁺(C)`, and `RF` the
corresponding right derived functor, so that `RF(X) = F(I(X))`. If `(J, j)` is any injective
resolution of `X` and `g : I(X) ⟶ J` is the morphism of the homotopy category `K(C)` with
`g ∘ i_X = j`, then the image `Q(F(g)) : RF(X) ⟶ F(J)` of `g` in `D(D)` is an isomorphism:
`g` is an isomorphism of `K(C)`, and the functors `K(C) ⥤ K(D)` induced by `F` and
`Q : K(D) ⥤ D(D)` preserve isomorphisms.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.isIso_rightDerivedFunctor_comparison`:
  `Q(F(g)) : RF(X) ⟶ F(J)` is an isomorphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4.
-/

@[expose] public section

open CategoryTheory

namespace CochainComplex

namespace InjectiveResolutionFunctor

open DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

/-- Let `X` be an object of `D⁺(C)`, `(J, j)` an injective resolution of `X`, and
`g : I(X) ⟶ J` a morphism of the homotopy category with `g ∘ i_X = j`. Then the image
`Q(F(g)) : RF(X) ⟶ F(J)` of `F(g)` in the derived category of `D` is an isomorphism. -/
@[weil "lem_fka2_right_derived_functor_comparison_iso"]
theorem isIso_rightDerivedFunctor_comparison (X : PlusComplexes C)
    (R : InjectiveResolutionPlus (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1)
    (g : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex)
    (hg : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).ι ≫ g =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι) :
    IsIso (Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map g) :
      (ρ.rightDerivedFunctor F).obj X ⟶
        Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj R.cocomplex))) := by
  have h := InjectiveResolutionPlus.isIso_of_comp_eq _ R g hg
  have : IsIso (Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map g)) := inferInstance
  exact this

end InjectiveResolutionFunctor

end CochainComplex

end

/-! ### The right derived functor of a choice of injective resolutions is well defined -/

/-!
# The right derived functor of a choice of injective resolutions is well defined

Let `F : C ⥤ D` be an additive functor between abelian categories and `ρ` an
injective-resolution functor for a choice `X ↦ (I(X), i_X)` of injective resolutions on the
bounded below derived category. For a morphism `φ : X ⟶ Y` of `D⁺(C)`, the value `RF(φ)` is the
image in `D(D)` of `F(r)`, where `r : I(X) ⟶ I(Y)` is a morphism of complexes representing the
homotopy class `ρ(φ)`. We show that this does not depend on the representative `r`: two
representatives are homotopic, hence so are their images under `F`, which therefore have the
same image in the homotopy category. Moreover the assignment is functorial: representatives of
`ρ(𝟙 X)` are sent to the identity, and representatives of `ρ(φ)`, `ρ(ψ)` and `ρ(φ ≫ ψ)` give a
commutative triangle in `D(D)`; indeed `RF` is the composite of the functors `ρ`,
`F : K(C) ⥤ K(D)` and `Q : K(D) ⥤ D(D)`.

## Main results

* `CochainComplex.InjectiveResolutionFunctor.Qh_map_mapHomologicalComplex_eq_of_representatives`:
  two representatives of `ρ(φ)` have the same image `Q(F(r)) = Q(F(r'))`.
* `CochainComplex.InjectiveResolutionFunctor.Qh_map_mapHomologicalComplex_id_of_representative`:
  a representative of `ρ(𝟙 X)` gives the identity of `RF(X)`.
* `CochainComplex.InjectiveResolutionFunctor.Qh_map_mapHomologicalComplex_comp_of_representatives`:
  representatives of `ρ(φ)`, `ρ(ψ)`, `ρ(φ ≫ ψ)` give `Q(F(t)) = Q(F(r)) ≫ Q(F(s))`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.4, p. 297.
-/

@[expose] public section

open CategoryTheory Limits DerivedCategory

namespace CochainComplex

namespace InjectiveResolutionFunctor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)
  (F : C ⥤ D) [F.Additive]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- Two morphisms of complexes with the same homotopy class have images under `F` with the same
class in the homotopy category: a homotopy `r ≃ r'` is carried by `F` to a homotopy
`F(r) ≃ F(r')`. -/
lemma quotient_map_mapHomologicalComplex_eq_of_quotient_map_eq
    {K L : CochainComplex C ℤ} {r r' : K ⟶ L}
    (h : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r') :
    (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r') :=
  HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy (HomotopyCategory.homotopyOfEq _ _ h))

/-- The value `RF(φ) = Q(F(r))` does not depend on the morphism of complexes `r` representing
`ρ(φ)`. -/
@[weil "lem_fka2_right_derived_functor_well_defined"]
theorem Qh_map_mapHomologicalComplex_eq_of_representatives {X Y : PlusComplexes C}
    (φ : X ⟶ Y)
    (r r' : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r = ρ.map φ)
    (hr' : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r' = ρ.map φ) :
    Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r)) =
      Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r')) := by
  rw [quotient_map_mapHomologicalComplex_eq_of_quotient_map_eq F (hr.trans hr'.symm)]

/-- A representative `r` of `ρ(𝟙 X)` gives the identity `Q(F(r)) = 𝟙` of `RF(X)`. -/
@[weil "lem_fka2_right_derived_functor_well_defined"]
theorem Qh_map_mapHomologicalComplex_id_of_representative (X : PlusComplexes C)
    (r : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r = ρ.map (𝟙 X)) :
    Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r)) = 𝟙 _ := by
  rw [← rightDerivedFunctor_map_eq ρ F (𝟙 X) r hr]
  exact (ρ.rightDerivedFunctor F).map_id X

/-- Representatives `r`, `s`, `t` of `ρ(φ)`, `ρ(ψ)` and `ρ(φ ≫ ψ)` satisfy
`Q(F(t)) = Q(F(r)) ≫ Q(F(s))`. -/
@[weil "lem_fka2_right_derived_functor_well_defined"]
theorem Qh_map_mapHomologicalComplex_comp_of_representatives {X Y Z : PlusComplexes C}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (r : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex)
    (s : (c (Y : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Y.2).cocomplex ⟶
      (c (Z : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Z.2).cocomplex)
    (t : (c (X : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 X.2).cocomplex ⟶
      (c (Z : {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}).1 Z.2).cocomplex)
    (hr : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map r = ρ.map φ)
    (hs : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map s = ρ.map ψ)
    (ht : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map t = ρ.map (φ ≫ ψ)) :
    Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map t)) =
      Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map r)) ≫
        Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) := by
  rw [← rightDerivedFunctor_map_eq ρ F _ t ht, ← rightDerivedFunctor_map_eq ρ F _ r hr,
    ← rightDerivedFunctor_map_eq ρ F _ s hs]
  exact (ρ.rightDerivedFunctor F).map_comp φ ψ

end InjectiveResolutionFunctor

end CochainComplex

/-! ### Complexes of acyclic objects compute right derived functors -/

/-!
# Complexes of acyclic objects compute right derived functors

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `K` be a bounded below complex all of whose terms are right acyclic for `F`.
For every injective resolution `i : K ⟶ I` of `K`, the morphism `F(i) : F(K) ⟶ F(I)` becomes an
isomorphism in the derived category `D(D)`. In particular, for a choice of injective resolutions
`(I(X), i_X)` on `D⁺(C)` and the derived functor `RF` attached to it, the map
`Q(F(i_K)) : F(K) ⟶ RF(K)` is an isomorphism.

## Main results

* `CochainComplex.exists_isGE_of_exists_isStrictlyGE`: a strictly bounded below complex is
  cohomologically bounded below.
* `CochainComplex.InjectiveResolutionPlus.isIso_Qh_map_map_ι_of_rightAcyclic`: `Q(F(i))` is an
  isomorphism for every injective resolution `i` of a bounded below complex of `F`-acyclic
  objects.
* `CochainComplex.InjectiveResolutionFunctor.isIso_Qh_map_map_ι_of_rightAcyclic`: the map
  `F(K) ⟶ RF(K)` given by the chosen resolution `i_K` is an isomorphism.

## Implementation notes

The proof deduces the statement from Leray's acyclicity lemma
`CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic` by naturality of the unit
`F.rightDerivedFunctorPlusUnit` along the quasi-isomorphism `i`, the unit being invertible on the
complex of injectives `I`. The source argues with the mapping cone of `i` instead; the two routes
prove the same statement. `F`-acyclicity is `CategoryTheory.Functor.rightAcyclic`, which for a
left exact `F` is the vanishing of the higher derived functors
(`CategoryTheory.Functor.rightAcyclic_iff_forall_isZero_rightDerivedPlus`); left exactness is not
needed for the statement in this form.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.
* [Stacks, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

public section

open CategoryTheory Limits DerivedCategory

-- Instance search for the right derived functor otherwise times out; the cheap instance coming
-- from `EnoughInjectives` is tried first, as in StacksFrontier's derived-category files.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CochainComplex

/-- A strictly bounded below complex is cohomologically bounded below. -/
lemma exists_isGE_of_exists_isStrictlyGE {C : Type*} [Category* C] [Abelian C]
    {K : CochainComplex C ℤ} (hK : ∃ n : ℤ, K.IsStrictlyGE n) : ∃ n : ℤ, K.IsGE n := by
  obtain ⟨n, _⟩ := hK
  exact ⟨n, inferInstance⟩

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

namespace InjectiveResolutionPlus

/-- If `K` is a bounded below complex all of whose terms are right acyclic for `F`, then for
every injective resolution `i : K ⟶ I` the morphism `F(i) : F(K) ⟶ F(I)` becomes an isomorphism
in the derived category. -/
theorem isIso_Qh_map_map_ι_of_rightAcyclic (F : C ⥤ D) [F.Additive] {K : CochainComplex C ℤ}
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hKF : ∀ n, F.rightAcyclic (K.X n))
    (R : InjectiveResolutionPlus K) :
    IsIso (Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι))) := by
  let Kp : CochainComplex.Plus C := ⟨K, hK⟩
  let Ip : CochainComplex.Plus C := (InjectiveObject.ι C).mapCochainComplexPlus.obj R.I
  let g : Kp ⟶ Ip := ObjectProperty.homMk R.ι
  let g' := (HomotopyCategory.Plus.quotient C).map g
  have h₁ : IsIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj Kp)) :=
    Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic F K hK hKF
  have h₂ : IsIso (Plus.Qh.map g') := by
    have : IsIso (TStructure.t.plus.ι.map (Plus.Qh.map g')) := by
      change IsIso (Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map R.ι))
      rw [← Functor.comp_map, NatIso.isIso_map_iff (quotientCompQhIso C),
        isIso_Q_map_iff_quasiIso]
      infer_instance
    exact TStructure.t.plus.fullyFaithfulι.isIso_of_isIso_map _
  have hnat := F.rightDerivedFunctorPlusUnit.naturality g'
  have h₃ : IsIso ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map g') := by
    have : IsIso ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map g' ≫
        F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj Ip)) := by
      have : IsIso ((Plus.Qh ⋙ F.rightDerivedFunctorPlus).map g') := by
        rw [Functor.comp_map]; infer_instance
      rw [hnat]; infer_instance
    exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlusUnit.app _)
  exact (inferInstance :
    IsIso (DerivedCategory.Plus.ι.map ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map g')))

end InjectiveResolutionPlus

namespace InjectiveResolutionFunctor

variable {c : ChoiceOfInjectiveResolutions C} (ρ : InjectiveResolutionFunctor c)

/-- **Acyclic complexes compute the derived functor.** Let `(I(X), i_X)` be a choice of injective
resolutions on `D⁺(C)`, `ρ` an injective-resolution functor for it and `RF` the derived functor of
`F` attached to `ρ`. If `K` is a bounded below complex all of whose terms are `F`-acyclic, then
`Q(F(i_K)) : F(K) ⟶ RF(K) = F(I(K))` is an isomorphism in `D(D)`. -/
@[weil "lem_fka2_acyclic_complex_computes_derived"]
theorem isIso_Qh_map_map_ι_of_rightAcyclic (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hKF : ∀ n, F.rightAcyclic (K.X n)) :
    IsIso (X := Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
      (Y := (ρ.rightDerivedFunctor F).obj
        (⟨K, exists_isGE_of_exists_isStrictlyGE hK⟩ :
          {K : CochainComplex C ℤ // ∃ n : ℤ, K.IsGE n}))
      (Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (c K (exists_isGE_of_exists_isStrictlyGE hK)).ι))) :=
  (c K _).isIso_Qh_map_map_ι_of_rightAcyclic F hK hKF

end InjectiveResolutionFunctor

end CochainComplex
