module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Weil.Attr
public import Weil.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Weil.Algebra.Homology.DerivedCategory.InjectiveResolutionComparisonIsIso
public import Weil.Algebra.Homology.DerivedCategory.InjectiveResolutionUniqueUpToHomotopy
public import Weil.Defs.Algebra.Homology.DerivedCategory.ClassicalDerivedFunctor

/-!
# Cohomology computed by injective resolutions is well defined

Let `F : C ⥤ D` be an additive functor between abelian categories and `X : C`. For two
injective resolutions `I` and `J` of `X`, the cohomology objects `Hⁿ(F(I))` and `Hⁿ(F(J))` are
canonically isomorphic: a morphism of resolutions over `𝟙 X` exists and is unique up to homotopy,
and `F`, being additive, carries homotopies to homotopies. These isomorphisms are compatible with
composition for three resolutions, and the maps induced by a morphism `X ⟶ Y` (through any lift
to the resolutions) are independent of the lift and functorial. With chosen resolutions these
isomorphisms identify `Hⁿ(F(I))` with the right derived functor `(F.rightDerived n).obj X`.

Applied to the abelian category of sheaves of abelian groups on the small étale site of a
scheme `X` and to the global sections functor `Γ(X, -)`, this says that the étale cohomology
groups `Hⁿ(X, 𝓕) = Hⁿ(Γ(X, 𝓘•))` are well defined up to canonical isomorphism and functorial
in `𝓕`.

## Main definitions

* `CategoryTheory.InjectiveResolution.homologyMapOfHom`: the map `Hⁿ(F(I)) ⟶ Hⁿ(F(J))` induced
  by `f : X ⟶ Y` for resolutions `I` of `X` and `J` of `Y`.
* `CategoryTheory.InjectiveResolution.homologyIso`: the canonical isomorphism
  `Hⁿ(F(I)) ≅ Hⁿ(F(J))` for two resolutions of the same object.
* `AlgebraicGeometry.Scheme.etaleGlobalSections`: the functor `Γ(X, -)` on étale sheaves of
  abelian groups, the value at the object `𝟙 X` of the small étale site.

## Main results

* `CategoryTheory.InjectiveResolution.homologyMapOfHom_eq`: any lift of `f` induces the map.
* `CategoryTheory.InjectiveResolution.homologyMapOfHom_id`,
  `CategoryTheory.InjectiveResolution.homologyMapOfHom_comp`: functoriality.
* `CategoryTheory.InjectiveResolution.homologyIso_refl`,
  `CategoryTheory.InjectiveResolution.homologyIso_trans`: compatibility for three resolutions.
* `CategoryTheory.InjectiveResolution.isoRightDerivedObj_symm_trans`: the canonical isomorphism
  is the one through the right derived functor.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe v u v' u' w

namespace CategoryTheory

open Category Limits

namespace InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- The map `Hⁿ(F(I)) ⟶ Hⁿ(F(J))` induced by a morphism `f : X ⟶ Y`, for an injective
resolution `I` of `X` and an injective resolution `J` of `Y`. -/
noncomputable def homologyMapOfHom {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (n : ℕ) :
    ((F.mapHomologicalComplex _).obj I.cocomplex).homology n ⟶
      ((F.mapHomologicalComplex _).obj J.cocomplex).homology n :=
  HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map (desc f J I)) n

/-- The map induced by `f` on `Hⁿ(F(-))` may be computed by any cochain map of resolutions
lifting `f`. -/
@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem homologyMapOfHom_eq {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    homologyMapOfHom F f I J n =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n := by
  unfold homologyMapOfHom
  apply Homotopy.homologyMap_eq
  apply F.mapHomotopy
  apply descHomotopy f
  all_goals aesop

@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem homologyMapOfHom_id {X : C} (I : InjectiveResolution X) (n : ℕ) :
    homologyMapOfHom F (𝟙 X) I I n = 𝟙 _ := by
  rw [homologyMapOfHom_eq F (𝟙 X) I I (𝟙 _) ((comp_id _).trans (id_comp _).symm), Functor.map_id,
    HomologicalComplex.homologyMap_id]

@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem homologyMapOfHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (K : InjectiveResolution Z) (n : ℕ) :
    homologyMapOfHom F (f ≫ g) I K n = homologyMapOfHom F f I J n ≫ homologyMapOfHom F g J K n := by
  rw [homologyMapOfHom_eq F (f ≫ g) I K (desc f J I ≫ desc g K J)
      (by
        rw [HomologicalComplex.comp_f, desc_commutes_zero_assoc]
        erw [assoc, desc_commutes_zero, ← assoc]
        rfl),
    Functor.map_comp, HomologicalComplex.homologyMap_comp]
  rfl

/-- The canonical isomorphism `Hⁿ(F(I)) ≅ Hⁿ(F(J))` between the cohomologies of `F` applied to
two injective resolutions `I`, `J` of the same object, induced by the homotopy equivalence
`I.homotopyEquiv J`. -/
@[weil "lem_fk102_etale_cohomology_well_defined"]
noncomputable def homologyIso {X : C} (I J : InjectiveResolution X) (n : ℕ) :
    ((F.mapHomologicalComplex _).obj I.cocomplex).homology n ≅
      ((F.mapHomologicalComplex _).obj J.cocomplex).homology n :=
  (F.mapHomotopyEquiv (I.homotopyEquiv J)).toHomologyIso n

theorem homologyIso_hom {X : C} (I J : InjectiveResolution X) (n : ℕ) :
    (homologyIso F I J n).hom = homologyMapOfHom F (𝟙 X) I J n :=
  rfl

theorem homologyIso_inv {X : C} (I J : InjectiveResolution X) (n : ℕ) :
    (homologyIso F I J n).inv = homologyMapOfHom F (𝟙 X) J I n :=
  rfl

/-- The canonical isomorphism does not depend on the chosen morphism of resolutions. -/
@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem homologyIso_hom_eq {X : C} (I J : InjectiveResolution X)
    (φ : I.cocomplex ⟶ J.cocomplex) (comm : I.ι.f 0 ≫ φ.f 0 = J.ι.f 0) (n : ℕ) :
    (homologyIso F I J n).hom =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) n := by
  rw [homologyIso_hom, homologyMapOfHom_eq F (𝟙 X) I J φ (comm.trans (id_comp _).symm)]

@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem homologyIso_refl {X : C} (I : InjectiveResolution X) (n : ℕ) :
    homologyIso F I I n = Iso.refl _ := by
  ext
  rw [homologyIso_hom, homologyMapOfHom_id]
  rfl

/-- The canonical isomorphisms are compatible with composition for three resolutions. -/
@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem homologyIso_trans {X : C} (I J K : InjectiveResolution X) (n : ℕ) :
    homologyIso F I J n ≪≫ homologyIso F J K n = homologyIso F I K n := by
  ext
  simp only [Iso.trans_hom, homologyIso_hom]
  rw [← homologyMapOfHom_comp, id_comp]

theorem homologyIso_symm {X : C} (I J : InjectiveResolution X) (n : ℕ) :
    (homologyIso F I J n).symm = homologyIso F J I n := by
  ext
  rfl

/-- The maps induced by a morphism commute with the canonical isomorphisms. -/
@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem homologyMapOfHom_comp_homologyIso_hom {X Y : C} (f : X ⟶ Y)
    (I I' : InjectiveResolution X) (J J' : InjectiveResolution Y) (n : ℕ) :
    homologyMapOfHom F f I J n ≫ (homologyIso F J J' n).hom =
      (homologyIso F I I' n).hom ≫ homologyMapOfHom F f I' J' n := by
  simp only [homologyIso_hom]
  rw [← homologyMapOfHom_comp, ← homologyMapOfHom_comp, comp_id, id_comp]

section RightDerived

variable [HasInjectiveResolutions C]

/-- Through the right derived functor `F.rightDerived n`, the identifications of
`(F.rightDerived n).obj X` with `Hⁿ(F(I))` and `Hⁿ(F(J))` differ by the canonical
isomorphism `homologyIso`. -/
@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem isoRightDerivedObj_symm_trans {X : C} (I J : InjectiveResolution X) (n : ℕ) :
    (I.isoRightDerivedObj F n).symm ≪≫ J.isoRightDerivedObj F n = homologyIso F I J n := by
  have h := isoRightDerivedObj_hom_naturality (𝟙 X) I J (desc (𝟙 X) J I)
    (desc_commutes_zero _ _ _) F n
  rw [Functor.map_id, id_comp] at h
  ext
  rw [Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq, h]
  rfl

/-- Under the identifications with the right derived functor, the map induced by `f` on
`Hⁿ(F(-))` is `(F.rightDerived n).map f`. -/
@[weil "lem_fk102_etale_cohomology_well_defined"]
theorem rightDerived_map_eq_homologyMapOfHom {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (n : ℕ) :
    (F.rightDerived n).map f =
      (I.isoRightDerivedObj F n).hom ≫ homologyMapOfHom F f I J n ≫
        (J.isoRightDerivedObj F n).inv := by
  have h := isoRightDerivedObj_hom_naturality f I J (desc f J I) (desc_commutes_zero _ _ _) F n
  exact ((Iso.eq_comp_inv _).2 h).trans (assoc _ _ _)

end RightDerived

end InjectiveResolution

end CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory Opposite

/-- The global sections functor `Γ(X, -)` on sheaves of abelian groups on the small étale site
of `X`: the value at the object `𝟙 X` of `X.Etale`. -/
noncomputable abbrev etaleGlobalSections (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (op (MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)))

instance (X : Scheme.{u}) : (etaleGlobalSections X).Additive where
  map_add := rfl

example (X : Scheme.{u}) :
    HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  inferInstance

end AlgebraicGeometry.Scheme

/-! ### The classical derived functor in degree zero -/

/-!
# The classical derived functor in degree zero

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, `C` having enough
injectives. For an object `M` of `C`, let `M[0]` be the complex with `M` in degree `0` and `0`
elsewhere, and let `i : M[0] ⟶ I(M[0])` be an injective resolution. Then
`H⁰(F(i)) : F(M) = H⁰(F(M[0])) ⟶ H⁰(F(I(M[0]))) = R⁰F(M[0])` is an isomorphism.

The proof compares `I(M[0])` with an injective resolution `J` of `M[0]` which vanishes in
negative degrees. For `J`, the statement is the left exactness of `F`: in degree `0`, the
cohomology of a complex vanishing in negative degrees is the kernel of its differential, and
`F` preserves kernels. The comparison morphism `I(M[0]) ⟶ J` is a homotopy equivalence, so it
induces isomorphisms on the cohomology of the images under `F`.

## Main results

* `CochainComplex.isIso_homologyMap_mapHomologicalComplex_zero`: for a left exact `F` and a
  morphism `φ : K ⟶ L` of complexes vanishing in negative degrees, if `H⁰(φ)` is an
  isomorphism then so is `H⁰(F(φ))`.
* `CochainComplex.InjectiveResolutionPlus.isIso_homologyMap_map_ι_single_zero`: `H⁰(F(i))` is an
  isomorphism for every injective resolution `i : M[0] ⟶ I` of `M[0]`.
* `CochainComplex.isIso_homologyMap_map_choiceOfInjectiveResolutions_single_zero`: the same for
  the resolution `i_{M[0]}` given by a choice of injective resolutions.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl],
  Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- For a left exact functor `F`, the canonical morphism `F(Z⁰(K)) ⟶ Z⁰(F(K))` from the image of
the cycles in degree `0` to the cycles of the image is an isomorphism. -/
noncomputable def mapCyclesZeroIso (K : CochainComplex C ℤ) :
    F.obj (K.cycles 0) ≅ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).cycles 0 :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.mapIsLimit _ (K.cyclesIsKernel 0 1 (by simp)) F)
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).cyclesIsKernel 0 1 (by simp))

@[reassoc (attr := simp)]
lemma mapCyclesZeroIso_hom_iCycles (K : CochainComplex C ℤ) :
    (mapCyclesZeroIso F K).hom ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).iCycles 0 =
      F.map (K.iCycles 0) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

lemma map_cyclesMap_comp_mapCyclesZeroIso_hom {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    F.map (HomologicalComplex.cyclesMap φ 0) ≫ (mapCyclesZeroIso F L).hom =
      (mapCyclesZeroIso F K).hom ≫
        HomologicalComplex.cyclesMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0 := by
  rw [← cancel_mono (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).iCycles 0)]
  simp only [Category.assoc, mapCyclesZeroIso_hom_iCycles, HomologicalComplex.cyclesMap_i,
    mapCyclesZeroIso_hom_iCycles_assoc, ← F.map_comp, Functor.mapHomologicalComplex_map_f]

lemma isIso_homologyπ_zero_of_isZero (K : CochainComplex C ℤ) (hK : IsZero (K.X (-1))) :
    IsIso (K.homologyπ 0) :=
  K.isIso_homologyπ (-1) 0 (by simp) (hK.eq_of_src _ _)

/-- Let `F` be left exact and `φ : K ⟶ L` a morphism of cochain complexes vanishing in negative
degrees. If `H⁰(φ)` is an isomorphism, then so is `H⁰(F(φ))`. -/
lemma isIso_homologyMap_mapHomologicalComplex_zero {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] [IsIso (HomologicalComplex.homologyMap φ 0)] :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
  have hK := K.isZero_of_isStrictlyGE 0 (-1)
  have hL := L.isZero_of_isStrictlyGE 0 (-1)
  have := isIso_homologyπ_zero_of_isZero K hK
  have := isIso_homologyπ_zero_of_isZero L hL
  have := isIso_homologyπ_zero_of_isZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (F.map_isZero hK)
  have := isIso_homologyπ_zero_of_isZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
    (F.map_isZero hL)
  have h₁ : IsIso (HomologicalComplex.cyclesMap φ 0) := by
    have h := HomologicalComplex.homologyπ_naturality φ 0
    have : IsIso (HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right _ (L.homologyπ 0)
  have h₂ : IsIso (HomologicalComplex.cyclesMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
    have h := map_cyclesMap_comp_mapCyclesZeroIso_hom F φ
    have : IsIso ((mapCyclesZeroIso F K).hom ≫ HomologicalComplex.cyclesMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_left (mapCyclesZeroIso F K).hom _
  have h := HomologicalComplex.homologyπ_naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0
  have : IsIso (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ 0 ≫
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
    rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ 0) _

namespace InjectiveResolutionPlus

variable [EnoughInjectives C]

/-- Let `F` be left exact and `i : M[0] ⟶ I` an injective resolution of `M[0]`. Then
`H⁰(F(i)) : H⁰(F(M[0])) ⟶ H⁰(F(I))` is an isomorphism. -/
theorem isIso_homologyMap_map_ι_single_zero (M : C)
    (R : InjectiveResolutionPlus ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι) 0) := by
  obtain ⟨R', hR'⟩ := exists_isStrictlyGE_of_isGE
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) 0
  obtain ⟨g, hg, -⟩ := existsUnique_homotopyCategory_hom_comp_eq R R'
  have : IsIso g := isIso_of_comp_eq R R' g hg
  let e := HomotopyCategory.homotopyEquivOfIso (asIso g)
  have h₁ : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom) 0) :=
    ((F.mapHomotopyEquiv e).toHomologyIso 0).isIso_hom
  have h₂ : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R'.ι) 0) :=
    isIso_homologyMap_mapHomologicalComplex_zero F R'.ι
  have h₃ : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R'.ι) 0 =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map R.ι) 0 ≫
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp]
    refine CochainComplex.InjectiveResolutionFunctor.homologyMap_mapHomologicalComplex_eq
      F _ _ ?_ 0
    rw [Functor.map_comp, ← hg]
    exact congrArg _ (HomotopyCategory.quotient_map_out g).symm
  rw [h₃] at h₂
  exact IsIso.of_isIso_comp_right _
    (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom) 0)

end InjectiveResolutionPlus

/-- Let `F : C ⥤ D` be a left exact additive functor, `C` having enough injectives, and `c` a
choice of injective resolutions `i_X : X ⟶ I(X)`. For every object `M` of `C`, the morphism
`H⁰(F(i_{M[0]})) : F(M) = H⁰(F(M[0])) ⟶ H⁰(F(I(M[0]))) = R⁰F(M[0])` is an isomorphism. -/
@[weil "lem_fka2_derived_functor_degree_zero"]
theorem isIso_homologyMap_map_choiceOfInjectiveResolutions_single_zero [EnoughInjectives C]
    (c : ChoiceOfInjectiveResolutions C) (M : C) :
    IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (c ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) ⟨0, inferInstance⟩).ι) 0) :=
  InjectiveResolutionPlus.isIso_homologyMap_map_ι_single_zero F M _

end CochainComplex
