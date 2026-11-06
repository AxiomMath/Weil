module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPlusAdjunctionUnitIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import WeilFrontier.Algebra.Homology.DerivedCategory.Plus
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageAbelian
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Attr

/-!
# Acyclic morphisms and the derived adjunction

Let `g : T ⟶ S` be an acyclic morphism of schemes: for every abelian sheaf `F` on the small
étale site of `S` which is torsion prime to the residue characteristics of `S`, the unit
`F ⟶ g_* g^* F` is an isomorphism and `R^i g_* (g^* F) = 0` for `i > 0`. Then for every
complex `K` of `D⁺(S)` whose cohomology sheaves are torsion prime to the residue
characteristics of `S`, the adjunction morphism `K ⟶ R g_* (g^* K)` is an isomorphism in
`D⁺(S)`.

The inverse image `g^*` is exact, so it acts on bounded below derived categories, and the
adjunction `g^* ⊣ g_*` descends to an adjunction `g^* ⊣ R g_*` between `D⁺(S)` and `D⁺(T)`;
the morphism in question is its unit. For a sheaf `F` as above placed in a single degree, the
unit is computed degreewise: it is the unit `F ⟶ g_* g^* F` followed by the comparison
`g_* (g^* F) ⟶ R g_* (g^* F)`, both invertible by acyclicity. The general case follows from the
way-out lemma `DerivedCategory.Plus.isIso_app_of_prop_homology`, applied to the identity functor
and to `R g_* ∘ g^*`, both triangulated and not lowering the degree in which cohomology starts.

## Main results

* `AlgebraicGeometry.BigEtaleSite.IsAcyclic.isIso_derivedPlusAdjunction_unit_app`: for an acyclic
  `g` and `K ∈ D⁺(S)` with cohomology sheaves torsion prime to the residue characteristics of
  `S`, the unit `K ⟶ R g_* (g^* K)` of the derived adjunction is an isomorphism.

## Implementation notes

The sheaves are abelian sheaves `AddCommGrpCat.{u + 1}` on the size-bounded small étale sites
`AlgebraicGeometry.SmallEtale` of a big étale site, as in the definition of
`AlgebraicGeometry.BigEtaleSite.IsAcyclic`. The derived adjunction is
`Stacks.ComparingTopologies.derivedPlusAdjunction` for the adjunction
`AlgebraicGeometry.smallEtaleInverseImageAdjunction`, and `R g_*` is Mathlib's total right derived
functor `CategoryTheory.Functor.rightDerivedFunctorPlus`. The source assumes `S` and `T`
noetherian; the argument does not use it, and the statement omits it.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory Pretriangulated

universe u

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.isTriangulated_rightDerivedFunctorPlus

namespace AlgebraicGeometry.BigEtaleSite

section General

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The derived unit at the image of a bounded below complex at each of whose terms the unit is
invertible and whose image under `L` is acyclic for `R`. -/
private theorem isIso_derivedPlusAdjunction_unit_app_Qh_obj (adj : L ⊣ R)
    (M : HomotopyCategory.Plus A) (hu : ∀ n : ℤ, IsIso (adj.unit.app (M.obj.as.X n)))
    (hac : ∀ n : ℤ, R.rightAcyclic (L.obj (M.obj.as.X n))) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction adj).unit.app
      (DerivedCategory.Plus.Qh.obj M)) := by
  have : L.mapDerivedCategoryPlus.IsLeftDerivedFunctor
      L.mapDerivedCategoryPlusFactorsh.hom (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      L.mapDerivedCategoryPlusFactorsh
  have : (L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        L.mapDerivedCategoryPlusFactorsh R.rightDerivedFunctorPlus)
  have hη := adj.mapHomotopyCategoryPlus.derivedη_fac_app (HomotopyCategory.Plus.quasiIso A)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnit M
  have h₁ : IsIso (adj.mapHomotopyCategoryPlus.unit.app M) :=
    Stacks.ComparingTopologies.isIso_mapHomotopyCategoryPlus_unit_app adj M hu
  have h₂ : IsIso (R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj M)) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic R _ hac
  have : IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction adj).unit.app
      (DerivedCategory.Plus.Qh.obj M) ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app M)) := by
    change IsIso ((adj.mapHomotopyCategoryPlus.derivedη (HomotopyCategory.Plus.quasiIso A)
      L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnit).app
        (DerivedCategory.Plus.Qh.obj M) ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app M))
    rw [hη]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app M))

/-- The objects at which the unit is invertible and whose image under `L` is acyclic for `R`. -/
private def unitIsoAcyclic (adj : L ⊣ R) : ObjectProperty A :=
  fun X ↦ IsIso (adj.unit.app X) ∧ R.rightAcyclic (L.obj X)

omit [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
private theorem unitIsoAcyclic_of_iso (adj : L ⊣ R) {X Y : A} (e : X ≅ Y)
    (h : unitIsoAcyclic adj X) : unitIsoAcyclic adj Y :=
  ⟨(NatTrans.isIso_app_iff_of_iso adj.unit e).1 h.1,
    (R.rightAcyclic).prop_of_iso (L.mapIso e) h.2⟩

omit [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
private theorem unitIsoAcyclic_of_isZero [PreservesFiniteLimits R] (adj : L ⊣ R) {X : A}
    (hX : IsZero X) : unitIsoAcyclic adj X := by
  have hLX : IsZero (L.obj X) := L.map_isZero hX
  refine ⟨IsZero.isIso hX (R.map_isZero hLX) _, ?_⟩
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n _
  exact (R.rightDerived n).map_isZero hLX

/-- The derived unit at a sheaf placed in a single degree. -/
private theorem isIso_derivedPlusAdjunction_unit_app_singleFunctor [PreservesFiniteLimits R]
    (adj : L ⊣ R) {X : A} (hX : unitIsoAcyclic adj X) (n : ℤ) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction adj).unit.app
      ((DerivedCategory.Plus.singleFunctor A n).obj X)) := by
  let M := (HomotopyCategory.Plus.singleFunctor A n).obj X
  let e : (DerivedCategory.Plus.singleFunctor A n).obj X ≅ DerivedCategory.Plus.Qh.obj M :=
    DerivedCategory.Plus.ι.preimageIso
      ((DerivedCategory.singleFunctorIsoCompQh A n).app X ≪≫
        DerivedCategory.Qh.mapIso
          ((HomotopyCategory.Plus.singleFunctorCompιIso A n).app X).symm)
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  have hM : ∀ k : ℤ, unitIsoAcyclic adj (M.obj.as.X k) := by
    intro k
    change unitIsoAcyclic adj
      (((HomologicalComplex.single A (ComplexShape.up ℤ) n).obj X).X k)
    by_cases hk : k = n
    · subst hk
      exact unitIsoAcyclic_of_iso adj (HomologicalComplex.singleObjXSelf _ _ X).symm hX
    · exact unitIsoAcyclic_of_isZero adj (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk)
  exact isIso_derivedPlusAdjunction_unit_app_Qh_obj adj M (fun k ↦ (hM k).1) (fun k ↦ (hM k).2)

/-- A triangulated functor between bounded below derived categories carries admissible triangles
to admissible triangles. -/
private theorem map_mem_admissibleTriangles {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (Φ : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D) [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (T : Triangle (DerivedCategory.Plus C))
    (hT : DerivedCategory.Plus.ι.mapTriangle.obj T ∈ DerivedCategory.admissibleTriangles C) :
    DerivedCategory.Plus.ι.mapTriangle.obj (Φ.mapTriangle.obj T) ∈
      DerivedCategory.admissibleTriangles D := by
  rw [DerivedCategory.Plus.mem_admissibleTriangles_ι_mapTriangle_iff] at hT ⊢
  refine isomorphic_distinguished _ (Φ.map_distinguished _ hT) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [Functor.mapTriangle])
      (by simp [Functor.mapTriangle])
      (by simp [Functor.mapTriangle]; rfl))

/-- **The derived unit on complexes with cohomology in a class.** Let `L ⊣ R` with `L` exact, and
let `𝒞` be a class of objects at which the unit is invertible and whose images under `L` are
acyclic for `R`. Then the unit `K ⟶ R(L K)` of the derived adjunction on bounded below derived
categories is invertible at every `K` all of whose cohomology objects lie in `𝒞`. -/
private theorem isIso_derivedPlusAdjunction_unit_app_of_prop_homology [PreservesFiniteLimits R]
    (adj : L ⊣ R)
    (𝒞 : ObjectProperty A) (hu : ∀ X : A, 𝒞 X → IsIso (adj.unit.app X))
    (hac : ∀ X : A, 𝒞 X → R.rightAcyclic (L.obj X)) (K : DerivedCategory.Plus A)
    (hK : ∀ ν : ℤ, 𝒞 ((DerivedCategory.Plus.homologyFunctor A ν).obj K)) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction adj).unit.app K) := by
  refine DerivedCategory.Plus.isIso_app_of_prop_homology
    (Φ := 𝟭 _) (Ψ := L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus)
    (fun T hT ↦ map_mem_admissibleTriangles (𝟭 _) T hT)
    (fun T hT ↦ map_mem_admissibleTriangles _ T hT)
    (fun _ _ h ↦ h) ?_ _ 𝒞 ?_ K hK
  · intro m K hK
    have : K.IsGE m := (DerivedCategory.Plus.isGE_iff K m).2 hK
    have : (L.mapDerivedCategoryPlus.obj K).IsGE m :=
      L.isGE_mapDerivedCategoryPlus_obj K m this
    exact (DerivedCategory.Plus.isGE_iff _ m).1
      (R.isGE_rightDerivedFunctorPlus_obj (L.mapDerivedCategoryPlus.obj K) m)
  · intro F hF j
    let e : ((DerivedCategory.Plus.singleFunctor A 0).obj F)⟦j⟧ ≅
        (DerivedCategory.Plus.singleFunctor A (-j)).obj F :=
      ((DerivedCategory.Plus.singleFunctors A).shiftIso j (-j) 0 (by omega)).app F
    refine (NatTrans.isIso_app_iff_of_iso _ e).2 ?_
    exact isIso_derivedPlusAdjunction_unit_app_singleFunctor adj ⟨hu F hF, hac F hF⟩ (-j)

end General

variable {B : BigEtaleSite.{u}} {S T : B.Scheme}
  [HasDerivedCategory (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory (Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1})]

/-- **Acyclic morphisms and the derived adjunction.** Let `g : T ⟶ S` be an acyclic morphism.
For every `K ∈ D⁺(S)` whose cohomology sheaves are torsion prime to the residue characteristics
of `S`, the unit `K ⟶ R g_* (g^* K)` of the adjunction `g^* ⊣ R g_*` on bounded below derived
categories is an isomorphism. -/
@[weil "lem_fk107_acyclicity_derived"]
theorem IsAcyclic.isIso_derivedPlusAdjunction_unit_app {g : T ⟶ S} (hg : IsAcyclic B g)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}))
    (hK : ∀ ν : ℤ, SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj
      ((DerivedCategory.Plus.homologyFunctor _ ν).obj K)) :
    IsIso ((Stacks.ComparingTopologies.derivedPlusAdjunction
      (smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1})).unit.app K) := by
  refine isIso_derivedPlusAdjunction_unit_app_of_prop_homology _
    (fun F ↦ SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F)
    (fun F hF ↦ hg.isIso_unit_app hF) (fun F hF ↦ ?_) K hK
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  exact hg.isZero_higherDirectImage hF hn

end AlgebraicGeometry.BigEtaleSite
