module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationStalkReduction

/-!
# Compatible systems of endomorphisms of `RΓ_c(X, Gₙ)`

Let `X` be a separated scheme of finite type over a field `k`, with a compactification of its
structure morphism, and let `G = (Gₙ)ₙ` be an `ℓ`-adic sheaf on `X`, so that `Gₙ` is a sheaf of
`Λₙ = ℤ/ℓⁿ⁺¹ℤ`-modules. The transition maps `τₙ : RΓ_c(X, Gₙ₊₁) ⟶ RΓ_c(X, Gₙ)` live in
`D⁺(Λₙ₊₁)`, `RΓ_c(X, Gₙ)` being read there through `Λₙ₊₁ → Λₙ`. A compatible system of
endomorphisms of `(RΓ_c(X, Gₙ))ₙ` is a family of endomorphisms `ψₙ` of `RΓ_c(X, Gₙ)` in `D⁺(Λₙ)`
with `τₙ ∘ ψₙ₊₁ = ψₙ ∘ τₙ` in `D⁺(Λₙ₊₁)`.

To make sense of `ψₙ ∘ τₙ`, the endomorphism `ψₙ` of `D⁺(Λₙ)` is carried to `D⁺(Λₙ₊₁)` by
restriction of scalars, and compactly supported cohomology commutes with restriction of scalars:
`RΓ_c(X, res F) ≅ res RΓ_c(X, F)`. This holds because restriction of scalars is exact and commutes
with extension by zero, direct images and global sections, and carries injective sheaves to
sheaves acyclic for these functors.

## Main definitions

* `Stacks.EtaleCohomology.compactlySupportedCohomologyRestrictScalars`:
  `RΓ_c(X, -) ∘ res ≅ res ∘ RΓ_c(X, -)` on Mathlib's small étale site, built from
  `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroRestrictScalars` and
  `Stacks.EtaleCohomology.derivedLowerShriekRestrictScalars`.
* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologySingleRestrictScalars`: the same for
  a sheaf in degree `0` on the small étale site `AlgebraicGeometry.SmallEtale`, naturally in it.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.CompatibleEndomorphismSystem`: a compatible system of
  endomorphisms of `(RΓ_c(X, Gₙ))ₙ`.
* `AlgebraicGeometry.SmallEtale.LAdicSheaf.CompatibleEndomorphismSystem.ofHom`: the system
  `(RΓ_c(X, φₙ))ₙ` induced by an endomorphism `φ` of `G`; `id` and `comp` are the identity
  system and the levelwise composite.

## Implementation notes

The `ℓ`-adic sheaves are those of Stacks, Tag 03UM (`AlgebraicGeometry.SmallEtale.LAdicSheaf`).
The derived categories are the bounded below ones, a sheaf being placed in degree `0`, and the
compactification is an explicit argument, as for
`AlgebraicGeometry.SmallEtale.LAdicSheaf.compactlySupportedCohomologyTransition`. The source works
over a separably closed field; the definition uses no hypothesis on the field.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], II.4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- `Rj_! ∘ res_ρ ≅ res_ρ ∘ Rj_!` on bounded below derived categories. -/
def etaleModuleDerivedExtensionByZeroRestrictScalars {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ' j ⋙
        (etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus ≅
      (etaleModuleRestrictScalars ρ U).mapDerivedCategoryPlus ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ j :=
  Functor.rightDerivedRestrictionIso _ _ _ _ (etaleModuleExtensionByZeroRestrictScalars ρ j).symm
    (fun _ _ => Functor.rightAcyclic_of_exact _ _)

/-- `Rf_! ∘ res_ρ ≅ res_ρ ∘ Rf_!` on bounded below derived categories, for `Rf_! = R(f̄)_* ∘ j_!`
attached to a compactification. -/
def derivedLowerShriekRestrictScalars {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriek.{u, 0} f j Λ' ⋙ (etaleModuleRestrictScalars ρ Y).mapDerivedCategoryPlus ≅
      (etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus ⋙
        derivedLowerShriek.{u, 0} f j Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedDirectImageRestrictScalars ρ j.toBase) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroRestrictScalars ρ j.immersion) _ ≪≫
    Functor.associator _ _ _

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]

/-- **Compactly supported cohomology commutes with restriction of scalars**:
`RΓ_c(X, res_ρ K) ≅ res_ρ RΓ_c(X, K)` on bounded below derived categories. -/
def compactlySupportedCohomologyRestrictScalars (j : CompactificationOf (Over.mk f)) :
    compactlySupportedCohomology.{u, 0} k f j Λ' ⋙
        (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus ≅
      (etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus ⋙
        compactlySupportedCohomology.{u, 0} k f j Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleDerivedGlobalSectionsRestrictScalars ρ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedLowerShriekRestrictScalars ρ f j) _ ≪≫
    Functor.associator _ _ _

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- Restriction of scalars commutes with the equivalence `moduleSheafEquiv` between sheaves of
modules on `SmallEtale` and on Mathlib's small étale site. -/
def moduleSheafEquivRestrictScalars :
    (moduleSheafEquiv B X hX Λ').functor ⋙ etaleModuleRestrictScalars ρ X ≅
      sheafCompose (topology B X hX) (ModuleCat.restrictScalars.{u + 1} ρ) ⋙
        (moduleSheafEquiv B X hX Λ).functor :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (moduleSheafEquiv B X hX Λ).counitIso.symm ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquiv B X hX Λ').functor
      (Functor.isoWhiskerRight
        (Iso.refl (etaleModuleRestrictScalars ρ X ⋙ (moduleSheafEquiv B X hX Λ).inverse :
          Stacks.EtaleCohomology.EtaleModules.{u, 0} Λ' X ⥤ _) ≪≫
          (Iso.refl ((moduleSheafEquiv B X hX Λ').inverse ⋙
            sheafCompose (topology B X hX) (ModuleCat.restrictScalars.{u + 1} ρ))))
        (moduleSheafEquiv B X hX Λ).functor) ≪≫
    Functor.isoWhiskerRight (moduleSheafEquiv B X hX Λ').unitIso.symm
      (sheafCompose (topology B X hX) (ModuleCat.restrictScalars.{u + 1} ρ) ⋙
        (moduleSheafEquiv B X hX Λ).functor) ≪≫
    Functor.leftUnitor _

variable (k : Type u) [Field k] {X} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))

set_option maxHeartbeats 1600000 in
-- The kernel check of the composite of whiskered isomorphisms unfolds the derived functors.
/-- **`RΓ_c` of a sheaf commutes with restriction of scalars**: for a sheaf `F` of `Λ'`-modules
on the small étale site of `X`, placed in degree `0`, `RΓ_c(X, res_ρ F) ≅ res_ρ RΓ_c(X, F)` in
`D⁺(Λ)`, naturally in `F`. -/
def compactlySupportedCohomologySingleRestrictScalars :
    sheafCompose (topology B X hX) (ModuleCat.restrictScalars.{u + 1} ρ) ⋙
        DerivedCategory.Plus.singleFunctor _ 0 ⋙ compactlySupportedCohomology.{u, 0} B hX Λ k f j ≅
      DerivedCategory.Plus.singleFunctor _ 0 ⋙ compactlySupportedCohomology.{u, 0} B hX Λ' k f j ⋙
        (ModuleCat.restrictScalars.{u + 1} ρ).mapDerivedCategoryPlus :=
  Functor.isoWhiskerLeft (sheafCompose (topology B X hX) (ModuleCat.restrictScalars.{u + 1} ρ))
      (Functor.isoWhiskerRight
        ((moduleSheafEquiv B X hX Λ).functor.mapDerivedCategoryPlusSingleFunctorIso 0)
        (Stacks.EtaleCohomology.compactlySupportedCohomology.{u, 0} k f j Λ)) ≪≫
    Functor.isoWhiskerRight (moduleSheafEquivRestrictScalars B X hX ρ).symm
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        Stacks.EtaleCohomology.compactlySupportedCohomology.{u, 0} k f j Λ) ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquiv B X hX Λ').functor
      (Functor.isoWhiskerRight
        ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlusSingleFunctorIso 0).symm
        (Stacks.EtaleCohomology.compactlySupportedCohomology.{u, 0} k f j Λ)) ≪≫
    Functor.isoWhiskerRight
      ((moduleSheafEquiv B X hX Λ').functor.mapDerivedCategoryPlusSingleFunctorIso 0).symm
      ((etaleModuleRestrictScalars ρ X).mapDerivedCategoryPlus ⋙
        Stacks.EtaleCohomology.compactlySupportedCohomology.{u, 0} k f j Λ) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor _ 0 ⋙
        (moduleSheafEquiv B X hX Λ').functor.mapDerivedCategoryPlus)
      (Stacks.EtaleCohomology.compactlySupportedCohomologyRestrictScalars ρ k f j).symm

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.obj] [Fact ℓ.Prime]
  (k : Type u) [Field k] (f : X.obj ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))

/-- The target of the transition map `τₙ`, compactly supported cohomology over `ℤ/ℓⁿ⁺²ℤ` of `Gₙ`
with its coefficients restricted, is the restriction of scalars of `RΓ_c(X, Gₙ) ∈ D⁺(ℤ/ℓⁿ⁺¹ℤ)`:
this is the isomorphism in `D⁺(ℤ/ℓⁿ⁺²ℤ)` through which `ψₙ` acts on the target of `τₙ`. -/
def LAdicSheaf.compactlySupportedCohomologyLevelRestrictScalars
    (G : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 2))) k f j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((G.level n).restrictScalars B X ℓ n)) ≅
      (ModuleCat.restrictScalars.{u + 1} (finiteLevelRingHom ℓ n)).mapDerivedCategoryPlus.obj
        ((compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 1))) k f j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj (G.level n))) :=
  (compactlySupportedCohomologySingleRestrictScalars B X.property
    (finiteLevelRingHom ℓ n) k f j).app (G.level n)

/-- **A compatible system of endomorphisms** of `(RΓ_c(X, Gₙ))ₙ` for an `ℓ`-adic sheaf `G`: a
family `ψ = (ψₙ)ₙ` of endomorphisms `ψₙ` of `RΓ_c(X, Gₙ)` in `D⁺(ℤ/ℓⁿ⁺¹ℤ)` such that
`τₙ ∘ ψₙ₊₁ = ψₙ ∘ τₙ` in `D⁺(ℤ/ℓⁿ⁺²ℤ)` for every `n`, where `τₙ` is the transition map
`LAdicSheaf.compactlySupportedCohomologyTransition` and `ψₙ` acts on its target through
`LAdicSheaf.compactlySupportedCohomologyLevelRestrictScalars`. -/
@[weil "def_fk204_compatible_endomorphism_system", ext]
structure LAdicSheaf.CompatibleEndomorphismSystem (G : LAdicSheaf.{u, u + 1} B X ℓ) where
  /-- The endomorphism `ψₙ` of `RΓ_c(X, Gₙ)` in `D⁺(ℤ/ℓⁿ⁺¹ℤ)`. -/
  app : ∀ n : ℕ,
    (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 1))) k f j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (G.level n)) ⟶
      (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 1))) k f j).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (G.level n))
  /-- `τₙ ∘ ψₙ₊₁ = ψₙ ∘ τₙ` in `D⁺(ℤ/ℓⁿ⁺²ℤ)`. -/
  comm : ∀ n : ℕ,
    app (n + 1) ≫ LAdicSheaf.compactlySupportedCohomologyTransition B X ℓ k f j G n =
      LAdicSheaf.compactlySupportedCohomologyTransition B X ℓ k f j G n ≫
        (LAdicSheaf.compactlySupportedCohomologyLevelRestrictScalars B X ℓ k f j G n).hom ≫
        (ModuleCat.restrictScalars.{u + 1} (finiteLevelRingHom ℓ n)).mapDerivedCategoryPlus.map
          (app n) ≫
        (LAdicSheaf.compactlySupportedCohomologyLevelRestrictScalars B X ℓ k f j G n).inv

namespace LAdicSheaf.CompatibleEndomorphismSystem

variable {B X ℓ k f j} {G : LAdicSheaf.{u, u + 1} B X ℓ}

/-- The compatible system of identities. -/
@[simps]
def id (G : LAdicSheaf.{u, u + 1} B X ℓ) : CompatibleEndomorphismSystem B X ℓ k f j G where
  app _ := 𝟙 _
  comm n := by
    rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id,
      Category.comp_id]

/-- The levelwise composite `(ψₙ ≫ ψ'ₙ)ₙ` of two compatible systems of endomorphisms. -/
@[simps]
def comp (ψ ψ' : CompatibleEndomorphismSystem B X ℓ k f j G) :
    CompatibleEndomorphismSystem B X ℓ k f j G where
  app n := ψ.app n ≫ ψ'.app n
  comm n := by
    rw [Category.assoc, ψ'.comm, reassoc_of% (ψ.comm n), CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The compatible system induced by an endomorphism** `φ : G ⟶ G` of an `ℓ`-adic sheaf:
`ψₙ = RΓ_c(X, φₙ)`. -/
@[simps]
def ofHom (φ : LAdicSheaf.Hom B X ℓ G G) : CompatibleEndomorphismSystem B X ℓ k f j G where
  app n := (compactlySupportedCohomology.{u, 0} B X.property (ZMod (ℓ ^ (n + 1))) k f j).map
    ((DerivedCategory.Plus.singleFunctor _ 0).map (φ.app n))
  comm n := by
    rw [← LAdicSheaf.compactlySupportedCohomologyTransition_naturality]
    congr 1
    have := (compactlySupportedCohomologySingleRestrictScalars B X.property
      (finiteLevelRingHom ℓ n) k f j).hom.naturality (φ.app n)
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact this

end LAdicSheaf.CompatibleEndomorphismSystem

end AlgebraicGeometry.SmallEtale
