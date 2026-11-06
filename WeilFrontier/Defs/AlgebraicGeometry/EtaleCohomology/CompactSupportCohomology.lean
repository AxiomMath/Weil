module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactSupportCohomologyDerived
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleHomExt

/-!
# Cohomology groups with compact support

Let `k` be a field, `f : X ⟶ Spec k` a separated morphism of finite type with a compactification
`j`, and `Λ` a ring. For a bounded below complex `K` of sheaves of `Λ`-modules on the small étale
site of `X`, the cohomology groups with compact support are `H^v_c(X, K) = H^v(RΓ_c(X, K))`,
`v ∈ ℤ`, the cohomology of `RΓ_c(X, K) = RΓ(Spec k, Rf_! K)`.

When `k` is separably closed, every étale covering of `Spec k` has a section, so the global
sections functor on the small étale site of `Spec k` is exact. An exact functor commutes with
taking cohomology of its derived functor, hence `H^v_c(X, K) ≅ Γ(Spec k, R^v f_! K)`, which is
the form in which the source defines the groups.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyGroup`: `K ↦ H^v_c(X, K)` on the
  bounded below derived category of sheaves of `Λ`-modules on the small étale site of `X`.

## Main results

* `AlgebraicGeometry.compactlySupportedCohomologyGroupIsoGlobalSections`: over a separably closed
  field, `Stacks.EtaleCohomology.compactlySupportedCohomologyGroup` is `Γ(Spec k, R^v f_!(-))`.
* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyGroupIsoGlobalSections`: the same for
  `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyGroup`.
* `AlgebraicGeometry.preservesHomology_etaleModuleGlobalSections_of_isSepClosed`: global sections
  over the spectrum of a separably closed field are exact.
* `CategoryTheory.Functor.rightDerivedFunctorPlusCompHomologyFunctorIso`: for an exact functor
  `F`, `Hⁿ(RF(K)) ≅ F(Hⁿ(K))` naturally in `K`.

## Implementation notes

The groups are defined as `H^v(RΓ_c(X, K))`, which is the definition of
`Stacks.EtaleCohomology.compactlySupportedCohomologyGroup` and makes sense over any field; the
source's `Γ(S, R^v f_!(K))` over the separably closed base `S = Spec k` is identified with it by
`compactlySupportedCohomologyGroupIsoGlobalSections`. The compactification is an explicit
argument, as in `AlgebraicGeometry.SmallEtale.compactlySupportedCohomology`. The higher direct
images `R^v f_!` are those of `AlgebraicGeometry.higherDirectImageProperSupport`, on Mathlib's
small étale site; complexes on `SmallEtale` reach it through
`AlgebraicGeometry.SmallEtale.moduleDerivedPlusEquiv`. The source works with complexes with
torsion cohomology sheaves; the formula needs no torsion hypothesis, so the groups are defined on
the whole bounded below derived category.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.8.
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r u₁ v₁ w₁ u₂ v₂ w₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- The homology of the total right derived functor of an exact functor is the functor applied
to the homology: `Hⁿ(RF(K)) ≅ F(Hⁿ(K))`, naturally in `K`. -/
def rightDerivedFunctorPlusCompHomologyFunctorIso (n : ℤ) :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B n ≅
      DerivedCategory.Plus.homologyFunctor A n ⋙ F :=
  haveI := preservesFiniteLimits_of_preservesHomology F
  haveI := preservesFiniteColimits_of_preservesHomology F
  isoWhiskerRight (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus) _ ≪≫
    (Iso.refl _ : F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙
        DerivedCategory.homologyFunctor B n ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor B n) ≪≫
    isoWhiskerLeft DerivedCategory.Plus.ι (F.mapDerivedCategoryHomologyIso n)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The terminal object `S` of the small étale site of `S`. -/
abbrev Etale.self : S.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 S) (inferInstance : AlgebraicGeometry.Etale (𝟙 S))

/-- `S` is terminal in the small étale site of `S`. -/
def Etale.isTerminalSelf : IsTerminal (Etale.self S) :=
  IsTerminal.ofUniqueHom (fun Y ↦ MorphismProperty.Over.homMk Y.hom (Category.comp_id _) trivial)
    (fun Y m ↦ by
      ext
      exact (Category.comp_id _).symm.trans (Over.w m.toCommaMorphism))

variable (k : Type u) [Field k] [IsSepClosed k]

/-- Over a separably closed field `k`, every covering sieve of the terminal object of the small
étale site of `Spec k` contains the identity. -/
theorem Etale.mem_self_of_mem_smallEtaleTopology {R : Sieve (Etale.self (Spec (.of k)))}
    (hR : R ∈ (Spec (.of k)).smallEtaleTopology (Etale.self _)) : R (𝟙 _) := by
  obtain ⟨Y, g, hg, t, -⟩ := (pointSmallEtale (𝟙 (Spec (.of k)))).jointly_surjective R hR
    (𝟙 (Over.mk (𝟙 (Spec (.of k)))))
  let t' : Etale.self (Spec (.of k)) ⟶ Y := (Etale.forget _).preimage t
  have := R.downward_closed hg t'
  rwa [(Etale.isTerminalSelf _).hom_ext (t' ≫ g) (𝟙 _)] at this

end AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] etaleModules_enoughInjectives

variable (Λ : Type r) [Ring Λ] (k : Type u) [Field k] [IsSepClosed k]

/-- Over a separably closed field `k`, taking sections over `Spec k` of sheaves of `Λ`-modules
on the small étale site of `Spec k` preserves epimorphisms. -/
theorem epi_sheafSections_map_of_isSepClosed {F G : EtaleModules.{u, r} Λ (Spec (.of k))}
    (φ : F ⟶ G) [Epi φ] :
    Epi (((sheafSections _ _).obj (op (Etale.self (Spec (.of k))))).map φ) := by
  have : Presheaf.IsLocallySurjective (Spec (.of k)).smallEtaleTopology φ.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).2 inferInstance
  rw [ModuleCat.epi_iff_surjective]
  intro s
  obtain ⟨t, ht⟩ := Etale.mem_self_of_mem_smallEtaleTopology k
    (Presheaf.imageSieve_mem (Spec (.of k)).smallEtaleTopology φ.hom s)
  exact ⟨t, by simpa using ht⟩

/-- Over a separably closed field `k`, the global sections functor on sheaves of `Λ`-modules on
the small étale site of `Spec k` preserves epimorphisms. -/
instance preservesEpimorphisms_etaleModuleGlobalSections_of_isSepClosed :
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).PreservesEpimorphisms :=
  haveI : ((sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
      (op (Etale.self (Spec (.of k))))).PreservesEpimorphisms :=
    ⟨fun φ _ ↦ epi_sheafSections_map_of_isSepClosed Λ k φ⟩
  Functor.PreservesEpimorphisms.of_iso
    (Sheaf.ΓNatIsoSheafSections _ _ (Etale.isTerminalSelf (Spec (.of k)))).symm

/-- Over a separably closed field `k`, the global sections functor on sheaves of `Λ`-modules on
the small étale site of `Spec k` is exact. -/
instance preservesHomology_etaleModuleGlobalSections_of_isSepClosed :
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f]

/-- **Cohomology with compact support as sections of the higher direct images.** Over a separably
closed field `k`, `H^v_c(X, K) = H^v(RΓ(Spec k, Rf_! K))` is `Γ(Spec k, R^v f_! K)`, naturally in
the bounded below complex `K` of sheaves of `Λ`-modules on the small étale site of `X`. -/
@[weil "def_fk108_compact_support_cohomology"]
def compactlySupportedCohomologyGroupIsoGlobalSections (j : CompactificationOf (Over.mk f))
    (v : ℤ) :
    compactlySupportedCohomologyGroup.{u, r} k f j Λ v ≅
      higherDirectImageProperSupport.{u, r} f j Λ v ⋙
        etaleModuleGlobalSections.{u, r} Λ (Spec (.of k)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedLowerShriek.{u, r} f j Λ)
      (Functor.rightDerivedFunctorPlusCompHomologyFunctorIso
        (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))) v) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] etaleModules_enoughInjectives

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (Λ : Type r) [Ring Λ]
  (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f]

/-- The **cohomology groups with compact support** `H^v_c(X, K) = H^v(RΓ_c(X, K))` of a bounded
below complex `K` of sheaves of `Λ`-modules on the small étale site of a separated finite type
`k`-scheme `X`, computed through the compactification `j` of `f : X ⟶ Spec k`. Over a separably
closed field this is `Γ(Spec k, R^v f_! K)`, by
`compactlySupportedCohomologyGroupIsoGlobalSections`. -/
@[weil "def_fk108_compact_support_cohomology"]
abbrev compactlySupportedCohomologyGroup (j : CompactificationOf (Over.mk f)) (v : ℤ) :
    DerivedCategory.Plus (Sheaf (topology B X hX) (ModuleCat.{max (u + 1) r} Λ)) ⥤
      ModuleCat.{max (u + 1) r} Λ :=
  compactlySupportedCohomology B hX Λ k f j ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) v

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- `H^v_c(X, -)` on `SmallEtale` is `Stacks.EtaleCohomology.compactlySupportedCohomologyGroup` on
Mathlib's small étale site, after the equivalence `moduleDerivedPlusEquiv`. -/
theorem compactlySupportedCohomologyGroup_eq (j : CompactificationOf (Over.mk f)) (v : ℤ) :
    compactlySupportedCohomologyGroup B hX Λ k f j v =
      (moduleDerivedPlusEquiv B X hX Λ).functor ⋙
        Stacks.EtaleCohomology.compactlySupportedCohomologyGroup.{u, r} k f j Λ v :=
  rfl

/-- **Cohomology with compact support as sections of the higher direct images.** Over a separably
closed field `k`, `H^v_c(X, K) = Γ(Spec k, R^v f_! K)`, naturally in the bounded below complex `K`
of sheaves of `Λ`-modules on the small étale site `SmallEtale` of `X`; the higher direct image
`R^v f_!` is taken on Mathlib's small étale site, through `moduleDerivedPlusEquiv`. -/
@[weil "def_fk108_compact_support_cohomology"]
def compactlySupportedCohomologyGroupIsoGlobalSections [IsSepClosed k]
    (j : CompactificationOf (Over.mk f)) (v : ℤ) :
    compactlySupportedCohomologyGroup B hX Λ k f j v ≅
      (moduleDerivedPlusEquiv B X hX Λ).functor ⋙ higherDirectImageProperSupport.{u, r} f j Λ v ⋙
        etaleModuleGlobalSections.{u, r} Λ (Spec (.of k)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleDerivedPlusEquiv B X hX Λ).functor
      (AlgebraicGeometry.compactlySupportedCohomologyGroupIsoGlobalSections Λ k f j v)

end AlgebraicGeometry.SmallEtale

end
