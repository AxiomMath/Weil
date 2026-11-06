module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactSupportCohomologyDerived
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PowerOfPair
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Weil.Attr

/-!
# The endomorphism of cohomology with compact support induced by a pair

Let `k` be a field, `V` a `k`-scheme with a compactification `j` of `f : V ⟶ Spec k`, and `Λ` a
ring. Let `(h, φ)` be a pair on `V`: an endomorphism `h : V ⟶ V` and a morphism
`φ : h^* G ⟶ G` of bounded below complexes of sheaves of `Λ`-modules on the small étale site of
`V`. Let `η : G ⟶ h_* h^* G` be the unit of `h^* ⊣ h_*`, termwise. For `h` finite over `k`,
`Rh_! = h_*` and `Rf_! ∘ Rh_! ≅ R(f ∘ h)_! = Rf_!` give isomorphisms
`ε_F : RΓ_c(V, h_* F) ≅ RΓ_c(V, F)`, natural in the complex `F`. Then
`h^♮ = ε_{h^* G} ∘ RΓ_c(V, η) : RΓ_c(V, G) ⟶ RΓ_c(V, h^* G)` and
`RΓ_c(h, φ) = RΓ_c(V, φ) ∘ h^♮ : RΓ_c(V, G) ⟶ RΓ_c(V, G)`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleComplexPlusUnit`: the unit `K ⟶ h_* h^* K`, termwise on
  bounded below complexes.
* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyComplex`: `RΓ_c(V, -)` on bounded
  below complexes of sheaves.
* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyPullback`: the natural
  transformation `h^♮ : RΓ_c(V, -) ⟶ RΓ_c(V, h^* -)`.
* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyEndomorphism`: the endomorphism
  `RΓ_c(h, φ)` of `RΓ_c(V, G)`.

## Main results

* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyPullback_app`: `h^♮` at `G` is
  `ε_{h^* G} ∘ RΓ_c(V, η_G)`.
* `AlgebraicGeometry.SmallEtale.compactlySupportedCohomologyEndomorphism_eq`: the formula
  `RΓ_c(h, φ) = RΓ_c(V, φ) ∘ ε_{h^* G} ∘ RΓ_c(V, η_G)`.

## Implementation notes

The source takes the isomorphisms `ε_F` as part of the data, and so does this file: `ε` is an
argument, a natural isomorphism `h_* ⋙ RΓ_c(V, -) ≅ RΓ_c(V, -)` of functors on bounded below
complexes. Finiteness of `h`, the condition that `h` is a morphism over `k`, and torsion of the
cohomology sheaves of `G` are what make the canonical `ε` exist; the formula itself uses none
of them, so they are not hypotheses of the definitions. The direct image of complexes is taken
termwise, which is its derived functor when `h` is finite, `h_*` being exact.

A related construction is `Stacks.EtaleCohomology.compactSupportPullback`, the endomorphism of
`RΓ_c` induced by an endomorphism of a compactification extending `h`; it uses that extension
in place of the isomorphisms `ε`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], II.3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

universe u r

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {V : B.Scheme} (Λ : Type r) [Ring Λ]

/-- The direct image of sheaves of `Λ`-modules is additive. -/
instance additive_smallEtaleModuleDirectImage (h : V ⟶ V) :
    ((smallEtaleBaseChange B h).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (topology B V.obj V.property) (topology B V.obj V.property)).Additive :=
  have := (smallEtaleInverseImageAdjunction B h (ModuleCat.{max (u + 1) r} Λ)).isRightAdjoint
  Functor.additive_of_preserves_binary_products _

/-- The inverse image of sheaves of `Λ`-modules is additive, being left adjoint to the additive
direct image. -/
instance additive_smallEtaleModuleInverseImage (h : V ⟶ V) :
    (smallEtaleInverseImage B h (ModuleCat.{max (u + 1) r} Λ)).Additive :=
  (smallEtaleInverseImageAdjunction B h (ModuleCat.{max (u + 1) r} Λ)).left_adjoint_additive


/-- The unit `K ⟶ h_* h^* K` of the adjunction `h^* ⊣ h_*`, taken termwise on bounded below
complexes of sheaves of `Λ`-modules on the small étale site of `V`. -/
def moduleComplexPlusUnit (h : V ⟶ V) :
    𝟭 (CochainComplex.Plus (Sheaf (topology B V.obj V.property)
        (ModuleCat.{max (u + 1) r} Λ))) ⟶
      (smallEtaleInverseImage B h (ModuleCat.{max (u + 1) r} Λ)).mapCochainComplexPlus ⋙
        ((smallEtaleBaseChange B h).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
          (topology B V.obj V.property) (topology B V.obj V.property)).mapCochainComplexPlus where
  app K := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex
      (smallEtaleInverseImageAdjunction B h (ModuleCat.{max (u + 1) r} Λ)).unit _).app K.obj)
  naturality K L g := by
    ext n : 2
    exact (smallEtaleInverseImageAdjunction B h (ModuleCat.{max (u + 1) r} Λ)).unit.naturality
      (g.hom.f n)

variable (k : Type u) [Field k] (f : V.obj ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))

/-- `RΓ_c(V, -)` on bounded below complexes of sheaves of `Λ`-modules on the small étale site
of `V`: the complex is sent to the bounded below derived category, then to
`compactlySupportedCohomology`. -/
abbrev compactlySupportedCohomologyComplex :
    CochainComplex.Plus (Sheaf (topology B V.obj V.property) (ModuleCat.{max (u + 1) r} Λ)) ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  DerivedCategory.Plus.Q ⋙ compactlySupportedCohomology B V.property Λ k f j

variable {B Λ k f j}

/-- **The map `h^♮ : RΓ_c(V, G) ⟶ RΓ_c(V, h^* G)`** of an endomorphism `h` of `V`, given the
isomorphisms `ε_F : RΓ_c(V, h_* F) ≅ RΓ_c(V, F)`, natural in `F`: it is
`ε_{h^* G} ∘ RΓ_c(V, η_G)`, where `η_G : G ⟶ h_* h^* G` is the unit. It is natural in `G`. -/
@[weil "def_fk203_cohomology_endomorphism_of_pair"]
def compactlySupportedCohomologyPullback {h : V ⟶ V}
    (ε : ((smallEtaleBaseChange B h).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
        (topology B V.obj V.property) (topology B V.obj V.property)).mapCochainComplexPlus ⋙
          compactlySupportedCohomologyComplex B Λ k f j ≅
        compactlySupportedCohomologyComplex B Λ k f j) :
    compactlySupportedCohomologyComplex B Λ k f j ⟶
      (smallEtaleInverseImage B h (ModuleCat.{max (u + 1) r} Λ)).mapCochainComplexPlus ⋙
        compactlySupportedCohomologyComplex B Λ k f j :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (moduleComplexPlusUnit B Λ h) _ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ ε.hom

lemma compactlySupportedCohomologyPullback_app {h : V ⟶ V}
    (ε : ((smallEtaleBaseChange B h).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
        (topology B V.obj V.property) (topology B V.obj V.property)).mapCochainComplexPlus ⋙
          compactlySupportedCohomologyComplex B Λ k f j ≅
        compactlySupportedCohomologyComplex B Λ k f j)
    (G : CochainComplex.Plus (Sheaf (topology B V.obj V.property)
      (ModuleCat.{max (u + 1) r} Λ))) :
    (compactlySupportedCohomologyPullback ε).app G =
      (compactlySupportedCohomologyComplex B Λ k f j).map ((moduleComplexPlusUnit B Λ h).app G) ≫
        ε.hom.app ((smallEtaleInverseImage B h _).mapCochainComplexPlus.obj G) := by
  simp only [compactlySupportedCohomologyPullback, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp]

/-- **The endomorphism `RΓ_c(h, φ)` of `RΓ_c(V, G)`** induced by a pair `(h, φ)`, with
`φ : h^* G ⟶ G` a morphism of bounded below complexes of sheaves of `Λ`-modules on the small
étale site of `V`, given the isomorphisms `ε_F : RΓ_c(V, h_* F) ≅ RΓ_c(V, F)`:
`RΓ_c(h, φ) = RΓ_c(V, φ) ∘ ε_{h^* G} ∘ RΓ_c(V, η_G)`. -/
@[weil "def_fk203_cohomology_endomorphism_of_pair"]
def compactlySupportedCohomologyEndomorphism
    {G : CochainComplex.Plus (Sheaf (topology B V.obj V.property)
      (ModuleCat.{max (u + 1) r} Λ))}
    (p : SmallEtaleComplexPair B V (ModuleCat.{max (u + 1) r} Λ) (ComplexShape.up ℤ) G.obj)
    (ε : ((smallEtaleBaseChange B p.hom).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) r} Λ)
        (topology B V.obj V.property) (topology B V.obj V.property)).mapCochainComplexPlus ⋙
          compactlySupportedCohomologyComplex B Λ k f j ≅
        compactlySupportedCohomologyComplex B Λ k f j) :
    (compactlySupportedCohomologyComplex B Λ k f j).obj G ⟶
      (compactlySupportedCohomologyComplex B Λ k f j).obj G :=
  (compactlySupportedCohomologyPullback ε).app G ≫
    (compactlySupportedCohomologyComplex B Λ k f j).map (ObjectProperty.homMk p.map)

/-- The defining formula `RΓ_c(h, φ) = RΓ_c(V, φ) ∘ ε_{h^* G} ∘ RΓ_c(V, η_G)`. -/
lemma compactlySupportedCohomologyEndomorphism_eq
    {G : CochainComplex.Plus (Sheaf (topology B V.obj V.property)
      (ModuleCat.{max (u + 1) r} Λ))}
    (p : SmallEtaleComplexPair B V (ModuleCat.{max (u + 1) r} Λ) (ComplexShape.up ℤ) G.obj)
    (ε : ((smallEtaleBaseChange B p.hom).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) r} Λ)
        (topology B V.obj V.property) (topology B V.obj V.property)).mapCochainComplexPlus ⋙
          compactlySupportedCohomologyComplex B Λ k f j ≅
        compactlySupportedCohomologyComplex B Λ k f j) :
    compactlySupportedCohomologyEndomorphism p ε =
      (compactlySupportedCohomologyComplex B Λ k f j).map
          ((moduleComplexPlusUnit B Λ p.hom).app G) ≫
        ε.hom.app ((smallEtaleInverseImage B p.hom _).mapCochainComplexPlus.obj G) ≫
          (compactlySupportedCohomologyComplex B Λ k f j).map (ObjectProperty.homMk p.map) := by
  rw [compactlySupportedCohomologyEndomorphism, compactlySupportedCohomologyPullback_app,
    Category.assoc]

end AlgebraicGeometry.SmallEtale

end
