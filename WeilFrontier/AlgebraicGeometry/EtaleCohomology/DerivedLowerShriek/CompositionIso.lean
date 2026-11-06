module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoCoefficientUniverse
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDerived
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.CompactSupportCohomologyDerived
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriekAffineEtale
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.Basic

/-!
# The composition of derived direct images with proper support

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of quasi-compact and quasi-separated schemes, and fix
compactifications of `f`, `g` and `h = g ∘ f`. Computing `Rf_!`, `Rg_!` and `Rh_!` with them,
there is an isomorphism `Rg_! (Rf_! K) ≅ Rh_! K`, natural in a bounded below complex `K` of
sheaves of `Λ`-modules on the small étale site of `X` with torsion cohomology sheaves.

A morphism admitting a compactification (an open immersion followed by a proper morphism) is
separated and locally of finite type, so the only conditions are the quasi-compactness and
quasi-separatedness of the schemes.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedLowerShriekCompIsoTorsion`: `Rh_! ≅ Rf_! ⋙ Rg_!` on
  `D⁺_tors(X)`, for arbitrary compactifications of `f`, `g` and `h = f ≫ g`, on the small étale
  sites `AlgebraicGeometry.SmallEtale` of a big étale site.

## Implementation notes

The isomorphism is `Stacks.EtaleCohomology.derivedLowerShriekCompIsoUniv`, on Mathlib's small
étale sites, transported along the equivalences of sheaf categories
`AlgebraicGeometry.SmallEtale.moduleSheafEquivEtaleModules`. The source states the result for
abelian sheaves; here the coefficients are an arbitrary ring `Λ`, the source's case being
`Λ = ℤ`. The torsion subcategory is `AlgebraicGeometry.SmallEtale.isTorsionPlus`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} (Λ : Type r) [Ring Λ]

/-- A morphism with a compactification is separated: it is an open immersion followed by a
proper morphism. -/
theorem isSeparated_of_compactification {X S : Scheme.{u}} {f : X ⟶ S}
    (c : f.Compactification) : IsSeparated f := by
  rw [← c.immersion_comp_toBase]
  infer_instance

/-- A morphism with a compactification is locally of finite type: it is an open immersion
followed by a proper morphism. -/
theorem locallyOfFiniteType_of_compactification {X S : Scheme.{u}} {f : X ⟶ S}
    (c : f.Compactification) : LocallyOfFiniteType f := by
  rw [← c.immersion_comp_toBase]
  infer_instance

variable {X Y S : B.Scheme} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ S.obj)

/-- Restricting `E_X : D⁺(X) ≌ D⁺(X_ét)`, from the small étale site of `B` to Mathlib's small
étale site, to the torsion complexes, for coefficients in any universe. -/
abbrev isTorsionPlusLiftUniv :
    (isTorsionPlus.{u, r} B X.obj X.property Λ).FullSubcategory ⥤
      (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).FullSubcategory :=
  ObjectProperty.lift _
    ((isTorsionPlus.{u, r} B X.obj X.property Λ).ι ⋙
      (moduleSheafEquivEtaleModules B Λ X).functor.mapDerivedCategoryPlus)
    (fun K ↦ K.property)

/-- **The composition of derived direct images with proper support.** Let `f : X ⟶ Y` and
`g : Y ⟶ S` be morphisms of quasi-compact and quasi-separated schemes, with compactifications
`cf`, `cg` and `ch` of `f`, `g` and `h = f ≫ g`. Then `Rh_! K ≅ Rg_! (Rf_! K)`, naturally in
`K ∈ D⁺_tors(X)`, the functors being computed with the given compactifications. -/
@[weil "thm_fk108_proper_direct_image_comp"]
def derivedLowerShriekCompIsoTorsion [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] [CompactSpace S.obj]
    [QuasiSeparatedSpace S.obj] (cf : f.Compactification) (cg : g.Compactification)
    (ch : (f ≫ g).Compactification) :
    (isTorsionPlus.{u, r} B X.obj X.property Λ).ι ⋙ derivedLowerShriek Λ (f ≫ g) ch ≅
      (isTorsionPlus.{u, r} B X.obj X.property Λ).ι ⋙ derivedLowerShriek Λ f cf ⋙
        derivedLowerShriek Λ g cg :=
  haveI := isSeparated_of_compactification cf
  haveI := locallyOfFiniteType_of_compactification cf
  haveI := isSeparated_of_compactification cg
  haveI := locallyOfFiniteType_of_compactification cg
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (isTorsionPlusLiftUniv Λ (X := X))
        (Stacks.EtaleCohomology.derivedLowerShriekCompIsoUniv.{u, r} Λ f g cf cg ch))
      (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus ≪≫
    Functor.isoWhiskerLeft
      (isTorsionPlusLiftUniv Λ (X := X) ⋙ (Stacks.EtaleCohomology.isTorsionPlus.{u, r} Λ X.obj).ι ⋙
        Stacks.EtaleCohomology.derivedLowerShriek.{u, r} f cf Λ)
      (Functor.isoWhiskerRight (mapDerivedCategoryPlusInverseCompFunctorIso Λ Y)
        (Stacks.EtaleCohomology.derivedLowerShriek.{u, r} g cg Λ ⋙
          (moduleSheafEquivEtaleModules B Λ S).inverse.mapDerivedCategoryPlus)).symm

end AlgebraicGeometry.SmallEtale

end

/-! ### The derived direct image with proper support preserves torsion and triangles -/

/-!
# The derived direct image with proper support preserves torsion and triangles

Let `f : X ⟶ S` be a morphism of schemes with a compactification `c = (X̄, j, f̄)`, and let
`Rf_! = R f̄_* ∘ j_!` be the derived direct image with proper support on bounded below derived
categories of étale sheaves of `Λ`-modules. Then `Rf_!` carries the bounded below complexes with
torsion cohomology sheaves on `X` to bounded below complexes with torsion cohomology sheaves on
`S`, and it carries admissible triangles to admissible triangles.

The first statement holds because `j_!` is exact and preserves torsion sheaves, so that `j_! K`
has torsion cohomology sheaves, and the derived direct image along the quasi-compact and
quasi-separated morphism `f̄` preserves torsion cohomology. The second holds because `Rf_!` is a
composite of triangulated functors.

## Main results

* `DerivedCategory.Plus.mapTriangle_mem_admissibleTriangles`: a triangulated functor between
  bounded below derived categories carries admissible triangles to admissible triangles.
* `AlgebraicGeometry.SmallEtale.isTorsionPlus_derivedLowerShriek_obj`: `Rf_!` carries
  `D⁺_tors(X)` into `D⁺_tors(S)`.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriek_isTriangulated`: `Rf_!` is a triangulated
  functor.
* `AlgebraicGeometry.SmallEtale.derivedLowerShriek_mapTriangle_mem_admissibleTriangles`: `Rf_!`
  carries admissible triangles to admissible triangles.

## Implementation notes

The source states the result for abelian sheaves, that is `Λ = ℤ`. The torsion statement is
proved for an arbitrary ring `Λ : Type`, and the statement about triangles for coefficients in
any universe. Triangles of `D⁺` are read in the derived category `D` through the inclusion
`D⁺ ⥤ D`, where admissible triangles are defined.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8][FreitagKiehl]
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace DerivedCategory.Plus

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]

/-- A triangulated functor `G : D⁺(C) ⥤ D⁺(D)` carries admissible triangles to admissible
triangles, the triangles of `D⁺` being read in the derived categories through the inclusions
`D⁺ ⥤ D`. -/
theorem mapTriangle_mem_admissibleTriangles (G : Plus C ⥤ Plus D) [G.CommShift ℤ]
    [G.IsTriangulated] (T : Triangle (Plus C))
    (hT : ι.mapTriangle.obj T ∈ DerivedCategory.admissibleTriangles C) :
    ι.mapTriangle.obj (G.mapTriangle.obj T) ∈ DerivedCategory.admissibleTriangles D := by
  rw [DerivedCategory.mem_admissibleTriangles_iff] at hT ⊢
  have h₁ : Triangle.mk T.mor₁ T.mor₂ (-T.mor₃) ∈ distTriang (Plus C) := by
    rw [← (ι : Plus C ⥤ _).map_distinguished_iff]
    exact isomorphic_distinguished _ hT _ ((ι : Plus C ⥤ _).mapTriangleNegMor₃Iso T)
  have h₂ : Triangle.mk (G.mapTriangle.obj T).mor₁ (G.mapTriangle.obj T).mor₂
      (-(G.mapTriangle.obj T).mor₃) ∈ distTriang (Plus D) :=
    isomorphic_distinguished _ (G.map_distinguished _ h₁) _ (G.mapTriangleNegMor₃Iso T).symm
  exact isomorphic_distinguished _ ((ι : Plus D ⥤ _).map_distinguished _ h₂) _
    ((ι : Plus D ⥤ _).mapTriangleNegMor₃Iso _).symm

end DerivedCategory.Plus

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X S : B.Scheme} (f : X.obj ⟶ S.obj) (c : f.Compactification)

section Torsion

attribute [-instance] hasSheafify_moduleCat_max hasSheafify_moduleSheaf

/-- Sheafification of presheaves of `Λ`-modules in the universe `u + 1` on the small étale site,
for `Λ : Type`: `AlgebraicGeometry.SmallEtale.hasSheafify_moduleSheaf` with its coefficient
universes fixed. -/
local instance hasSheafify_moduleCat_succ_ofTorsion (Y : B.Scheme) (Λ : Type) [Ring Λ] :
    HasSheafify (topology B Y.obj Y.property) (ModuleCat.{u + 1} Λ) :=
  hasSheafify_moduleSheaf.{u, 0, 0} B Y Λ

/-- **`Rf_!` carries `D⁺_tors(X)` into `D⁺_tors(S)`**: for a compactification `c` of
`f : X ⟶ S` and a bounded below complex `K` of sheaves of `Λ`-modules on the small étale site of
`X` all of whose cohomology sheaves are torsion, every cohomology sheaf of `Rf_! K` is
torsion. -/
@[weil "lem_fk108_proper_direct_image_derived_torsion"]
theorem isTorsionPlus_derivedLowerShriek_obj (Λ : Type) [Ring Λ]
    (K : DerivedCategory.Plus (ModuleSheaf.{u, 0, 0} B X Λ))
    (hK : isTorsionPlus.{u, 0} B X.obj X.property Λ K) :
    isTorsionPlus.{u, 0} B S.obj S.property Λ ((derivedLowerShriek.{u, 0} Λ f c).obj K) := by
  have h := Stacks.EtaleCohomology.isTorsionPlus_derivedLowerShriek_obj Λ f c _ hK
  intro q
  exact Stacks.EtaleCohomology.IsTorsionEtaleModule.of_iso_univ Λ
    ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((mapDerivedCategoryPlusInverseCompFunctorIso Λ S).app _).symm) (h q)

end Torsion

variable (Λ : Type r) [Ring Λ]

/-- `Rf_!` commutes with the shift, being a composite of functors that do. -/
instance derivedLowerShriek_commShift : (derivedLowerShriek.{u, r} Λ f c).CommShift ℤ := by
  dsimp only [derivedLowerShriek]
  infer_instance

/-- **`Rf_!` is a triangulated functor**, being the composite of the triangulated functors
`E_X`, `Rf̄_* ∘ j_!` and `E_S⁻¹`, for `E` the equivalences with the sheaf categories of
Mathlib's small étale sites. -/
instance derivedLowerShriek_isTriangulated : (derivedLowerShriek.{u, r} Λ f c).IsTriangulated := by
  dsimp only [derivedLowerShriek, derivedLowerShriek_commShift]
  infer_instance

/-- **`Rf_!` carries admissible triangles to admissible triangles**: for a compactification `c`
of `f : X ⟶ S` and a triangle `T` of `D⁺(X)` which is admissible in `D(X)`, the triangle
`Rf_! T` of `D⁺(S)` is admissible in `D(S)`. -/
@[weil "lem_fk108_proper_direct_image_derived_torsion"]
theorem derivedLowerShriek_mapTriangle_mem_admissibleTriangles
    (T : Triangle (DerivedCategory.Plus (ModuleSheaf.{u, r, r} B X Λ)))
    (hT : DerivedCategory.Plus.ι.mapTriangle.obj T ∈ DerivedCategory.admissibleTriangles _) :
    DerivedCategory.Plus.ι.mapTriangle.obj ((derivedLowerShriek.{u, r} Λ f c).mapTriangle.obj T) ∈
      DerivedCategory.admissibleTriangles _ :=
  DerivedCategory.Plus.mapTriangle_mem_admissibleTriangles _ T hT

end AlgebraicGeometry.SmallEtale
