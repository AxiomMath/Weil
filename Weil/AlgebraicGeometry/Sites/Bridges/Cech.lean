module

public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyCovering
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.CechProductMapExt

/-!
# Čech complexes on `Et(S)` and on the small étale site

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes, a full
subcategory of the small étale category of `S` stable under fibre products. For a family
`𝔘 = (Uᵢ → U)_i` of morphisms of `Et(S)` with target `U`, the iterated fibre products
`U_{ν₀} ×_U ⋯ ×_U U_{ν_p}` are the same whether they are formed in `Et(S)` or in the small
étale category. Hence, for a presheaf `G` on the small étale category, the Čech complex of the
image family `ι(𝔘)` with coefficients in `G` is isomorphic to the Čech complex of `𝔘` with
coefficients in the restriction `G ∘ ι`, compatibly with refinement maps; the same holds for
Čech cohomology. For `S` locally noetherian, sheaves on `Et(S)` are sheaves on the small étale
site (`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`), and the Čech complex of an
`Et(S)`-sheaf `F` along `𝔘` is the Čech complex of the corresponding small étale sheaf along
`ι(𝔘)`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplexIsoSmallEtale`:
  `Č^•(ι(𝔘), G) ≅ Č^•(𝔘, G ∘ ι)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomologyIsoSmallEtale`:
  `Ȟ^p(ι(𝔘), G) ≅ Ȟ^p(𝔘, G ∘ ι)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplexIsoSheafEquiv`,
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomologyIsoSheafEquiv`: the same for a
  sheaf on `Et(S)` and the corresponding sheaf on the small étale site.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementMapInclusion`: the image under
  `ι` of a refinement.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.preservesFiniteProducts_overPost_inclusion`:
  the inclusion preserves the iterated fibre products over an object.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplexMap_comp_cechComplexIsoSmallEtale_hom`
  : the isomorphism `cechComplexIsoSmallEtale` commutes with the cochain maps of refinements.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inclusion of `Et(S)` into the small étale category preserves the terminal object of each
slice. -/
instance preservesTerminal_overPost_inclusion (U : SmallNoetherianSeparatedEtale B S hS) :
    PreservesLimit (Functor.empty.{0} (Over U)) (Over.post (X := U) (inclusion B S hS)) :=
  preservesLimit_of_preserves_limit_cone (Over.mkIdTerminal (X := U))
    ((isLimitMapConeEmptyConeEquiv _ _).symm
      (Over.mkIdTerminal.ofIso (Over.isoMk (Iso.refl _) (by
        simp only [Over.mk_hom, Iso.refl_hom]; rfl))))

/-- The inclusion of `Et(S)` into the small étale category preserves finite products in each
slice, i.e. finite iterated fibre products over an object. -/
instance preservesFiniteProducts_overPost_inclusion (U : SmallNoetherianSeparatedEtale B S hS) :
    PreservesFiniteProducts (Over.post (X := U) (inclusion B S hS)) :=
  have := preservesLimitsOfShape_pempty_of_preservesTerminal
    (Over.post (X := U) (inclusion B S hS))
  .of_preserves_binary_and_terminal _

variable {U : SmallNoetherianSeparatedEtale B S hS} (E : PreZeroHypercover.{w} U)

/-- The comparison map from the image of an iterated fibre product of `E` to the iterated fibre
product of the image family is an isomorphism. -/
instance isIso_cechProductMapOfFunctor_inclusion (n : ℕ) (i : Fin (n + 1) → E.I₀) :
    IsIso (Stacks.CechSite.cechProductMapOfFunctor (inclusion B S hS) E n i) :=
  Stacks.CechSite.isIso_cechProductMapOfFunctor _ _ n i

section Presheaf

variable {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]

/-- Transport of `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplex` to the small
étale category: for a presheaf `G` on the small étale category, the Čech complex of the image
family `ι(𝔘)` with coefficients in `G` is the Čech complex of `𝔘` with coefficients in `G ∘ ι`. -/
noncomputable def cechComplexIsoSmallEtale (G : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    Stacks.CechSite.cechComplex (E.map (inclusion B S hS)) G ≅
      cechComplex E ((inclusion B S hS).op ⋙ G) :=
  Stacks.CechSite.cechComplexIsoOfFunctor _ E G fun _ _ ↦ inferInstance

/-- The image under the inclusion `ι` of a refinement `φ : 𝔘 ⟶ 𝔙` of families of `Et(S)` with
target `U`: the refinement `ι(𝔘) ⟶ ι(𝔙)` with the same index map and components `ι(φᵢ)`. -/
@[simps]
def refinementMapInclusion {G : PreZeroHypercover.{w'} U} (φ : E.Hom G) :
    (E.map (inclusion B S hS)).Hom (G.map (inclusion B S hS)) where
  s₀ := φ.s₀
  h₀ i := (inclusion B S hS).map (φ.h₀ i)
  w₀ i := ((inclusion B S hS).map_comp _ _).symm.trans (congrArg _ (φ.w₀ i))

-- The image family shares its index type and selected objects with the original one only after
-- `PreZeroHypercover.map` and `Over.post` are unfolded; the rewrites below need these unfoldings
-- at `implicit` transparency, as in `Stacks.CechSite.cechComplexMapOfFunctor`.
attribute [local implicit_reducible] Stacks.CechSite.cechFormalCoproduct
  Stacks.CechSite.cechFormalCoproductMap CategoryTheory.PreZeroHypercover.map
  CategoryTheory.Over.post in
/-- Transport of `AlgebraicGeometry.SmallNoetherianSeparatedEtale.refinementCochainMap` to the
small étale category: under `cechComplexIsoSmallEtale`, the cochain map of the image refinement
`ι(φ)` with coefficients in `G` is the cochain map of `φ` with coefficients in `G ∘ ι`. -/
@[reassoc]
theorem cechComplexMap_comp_cechComplexIsoSmallEtale_hom [HasProducts.{w'} A]
    {G : PreZeroHypercover.{w'} U} (φ : E.Hom G) (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    Stacks.CechSite.cechComplexMap (E.map (inclusion B S hS)) (G.map (inclusion B S hS))
        ((PreZeroHypercover.homOverIdEquivHom _ _).symm (refinementMapInclusion E φ)) P ≫
        (cechComplexIsoSmallEtale E P).hom =
      (cechComplexIsoSmallEtale G P).hom ≫ refinementCochainMap φ ((inclusion B S hS).op ⋙ P) := by
  ext n : 1
  refine Pi.hom_ext _ _ fun (i : Fin (n + 1) → E.I₀) ↦ ?_
  have hkey : (Stacks.CechSite.cechProductMapOfFunctor (inclusion B S hS) E n i).left ≫
      Stacks.CechSite.cechProductMap (E.map (inclusion B S hS)) (G.map (inclusion B S hS))
        ((PreZeroHypercover.homOverIdEquivHom _ _).symm (refinementMapInclusion E φ)) n i =
      (inclusion B S hS).map (refinementProductMap φ n i) ≫
        (Stacks.CechSite.cechProductMapOfFunctor (inclusion B S hS) G n (φ.s₀ ∘ i)).left := by
    refine Stacks.CechSite.cechProduct_left_hom_ext (G.map (inclusion B S hS)) n (φ.s₀ ∘ i)
      fun b ↦ ?_
    erw [Category.assoc, Stacks.CechSite.cechProductMap_comp_π_left_anyUniverses,
      Category.assoc]
    have e1 := (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left
      (Stacks.CechSite.cechProductMapOfFunctor_comp_π (inclusion B S hS) E n i b))
    have e2 := (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left
      (Stacks.CechSite.cechProductMapOfFunctor_comp_π (inclusion B S hS) G n (φ.s₀ ∘ i) b))
    have e3 := refinementProductMap_π φ n i b
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine (congrArg (· ≫ _) e1).trans (Eq.trans ?_ (congrArg (_ ≫ ·) e2).symm)
    exact ((inclusion B S hS).map_comp _ _).symm.trans
      ((congrArg (inclusion B S hS).map e3.symm).trans ((inclusion B S hS).map_comp _ _))
  have h1 := Stacks.CechSite.cechComplexMapOfFunctor_f_Pi_π (inclusion B S hS) E P n i
  have h2 := Stacks.CechSite.cechComplexMap_f_Pi_π (E.map (inclusion B S hS))
    (G.map (inclusion B S hS))
    ((PreZeroHypercover.homOverIdEquivHom _ _).symm (refinementMapInclusion E φ)) P n i
  have h3 := Stacks.CechSite.cechComplexMapOfFunctor_f_Pi_π (inclusion B S hS) G P n (φ.s₀ ∘ i)
  have h4 := refinementCochainMap_f_π φ ((inclusion B S hS).op ⋙ P) n i
  simp only [HomologicalComplex.comp_f, cechComplexIsoSmallEtale,
    Stacks.CechSite.cechComplexIsoOfFunctor, asIso_hom]
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine (congrArg (_ ≫ ·) h1).trans (Eq.trans ?_ (congrArg (_ ≫ ·) h4).symm)
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
  refine (congrArg (· ≫ _) h2).trans (Eq.trans ?_ (congrArg (· ≫ _) h3).symm)
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine congrArg (_ ≫ ·) ?_
  refine (P.map_comp _ _).symm.trans (Eq.trans ?_ (P.map_comp _ _))
  exact congrArg (fun f ↦ P.map f.op) hkey

end Presheaf

section Cohomology

variable {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]

/-- Transport of `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomology` to the small
étale category: `Ȟ^p(ι(𝔘), G) ≅ Ȟ^p(𝔘, G ∘ ι)` for a presheaf `G` on the small étale
category. -/
noncomputable def cechCohomologyIsoSmallEtale (G : (SmallEtale B S hS)ᵒᵖ ⥤ A) (p : ℕ) :
    Stacks.CechSite.cechCohomology (E.map (inclusion B S hS)) G p ≅
      cechCohomology E ((inclusion B S hS).op ⋙ G) p :=
  Stacks.CechSite.cechCohomologyIsoOfFunctor _ E G (fun _ _ ↦ inferInstance) p

end Cohomology

section Sheaf

variable [IsLocallyNoetherian S] {A : Type u'} [Category.{v'} A] [HasLimitsOfSize.{u, u} A]

/-- Transport of `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechComplex` along
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`: the Čech complex of a sheaf `F`
on `Et(S)` along `𝔘` is the Čech complex of the corresponding sheaf on the small étale site
along `ι(𝔘)`. -/
noncomputable def cechComplexIsoSheafEquiv [Preadditive A] [HasProducts.{w} A]
    (F : Sheaf (topology B S hS) A) :
    cechComplex E F.obj ≅
      Stacks.CechSite.cechComplex (E.map (inclusion B S hS))
        ((sheafEquiv B S hS A).functor.obj F).obj :=
  (Stacks.CechSite.cechComplexFunctor E).mapIso
      ((sheafToPresheaf _ A).mapIso ((sheafEquiv B S hS A).unitIso.app F)) ≪≫
    (cechComplexIsoSmallEtale E ((sheafEquiv B S hS A).functor.obj F).obj).symm

/-- Transport of `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomology` along
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`: `Ȟ^p(𝔘, F)` for a sheaf `F` on
`Et(S)` is `Ȟ^p(ι(𝔘), F')` for the corresponding sheaf `F'` on the small étale site. -/
noncomputable def cechCohomologyIsoSheafEquiv [Abelian A] [HasProducts.{w} A]
    (F : Sheaf (topology B S hS) A) (p : ℕ) :
    cechCohomology E F.obj p ≅
      Stacks.CechSite.cechCohomology (E.map (inclusion B S hS))
        ((sheafEquiv B S hS A).functor.obj F).obj p :=
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (cechComplexIsoSheafEquiv E F)

end Sheaf

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
