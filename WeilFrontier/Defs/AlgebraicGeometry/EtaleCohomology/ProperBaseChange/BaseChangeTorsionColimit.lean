module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit
public import Weil.Attr

/-!
# The base change homomorphism computed by a choice of resolutions

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes, `F` an abelian sheaf on the small étale site of `X` and
`i` an integer. A choice of resolutions for `F[0]` is a quasi-isomorphism `ι : F[0] ⟶ I` and a
quasi-isomorphism `q : g'^* I ⟶ J`, with `I` and `J` K-injective (for instance bounded below
complexes of injective sheaves). The *base change homomorphism relative to `(ι, q)`* is
$$
β^i_{(ι,q)} := H^i(γ_{(ι,q)}) : H^i(g^* f_* I) ⟶ H^i(f'_* J),
$$
where `γ_{(ι,q)} : g^* f_* I ⟶ f'_* J` is the base change morphism of complexes
`Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`. Since `g^*` is exact and `I`
computes `Rf_* F`, the source is `g^*(R^i f_* F)`; since `g'^*` is exact, `J` computes
`Rf'_*(g'^* F)` and the target is `R^i f'_*(g'^* F)`.

We show that, read through these identifications, `β^i_{(ι,q)}` is the canonical base change
map in degree `i`, `Stacks.EtaleCohomology.etaleAbelianHigherBaseChange`, which is `H^i` of the
derived base change map at `F[0]` and involves no choice. In particular `β^i_{(ι,q)}` does not
depend on the choice of resolutions up to the identifications of its source and target.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChange` — the base change
  homomorphism `β^i_{(ι,q)} = H^i(γ_{(ι,q)})`.
* `Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChangeSourceIso`,
  `Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChangeTargetIso` — the identifications
  of `H^i(g^* f_* I)` and `H^i(f'_* J)` with the source and target of the canonical map.
* `Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChangeRightDerivedSourceIso`,
  `Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChangeRightDerivedTargetIso` — for
  `i ≥ 0`, the identifications `H^i(g^* f_* I) ≅ g^*(R^i f_* F)` and
  `H^i(f'_* J) ≅ R^i f'_*(g'^* F)`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianHigherBaseChange_app_eq` — the canonical base change map
  in degree `i` at `F` is `β^i_{(ι,q)}` read through the identifications.
* `Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChange_eq` — for `i ≥ 0`, under
  `H^i(g^* f_* I) ≅ g^*(R^i f_* F)` and `H^i(f'_* J) ≅ R^i f'_*(g'^* F)`, `β^i_{(ι,q)}` is the
  canonical map `g^*(R^i f_* F) ⟶ R^i f'_*(g'^* F)`.

## Implementation notes

Sheaves are abelian sheaves on Mathlib's small étale site `X.smallEtaleTopology` with
coefficients `AddCommGrpCat.{max (u + 1) v}`, the setting of
`Stacks.EtaleCohomology.etaleAbelianHigherBaseChange`. The resolutions are only asked to be
K-injective, which contains the case of bounded below complexes of injective sheaves
(`CochainComplex.isKInjective_of_injective`). The square is only assumed commutative.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6, p. 61][FreitagKiehl1988]
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/- As in `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`, the preadditive structure and
the zero morphisms of abelian sheaves are taken from the abelian structure. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The `n`-th cohomology of the image in the derived category of a complex `K` is the `n`-th
homology of `K`. -/
def homologyFunctorObjQhQuotientObjIso (K : CochainComplex C ℤ) (n : ℤ) :
    (homologyFunctor C n).obj (Qh.obj ((HomotopyCategory.quotient C _).obj K)) ≅ K.homology n :=
  (homologyFunctorFactorsh C n).app _ ≪≫ (HomotopyCategory.homologyFunctorFactors C _ n).app K

/-- The `n`-th cohomology of the image in the derived category of a morphism of complexes `φ` is
`H^n(φ)`, read through `homologyFunctorObjQhQuotientObjIso`. -/
@[reassoc]
theorem homologyFunctor_map_Qh_map_quotient_map {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    (homologyFunctor C n).map (Qh.map ((HomotopyCategory.quotient C _).map φ)) =
      (homologyFunctorObjQhQuotientObjIso K n).hom ≫ HomologicalComplex.homologyMap φ n ≫
        (homologyFunctorObjQhQuotientObjIso L n).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  have h₁ := (homologyFunctorFactorsh C n).hom.naturality ((HomotopyCategory.quotient C _).map φ)
  have h₂ := (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).hom.naturality φ
  simp only [Functor.comp_map] at h₁ h₂
  dsimp only [homologyFunctorObjQhQuotientObjIso]
  erw [reassoc_of% h₁, h₂]
  exact (Category.assoc _ _ _).symm

end DerivedCategory

namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The base change homomorphism relative to a choice of resolutions.** For a complex `I` of
abelian sheaves on `X`, a morphism of complexes `q : g'^* I ⟶ J` and `i : ℤ`, the morphism
`β^i = H^i(γ) : H^i(g^* f_* I) ⟶ H^i(f'_* J)` on `Y'`, where
`γ = etaleAbelianResolutionBaseChange f g g' f' h I q`. -/
@[weil "def_fk106_base_change_homomorphism"]
def etaleAbelianResolutionHigherBaseChange
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    (i : ℤ) :
    (((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i ⟶
      (((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).homology i :=
  HomologicalComplex.homologyMap (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I q) i

section Resolutions

variable {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
  {J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
  (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F ⟶ I) [QuasiIso ι]
  (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)

/-- The image of a sheaf `F` under the single-complex functor of the derived category is the
image of the complex `F[0]`. -/
def etaleAbelianSingleObjIsoQhObj (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (DerivedCategory.singleFunctor _ 0).obj F ≅ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) :=
  (DerivedCategory.singleFunctorIsoCompQh _ 0).app F

/-- For a quasi-isomorphism `ι : F[0] ⟶ I` into a K-injective complex, the identification of
`H^i(g^* f_* I)` with `H^i(g^*(Rf_* F[0]))`. -/
def etaleAbelianResolutionHigherBaseChangeSourceIso (hI : CochainComplex.IsKInjective I) (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((etaleAbelianDerivedInverseImage.{u, v} g).obj
      ((etaleAbelianDerivedDirectImage.{u, v} f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
    (((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i :=
  (DerivedCategory.homologyFunctor _ i).mapIso
      ((etaleAbelianDerivedInverseImage.{u, v} g).mapIso
          ((etaleAbelianDerivedDirectImage.{u, v} f).mapIso (etaleAbelianSingleObjIsoQhObj F)) ≪≫
        (etaleAbelianResolutionBaseChangeSourceIso.{u, v} f g ι hI).symm) ≪≫
    DerivedCategory.homologyFunctorObjQhQuotientObjIso _ i

/-- For quasi-isomorphisms `ι : F[0] ⟶ I` and `q : g'^* I ⟶ J` with `J` K-injective, the
identification of `H^i(f'_* J)` with `H^i(Rf'_*(g'^* F[0]))`. -/
def etaleAbelianResolutionHigherBaseChangeTargetIso [QuasiIso q]
    (hJ : CochainComplex.IsKInjective J) (i : ℤ) :
    (((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj J).homology
        i ≅
    (DerivedCategory.homologyFunctor _ i).obj ((etaleAbelianDerivedDirectImage.{u, v} f').obj
      ((etaleAbelianDerivedInverseImage.{u, v} g').obj
        ((DerivedCategory.singleFunctor _ 0).obj F))) :=
  (DerivedCategory.homologyFunctorObjQhQuotientObjIso _ i).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso
      (etaleAbelianResolutionBaseChangeTargetIso.{u, v} g' f' ι q hJ ≪≫
        (etaleAbelianDerivedDirectImage.{u, v} f').mapIso
          ((etaleAbelianDerivedInverseImage.{u, v} g').mapIso
            (etaleAbelianSingleObjIsoQhObj F).symm))

/-- **The base change homomorphism is the canonical one.** For quasi-isomorphisms
`ι : F[0] ⟶ I` and `q : g'^* I ⟶ J` with `I` and `J` K-injective, the canonical base change map
in degree `i` at `F` is `β^i_{(ι,q)} = H^i(γ_{(ι,q)})`, read through the identifications of
its source and target. -/
theorem etaleAbelianHigherBaseChange_app_eq [QuasiIso q] (hI : CochainComplex.IsKInjective I)
    (hJ : CochainComplex.IsKInjective J) (i : ℤ) :
    (etaleAbelianHigherBaseChange.{u, v} f g g' f' h i).app F =
      (etaleAbelianResolutionHigherBaseChangeSourceIso.{u, v} f g ι hI i).hom ≫
        etaleAbelianResolutionHigherBaseChange.{u, v} f g g' f' h I q i ≫
        (etaleAbelianResolutionHigherBaseChangeTargetIso.{u, v} g' f' ι q hJ i).hom := by
  have hnat := (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).naturality
    (etaleAbelianSingleObjIsoQhObj F).inv
  have hβ : (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
      ((DerivedCategory.singleFunctor _ 0).obj F) =
      (etaleAbelianDerivedDirectImage.{u, v} f ⋙ etaleAbelianDerivedInverseImage.{u, v} g).map
          (etaleAbelianSingleObjIsoQhObj F).hom ≫
        (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app _ ≫
        (etaleAbelianDerivedInverseImage.{u, v} g' ⋙ etaleAbelianDerivedDirectImage.{u, v} f').map
          (etaleAbelianSingleObjIsoQhObj F).inv := by
    rw [← hnat, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  simp only [etaleAbelianHigherBaseChange, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    etaleAbelianResolutionHigherBaseChangeSourceIso,
    etaleAbelianResolutionHigherBaseChangeTargetIso,
    etaleAbelianResolutionHigherBaseChange, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [hβ, etaleAbelianDerivedBaseChange_app_eq.{u, v} f g g' f' h ι q hI hJ]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc,
    DerivedCategory.homologyFunctor_map_Qh_map_quotient_map_assoc]

/-- For `p : ℕ`, the identification `H^p(g^* f_* I) ≅ g^*(R^p f_* F)`. -/
def etaleAbelianResolutionHigherBaseChangeRightDerivedSourceIso
    (hI : CochainComplex.IsKInjective I) (p : ℕ) :
    (((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology (p : ℤ) ≅
      (etaleAbelianInverseImage.{u, v} g).obj
        (((etaleAbelianDirectImage.{u, v} f).rightDerived p).obj F) :=
  (etaleAbelianResolutionHigherBaseChangeSourceIso.{u, v} f g ι hI p).symm ≪≫
    (etaleAbelianHigherBaseChangeSourceIso.{u, v} f g p).app F

/-- For `p : ℕ`, the identification `H^p(f'_* J) ≅ R^p f'_*(g'^* F)`. -/
def etaleAbelianResolutionHigherBaseChangeRightDerivedTargetIso [QuasiIso q]
    (hJ : CochainComplex.IsKInjective J) (p : ℕ) :
    (((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj J).homology
        (p : ℤ) ≅
      ((etaleAbelianDirectImage.{u, v} f').rightDerived p).obj
        ((etaleAbelianInverseImage.{u, v} g').obj F) :=
  etaleAbelianResolutionHigherBaseChangeTargetIso.{u, v} g' f' ι q hJ p ≪≫
    (etaleAbelianHigherBaseChangeTargetIso.{u, v} g' f' p).app F

/-- **The base change homomorphism `g^*(R^p f_* F) ⟶ R^p f'_*(g'^* F)`.** For `p : ℕ` and
quasi-isomorphisms `ι : F[0] ⟶ I`, `q : g'^* I ⟶ J` with `I` and `J` K-injective, the base
change homomorphism `β^p_{(ι,q)} = H^p(γ_{(ι,q)})`, read through
`H^p(g^* f_* I) ≅ g^*(R^p f_* F)` and `H^p(f'_* J) ≅ R^p f'_*(g'^* F)`, is the canonical base
change map in degree `p` at `F`. -/
@[weil "def_fk106_base_change_homomorphism"]
theorem etaleAbelianResolutionHigherBaseChange_eq [QuasiIso q]
    (hI : CochainComplex.IsKInjective I) (hJ : CochainComplex.IsKInjective J) (p : ℕ) :
    (etaleAbelianResolutionHigherBaseChangeRightDerivedSourceIso.{u, v} f g ι hI p).inv ≫
        etaleAbelianResolutionHigherBaseChange.{u, v} f g g' f' h I q p ≫
        (etaleAbelianResolutionHigherBaseChangeRightDerivedTargetIso.{u, v} g' f' ι q hJ p).hom =
      (etaleAbelianHigherBaseChangeSourceIso.{u, v} f g p).inv.app F ≫
        (etaleAbelianHigherBaseChange.{u, v} f g g' f' h p).app F ≫
        (etaleAbelianHigherBaseChangeTargetIso.{u, v} g' f' p).hom.app F := by
  rw [etaleAbelianHigherBaseChange_app_eq.{u, v} f g g' f' h ι q hI hJ]
  simp only [etaleAbelianResolutionHigherBaseChangeRightDerivedSourceIso,
    etaleAbelianResolutionHigherBaseChangeRightDerivedTargetIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.app_inv, Iso.app_hom, Category.assoc]

end Resolutions

end Stacks.EtaleCohomology
