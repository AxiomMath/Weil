module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionVanishing
public import Weil.Attr

/-!
# The base change morphism computed by a choice of resolutions

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a commutative square of schemes and `F` a complex of abelian sheaves on the small étale site
of `X`. A *choice of resolutions* for `F` is a pair of quasi-isomorphisms `ι : F ⟶ I` and
`q : g'^* I ⟶ J`, where `I` (on `X`) and `J` (on `X'`) are complexes of injective sheaves
(bounded below). The *base change morphism relative to `(ι, q)`* is the morphism of complexes of
sheaves on `Y'`
$$
γ_{(ι,q)} := f'_*(q) ∘ β_I : g^* f_* I ⟶ f'_* g'^* I ⟶ f'_* J,
$$
where `β_I` is the base change map applied degreewise. Since `f_* I` represents `Rf_* F` and
`f'_* J` represents `Rf'_* (g'^* F)`, the image of `γ_{(ι,q)}` in the derived category of `Y'` is
regarded as a morphism `g^*(Rf_* F) ⟶ Rf'_*(g'^* F)`.

We show that this morphism is the canonical base change map
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` at `F`, which is defined without any
choice by the universal property of the derived functor: under the identifications
`Q(g^* f_* I) ≅ g^*(Rf_* F)` and `Q(f'_* J) ≅ Rf'_*(g'^* F)` given by `ι`, `q` and the
derived-functor units, `Q(γ_{(ι,q)})` is the base change map. In particular `Q(γ_{(ι,q)})` does
not depend on the choice of resolutions.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange` — the morphism of complexes
  `γ_{(ι,q)} : g^* f_* I ⟶ f'_* J`.
* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChangeSourceIso` — the identification
  `Q(g^* f_* I) ≅ g^*(Rf_* F)`.
* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChangeTargetIso` — the identification
  `Q(f'_* J) ≅ Rf'_*(g'^* F)`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_map_eq` — for an arbitrary complex
  `I` and an arbitrary morphism `q : g'^* I ⟶ J`, the base change map at `I` followed by
  `Rf'_*(q)` agrees with `Q(γ)` followed by the derived-functor unit of `Rf'_*` at `J`.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_app_eq` — for a choice of resolutions
  `(ι, q)` by K-injective complexes, the base change map at `F` is
  `Q(γ_{(ι,q)})` read through the two identifications.
* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_app_eq_of_injective` — the same for
  bounded below complexes of injective sheaves.

## Implementation notes

The square is only assumed commutative, and the complexes are unbounded; boundedness below of
`I` and `J` is used only to know that they are K-injective
(`CochainComplex.isKInjective_of_injective`), which is all the general statement asks. Sheaves
are abelian sheaves on Mathlib's small étale site `X.smallEtaleTopology` with coefficients
`AddCommGrpCat.{max (u + 1) v}`, the setting of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`.

Complexes of sheaves carry the zero morphisms of the preadditive structure of the abelian
category of sheaves, which is how the homotopy category and the derived category see them;
`Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange` is defined directly as the degreewise
base change map followed by `f'_*(q)`, in that spelling, and is stated for an arbitrary complex
shape. Its degree `n` component is `f'_*(q^n) ∘ β_{I^n}`
(`Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange_f`), with `β` the base change map of
`Stacks.EtaleCohomology.etaleAbelianBaseChange_unit`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6, p. 61][FreitagKiehl1988]
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/- As in `Stacks.EtaleCohomology.etaleAbelianHomotopyBaseChange`, the preadditive structure on
abelian sheaves is taken from the abelian structure. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

/- The zero morphisms of abelian sheaves are likewise taken from the preadditive structure, which
is how `HomotopyCategory.quotient` and the derived category spell the category of complexes; with
the zero morphisms of sheaves as a full subcategory of presheaves instead, the two categories of
complexes agree only after unfolding the sheaf category, which the kernel cannot afford. -/
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v


namespace CategoryTheory.NatTrans

/-- Composing, after a functor `Φ` on the homotopy category, the degreewise action of
`β : F ⟶ G ⋙ H` at `K` with `H` applied to `q : G(K) ⟶ L`. The instances are implicit
arguments so that they are read off the goal rather than synthesized. -/
private theorem map_quotient_map_mapHomologicalComplex_app_comp {ι V W U D : Type*}
    [Category* V] [Category* W] [Category* U] [Category* D] {_ : Preadditive V}
    {_ : Preadditive W} {_ : Preadditive U} {c : ComplexShape ι} {F : V ⥤ U} {G : V ⥤ W}
    {H : W ⥤ U} {_ : F.PreservesZeroMorphisms} {_ : G.PreservesZeroMorphisms}
    {_ : H.PreservesZeroMorphisms} (β : F ⟶ G ⋙ H) (K : HomologicalComplex V c)
    {L : HomologicalComplex W c} (q : (G.mapHomologicalComplex c).obj K ⟶ L)
    (Φ : HomotopyCategory U c ⥤ D) {T : D}
    (t : Φ.obj ((HomotopyCategory.quotient U c).obj ((H.mapHomologicalComplex c).obj L)) ⟶ T) :
    Φ.map ((HomotopyCategory.quotient U c).map ((NatTrans.mapHomologicalComplex β c).app K)) ≫
        Φ.map ((HomotopyCategory.quotient U c).map ((H.mapHomologicalComplex c).map q)) ≫ t =
      Φ.map ((HomotopyCategory.quotient U c).map
        ((NatTrans.mapHomologicalComplex β c).app K ≫ (H.mapHomologicalComplex c).map q)) ≫ t := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc]

end CategoryTheory.NatTrans


namespace Stacks.EtaleCohomology

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The base change morphism relative to a choice of resolutions.** For a complex `I` of abelian
sheaves on `X` and a morphism of complexes `q : g'^* I ⟶ J`, the morphism of complexes
`γ = f'_*(q) ∘ β_I : g^* f_* I ⟶ f'_* g'^* I ⟶ f'_* J` on `Y'`, where `β_I` is the base change
map applied degreewise. -/
@[weil "def_fk106_derived_base_change_morphism"]
def etaleAbelianResolutionBaseChange {ι : Type*} {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J : HomologicalComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I ⟶ J) :
    ((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
        c).obj I ⟶ ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex c).obj J :=
  (NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h) c).app I ≫
    ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex c).map q

/-- In degree `n`, the base change morphism relative to `q` is `f'_*(q^n) ∘ β_{I^n}`. -/
@[simp]
theorem etaleAbelianResolutionBaseChange_f {ι : Type*} {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J : HomologicalComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I ⟶ J) (n : ι) :
    (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I q).f n =
      (etaleAbelianBaseChange.{u, v} f g g' f' h).app (I.X n) ≫
        (etaleAbelianDirectImage.{u, v} f').map (q.f n) := by
  simp [etaleAbelianResolutionBaseChange]

/-- **The base change map against the base change morphism of complexes.** For a complex `I` of
abelian sheaves on `X` and any morphism of complexes `q : g'^* I ⟶ J`, the base change map at `I`,
read from `Q(g^* f_* I)` through the derived-functor unit of `Rf_*` and continued by
`Rf'_*(Q(q))`, is `Q(γ)` followed by the derived-functor unit of `Rf'_*` at `J`, where
`γ = etaleAbelianResolutionBaseChange f g g' f' h I q`. No hypothesis on `I`, `J` or `q` is
needed. -/
theorem etaleAbelianDerivedBaseChange_comp_map_eq
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ))
    {J : HomologicalComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
      (ComplexShape.up ℤ)}
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      J) :
    (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
        (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (etaleAbelianDerivedInverseImage.{u, v} g).map
        ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (etaleAbelianDerivedDirectImage.{u, v} f').map
        ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I q)) ≫
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) := by
  have hfac := etaleAbelianDerivedBaseChange_fac.{u, v} f g g' f' h
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  rw [Functor.map_comp, reassoc_of% hfac, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat : (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
        (((etaleAbelianInverseImage.{u, v} g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
      (etaleAbelianDerivedDirectImage.{u, v} f').map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map q)) ≫
        (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) :=
    ((etaleAbelianDerivedDirectImageUnit.{u, v} f').naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)).symm
  rw [hnat, etaleAbelianHomotopyBaseChange_app_quotient_obj]
  exact NatTrans.map_quotient_map_mapHomologicalComplex_app_comp _ _ _ _ _

attribute [local instance] Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso

/-- Cancelling an isomorphism and an invertible morphism. -/
private theorem hom_comp_inv_comp_inv_comp {D : Type*} [Category* D] {p p' r t : D} (e : p ≅ p')
    (b : p' ⟶ r) [IsIso b] (x : p ⟶ t) : (e.hom ≫ b) ≫ inv b ≫ e.inv ≫ x = x := by
  simp

/-- The diagram chase behind `etaleAbelianDerivedBaseChange_app_eq`, in an arbitrary category. -/
private theorem diagram_chase {D : Type*} [Category* D] {a₀ a₁ a₂ a₃ b₂ b₃ b₄ c₀ : D}
    (i : a₀ ⟶ a₁) (j : a₁ ⟶ a₂) (n₁ : a₂ ⟶ a₃) (s : a₃ ⟶ b₃) (t : a₂ ⟶ b₂) (n₂ : b₂ ⟶ b₃)
    (hnat : n₁ ≫ s = t ≫ n₂) (r : b₂ ⟶ b₄) (r' : b₄ ⟶ b₃) (hr : r ≫ r' = n₂) (γ : a₀ ⟶ c₀)
    (w : c₀ ⟶ b₄) (hC : i ≫ j ≫ t ≫ r = γ ≫ w) :
    (i ≫ j ≫ n₁) ≫ s = γ ≫ w ≫ r' := by
  rw [Category.assoc, Category.assoc, hnat, ← hr, ← reassoc_of% hC]

section Resolutions

variable {F I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (ComplexShape.up ℤ)}
  {J : HomologicalComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (ComplexShape.up ℤ)}
  (ι : F ⟶ I) [QuasiIso ι]
  (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)

/-- For a quasi-isomorphism `ι : F ⟶ I` into a K-injective complex, the identification
`Q(g^* f_* I) ≅ g^*(Rf_* F)`: the exactness comparison for `g^*`, then `g^*` of the
derived-functor unit of `Rf_*` at `I` (invertible since `I` is K-injective), then
`g^* Rf_*` of the inverse of `Q(ι)`. -/
def etaleAbelianResolutionBaseChangeSourceIso (hI : CochainComplex.IsKInjective I) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleAbelianDirectImage.{u, v} f ⋙
          etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≅
      (etaleAbelianDerivedInverseImage.{u, v} g).obj
        ((etaleAbelianDerivedDirectImage.{u, v} f).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F))) :=
  ((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.app
      (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (etaleAbelianDerivedInverseImage.{u, v} g).mapIso
      (@asIso _ _ _ _ ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
        (Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ I hI) ≪≫
      (etaleAbelianDerivedDirectImage.{u, v} f).mapIso
        (@asIso _ _ _ _ (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι))
          (Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso ι)).symm)

theorem etaleAbelianResolutionBaseChangeSourceIso_hom (hI : CochainComplex.IsKInjective I) :
    (etaleAbelianResolutionBaseChangeSourceIso.{u, v} f g ι hI).hom =
      (etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryFactorsh.inv.app
          (((etaleAbelianDirectImage.{u, v} f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≫
        (etaleAbelianDerivedInverseImage.{u, v} g).map
          ((etaleAbelianDerivedDirectImageUnit.{u, v} f).app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≫
            (etaleAbelianDerivedDirectImage.{u, v} f).map
              (inv (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι)))) :=
  rfl

/-- For quasi-isomorphisms `ι : F ⟶ I` and `q : g'^* I ⟶ J` with `J` K-injective, the
identification `Q(f'_* J) ≅ Rf'_*(g'^* F)`: the derived-functor unit of `Rf'_*` at `J`
(invertible since `J` is K-injective), then `Rf'_*` of the inverses of `Q(q)`, of the exactness
comparison for `g'^*` and of `g'^* Q(ι)`. -/
def etaleAbelianResolutionBaseChangeTargetIso [QuasiIso q] (hJ : CochainComplex.IsKInjective J) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) ≅
      (etaleAbelianDerivedDirectImage.{u, v} f').obj
        ((etaleAbelianDerivedInverseImage.{u, v} g').obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F))) :=
  @asIso _ _ _ _ ((etaleAbelianDerivedDirectImageUnit.{u, v} f').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J))
    (Stacks.Cohomology.UnboundedComplexes.isIso_app_of_isKInjective _ _ _ _ J hJ) ≪≫
  (etaleAbelianDerivedDirectImage.{u, v} f').mapIso
    ((@asIso _ _ _ _ (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))
      (Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso q)).symm ≪≫
    ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)).symm ≪≫
    (etaleAbelianDerivedInverseImage.{u, v} g').mapIso
      (@asIso _ _ _ _ (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι))
        (Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso ι)).symm)

theorem etaleAbelianResolutionBaseChangeTargetIso_hom [QuasiIso q]
    (hJ : CochainComplex.IsKInjective J) :
    (etaleAbelianResolutionBaseChangeTargetIso.{u, v} g' f' ι q hJ).hom =
      (etaleAbelianDerivedDirectImageUnit.{u, v} f').app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J) ≫
        (etaleAbelianDerivedDirectImage.{u, v} f').map
          (inv (DerivedCategory.Qh.map
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) ≫
            (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≫
            (etaleAbelianDerivedInverseImage.{u, v} g').map
              (inv (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι)))) :=
  rfl

/-- **The base change map is computed by any choice of resolutions.** Let `ι : F ⟶ I` and
`q : g'^* I ⟶ J` be quasi-isomorphisms with `I` and `J` K-injective. Then the base change map
`g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` at `F` is the image `Q(γ)` of the base change morphism of complexes
`γ = etaleAbelianResolutionBaseChange f g g' f' h I q : g^* f_* I ⟶ f'_* J`, read through the
identifications `Q(g^* f_* I) ≅ g^*(Rf_* F)` and `Q(f'_* J) ≅ Rf'_*(g'^* F)`. In particular `Q(γ)`
does not depend on the choice of resolutions. -/
@[weil "def_fk106_derived_base_change_morphism"]
theorem etaleAbelianDerivedBaseChange_app_eq [QuasiIso q] (hI : CochainComplex.IsKInjective I)
    (hJ : CochainComplex.IsKInjective J) :
    (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)) =
      (etaleAbelianResolutionBaseChangeSourceIso.{u, v} f g ι hI).inv ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I q)) ≫
        (etaleAbelianResolutionBaseChangeTargetIso.{u, v} g' f' ι q hJ).hom := by
  have hnat := (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).naturality
    (inv (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι)))
  have hr : (etaleAbelianDerivedDirectImage.{u, v} f').map
        ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.hom.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) ≫
      (etaleAbelianDerivedDirectImage.{u, v} f').map
          (inv (DerivedCategory.Qh.map
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) ≫
            (etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.inv.app
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≫
            (etaleAbelianDerivedInverseImage.{u, v} g').map
              (inv (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι)))) =
      (etaleAbelianDerivedDirectImage.{u, v} f').map
        ((etaleAbelianDerivedInverseImage.{u, v} g').map
          (inv (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ι)))) := by
    rw [← Functor.map_comp]
    congr 1
    exact @hom_comp_inv_comp_inv_comp _ _ _ _ _ _
      ((etaleAbelianInverseImage.{u, v} g').mapDerivedCategoryFactorsh.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))
      (Stacks.Homology.isIso_Qh_map_quotient_map_of_quasiIso q) _
  rw [Iso.eq_inv_comp, etaleAbelianResolutionBaseChangeSourceIso_hom,
    etaleAbelianResolutionBaseChangeTargetIso_hom, Functor.map_comp]
  exact diagram_chase _ _ _ _ _ _ hnat _ _ hr _ _
    (etaleAbelianDerivedBaseChange_comp_map_eq.{u, v} f g g' f' h I q)

/-- **The base change map is computed by injective resolutions.** The case of
`etaleAbelianDerivedBaseChange_app_eq` in which `I` and `J` are bounded below complexes of
injective sheaves. -/
theorem etaleAbelianDerivedBaseChange_app_eq_of_injective [QuasiIso q] (a b : ℤ)
    [CochainComplex.IsStrictlyGE I a] [∀ n, Injective (I.X n)]
    [CochainComplex.IsStrictlyGE J b] [∀ n, Injective (J.X n)] :
    (etaleAbelianDerivedBaseChange.{u, v} f g g' f' h).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)) =
      (etaleAbelianResolutionBaseChangeSourceIso.{u, v} f g ι
          (CochainComplex.isKInjective_of_injective I a)).inv ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I q)) ≫
        (etaleAbelianResolutionBaseChangeTargetIso.{u, v} g' f' ι q
          (CochainComplex.isKInjective_of_injective J b)).hom :=
  etaleAbelianDerivedBaseChange_app_eq.{u, v} f g g' f' h ι q _ _

end Resolutions

end Stacks.EtaleCohomology

end
