module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import Weil.Attr

/-!
# Base change morphisms of resolutions along a composite of base changes

Consider a tower of two commutative squares of schemes
```
W <--j-- Z
|i       |k
X <--h-- Y
|f       |e
S <--g-- T
```
with `a = i ≫ f` and `b = k ≫ e` the composites along the two sides of the outer rectangle.
Let `I` be a complex of abelian sheaves on the small étale site of `T`, `q₁ : e^* I ⟶ J₁` a
morphism of complexes on `Y` and `q₂ : k^* J₁ ⟶ J₂` a morphism of complexes on `Z`. The base
change morphism of complexes attached to the outer rectangle and to the composite
`b^* I ≅ k^* e^* I ⟶ k^* J₁ ⟶ J₂` is `i^*` of the base change morphism of the lower square
relative to `q₁`, followed by the base change morphism of the upper square relative to `q₂`,
read through the identification `a^* ≅ f^* ⋙ i^*`.

When `(ι, q₁)` is a choice of resolutions of a bounded below complex for the lower square and
`q₂` a quasi-isomorphism into a bounded below complex of injective sheaves, this is the
compatibility of the base change morphism relative to a choice of resolutions with composition
of base changes.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange_comp` — the base change morphism of
  complexes of the outer rectangle is the composite of those of the two squares.

## Implementation notes

The identity holds for arbitrary morphisms of complexes `q₁`, `q₂` over an arbitrary complex
shape, and for squares that are merely commutative; no resolution hypothesis is used. Its degree
zero case, for single sheaves, is
`Stacks.EtaleCohomology.etaleAbelianBaseChange_comp_app`.

In the notation of [FreitagKiehl1988], with `f : X → S` the morphism pushed forward and
`T₂ → T₁ → S` the two base changes, the morphisms here are named: `g` for `f`, `f` for the base
change `T₁ → S`, `i` for `T₂ → T₁`, `e` for `g'₁`, `h` for `f'₁`, `k` for `h'` and `j` for `f'₂`;
the composites `a = i ≫ f` and `b = k ≫ e` are carried as named morphisms with their defining
equations, and the identifications `(gh)^* ≅ h^* g^*` and `(g'₁h')^* ≅ h'^* g'₁^*` are
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'`. The quasi-isomorphism hypotheses on the
resolutions are not needed for the identity.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

/- As in `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`, the preadditive structure
and the zero morphisms of abelian sheaves are taken from the abelian structure. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v

namespace Stacks.EtaleCohomology

variable {S T W X Y Z : Scheme.{u}}

/-- The pasting identity behind `etaleAbelianResolutionBaseChange_comp`, for arbitrary functors
between categories with zero morphisms: if the transformation `β` attached to an outer rectangle
is, objectwise, `cA` followed by `I(β₁)`, `β₂` and `J(cB⁻¹)`, then the same holds degreewise for
the morphisms of complexes they induce, continued by `q₁` and `q₂`. Working with arbitrary functors
keeps every definitional unfolding at the level of `Functor.mapHomologicalComplex`. -/
private theorem mapHomologicalComplex_pasting {Ct Cs Cx Cy Cw Cz : Type*} [Category* Ct]
    [Category* Cs] [Category* Cx] [Category* Cy] [Category* Cw] [Category* Cz]
    [HasZeroMorphisms Ct] [HasZeroMorphisms Cs] [HasZeroMorphisms Cx] [HasZeroMorphisms Cy]
    [HasZeroMorphisms Cw] [HasZeroMorphisms Cz]
    (G : Ct ⥤ Cs) (F : Cs ⥤ Cx) (H : Cy ⥤ Cx) (E : Ct ⥤ Cy) (Ii : Cx ⥤ Cw) (Jd : Cz ⥤ Cw)
    (K : Cy ⥤ Cz) (A : Cs ⥤ Cw) (B : Ct ⥤ Cz)
    [G.PreservesZeroMorphisms] [F.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    [E.PreservesZeroMorphisms] [Ii.PreservesZeroMorphisms] [Jd.PreservesZeroMorphisms]
    [K.PreservesZeroMorphisms] [A.PreservesZeroMorphisms] [B.PreservesZeroMorphisms]
    (β₁ : G ⋙ F ⟶ E ⋙ H) (β₂ : H ⋙ Ii ⟶ K ⋙ Jd) (β : G ⋙ A ⟶ B ⋙ Jd)
    (cA : A ≅ F ⋙ Ii) (cB : B ≅ E ⋙ K)
    (hcomp : ∀ X, β.app X = cA.hom.app (G.obj X) ≫ Ii.map (β₁.app X) ≫ β₂.app (E.obj X) ≫
      Jd.map (cB.inv.app X))
    {ι : Type*} {c : ComplexShape ι} (I : HomologicalComplex Ct c) {J₁ : HomologicalComplex Cy c}
    {J₂ : HomologicalComplex Cz c} (q₁ : (E.mapHomologicalComplex c).obj I ⟶ J₁)
    (q₂ : (K.mapHomologicalComplex c).obj J₁ ⟶ J₂) :
    (NatTrans.mapHomologicalComplex β c).app I ≫
        (Jd.mapHomologicalComplex c).map
          ((NatIso.mapHomologicalComplex cB c).hom.app I ≫ (K.mapHomologicalComplex c).map q₁ ≫
            q₂) =
      (NatIso.mapHomologicalComplex cA c).hom.app ((G.mapHomologicalComplex c).obj I) ≫
        (Ii.mapHomologicalComplex c).map
          ((NatTrans.mapHomologicalComplex β₁ c).app I ≫ (H.mapHomologicalComplex c).map q₁) ≫
        (NatTrans.mapHomologicalComplex β₂ c).app J₁ ≫ (Jd.mapHomologicalComplex c).map q₂ := by
  ext n : 1
  have hnat := β₂.naturality (q₁.f n)
  simp only [Functor.comp_map] at hnat
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_obj_X, hcomp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, ← Jd.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- **The base change morphisms of resolutions compose along a tower of squares.** For squares
`e ≫ g = h ≫ f` and `k ≫ h = j ≫ i` of schemes, with `a = i ≫ f` and `b = k ≫ e`, a complex
`I` on `T` and morphisms of complexes `q₁ : e^* I ⟶ J₁`, `q₂ : k^* J₁ ⟶ J₂`, the base change
morphism of the outer rectangle relative to `b^* I ≅ k^* e^* I ⟶ k^* J₁ ⟶ J₂` is the identification
`a^* ≅ f^* ⋙ i^*` at `g_* I`, then `i^*` of the base change morphism of the lower square relative
to `q₁`, then the base change morphism of the upper square relative to `q₂`. -/
@[weil "lem_fk106_base_change_compatible_composition_base_change"]
theorem etaleAbelianResolutionBaseChange_comp (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
    (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i)
    (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T) (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)
    {ι : Type*} {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J₁ : HomologicalComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    {J₂ : HomologicalComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q₁ : ((etaleAbelianInverseImage.{u, v} e).mapHomologicalComplex c).obj I ⟶ J₁)
    (q₂ : ((etaleAbelianInverseImage.{u, v} k).mapHomologicalComplex c).obj J₁ ⟶ J₂) :
    etaleAbelianResolutionBaseChange.{u, v} g a b j hyp I
        ((NatIso.mapHomologicalComplex (etaleAbelianInverseImageCompIso'.{u, v} k e b hb)
            c).hom.app I ≫
          ((etaleAbelianInverseImage.{u, v} k).mapHomologicalComplex c).map q₁ ≫ q₂) =
      (NatIso.mapHomologicalComplex (etaleAbelianInverseImageCompIso'.{u, v} i f a ha)
          c).hom.app (((etaleAbelianDirectImage.{u, v} g).mapHomologicalComplex c).obj I) ≫
        ((etaleAbelianInverseImage.{u, v} i).mapHomologicalComplex c).map
          (etaleAbelianResolutionBaseChange.{u, v} g f e h sq₁ I q₁) ≫
        etaleAbelianResolutionBaseChange.{u, v} h i k j sq₂ J₁ q₂ := by
  exact mapHomologicalComplex_pasting (etaleAbelianDirectImage.{u, v} g)
    (etaleAbelianInverseImage.{u, v} f) (etaleAbelianDirectImage.{u, v} h)
    (etaleAbelianInverseImage.{u, v} e) (etaleAbelianInverseImage.{u, v} i)
    (etaleAbelianDirectImage.{u, v} j) (etaleAbelianInverseImage.{u, v} k)
    (etaleAbelianInverseImage.{u, v} a) (etaleAbelianInverseImage.{u, v} b)
    (etaleAbelianBaseChange.{u, v} g f e h sq₁) (etaleAbelianBaseChange.{u, v} h i k j sq₂)
    (etaleAbelianBaseChange.{u, v} g a b j hyp) (etaleAbelianInverseImageCompIso'.{u, v} i f a ha)
    (etaleAbelianInverseImageCompIso'.{u, v} k e b hb)
    (etaleAbelianBaseChange_comp_app.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp) I q₁ q₂

end Stacks.EtaleCohomology

end
