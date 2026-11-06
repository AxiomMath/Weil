module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismUnderivedBaseChange
public import Weil.Attr

/-!
# The base change morphism of a composite, on resolutions

Let `X --f₂--> X' --f₁--> S` with composite `f = f₂ ≫ f₁`, and let `g : T ⟶ S`. Let
```
X_T --g'--> X
 |f₂'       |f₂
 v          v
X'_T --g₁'--> X'
 |f₁'       |f₁
 v          v
 T  ---g--> S
```
be two commutative squares, so that the outer rectangle, with `f' = f₂' ≫ f₁'`, is a commutative
square for `f` and `g`. For a complex `I` of abelian sheaves on `X` and morphisms of complexes
`q : g'^* I ⟶ J` and `q₁ : g₁'^* f₂_* I ⟶ J₁`, let `γ`, `γ₁`, `γ₂` be the base change morphisms
relative to these choices for the outer rectangle, the lower square (at the complex `f₂_* I`) and
the upper square. If `w : J₁ ⟶ f₂'_* J` is a morphism of complexes with `w ∘ q₁ ≃ γ₂`, then,
under the identifications `f_* ≅ f₁_* f₂_*` and `f'_* ≅ f₁'_* f₂'_*`,
$$ γ ≃ f₁'_*(w) ∘ γ₁ . $$
That is, the base change morphism for `f₁ f₂` is the composite of the one for `f₁` and the
direct image under `f₁'_*` of the one for `f₂`.

The proof is the identity in degree zero,
`Stacks.EtaleCohomology.etaleAbelianBaseChange_compDirectImage_app`, applied in each degree,
which gives `γ = f₁'_*(γ₂) ∘ β₁` on the nose; the homotopy `w ∘ q₁ ≃ γ₂` is then carried along
by the additive functor `f₁'_*`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange_comp_eq` — the identity
  `γ = f₁'_*(γ₂) ∘ β₁` of morphisms of complexes.
* `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange_comp_homotopic` — the homotopy
  `γ ≃ f₁'_*(w) ∘ γ₁`.

## Implementation notes

Sheaves are abelian sheaves on Mathlib's small étale site `X.smallEtaleTopology` with
coefficients `AddCommGrpCat.{max (u + 1) v}`, the setting of
`Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`. The identity holds for arbitrary
complexes and morphisms `q`, `q₁`, `w`: injectivity of the terms, boundedness below and the
quasi-isomorphism conditions of the source are what make `γ`, `γ₁` represent the derived base
change maps, and are not needed for the identity itself; the existence of a `w` with
`w ∘ q₁ ≃ γ₂` when `q₁` is a quasi-isomorphism and `J` is a bounded below complex of injectives
is `CochainComplex.IsKInjective.Qh_map_bijective`. The derived form of the statement is
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_compDirectImage_app`.

The degreewise argument is carried out for arbitrary functors and natural transformations
between the sheaf categories and then specialized, so that no step has to compare two
composites of the concrete sheaf functors by unfolding them. For the same reason the additivity
of `f₁'_*` used to transport the homotopy is taken for the preadditive structure coming from the
abelian structure of sheaves, the one the complexes here carry.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
* [Stacks Project, Tag 0A4D](https://stacks.math.columbia.edu/tag/0A4D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe w u v

namespace Stacks.EtaleCohomology

variable {X X' S T X'T XT : Scheme.{u}}
  {P₂ : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {P₁ : Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {P : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {G : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {G₁ : Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf X'T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf XT.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {P₂' : Sheaf XT.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf X'T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {P₁' : Sheaf X'T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {P' : Sheaf XT.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  [P₂.PreservesZeroMorphisms] [P₁.PreservesZeroMorphisms] [P.PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [G₁.PreservesZeroMorphisms] [G'.PreservesZeroMorphisms]
  [P₂'.PreservesZeroMorphisms] [P₁'.PreservesZeroMorphisms] [P'.PreservesZeroMorphisms]
  (e : P₂ ⋙ P₁ ≅ P) (e' : P₂' ⋙ P₁' ≅ P')
  (β : P ⋙ G ⟶ G' ⋙ P') (β₁ : P₁ ⋙ G ⟶ G₁ ⋙ P₁') (β₂ : P₂ ⋙ G₁ ⟶ G' ⋙ P₂')
  (hβ : ∀ F, β.app F = G.map (e.inv.app F) ≫ β₁.app (P₂.obj F) ≫ P₁'.map (β₂.app F) ≫
    e'.hom.app (G'.obj F))

include hβ

/-- The formal identity behind
`Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange_comp_eq`: if a transformation `β`
decomposes objectwise through `β₁` and `β₂`, then, on complexes, `β` followed by `P'(q)` is
`β₁` followed by `P₁'` of `β₂` followed by `P₂'(q)`, read through `e` and `e'`. -/
private theorem mapHomologicalComplex_app_comp_map_eq_of_app_eq {ι : Type w}
    {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J : HomologicalComplex (Sheaf XT.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q : (G'.mapHomologicalComplex c).obj I ⟶ J) :
    ((NatTrans.mapHomologicalComplex β c).app I ≫ (P'.mapHomologicalComplex c).map q) ≫
        (NatTrans.mapHomologicalComplex e'.inv c).app J =
      (NatTrans.mapHomologicalComplex (Functor.whiskerRight e.inv G) c).app I ≫
        (NatTrans.mapHomologicalComplex β₁ c).app ((P₂.mapHomologicalComplex c).obj I) ≫
        (P₁'.mapHomologicalComplex c).map
          ((NatTrans.mapHomologicalComplex β₂ c).app I ≫
            (P₂'.mapHomologicalComplex c).map q) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc, hβ]
  rw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id, Functor.comp_map]
  rfl

/-- The homotopy form of `mapHomologicalComplex_app_comp_map_eq_of_app_eq`: given a homotopy
`q₁ ≫ w ≃ β₂ ≫ P₂'(q)`, the composite `β ≫ P'(q)` read through `e'` is homotopic to
`β₁ ≫ P₁'(q₁) ≫ P₁'(w)` read through `e`. -/
private def mapHomologicalComplexAppCompMapHomotopy (hA : P₁'.Additive) {ι : Type w}
    {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J : HomologicalComplex (Sheaf XT.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q : (G'.mapHomologicalComplex c).obj I ⟶ J)
    {J₁ : HomologicalComplex (Sheaf X'T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q₁ : (G₁.mapHomologicalComplex c).obj ((P₂.mapHomologicalComplex c).obj I) ⟶ J₁)
    (w : J₁ ⟶ (P₂'.mapHomologicalComplex c).obj J)
    (H : Homotopy (q₁ ≫ w)
      ((NatTrans.mapHomologicalComplex β₂ c).app I ≫ (P₂'.mapHomologicalComplex c).map q)) :
    Homotopy
      (((NatTrans.mapHomologicalComplex β c).app I ≫ (P'.mapHomologicalComplex c).map q) ≫
        (NatTrans.mapHomologicalComplex e'.inv c).app J)
      ((NatTrans.mapHomologicalComplex (Functor.whiskerRight e.inv G) c).app I ≫
        ((NatTrans.mapHomologicalComplex β₁ c).app ((P₂.mapHomologicalComplex c).obj I) ≫
          (P₁'.mapHomologicalComplex c).map q₁) ≫
        (P₁'.mapHomologicalComplex c).map w) := by
  refine (Homotopy.ofEq
    (mapHomologicalComplex_app_comp_map_eq_of_app_eq.{w, u, v} e e' β β₁ β₂ hβ I q)).trans
      (Homotopy.compLeft ?_ _)
  haveI := hA
  refine (Homotopy.compLeft (P₁'.mapHomotopy H).symm _).trans (Homotopy.ofEq ?_)
  rw [Functor.map_comp, Category.assoc]

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

variable {X X' S T X'T XT : Scheme.{u}}
  (f₂ : X ⟶ X') (f₁ : X' ⟶ S) (f : X ⟶ S) (hf : f = f₂ ≫ f₁) (g : T ⟶ S)
  (g₁' : X'T ⟶ X') (f₁' : X'T ⟶ T) (h₁ : g₁' ≫ f₁ = f₁' ≫ g)
  (g' : XT ⟶ X) (f₂' : XT ⟶ X'T) (h₂ : g' ≫ f₂ = f₂' ≫ g₁')
  (f' : XT ⟶ T) (hf' : f' = f₂' ≫ f₁') (h : g' ≫ f = f' ≫ g)

/-- Direct image of abelian étale sheaves is additive for the preadditive structure of the
abelian category of sheaves: it is a right adjoint, so it preserves binary products and zero
morphisms. -/
private theorem additive_etaleAbelianDirectImage_of_abelian {Y Z : Scheme.{u}} (p : Y ⟶ Z) :
    (etaleAbelianDirectImage.{u, v} p).Additive := by
  have : (etaleAbelianDirectImage.{u, v} p).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, v} p).isRightAdjoint
  have := Functor.preservesZeroMorphisms_of_isRightAdjoint (etaleAbelianDirectImage.{u, v} p)
  exact Functor.additive_of_preserves_binary_products (etaleAbelianDirectImage.{u, v} p)

/-- **The base change morphism of a composite, on the nose.** For a complex `I` on `X` and a
morphism of complexes `q : g'^* I ⟶ J`, the base change morphism `γ` of the outer rectangle,
read through `f'_* ≅ f₁'_* f₂'_*`, is the identification `g^* f_* ≅ g^* f₁_* f₂_*`, followed by
the degreewise base change map `β₁` of the lower square at `f₂_* I` and by `f₁'_*` of the base
change morphism `γ₂` of the upper square. -/
theorem etaleAbelianResolutionBaseChange_comp_eq {ι : Type w} {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J : HomologicalComplex (Sheaf XT.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I ⟶ J) :
    etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I q ≫
        (NatTrans.mapHomologicalComplex
          (etaleAbelianDirectImageCompIso'.{u, v} f₂' f₁' f' hf').inv c).app J =
      (NatTrans.mapHomologicalComplex
          (Functor.whiskerRight (etaleAbelianDirectImageCompIso'.{u, v} f₂ f₁ f hf).inv
            (etaleAbelianInverseImage.{u, v} g)) c).app I ≫
        (NatTrans.mapHomologicalComplex
          (etaleAbelianBaseChange.{u, v} f₁ g g₁' f₁' h₁) c).app
            (((etaleAbelianDirectImage.{u, v} f₂).mapHomologicalComplex c).obj I) ≫
        ((etaleAbelianDirectImage.{u, v} f₁').mapHomologicalComplex c).map
          (etaleAbelianResolutionBaseChange.{u, v} f₂ g₁' g' f₂' h₂ I q) :=
  mapHomologicalComplex_app_comp_map_eq_of_app_eq
    (etaleAbelianDirectImageCompIso'.{u, v} f₂ f₁ f hf)
    (etaleAbelianDirectImageCompIso'.{u, v} f₂' f₁' f' hf')
    (etaleAbelianBaseChange.{u, v} f g g' f' h) (etaleAbelianBaseChange.{u, v} f₁ g g₁' f₁' h₁)
    (etaleAbelianBaseChange.{u, v} f₂ g₁' g' f₂' h₂)
    (etaleAbelianBaseChange_compDirectImage_app.{u, v} f₂ f₁ f hf g g₁' f₁' g' f₂' f' hf'
      h₁ h₂ h) I q

/-- **The base change morphism of a composite is the composite of the base change morphisms**
(up to homotopy). Let `q : g'^* I ⟶ J` and `q₁ : g₁'^* f₂_* I ⟶ J₁` be morphisms of complexes and
`w : J₁ ⟶ f₂'_* J` a morphism of complexes with `w ∘ q₁ ≃ γ₂`, where `γ₂` is the base change
morphism of the upper square relative to `q`. Then the base change morphism `γ` of the outer
rectangle relative to `q`, read through the identifications `f_* ≅ f₁_* f₂_*` and
`f'_* ≅ f₁'_* f₂'_*`, is homotopic to `f₁'_*(w) ∘ γ₁`, where `γ₁` is the base change morphism of
the lower square at the complex `f₂_* I` relative to `q₁`. -/
@[weil "lem_fk106_base_change_compatible_composition_structure"]
theorem etaleAbelianResolutionBaseChange_comp_homotopic {ι : Type w} {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J : HomologicalComplex (Sheaf XT.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q : ((etaleAbelianInverseImage.{u, v} g').mapHomologicalComplex c).obj I ⟶ J)
    {J₁ : HomologicalComplex (Sheaf X'T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q₁ : ((etaleAbelianInverseImage.{u, v} g₁').mapHomologicalComplex c).obj
      (((etaleAbelianDirectImage.{u, v} f₂).mapHomologicalComplex c).obj I) ⟶ J₁)
    (w : J₁ ⟶ ((etaleAbelianDirectImage.{u, v} f₂').mapHomologicalComplex c).obj J)
    (H : Homotopy (q₁ ≫ w)
      (etaleAbelianResolutionBaseChange.{u, v} f₂ g₁' g' f₂' h₂ I q)) :
    Nonempty (Homotopy
      (etaleAbelianResolutionBaseChange.{u, v} f g g' f' h I q ≫
        (NatTrans.mapHomologicalComplex
          (etaleAbelianDirectImageCompIso'.{u, v} f₂' f₁' f' hf').inv c).app J)
      ((NatTrans.mapHomologicalComplex
          (Functor.whiskerRight (etaleAbelianDirectImageCompIso'.{u, v} f₂ f₁ f hf).inv
            (etaleAbelianInverseImage.{u, v} g)) c).app I ≫
        etaleAbelianResolutionBaseChange.{u, v} f₁ g g₁' f₁' h₁
          (((etaleAbelianDirectImage.{u, v} f₂).mapHomologicalComplex c).obj I) q₁ ≫
        ((etaleAbelianDirectImage.{u, v} f₁').mapHomologicalComplex c).map w)) :=
  ⟨mapHomologicalComplexAppCompMapHomotopy.{w, u, v}
    (etaleAbelianDirectImageCompIso'.{u, v} f₂ f₁ f hf)
    (etaleAbelianDirectImageCompIso'.{u, v} f₂' f₁' f' hf')
    (etaleAbelianBaseChange.{u, v} f g g' f' h) (etaleAbelianBaseChange.{u, v} f₁ g g₁' f₁' h₁)
    (etaleAbelianBaseChange.{u, v} f₂ g₁' g' f₂' h₂)
    (etaleAbelianBaseChange_compDirectImage_app.{u, v} f₂ f₁ f hf g g₁' f₁' g' f₂' f' hf'
      h₁ h₂ h) (additive_etaleAbelianDirectImage_of_abelian.{u, v} f₁') I q q₁ w H⟩

end Stacks.EtaleCohomology

end
