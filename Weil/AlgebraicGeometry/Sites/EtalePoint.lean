/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Weil.Attr

/-!
# Stalks of the sheafification on the small étale site

Let `S` be a scheme and `s : Spec Ω ⟶ S` a geometric point, `Ω` a separably closed field.
For every presheaf `F` on the small étale site of `S` (of sets, of abelian groups, or more
generally with values in a concrete category with products, colimits and sheafification), the map
`F_s ⟶ (F^♯)_s` induced on stalks by the sheafification morphism `F ⟶ F^♯` is bijective.

## Main results

* `AlgebraicGeometry.Scheme.bijective_pointSmallEtale_presheafFiber_map_toSheafify`: the
  stalk map of `toSheafify` at a geometric point is bijective.
* `AlgebraicGeometry.Scheme.bijective_pointSmallEtale_presheafFiber_map_toSheafify_type` and
  `AlgebraicGeometry.Scheme.bijective_pointSmallEtale_presheafFiber_map_toSheafify_addCommGrp`:
  the cases of presheaves of sets and of abelian groups.

## Implementation notes

The stalk at `s` is `(pointSmallEtale s).presheafFiber`, the colimit of `F` over the category
of étale neighbourhoods of `s`. The result is the specialisation to this point of the general
fact that the fiber functor at a point of a site inverts the morphisms `J.W`, among which is
`toSheafify J F` for any choice of sheafification; this is independent of the construction of
the sheafification, in particular it covers the plus construction applied twice.
Geometric points are taken over separably closed fields, which contains the algebraically
closed case.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- The map on stalks at a geometric point induced by the sheafification morphism of a
presheaf on the small étale site is bijective. -/
@[weil "lem_fk102_sheafification_stalks"]
theorem bijective_pointSmallEtale_presheafFiber_map_toSheafify
    {A : Type*} [Category A] [HasProducts.{u} A] [HasColimitsOfSize.{u, u} A]
    {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [HasWeakSheafify (smallEtaleTopology S) A] (F : S.Etaleᵒᵖ ⥤ A) :
    Function.Bijective
      (ConcreteCategory.hom ((pointSmallEtale s).presheafFiber.map
        (toSheafify (smallEtaleTopology S) F))) :=
  ConcreteCategory.bijective_of_isIso _

/-- The stalk map of the sheafification of a presheaf of sets is bijective. -/
theorem bijective_pointSmallEtale_presheafFiber_map_toSheafify_type
    (F : S.Etaleᵒᵖ ⥤ Type u) :
    Function.Bijective
      ((pointSmallEtale s).presheafFiber.map (toSheafify (smallEtaleTopology S) F)) :=
  (isIso_iff_bijective _).1 inferInstance

/-- The stalk map of the sheafification of a presheaf of abelian groups is bijective. -/
theorem bijective_pointSmallEtale_presheafFiber_map_toSheafify_addCommGrp
    (F : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Function.Bijective
      ((pointSmallEtale s).presheafFiber.map (toSheafify (smallEtaleTopology S) F)) :=
  bijective_pointSmallEtale_presheafFiber_map_toSheafify s F

end AlgebraicGeometry.Scheme

end

/-! ### Germs of étale sections agree iff the sections agree near the point -/

/-!
# Germs of étale sections agree iff the sections agree near the point

Let `F` be a sheaf on the small étale site of a scheme `X`, with values in a concrete category
whose forgetful functor preserves filtered colimits (sets, abelian groups, modules, ...). Let
`U ⟶ X` be étale, `α β ∈ F(U)` and `ū : Spec Ω ⟶ U` a geometric point of `U` (with `Ω`
separably closed), viewed as a point of the fiber at the geometric point `ū ≫ (U ⟶ X)` of `X`.
Then the germs of `α` and `β` at `ū` agree if and only if `α` and `β` have the same restriction
to some Zariski open neighbourhood `W ⊆ U` of the image point of `ū`.

The "if" direction holds because `ū` factors through the open subscheme `W`. For "only if",
equality of germs gives an étale neighbourhood `h : V ⟶ U` of `ū` on which `α` and `β` agree;
its image `W` is open (étale morphisms are open maps), `h` factors through a surjective étale
map `V ⟶ W`, which is a covering of the small étale site, and the sheaf `F` is separated for it.

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.ofOpens`: an open subscheme of `U : X.Etale`, as an object of
  `X.Etale`.
* `AlgebraicGeometry.Scheme.Etale.ofOpensι`: its inclusion into `U`, a morphism of `X.Etale`.

## Main results

* `AlgebraicGeometry.Scheme.toPresheafFiber_eq_iff_exists_opens`: the germs of two sections at a
  geometric point agree iff the sections agree on a Zariski open neighbourhood of its image.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitagkiehl1988], I.3
-/

@[expose] public noncomputable section

universe w' v' u' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite

namespace AlgebraicGeometry.Scheme

namespace Etale

variable {X : Scheme.{u}}

/-- An open subscheme `W` of an object `U` of the small étale site of `X`, as an object of the
small étale site: the composite `W ⟶ U ⟶ X` is étale. -/
def ofOpens (U : X.Etale) (W : U.left.Opens) : X.Etale :=
  haveI : Etale U.hom := U.prop
  MorphismProperty.Over.mk ⊤ (W.ι ≫ U.hom) inferInstance

/-- The inclusion of an open subscheme `W ⊆ U` as a morphism `ofOpens U W ⟶ U` of the small
étale site. -/
def ofOpensι (U : X.Etale) (W : U.left.Opens) : ofOpens U W ⟶ U :=
  MorphismProperty.Over.homMk W.ι rfl trivial

@[simp]
lemma ofOpensι_left (U : X.Etale) (W : U.left.Opens) : (ofOpensι U W).left = W.ι := rfl

end Etale

variable {X : Scheme.{u}} {A : Type u'} [Category.{v'} A] {FC : A → A → Type*}
  {CC : A → Type w'} [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{w'} A FC]
  [HasColimitsOfSize.{u, u} A] [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- **Germs agree iff the sections agree near the point.** Let `F` be a sheaf on the small étale
site of `X`, `U : X.Etale`, `α β ∈ F(U)` and `ū` a geometric point of `U` lying over the
geometric point `x` of `X`. Then the germs of `α` and `β` at `ū` agree if and only if there is
a Zariski open `W ⊆ U` containing the image point of `ū` with `α|_W = β|_W`. -/
@[weil "lem_fk103_germs_equal_iff_equal_near_point"]
theorem toPresheafFiber_eq_iff_exists_opens
    [(smallEtaleTopology X).HasSheafCompose (CategoryTheory.forget A)]
    (F : Sheaf (smallEtaleTopology X) A) (U : X.Etale) (α β : ToType (F.obj.obj (op U)))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (ū : (pointSmallEtale x).fiber.obj U) :
    (pointSmallEtale x).toPresheafFiber U ū F.obj α =
        (pointSmallEtale x).toPresheafFiber U ū F.obj β ↔
      ∃ W : U.left.Opens, ū.left (default : Spec (.of Ω)) ∈ W ∧
        F.obj.map (Etale.ofOpensι U W).op α = F.obj.map (Etale.ofOpensι U W).op β := by
  rw [Point.toPresheafFiber_eq_iff']
  constructor
  · rintro ⟨V, f, y, hy, hf⟩
    have : Etale f.left := inferInstance
    have : Flat f.left := inferInstance
    have : LocallyOfFinitePresentation f.left := inferInstance
    have : UniversallyOpen f.left := UniversallyOpen.of_flat f.left
    let W : U.left.Opens := ⟨Set.range f.left, f.left.isOpenMap.isOpen_range⟩
    have hW : Set.range f.left ⊆ Set.range W.ι := by rw [Scheme.Opens.range_ι]; exact le_rfl
    let g : V.left ⟶ W.toScheme := IsOpenImmersion.lift W.ι f.left hW
    have hg : g ≫ W.ι = f.left := IsOpenImmersion.lift_fac _ _ _
    let gE : V ⟶ Etale.ofOpens U W := MorphismProperty.Over.homMk g (by
      change g ≫ W.ι ≫ U.hom = V.hom
      rw [← Category.assoc, hg]
      exact MorphismProperty.Over.w f) trivial
    have hgE : gE ≫ Etale.ofOpensι U W = f := by
      apply MorphismProperty.Over.Hom.ext
      exact hg
    refine ⟨W, ⟨y.left (default : Spec (.of Ω)), ?_⟩, ?_⟩
    · rw [← hy]
      rfl
    · have hcov : Sieve.ofArrows (fun _ : PUnit.{1} ↦ V) (fun _ ↦ gE) ∈
          smallEtaleTopology X (Etale.ofOpens U W) := by
        rw [ofArrows_mem_smallEtaleTopology_iff]
        refine Set.eq_univ_of_forall fun w ↦ ?_
        obtain ⟨v, hv⟩ := w.2
        refine Set.mem_iUnion.2 ⟨PUnit.unit, v, W.ι.isOpenEmbedding.injective ?_⟩
        change (gE.left ≫ W.ι) v = W.ι w
        change (g ≫ W.ι) v = W.ι w
        rw [hg, hv]
        rfl
      let G := F.obj ⋙ CategoryTheory.forget A
      have hG : Presieve.IsSheaf (smallEtaleTopology X) G :=
        (isSheaf_iff_isSheaf_of_type _ _).1
          ((sheafCompose _ (CategoryTheory.forget A)).obj F).property
      refine (hG _ hcov).isSeparatedFor.ext fun Z h hh ↦ ?_
      obtain ⟨_, e, _, ⟨_⟩, rfl⟩ := hh
      change G.map (e ≫ gE).op (G.map (Etale.ofOpensι U W).op α) =
        G.map (e ≫ gE).op (G.map (Etale.ofOpensι U W).op β)
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        Category.assoc, hgE, op_comp, Functor.map_comp_apply,
        Functor.map_comp_apply]
      exact congrArg _ hf
  · rintro ⟨W, hu, hW⟩
    have hsub : Set.range ū.left ⊆ Set.range W.ι := by
      rintro _ ⟨a, rfl⟩
      obtain rfl : a = (default : Spec (.of Ω)) := Subsingleton.elim (α := Spec (.of Ω)) _ _
      exact ⟨⟨_, hu⟩, rfl⟩
    let l : Spec (.of Ω) ⟶ W.toScheme := IsOpenImmersion.lift W.ι ū.left hsub
    have hl : l ≫ W.ι = ū.left := IsOpenImmersion.lift_fac _ _ _
    let y : (pointSmallEtale x).fiber.obj (Etale.ofOpens U W) := Over.homMk l (by
      change l ≫ W.ι ≫ U.hom = x
      rw [← Category.assoc, hl]
      exact Over.w ū)
    exact ⟨Etale.ofOpens U W, Etale.ofOpensι U W, y, Over.OverMorphism.ext hl, hW⟩

end AlgebraicGeometry.Scheme
