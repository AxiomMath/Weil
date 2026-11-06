module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# The inverse image along a composite

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes of a big étale site `B`. For a sheaf
`H` on the small étale site of `Z` (of sets, of abelian groups, or with values in any category
with the relevant colimits and sheafification) there is an isomorphism
`θ_H : f^* g^* H ≅ (g ∘ f)^* H`, natural in `H`, and for a third morphism `h : W ⟶ X` the two
isomorphisms `h^* f^* g^* H ≅ (g ∘ f ∘ h)^* H` built from `θ` agree.

The isomorphism comes from the adjunctions `f^* ⊣ f_*` and the identification
`(g ∘ f)_* ≅ g_* ∘ f_*` of direct images: two left adjoints of isomorphic functors are
isomorphic, by a unique isomorphism compatible with the adjunctions (the Yoneda lemma). The
direct image identification is precomposition with the canonical isomorphism of iterated fibre
products `X ×_Y (Y ×_Z V) ≅ X ×_Z V`, and the associativity of iterated fibre products gives
the cocycle condition for the direct images, hence for the inverse images.

## Main definitions

* `AlgebraicGeometry.smallEtaleDirectImageComp` — `g_* ∘ f_* ≅ (g ∘ f)_*`.
* `AlgebraicGeometry.smallEtaleInverseImageComp` — `θ : f^* ∘ g^* ≅ (g ∘ f)^*`.

## Main results

* `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_assoc` — the two identifications of
  `W ×_X (X ×_Y (Y ×_Z V))` with `W ×_Z V` agree.
* `AlgebraicGeometry.smallEtaleDirectImageComp_assoc` — the cocycle condition for the direct
  images.
* `AlgebraicGeometry.smallEtaleInverseImageComp_hom_naturality` — `θ_H` is natural in `H`.
* `AlgebraicGeometry.smallEtaleInverseImageComp_assoc` — the cocycle condition for `θ` along
  three composable morphisms.

## Implementation notes

The composites `g ∘ f`, `f ∘ h`, `g ∘ f ∘ h` are named, with hypotheses `f ≫ g = fg` and so on,
so that the cocycle condition is an equation between isomorphisms of the same two functors and
no transport along the associativity of composition appears in the statement. Base change along
a composite is `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso`. The statement is
proved for arbitrary morphisms of the big étale site; Freitag–Kiehl state it for noetherian
separated schemes.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03PZ](https://stacks.math.columbia.edu/tag/03PZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {W X Y Z : B.Scheme}

/-- The first projection `X ×_Y V ⟶ V` of a base change of étale schemes. -/
abbrev smallEtaleBaseChangePullbackFst (f : X ⟶ Y) (V : SmallEtale B Y.obj Y.property) :
    ((smallEtaleBaseChange B f).obj V).obj.left ⟶ V.obj.left :=
  pullback.fst V.obj.hom f

/-- A morphism into a base change `X ×_Y V` of étale `X`-schemes is determined by its first
component. This is StacksFrontier's `AlgebraicGeometry.smallEtaleBaseChange_hom_ext`, kept here
under its own name to avoid importing its constructible-sheaf module. -/
lemma smallEtaleBaseChange_hom_ext_fst (f : X ⟶ Y) {T : SmallEtale B X.obj X.property}
    {V : SmallEtale B Y.obj Y.property} {p q : T ⟶ (smallEtaleBaseChange B f).obj V}
    (hpq : p.hom.left ≫ smallEtaleBaseChangePullbackFst B f V =
      q.hom.left ≫ smallEtaleBaseChangePullbackFst B f V) :
    p = q := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.hom_ext hpq ?_))
  exact (Over.w p.hom).trans (Over.w q.hom).symm

/-- The first projection of a base change is natural. -/
@[reassoc (attr := simp)]
lemma smallEtaleBaseChange_map_hom_left_fst (f : X ⟶ Y) {V V' : SmallEtale B Y.obj Y.property}
    (e : V ⟶ V') :
    ((smallEtaleBaseChange B f).map e).hom.left ≫ smallEtaleBaseChangePullbackFst B f V' =
      smallEtaleBaseChangePullbackFst B f V ≫ e.hom.left :=
  pullback.lift_fst _ _ _

/-- The comparison `X ×_Y (Y ×_Z V) ≅ X ×_Z V` carries the first projection of `X ×_Z V` to
the composite of the first projections. -/
@[reassoc (attr := simp)]
lemma smallEtaleBaseChange_factoredCompIso_hom_app_left_pullbackFst (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : f ≫ g = fg) (V : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app V).hom.left ≫
        smallEtaleBaseChangePullbackFst B fg V =
      smallEtaleBaseChangePullbackFst B f ((smallEtaleBaseChange B g).obj V) ≫
        smallEtaleBaseChangePullbackFst B g V :=
  smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z f g fg hfg V

/-- **Associativity of base change along composites.** For `h : W ⟶ X`, `f : X ⟶ Y`,
`g : Y ⟶ Z`, the two identifications of `W ×_X (X ×_Y (Y ×_Z V))` with `W ×_Z V` agree. -/
lemma smallEtaleBaseChange_factoredCompIso_assoc (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (hf : W ⟶ Y) (hhf : h ≫ f = hf) (hfg' : W ⟶ Z)
    (h₁ : h ≫ fg = hfg') (h₂ : hf ≫ g = hfg') :
    Functor.isoWhiskerRight (smallEtaleBaseChange_factoredCompIso B _ _ _ f g fg hfg)
        (smallEtaleBaseChange B h) ≪≫
        smallEtaleBaseChange_factoredCompIso B _ _ _ h fg hfg' h₁ =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (smallEtaleBaseChange B g)
          (smallEtaleBaseChange_factoredCompIso B _ _ _ h f hf hhf) ≪≫
        smallEtaleBaseChange_factoredCompIso B _ _ _ hf g hfg' h₂ := by
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  apply smallEtaleBaseChange_hom_ext_fst
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc,
    smallEtaleBaseChange_factoredCompIso_hom_app_left_pullbackFst,
    smallEtaleBaseChange_map_hom_left_fst_assoc,
    smallEtaleBaseChange_factoredCompIso_hom_app_left_pullbackFst_assoc]
  rfl

variable (A : Type w) [Category.{v} A]

/-- The direct image `f_*` of sheaves on the small étale sites, `(f_* F)(V) = F(X ×_Y V)`. -/
abbrev smallEtaleDirectImage (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B X.obj X.property) A ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) A :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- **The direct image along a composite.** `g_* ∘ f_* ≅ (g ∘ f)_*`, by precomposition with
the canonical isomorphisms `X ×_Y (Y ×_Z V) ≅ X ×_Z V`. -/
def smallEtaleDirectImageComp (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
    smallEtaleDirectImage B A f ⋙ smallEtaleDirectImage B A g ≅ smallEtaleDirectImage B A fg :=
  Functor.sheafPushforwardContinuousComp'
    (smallEtaleBaseChange_factoredCompIso B _ _ _ f g fg hfg) A _ _ _

/-- The cocycle condition for the identifications of direct images along composites. -/
lemma smallEtaleDirectImageComp_assoc (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (hf : W ⟶ Y) (hhf : h ≫ f = hf) (hfg' : W ⟶ Z)
    (h₁ : h ≫ fg = hfg') (h₂ : hf ≫ g = hfg') :
    Functor.isoWhiskerLeft (smallEtaleDirectImage B A h)
        (smallEtaleDirectImageComp B A f g fg hfg) ≪≫
        smallEtaleDirectImageComp B A h fg hfg' h₁ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleDirectImageComp B A h f hf hhf)
          (smallEtaleDirectImage B A g) ≪≫
        smallEtaleDirectImageComp B A hf g hfg' h₂ := by
  have key := congrArg (fun e => NatTrans.app (Iso.inv e))
    (smallEtaleBaseChange_factoredCompIso_assoc B h f g fg hfg hf hhf hfg' h₁ h₂)
  refine Iso.ext (NatTrans.ext (funext fun F => ObjectProperty.hom_ext _
    (NatTrans.ext (funext fun V => ?_))))
  have kV := congrFun key V.unop
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id] at kV
  simp only [smallEtaleDirectImageComp, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
  simp only [Functor.sheafPushforwardContinuous_map_hom_app,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
  change F.obj.map ((smallEtaleBaseChange B h).map
        ((smallEtaleBaseChange_factoredCompIso B _ _ _ f g fg hfg).inv.app V.unop)).op ≫
      F.obj.map ((smallEtaleBaseChange_factoredCompIso B _ _ _ h fg hfg' h₁).inv.app V.unop).op =
    F.obj.map ((smallEtaleBaseChange_factoredCompIso B _ _ _ h f hf hhf).inv.app
        ((smallEtaleBaseChange B g).obj V.unop)).op ≫
      F.obj.map ((smallEtaleBaseChange_factoredCompIso B _ _ _ hf g hfg' h₂).inv.app V.unop).op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp, kV]

section InverseImage

variable [HasColimitsOfSize.{u, u + 1} A]

/-- **The inverse image along a composite** (Freitag–Kiehl I.4). For `f : X ⟶ Y`,
`g : Y ⟶ Z` and `fg = f ≫ g`, the isomorphism `θ : f^* ∘ g^* ≅ (g ∘ f)^*` of inverse image
functors on sheaves on the small étale sites: it is the unique isomorphism compatible with the
adjunctions `f^* ⊣ f_*` and the identification `g_* ∘ f_* ≅ (g ∘ f)_*`
(`smallEtaleDirectImageComp`). -/
@[weil "lem_fk104_inverse_image_composite"]
def smallEtaleInverseImageComp (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg)
    [HasWeakSheafify (SmallEtale.topology B X.obj X.property) A]
    [HasWeakSheafify (SmallEtale.topology B Y.obj Y.property) A] :
    smallEtaleInverseImage B g A ⋙ smallEtaleInverseImage B f A ≅
      smallEtaleInverseImage B fg A :=
  Adjunction.leftAdjointCompIso (smallEtaleInverseImageAdjunction B g A)
    (smallEtaleInverseImageAdjunction B f A) (smallEtaleInverseImageAdjunction B fg A)
    (smallEtaleDirectImageComp B A f g fg hfg)

/-- **`θ_H` is natural in `H`.** -/
@[reassoc]
lemma smallEtaleInverseImageComp_hom_naturality (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) [HasWeakSheafify (SmallEtale.topology B X.obj X.property) A]
    [HasWeakSheafify (SmallEtale.topology B Y.obj Y.property) A]
    {H H' : Sheaf (SmallEtale.topology B Z.obj Z.property) A} (φ : H ⟶ H') :
    (smallEtaleInverseImage B f A).map ((smallEtaleInverseImage B g A).map φ) ≫
        (smallEtaleInverseImageComp B A f g fg hfg).hom.app H' =
      (smallEtaleInverseImageComp B A f g fg hfg).hom.app H ≫
        (smallEtaleInverseImage B fg A).map φ :=
  (smallEtaleInverseImageComp B A f g fg hfg).hom.naturality φ

/-- **The cocycle condition for `θ`.** For `h : W ⟶ X`, `f : X ⟶ Y`, `g : Y ⟶ Z`, the two
isomorphisms `h^* ∘ f^* ∘ g^* ≅ (g ∘ f ∘ h)^*` obtained from `θ` agree. -/
@[weil "lem_fk104_inverse_image_composite"]
theorem smallEtaleInverseImageComp_assoc (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : f ≫ g = fg) (hf : W ⟶ Y) (hhf : h ≫ f = hf) (hfg' : W ⟶ Z)
    (h₁ : h ≫ fg = hfg') (h₂ : hf ≫ g = hfg')
    [HasWeakSheafify (SmallEtale.topology B W.obj W.property) A]
    [HasWeakSheafify (SmallEtale.topology B X.obj X.property) A]
    [HasWeakSheafify (SmallEtale.topology B Y.obj Y.property) A] :
    Functor.isoWhiskerLeft (smallEtaleInverseImage B g A)
          (smallEtaleInverseImageComp B A h f hf hhf) ≪≫
        smallEtaleInverseImageComp B A hf g hfg' h₂ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleInverseImageComp B A f g fg hfg)
          (smallEtaleInverseImage B h A) ≪≫
        smallEtaleInverseImageComp B A h fg hfg' h₁ :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (smallEtaleDirectImageComp_assoc B A h f g fg hfg hf hhf hfg' h₁ h₂)

/-- The two isomorphisms `h^* f^* g^* H ≅ (g ∘ f ∘ h)^* H` obtained from `θ` agree. -/
@[reassoc]
lemma smallEtaleInverseImageComp_hom_app_cocycle (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : f ≫ g = fg) (hf : W ⟶ Y) (hhf : h ≫ f = hf) (hfg' : W ⟶ Z)
    (h₁ : h ≫ fg = hfg') (h₂ : hf ≫ g = hfg')
    [HasWeakSheafify (SmallEtale.topology B W.obj W.property) A]
    [HasWeakSheafify (SmallEtale.topology B X.obj X.property) A]
    [HasWeakSheafify (SmallEtale.topology B Y.obj Y.property) A]
    (H : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    (smallEtaleInverseImageComp B A h f hf hhf).hom.app ((smallEtaleInverseImage B g A).obj H) ≫
        (smallEtaleInverseImageComp B A hf g hfg' h₂).hom.app H =
      (smallEtaleInverseImage B h A).map ((smallEtaleInverseImageComp B A f g fg hfg).hom.app H) ≫
        (smallEtaleInverseImageComp B A h fg hfg' h₁).hom.app H := by
  have := congrArg (fun e => NatTrans.app (Iso.hom e) H)
    (smallEtaleInverseImageComp_assoc B A h f g fg hfg hf hhf hfg' h₁ h₂)
  simpa using this

end InverseImage

end AlgebraicGeometry
