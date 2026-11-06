module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Attr

/-!
# Base change of the cokernel of a pair of representable étale sheaves

Let `u, v : R ⟶ Y` be morphisms in the small étale site of a scheme `S`, let `f : T ⟶ S` be a
morphism, and let `u', v' : R ×_S T ⇉ Y ×_S T` be their base changes. Write `h_Z` for the sheaf
of sets represented by `Z`. Then the inverse image along `f` of the cokernel (coequalizer)
`Coker(h_u, h_v)` is the cokernel `Coker(h_{u'}, h_{v'})`.

Indeed, the inverse image `f^*` is a left adjoint, so it preserves coequalizers, and it carries
the representable sheaf `h_Z` to the representable sheaf `h_{Z ×_S T}`, naturally in `Z`. The
second fact holds for any continuous functor `G : C ⥤ D` between subcanonical sites: for a sheaf
`F` on `D`, the adjunction and the Yoneda bijection give
`Hom(G^* h_X, F) ≃ Hom(h_X, G_* F) ≃ (G_* F)(X) = F(G X)`, and the Yoneda bijection alone gives
`Hom(h_{G X}, F) ≃ F(G X)`; two objects corepresenting the same functor are isomorphic.

## Main definitions

* `CategoryTheory.Functor.sheafPullbackUliftYonedaIso`: for a continuous functor `G` between
  subcanonical sites, the pullback of the sheaf represented by `X` is the sheaf represented by
  `G X`, naturally in `X` (`CategoryTheory.Functor.sheafPullbackUliftYonedaNatIso`).
* `CategoryTheory.Functor.sheafPullbackCoequalizerUliftYonedaIso`: the pullback of the
  coequalizer of `h_u, h_v` is the coequalizer of `h_{G u}, h_{G v}`.
* `AlgebraicGeometry.smallEtaleInverseImageCoequalizerIso`: the inverse image along `f` of
  `Coker(h_u, h_v)` is `Coker(h_{u'}, h_{v'})`, for the base changes `u', v'` of `u, v`.

## Main results

* `AlgebraicGeometry.smallEtaleInverseImage_map_π_comp_coequalizerIso_hom`: the isomorphism
  carries the inverse image of the projection `h_Y ⟶ Coker(h_u, h_v)` to the projection
  `h_{Y ×_S T} ⟶ Coker(h_{u'}, h_{v'})`, up to the identification `f^* h_Y ≅ h_{Y ×_S T}`.

## Implementation notes

The cokernel of a pair of morphisms of sheaves of sets is Mathlib's coequalizer in the category
of sheaves; up to a canonical isomorphism it is the sheafification of the objectwise quotient.
Sheaves of sets on the small étale site of a scheme in `Scheme.{u}` take values in
`Type (u + 1)`, where the inverse image exists, and the representable sheaves are
`AlgebraicGeometry.smallEtaleUliftYoneda`. The statement holds for any pair `u, v`; that `u, v`
is an equivalence relation, and then so is its base change
(`AlgebraicGeometry.isEquivalenceRelation_smallEtaleBaseChange`), is not used.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁ u₂ u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D] (G : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [G.IsContinuous J K]
  [J.Subcanonical] [K.Subcanonical]
  [(G.sheafPushforwardContinuous (Type (max v w)) J K).IsRightAdjoint]

/-- The functor `F ↦ (G_* F)(X)` on sheaves on `D`, which both `G^* h_X` and `h_{G X}`
corepresent. -/
abbrev sheafPushforwardSections (X : C) : Sheaf K (Type (max v w)) ⥤ Type (max v w) :=
  G.sheafPushforwardContinuous (Type (max v w)) J K ⋙
    (sheafSections J (Type (max v w))).obj (op X)

/-- The pullback of the sheaf represented by `X` corepresents `F ↦ (G_* F)(X)`: the adjunction
followed by the Yoneda bijection. -/
def corepresentableBySheafPullbackUliftYoneda (X : C) :
    (sheafPushforwardSections.{w} G J K X).CorepresentableBy
      ((G.sheafPullback (Type (max v w)) J K).obj (J.uliftYoneda.{w}.obj X)) where
  homEquiv := ((G.sheafAdjunctionContinuous (Type (max v w)) J K).homEquiv _ _).trans
    J.uliftYonedaEquiv
  homEquiv_comp g h := by
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right, J.uliftYonedaEquiv_comp]
    rfl

/-- The sheaf represented by `G X` corepresents `F ↦ (G_* F)(X) = F(G X)`, by the Yoneda
bijection. -/
def corepresentableByUliftYonedaObj (X : C) :
    (sheafPushforwardSections.{w} G J K X).CorepresentableBy
      (K.uliftYoneda.{w}.obj (G.obj X)) where
  homEquiv := K.uliftYonedaEquiv
  homEquiv_comp g h := K.uliftYonedaEquiv_comp h g

/-- **Pullback of a representable sheaf.** For a continuous functor `G` between subcanonical
sites, the pullback of the sheaf represented by `X` is the sheaf represented by `G X`. -/
def sheafPullbackUliftYonedaIso (X : C) :
    (G.sheafPullback (Type (max v w)) J K).obj (J.uliftYoneda.{w}.obj X) ≅
      K.uliftYoneda.{w}.obj (G.obj X) :=
  (corepresentableBySheafPullbackUliftYoneda.{w} G J K X).uniqueUpToIso
    (corepresentableByUliftYonedaObj.{w} G J K X)

/-- Two corepresentations of one functor are compared by the isomorphism of their
corepresenting objects: precomposing with it carries one bijection to the other. -/
private lemma homEquiv_uniqueUpToIso_hom_comp {E : Type*} [Category E] {P : E ⥤ Type*}
    {A A' : E} (e : P.CorepresentableBy A) (e' : P.CorepresentableBy A') {Z : E} (g : A' ⟶ Z) :
    e.homEquiv ((e.uniqueUpToIso e').hom ≫ g) = e'.homEquiv g := by
  rw [e.homEquiv_comp, e'.homEquiv_eq g]
  congr 1
  rw [Functor.CorepresentableBy.uniqueUpToIso_hom, Coyoneda.fullyFaithful_preimage]
  simp [NatIso.ofComponents]

/-- The defining property of `sheafPullbackUliftYonedaIso`: precomposition with it carries the
Yoneda bijection of `h_{G X}` to the corepresentability bijection of `G^* h_X`. -/
lemma corepresentableBySheafPullbackUliftYoneda_homEquiv_iso_hom_comp (X : C)
    {F : Sheaf K (Type (max v w))} (g : K.uliftYoneda.{w}.obj (G.obj X) ⟶ F) :
    (corepresentableBySheafPullbackUliftYoneda.{w} G J K X).homEquiv
        ((sheafPullbackUliftYonedaIso.{w} G J K X).hom ≫ g) =
      (corepresentableByUliftYonedaObj.{w} G J K X).homEquiv g :=
  homEquiv_uniqueUpToIso_hom_comp _ _ g

/-- **Pullback of representable sheaves, naturally.** For a continuous functor `G` between
subcanonical sites, `G^* h_X ≅ h_{G X}`, naturally in `X`. -/
def sheafPullbackUliftYonedaNatIso :
    J.uliftYoneda.{w} ⋙ G.sheafPullback (Type (max v w)) J K ≅ G ⋙ K.uliftYoneda.{w} :=
  NatIso.ofComponents (sheafPullbackUliftYonedaIso.{w} G J K) (by
    intro X Y g
    apply (corepresentableBySheafPullbackUliftYoneda.{w} G J K X).homEquiv.injective
    have hL : (corepresentableBySheafPullbackUliftYoneda.{w} G J K X).homEquiv
        ((G.sheafPullback (Type (max v w)) J K).map (J.uliftYoneda.map g) ≫
          (sheafPullbackUliftYonedaIso.{w} G J K Y).hom) =
        ((G.sheafPushforwardContinuous (Type (max v w)) J K).obj _).obj.map g.op
          ((corepresentableBySheafPullbackUliftYoneda.{w} G J K Y).homEquiv
            (sheafPullbackUliftYonedaIso.{w} G J K Y).hom) := by
      dsimp only [corepresentableBySheafPullbackUliftYoneda, Equiv.trans_apply]
      rw [Adjunction.homEquiv_naturality_left]
      exact (J.uliftYonedaEquiv_naturality _ _).symm
    have hI := corepresentableBySheafPullbackUliftYoneda_homEquiv_iso_hom_comp.{w} G J K Y (𝟙 _)
    rw [Category.comp_id] at hI
    have hY : (corepresentableByUliftYonedaObj.{w} G J K X).homEquiv
        (K.uliftYoneda.map (G.map g) ≫ 𝟙 (K.uliftYoneda.{w}.obj (G.obj Y))) =
        ((G.sheafPushforwardContinuous (Type (max v w)) J K).obj _).obj.map g.op
          ((corepresentableByUliftYonedaObj.{w} G J K Y).homEquiv (𝟙 _)) :=
      (K.uliftYonedaEquiv_naturality _ _).symm
    rw [Category.comp_id] at hY
    dsimp only [Functor.comp_map]
    rw [hL, hI, ← hY]
    exact (corepresentableBySheafPullbackUliftYoneda_homEquiv_iso_hom_comp.{w} G J K X _).symm)

variable [HasCoequalizers (Sheaf J (Type (max v w)))] [HasCoequalizers (Sheaf K (Type (max v w)))]

/-- **Pullback of the cokernel of a pair of representable sheaves.** For a continuous functor
`G` between subcanonical sites and `u, v : R ⟶ Y` in `C`, the pullback of the coequalizer of
`h_u, h_v` is the coequalizer of `h_{G u}, h_{G v}`. -/
def sheafPullbackCoequalizerUliftYonedaIso {R Y : C} (u v : R ⟶ Y) :
    (G.sheafPullback (Type (max v w)) J K).obj
        (coequalizer (J.uliftYoneda.{w}.map u) (J.uliftYoneda.{w}.map v)) ≅
      coequalizer (K.uliftYoneda.{w}.map (G.map u)) (K.uliftYoneda.{w}.map (G.map v)) :=
  haveI : PreservesColimitsOfShape WalkingParallelPair (G.sheafPullback (Type (max v w)) J K) :=
    (G.sheafAdjunctionContinuous (Type (max v w)) J K).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  (PreservesCoequalizer.iso (G.sheafPullback (Type (max v w)) J K) _ _).symm ≪≫
    HasColimit.isoOfNatIso
      (parallelPair.ext ((sheafPullbackUliftYonedaNatIso.{w} G J K).app R)
        ((sheafPullbackUliftYonedaNatIso.{w} G J K).app Y)
        ((sheafPullbackUliftYonedaNatIso.{w} G J K).hom.naturality u)
        ((sheafPullbackUliftYonedaNatIso.{w} G J K).hom.naturality v))

/-- The isomorphism `sheafPullbackCoequalizerUliftYonedaIso` carries the pullback of the
projection `h_Y ⟶ Coker(h_u, h_v)` to the projection `h_{G Y} ⟶ Coker(h_{G u}, h_{G v})`, up to
`G^* h_Y ≅ h_{G Y}`. -/
@[reassoc]
lemma sheafPullback_map_π_comp_coequalizerUliftYonedaIso_hom {R Y : C} (u v : R ⟶ Y) :
    (G.sheafPullback (Type (max v w)) J K).map (coequalizer.π _ _) ≫
        (sheafPullbackCoequalizerUliftYonedaIso.{w} G J K u v).hom =
      (sheafPullbackUliftYonedaIso.{w} G J K Y).hom ≫ coequalizer.π _ _ := by
  have : PreservesColimitsOfShape WalkingParallelPair (G.sheafPullback (Type (max v w)) J K) :=
    (G.sheafAdjunctionContinuous (Type (max v w)) J K).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  simp only [sheafPullbackCoequalizerUliftYonedaIso, Iso.trans_hom, Iso.symm_hom,
    map_π_preserves_coequalizer_inv_assoc]
  rw [HasColimit.isoOfNatIso_ι_hom]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- **Base change of the cokernel of a pair of representable sheaves** (FK I.4). Let
`u, v : R ⟶ Y` be morphisms in the small étale site of `S`, `f : T ⟶ S` a morphism, and
`u', v' : R ×_S T ⇉ Y ×_S T` their base changes. Then
`f^* Coker(h_u, h_v) ≅ Coker(h_{u'}, h_{v'})`. -/
@[weil "lem_fk104_cokernel_base_change"]
def smallEtaleInverseImageCoequalizerIso {R Y : SmallEtale B S.obj S.property} (u v : R ⟶ Y) :
    (smallEtaleInverseImage B f (Type (u + 1))).obj
        (coequalizer ((smallEtaleUliftYoneda.{u, u + 1} B S.obj S.property).map u)
          ((smallEtaleUliftYoneda.{u, u + 1} B S.obj S.property).map v)) ≅
      coequalizer ((smallEtaleUliftYoneda.{u, u + 1} B T.obj T.property).map
          ((smallEtaleBaseChange B f).map u))
        ((smallEtaleUliftYoneda.{u, u + 1} B T.obj T.property).map
          ((smallEtaleBaseChange B f).map v)) :=
  (smallEtaleBaseChange B f).sheafPullbackCoequalizerUliftYonedaIso.{u + 1} _ _ u v

/-- The isomorphism `smallEtaleInverseImageCoequalizerIso` is compatible with the projections:
it carries `f^*` of `h_Y ⟶ Coker(h_u, h_v)` to `h_{Y ×_S T} ⟶ Coker(h_{u'}, h_{v'})`, up to the
identification `f^* h_Y ≅ h_{Y ×_S T}`. -/
@[reassoc]
lemma smallEtaleInverseImage_map_π_comp_coequalizerIso_hom
    {R Y : SmallEtale B S.obj S.property} (u v : R ⟶ Y) :
    (smallEtaleInverseImage B f (Type (u + 1))).map (coequalizer.π _ _) ≫
        (smallEtaleInverseImageCoequalizerIso B f u v).hom =
      ((smallEtaleBaseChange B f).sheafPullbackUliftYonedaIso.{u + 1} _ _ Y).hom ≫
        coequalizer.π _ _ :=
  (smallEtaleBaseChange B f).sheafPullback_map_π_comp_coequalizerUliftYonedaIso_hom.{u + 1}
    _ _ u v

end AlgebraicGeometry
