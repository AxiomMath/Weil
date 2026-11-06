module

public import Weil.AlgebraicGeometry.ComplexPoints.ComparisonPushforward

/-!
# The comparison map for finite morphisms and points

Let `c^ν(X, F) : H^ν_et(X, F) → H^ν(X(ℂ), F_an)` be the comparison map of a scheme `X` locally of
finite type over `ℂ`. This file proves that it is compatible with direct images along finite
morphisms; the generalities, and the case of `Spec ℂ`, are in
`Weil.AlgebraicGeometry.ComplexPoints.ComparisonPushforward`.

Let `f : X' ⟶ X` be finite over `ℂ`, with `X` separated. The map `f_an : X'(ℂ) → X(ℂ)` is closed
(the values at a point of `X'(ℂ)` of the sections of `f⁻¹ U`, `U` affine, are roots of monic
polynomials whose coefficients are values at its image) and has finite fibres. Hence the stalk of
`f_an,* K` at `p` is the product of the stalks of `K` along the fibre over `p`; the same holds
for the étale direct image `f_*` at a geometric point (Stacks 03QP, transported from the bounded
small étale site). Both direct images are exact. The base change map
`ε^* f_* G ⟶ f_an,* ε'^* G` is an isomorphism: on the stalk at `p`, followed by the component at
a point `q` over `p`, it is the étale component at `q`. This is checked on transposes into
skyscraper sheaves, where it reduces to the identification of `ε_*` of an analytic skyscraper
sheaf with an étale one, read on the generators of the free sheaves of sections. Finally the
adjunctions `f^* ⊣ f_*` and `f_an^* ⊣ f_an,*` of exact functors identify `Ext^ν(ℤ, f_* G)` with
`Ext^ν(ℤ, G)` on both sides, compatibly with `ε^*`; so `c^ν(X, f_* G)` is bijective exactly when
`c^ν(X', G)` is. A complex point `p : Spec ℂ ⟶ X` is a closed immersion, so `c^ν(X, p_* G)` is
bijective for every abelian sheaf `G` on `Spec ℂ`.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.etaleBaseChangeFiberMap`: lifts of a geometric point
  to a base change.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.bijective_etalePushforwardFiberMaps`: the stalk of a
  finite direct image on the small étale site is the product of the stalks at the lifts.
* `AlgebraicGeometry.Scheme.ComplexPoints.isClosedMap_map_of_isFinite`: `X'(ℂ) → X(ℂ)` is closed
  for `f` finite and `X` separated.
* `AlgebraicGeometry.Scheme.ComplexPoints.isIso_pushforwardBaseChange_of_isFinite`: the base change
  map `ε^* f_* ⟶ f_an,* ε'^*` is an isomorphism for `f` finite.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_pushforward_bijective_iff`: `c^ν(X, f_* G)`
  is bijective if and only if `c^ν(X', G)` is, for `f` finite.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_pushforward_point_bijective`:
  `c^ν(X, p_* G)` is bijective for a complex point `p`.

## Implementation notes

The analytic inverse image is a left adjoint known only through its right adjoint `ε_*`, so every
map out of a stalk of `ε^* F` is compared through its transpose into a skyscraper sheaf
(`CategoryTheory.Adjunction.homEquiv_eq_homEquiv_leftAdjointUniq_inv`,
`CategoryTheory.Adjunction.homEquiv_mateEquiv_leftAdjointUniq_inv_app_comp`).

The stalk formula of Stacks 03QP is proved in the library for sheaves of sets on the bounded small
étale site of Stacks 021B; it is transported to Mathlib's small étale site along the initial
functor between the two categories of étale neighbourhoods and the identification of the two
base change functors, and from sheaves of sets to abelian sheaves along the forgetful functor.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [SGA 4, Exposé XVI, §4]
* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### Fibres of direct images on the small étale site -/

section EtaleFiber

open Stacks.EtaleCohomology

/-- Base change of étale schemes along a morphism of schemes. -/
local notation "𝔅" => Stacks.EtaleCohomology.smallEtaleBaseChange

variable {X X' : Scheme.{0}} (f : X' ⟶ X) {Ω : Type} [Field Ω] [IsSepClosed Ω]

/-- A lift `t` of a geometric point `s = s' ≫ f` to an étale `X`-scheme `U` gives the lift
`(t, s')` of `s'` to the base change `U ×_X X'`. -/
noncomputable def etaleBaseChangeFiberMap (s' : Spec (.of Ω) ⟶ X') (s : Spec (.of Ω) ⟶ X)
    (h : s' ≫ f = s) : (pointSmallEtale s).fiber ⟶ 𝔅 f ⋙ (pointSmallEtale s').fiber where
  app U := TypeCat.ofHom fun t => Over.homMk (pullback.lift t.left s' ((Over.w t).trans h.symm))
    (pullback.lift_snd _ _ _)
  naturality U V g := by
    ext t
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · change pullback.lift (t.left ≫ g.left) s' _ ≫ _ = (pullback.lift t.left s' _ ≫
        pullback.lift (pullback.fst U.hom f ≫ g.left) (pullback.snd U.hom f) _) ≫ _
      erw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · change pullback.lift (t.left ≫ g.left) s' _ ≫ _ = (pullback.lift t.left s' _ ≫
        pullback.lift (pullback.fst U.hom f ≫ g.left) (pullback.snd U.hom f) _) ≫ _
      erw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]

section BoundedBaseChange

variable (B : BigEtaleSite.{0}) (hX : B.Contains X) (hX' : B.Contains X')

/-- The morphism `f` in the big étale site. -/
abbrev boundedHom : B.obj X' hX' ⟶ B.obj X hX := ObjectProperty.homMk f

/-- Base change on the bounded site followed by the inclusion into Mathlib's small étale site is
the inclusion followed by base change. -/
noncomputable def toEtaleSiteBaseChangeIso :
    AlgebraicGeometry.smallEtaleBaseChange B (boundedHom f B hX hX') ⋙
        SmallEtale.toEtaleSite B X' hX' ≅
      SmallEtale.toEtaleSite B X hX ⋙ 𝔅 f :=
  NatIso.ofComponents (fun V => MorphismProperty.Over.isoMk
      (((IsPullback.of_hasPullback V.obj.hom (boundedHom f B hX hX')).map B.inclusion).isoPullback)
      (by
        change _ ≫ pullback.snd _ _ = _
        erw [IsPullback.isoPullback_hom_snd]
        rfl))
    (fun {V W} g => by
      have hB₁ : ((AlgebraicGeometry.smallEtaleBaseChange B (boundedHom f B hX hX')).map
          g).hom.left ≫ pullback.fst W.obj.hom (boundedHom f B hX hX') =
            pullback.fst V.obj.hom (boundedHom f B hX hX') ≫ g.hom.left := by
        change ((Over.pullback (boundedHom f B hX hX')).map
          ((SmallEtale.inclusion B _ _).map g)).left ≫ _ = _
        simp only [Over.pullback_map_left]
        exact pullback.lift_fst _ _ _
      have hB₂ : ((AlgebraicGeometry.smallEtaleBaseChange B (boundedHom f B hX hX')).map
          g).hom.left ≫ pullback.snd W.obj.hom (boundedHom f B hX hX') =
            pullback.snd V.obj.hom (boundedHom f B hX hX') := by
        change ((Over.pullback (boundedHom f B hX hX')).map
          ((SmallEtale.inclusion B _ _).map g)).left ≫ _ = _
        simp only [Over.pullback_map_left]
        exact pullback.lift_snd _ _ _
      refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
      · change B.inclusion.map ((AlgebraicGeometry.smallEtaleBaseChange B
          (boundedHom f B hX hX')).map g).hom.left ≫ _ ≫ _ = _ ≫
            pullback.lift (pullback.fst _ _ ≫ B.inclusion.map g.hom.left) (pullback.snd _ _) _ ≫ _
        erw [IsPullback.isoPullback_hom_fst, ← B.inclusion.map_comp, hB₁, B.inclusion.map_comp,
          pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc]
        rfl
      · change B.inclusion.map ((AlgebraicGeometry.smallEtaleBaseChange B
          (boundedHom f B hX hX')).map g).hom.left ≫ _ ≫ _ = _ ≫
            pullback.lift (pullback.fst _ _ ≫ B.inclusion.map g.hom.left) (pullback.snd _ _) _ ≫ _
        erw [IsPullback.isoPullback_hom_snd, ← B.inclusion.map_comp, hB₂,
          pullback.lift_snd, IsPullback.isoPullback_hom_snd]
        rfl)

/-- **The stalk of a finite direct image of a sheaf of sets** at a geometric point is the
product of the stalks at its lifts (Stacks 03QP, transported from the bounded small étale
site). -/
theorem bijective_etalePushforwardFiberMaps_type [IsFinite f] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (G : Sheaf X'.smallEtaleTopology (Type 1)) :
    Function.Bijective (fun (z : (pointSmallEtale s).sheafFiber.obj
        (((𝔅 f).sheafPushforwardContinuous (Type 1) _ _).obj G))
        (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s}) =>
      GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) G z) := by
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({X, X'} : Set Scheme.{0})
  have hX : B.Contains X := hB X (by simp)
  have hX' : B.Contains X' := hB X' (by simp)
  let fB := boundedHom f B hX hX'
  have : IsFinite (B.inclusion.map fB) := ‹IsFinite f›
  let y : GeometricPoint X := ⟨Ω, s⟩
  let FB : Sheaf (SmallEtale.topology B X' hX') (Type 1) :=
    ((SmallEtale.toEtaleSite B X' hX').sheafPushforwardContinuous (Type 1) _ _).obj G
  have hbij := finitePushforwardStalkToProduct_bijective_univ.{0, 0} B fB y FB
  let ι := toEtaleSiteBaseChangeIso f B hX hX'
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B fB
  let PB := ((AlgebraicGeometry.smallEtaleBaseChange B fB).sheafPushforwardContinuous
      (Type 1) (SmallEtale.topology B (B.obj X hX).1 (B.obj X hX).property)
      (SmallEtale.topology B (B.obj X' hX').1 (B.obj X' hX').property)).obj FB
  let eα₁ : etaleStalk B X hX y
      (((AlgebraicGeometry.smallEtaleBaseChange B fB).sheafPushforwardContinuous
      (Type 1) (SmallEtale.topology B (B.obj X hX).1 (B.obj X hX).property)
      (SmallEtale.topology B (B.obj X' hX').1 (B.obj X' hX').property)).obj FB).obj ≅
      etaleStalk B X hX y ((SmallEtale.toEtaleSite B X hX).op ⋙ (𝔅 f).op ⋙ G.obj) :=
    colim.mapIso (Functor.isoWhiskerLeft (CategoryOfElements.π (geometricPointFiber B X hX y)).op
      (Functor.isoWhiskerRight (NatIso.op ι.symm) G.obj))
  let α₂ := etaleStalkToPresheafFiber B hX y ((𝔅 f).op ⋙ G.obj)
  let β := fun t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s} =>
    etaleStalkToPresheafFiber B hX' (geometricPointLift (B.inclusion.map fB) y t) G.obj
  have hsq : ∀ z, (fun t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s} =>
      GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) G (α₂ (eα₁.hom z))) =
      (fun t => β t (finitePushforwardStalkToProductUniv.{0, 0} B fB y FB z t)) := by
    intro z
    obtain ⟨⟨U⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit (colimit.isColimit _) z
    funext t
    have e₁' : colimit.ι ((CategoryOfElements.π (geometricPointFiber B X hX y)).op ⋙
        PB.obj) (op U) ≫ eα₁.hom = G.obj.map (ι.inv.app U.1).op ≫ colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B X hX y)).op ⋙
          (SmallEtale.toEtaleSite B X hX).op ⋙ (𝔅 f).op ⋙ G.obj) (op U) := by
      simp only [eα₁, Functor.mapIso_hom]
      erw [colim_map, ι_colimMap]
      rfl
    have e₁ : eα₁.hom (colimit.ι ((CategoryOfElements.π (geometricPointFiber B X hX y)).op ⋙
        PB.obj) (op U) a) = colimit.ι
        ((CategoryOfElements.π (geometricPointFiber B X hX y)).op ⋙
          (SmallEtale.toEtaleSite B X hX).op ⋙ (𝔅 f).op ⋙ G.obj) (op U)
        (G.obj.map (ι.inv.app U.1).op a) := ConcreteCategory.congr_hom e₁' a
    have e₂ := finitePushforwardStalkComponent_germ_univ.{0, 0} B fB y FB t U a
    change GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) G (α₂ (eα₁.hom (colimit.ι
          ((CategoryOfElements.π (geometricPointFiber B X hX y)).op ⋙ PB.obj) (op U) a))) =
      β t (finitePushforwardStalkComponentUniv.{0, 0} B fB y FB t (colimit.ι
          ((CategoryOfElements.π (geometricPointFiber B X hX y)).op ⋙ PB.obj) (op U) a))
    erw [e₁, e₂]
    let v := (toEtaleSiteFiberIso B X hX y).inv.app U.1 U.2
    let L := liftedEtaleNeighborhood B fB y t U
    have e₃ : α₂ (colimit.ι ((CategoryOfElements.π (geometricPointFiber B X hX y)).op ⋙
          (SmallEtale.toEtaleSite B X hX).op ⋙ (𝔅 f).op ⋙ G.obj) (op U)
          (G.obj.map (ι.inv.app U.1).op a)) =
        (pointSmallEtale s).toPresheafFiber ((SmallEtale.toEtaleSite B X hX).obj U.1) v
          ((𝔅 f).op ⋙ G.obj) (G.obj.map (ι.inv.app U.1).op a) :=
      ConcreteCategory.congr_hom (ι_etaleStalkToPresheafFiber B hX y ((𝔅 f).op ⋙ G.obj) U) _
    have e₄ : β t (colimit.ι ((CategoryOfElements.π (geometricPointFiber B X' hX'
          (geometricPointLift (B.inclusion.map fB) y t))).op ⋙ FB.obj) (op L) a) =
        (pointSmallEtale t.1).toPresheafFiber ((SmallEtale.toEtaleSite B X' hX').obj L.1)
          ((toEtaleSiteFiberIso B X' hX' _).inv.app L.1 L.2) G.obj a :=
      ConcreteCategory.congr_hom (ι_etaleStalkToPresheafFiber B hX'
        (geometricPointLift (B.inclusion.map fB) y t) G.obj L) a
    have e₅ := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_pushforwardFiberMap
      (𝔅 f) (etaleBaseChangeFiberMap f t.1 s t.2) G ((SmallEtale.toEtaleSite B X hX).obj U.1) v)
      (G.obj.map (ι.inv.app U.1).op a)
    have e₆ := (pointSmallEtale t.1).toPresheafFiber_w_apply (ι.inv.app U.1)
      ((etaleBaseChangeFiberMap f t.1 s t.2).app _ v) G.obj a
    have hfib : (pointSmallEtale t.1).fiber.map (ι.inv.app U.1)
        ((etaleBaseChangeFiberMap f t.1 s t.2).app _ v) =
        (toEtaleSiteFiberIso B X' hX' (geometricPointLift (B.inclusion.map fB) y t)).inv.app
          L.1 L.2 := by
      let sq := (IsPullback.of_hasPullback U.1.obj.hom fB).map B.inclusion
      refine Over.OverMorphism.ext ?_
      change pullback.lift U.2.1 t.1 _ ≫ sq.isoPullback.inv = L.2.1
      refine (Iso.comp_inv_eq _).2 (pullback.hom_ext ?_ ?_)
      · erw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst,
          liftedEtaleNeighborhood_point_fst]
      · erw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd]
        exact L.2.2.symm
    refine (congrArg _ e₃).trans (e₅.trans (e₆.trans (Eq.trans ?_ e₄.symm)))
    rw [hfib]
    rfl
  have hα₂ : Function.Bijective α₂ := (isIso_iff_bijective _).1 inferInstance
  have hα₁ : Function.Bijective eα₁.hom := (isIso_iff_bijective _).1 inferInstance
  have hβ : ∀ t, Function.Bijective (β t) := fun t => (isIso_iff_bijective _).1 inferInstance
  have key : (fun (z : (pointSmallEtale s).sheafFiber.obj
        (((𝔅 f).sheafPushforwardContinuous (Type 1) _ _).obj G))
        (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s}) =>
      GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) G z) ∘ (α₂ ∘ eα₁.hom) =
      (fun w t => β t (w t)) ∘ finitePushforwardStalkToProductUniv.{0, 0} B fB y FB :=
    funext fun z => hsq z
  have h1 := Eq.mpr (congrArg Function.Bijective key) ((Function.Bijective.piMap hβ).comp hbij)
  exact (Function.Bijective.of_comp_iff _ (hα₂.comp hα₁)).1 h1

/-- Forgetting the group structure commutes with filtered colimits indexed in universe `0`. -/
instance preservesFilteredColimitsOfSize_zero_forget_addCommGrpCat :
    PreservesFilteredColimitsOfSize.{0, 0} (CategoryTheory.forget AddCommGrpCat.{1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{1, 1, 0, 0} (CategoryTheory.forget AddCommGrpCat.{1})

/-- **The stalk of a finite direct image of an abelian sheaf** on the small étale site at a
geometric point is the product of the stalks at its lifts (Stacks 03QP). -/
theorem bijective_etalePushforwardFiberMaps [IsFinite f] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) (G : Sheaf X'.smallEtaleTopology AddCommGrpCat.{1}) :
    Function.Bijective (fun (z : ToType ((pointSmallEtale s).sheafFiber.obj
        (((𝔅 f).sheafPushforwardContinuous AddCommGrpCat.{1} _ _).obj G)))
        (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s}) =>
      GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) G z) := by
  let Gt := (sheafCompose X'.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{1})).obj G
  have hT := bijective_etalePushforwardFiberMaps_type f s Gt
  let e := fun (Φ : X'.smallEtaleTopology.Point.{0}) =>
    (Φ.presheafFiberCompIso (CategoryTheory.forget AddCommGrpCat.{1})).app G.obj
  let e' := ((pointSmallEtale s).presheafFiberCompIso (CategoryTheory.forget AddCommGrpCat.{1})).app
    ((𝔅 f).op ⋙ G.obj)
  have hsq : ∀ t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s},
      GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
          (etaleBaseChangeFiberMap f t.1 s t.2) Gt ≫ (e (pointSmallEtale t.1)).hom =
        e'.hom ≫ (CategoryTheory.forget AddCommGrpCat.{1}).map
          (GrothendieckTopology.Point.pushforwardFiberMap
          (𝔅 f) (etaleBaseChangeFiberMap f t.1 s t.2) G) := by
    intro t
    refine (pointSmallEtale s).presheafFiber_hom_ext fun U v => ?_
    ext a
    have h1 := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) Gt U v) a
    have h2 := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app (pointSmallEtale t.1)
        (CategoryTheory.forget AddCommGrpCat.{1}) _
        ((etaleBaseChangeFiberMap f t.1 s t.2).app U v) G.obj) a
    have h3 := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app (pointSmallEtale s)
        (CategoryTheory.forget AddCommGrpCat.{1}) U v ((𝔅 f).op ⋙ G.obj)) a
    have h4 := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) G U v) a
    exact (congrArg _ h1).trans (h2.trans (h4.symm.trans (congrArg _ h3.symm)))
  have he : ∀ Φ : X'.smallEtaleTopology.Point.{0}, Function.Bijective (e Φ).hom :=
    fun Φ => (isIso_iff_bijective _).1 inferInstance
  have he' : Function.Bijective e'.hom := (isIso_iff_bijective _).1 inferInstance
  have key : (fun (w : ∀ t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s},
      ToType ((pointSmallEtale t.1).sheafFiber.obj Gt))
      (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s}) => (e (pointSmallEtale t.1)).hom (w t)) ∘
      (fun (z : ToType ((pointSmallEtale s).sheafFiber.obj
        (((𝔅 f).sheafPushforwardContinuous (Type 1) _ _).obj Gt)))
      (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s}) =>
        GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
          (etaleBaseChangeFiberMap f t.1 s t.2) Gt z) =
      (fun (z : ToType ((pointSmallEtale s).sheafFiber.obj
        (((𝔅 f).sheafPushforwardContinuous AddCommGrpCat.{1} _ _).obj G)))
        (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s}) =>
      GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f t.1 s t.2) G z) ∘ e'.hom :=
    funext fun z => funext fun t => (ConcreteCategory.congr_hom (hsq t) z :)
  have hpi : Function.Bijective (fun (w : ∀ t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s},
      ToType ((pointSmallEtale t.1).sheafFiber.obj Gt))
      (t : {t : Spec (.of Ω) ⟶ X' // t ≫ f = s}) => (e (pointSmallEtale t.1)).hom (w t)) :=
    Function.Bijective.piMap fun t => he (pointSmallEtale t.1)
  have h1 := hpi.comp hT
  rw [key] at h1
  exact (Function.Bijective.of_comp_iff _ he').1 h1

end BoundedBaseChange

end EtaleFiber

/-! ### The base change map on stalks -/

section BaseChangeStalk

open Stacks.EtaleCohomology

-- At the coefficient universe `max (u + 1) v` this instance is also tried for `AddCommGrpCat.{2}`
-- on the small étale site, and instance search stops at `2 =?= max 1 ?v`.
attribute [-instance] Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale

/-- Base change of étale schemes along a morphism of schemes. -/
local notation "𝔅" => Stacks.EtaleCohomology.smallEtaleBaseChange

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType x'] (f : X' ⟶ X) (hf : f ≫ x = x')
  {p : ComplexPoints x} {q : ComplexPoints x'} (hpq : map f hf q = p)

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
include hpq in
theorem hom_comp_eq_of_map_eq : q.hom ≫ f = p.hom := by
  rw [← hpq]
  rfl

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
include hpq in
theorem analyticMap_up_of_map_eq : analyticMap x x' f hf (ULift.up q) = ULift.up p := by
  rw [analyticMap_apply, hpq]

/-- `f_an,*` of the skyscraper sheaf at `q` maps to the skyscraper sheaf at `p = f(q)`. -/
noncomputable abbrev analyticSkyscraperHom (M : AddCommGrpCat.{1}) :
    (analyticPushforward x x' f hf).obj ((anPoint x' q).skyscraperSheaf M) ⟶
      (anPoint x p).skyscraperSheaf M :=
  TopCat.Sheaf.pushforwardSkyscraperHom (analyticMap_up_of_map_eq x x' f hf hpq) M

/-- `f_*` of the étale skyscraper sheaf at `q` maps to the étale skyscraper sheaf at `p`. -/
noncomputable abbrev etaleSkyscraperHom (M : AddCommGrpCat.{1}) :
    (smallEtalePushforwardAb f).obj ((etPoint x' q).skyscraperSheaf M) ⟶
      (etPoint x p).skyscraperSheaf M :=
  GrothendieckTopology.Point.pushforwardSkyscraperMap (𝔅 f)
    (etaleBaseChangeFiberMap f q.hom p.hom (hom_comp_eq_of_map_eq x x' f hf hpq)) M

/-- **The skyscraper sheaves and the base change of `ε_*`.** -/
theorem directImageBaseChangeIso_skyscraper (M : AddCommGrpCat.{1}) :
    (directImageBaseChangeIso x x' f hf).hom.app ((anPoint x' q).skyscraperSheaf M) ≫
        (analyticDirectImage x).map (analyticSkyscraperHom x x' f hf hpq M) ≫
          (skyscraperIso x p).hom.app M =
      (smallEtalePushforwardAb f).map ((skyscraperIso x' q).hom.app M) ≫
        etaleSkyscraperHom x x' f hf hpq M := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  induction U using Opposite.rec with | op U => ?_
  refine Pi.hom_ext _ _ fun t => ?_
  ext m
  obtain ⟨z, hz⟩ := sectionsFiberToFiber_surjective x p U (ULift.up t)
  obtain ⟨V, ⟨⟨hpV⟩⟩, σ, rfl⟩ :=
    (anPoint x p).toPresheafFiber_jointly_surjective (P := sectionsPresheaf x U) z
  have hq : ULift.up q ∈ (TopologicalSpace.Opens.map (analyticMap x x' f hf)).obj V := by
    change analyticMap x x' f hf (ULift.up q) ∈ V
    rw [analyticMap_up_of_map_eq x x' f hf hpq]
    exact hpV
  have lhs : Pi.π (fun _ => M) t
      ((((directImageBaseChangeIso x x' f hf).hom.app ((anPoint x' q).skyscraperSheaf M) ≫
        (analyticDirectImage x).map (analyticSkyscraperHom x x' f hf hpq M) ≫
          (skyscraperIso x p).hom.app M).hom.app (op U)) m) =
      Pi.π (fun _ => M) (⟨⟨hq⟩⟩ : (anPoint x' q).fiber.obj _)
        (m.hom.app (op ((TopologicalSpace.Opens.map (analyticMap x x' f hf)).obj V))
          (sectionGenerator x' ((𝔅 f).obj U) (baseChangeSection x x' f hf U V σ))) := by
    change Pi.π (fun _ => M) t (((skyscraperIso x p).hom.app M).hom.app (op U)
      (((analyticDirectImage x).map (analyticSkyscraperHom x x' f hf hpq M)).hom.app (op U)
        (((directImageBaseChangeIso x x' f hf).hom.app
          ((anPoint x' q).skyscraperSheaf M)).hom.app (op U) m))) = _
    refine (π_skyscraperIso_hom_app x p M U t V hpV σ hz _).trans ?_
    change Pi.π (fun _ => M) (⟨⟨hpV⟩⟩ : (anPoint x p).fiber.obj V)
      ((analyticSkyscraperHom x x' f hf hpq M).hom.app (op V)
        (m.hom.app (op ((TopologicalSpace.Opens.map (analyticMap x x' f hf)).obj V))
          ((freeBaseChangeSections x x' f hf U).hom.app (op V)
            (sectionGenerator x U σ)))) = _
    rw [freeBaseChangeSections_sectionGenerator]
    exact ConcreteCategory.congr_hom (TopCat.Sheaf.pushforwardSkyscraperHom_app_π
      (analyticMap_up_of_map_eq x x' f hf hpq) M (op V) ⟨⟨hpV⟩⟩) _
  have ht : t.left = (σ.1 ⟨ULift.up p, hpV⟩).down.hom := by
    rw [sectionsFiberToFiber_toPresheafFiber] at hz
    exact (congrArg (fun w => Over.Hom.left w.down) hz).symm
  have hσ' : sectionsFiberToFiber x' q ((𝔅 f).obj U) ((anPoint x' q).toPresheafFiber _ ⟨⟨hq⟩⟩
      (sectionsPresheaf x' _) (baseChangeSection x x' f hf U V σ)) =
      ULift.up ((etaleBaseChangeFiberMap f q.hom p.hom
        (hom_comp_eq_of_map_eq x x' f hf hpq)).app U t) := by
    rw [sectionsFiberToFiber_toPresheafFiber]
    refine congrArg ULift.up (Over.OverMorphism.ext ?_)
    change pullback.lift _ q.hom _ = pullback.lift t.left q.hom _
    congr 1
    rw [ht]
    exact congrArg (fun v => (σ.1 v).down.hom)
      (Subtype.ext (analyticMap_up_of_map_eq x x' f hf hpq))
  have rhs : Pi.π (fun _ => M) t
      ((((smallEtalePushforwardAb f).map ((skyscraperIso x' q).hom.app M) ≫
        etaleSkyscraperHom x x' f hf hpq M).hom.app (op U)) m) =
      Pi.π (fun _ => M) (⟨⟨hq⟩⟩ : (anPoint x' q).fiber.obj _)
        (m.hom.app (op ((TopologicalSpace.Opens.map (analyticMap x x' f hf)).obj V))
          (sectionGenerator x' ((𝔅 f).obj U) (baseChangeSection x x' f hf U V σ))) := by
    change Pi.π (fun _ => M) t ((etaleSkyscraperHom x x' f hf hpq M).hom.app (op U)
      (((skyscraperIso x' q).hom.app M).hom.app (op ((𝔅 f).obj U)) m)) = _
    refine (ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.pushforwardSkyscraperMap_app_π (𝔅 f)
        (etaleBaseChangeFiberMap f q.hom p.hom (hom_comp_eq_of_map_eq x x' f hf hpq)) M
        (op U) t) _).trans ?_
    exact π_skyscraperIso_hom_app x' q M ((𝔅 f).obj U) _
      ((TopologicalSpace.Opens.map (analyticMap x x' f hf)).obj V) hq
      (baseChangeSection x x' f hf U V σ) hσ' m
  exact lhs.trans rhs.symm

/-- **The base change map on stalks.** At a complex point `p` of `X` and a complex point `q` of
`X'` over it, the stalk of `ε^* f_* G ⟶ f_an,* ε'^* G` followed by the component at `q` of the
stalk of `f_an,*` is the étale component at `q` of the stalk of `f_*`, through the stalk
identifications of `ε^*` and `ε'^*`. -/
theorem sheafFiber_map_pushforwardBaseChange_comp (G : EtSheaf X') :
    (anPoint x p).sheafFiber.map ((pushforwardBaseChange x x' f hf).app G) ≫
        TopCat.Sheaf.pushforwardFiberComponent (analyticMap_up_of_map_eq x x' f hf hpq)
          ((analyticInverseImage x').obj G) ≫ (stalkIso x' q).hom.app G =
      (stalkIso x p).hom.app ((smallEtalePushforwardAb f).obj G) ≫
        GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
          (etaleBaseChangeFiberMap f q.hom p.hom (hom_comp_eq_of_map_eq x x' f hf hpq)) G := by
  let adj := (analyticAdjunction x).comp (anPoint x p).skyscraperSheafAdjunction
  let adj' := (analyticAdjunction x').comp (anPoint x' q).skyscraperSheafAdjunction
  apply (adj.homEquiv _ _).injective
  have hR := Adjunction.homEquiv_eq_homEquiv_leftAdjointUniq_inv adj
    (etPoint x p).skyscraperSheafAdjunction (skyscraperIso x p).symm
    ((stalkIso x p).hom.app ((smallEtalePushforwardAb f).obj G) ≫
      GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
        (etaleBaseChangeFiberMap f q.hom p.hom (hom_comp_eq_of_map_eq x x' f hf hpq)) G)
  have hQ := Adjunction.homEquiv_eq_homEquiv_leftAdjointUniq_inv adj'
    (etPoint x' q).skyscraperSheafAdjunction (skyscraperIso x' q).symm ((stalkIso x' q).hom.app G)
  change _ = (etPoint x p).skyscraperSheafAdjunction.homEquiv _ _
    ((stalkIso x p).inv.app _ ≫ (stalkIso x p).hom.app _ ≫ _) ≫ _ at hR
  change _ = (etPoint x' q).skyscraperSheafAdjunction.homEquiv _ _
    ((stalkIso x' q).inv.app _ ≫ (stalkIso x' q).hom.app _) ≫ _ at hQ
  erw [Iso.inv_hom_id_app_assoc] at hR
  erw [Iso.inv_hom_id_app] at hQ
  have hP := GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_pushforwardFiberMap_comp
    (𝔅 f) (etaleBaseChangeFiberMap f q.hom p.hom (hom_comp_eq_of_map_eq x x' f hf hpq)) G
    (𝟙 ((etPoint x' q).sheafFiber.obj G))
  rw [Category.comp_id] at hP
  rw [hR]
  erw [hP]
  rw [Adjunction.comp_homEquiv] at hQ ⊢
  simp only [Equiv.trans_apply] at hQ ⊢
  have hL1 := (anPoint x p).skyscraperSheafAdjunction.homEquiv_naturality_left
    ((pushforwardBaseChange x x' f hf).app G)
    (TopCat.Sheaf.pushforwardFiberComponent (analyticMap_up_of_map_eq x x' f hf hpq)
      ((analyticInverseImage x').obj G) ≫ (stalkIso x' q).hom.app G)
  have hL2 := TopCat.Sheaf.skyscraperSheafAdjunction_homEquiv_pushforwardFiberComponent_comp
    (analyticMap_up_of_map_eq x x' f hf hpq) ((analyticInverseImage x').obj G)
    ((stalkIso x' q).hom.app G)
  erw [hL1]
  erw [hL2]
  have hM := homEquiv_pushforwardBaseChange_app_comp x x' f hf G
    ((anPoint x' q).skyscraperSheafAdjunction.homEquiv _ _ ((stalkIso x' q).hom.app G))
  have hN := (analyticAdjunction x).homEquiv_naturality_right
    ((pushforwardBaseChange x x' f hf).app G ≫ (analyticPushforward x x' f hf).map
      ((anPoint x' q).skyscraperSheafAdjunction.homEquiv _ _ ((stalkIso x' q).hom.app G)))
    (analyticSkyscraperHom x x' f hf hpq ((etPoint x' q).sheafFiber.obj G))
  erw [← Category.assoc, hN, hM, hQ]
  have hC := directImageBaseChangeIso_skyscraper x x' f hf hpq ((etPoint x' q).sheafFiber.obj G)
  rw [← cancel_mono ((skyscraperIso x p).hom.app ((etPoint x' q).sheafFiber.obj G))]
  simp only [Category.assoc, Iso.symm_hom, Functor.map_comp]
  erw [hC]
  have e1 : (smallEtalePushforwardAb f).map
      (((etPoint x' q).skyscraperSheafAdjunction.homEquiv G ((etPoint x' q).sheafFiber.obj G))
        (𝟙 ((etPoint x' q).sheafFiber.obj G)) ≫
          (skyscraperIso x' q).inv.app ((etPoint x' q).sheafFiber.obj G)) ≫
      (smallEtalePushforwardAb f).map
        ((skyscraperIso x' q).hom.app ((etPoint x' q).sheafFiber.obj G)) =
      (smallEtalePushforwardAb f).map
        (((etPoint x' q).skyscraperSheafAdjunction.homEquiv G ((etPoint x' q).sheafFiber.obj G))
          (𝟙 ((etPoint x' q).sheafFiber.obj G))) := by
    rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e1)).trans
    ((Category.assoc _ _ _).trans ((congrArg _ ((skyscraperIso x p).inv_hom_id_app _)).trans
      (Category.comp_id _))).symm

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
include hf in
theorem map_eq_of_analyticMap_eq {w : analyticSpace x'} {p : ComplexPoints x}
    (hw : analyticMap x x' f hf w = ULift.up p) : map f hf w.down = p :=
  ULift.up_injective hw

/-- The complex points of `X'` over a complex point `p` of `X` are the lifts of the geometric
point `p` to `X'`. -/
noncomputable def analyticFiberEquivLifts (p : ComplexPoints x) :
    {w : analyticSpace x' // analyticMap x x' f hf w = ULift.up p} ≃
      {t : Spec (.of ℂ) ⟶ X' // t ≫ f = p.hom} where
  toFun w := ⟨w.1.down.hom,
    hom_comp_eq_of_map_eq x x' f hf (map_eq_of_analyticMap_eq x x' f hf w.2)⟩
  invFun t := ⟨ULift.up ⟨t.1, by rw [← hf, ← Category.assoc, t.2, p.hom_comp]⟩,
    ULift.ext _ _ (ext t.2)⟩
  left_inv w := rfl
  right_inv t := rfl

/-- **The base change map is invertible for a finite morphism** whose map of complex points is
closed with finite fibres, out of a Hausdorff space. -/
theorem isIso_pushforwardBaseChange_app_of_isClosedMap [IsFinite f] [T2Space (analyticSpace x')]
    (hclosed : IsClosedMap (analyticMap x x' f hf))
    (hfin : ∀ w, (analyticMap x x' f hf ⁻¹' {w}).Finite) (G : EtSheaf X') :
    IsIso ((pushforwardBaseChange x x' f hf).app G) := by
  have hp : ∀ p : ComplexPoints x,
      Function.Bijective
        ((anPoint x p).sheafFiber.map ((pushforwardBaseChange x x' f hf).app G)) := by
    intro p
    let e := analyticFiberEquivLifts x x' f hf p
    have han := TopCat.Sheaf.bijective_pushforwardFiberComponents (analyticMap x x' f hf)
      (ULift.up p) hclosed (hfin _) ((analyticInverseImage x').obj G)
    have hs : ∀ w : {w : analyticSpace x' // analyticMap x x' f hf w = ULift.up p},
        Function.Bijective ((stalkIso x' w.1.down).hom.app G) := fun w =>
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    have h1 := (Function.Bijective.piMap hs).comp han
    have het := bijective_etalePushforwardFiberMaps f p.hom G
    have hsI : Function.Bijective ((stalkIso x p).hom.app ((smallEtalePushforwardAb f).obj G)) :=
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    have hR : Function.Bijective (fun (g : ∀ t : {t : Spec (.of ℂ) ⟶ X' // t ≫ f = p.hom},
        ToType ((pointSmallEtale t.1).sheafFiber.obj G))
        (w : {w : analyticSpace x' // analyticMap x x' f hf w = ULift.up p}) => g (e w)) :=
      (Equiv.piCongrLeft' (fun t : {t : Spec (.of ℂ) ⟶ X' // t ≫ f = p.hom} =>
        ToType ((pointSmallEtale t.1).sheafFiber.obj G)) e.symm).bijective
    have h2 := hR.comp (het.comp hsI)
    have key : ∀ z, (fun (w : {w : analyticSpace x' // analyticMap x x' f hf w = ULift.up p}) =>
        (stalkIso x' w.1.down).hom.app G (TopCat.Sheaf.pushforwardFiberComponents
          (analyticMap x x' f hf) (ULift.up p) ((analyticInverseImage x').obj G)
          ((anPoint x p).sheafFiber.map ((pushforwardBaseChange x x' f hf).app G) z) w)) =
        fun w => GrothendieckTopology.Point.pushforwardFiberMap (𝔅 f)
          (etaleBaseChangeFiberMap f (e w).1 p.hom (e w).2) G
          ((stalkIso x p).hom.app ((smallEtalePushforwardAb f).obj G) z) := fun z => funext fun w =>
      ConcreteCategory.congr_hom (sheafFiber_map_pushforwardBaseChange_comp x x' f hf
        (map_eq_of_analyticMap_eq x x' f hf w.2) G) z
    refine (Function.Bijective.of_comp_iff' h1 _).1 ?_
    exact Eq.mpr (congrArg Function.Bijective (funext key)) h2
  have : ∀ Φ : (_root_.Opens.pointsGrothendieckTopology (analyticSpace x)).FullSubcategory,
      IsIso (Φ.obj.sheafFiber.map ((pushforwardBaseChange x x' f hf).app G)) := by
    intro Φ
    obtain ⟨w, hw⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
    rw [← hw]
    exact (ConcreteCategory.isIso_iff_bijective _).2 (hp w.down)
  exact ((_root_.Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
    (analyticSpace x)).jointlyReflectIsomorphisms AddCommGrpCat.{1}).isIso _

end BaseChangeStalk

/-! ### Finite morphisms -/

section Finite

open Stacks.EtaleCohomology

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType x'] (f : X' ⟶ X) (hf : f ≫ x = x')

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
open Filter Topology in
/-- **The map of complex points of a finite morphism is closed.** -/
theorem isClosedMap_map_of_isFinite [IsFinite f] [IsSeparated x] : IsClosedMap (map f hf) := by
  refine (isProperMap_iff_ultrafilter.2 ⟨continuous_map f hf, fun 𝒰 p hp => ?_⟩).isClosedMap
  obtain ⟨pt⟩ : Nonempty (Spec (.of ℂ)) := inferInstance
  obtain ⟨U, hU, hpU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
      (show p.hom.base pt ∈ (⊤ : X.Opens) from trivial)
  have hpU' : p.Mem U := (mem_iff pt).2 hpU
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hS : Set.range (Subtype.val : {q : ComplexPoints x' // q.Mem (f ⁻¹ᵁ U)} → _) ∈ 𝒰 := by
    rw [Subtype.range_coe_subtype]
    exact hp ((isOpen_setOf_mem U).mem_nhds hpU')
  let 𝒱 := 𝒰.comap Subtype.val_injective hS
  let 𝔉 : Filter {q : ComplexPoints x' // q.Mem (f ⁻¹ᵁ U)} := 𝒱
  have h𝒱 : Tendsto (Subtype.val : {q : ComplexPoints x' // q.Mem (f ⁻¹ᵁ U)} → _)
      𝔉 (𝒰 : Filter _) := Filter.tendsto_comap
  have hfq : Tendsto (fun q : {q : ComplexPoints x' // q.Mem (f ⁻¹ᵁ U)} =>
      (⟨map f hf q.1, q.2⟩ : {r : ComplexPoints x // r.Mem U})) 𝔉 (𝓝 ⟨p, hpU'⟩) :=
    tendsto_subtype_rng.2 (hp.comp h𝒱)
  have hbound : ∀ b : Γ(X', f ⁻¹ᵁ U), ∃ R : ℝ,
      ∀ᶠ q in 𝔉, ‖evalMap (y := x') (f ⁻¹ᵁ U) q b‖ ≤ R := by
    intro b
    obtain ⟨P, hPm, hP⟩ := IsIntegralHom.isIntegral_app f U hU b
    let B : NNReal := ∑ i ∈ Finset.range P.natDegree, (‖eval (P.coeff i) p hpU'‖₊ + 1)
    refine ⟨B + 1, ?_⟩
    have hc : ∀ i ∈ Finset.range P.natDegree, ∀ᶠ q in
        𝔉,
        ‖eval (P.coeff i) (map f hf q.1) q.2‖₊ ≤ ‖eval (P.coeff i) p hpU'‖₊ + 1 := by
      intro i _
      have ht := (((continuous_eval_of_isOpen U (P.coeff i)).tendsto ⟨p, hpU'⟩).comp hfq).nnnorm
      exact ht.eventually (eventually_le_nhds (lt_add_one _))
    filter_upwards [(Filter.eventually_all_finset _).2 hc] with q hq
    have he : (evalHom q.1 q.2).comp (f.app U).hom = evalHom (map f hf q.1) q.2 :=
      RingHom.ext fun g => (eval_map_point f hf g q.1 q.2).symm
    have hroot : (P.map (evalHom (map f hf q.1) q.2)).IsRoot (evalHom q.1 q.2 b) := by
      rw [← he, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂, hP, map_zero]
    have hlt := hroot.norm_lt_cauchyBound ((hPm.map _).ne_zero)
    have hcb : Polynomial.cauchyBound (P.map (evalHom (map f hf q.1) q.2)) ≤ B + 1 := by
      unfold Polynomial.cauchyBound
      rw [(hPm.map _).leadingCoeff, nnnorm_one, div_one, hPm.natDegree_map]
      gcongr
      refine Finset.sup_le fun i hi => ?_
      rw [Polynomial.coeff_map]
      exact (hq i hi).trans (Finset.single_le_sum
        (f := fun i => ‖eval (P.coeff i) p hpU'‖₊ + 1) (fun _ _ => zero_le) hi)
    exact NNReal.coe_le_coe.2 (hlt.trans_le hcb).le
  choose R hR using hbound
  have hcoord : ∀ b, ∃ c, Tendsto (fun q => evalMap (y := x') (f ⁻¹ᵁ U) q b) 𝔉 (𝓝 c) := by
    intro b
    obtain ⟨c, -, hc⟩ := (isCompact_closedBall (0 : ℂ) (R b)).ultrafilter_le_nhds
      (𝒱.map fun q => evalMap (y := x') (f ⁻¹ᵁ U) q b)
      (Filter.le_principal_iff.2 (Ultrafilter.mem_map.2 (by
        filter_upwards [hR b] with q hq
        simpa using hq)))
    exact ⟨c, hc⟩
  choose c hc using hcoord
  have hlim : Tendsto (evalMap (y := x') (f ⁻¹ᵁ U)) 𝔉 (𝓝 c) := tendsto_pi_nhds.2 hc
  have hcl := isClosedEmbedding_evalMap (y := x') hV
  obtain ⟨q₀, rfl⟩ : c ∈ Set.range (evalMap (y := x') (f ⁻¹ᵁ U)) :=
    hcl.isClosed_range.mem_of_tendsto hlim (Filter.Eventually.of_forall fun q => ⟨q, rfl⟩)
  have hq₀ : Tendsto id 𝔉 (𝓝 q₀) := hcl.isInducing.tendsto_nhds_iff.2 hlim
  have h𝒰 : (𝒰 : Filter (ComplexPoints x')) ≤ 𝓝 q₀.1 := by
    have h1 := (continuous_subtype_val.tendsto q₀).comp hq₀
    have h2 : (𝒱.map Subtype.val : Ultrafilter (ComplexPoints x')) = 𝒰 :=
      Ultrafilter.coe_injective (Filter.map_comap_of_mem hS)
    rw [← h2]
    exact h1
  refine ⟨q₀.1, tendsto_nhds_unique ((continuous_map f hf).tendsto q₀.1 |>.mono_left h𝒰) hp, h𝒰⟩

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
theorem isClosedMap_analyticMap_of_isFinite [IsFinite f] [IsSeparated x] :
    IsClosedMap (analyticMap x x' f hf) := by
  have h := (Homeomorph.ulift.{1} (X := ComplexPoints x)).symm.isClosedMap.comp
    ((isClosedMap_map_of_isFinite x x' f hf).comp
      (Homeomorph.ulift.{1} (X := ComplexPoints x')).isClosedMap)
  exact h

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
theorem finite_preimage_analyticMap_of_isFinite [IsFinite f] (w : analyticSpace x) :
    (analyticMap x x' f hf ⁻¹' {w}).Finite := by
  have h := (finite_preimage_singleton_map f hf w.down).image (ULift.up.{1})
  refine h.subset fun z hz => ⟨z.down, ?_, rfl⟩
  have : analyticMap x x' f hf z = w := hz
  rw [← this]
  rfl

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
include hf in
theorem t2Space_analyticSpace_of_isFinite [IsFinite f] [IsSeparated x] :
    T2Space (analyticSpace x') := by
  have : IsSeparated x' := hf ▸ inferInstance
  exact inferInstanceAs (T2Space (ULift (ComplexPoints x')))

/-- **For a finite morphism, the base change map `ε^* f_* G ⟶ f_an,* ε'^* G` is an
isomorphism.** -/
theorem isIso_pushforwardBaseChange_of_isFinite [IsFinite f] [IsSeparated x] (G : EtSheaf X') :
    IsIso ((pushforwardBaseChange x x' f hf).app G) :=
  have := t2Space_analyticSpace_of_isFinite x x' f hf
  isIso_pushforwardBaseChange_app_of_isClosedMap x x' f hf
    (isClosedMap_analyticMap_of_isFinite x x' f hf)
    (finite_preimage_analyticMap_of_isFinite x x' f hf) G

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
instance preservesFiniteColimits_smallEtalePushforwardAb_of_isFinite [IsFinite f] :
    PreservesFiniteColimits (smallEtalePushforwardAb f) :=
  (smallEtalePushforwardAb_exact_of_isIntegralHom f).2

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
theorem preservesFiniteColimits_analyticPushforward_of_isFinite [IsFinite f] [IsSeparated x] :
    PreservesFiniteColimits (analyticPushforward x x' f hf) := by
  have := t2Space_analyticSpace_of_isFinite x x' f hf
  have := TopCat.Sheaf.preservesEpimorphisms_pushforwardAb (analyticMap x x' f hf)
    (isClosedMap_analyticMap_of_isFinite x x' f hf)
    (finite_preimage_analyticMap_of_isFinite x x' f hf)
  have : (analyticPushforward x x' f hf).PreservesEpimorphisms := this
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (analyticPushforward x x' f hf)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

include hf in
/-- **The comparison map along a finite morphism**: for `f : X' ⟶ X` finite over `ℂ` and `X`
separated, `c^n(X, f_* G)` is bijective if and only if `c^n(X', G)` is. -/
theorem comparisonMap_pushforward_bijective_iff [IsFinite f] [IsSeparated x] (G : EtSheaf X')
    (n : ℕ) :
    Function.Bijective (comparisonMap x ((smallEtalePushforwardAb f).obj G) n) ↔
      Function.Bijective (comparisonMap x' G n) := by
  have := preservesFiniteColimits_analyticPushforward_of_isFinite x x' f hf
  have := isIso_pushforwardBaseChange_of_isFinite x x' f hf G
  exact comparisonMap_pushforward_bijective_iff_of_isIso x x' f hf G n

omit [LocallyOfFiniteType x] in
/-- A complex point of a separated scheme over `ℂ` is a closed immersion. -/
theorem isClosedImmersion_hom [IsSeparated x] (p : ComplexPoints x) : IsClosedImmersion p.hom := by
  have e : p.hom = pullback.lift (𝟙 _) p.hom (Category.id_comp (p.hom ≫ x)) ≫
      pullback.snd (p.hom ≫ x) x := (pullback.lift_snd _ _ _).symm
  have : IsIso (p.hom ≫ x) := by rw [p.hom_comp]; infer_instance
  rw [e]
  infer_instance

/-- **The comparison map on the direct image along a complex point** `p : Spec ℂ ⟶ X` of a
separated scheme: `c^n(X, p_* G)` is bijective for every abelian sheaf `G` on `Spec ℂ`. -/
theorem comparisonMap_pushforward_point_bijective [IsSeparated x] (p : ComplexPoints x)
    (G : EtSheaf (Spec (.of ℂ))) (n : ℕ) :
    Function.Bijective (comparisonMap x ((smallEtalePushforwardAb p.hom).obj G) n) := by
  have := isClosedImmersion_hom x p
  rw [comparisonMap_pushforward_bijective_iff x (𝟙 _) p.hom p.hom_comp G n]
  exact comparisonBijectiveOn_spec G trivial n

end Finite

end AlgebraicGeometry.Scheme.ComplexPoints
