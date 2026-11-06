module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import Weil.Defs.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringIsomorphism
public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ForgetfulFunctors
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct

/-!
# Extending Galois covering spaces from the closed fibre

Let `A` be a henselian local ring with maximal ideal `𝔪`, `X` a proper `A`-scheme, `X₀ = X ⊗_A A/𝔪`
its closed fibre and `F` a finite group. Every `F`-Galois covering space `Y₀ → X₀` extends to an
`F`-Galois covering space `Y → X`: there is one with `Y ×_X X₀ ≅ Y₀` as `F`-Galois covering spaces
of `X₀`.

A Galois covering space with finite group is finite étale, since it becomes the trivial covering
`∐_{σ ∈ F} Y₀ → Y₀` after the surjective étale base change `Y₀ → X₀`. Base change
`FÉt_X ⥤ FÉt_{X₀}` is an equivalence of categories (Stacks, Tag 0A48), so `Y₀` comes from a finite
étale `X`-scheme `Y`, the action of `F` transports to `Y` by full faithfulness, and the Galois
condition on `Y` follows from the one on `Y₀`: the morphism `∐_{σ ∈ F} Y → Y ×_X Y` is built from a
coproduct and a product in `FÉt_X`, which the equivalence preserves, and an equivalence reflects
isomorphisms. Surjectivity of `Y → X` holds because its image is open and every point of `X`
specializes into the closed fibre.

## Main definitions

* `CategoryTheory.Limits.cofanToFanMap` — in any category, the morphism `∐_{σ ∈ F} Y → Y × Y`
  which is `(ρ σ, 𝟙)` on the summand indexed by `σ`, for given colimit cofan and limit fan.
* `AlgebraicGeometry.finiteEtalePullbackFan` — the fibre product `P ×_S P` as a product in
  `FÉt_S`.

## Main results

* `AlgebraicGeometry.exists_galoisCovering_pullback_closedFibre_iso` — the extension of Galois
  covering spaces from the closed fibre of a proper scheme over a henselian local ring.
* `AlgebraicGeometry.IsGaloisCovering.isFinite` — a Galois covering space with finite group is
  finite.
* `CategoryTheory.Limits.isIso_cofanToFanMap_iff` — a functor reflecting isomorphisms and
  preserving the cofan and the fan detects whether `cofanToFanMap` is an isomorphism.

## Implementation notes

FK state the result for a strictly henselian noetherian `A` which is admissible (a strict
henselization of a finitely generated `ℤ`-algebra at a prime), `X` projective over `A` and
`F = ℤ/nℤ`, and prove it by Artin approximation from the complete case. The statement here holds
for every henselian local ring, every proper `X` and every finite group `F`, which contains FK's
case; the proof is the one of Stacks, through Tag 0A48, and needs neither admissibility nor
Artin approximation. The closed fibre is `X ×_{Spec A} Spec (A/𝔪)` and the isomorphism
`Y ×_X X₀ ≅ Y₀` of `F`-Galois covering spaces is an `X₀`-isomorphism of the base change
`(Over.pullback i).obj Y` along `i : X₀ → X` compatible with the actions of `F`, which is
`AlgebraicGeometry.GaloisCovering.isoEquiv`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1, pp. 63–64.
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {F : Type*} {Y : C}

/-- The morphism `∐_{σ ∈ F} Y → Y × Y` which is `(ρ σ, 𝟙)` on the summand indexed by `σ`, for a
colimit cofan and a limit binary fan. -/
def cofanToFanMap {c : Cofan fun _ : F ↦ Y} (hc : IsColimit c) {p : BinaryFan Y Y}
    (hp : IsLimit p) (ρ : F → (Y ⟶ Y)) : c.pt ⟶ p.pt :=
  Cofan.IsColimit.desc hc fun σ ↦ hp.lift (BinaryFan.mk (ρ σ) (𝟙 Y))

@[reassoc (attr := simp)]
lemma inj_cofanToFanMap_fst {c : Cofan fun _ : F ↦ Y} (hc : IsColimit c) {p : BinaryFan Y Y}
    (hp : IsLimit p) (ρ : F → (Y ⟶ Y)) (σ : F) :
    c.inj σ ≫ cofanToFanMap hc hp ρ ≫ p.fst = ρ σ := by
  rw [cofanToFanMap, Cofan.IsColimit.fac_assoc]
  exact hp.fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
lemma inj_cofanToFanMap_snd {c : Cofan fun _ : F ↦ Y} (hc : IsColimit c) {p : BinaryFan Y Y}
    (hp : IsLimit p) (ρ : F → (Y ⟶ Y)) (σ : F) :
    c.inj σ ≫ cofanToFanMap hc hp ρ ≫ p.snd = 𝟙 Y := by
  rw [cofanToFanMap, Cofan.IsColimit.fac_assoc]
  exact hp.fac _ ⟨WalkingPair.right⟩

variable {D : Type*} [Category* D]

/-- A functor reflecting isomorphisms and preserving the cofan and the fan detects whether
`cofanToFanMap` is an isomorphism, after transport along an equivariant isomorphism. -/
theorem isIso_cofanToFanMap_iff (G : C ⥤ D) [G.ReflectsIsomorphisms] {Y' : D}
    (e : G.obj Y ≅ Y') (ρ : F → (Y ⟶ Y)) (ρ' : F → (Y' ⟶ Y'))
    (hρ : ∀ σ, G.map (ρ σ) ≫ e.hom = e.hom ≫ ρ' σ)
    {c : Cofan fun _ : F ↦ Y} (hc : IsColimit c) {p : BinaryFan Y Y} (hp : IsLimit p)
    (hcG : IsColimit (G.mapCocone c)) (hpG : IsLimit (G.mapCone p))
    {c' : Cofan fun _ : F ↦ Y'} (hc' : IsColimit c') {p' : BinaryFan Y' Y'} (hp' : IsLimit p') :
    IsIso (cofanToFanMap hc hp ρ) ↔ IsIso (cofanToFanMap hc' hp' ρ') := by
  let α : G.obj c.pt ≅ c'.pt :=
    IsColimit.coconePointsIsoOfNatIso hcG hc' (Discrete.natIso fun _ ↦ e)
  let β : G.obj p.pt ≅ p'.pt :=
    IsLimit.conePointsIsoOfNatIso hpG hp' (mapPairIso e e)
  have key : G.map (cofanToFanMap hc hp ρ) ≫ β.hom = α.hom ≫ cofanToFanMap hc' hp' ρ' := by
    refine hcG.hom_ext fun ⟨σ⟩ ↦ ?_
    have hα : (G.mapCocone c).ι.app ⟨σ⟩ ≫ α.hom = e.hom ≫ c'.inj σ :=
      IsColimit.comp_coconePointsIsoOfNatIso_hom _ _ _ _
    rw [reassoc_of% hα]
    refine BinaryFan.IsLimit.hom_ext hp' ?_ ?_
    · have hβ : β.hom ≫ p'.fst = G.map p.fst ≫ e.hom :=
        IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)
      simp only [Functor.mapCocone_ι_app, Category.assoc, hβ, inj_cofanToFanMap_fst]
      rw [← G.map_comp_assoc, ← G.map_comp_assoc]
      rw [Category.assoc]
      change G.map (c.inj σ ≫ cofanToFanMap hc hp ρ ≫ p.fst) ≫ e.hom = _
      rw [inj_cofanToFanMap_fst, hρ]
    · have hβ : β.hom ≫ p'.snd = G.map p.snd ≫ e.hom :=
        IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)
      simp only [Functor.mapCocone_ι_app, Category.assoc, hβ, inj_cofanToFanMap_snd]
      rw [← G.map_comp_assoc, ← G.map_comp_assoc]
      rw [Category.assoc]
      change G.map (c.inj σ ≫ cofanToFanMap hc hp ρ ≫ p.snd) ≫ e.hom = _
      rw [inj_cofanToFanMap_snd, G.map_id, Category.id_comp, Category.comp_id]
  have hG : G.map (cofanToFanMap hc hp ρ) = (α.hom ≫ cofanToFanMap hc' hp' ρ') ≫ β.inv := by
    rw [← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  constructor
  · intro h
    have : IsIso (α.hom ≫ cofanToFanMap hc' hp' ρ') := by
      rw [← key]; infer_instance
    exact IsIso.of_isIso_comp_left α.hom _
  · intro h
    have : IsIso (G.map (cofanToFanMap hc hp ρ)) := by rw [hG]; infer_instance
    exact isIso_of_reflects_iso _ G

end CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/-- The fibre product `P ×_S P` of a finite étale `S`-scheme with itself, as a binary fan in the
category of finite étale `S`-schemes. -/
def finiteEtalePullbackFan (P : FiniteEtaleOver S) : BinaryFan P P :=
  BinaryFan.mk (P := MorphismProperty.Over.mk ⊤ (pullback.fst P.hom P.hom ≫ P.hom)
      (finiteEtale.comp_mem _ _ (finiteEtale.pullback_fst _ _ P.prop) P.prop))
    (MorphismProperty.Over.homMk (pullback.fst P.hom P.hom) rfl)
    (MorphismProperty.Over.homMk (pullback.snd P.hom P.hom) pullback.condition.symm)

/-- The fibre product `P ×_S P` is the product of `P` with itself in the category of finite étale
`S`-schemes. -/
def isLimitFiniteEtalePullbackFan (P : FiniteEtaleOver S) :
    IsLimit (finiteEtalePullbackFan P) :=
  BinaryFan.IsLimit.mk _
    (fun {T} a b ↦ MorphismProperty.Over.homMk
      (pullback.lift a.left b.left (by rw [MorphismProperty.Over.w, MorphismProperty.Over.w]))
      (by
        change _ ≫ pullback.fst P.hom P.hom ≫ P.hom = _
        rw [pullback.lift_fst_assoc, MorphismProperty.Over.w]))
    (fun a b ↦ MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _))
    (fun a b ↦ MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _))
    (fun a b m h₁ h₂ ↦ MorphismProperty.Over.Hom.ext (pullback.hom_ext
      ((congrArg (fun k ↦ k.left) h₁).trans (pullback.lift_fst _ _ _).symm)
      ((congrArg (fun k ↦ k.left) h₂).trans (pullback.lift_snd _ _ _).symm)))

variable {F : Type u} [Group F] [Finite F]

/-- For a finite étale `S`-scheme `P` with an action of `F`, the morphism `cofanToFanMap` of the
category of finite étale `S`-schemes, built from the disjoint union and the fibre product, is an
isomorphism exactly when `galoisCoveringMap` is. -/
theorem isIso_cofanToFanMap_iff_isIso_galoisCoveringMap (P : FiniteEtaleOver S)
    (ρP : F → (P ⟶ P)) (ρ : F →* Aut ((MorphismProperty.Over.forget _ ⊤ S).obj P))
    (h : ∀ σ, (ρP σ).left = (ρ σ).hom.left) :
    IsIso (cofanToFanMap (Stacks.FundamentalGroup.isColimitSigmaCocone S
        (Discrete.functor fun _ : F ↦ P)) (isLimitFiniteEtalePullbackFan P) ρP) ↔
      IsIso (galoisCoveringMap ((MorphismProperty.Over.forget _ ⊤ S).obj P) ρ) := by
  set m := cofanToFanMap (Stacks.FundamentalGroup.isColimitSigmaCocone S
    (Discrete.functor fun _ : F ↦ P)) (isLimitFiniteEtalePullbackFan P) ρP
  have hm : m.left = galoisCoveringMap ((MorphismProperty.Over.forget _ ⊤ S).obj P) ρ := by
    refine Sigma.hom_ext _ _ fun σ ↦ pullback.hom_ext ?_ ?_
    · have := congrArg (fun k ↦ k.left)
        (inj_cofanToFanMap_fst (Stacks.FundamentalGroup.isColimitSigmaCocone S
          (Discrete.functor fun _ : F ↦ P)) (isLimitFiniteEtalePullbackFan P) ρP σ)
      simp only [MorphismProperty.Comma.comp_left] at this
      exact ((Category.assoc _ _ _).trans this).trans ((h σ).trans
        ((ι_galoisCoveringMap_fst _ ρ σ).symm.trans (Category.assoc _ _ _).symm))
    · have := congrArg (fun k ↦ k.left)
        (inj_cofanToFanMap_snd (Stacks.FundamentalGroup.isColimitSigmaCocone S
          (Discrete.functor fun _ : F ↦ P)) (isLimitFiniteEtalePullbackFan P) ρP σ)
      simp only [MorphismProperty.Comma.comp_left] at this
      exact ((Category.assoc _ _ _).trans this).trans
        ((ι_galoisCoveringMap_snd _ ρ σ).symm.trans (Category.assoc _ _ _).symm)
  rw [← hm]
  constructor
  · intro _
    exact (inferInstance : IsIso
      ((MorphismProperty.Over.forget _ ⊤ S ⋙ CategoryTheory.Over.forget S).map m))
  · intro hl
    have : IsIso ((MorphismProperty.Over.forget _ ⊤ S ⋙ CategoryTheory.Over.forget S).map m) := hl
    exact isIso_of_reflects_iso m
      (MorphismProperty.Over.forget _ ⊤ S ⋙ CategoryTheory.Over.forget S)

/-- The structure morphism of an `F`-Galois covering space, `F` finite, is finite: after the base
change along itself, which is surjective, flat and locally of finite presentation, it becomes the
projection `∐_{σ ∈ F} Y → Y`, and finiteness descends along such morphisms. -/
theorem IsGaloisCovering.isFinite {Y : Over S} {ρ : F →* Aut Y} (h : IsGaloisCovering Y ρ) :
    IsFinite Y.hom := by
  have := h.etale
  have := h.surjective
  have := h.isIso_galoisCoveringMap
  have := isFinite_descendsAlong_fppf.{u}
  have e₁ : galoisCoveringMap Y ρ ≫ pullback.fst Y.hom Y.hom =
      Sigma.desc fun σ ↦ (ρ σ).hom.left :=
    Sigma.hom_ext _ _ fun σ ↦ by simp
  have e₂ : pullback.fst Y.hom Y.hom =
      inv (galoisCoveringMap Y ρ) ≫ Sigma.desc fun σ ↦ (ρ σ).hom.left := by
    rw [← e₁, IsIso.inv_hom_id_assoc]
  have hfst : IsFinite (pullback.fst Y.hom Y.hom) := by
    rw [e₂]
    have : ∀ σ : F, IsFinite (ρ σ).hom.left := fun σ ↦
      have : IsIso (ρ σ).hom.left := Iso.isIso_hom ((Over.forget S).mapIso (ρ σ))
      inferInstance
    have : IsFinite (Sigma.desc fun σ ↦ (ρ σ).hom.left) := isFinite_sigmaDesc
    infer_instance
  exact MorphismProperty.of_pullback_fst_of_descendsAlong (P := @IsFinite)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) (f := Y.hom)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfst

open IsLocalRing in
/-- **FK I.6.1, proof, case `i = 1`.** Let `A` be a henselian local ring with maximal ideal `𝔪`,
`X` a proper `A`-scheme with closed fibre `X₀ = X ×_{Spec A} Spec (A/𝔪)`, and `F` a finite group.
For every `F`-Galois covering space `Y₀` of `X₀` there is an `F`-Galois covering space `Y` of `X`
with `Y ×_X X₀ ≅ Y₀` as `F`-Galois covering spaces of `X₀`: an `X₀`-isomorphism compatible with
the actions of `F`. -/
@[weil "lem_fk106_galois_covering_extends_admissible_base"]
theorem exists_galoisCovering_pullback_closedFibre_iso (A : Type u) [CommRing A]
    [HenselianLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (Y₀ : GaloisCovering
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A))))) F) :
    ∃ (Y : GaloisCovering X F)
      (e : (Over.pullback (pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))))).obj Y.over ≅
        Y₀.over),
      ∀ σ : F, (Over.pullback _).mapIso (Y.act σ) ≪≫ e = e ≪≫ Y₀.act σ := by
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A))))
  let E := finiteEtaleBaseChange i
  have : E.IsEquivalence :=
    isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing A f
  let X₀ := pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A))))
  let U := MorphismProperty.Over.forget finiteEtale ⊤ X
  let U₀ := MorphismProperty.Over.forget finiteEtale ⊤ X₀
  have hY₀ := Y₀.isGaloisCovering
  have := hY₀.surjective
  let P₀ : FiniteEtaleOver X₀ :=
    MorphismProperty.Over.mk ⊤ Y₀.over.hom ⟨hY₀.isFinite, hY₀.etale⟩
  let P := E.objPreimage P₀
  let e : E.obj P ≅ P₀ := E.objObjPreimageIso P₀
  let hffE : E.FullyFaithful := .ofFullyFaithful E
  let hff₀ : U₀.FullyFaithful := .ofFullyFaithful U₀
  let ρ₀ : F →* Aut P₀ := (hff₀.autMulEquivOfFullyFaithful P₀).symm.toMonoidHom.comp Y₀.act
  let ρP : F →* Aut P := (hffE.autMulEquivOfFullyFaithful P).symm.toMonoidHom.comp
    (e.symm.conjAut.toMonoidHom.comp ρ₀)
  let ρ : F →* Aut (U.obj P) := (U.mapAut P).comp ρP
  have hρE : ∀ σ, E.map (ρP σ).hom ≫ e.hom = e.hom ≫ (ρ₀ σ).hom := by
    intro σ
    have h₁ : E.mapIso (ρP σ) = e.symm.conjAut (ρ₀ σ) :=
      (hffE.autMulEquivOfFullyFaithful P).apply_symm_apply _
    have h₂ : E.map (ρP σ).hom = e.hom ≫ (ρ₀ σ).hom ≫ e.inv := by
      have := congrArg Iso.hom h₁
      rw [Iso.conjAut_apply] at this
      change E.map (ρP σ).hom = e.hom ≫ (ρ₀ σ ≪≫ e.symm).hom at this
      rw [this]; rfl
    rw [h₂]
    simp
  have hρ₀ : ∀ σ, U₀.map (ρ₀ σ).hom = (Y₀.act σ).hom := fun σ ↦
    congrArg Iso.hom ((hff₀.autMulEquivOfFullyFaithful P₀).apply_symm_apply (Y₀.act σ))
  have hgal : IsGaloisCovering (U.obj P) ρ := by
    have hetale : Etale P.hom := P.prop.2
    refine ⟨hetale, ?_, ?_⟩
    · -- surjectivity
      have hsurj₀ : Surjective (E.obj P).hom := by
        rw [← MorphismProperty.Over.w e.hom]
        change Surjective (e.hom.left ≫ Y₀.over.hom)
        have : IsIso e.hom.left := Iso.isIso_hom ((MorphismProperty.Over.forget _ ⊤ X₀ ⋙
          CategoryTheory.Over.forget X₀).mapIso e)
        exact ⟨hY₀.surjective.surj.comp e.hom.left.homeomorph.surjective⟩
      refine ⟨fun x ↦ ?_⟩
      have hI : maximalIdeal A ≤ (⊥ : Ideal A).jacobson := by
        rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      obtain ⟨x', ⟨z, rfl⟩, hsp⟩ :=
        exists_specializes_mem_range_pullback_fst_of_isProper A hI f x
      obtain ⟨w, hw⟩ := hsurj₀.surj z
      have hx' : i.base z ∈ Set.range P.hom.base := by
        refine ⟨(pullback.fst P.hom i).base w, ?_⟩
        change (pullback.snd P.hom i).base w = z at hw
        rw [← hw]
        exact (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg
          (fun g : pullback P.hom i ⟶ X ↦ g w) pullback.condition).trans
          (Scheme.Hom.comp_apply _ _ _))
      exact hsp.mem_open P.hom.isOpenMap.isOpen_range hx'
    · refine (isIso_cofanToFanMap_iff_isIso_galoisCoveringMap P (fun σ ↦ (ρP σ).hom) ρ
        (fun σ ↦ rfl)).mp ?_
      let hc := Stacks.FundamentalGroup.isColimitSigmaCocone X (Discrete.functor fun _ : F ↦ P)
      let hp := isLimitFiniteEtalePullbackFan P
      refine (isIso_cofanToFanMap_iff E e (fun σ ↦ (ρP σ).hom) (fun σ ↦ (ρ₀ σ).hom) hρE hc hp
        (isColimitOfPreserves E hc) (isLimitOfPreserves E hp)
        (Stacks.FundamentalGroup.isColimitSigmaCocone X₀ (Discrete.functor fun _ : F ↦ P₀))
        (isLimitFiniteEtalePullbackFan P₀)).mpr ?_
      exact (isIso_cofanToFanMap_iff_isIso_galoisCoveringMap P₀ (fun σ ↦ (ρ₀ σ).hom) Y₀.act
        fun σ ↦ congrArg (fun k ↦ k.left) (hρ₀ σ)).mpr hY₀.isIso_galoisCoveringMap
  refine ⟨GaloisCovering.of (U.obj P) ρ hgal,
    ((Stacks.FundamentalGroup.finiteEtaleBaseChangeForgetIso i).app P).symm ≪≫ U₀.mapIso e,
    fun σ ↦ ?_⟩
  ext : 1
  have h₃ : U₀.map (E.map (ρP σ).hom) ≫ U₀.map e.hom = U₀.map e.hom ≫ (Y₀.act σ).hom := by
    rw [← U₀.map_comp, hρE, U₀.map_comp, hρ₀]
    rfl
  simp only [GaloisCovering.of_act]
  exact h₃

end AlgebraicGeometry

/-! ### Galois covering spaces of the closed fibre extend over a henselian base -/

/-!
# Galois covering spaces of the closed fibre extend over a henselian base

Let `A` be a henselian local ring with maximal ideal `𝔪`, let `X` be a proper scheme over
`Spec A` and `X₀ = X ×_{Spec A} Spec (A ⧸ 𝔪)` its closed fibre. For a finite group `F`, every
`F`-Galois covering space `Y₁ → X₀` is, up to isomorphism of `F`-Galois covering spaces, the
base change `Y ×_X X₀` of an `F`-Galois covering space `Y → X`.

The proof uses that base change `FÉt_X ⥤ FÉt_{X₀}` is an equivalence of categories
(Stacks, Tag 0A48). A Galois covering space with finite group is finite (its square
`Y₁ ×_{X₀} Y₁ ≅ ∐_{σ ∈ F} Y₁` is finite over `Y₁`, and finiteness descends along the fppf
covering `Y₁ → X₀`), so `Y₁` comes from a finite étale `Y → X`. The action of `F` is
transported along the equivalence, and so is the condition that `∐_{σ ∈ F} Y → Y ×_X Y` is
an isomorphism, since the equivalence and the forgetful functors preserve finite coproducts and
binary products. Surjectivity of `Y → X` follows because its image is open and contains the
closed fibre, into which every point of `X` specializes.

## Main definitions

* `CategoryTheory.Limits.sigmaLiftProd a` — for a family `a` of endomorphisms of `Y`, the
  morphism `∐_i Y → Y ⨯ Y` given on the copy indexed by `i` by `(a i, 𝟙)`.

## Main results

* `AlgebraicGeometry.GaloisCovering.exists_pullback_closedFibre_iso`: an `F`-Galois covering
  space of the closed fibre of a proper scheme over a henselian local ring extends to an
  `F`-Galois covering space of the scheme.
* `AlgebraicGeometry.GaloisCovering.isFinite_hom`: a Galois covering space with finite group
  is finite.

## Implementation notes

The source states the result for a noetherian strictly Henselian local ring `A`, a projective
`X → Spec A` and the group `ℤ/nℤ` with `n` invertible in `A`. It is proved here for any
henselian local ring, any proper `X` and any finite group: none of the extra hypotheses is used.
The source's proof goes through Artin approximation over admissible rings; here Tag 0A48 is
used instead.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6, pp. 63–64.
* [Stacks Project, Tag 0A48](https://stacks.math.columbia.edu/tag/0A48)
-/

@[expose] public noncomputable section

open CategoryTheory Limits IsLocalRing

universe u

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] {ι : Type*}

/-- For a family `a` of endomorphisms of `Y`, the morphism `∐_i Y → Y ⨯ Y` given on the copy
indexed by `i` by `(a i, 𝟙 Y)`. -/
def sigmaLiftProd {Y : C} [HasCoproduct fun _ : ι ↦ Y] [HasBinaryProduct Y Y]
    (a : ι → (Y ⟶ Y)) : (∐ fun _ : ι ↦ Y) ⟶ Y ⨯ Y :=
  Sigma.desc fun i ↦ prod.lift (a i) (𝟙 Y)

@[reassoc (attr := simp)]
lemma ι_sigmaLiftProd {Y : C} [HasCoproduct fun _ : ι ↦ Y] [HasBinaryProduct Y Y]
    (a : ι → (Y ⟶ Y)) (i : ι) :
    Sigma.ι (fun _ : ι ↦ Y) i ≫ sigmaLiftProd a = prod.lift (a i) (𝟙 Y) :=
  Sigma.ι_desc _ _

/-- A functor carries `sigmaLiftProd` to `sigmaLiftProd`, up to the comparison maps for
coproducts and binary products. -/
lemma sigmaComparison_map_sigmaLiftProd_prodComparison (G : C ⥤ D) {Y : C}
    [HasCoproduct fun _ : ι ↦ Y] [HasBinaryProduct Y Y]
    [HasCoproduct fun _ : ι ↦ G.obj Y] [HasBinaryProduct (G.obj Y) (G.obj Y)]
    (a : ι → (Y ⟶ Y)) :
    sigmaComparison G (fun _ : ι ↦ Y) ≫ G.map (sigmaLiftProd a) ≫ prodComparison G Y Y =
      sigmaLiftProd fun i ↦ G.map (a i) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [ι_comp_sigmaComparison_assoc, ← G.map_comp_assoc, ι_sigmaLiftProd, ι_sigmaLiftProd]
  ext <;> simp [← G.map_comp]

/-- A functor preserving the coproduct and the binary product, and reflecting isomorphisms,
preserves and reflects the property that `sigmaLiftProd` is an isomorphism. -/
lemma isIso_sigmaLiftProd_map_iff (G : C ⥤ D) [G.ReflectsIsomorphisms] {Y : C}
    [HasCoproduct fun _ : ι ↦ Y] [HasBinaryProduct Y Y]
    [HasCoproduct fun _ : ι ↦ G.obj Y] [HasBinaryProduct (G.obj Y) (G.obj Y)]
    [PreservesColimit (Discrete.functor fun _ : ι ↦ Y) G] [PreservesLimit (pair Y Y) G]
    (a : ι → (Y ⟶ Y)) :
    IsIso (sigmaLiftProd fun i ↦ G.map (a i)) ↔ IsIso (sigmaLiftProd a) := by
  rw [← sigmaComparison_map_sigmaLiftProd_prodComparison, isIso_comp_left_iff,
    isIso_comp_right_iff]
  exact ⟨fun _ ↦ isIso_of_reflects_iso _ G, fun _ ↦ inferInstance⟩

/-- `sigmaLiftProd` is an isomorphism for one family if and only if it is for a family
conjugate to it by an isomorphism. -/
lemma isIso_sigmaLiftProd_iff_of_iso {Y Y' : C} [HasCoproduct fun _ : ι ↦ Y]
    [HasBinaryProduct Y Y] [HasCoproduct fun _ : ι ↦ Y'] [HasBinaryProduct Y' Y']
    (e : Y ≅ Y') {a : ι → (Y ⟶ Y)} {a' : ι → (Y' ⟶ Y')} (h : ∀ i, a i ≫ e.hom = e.hom ≫ a' i) :
    IsIso (sigmaLiftProd a) ↔ IsIso (sigmaLiftProd a') := by
  let s : (∐ fun _ : ι ↦ Y) ≅ ∐ fun _ : ι ↦ Y' :=
    { hom := Sigma.desc fun i ↦ e.hom ≫ Sigma.ι (fun _ : ι ↦ Y') i
      inv := Sigma.desc fun i ↦ e.inv ≫ Sigma.ι (fun _ : ι ↦ Y) i
      hom_inv_id := Sigma.hom_ext _ _ fun i ↦ by simp
      inv_hom_id := Sigma.hom_ext _ _ fun i ↦ by simp }
  have : IsIso s.hom := s.isIso_hom
  have key : s.hom ≫ sigmaLiftProd a' = sigmaLiftProd a ≫ (prod.mapIso e e).hom := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    simp only [s, Sigma.ι_desc_assoc, Category.assoc, ι_sigmaLiftProd, ι_sigmaLiftProd_assoc,
      prod.mapIso_hom]
    ext <;> simp [h]
  constructor
  · intro _
    have : IsIso (s.hom ≫ sigmaLiftProd a') := by
      rw [key]; infer_instance
    exact IsIso.of_isIso_comp_left s.hom _
  · intro _
    have : IsIso (sigmaLiftProd a ≫ (prod.mapIso e e).hom) := by
      rw [← key]; infer_instance
    exact IsIso.of_isIso_comp_right _ (prod.mapIso e e).hom

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {F : Type u} [Group F]

/-- The morphism `∐_{σ ∈ F} Y → Y ×_X Y` defining Galois covering spaces is, up to the
identification of `(Y ⨯ Y).left` with `Y ×_X Y`, the morphism `sigmaLiftProd` of `Over X`. -/
lemma sigmaComparison_sigmaLiftProd_left_prodLeftIsoPullback (Y : Over X) (ρ : F →* Aut Y) :
    sigmaComparison (Over.forget X) (fun _ : F ↦ Y) ≫
        (sigmaLiftProd fun σ ↦ (ρ σ).hom).left ≫ (Over.prodLeftIsoPullback Y Y).hom =
      galoisCoveringMap Y ρ := by
  refine Sigma.hom_ext _ _ fun σ ↦ ?_
  rw [ι_comp_sigmaComparison_assoc, Over.forget_map, ← Over.comp_left_assoc,
    ι_sigmaLiftProd]
  apply pullback.hom_ext
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.lift_fst]
    exact (ι_galoisCoveringMap_fst Y ρ σ).symm
  · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.lift_snd,
      Over.id_left]
    exact (ι_galoisCoveringMap_snd Y ρ σ).symm

lemma isIso_galoisCoveringMap_iff_isIso_sigmaLiftProd [Finite F] (Y : Over X)
    (ρ : F →* Aut Y) :
    IsIso (galoisCoveringMap Y ρ) ↔ IsIso (sigmaLiftProd fun σ ↦ (ρ σ).hom) := by
  rw [← sigmaComparison_sigmaLiftProd_left_prodLeftIsoPullback]
  have : IsIso (sigmaComparison (Over.forget X) fun _ : F ↦ Y) := inferInstance
  rw [isIso_comp_left_iff, isIso_comp_right_iff]
  refine ⟨fun h ↦ ?_, fun _ ↦ (Over.forget X).map_isIso _⟩
  have : IsIso ((Over.forget X).map (sigmaLiftProd fun σ ↦ (ρ σ).hom)) := h
  exact isIso_of_reflects_iso _ (Over.forget X)

namespace GaloisCovering

/-- An `F`-Galois covering space with `F` finite is finite: `Y ×_X Y ≅ ∐_{σ ∈ F} Y` is finite
over `Y`, and finiteness descends along the fppf covering `Y → X`. -/
lemma isFinite_hom [Finite F] (Y : GaloisCovering X F) : IsFinite Y.over.hom := by
  have hY := Y.isGaloisCovering
  have _ := hY.etale
  have _ := hY.isIso_galoisCoveringMap
  have : MorphismProperty.DescendsAlong (@IsFinite) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    Space.isFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have : IsZariskiLocalAtTarget @IsFinite.{u} := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  have : MorphismProperty.DescendsAlong (@IsFinite)
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  have : ∀ σ, IsFinite (Y.act σ).hom.left := fun σ ↦ by
    have : IsIso (Y.act σ).hom.left := ((Over.forget X).mapIso (Y.act σ)).isIso_hom
    infer_instance
  have : IsFinite (inv (galoisCoveringMap Y.over Y.act)) := inferInstance
  have hfst : pullback.fst Y.over.hom Y.over.hom =
      inv (galoisCoveringMap Y.over Y.act) ≫
        Sigma.desc fun σ ↦ (Y.act σ).hom.left := by
    rw [IsIso.eq_inv_comp]
    exact Sigma.hom_ext _ _ fun σ ↦ by simp
  have : IsFinite (pullback.fst Y.over.hom Y.over.hom) := by
    rw [hfst]; infer_instance
  exact MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    ⟨⟨hY.surjective, inferInstance⟩, inferInstance⟩ this

/-- Let `j : X₀ → X` be a morphism such that base change `FÉt_X ⥤ FÉt_{X₀}` is an equivalence
and every point of `X` specializes to a point in the image of `j`, and let `F` be a finite
group. Every `F`-Galois covering space `Y₁` of `X₀` is isomorphic, as an `F`-Galois covering
space, to the base change `Y ×_X X₀` of an `F`-Galois covering space `Y` of `X`. -/
theorem exists_pullback_iso_of_isEquivalence [Finite F] {X₀ : Scheme.{u}} (j : X₀ ⟶ X)
    [(finiteEtaleBaseChange j).IsEquivalence] (hsp : ∀ x : X, ∃ x' ∈ Set.range j, x ⤳ x')
    (Y₁ : GaloisCovering X₀ F) :
    ∃ (Y : GaloisCovering X F) (e : (Over.pullback j).obj Y.over ≅ Y₁.over),
      ∀ σ : F, (Over.pullback j).mapIso (Y.act σ) ≪≫ e = e ≪≫ Y₁.act σ := by
  have := Fintype.ofFinite F
  let E := finiteEtaleBaseChange j
  have := preservesFiniteColimits_finiteEtaleOverForgetOver X
  have := preservesFiniteColimits_finiteEtaleOverForgetOver X₀
  have := preservesFiniteLimits_finiteEtaleOverForgetOver X
  have := preservesFiniteLimits_finiteEtaleOverForgetOver X₀
  let U := finiteEtaleOverForgetOver X
  let U₁ := finiteEtaleOverForgetOver X₀
  obtain ⟨P₁, ⟨eY⟩⟩ : ∃ P₁ : FiniteEtaleOver X₀, Nonempty (U₁.obj P₁ ≅ Y₁.over) :=
    ⟨MorphismProperty.Over.mk ⊤ Y₁.over.hom ⟨Y₁.isFinite_hom, Y₁.isGaloisCovering.etale⟩,
      ⟨Over.isoMk (Iso.refl _)⟩⟩
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P : FiniteEtaleOver X, Nonempty (E.obj P ≅ P₁) :=
    ⟨E.objPreimage P₁, ⟨E.objObjPreimageIso P₁⟩⟩
  let hU₁ : U₁.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful U₁
  let hE : E.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful E
  let ρ₁ : F →* Aut P₁ := (hU₁.autMulEquivOfFullyFaithful P₁).symm.toMonoidHom.comp
    (eY.conjAut.symm.toMonoidHom.comp Y₁.act)
  let ρP : F →* Aut P :=
    (hE.autMulEquivOfFullyFaithful P).symm.toMonoidHom.comp (eP.conjAut.symm.toMonoidHom.comp ρ₁)
  let ρ : F →* Aut (U.obj P) := (U.mapAut P).comp ρP
  have h1 : ∀ σ, U₁.map (ρ₁ σ).hom ≫ eY.hom = eY.hom ≫ (Y₁.act σ).hom := fun σ ↦ by
    have hc := eY.conjAut_apply (eY.conjAut.symm (Y₁.act σ))
    rw [MulEquiv.apply_symm_apply] at hc
    have hm : U₁.map (ρ₁ σ).hom = (eY.conjAut.symm (Y₁.act σ)).hom :=
      congrArg Iso.hom (hU₁.isoEquiv.apply_symm_apply (eY.conjAut.symm (Y₁.act σ)))
    rw [hm]
    generalize eY.conjAut.symm (Y₁.act σ) = g at hc ⊢
    rw [hc]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    rfl
  have h2 : ∀ σ, E.map (ρP σ).hom ≫ eP.hom = eP.hom ≫ (ρ₁ σ).hom := fun σ ↦ by
    have hc := eP.conjAut_apply (eP.conjAut.symm (ρ₁ σ))
    rw [MulEquiv.apply_symm_apply] at hc
    have hm : E.map (ρP σ).hom = (eP.conjAut.symm (ρ₁ σ)).hom :=
      congrArg Iso.hom (hE.isoEquiv.apply_symm_apply (eP.conjAut.symm (ρ₁ σ)))
    rw [hm]
    generalize eP.conjAut.symm (ρ₁ σ) = g at hc ⊢
    rw [hc]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    rfl
  let e : (Over.pullback j).obj (U.obj P) ≅ Y₁.over :=
    ((Stacks.FundamentalGroup.finiteEtaleBaseChangeForgetIso j).app P).symm ≪≫ U₁.mapIso eP ≪≫ eY
  have hgal : IsGaloisCovering (U.obj P) ρ := by
    refine ⟨P.prop.2, ⟨fun x ↦ ?_⟩, ?_⟩
    · obtain ⟨_, ⟨y, rfl⟩, hxy⟩ := hsp x
      have : Etale P.hom := P.prop.2
      have hopen : IsOpen (Set.range P.hom) := P.hom.isOpenMap.isOpen_range
      have hw : e.inv.left ≫ pullback.snd P.hom j = Y₁.over.hom := Over.w e.inv
      have : Surjective (e.inv.left ≫ pullback.snd P.hom j) := by
        rw [hw]; exact Y₁.isGaloisCovering.surjective
      have : Surjective (pullback.snd P.hom j) := Surjective.of_comp e.inv.left _
      obtain ⟨w, rfl⟩ := (pullback.snd P.hom j).surjective y
      have hmem : j (pullback.snd P.hom j w) ∈ Set.range P.hom := ⟨pullback.fst P.hom j w, by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]⟩
      exact hxy.mem_open hopen hmem
    · rw [isIso_galoisCoveringMap_iff_isIso_sigmaLiftProd]
      change IsIso (sigmaLiftProd fun σ ↦ U.map (ρP σ).hom)
      rw [isIso_sigmaLiftProd_map_iff U, ← isIso_sigmaLiftProd_map_iff E,
        isIso_sigmaLiftProd_iff_of_iso eP h2, ← isIso_sigmaLiftProd_map_iff U₁,
        isIso_sigmaLiftProd_iff_of_iso eY h1, ← isIso_galoisCoveringMap_iff_isIso_sigmaLiftProd]
      exact Y₁.isGaloisCovering.isIso_galoisCoveringMap
  refine ⟨of (U.obj P) ρ hgal, e, fun σ ↦ ?_⟩
  ext : 1
  change (Over.pullback j).map (ρ σ).hom ≫ e.hom = e.hom ≫ (Y₁.act σ).hom
  have hn := (Stacks.FundamentalGroup.finiteEtaleBaseChangeForgetIso j).inv.naturality (ρP σ).hom
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Category.assoc, e]
  rw [← h1, ← reassoc_of% (U₁.map_comp _ _), ← h2, U₁.map_comp_assoc]
  exact (reassoc_of% hn) _

/-- **Galois covering spaces of the closed fibre extend.** Let `A` be a henselian local ring,
`f : X → Spec A` proper, `j : X₀ → X` the closed fibre `X ×_{Spec A} Spec (A ⧸ 𝔪)` and `F` a
finite group. For every `F`-Galois covering space `Y₁` of `X₀` there is an `F`-Galois covering
space `Y` of `X` and an isomorphism of `F`-Galois covering spaces `Y ×_X X₀ ≅ Y₁`: an
`X₀`-isomorphism `e` with `σ ≫ e = e ≫ σ` for every `σ ∈ F`. -/
@[weil "lem_fk106_galois_covering_special_fibre_extends"]
theorem exists_pullback_closedFibre_iso (A : Type u) [CommRing A] [HenselianLocalRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f] [Finite F]
    (Y₁ : GaloisCovering
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A))))) F) :
    ∃ (Y : GaloisCovering X F)
      (e : (Over.pullback (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A)))))).obj Y.over ≅
          Y₁.over),
      ∀ σ : F, (Over.pullback _).mapIso (Y.act σ) ≪≫ e = e ≪≫ Y₁.act σ := by
  have := isEquivalence_finiteEtaleBaseChange_of_isProper_of_henselianLocalRing A f
  exact exists_pullback_iso_of_isEquivalence _
    (exists_specializes_mem_range_pullback_fst_of_isProper A
      (jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm.le f) Y₁

end GaloisCovering

end AlgebraicGeometry
