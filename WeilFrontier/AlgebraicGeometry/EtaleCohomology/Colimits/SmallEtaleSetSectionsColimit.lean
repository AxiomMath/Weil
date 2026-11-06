module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleSetSectionsColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeSetInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
# Sections of inverse images along a projective system: the colimit map is injective

Let `X = lim X_α` be the limit of an inverse system of schemes over a directed set, with affine
transition morphisms `p_{βα} : X_β ⟶ X_α` and projections `p_α : X ⟶ X_α`, let `α₀` be an index
and `G_{α₀}` a sheaf of sets on the small étale site of `X_{α₀}`. Write
`G_α = p_{αα₀}^{-1} G_{α₀}` for `α ≥ α₀` and `G = p_{α₀}^{-1} G_{α₀}`. For `α₁ ≥ α₀` and a
quasi-compact quasi-separated scheme `U_{α₁}` étale over `X_{α₁}`, with base changes
`U_α = U_{α₁} ×_{X_{α₁}} X_α` and `U = U_{α₁} ×_{X_{α₁}} X`, the restriction maps
`G_α(U_α) ⟶ G(U)` induce an injective map `colim_{α ≥ α₁} G_α(U_α) ⟶ G(U)`: two sections of
`G_β` over `U_β` with the same image in `G(U)` already agree in `G_γ(U_γ)` for some `γ ≥ β`.

This is the injectivity half of [Stacks, Tag 09YQ] in degree zero for the system of inverse
images of a single sheaf, and is deduced from it. The inverse images `G_α` are the inverse
image, along the morphism of systems `(X_α)_{α ≥ α₀} ⟶ (X_{α₀})`, of the constant system with
value `G_{α₀}` on the constant system `X_{α₀}`; the constant system is presented by `G_{α₀}`
itself (`AlgebraicGeometry.StageInverseImage.isDirPresentation_constantSystem`), so its inverse
image is presented by `G`
(`Stacks.EtaleCohomology.LimitSetBaseChange.isDirPresentation_inverseImageSystem`),
and [Stacks, Tag 09YQ] for presented systems of sheaves of sets
(`Stacks.EtaleCohomology.SetLinearization.isSectionsColimitAt_of_presentation`) applies.

## Main definitions

* `AlgebraicGeometry.StageInverseImage.constantSystem`: the constant system of sheaves with value
  a sheaf `G₀`, on the constant inverse system of schemes.
* `AlgebraicGeometry.StageInverseImage.stageSystem`: the system `(G_α)_{α ≥ α₀}` of inverse
  images of `G_{α₀}`.
* `AlgebraicGeometry.StageInverseImage.sectionsToLimit`: the restriction map
  `G_β(U_β) ⟶ G(U)`.
* `AlgebraicGeometry.StageInverseImage.sectionsTransition`: the transition map
  `G_β(U_β) ⟶ G_γ(U_γ)` for `β ≤ γ`.

## Main results

* `AlgebraicGeometry.StageInverseImage.isDirPresentation_constantSystem`: a sheaf presents the
  colimit of the constant system with value that sheaf.
* `AlgebraicGeometry.StageInverseImage.sectionsToLimit_sectionsTransition`: the restriction maps
  are compatible with the transition maps, so they induce a map out of the colimit.
* `AlgebraicGeometry.StageInverseImage.exists_sectionsTransition_eq_of_sectionsToLimit_eq`:
  the induced map `colim_{α ≥ α₁} G_α(U_α) ⟶ G(U)` is injective.

## Implementation notes

The projective system is an inverse system over a directed preorder `I`, a functor
`D : Iᵒᵖ ⥤ Scheme` with affine transition morphisms, with a limit cone `c`; the étale site is
`AlgebraicGeometry.Scheme.smallEtaleTopology` and the inverse image is
`Stacks.EtaleCohomology.smallEtaleInverseImage`. Sheaves take values in `Type (u + 1)` for
schemes in `Scheme.{u}` and an index set in `Type u`, the universes in which the colimit
description of sections is available. The étale `X_{α₁}`-scheme `U_{α₁}` is assumed
quasi-compact and quasi-separated, as every étale scheme of finite type over a noetherian
scheme is.

Freitag and Kiehl state the result for the inverse images of the cokernel of a pair of
representable sheaves forming an equivalence relation; it is proved here for the inverse
images of an arbitrary sheaf of sets. The colimit is stated elementwise. The restriction map
`G_β(U_β) ⟶ G(U)` is the composite of the direct image along `p_{βα₁}` of the transpose of the
unit `G_β ⟶ p_{β,*} p_β^{-1} G_β`, read through the identification of `p_β^{-1} G_β` with `G`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.4.17 2), p. 52.
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

/- FK's lemma is stated in the presentation setting
(`G_{α₀} = Coker(R̃ ⇉ H̃)`), proved there through the presheaf image and the colimit of
`Hom(U_α, H_α)`; this file proves the generalization to an arbitrary sheaf of sets on
`X_{α₀}` through Stacks 09YQ, which contains FK's case. -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology

universe w' w u

namespace AlgebraicGeometry.StageInverseImage

section Identity

variable (S : Scheme.{u}) (A : Type w) [Category.{w'} A]

/-- The direct image along the identity of a scheme is the identity functor on étale sheaves. -/
def pushforwardIdIso : smallEtalePushforward (𝟙 S) A ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId S) A _

/-- The component of `pushforwardIdIso` at a sheaf and an étale scheme. -/
theorem pushforwardIdIso_inv_app_hom_app (K : Sheaf (Scheme.smallEtaleTopology S) A)
    (U : (S.Etale)ᵒᵖ) :
    ((pushforwardIdIso S A).inv.app K).hom.app U =
      K.obj.map ((smallEtaleBaseChangeId S).hom.app U.unop).op := by
  simp [pushforwardIdIso]
  rfl

/-- The comparison of base change along `𝟙 ≫ 𝟙` with the composite of the base changes, followed
by the identification of base change along the identity, is the identity. -/
theorem baseChangeComp'_id_comp (h : 𝟙 S = 𝟙 S ≫ 𝟙 S) (U : S.Etale) :
    (smallEtaleBaseChangeComp' (𝟙 S) (𝟙 S) (𝟙 S) h).hom.app U ≫
      (smallEtaleBaseChangeId S).hom.app
        ((Stacks.EtaleCohomology.smallEtaleBaseChange (𝟙 S)).obj U) = 𝟙 _ := by
  apply smallEtaleBaseChange_hom_ext
  exact (smallEtaleBaseChangeComp'_fst_fst (𝟙 S) (𝟙 S) (𝟙 S) h U).trans (Category.id_comp _).symm

/-- The cocycle law for the identification `K ≅ (𝟙)_* K` of a sheaf with its direct image along the
identity. -/
theorem pushforwardIdIso_inv_comp (h : 𝟙 S = 𝟙 S ≫ 𝟙 S)
    (K : Sheaf (Scheme.smallEtaleTopology S) A) :
    (pushforwardIdIso S A).inv.app K ≫
        (smallEtalePushforward (𝟙 S) A).map ((pushforwardIdIso S A).inv.app K) ≫
          (smallEtalePushforwardComp' (𝟙 S) (𝟙 S) (𝟙 S) h A).hom.app K =
      (pushforwardIdIso S A).inv.app K := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [smallEtalePushforwardComp'_hom_app_hom_app, pushforwardIdIso_inv_app_hom_app]
  change K.obj.map _ ≫ ((pushforwardIdIso S A).inv.app K).hom.app _ ≫ _ = _
  rw [pushforwardIdIso_inv_app_hom_app]
  have e := congrArg (fun m => K.obj.map (Quiver.Hom.op m)) (baseChangeComp'_id_comp S h U.unop)
  simp only [op_comp, Functor.map_comp, op_id] at e
  dsimp only [Functor.id_obj, unop_op] at e ⊢
  erw [e, K.obj.map_id]
  exact Category.comp_id _

/-- A map into the direct image along the identity, precomposed with the identification
`G ≅ (𝟙)_* G` and pushed forward again, is the map itself. -/
theorem pushforwardIdIso_inv_comp_map_comp (h : 𝟙 S = 𝟙 S ≫ 𝟙 S)
    {G K : Sheaf (Scheme.smallEtaleTopology S) A}
    (φ : G ⟶ (smallEtalePushforward (𝟙 S) A).obj K) :
    (pushforwardIdIso S A).inv.app G ≫ (smallEtalePushforward (𝟙 S) A).map φ ≫
        (smallEtalePushforwardComp' (𝟙 S) (𝟙 S) (𝟙 S) h A).hom.app K = φ := by
  have hφ : φ = (φ ≫ (pushforwardIdIso S A).hom.app K) ≫ (pushforwardIdIso S A).inv.app K := by
    rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hn := (pushforwardIdIso S A).inv.naturality (φ ≫ (pushforwardIdIso S A).hom.app K)
  dsimp only [Functor.id_map] at hn
  calc _ = (pushforwardIdIso S A).inv.app G ≫ (smallEtalePushforward (𝟙 S) A).map
          ((φ ≫ (pushforwardIdIso S A).hom.app K) ≫ (pushforwardIdIso S A).inv.app K) ≫
            (smallEtalePushforwardComp' (𝟙 S) (𝟙 S) (𝟙 S) h A).hom.app K := by rw [← hφ]
    _ = (φ ≫ (pushforwardIdIso S A).hom.app K) ≫ (pushforwardIdIso S A).inv.app K ≫
          (smallEtalePushforward (𝟙 S) A).map ((pushforwardIdIso S A).inv.app K) ≫
            (smallEtalePushforwardComp' (𝟙 S) (𝟙 S) (𝟙 S) h A).hom.app K := by
        rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hn]
        simp only [Category.assoc]
        rfl
    _ = φ := by rw [pushforwardIdIso_inv_comp, ← hφ]

end Identity

section Constant

variable {J : Type u} [Preorder J] (S : Scheme.{u})
  (G₀ : Sheaf (Scheme.smallEtaleTopology S) (Type (u + 1)))

/-- The cocycle law of the constant system of sheaves. -/
theorem constantSystem_cocycle {i j k : Jᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (pushforwardIdIso S (Type (u + 1))).inv.app G₀ =
      (pushforwardIdIso S (Type (u + 1))).inv.app G₀ ≫
        (systemPushforward ((Functor.const Jᵒᵖ).obj S) (Type (u + 1)) b).map
            ((pushforwardIdIso S (Type (u + 1))).inv.app G₀) ≫
          (smallEtalePushforwardComp' (((Functor.const Jᵒᵖ).obj S).map a)
            (((Functor.const Jᵒᵖ).obj S).map b) (((Functor.const Jᵒᵖ).obj S).map (a ≫ b))
            (((Functor.const Jᵒᵖ).obj S).map_comp a b) (Type (u + 1))).hom.app G₀ :=
  (pushforwardIdIso_inv_comp S _ _ G₀).symm

/-- **The constant system of sheaves** with value `G₀` on the constant inverse system of schemes
with value `S`: every transition map is the identification of `G₀` with its direct image along
the identity. -/
def constantSystem : EtaleSheafSystem ((Functor.const Jᵒᵖ).obj S) (Type (u + 1)) :=
  EtaleSheafSystem.ofMapTranspose (fun _ => G₀) (fun _ => (pushforwardIdIso S _).inv.app G₀)
    (fun a b => constantSystem_cocycle S G₀ a b)

/-- The transposed transition maps of the constant system. -/
theorem constantSystem_mapTranspose {i j : Jᵒᵖ} (a : i ⟶ j) :
    (constantSystem S G₀).mapTranspose a = (pushforwardIdIso S _).inv.app G₀ :=
  EtaleSheafSystem.mapTranspose_ofMapTranspose _ _ (fun a b => constantSystem_cocycle S G₀ a b) a

/-- **A sheaf presents the colimit of the constant system with value that sheaf**, over a
nonempty directed index set. -/
theorem isDirPresentation_constantSystem [Nonempty J] [IsDirected J (· ≤ ·)] :
    SetLinearization.IsDirPresentation (Type (u + 1)) (constCone Jᵒᵖ S)
      (constantSystem (J := J) S G₀) G₀ (fun _ => (pushforwardIdIso S _).inv.app G₀) := by
  refine ⟨fun i j a => ?_, fun K τ hτ => ?_⟩
  · rw [constantSystem_mapTranspose]
    exact (pushforwardIdIso_inv_comp S _ _ G₀).symm
  · have heq : ∀ ⦃i j : Jᵒᵖ⦄ (_ : i ⟶ j), τ j = τ i := fun i j a => by
      rw [hτ a, constantSystem_mapTranspose]
      exact pushforwardIdIso_inv_comp_map_comp S _ _ (τ i)
    have hall : ∀ i j : Jᵒᵖ, τ i = τ j := fun i j => by
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.unop j.unop
      exact (heq (homOfLE hik).op).trans (heq (homOfLE hjk).op).symm
    let i₀ : Jᵒᵖ := op (Classical.arbitrary J)
    have key : ∀ χ : G₀ ⟶ K,
        (pushforwardIdIso S _).inv.app G₀ ≫ (smallEtalePushforward (𝟙 S) _).map χ =
          χ ≫ (pushforwardIdIso S _).inv.app K := fun χ =>
      ((pushforwardIdIso S _).inv.naturality χ).symm
    refine ⟨τ i₀ ≫ (pushforwardIdIso S _).hom.app K, fun i => ?_, fun χ hχ => ?_⟩
    · refine (key _).trans ?_
      erw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
      exact hall i₀ i
    · have h1 := (key χ).symm.trans (hχ i₀)
      rw [← h1]
      erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end Constant


section Stages

open SmallEtaleLimitCohomology LimitSetBaseChange SetLinearization LimitDirectImage

attribute [local instance] IsCofiltered.isConnected

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)
  (α₀ : I) (G₀ : Sheaf (D.obj (op α₀)).smallEtaleTopology (Type (u + 1)))

/-- The morphism of inverse systems `(X_α)_{α ≥ α₀} ⟶ (X_{α₀})` to the constant system, given by
the transition morphisms `p_{αα₀}`. -/
def toBase : geIndexOpFunctor α₀ ⋙ D ⟶ (Functor.const (GeIndex α₀)ᵒᵖ).obj (D.obj (op α₀)) where
  app j := D.map (geIndexToBase α₀ j)
  naturality j k a := by
    simp only [Functor.comp_map, Functor.const_obj_map, ← D.map_comp]
    exact congrArg D.map (Subsingleton.elim _ _)

/-- **The system `(G_α)_{α ≥ α₀}`** of the inverse images `G_α = p_{αα₀}^{-1} G_{α₀}`. -/
abbrev stageSystem : EtaleSheafSystem (geIndexOpFunctor α₀ ⋙ D) (Type (u + 1)) :=
  inverseImageSystem (toBase α₀) (constantSystem (J := GeIndex α₀) (D.obj (op α₀)) G₀)

/-- The inverse image `G = p_{α₀}^{-1} G_{α₀}` on the limit, as the inverse image of `G_{α₀}` along
the limit of the morphism of systems `toBase`. -/
abbrev limitSheaf : Sheaf c.pt.smallEtaleTopology (Type (u + 1)) :=
  inverseImageSheaf (toBase α₀) (c.whisker (geIndexOpFunctor α₀))
    (constCone (GeIndex α₀)ᵒᵖ (D.obj (op α₀))) (isLimitConstCone _ _) G₀

/-- The structure maps `G_α ⟶ p_{α,*} G` of the presentation of `G` as the colimit of the `G_α`. -/
abbrev limitLeg (j : (GeIndex α₀)ᵒᵖ) :=
  inverseImageLeg (toBase α₀) (constantSystem (J := GeIndex α₀) (D.obj (op α₀)) G₀)
    (c.whisker (geIndexOpFunctor α₀)) (constCone (GeIndex α₀)ᵒᵖ (D.obj (op α₀)))
    (isLimitConstCone _ _) (fun _ => (pushforwardIdIso (D.obj (op α₀)) _).inv.app G₀) j

/-- **`G = colim_{α ≥ α₀} p_α^{-1} G_α`**, in adjoint form. -/
theorem isDirPresentation_limitLeg :
    IsDirPresentation (Type (u + 1)) (c.whisker (geIndexOpFunctor α₀)) (stageSystem α₀ G₀)
      (limitSheaf c α₀ G₀) (limitLeg c α₀ G₀) :=
  isDirPresentation_inverseImageSystem _ _ _ _ _ _
    (isDirPresentation_constantSystem (D.obj (op α₀)) G₀)

/-- The limit of the morphism of systems `toBase` is the projection `p_{α₀}`. -/
theorem limitMorphism_toBase :
    LimitHigherDirectImage.limitMorphism (toBase α₀) (c.whisker (geIndexOpFunctor α₀))
      (constCone (GeIndex α₀)ᵒᵖ (D.obj (op α₀))) (isLimitConstCone _ _) = c.π.app (op α₀) :=
  (Category.comp_id _).symm.trans
    ((LimitHigherDirectImage.limitMorphism_comp_π _ _ _ _ (op ⟨α₀, le_rfl⟩)).trans (c.w _))

/-- Transport along an equality of morphisms of the sections of an inverse image is injective. -/
theorem injective_eqToHom_inverseImage_app {X Y : Scheme.{u}} {q q' : X ⟶ Y} (hq : q = q')
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1))) (V : (X.Etale)ᵒᵖ) :
    Function.Injective ((eqToHom (congrArg
      (fun q => (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0} q).obj G) hq)).hom.app
        V) := by
  subst hq
  exact fun _ _ h => h

variable {α₀} (α₁ : I) (h₀₁ : α₀ ≤ α₁) (U₁ : (D.obj (op α₁)).Etale)

/-- **The restriction map `G_β(U_β) ⟶ G(U)`** for `α₀ ≤ α₁ ≤ β`, an étale `X_{α₁}`-scheme
`U_{α₁}`, `U_β = U_{α₁} ×_{X_{α₁}} X_β` and `U = U_{α₁} ×_{X_{α₁}} X`. -/
def sectionsToLimit {β : I} (h₁β : α₁ ≤ β) :
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}
        (D.map (homOfLE (h₀₁.trans h₁β)).op)).obj G₀).obj.obj
      (op ((Stacks.EtaleCohomology.smallEtaleBaseChange (D.map (homOfLE h₁β).op)).obj U₁)) →
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0} (c.π.app (op α₀))).obj G₀).obj.obj
      (op ((Stacks.EtaleCohomology.smallEtaleBaseChange (c.π.app (op α₁))).obj U₁)) :=
  fun t => (eqToHom (congrArg
    (fun q => (Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0} q).obj G₀)
    (limitMorphism_toBase c α₀))).hom.app _
    ((shiftLeg (c := c.whisker (geIndexOpFunctor α₀)) (limitLeg c α₀ G₀)
      (homOfLE (show (⟨α₁, h₀₁⟩ : GeIndex α₀) ≤ ⟨β, h₀₁.trans h₁β⟩ from h₁β)).op).hom.app
        (op U₁) t)

/-- **The transition map `G_β(U_β) ⟶ G_γ(U_γ)`** of the system of sections, for
`α₁ ≤ β ≤ γ`. -/
def sectionsTransition {β γ : I} (h₁β : α₁ ≤ β) (hβγ : β ≤ γ) :
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}
        (D.map (homOfLE (h₀₁.trans h₁β)).op)).obj G₀).obj.obj
      (op ((Stacks.EtaleCohomology.smallEtaleBaseChange (D.map (homOfLE h₁β).op)).obj U₁)) →
    ((Stacks.EtaleCohomology.smallEtaleInverseImage.{u, 0}
        (D.map (homOfLE (h₀₁.trans (h₁β.trans hβγ))).op)).obj G₀).obj.obj
      (op ((Stacks.EtaleCohomology.smallEtaleBaseChange
        (D.map (homOfLE (h₁β.trans hβγ)).op)).obj U₁)) :=
  (shiftTransition (Type (u + 1)) (stageSystem α₀ G₀).mapTranspose
    (homOfLE (show (⟨β, h₀₁.trans h₁β⟩ : GeIndex α₀) ≤ ⟨γ, h₀₁.trans (h₁β.trans hβγ)⟩ from hβγ)).op
    (homOfLE (show (⟨α₁, h₀₁⟩ : GeIndex α₀) ≤ ⟨β, h₀₁.trans h₁β⟩ from h₁β)).op
    (homOfLE (show (⟨α₁, h₀₁⟩ : GeIndex α₀) ≤ ⟨γ, h₀₁.trans (h₁β.trans hβγ)⟩ from
      h₁β.trans hβγ)).op (Subsingleton.elim _ _)).hom.app (op U₁)

/-- The restriction maps to `G(U)` are compatible with the transition maps, so they induce a map
`colim_{α ≥ α₁} G_α(U_α) ⟶ G(U)`. -/
@[weil "lem_fk104_sections_colimit_injective"]
theorem sectionsToLimit_sectionsTransition {β γ : I} (h₁β : α₁ ≤ β) (hβγ : β ≤ γ) (s) :
    sectionsToLimit c G₀ α₁ h₀₁ U₁ (h₁β.trans hβγ) (sectionsTransition G₀ α₁ h₀₁ U₁ h₁β hβγ s) =
      sectionsToLimit c G₀ α₁ h₀₁ U₁ h₁β s := by
  dsimp only [sectionsToLimit]
  congr 1
  exact congrArg (fun m => m.hom.app (op U₁) s)
    (shiftTransition_comp_shiftLeg (stageSystem α₀ G₀).mapTranspose (limitLeg c α₀ G₀)
      (fun a => (isDirPresentation_limitLeg c α₀ G₀).1 a)
      (homOfLE (show (⟨β, h₀₁.trans h₁β⟩ : GeIndex α₀) ≤ ⟨γ, h₀₁.trans (h₁β.trans hβγ)⟩ from
        hβγ)).op
      (homOfLE (show (⟨α₁, h₀₁⟩ : GeIndex α₀) ≤ ⟨β, h₀₁.trans h₁β⟩ from h₁β)).op
      (homOfLE (show (⟨α₁, h₀₁⟩ : GeIndex α₀) ≤ ⟨γ, h₀₁.trans (h₁β.trans hβγ)⟩ from
        h₁β.trans hβγ)).op (Subsingleton.elim _ _))

/-- **The map `colim_{α ≥ α₁} G_α(U_α) ⟶ G(U)` is injective.** Let `X = lim X_α` with affine
transition morphisms, `G_{α₀}` a sheaf of sets on the small étale site of `X_{α₀}`,
`G_α = p_{αα₀}^{-1} G_{α₀}` and `G = p_{α₀}^{-1} G_{α₀}`, and let `U_{α₁}` be a quasi-compact
quasi-separated scheme étale over `X_{α₁}` for some `α₁ ≥ α₀`. If two sections of `G_β` over
`U_β` have the same image in `G(U)`, they have the same image in `G_γ(U_γ)` for some `γ ≥ β`. -/
@[weil "lem_fk104_sections_colimit_injective"]
theorem exists_sectionsTransition_eq_of_sectionsToLimit_eq (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [CompactSpace U₁.left] [QuasiSeparatedSpace U₁.left] {β : I} (h₁β : α₁ ≤ β) (s s')
    (h : sectionsToLimit c G₀ α₁ h₀₁ U₁ h₁β s = sectionsToLimit c G₀ α₁ h₀₁ U₁ h₁β s') :
    ∃ (γ : I) (hβγ : β ≤ γ), sectionsTransition G₀ α₁ h₀₁ U₁ h₁β hβγ s =
      sectionsTransition G₀ α₁ h₀₁ U₁ h₁β hβγ s' := by
  have : ∀ {i j : (GeIndex α₀)ᵒᵖ} (a : i ⟶ j), IsAffineHom ((geIndexOpFunctor α₀ ⋙ D).map a) :=
    fun a => inferInstanceAs (IsAffineHom (D.map _))
  have hsec := isSectionsColimitAt_of_presentation (isLimit_whisker_geIndexOpFunctor α₀ hc)
    (stageSystem α₀ G₀) (limitLeg c α₀ G₀) (isDirPresentation_limitLeg c α₀ G₀) ⟨α₁, h₀₁⟩ U₁
  obtain ⟨k', b, hb⟩ := hsec.2 (op ⟨⟨β, h₀₁.trans h₁β⟩, h₁β⟩) s s'
    (injective_eqToHom_inverseImage_app (limitMorphism_toBase c α₀) G₀ _ h)
  exact ⟨k'.unop.1.1, leOfHom b.unop, hb⟩

end Stages

end AlgebraicGeometry.StageInverseImage
