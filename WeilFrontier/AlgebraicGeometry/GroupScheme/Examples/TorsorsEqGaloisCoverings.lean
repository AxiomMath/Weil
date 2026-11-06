module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TorsorClasses
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TorsorUnderConstantSheaf
public import WeilFrontier.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringFunctorIsTorsor
public import WeilFrontier.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringSpace
public import WeilFrontier.Defs.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringIsomorphism
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.InducedActionOnPoints
public import Weil.Attr

/-!
# Torsors under a finite constant sheaf are Galois covering spaces

Let `X` be a noetherian separated scheme and `F` a finite group. The assignment `X' ↦ h_{X'}`,
which sends an `F`-Galois covering space `X'/X` to the sheaf `h_{X'} : U ↦ Hom_X(U, X')` on the
étale category `Et(X)` with the right action of the constant sheaf of groups `F_X` induced by the
action of `F` on `X'`, induces a bijection from the set of isomorphism classes of `F`-Galois
covering spaces of `X` onto the set of `F`-equivariant isomorphism classes of `F_X`-torsors.

The map is well defined because an `F`-equivariant `X`-isomorphism `g : X' → X''` gives the
equivariant isomorphism `t ↦ t ≫ g` of sheaves. It is surjective because every `F_X`-torsor is
represented, equivariantly, by an object of `Et(X)` with an action of `F`, which is then an
`F`-Galois covering space. It is injective by the Yoneda lemma: both covering spaces are objects
of `Et(X)`, so an equivariant isomorphism `η : h_{X'} ≅ h_{X''}` is `t ↦ t ≫ g` for the
`X`-isomorphism `g = η(id)`, and evaluating the equivariance of `η` on the constant sections of
`F_X` gives `a'_τ ≫ g = g ≫ a''_τ`.

## Main definitions

* `AlgebraicGeometry.GaloisCovering.torsorClass` — the class of the `F_X`-torsor `h_{X'}` of an
  `F`-Galois covering space `X'`.
* `AlgebraicGeometry.GaloisCovering.isoClassTorsorClass` — the induced map from isomorphism
  classes of `F`-Galois covering spaces to isomorphism classes of `F_X`-torsors.

## Main results

* `AlgebraicGeometry.GaloisCovering.bijective_isoClassTorsorClass` — for `X` noetherian and
  separated and `F` finite, this map is a bijection.

## Implementation notes

The `F_X`-torsors are the pseudo torsors (`PseudoTorsor`) under the sheaf of groups
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantSheafOfGroups` which are torsors
(`PseudoTorsor.IsTorsor`), for the left action `σ • t = t ^ σ⁻¹`; their equivariant isomorphism
classes form `SheafOfGroups.TorsorClasses`. The torsor `h_{X'}` is
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.representableRightAction` turned into a pseudo
torsor. Galois covering spaces include the surjectivity of `X' → X`
(`AlgebraicGeometry.IsGaloisCovering`), and their isomorphism classes are the classes of
`CategoryTheory.isIsomorphicSetoid` on the category `AlgebraicGeometry.GaloisCovering X F`.
The map is defined for any locally noetherian `X` and any group `F`; finiteness of `F` and `X`
noetherian and separated are used for the bijectivity, which places `X'` in `Et(X)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

open SmallNoetherianSeparatedEtale

namespace GaloisCovering

section TorsorClass

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) [IsLocallyNoetherian X]
  {F : Type u} [Group F]

/-- The class of the `F_X`-torsor `h_{X'}` of an `F`-Galois covering space `X'` of `X`, with the
right action of `F_X` induced by the action of `F` on `X'`. -/
def torsorClass (Y : GaloisCovering X F) :
    SheafOfGroups.TorsorClasses.{u} (locallyConstantSheafOfGroups B X hX F) :=
  SheafOfGroups.TorsorClasses.mk _
    (Y.isGaloisCovering.isTorsor_representableRightAction (B := B) (hX := hX))

omit [IsLocallyNoetherian X] in
/-- Postcomposition with an equivariant `X`-morphism commutes with the twist `t ↦ t ^ σ`. -/
private lemma locallyConstantSMul_comp {U Y Y' : Over X} {ρ : F →* Aut Y} {ρ' : F →* Aut Y'}
    (g : Y ⟶ Y') (hg : ∀ τ : F, (ρ τ).hom ≫ g = g ≫ (ρ' τ).hom)
    (σ : LocallyConstant U.left F) (t : U ⟶ Y) :
    Over.locallyConstantSMul ρ σ t ≫ g = Over.locallyConstantSMul ρ' σ (t ≫ g) := by
  ext1
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ⟨fiberOpen F σ (σ x), rfl, ?_⟩
  have h := congrArg CommaMorphism.left (hg (σ x)⁻¹)
  simp only [Over.comp_left] at h
  simp only [Over.comp_left, Over.locallyConstantSMul_left,
    Scheme.ι_fiberOpen_twistByLocallyConstant_assoc, Scheme.ι_fiberOpen_twistByLocallyConstant,
    Category.assoc, h]

/-- The equivariant isomorphism of torsors `h_{X'} ≅ h_{X''}`, `t ↦ t ≫ g`, of an
isomorphism `g` of `F`-Galois covering spaces. -/
private def torsorHom {Y Y' : GaloisCovering X F} (e : Y ≅ Y') :
    ((representableRightAction B hX Y.over Y.act).toPseudoTorsor
      (Y.isGaloisCovering.isFormallyPrincipal_representableRightAction)).Hom
    ((representableRightAction B hX Y'.over Y'.act).toPseudoTorsor
      (Y'.isGaloisCovering.isFormallyPrincipal_representableRightAction)) where
  hom := (representablePresheafFunctor B X hX).map (isoOver e).hom
  map_act _ _ t :=
    locallyConstantSMul_comp (isoOver e).hom
      (fun τ ↦ congrArg Iso.hom (act_trans_isoOver e τ)) _ t

lemma torsorClass_eq_of_iso {Y Y' : GaloisCovering X F} (e : Y ≅ Y') :
    torsorClass B hX Y = torsorClass B hX Y' :=
  SheafOfGroups.TorsorClasses.mk_eq_mk_of_hom _ _ (torsorHom B hX e)

/-- **From Galois covering spaces to torsors.** The map sending the isomorphism class of an
`F`-Galois covering space `X'/X` to the `F`-equivariant isomorphism class of the `F_X`-torsor
`h_{X'}`, with the right action of `F_X` induced by the action of `F` on `X'`. -/
@[weil "lem_fk102_torsors_eq_galois_coverings"]
def isoClassTorsorClass :
    Quotient (isIsomorphicSetoid (GaloisCovering X F)) →
      SheafOfGroups.TorsorClasses.{u} (locallyConstantSheafOfGroups B X hX F) :=
  Quotient.lift (torsorClass B hX) fun _ _ ⟨e⟩ ↦ torsorClass_eq_of_iso B hX e

@[simp]
lemma isoClassTorsorClass_mk (Y : GaloisCovering X F) :
    isoClassTorsorClass B hX ⟦Y⟧ = torsorClass B hX Y :=
  rfl

end TorsorClass

section Bijective

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {F : Type u} [Group F]

/-- A morphism `η : h_{X'} ⟶ h_{X''}` out of the presheaf of an object `X'` of `Et(X)` is
`t ↦ t ≫ η(id)`. -/
private lemma app_eq_comp (A U : SmallNoetherianSeparatedEtale B X hX) {Y' : Over X}
    (η : representablePresheaf B X hX ((toOver B X hX).obj A) ⟶
      representablePresheaf B X hX Y')
    (t : (toOver B X hX).obj U ⟶ (toOver B X hX).obj A) :
    η.app (op U) t = t ≫ η.app (op A) (𝟙 _) := by
  obtain ⟨p, rfl⟩ := (toOver B X hX).map_surjective t
  have h := NatTrans.naturality_apply η p.op (𝟙 ((toOver B X hX).obj A))
  simp only [representablePresheaf.map_apply] at h
  exact h

/-- The twist `t ^ σ` by a section `σ` with constant value `τ` is `t ≫ a_{τ⁻¹}`. -/
private lemma locallyConstantSMul_of_forall {U Y : Over X} (ρ : F →* Aut Y)
    (σ : LocallyConstant U.left F) (t : U ⟶ Y) (τ : F) (hσ : ∀ x, σ x = τ) :
    Over.locallyConstantSMul ρ σ t = t ≫ (ρ τ⁻¹).hom := by
  ext1
  simpa using Over.comp_locallyConstantSMul_left_of_forall (𝟙 _) ρ σ t τ hσ

/-- **Injectivity.** An equivariant morphism between the torsors `h_{X'}` and `h_{X''}` of two
`F`-Galois covering spaces comes from an isomorphism of `F`-Galois covering spaces. -/
private lemma nonempty_iso_of_torsorHom [Finite F] [IsNoetherian X] [X.IsSeparated]
    {Y Y' : GaloisCovering X F}
    (e : ((representableRightAction B hX Y.over Y.act).toPseudoTorsor
      (Y.isGaloisCovering.isFormallyPrincipal_representableRightAction)).Hom
      ((representableRightAction B hX Y'.over Y'.act).toPseudoTorsor
        (Y'.isGaloisCovering.isFormallyPrincipal_representableRightAction)))
    (he : e.IsIso) : Nonempty (Y ≅ Y') := by
  let A := Y.isGaloisCovering.toEt B hX
  let A' := Y'.isGaloisCovering.toEt B hX
  let η : representablePresheaf B X hX ((toOver B X hX).obj A) ⟶
      representablePresheaf B X hX ((toOver B X hX).obj A') := e.hom
  have : IsIso η := he
  let E := asIso η
  let g : Y.over ⟶ Y'.over := η.app (op A) (𝟙 Y.over)
  let g' : Y'.over ⟶ Y.over := E.inv.app (op A') (𝟙 Y'.over)
  have hgg' : g ≫ g' = 𝟙 _ := by
    have h : E.inv.app (op A) g = g ≫ g' := app_eq_comp A' A E.inv g
    rw [← h]
    exact ConcreteCategory.congr_hom (E.hom_inv_id_app (op A)) (𝟙 Y.over)
  have hg'g : g' ≫ g = 𝟙 _ := by
    have h : η.app (op A') g' = g' ≫ g := app_eq_comp A A' η g'
    rw [← h]
    exact ConcreteCategory.congr_hom (E.inv_hom_id_app (op A')) (𝟙 Y'.over)
  refine ⟨isoMk ⟨g, g', hgg', hg'g⟩ fun σ ↦ Iso.ext ?_⟩
  change (Y.act σ).hom ≫ g = g ≫ (Y'.act σ).hom
  have h := e.map_act (op A) (LocallyConstant.const _ σ) (𝟙 Y.over)
  change η.app (op A) (Over.locallyConstantSMul Y.act
      ((LocallyConstant.const Y.over.left σ)⁻¹ : LocallyConstant Y.over.left F) (𝟙 Y.over)) =
    Over.locallyConstantSMul Y'.act
      ((LocallyConstant.const Y.over.left σ)⁻¹ : LocallyConstant Y.over.left F) g at h
  have h1 : η.app (op A) (Y.act σ).hom = (Y.act σ).hom ≫ g := app_eq_comp A A η _
  have hL : Over.locallyConstantSMul (U := (toOver B X hX).obj A) Y.act
      ((LocallyConstant.const Y.over.left σ)⁻¹ : LocallyConstant Y.over.left F) (𝟙 Y.over) =
        (Y.act σ).hom := by
    refine (locallyConstantSMul_of_forall (U := (toOver B X hX).obj A) Y.act _ _ σ⁻¹
      fun _ ↦ rfl).trans ?_
    rw [inv_inv]
    exact Category.id_comp _
  have hR : Over.locallyConstantSMul (U := (toOver B X hX).obj A) Y'.act
      ((LocallyConstant.const Y.over.left σ)⁻¹ : LocallyConstant Y.over.left F) g =
        g ≫ (Y'.act σ).hom := by
    refine (locallyConstantSMul_of_forall (U := (toOver B X hX).obj A) Y'.act _ _ σ⁻¹
      fun _ ↦ rfl).trans ?_
    rw [inv_inv]
    rfl
  exact h1.symm.trans ((congrArg (η.app (op A)) hL.symm).trans (h.trans hR))

variable (B hX) in
/-- **Isomorphism classes of torsors under a finite constant sheaf are isomorphism classes of
Galois covering spaces.** Let `X` be a noetherian separated scheme and `F` a finite group. The
map sending an `F`-Galois covering space `X'/X` (with `X' → X` surjective) to the `F_X`-torsor
`h_{X'}`, with the right action of `F_X` induced by the action of `F` on `X'`, induces a
bijection from the isomorphism classes of `F`-Galois covering spaces of `X` onto the
`F`-equivariant isomorphism classes of `F_X`-torsors. -/
@[weil "lem_fk102_torsors_eq_galois_coverings"]
theorem bijective_isoClassTorsorClass [Finite F] [IsNoetherian X] [X.IsSeparated] :
    Function.Bijective (isoClassTorsorClass B hX (F := F)) := by
  refine ⟨fun c c' hcc' ↦ ?_, fun c ↦ ?_⟩
  · induction c using Quotient.inductionOn with | h Y => ?_
    induction c' using Quotient.inductionOn with | h Y' => ?_
    obtain ⟨e, he⟩ := (SheafOfGroups.TorsorClasses.mk_eq_mk_iff _ _).1 hcc'
    exact Quotient.sound (nonempty_iso_of_torsorHom e he)
  · obtain ⟨T, hT, rfl⟩ := SheafOfGroups.TorsorClasses.mk_surjective c
    obtain ⟨S, hS, hne⟩ := hT (final B X hX)
    obtain ⟨P, ⟨ι, _, V, φ, rfl, hφ⟩, hle⟩ := exists_finite_subfamily B X hX S hS
    have hstr (i : ι) : structureMorphism (V i) = (toScheme B X hX).map (φ i) := by
      rw [← toScheme_map_comp_structureMorphism (φ i)]
      exact Category.comp_id _
    have hcov : Scheme.IsEtaleCovering fun i ↦ structureMorphism (V i) :=
      ⟨inferInstance, fun i ↦ inferInstance, by simp only [hstr]; exact hφ⟩
    obtain ⟨X', ρ, θ, -, -, hθ⟩ := exists_iso_representablePresheaf_of_isFormallyPrincipal
      T.toRightAction (SheafOfGroups.RightAction.isFormallyPrincipal_toRightAction T) V hcov
      fun i ↦ hne (hle _ _ (Presieve.ofArrows.mk i))
    have hG := isGaloisCovering_of_isTorsor T hT X' ρ θ hθ
    refine ⟨⟦of _ ρ hG⟧, SheafOfGroups.TorsorClasses.mk_eq_mk_of_hom _ _
      ⟨θ.hom, fun U s t ↦ ?_⟩⟩
    refine (hθ U.unop s⁻¹ t).trans ?_
    change T.act U s⁻¹⁻¹ _ = _
    rw [inv_inv]
    rfl

end Bijective

end GaloisCovering

end AlgebraicGeometry

end
