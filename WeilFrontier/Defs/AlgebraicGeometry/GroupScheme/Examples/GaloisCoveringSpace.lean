module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilFrontier.Defs.AlgebraicGeometry.GroupScheme.Examples.Constant
public import Weil.Attr

/-!
# Galois covering spaces

Let `X` be a scheme and `F` a group. An `X`-scheme `X'` with a left action `σ ↦ a_σ` of `F` by
`X`-automorphisms is an *`F`-Galois covering space* of `X` if `X' → X` is étale and surjective,
and the `X`-morphism
`∐_{σ ∈ F} X' → X' ×_X X'`, given on the copy indexed by `σ` by `x' ↦ (σ x', x')`,
is an isomorphism. For `F` finite, the source is `X' ×_X F̃_X`, the fibre product with the
constant group scheme `F̃_X = ∐_{σ ∈ F} X`.

## Main definitions

* `AlgebraicGeometry.galoisCoveringMap Y ρ` — the morphism `∐_{σ ∈ F} Y → Y ×_X Y`,
  `x' ↦ (σ x', x')` on the copy indexed by `σ`.
* `AlgebraicGeometry.IsGaloisCovering Y ρ` — the `X`-scheme `Y` with the action `ρ` of `F` is an
  `F`-Galois covering space of `X`.

## Main results

* `AlgebraicGeometry.galoisCoveringMapOfTensor Y ρ` — the same morphism with source
  `Y ×_X F̃_X`, and `AlgebraicGeometry.isGaloisCovering_iff_isIso_galoisCoveringMapOfTensor`,
  which expresses the definition through it.

## Implementation notes

The action is a monoid homomorphism `F →* Aut Y`, `Y` an object of `Over X`; the multiplication
of `Aut Y` is composition (`σ * τ` acts as `τ` followed by `σ`), so this is a left action.
Finiteness of `F` is not needed to state the definition, and is assumed only for the comparison
with the constant group scheme. The fibre product with the constant group scheme is taken as
`Y ⊗ F̃_X` rather than `F̃_X ⊗ Y`; the two are canonically isomorphic.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {F : Type u} [Group F]

/-- The morphism `∐_{σ ∈ F} Y → Y ×_X Y` of an `X`-scheme `Y` with an action `ρ` of `F` by
`X`-automorphisms, given on the copy indexed by `σ` by `x' ↦ (σ x', x')`. -/
def galoisCoveringMap (Y : Over X) (ρ : F →* Aut Y) :
    (∐ fun _ : F ↦ Y.left) ⟶ pullback Y.hom Y.hom :=
  Sigma.desc fun σ ↦ pullback.lift (ρ σ).hom.left (𝟙 Y.left) (by simp)

@[reassoc (attr := simp)]
lemma ι_galoisCoveringMap_fst (Y : Over X) (ρ : F →* Aut Y) (σ : F) :
    Sigma.ι (fun _ : F ↦ Y.left) σ ≫ galoisCoveringMap Y ρ ≫ pullback.fst Y.hom Y.hom =
      (ρ σ).hom.left := by
  rw [galoisCoveringMap, Sigma.ι_desc_assoc]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma ι_galoisCoveringMap_snd (Y : Over X) (ρ : F →* Aut Y) (σ : F) :
    Sigma.ι (fun _ : F ↦ Y.left) σ ≫ galoisCoveringMap Y ρ ≫ pullback.snd Y.hom Y.hom =
      𝟙 Y.left := by
  rw [galoisCoveringMap, Sigma.ι_desc_assoc]
  exact pullback.lift_snd _ _ _

/-- An `X`-scheme `Y` with a left action `ρ` of `F` by `X`-automorphisms is an
*`F`-Galois covering space* of `X` if `Y → X` is étale and surjective and the morphism
`∐_{σ ∈ F} Y → Y ×_X Y`, `x' ↦ (σ x', x')` on the copy indexed by `σ`, is an isomorphism. -/
@[weil "def_fk102_galois_covering_space"]
structure IsGaloisCovering (Y : Over X) (ρ : F →* Aut Y) : Prop where
  etale : Etale Y.hom
  surjective : Surjective Y.hom
  isIso_galoisCoveringMap : IsIso (galoisCoveringMap Y ρ)

section Tensor

variable [Finite F]

/-- The morphism `Y ×_X F̃_X → Y ×_X Y` from the fibre product with the constant group scheme
`F̃_X = ∐_{σ ∈ F} X`, given on the copy of `Y` indexed by `σ` by `x' ↦ (σ x', x')`. -/
def galoisCoveringMapOfTensor (Y : Over X) (ρ : F →* Aut Y) :
    (Y ⊗ sigmaConstOver X F).left ⟶ pullback Y.hom Y.hom :=
  Cofan.IsColimit.desc (sigmaConstOver.isColimit_tensorCopy (F := F) Y).some
    fun σ ↦ pullback.lift (ρ σ).hom.left (𝟙 Y.left) (by simp)

@[reassoc (attr := simp)]
lemma tensorCopy_galoisCoveringMapOfTensor (Y : Over X) (ρ : F →* Aut Y) (σ : F) :
    sigmaConstOver.tensorCopy Y σ ≫ galoisCoveringMapOfTensor Y ρ =
      pullback.lift (ρ σ).hom.left (𝟙 Y.left) (by simp) :=
  Cofan.IsColimit.fac (sigmaConstOver.isColimit_tensorCopy (F := F) Y).some _ σ

omit [Group F] in
/-- The identification of `Y ×_X F̃_X` with `∐_{σ ∈ F} Y`, the copy indexed by `σ`. -/
def tensorSigmaConstOverIso (Y : Over X) :
    (∐ fun _ : F ↦ Y.left) ≅ (Y ⊗ sigmaConstOver X F).left :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso
    (sigmaConstOver.isColimit_tensorCopy (F := F) Y).some

omit [Group F] in
@[reassoc (attr := simp)]
lemma ι_tensorSigmaConstOverIso_hom (Y : Over X) (σ : F) :
    Sigma.ι (fun _ : F ↦ Y.left) σ ≫ (tensorSigmaConstOverIso Y).hom =
      sigmaConstOver.tensorCopy Y σ :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom _ ⟨σ⟩

lemma tensorSigmaConstOverIso_hom_galoisCoveringMapOfTensor (Y : Over X) (ρ : F →* Aut Y) :
    (tensorSigmaConstOverIso Y).hom ≫ galoisCoveringMapOfTensor Y ρ =
      galoisCoveringMap Y ρ := by
  refine Sigma.hom_ext _ _ fun σ ↦ ?_
  simp [galoisCoveringMap]

lemma isIso_galoisCoveringMapOfTensor_iff (Y : Over X) (ρ : F →* Aut Y) :
    IsIso (galoisCoveringMapOfTensor Y ρ) ↔ IsIso (galoisCoveringMap Y ρ) := by
  rw [← tensorSigmaConstOverIso_hom_galoisCoveringMapOfTensor]
  exact (isIso_comp_left_iff _ _).symm

/-- The definition of a Galois covering space through the fibre product `Y ×_X F̃_X` with the
constant group scheme. -/
lemma isGaloisCovering_iff_isIso_galoisCoveringMapOfTensor (Y : Over X) (ρ : F →* Aut Y) :
    IsGaloisCovering Y ρ ↔
      Etale Y.hom ∧ Surjective Y.hom ∧ IsIso (galoisCoveringMapOfTensor Y ρ) := by
  rw [isIso_galoisCoveringMapOfTensor_iff]
  exact ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

end Tensor

end AlgebraicGeometry
