module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData

/-!
# Threefold fibre products, their projections, and pulled-back gluing maps

Let `f : T ⟶ S` be a morphism. We write `T ×_S T` for the fibre product of `f` with itself, with
projections `p₁, p₂`, and `T ×_S T ×_S T` for the threefold fibre product, with the projections
`p₁₂, p₂₃, p₁₃ : T ×_S T ×_S T ⟶ T ×_S T` onto two of the factors and `q₁, q₂, q₃ : T ×_S T ×_S T ⟶ T`
onto one factor. They satisfy `p₁₂ ≫ p₁ = q₁`, `p₁₂ ≫ p₂ = q₂`, `p₂₃ ≫ p₁ = q₂`, `p₂₃ ≫ p₂ = q₃`,
`p₁₃ ≫ p₁ = q₁` and `p₁₃ ≫ p₂ = q₃`. The diagonals `δ : T ⟶ T ×_S T` and
`δ₃ : T ⟶ T ×_S T ×_S T` satisfy `δ ≫ pₖ = 𝟙 T`, `δ₃ ≫ pᵢⱼ = δ` and `δ₃ ≫ qₘ = 𝟙 T`.

For a morphism of schemes `u : Z ⟶ T ×_S T` and a morphism of sheaves of modules
`σ : p₁^* 𝒩 ⟶ p₂^* 𝒩`, the pulled-back morphism `u^⋆ σ : (u ≫ p₁)^* 𝒩 ⟶ (u ≫ p₂)^* 𝒩` is
`c_{u,p₂} ∘ u^* σ ∘ c_{u,p₁}⁻¹`, where `c_{u,v} : u^* v^* 𝒩 ≅ (u ≫ v)^* 𝒩` is the canonical
isomorphism. This is Mathlib's `Pseudofunctor.LocallyDiscreteOpToCat.pullHom` for the
pullback pseudofunctor of sheaves of modules; in particular `p_{ij}^⋆ σ : q_i^* 𝒩 ⟶ q_j^* 𝒩`
and `δ^⋆ σ : 𝒩 ⟶ 𝒩`.

## Main definitions

* `CategoryTheory.Limits.ChosenPullback.ofPullback`: the fibre product given by
  `HasPullback`, as a `ChosenPullback`.
* `CategoryTheory.Limits.ChosenPullback₃.ofHasPullback`: the threefold fibre product built from
  chosen binary fibre products, as a `ChosenPullback₃`.
* `CategoryTheory.Limits.selfPullback f`: `T ×_S T` with its projections `p₁, p₂`.
* `CategoryTheory.Limits.selfPullback₃ f`: `T ×_S T ×_S T` with its projections
  `p₁₂, p₂₃, p₁₃` and `p₁, p₂, p₃` (the `qₘ`).
* `CategoryTheory.Limits.selfPullback₃.diagonal f`: the diagonal `T ⟶ T ×_S T ×_S T`.
* `AlgebraicGeometry.Scheme.Modules.diagonalPullHom`: `δ^⋆ σ : 𝒩 ⟶ 𝒩`.

## Main results

* `CategoryTheory.Limits.selfPullback₃_projections`: the six relations between the `pᵢⱼ` and the
  `qₘ`.
* `CategoryTheory.Limits.selfPullback₃.diagonal_projections`: the relations satisfied by the
  diagonals.
* `AlgebraicGeometry.Scheme.Modules.pullHom_eq`: `pullHom σ u` is
  `c_{u,p₂} ∘ u^* σ ∘ c_{u,p₁}⁻¹`, written with `Scheme.Modules.pullbackComp`.

## Implementation notes

The fibre products are Mathlib's `ChosenPullback` and `ChosenPullback₃`, the presentation used by
`Pseudofunctor.DescentData'`, so that descent data written with these projections are directly
Mathlib's. The pulled-back morphism `u^⋆ σ` is Mathlib's `pullHom` for the pseudofunctor
`AlgebraicGeometry.modulePullbackPseudofunctor`; `Scheme.Modules.pullHom_eq` identifies it with
the formula through the composition isomorphisms `Scheme.Modules.pullbackComp`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III, p. 306.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The fibre product of `f₁` and `f₂` provided by `HasPullback`, as a chosen pullback. -/
noncomputable abbrev ChosenPullback.ofPullback {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] : ChosenPullback f₁ f₂ where
  pullback := Limits.pullback f₁ f₂
  p₁ := pullback.fst f₁ f₂
  p₂ := pullback.snd f₁ f₂
  condition := pullback.condition
  isLimit := pullbackIsPullback f₁ f₂

lemma ChosenPullback.ofPullback_p₁ {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] : (ChosenPullback.ofPullback f₁ f₂).p₁ = pullback.fst f₁ f₂ := rfl

lemma ChosenPullback.ofPullback_p₂ {X₁ X₂ S : C} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    [HasPullback f₁ f₂] : (ChosenPullback.ofPullback f₁ f₂).p₂ = pullback.snd f₁ f₂ := rfl

/-- The threefold fibre product of `f₁, f₂, f₃` built, from chosen fibre products of the pairs,
as the fibre product of `h₁₂.p₂` and `h₂₃.p₁` provided by `HasPullback`. -/
noncomputable def ChosenPullback₃.ofHasPullback {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    {f₃ : X₃ ⟶ S} (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) [HasPullback h₁₂.p₂ h₂₃.p₁] : ChosenPullback₃ h₁₂ h₂₃ h₁₃ where
  chosenPullback := ChosenPullback.ofPullback h₁₂.p₂ h₂₃.p₁
  l :=
    { f := h₁₃.isPullback.lift ((ChosenPullback.ofPullback h₁₂.p₂ h₂₃.p₁).p₁ ≫ h₁₂.p₁)
        ((ChosenPullback.ofPullback h₁₂.p₂ h₂₃.p₁).p₂ ≫ h₂₃.p₂) (by
          rw [Category.assoc, Category.assoc, h₁₂.condition, ← h₂₃.condition,
            (ChosenPullback.ofPullback h₁₂.p₂ h₂₃.p₁).condition_assoc])
      f_p₁ := IsPullback.lift_fst _ _ _ _
      f_p₂ := IsPullback.lift_snd _ _ _ _
      f_p := by
        rw [← h₁₃.hp₁, IsPullback.lift_fst_assoc, Category.assoc, h₁₂.hp₁] }

section SelfPullback

variable {T S : C} (f : T ⟶ S) [HasPullbacks C]

/-- The fibre product `T ×_S T` of `f : T ⟶ S` with itself, with its projections `p₁, p₂`. -/
noncomputable abbrev selfPullback : ChosenPullback f f := ChosenPullback.ofPullback f f

@[reassoc (attr := simp)]
lemma diagonal_selfPullback_p₁ : pullback.diagonal f ≫ (selfPullback f).p₁ = 𝟙 T :=
  pullback.diagonal_fst f

@[reassoc (attr := simp)]
lemma diagonal_selfPullback_p₂ : pullback.diagonal f ≫ (selfPullback f).p₂ = 𝟙 T :=
  pullback.diagonal_snd f

/-- The threefold fibre product `T ×_S T ×_S T` of `f : T ⟶ S` with itself, with its projections
`p₁₂, p₂₃, p₁₃` onto `T ×_S T` and `p₁, p₂, p₃` onto `T`. -/
@[weil "not_fka3_triple_projections"]
noncomputable abbrev selfPullback₃ :
    ChosenPullback₃ (selfPullback f) (selfPullback f) (selfPullback f) :=
  ChosenPullback₃.ofHasPullback _ _ _

/-- The projections of the threefold fibre product onto two factors and onto one factor are
compatible: `p₁₂ ≫ p₁ = q₁`, `p₁₂ ≫ p₂ = q₂`, `p₂₃ ≫ p₁ = q₂`, `p₂₃ ≫ p₂ = q₃`, `p₁₃ ≫ p₁ = q₁`,
`p₁₃ ≫ p₂ = q₃`. -/
@[weil "not_fka3_triple_projections"]
theorem selfPullback₃_projections :
    (selfPullback₃ f).p₁₂ ≫ (selfPullback f).p₁ = (selfPullback₃ f).p₁ ∧
    (selfPullback₃ f).p₁₂ ≫ (selfPullback f).p₂ = (selfPullback₃ f).p₂ ∧
    (selfPullback₃ f).p₂₃ ≫ (selfPullback f).p₁ = (selfPullback₃ f).p₂ ∧
    (selfPullback₃ f).p₂₃ ≫ (selfPullback f).p₂ = (selfPullback₃ f).p₃ ∧
    (selfPullback₃ f).p₁₃ ≫ (selfPullback f).p₁ = (selfPullback₃ f).p₁ ∧
    (selfPullback₃ f).p₁₃ ≫ (selfPullback f).p₂ = (selfPullback₃ f).p₃ :=
  ⟨(selfPullback₃ f).p₁₂_p₁, (selfPullback₃ f).p₁₂_p₂, (selfPullback₃ f).p₂₃_p₂,
    (selfPullback₃ f).p₂₃_p₃, (selfPullback₃ f).p₁₃_p₁, (selfPullback₃ f).p₁₃_p₃⟩

/-- The diagonal `δ₃ : T ⟶ T ×_S T ×_S T`. -/
@[weil "not_fka3_triple_projections"]
noncomputable def selfPullback₃.diagonal : T ⟶ (selfPullback₃ f).pullback :=
  (selfPullback₃ f).chosenPullback.isPullback.lift (pullback.diagonal f) (pullback.diagonal f)
    (by simp)

@[reassoc (attr := simp)]
lemma selfPullback₃.diagonal_p₁₂ :
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₁₂ = pullback.diagonal f :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma selfPullback₃.diagonal_p₂₃ :
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₂₃ = pullback.diagonal f :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
lemma selfPullback₃.diagonal_p₁ :
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₁ = 𝟙 T := by
  rw [← (selfPullback₃ f).p₁₂_p₁, diagonal_p₁₂_assoc]
  simp

@[reassoc (attr := simp)]
lemma selfPullback₃.diagonal_p₂ :
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₂ = 𝟙 T := by
  rw [← (selfPullback₃ f).p₁₂_p₂, diagonal_p₁₂_assoc]
  simp

@[reassoc (attr := simp)]
lemma selfPullback₃.diagonal_p₃ :
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₃ = 𝟙 T := by
  rw [← (selfPullback₃ f).p₂₃_p₃, diagonal_p₂₃_assoc]
  simp

@[reassoc (attr := simp)]
lemma selfPullback₃.diagonal_p₁₃ :
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₁₃ = pullback.diagonal f := by
  apply (selfPullback f).hom_ext
  · rw [Category.assoc, (selfPullback₃ f).p₁₃_p₁, diagonal_p₁, diagonal_selfPullback_p₁]
  · rw [Category.assoc, (selfPullback₃ f).p₁₃_p₃, diagonal_p₃, diagonal_selfPullback_p₂]

/-- The diagonals `δ : T ⟶ T ×_S T` and `δ₃ : T ⟶ T ×_S T ×_S T` satisfy `δ ≫ pₖ = 𝟙 T`,
`δ₃ ≫ pᵢⱼ = δ` and `δ₃ ≫ qₘ = 𝟙 T`. -/
@[weil "not_fka3_triple_projections"]
theorem selfPullback₃.diagonal_projections :
    pullback.diagonal f ≫ (selfPullback f).p₁ = 𝟙 T ∧
    pullback.diagonal f ≫ (selfPullback f).p₂ = 𝟙 T ∧
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₁₂ = pullback.diagonal f ∧
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₂₃ = pullback.diagonal f ∧
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₁₃ = pullback.diagonal f ∧
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₁ = 𝟙 T ∧
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₂ = 𝟙 T ∧
    selfPullback₃.diagonal f ≫ (selfPullback₃ f).p₃ = 𝟙 T := by
  simp

end SelfPullback

end CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

/-- The pulled-back morphism `u^⋆ φ` of Mathlib's `pullHom`, for sheaves of modules on schemes,
is `c_{u,f₂} ∘ u^* φ ∘ c_{u,f₁}⁻¹`, where `c_{u,v} : u^* v^* ≅ (u ≫ v)^*` is
`Scheme.Modules.pullbackComp u v`. -/
@[weil "not_fka3_triple_projections"]
theorem pullHom_eq {X₁ X₂ Y Z : Scheme.{u}} {M₁ : X₁.Modules} {M₂ : X₂.Modules}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (u : Z ⟶ Y) :
    pullHom (F := modulePullbackPseudofunctor) φ u (u ≫ f₁) (u ≫ f₂) =
      (pullbackComp u f₁).inv.app M₁ ≫ (pullback u).map φ ≫ (pullbackComp u f₂).hom.app M₂ := by
  rfl

/-- For `σ : p₁^* 𝒩 ⟶ p₂^* 𝒩` on `T ×_S T`, the morphism `δ^⋆ σ : 𝒩 ⟶ 𝒩` obtained by pulling `σ`
back along the diagonal `δ : T ⟶ T ×_S T` and identifying `(𝟙 T)^* 𝒩` with `𝒩`. -/
@[weil "not_fka3_triple_projections"]
noncomputable def diagonalPullHom {T S : Scheme.{u}} (f : T ⟶ S) {N : T.Modules}
    (σ : (pullback (selfPullback f).p₁).obj N ⟶ (pullback (selfPullback f).p₂).obj N) :
    N ⟶ N :=
  (pullbackId T).inv.app N ≫
    pullHom (F := modulePullbackPseudofunctor) σ (pullback.diagonal f) (𝟙 T) (𝟙 T) ≫
      (pullbackId T).hom.app N

end AlgebraicGeometry.Scheme.Modules
