module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import WeilFrontier.Defs.CategoryTheory.Yoneda

/-!
# The action of the constant sheaf `F_X` on `h_{X'}` induced by an action on `X'`

Let `F` be a group and `X'` an `X`-scheme on which `F` acts by `X`-automorphisms,
`τ ↦ a_τ` with `a_{ττ'} = a_τ ∘ a_{τ'}` and `a_1 = id`. For an `X`-scheme `U`, a locally constant
map `σ : |U| → F` and an `X`-morphism `t : U ⟶ X'`, the morphism `t^σ : U ⟶ X'` is the one whose
restriction to the open and closed subset `{σ = τ}` of `U` is `a_{τ⁻¹} ∘ t`. When `U` is
noetherian these subsets are unions of connected components of `U`, so `t^σ` restricted to a
connected component `U_c` on which `σ` takes the value `σ_c` is `a_{σ_c⁻¹} ∘ t|_{U_c}`.

The rule `t ↦ t^σ` is a right action of the group of locally constant maps `|U| → F` on
`Hom_X(U, X')`, compatible with restriction along `X`-morphisms `V ⟶ U`. On the étale category
`Et(X)` this is the induced right action of the constant sheaf `F_X` on the presheaf `h_{X'}`.

## Main definitions

* `AlgebraicGeometry.Scheme.twistByLocallyConstant` — for a family `a : F → (Y ⟶ Y)` of
  endomorphisms of a scheme `Y`, a locally constant `σ : |U| → F` and `t : U ⟶ Y`, the morphism
  equal to `t ≫ a τ` on `{σ = τ}`.
* `AlgebraicGeometry.Over.locallyConstantSMul` — the morphism `t^σ` of `X`-schemes, for an action
  `ρ : F →* Aut X'` by `X`-automorphisms.
* `AlgebraicGeometry.Over.locallyConstantMulAction` — the right action `t ↦ t^σ` of
  `LocallyConstant U F` on `U ⟶ X'`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.inducedMulAction` — the induced right action
  of the sections of the constant sheaf `F_X` on the sections of `h_{X'}` over an object of
  `Et(X)`.

## Main results

* `AlgebraicGeometry.Scheme.comp_twistByLocallyConstant_of_forall` — on any `V ⟶ U` along which
  `σ` is constant with value `τ`, `t^σ` restricts to `t ≫ a τ`; in particular
  `AlgebraicGeometry.Scheme.ι_twistByLocallyConstant` on the fibres and on connected components.
* `AlgebraicGeometry.Scheme.comp_twistByLocallyConstant` — compatibility with restriction.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.inducedMulAction_map` — the restriction maps
  of `h_{X'}` are equivariant for the restriction maps of `F_X`.

## Implementation notes

The definition does not need `F` finite nor `U` noetherian: the fibres `{σ = τ}` of a locally
constant map form an open cover of `U` by pairwise disjoint opens, on which the morphisms
`t ≫ a τ` glue. The right action is written as a left action of the opposite group
`(LocallyConstant U F)ᵐᵒᵖ`, the convention of Mathlib.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry

namespace Scheme

variable {F : Type w} [Group F] {U Y : Scheme.{u}}

/-- The morphisms `t ≫ a τ` on the fibres `{σ = τ}` agree on overlaps. -/
lemma twistByLocallyConstant_compat (a : F → (Y ⟶ Y)) (σ : LocallyConstant U F) (t : U ⟶ Y)
    (g h : F) :
    pullback.fst ((fiberCover F σ).f g) ((fiberCover F σ).f h) ≫
        ((fiberCover F σ).f g ≫ t ≫ a g) =
      pullback.snd _ _ ≫ ((fiberCover F σ).f h ≫ t ≫ a h) := by
  let 𝒰 := fiberCover F σ
  by_cases e : g = h
  · subst h
    have : IsOpenImmersion (𝒰.f g) := 𝒰.map_prop g
    rw [← Category.assoc, ← Category.assoc,
      (Mono.right_cancellation _ _ pullback.condition :
        pullback.fst (𝒰.f g) (𝒰.f g) = pullback.snd _ _)]
    rfl
  · have hEmpty : IsEmpty ↑(pullback (𝒰.f g) (𝒰.f h)) := by
      refine ⟨fun x ↦ e ?_⟩
      have hx : (𝒰.f g) ((pullback.fst (𝒰.f g) (𝒰.f h)) x) =
          (𝒰.f h) ((pullback.snd (𝒰.f g) (𝒰.f h)) x) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      have hg : σ ((𝒰.f g) ((pullback.fst (𝒰.f g) (𝒰.f h)) x)) = g :=
        ((pullback.fst (𝒰.f g) (𝒰.f h)) x).property
      have hh : σ ((𝒰.f h) ((pullback.snd (𝒰.f g) (𝒰.f h)) x)) = h :=
        ((pullback.snd (𝒰.f g) (𝒰.f h)) x).property
      exact hg.symm.trans ((congrArg σ hx).trans hh)
    exact (isInitialOfIsEmpty (X := pullback (𝒰.f g) (𝒰.f h))).hom_ext _ _

/-- **Twisting a morphism by a locally constant map.** For a family `a : F → (Y ⟶ Y)` of
endomorphisms of `Y`, a locally constant map `σ : |U| → F` and `t : U ⟶ Y`, the morphism
`U ⟶ Y` whose restriction to the open subset `{σ = τ}` is `t ≫ a τ`, for every `τ : F`. -/
noncomputable def twistByLocallyConstant (a : F → (Y ⟶ Y)) (σ : LocallyConstant U F)
    (t : U ⟶ Y) : U ⟶ Y :=
  (fiberCover F σ).glueMorphisms (fun g ↦ (fiberCover F σ).f g ≫ t ≫ a g)
    (twistByLocallyConstant_compat a σ t)

/-- On the fibre `{σ = τ}`, the twist of `t` by `σ` is `t ≫ a τ`. -/
@[reassoc (attr := simp)]
lemma ι_fiberOpen_twistByLocallyConstant (a : F → (Y ⟶ Y)) (σ : LocallyConstant U F)
    (t : U ⟶ Y) (τ : F) :
    (fiberOpen F σ τ).ι ≫ twistByLocallyConstant a σ t = (fiberOpen F σ τ).ι ≫ t ≫ a τ :=
  (fiberCover F σ).ι_glueMorphisms _ (twistByLocallyConstant_compat a σ t) τ

/-- **The twist on a piece where `σ` is constant.** For a morphism `f : V ⟶ U` along which `σ`
takes the constant value `τ` (for instance the inclusion of a connected component of `U` on which
`σ` is `τ`), `f ≫ t^σ = f ≫ t ≫ a τ`. -/
lemma comp_twistByLocallyConstant_of_forall {V : Scheme.{u}} (f : V ⟶ U)
    (a : F → (Y ⟶ Y)) (σ : LocallyConstant U F) (t : U ⟶ Y) (τ : F)
    (hf : ∀ x, σ (f x) = τ) :
    f ≫ twistByLocallyConstant a σ t = f ≫ t ≫ a τ := by
  have hR : Set.range f ⊆ Set.range (fiberOpen F σ τ).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf x
  rw [← IsOpenImmersion.lift_fac (fiberOpen F σ τ).ι f hR, Category.assoc,
    ι_fiberOpen_twistByLocallyConstant, Category.assoc]

/-- On an open subset `W` of `U` on which `σ` takes the constant value `τ` (for instance a
connected component of `U` when the components are open), `t^σ` restricts to `t ≫ a τ`. -/
lemma ι_twistByLocallyConstant (W : U.Opens) (a : F → (Y ⟶ Y)) (σ : LocallyConstant U F)
    (t : U ⟶ Y) (τ : F) (hW : ∀ x ∈ W, σ x = τ) :
    W.ι ≫ twistByLocallyConstant a σ t = W.ι ≫ t ≫ a τ :=
  comp_twistByLocallyConstant_of_forall W.ι a σ t τ fun x ↦
    hW _ ((Scheme.Opens.range_ι W).subset ⟨x, rfl⟩)

/-- Twisting by a constant map is composition with the corresponding endomorphism. -/
@[simp]
lemma twistByLocallyConstant_const (a : F → (Y ⟶ Y)) (τ : F) (t : U ⟶ Y) :
    twistByLocallyConstant a (LocallyConstant.const U τ) t = t ≫ a τ := by
  simpa using comp_twistByLocallyConstant_of_forall (𝟙 U) a (LocallyConstant.const U τ) t τ
    fun _ ↦ rfl

/-- **Compatibility with restriction.** For `f : V ⟶ U`, `f ≫ t^σ = (f ≫ t)^{σ ∘ f}`. -/
lemma comp_twistByLocallyConstant {V : Scheme.{u}} (f : V ⟶ U) (a : F → (Y ⟶ Y))
    (σ : LocallyConstant U F) (t : U ⟶ Y) :
    f ≫ twistByLocallyConstant a σ t =
      twistByLocallyConstant a (σ.comap f.base.hom) (f ≫ t) := by
  refine hom_ext_of_forall _ _ fun x ↦ ⟨fiberOpen F (σ.comap f.base.hom) (σ (f x)), rfl, ?_⟩
  rw [ι_fiberOpen_twistByLocallyConstant, ← Category.assoc,
    comp_twistByLocallyConstant_of_forall ((fiberOpen F (σ.comap f.base.hom) (σ (f x))).ι ≫ f)
      a σ t _ fun y ↦ y.2]
  simp only [Category.assoc]

/-- The twist is compatible with postcomposition by a morphism `p : Y ⟶ Z` fixed by every
`a τ`: `t^σ ≫ p = t ≫ p`. -/
@[reassoc]
lemma twistByLocallyConstant_comp {Z : Scheme.{u}} (a : F → (Y ⟶ Y)) (σ : LocallyConstant U F)
    (t : U ⟶ Y) (p : Y ⟶ Z) (hp : ∀ τ, a τ ≫ p = p) :
    twistByLocallyConstant a σ t ≫ p = t ≫ p := by
  refine hom_ext_of_forall _ _ fun x ↦ ⟨fiberOpen F σ (σ x), rfl, ?_⟩
  rw [ι_fiberOpen_twistByLocallyConstant_assoc, hp]

/-- Twisting twice: if `a (τ * τ') = a τ ≫ a τ'`, then `(t^σ)^{σ'} = t^{σ * σ'}`. -/
lemma twistByLocallyConstant_twistByLocallyConstant (a : F → (Y ⟶ Y))
    (ha : ∀ τ τ', a (τ * τ') = a τ ≫ a τ') (σ σ' : LocallyConstant U F) (t : U ⟶ Y) :
    twistByLocallyConstant a σ' (twistByLocallyConstant a σ t) =
      twistByLocallyConstant a (σ * σ') t := by
  refine hom_ext_of_forall _ _ fun x ↦ ⟨fiberOpen F σ (σ x) ⊓ fiberOpen F σ' (σ' x),
    ⟨rfl, rfl⟩, ?_⟩
  set W := fiberOpen F σ (σ x) ⊓ fiberOpen F σ' (σ' x)
  rw [ι_twistByLocallyConstant W a σ' _ (σ' x) fun y hy ↦ hy.2, ← Category.assoc,
    ι_twistByLocallyConstant W a σ t (σ x) fun y hy ↦ hy.1,
    ι_twistByLocallyConstant W a (σ * σ') t (σ x * σ' x) fun y hy ↦ by
      simp only [LocallyConstant.coe_mul, Pi.mul_apply]
      rw [hy.1, hy.2], ha]
  simp only [Category.assoc]

/-- Twisting by the constant map `1` is the identity when `a 1 = 𝟙`. -/
lemma twistByLocallyConstant_one (a : F → (Y ⟶ Y)) (ha : a 1 = 𝟙 Y) (t : U ⟶ Y) :
    twistByLocallyConstant a 1 t = t := by
  rw [show (1 : LocallyConstant U F) = LocallyConstant.const U 1 from rfl,
    twistByLocallyConstant_const, ha, Category.comp_id]

end Scheme

namespace Over

variable {X : Scheme.{u}} {F : Type w} [Group F]

/-- The family of scheme endomorphisms `τ ↦ a_{τ⁻¹}` of `X'` attached to an action
`ρ : F →* Aut X'` by `X`-automorphisms. -/
abbrev invActionHom {X' : Over X} (ρ : F →* Aut X') (τ : F) : X'.left ⟶ X'.left :=
  (ρ τ⁻¹).hom.left

lemma invActionHom_mul {X' : Over X} (ρ : F →* Aut X') (τ τ' : F) :
    invActionHom ρ (τ * τ') = invActionHom ρ τ ≫ invActionHom ρ τ' := by
  simp only [invActionHom, mul_inv_rev, map_mul, Aut.Aut_mul_def]
  rfl

lemma invActionHom_one {X' : Over X} (ρ : F →* Aut X') : invActionHom ρ 1 = 𝟙 X'.left := by
  simp only [invActionHom, inv_one, map_one]
  rfl

/-- **The morphism `t^σ`.** For an action `ρ : F →* Aut X'` of a group `F` on an `X`-scheme `X'`
by `X`-automorphisms, an `X`-scheme `U`, a locally constant map `σ : |U| → F` and an
`X`-morphism `t : U ⟶ X'`, the `X`-morphism `t^σ : U ⟶ X'` whose restriction to `{σ = τ}` is
`a_{τ⁻¹} ∘ t`, with `a_τ = ρ τ`. -/
noncomputable def locallyConstantSMul {U X' : Over X} (ρ : F →* Aut X')
    (σ : LocallyConstant U.left F) (t : U ⟶ X') : U ⟶ X' :=
  Over.homMk (Scheme.twistByLocallyConstant (invActionHom ρ) σ t.left) (by
    rw [Scheme.twistByLocallyConstant_comp _ _ _ _ fun τ ↦ Over.w (ρ τ⁻¹).hom, Over.w])

@[simp]
lemma locallyConstantSMul_left {U X' : Over X} (ρ : F →* Aut X')
    (σ : LocallyConstant U.left F) (t : U ⟶ X') :
    (locallyConstantSMul ρ σ t).left =
      Scheme.twistByLocallyConstant (invActionHom ρ) σ t.left :=
  rfl

/-- On a piece `f : V ⟶ U` along which `σ` is constant with value `τ` (e.g. a connected
component of `U`), `t^σ` restricts to `a_{τ⁻¹} ∘ t`. -/
lemma comp_locallyConstantSMul_left_of_forall {U X' : Over X} {V : Scheme.{u}}
    (f : V ⟶ U.left) (ρ : F →* Aut X') (σ : LocallyConstant U.left F) (t : U ⟶ X') (τ : F)
    (hf : ∀ x, σ (f x) = τ) :
    f ≫ (locallyConstantSMul ρ σ t).left = f ≫ t.left ≫ (ρ τ⁻¹).hom.left :=
  Scheme.comp_twistByLocallyConstant_of_forall f _ σ t.left τ hf

/-- **The right action of `LocallyConstant U F` on `Hom_X(U, X')`**, `t ↦ t^σ`, written as a left
action of the opposite group. -/
@[instance_reducible]
noncomputable def locallyConstantMulAction {U X' : Over X} (ρ : F →* Aut X') :
    MulAction (LocallyConstant U.left F)ᵐᵒᵖ (U ⟶ X') where
  smul σ t := locallyConstantSMul ρ σ.unop t
  one_smul t := by
    ext1
    exact Scheme.twistByLocallyConstant_one _ (invActionHom_one ρ) t.left
  mul_smul σ σ' t := by
    ext1
    exact (Scheme.twistByLocallyConstant_twistByLocallyConstant _ (invActionHom_mul ρ)
      σ'.unop σ.unop t.left).symm

/-- Compatibility of `t ↦ t^σ` with restriction along an `X`-morphism `f : V ⟶ U`. -/
lemma comp_locallyConstantSMul {U V X' : Over X} (f : V ⟶ U) (ρ : F →* Aut X')
    (σ : LocallyConstant U.left F) (t : U ⟶ X') :
    f ≫ locallyConstantSMul ρ σ t = locallyConstantSMul ρ (σ.comap f.left.base.hom) (f ≫ t) := by
  ext1
  exact Scheme.comp_twistByLocallyConstant f.left _ σ t.left

end Over

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {F : Type w} [Group F]
  {X' : Over X}

/-- **The induced right action of `F_X` on `h_{X'}`.** For a group `F` acting on an `X`-scheme `X'`
by `X`-automorphisms through `ρ : F →* Aut X'`, and an object `U` of `Et(X)`, the right action of
the sections `σ ∈ F_X(U)` (locally constant maps `|U| → F`) on the sections `t ∈ h_{X'}(U)`
(`X`-morphisms `U ⟶ X'`): `t^σ` is the morphism whose restriction to each connected component
`U_c` of `U`, on which `σ` takes the value `σ_c`, is `a_{σ_c⁻¹} ∘ t|_{U_c}`. -/
@[weil "def_fk102_induced_action_on_points", instance_reducible]
noncomputable def inducedMulAction (ρ : F →* Aut X') (U : SmallNoetherianSeparatedEtale B X hX) :
    MulAction ((locallyConstantPresheafGrp B X hX F).obj (op U))ᵐᵒᵖ
      ((representablePresheaf B X hX X').obj (op U)) :=
  Over.locallyConstantMulAction (U := (toOver B X hX).obj U) ρ

/-- `t^σ` on a connected component (or any piece `f : V ⟶ U` on which `σ` is constant with value
`τ`) is `a_{τ⁻¹} ∘ t`. -/
@[weil "def_fk102_induced_action_on_points"]
lemma comp_inducedMulAction_smul_left_of_forall (ρ : F →* Aut X')
    {U : SmallNoetherianSeparatedEtale B X hX} {V : Scheme.{u}} (f : V ⟶ (toScheme B X hX).obj U)
    (σ : (locallyConstantPresheafGrp B X hX F).obj (op U))
    (t : (representablePresheaf B X hX X').obj (op U)) (τ : F)
    (hf : ∀ x, (show LocallyConstant ((toScheme B X hX).obj U) F from σ) (f x) = τ) :
    f ≫ (letI := inducedMulAction ρ U; (MulOpposite.op σ • t :
      (representablePresheaf B X hX X').obj (op U))).left =
      f ≫ (show (toOver B X hX).obj U ⟶ X' from t).left ≫ (ρ τ⁻¹).hom.left :=
  Over.comp_locallyConstantSMul_left_of_forall (U := (toOver B X hX).obj U) f ρ σ t τ hf

/-- The restriction maps of `h_{X'}` are equivariant for the restriction maps of `F_X`:
`(t^σ)|_V = (t|_V)^{σ|_V}` for `h : V ⟶ U` in `Et(X)`. -/
lemma inducedMulAction_map (ρ : F →* Aut X') {U V : SmallNoetherianSeparatedEtale B X hX}
    (h : V ⟶ U) (σ : (locallyConstantPresheafGrp B X hX F).obj (op U))
    (t : (representablePresheaf B X hX X').obj (op U)) :
    (representablePresheaf B X hX X').map h.op
        (letI := inducedMulAction ρ U; MulOpposite.op σ • t) =
      (letI := inducedMulAction ρ V;
        MulOpposite.op ((locallyConstantPresheafGrp B X hX F).map h.op σ) •
          (representablePresheaf B X hX X').map h.op t) :=
  Over.comp_locallyConstantSMul ((toOver B X hX).map h) ρ σ t

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
