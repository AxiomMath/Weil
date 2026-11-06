module

public import Weil.Attr
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import Weil.AlgebraicGeometry.Sites.Bridges.ConstantSheaf

/-!
# Formally principal sheaves

Let `(C, J)` be a site and `G` a sheaf of groups on it. A sheaf of sets `𝒢` with a right action
of `G`, that is, a morphism of sheaves `𝒢 × G → 𝒢`, `(t, σ) ↦ t ^ σ`, which is a right group
action on the sections over every object, is *formally principal* if the morphism of sheaves
`G × 𝒢 → 𝒢 × 𝒢`, `(σ, t) ↦ (t ^ σ, t)` is an isomorphism. Equivalently, on every set of
sections `𝒢(U)` the group `G(U)` acts simply transitively (or `𝒢(U)` is empty).

The main case is the constant sheaf of groups `F_X` of locally constant `F`-valued maps on the
étale category `Et(X)` of a locally noetherian scheme `X`, for a group `F`.

Turning the right action into the left action `σ • t = t ^ σ⁻¹`, formally principal sheaves
with right `G`-action are the same as pseudo `G`-torsors in the sense of Stacks, Tag 03AH
(`PseudoTorsor`).

## Main definitions

* `SheafOfGroups.RightAction G`: a sheaf of sets with a right action of the sheaf of groups `G`.
* `SheafOfGroups.RightAction.actMap`: the morphism `G × 𝒢 ⟶ 𝒢 × 𝒢`, `(σ, t) ↦ (t ^ σ, t)`.
* `SheafOfGroups.RightAction.IsFormallyPrincipal`: `actMap` is an isomorphism.
* `SheafOfGroups.RightAction.toPseudoTorsor`: a formally principal sheaf as a pseudo torsor.
* `PseudoTorsor.toRightAction`: a pseudo torsor as a sheaf with right action.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantSheafOfGroups`: the constant
  sheaf of groups `F_X` on `Et(X)`, as a sheaf of groups.

## Main results

* `SheafOfGroups.RightAction.isFormallyPrincipal_iff`: `𝒢` is formally principal if and only
  if for all sections `s, t ∈ 𝒢(U)` there is a unique `σ ∈ G(U)` with `t ^ σ = s`.
* `SheafOfGroups.RightAction.isFormallyPrincipal_toRightAction`: a pseudo torsor is
  formally principal.

## Implementation notes

The product of presheaves of sets is the pointwise product (the cartesian monoidal structure
on the functor category), whose sections over `U` are the pairs of sections over `U`. Since
sheaves form a full subcategory of presheaves, `actMap` is an isomorphism of sheaves if and only
if it is an isomorphism of presheaves, which is how `IsFormallyPrincipal` is stated.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory

universe w v u

namespace SheafOfGroups

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The restriction maps of a sheaf of groups, as group homomorphisms. -/
def mapMonoidHom (G : SheafOfGroups.{w} (C := C) J) {U V : Cᵒᵖ} (f : U ⟶ V) :
    G.presheaf.obj U →* G.presheaf.obj V :=
  MonoidHom.mk' (G.presheaf.map f) (G.map_mul f)

@[simp]
lemma mapMonoidHom_apply (G : SheafOfGroups.{w} (C := C) J) {U V : Cᵒᵖ} (f : U ⟶ V)
    (g : G.presheaf.obj U) : G.mapMonoidHom f g = G.presheaf.map f g :=
  rfl

/-- The restriction maps of a sheaf of groups preserve inverses. -/
lemma mapMonoidHom_inv (G : SheafOfGroups.{w} (C := C) J) {U V : Cᵒᵖ} (f : U ⟶ V)
    (g : G.presheaf.obj U) : G.presheaf.map f g⁻¹ = (G.presheaf.map f g)⁻¹ :=
  (G.mapMonoidHom f).map_inv g

/-- **A sheaf of sets with a right action of a sheaf of groups `G`**: a sheaf of sets `𝒢`
with maps `𝒢(U) × G(U) → 𝒢(U)`, `(t, σ) ↦ t ^ σ`, which are right group actions and commute
with restriction, i.e. form a morphism of sheaves `𝒢 × G → 𝒢`. -/
@[weil "def_fk102_formal_torsor_sheaf"]
structure RightAction (G : SheafOfGroups.{w} (C := C) J) where
  /-- The underlying presheaf of sets. -/
  presheaf : Cᵒᵖ ⥤ Type w
  /-- The sheaf condition. -/
  isSheaf : Presheaf.IsSheaf J presheaf
  /-- The right action `(t, σ) ↦ t ^ σ` of the sections of `G` on the sections of `𝒢`. -/
  act : ∀ U, presheaf.obj U → G.presheaf.obj U → presheaf.obj U
  /-- The unit acts trivially. -/
  act_one : ∀ U (t : presheaf.obj U), act U t 1 = t
  /-- `t ^ (σ * τ) = (t ^ σ) ^ τ`. -/
  act_mul : ∀ U (t : presheaf.obj U) (σ τ : G.presheaf.obj U),
    act U t (σ * τ) = act U (act U t σ) τ
  /-- The action commutes with restriction. -/
  naturality : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (t : presheaf.obj U) (σ : G.presheaf.obj U),
    presheaf.map f (act U t σ) = act V (presheaf.map f t) (G.presheaf.map f σ)

namespace RightAction

variable {G : SheafOfGroups.{w} (C := C) J} (𝒢 : RightAction G)

/-- The morphism of presheaves `G × 𝒢 ⟶ 𝒢 × 𝒢`, `(σ, t) ↦ (t ^ σ, t)`. -/
def actMap : G.presheaf ⊗ 𝒢.presheaf ⟶ 𝒢.presheaf ⊗ 𝒢.presheaf where
  app U := TypeCat.ofHom fun p => (𝒢.act U p.2 p.1, p.2)
  naturality U V f := by
    ext p
    exact Prod.ext (𝒢.naturality f p.2 p.1).symm rfl

@[simp]
lemma actMap_app_apply (U : Cᵒᵖ) (p : G.presheaf.obj U × 𝒢.presheaf.obj U) :
    𝒢.actMap.app U p = (𝒢.act U p.2 p.1, p.2) :=
  rfl

/-- **Formally principal sheaves.** A sheaf `𝒢` with right action of `G` is *formally
principal* if the morphism `G × 𝒢 ⟶ 𝒢 × 𝒢`, `(σ, t) ↦ (t ^ σ, t)`, is an isomorphism. -/
@[weil "def_fk102_formal_torsor_sheaf"]
def IsFormallyPrincipal : Prop :=
  IsIso 𝒢.actMap

/-- `𝒢` is formally principal if and only if for all sections `s, t` of `𝒢` over `U` there is
a unique section `σ` of `G` over `U` with `t ^ σ = s`. -/
theorem isFormallyPrincipal_iff :
    𝒢.IsFormallyPrincipal ↔
      ∀ U (s t : 𝒢.presheaf.obj U), ∃! σ : G.presheaf.obj U, 𝒢.act U t σ = s := by
  unfold IsFormallyPrincipal
  rw [NatTrans.isIso_iff_isIso_app]
  refine forall_congr' fun U => ?_
  rw [isIso_iff_bijective]
  change Function.Bijective (fun p : G.presheaf.obj U × 𝒢.presheaf.obj U =>
    (𝒢.act U p.2 p.1, p.2)) ↔ _
  constructor
  · intro h s t
    obtain ⟨⟨σ, t'⟩, hx⟩ := h.2 (s, t)
    simp only [Prod.mk.injEq] at hx
    obtain ⟨hx, rfl⟩ := hx
    refine ⟨σ, hx, fun τ hτ => ?_⟩
    have := @h.1 (τ, t') (σ, t') (by simp [hx, hτ])
    exact congrArg Prod.fst this
  · intro h
    refine ⟨fun ⟨σ, t⟩ ⟨τ, t'⟩ hy => ?_, fun ⟨s, t⟩ => ?_⟩
    · simp only [Prod.mk.injEq] at hy
      obtain ⟨hy, rfl⟩ := hy
      obtain ⟨ρ, -, huniq⟩ := h (𝒢.act U t τ) t
      exact Prod.ext ((huniq σ hy).trans (huniq τ rfl).symm) rfl
    · obtain ⟨σ, hσ, -⟩ := h s t
      exact ⟨(σ, t), by simp [hσ]⟩

/-- The left action `σ • t = t ^ σ⁻¹` associated with a right action. -/
lemma act_inv_act (U : Cᵒᵖ) (t : 𝒢.presheaf.obj U) (σ : G.presheaf.obj U) :
    𝒢.act U (𝒢.act U t σ) σ⁻¹ = t := by
  rw [← 𝒢.act_mul, mul_inv_cancel, 𝒢.act_one]

/-- A formally principal sheaf with right `G`-action, as a pseudo `G`-torsor (Stacks,
Tag 03AH) for the left action `σ • t = t ^ σ⁻¹`. -/
def toPseudoTorsor (h : 𝒢.IsFormallyPrincipal) : PseudoTorsor.{w} (C := C) G where
  presheaf := 𝒢.presheaf
  isSheaf := 𝒢.isSheaf
  act U σ t := 𝒢.act U t σ⁻¹
  one_act U t := by simp [𝒢.act_one]
  mul_act U σ τ t := by simp [mul_inv_rev, 𝒢.act_mul]
  naturality f σ t := by simp [𝒢.naturality, mapMonoidHom_inv]
  simplyTransitive U _ s t := by
    obtain ⟨σ, hσ, huniq⟩ := (𝒢.isFormallyPrincipal_iff.mp h) U t s
    refine ⟨σ⁻¹, by simpa using hσ, fun τ hτ => ?_⟩
    rw [← inv_inv τ, huniq τ⁻¹ hτ]

@[simp]
lemma toPseudoTorsor_presheaf (h : 𝒢.IsFormallyPrincipal) :
    (𝒢.toPseudoTorsor h).presheaf = 𝒢.presheaf :=
  rfl

@[simp]
lemma toPseudoTorsor_act (h : 𝒢.IsFormallyPrincipal) (U : Cᵒᵖ) (σ : G.presheaf.obj U)
    (t : 𝒢.presheaf.obj U) : (𝒢.toPseudoTorsor h).act U σ t = 𝒢.act U t σ⁻¹ :=
  rfl

end RightAction

end SheafOfGroups

namespace PseudoTorsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : SheafOfGroups.{w} (C := C) J} (T : PseudoTorsor.{w} (C := C) G)

/-- A pseudo `G`-torsor as a sheaf with right `G`-action `t ^ σ = σ⁻¹ • t`. -/
def toRightAction : SheafOfGroups.RightAction G where
  presheaf := T.presheaf
  isSheaf := T.isSheaf
  act U t σ := T.act U σ⁻¹ t
  act_one U t := by simp [T.one_act]
  act_mul U t σ τ := by simp [mul_inv_rev, T.mul_act]
  naturality f t σ := by simp [T.naturality, SheafOfGroups.mapMonoidHom_inv]

@[simp]
lemma toRightAction_presheaf : T.toRightAction.presheaf = T.presheaf :=
  rfl

@[simp]
lemma toRightAction_act (U : Cᵒᵖ) (t : T.presheaf.obj U) (σ : G.presheaf.obj U) :
    T.toRightAction.act U t σ = T.act U σ⁻¹ t :=
  rfl

end PseudoTorsor

namespace SheafOfGroups.RightAction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : SheafOfGroups.{w} (C := C) J}

/-- A pseudo `G`-torsor, with its right action `t ^ σ = σ⁻¹ • t`, is formally principal. -/
theorem isFormallyPrincipal_toRightAction (T : PseudoTorsor.{w} (C := C) G) :
    T.toRightAction.IsFormallyPrincipal := by
  rw [isFormallyPrincipal_iff]
  intro U s t
  obtain ⟨g, hg, huniq⟩ := T.simplyTransitive U ⟨t⟩ t s
  refine ⟨g⁻¹, ?_, fun τ hτ => ?_⟩
  · change T.act U g⁻¹⁻¹ t = s
    rw [inv_inv]
    exact hg
  · rw [← inv_inv τ, huniq τ⁻¹ hτ]

/-- Turning a formally principal sheaf into a pseudo torsor and back gives the same action. -/
lemma toRightAction_toPseudoTorsor_act (𝒢 : RightAction G) (h : 𝒢.IsFormallyPrincipal)
    (U : Cᵒᵖ) (t : 𝒢.presheaf.obj U) (σ : G.presheaf.obj U) :
    (𝒢.toPseudoTorsor h).toRightAction.act U t σ = 𝒢.act U t σ := by
  change 𝒢.act U t σ⁻¹⁻¹ = 𝒢.act U t σ
  rw [inv_inv]

/-- Turning a pseudo torsor into a formally principal sheaf and back gives the same action. -/
lemma toPseudoTorsor_toRightAction_act (T : PseudoTorsor.{w} (C := C) G) (U : Cᵒᵖ)
    (σ : G.presheaf.obj U) (t : T.presheaf.obj U) :
    (T.toRightAction.toPseudoTorsor (isFormallyPrincipal_toRightAction T)).act U σ t =
      T.act U σ t := by
  change T.act U σ⁻¹⁻¹ t = T.act U σ t
  rw [inv_inv]

end SheafOfGroups.RightAction

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]

/-- **The constant sheaf of groups `F_S` on `Et(S)`** for a group `F`: the sheaf of locally
constant maps `|U| → F`, a group under pointwise multiplication. -/
def locallyConstantSheafOfGroups (F : Type w) [Group F] :
    SheafOfGroups.{max u w} (C := SmallNoetherianSeparatedEtale B S hS) (topology B S hS) where
  presheaf := locallyConstantPresheaf B S hS F
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).mpr (locallyConstantPresheaf_isSheaf F)
  group U := inferInstanceAs (Group (LocallyConstant ((toScheme B S hS).obj U.unop) F))
  map_mul _ _ _ := rfl

lemma locallyConstantSheafOfGroups_presheaf (F : Type w) [Group F] :
    (locallyConstantSheafOfGroups B S hS F).presheaf = locallyConstantPresheaf B S hS F :=
  rfl

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
