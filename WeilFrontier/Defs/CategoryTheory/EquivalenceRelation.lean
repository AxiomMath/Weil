module

public import Mathlib.CategoryTheory.EquivalenceRelation
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Equivalence relations in categories of sheaves of sets

A pair of morphisms `u v : R ⟶ G` of sheaves of sets on a site *represents an equivalence
relation* if for every object `U` the map `(u_U, v_U) : R(U) → G(U) × G(U)` is injective and its
image is an equivalence relation on the set `G(U)`.

This is the internal notion `CategoryTheory.IsEquivalenceRelation u v` of Mathlib (a jointly
monic pair with reflexivity, symmetry and transitivity morphisms) in the category
`Sheaf J (Type w)`: since finite limits of sheaves of sets are computed sectionwise, the
internal notion is equivalent to the sectionwise one. We prove this equivalence for an arbitrary
site, and state it for the small étale site of a scheme.

## Main definitions

* `CategoryTheory.Sheaf.liftOfSectionwise`: a morphism into a sectionwise injective pair,
  built from sections.

## Main results

* `CategoryTheory.Types.jointlyMono₂_iff_injective`: a pair of maps of types is jointly monic
  if and only if the induced map into the product is injective.
* `CategoryTheory.Types.isEquivalenceRelation_iff`: internal equivalence relations in the
  category of types are the injective pairs whose image is an equivalence relation.
* `CategoryTheory.Sheaf.isEquivalenceRelation_iff_forall`: a pair `u v : R ⟶ G` of sheaves of
  sets is an internal equivalence relation if and only if, for every object `U`, the map
  `(u_U, v_U)` is injective and its image is an equivalence relation on `G(U)`.
* `AlgebraicGeometry.SmallEtale.isEquivalenceRelation_iff_forall`: the same on the small étale
  site of a scheme.

## Implementation notes

The definition of an equivalence relation of sheaves is not a new declaration: it is
`CategoryTheory.IsEquivalenceRelation u v` in `Sheaf J (Type w)`, and the sectionwise form is
the characterization `CategoryTheory.Sheaf.isEquivalenceRelation_iff_forall`. The site is the
small étale site `AlgebraicGeometry.SmallEtale` of a scheme in a big étale site, whose objects
are all étale schemes over `S` (rather than only the noetherian separated ones).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §4.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Types

variable {R X : Type w} {p₁ p₂ : R ⟶ X}

/-- A pair of maps of types is jointly monic if and only if the induced map into the product
is injective. -/
lemma jointlyMono₂_iff_injective :
    JointlyMono₂ p₁ p₂ ↔ Function.Injective (fun r => (p₁ r, p₂ r)) := by
  constructor
  · intro h a b hab
    have h₁ : p₁ a = p₁ b := congr($hab.1)
    have h₂ : p₂ a = p₂ b := congr($hab.2)
    have := h.right_cancellation (Y := PUnit.{w + 1}) (↾fun _ => a) (↾fun _ => b)
      (by ext; exact h₁) (by ext; exact h₂)
    exact congr($this PUnit.unit)
  · intro h
    refine ⟨fun Y f g h₁ h₂ => ?_⟩
    ext y
    exact h (Prod.ext congr($h₁ y) congr($h₂ y))

/-- An internal equivalence relation in the category of types is an injective pair of maps
whose image is an equivalence relation. -/
lemma isEquivalenceRelation_iff :
    IsEquivalenceRelation p₁ p₂ ↔ Function.Injective (fun r => (p₁ r, p₂ r)) ∧
      _root_.Equivalence (TypeCat.Rel.ofPair p₁ p₂) := by
  constructor
  · rintro ⟨⟨e⟩⟩
    exact ⟨jointlyMono₂_iff_injective.1 e.toJointlyMono₂,
      TypeCat.equivalence_of_equivalenceRelation e⟩
  · rintro ⟨hinj, hequiv⟩
    have hmono : JointlyMono₂ p₁ p₂ := jointlyMono₂_iff_injective.2 hinj
    choose lift hlift₁ hlift₂ using fun (x : X × X) (hx : TypeCat.Rel.ofPair p₁ p₂ x.1 x.2) => hx
    refine EquivalenceRelation.isEquivalenceRelation
      { toJointlyMono₂ := hmono
        r := ↾fun x => lift (x, x) (hequiv.refl x)
        reflexivity₁ := by ext x; exact hlift₁ _ _
        reflexivity₂ := by ext x; exact hlift₂ _ _
        s := ↾fun r => lift (p₂ r, p₁ r) (hequiv.symm ⟨r, rfl, rfl⟩)
        symmetry₁ := by ext r; exact hlift₁ _ _
        symmetry₂ := by ext r; exact hlift₂ _ _
        c := Types.pullbackCone p₂ p₁
        isLimit := (Types.pullbackLimitCone p₂ p₁).isLimit
        t := ↾fun x => lift (p₁ x.1.1, p₂ x.1.2)
          (hequiv.trans ⟨x.1.1, rfl, rfl⟩ (by rw [x.2]; exact ⟨x.1.2, rfl, rfl⟩))
        transitivity₁ := by ext x; exact hlift₁ _ _
        transitivity₂ := by ext x; exact hlift₂ _ _ }

end Types

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R G : Sheaf J (Type w)} {u v : R ⟶ G}

/-- Given a pair `u v : R ⟶ G` of sheaves of sets which is sectionwise injective, a pair of
morphisms `φ ψ : Y ⟶ G` whose values are sectionwise related by `(u, v)` lifts to a morphism
`Y ⟶ R`. -/
noncomputable def liftOfSectionwise
    (hinj : ∀ U : C, Function.Injective
      (fun r : R.obj.obj (op U) => (u.hom.app (op U) r, v.hom.app (op U) r)))
    {Y : Sheaf J (Type w)} (φ ψ : Y ⟶ G)
    (h : ∀ (U : C) (y : Y.obj.obj (op U)), ∃ r : R.obj.obj (op U),
      u.hom.app (op U) r = φ.hom.app (op U) y ∧ v.hom.app (op U) r = ψ.hom.app (op U) y) :
    Y ⟶ R :=
  ObjectProperty.homMk
    { app := fun U => ↾fun y => (h U.unop y).choose
      naturality := fun U U' f => by
        ext y
        apply hinj U'.unop
        refine Prod.ext ?_ ?_
        · dsimp
          have h₁ := (h U'.unop ((Y.obj.map f) y)).choose_spec.1
          have h₂ := (h U.unop y).choose_spec.1
          dsimp at h₁ h₂
          rw [h₁, NatTrans.naturality_apply u.hom, h₂, NatTrans.naturality_apply φ.hom]
        · dsimp
          have h₁ := (h U'.unop ((Y.obj.map f) y)).choose_spec.2
          have h₂ := (h U.unop y).choose_spec.2
          dsimp at h₁ h₂
          rw [h₁, NatTrans.naturality_apply v.hom, h₂, NatTrans.naturality_apply ψ.hom] }

section lift

variable (hinj : ∀ U : C, Function.Injective
      (fun r : R.obj.obj (op U) => (u.hom.app (op U) r, v.hom.app (op U) r)))
    {Y : Sheaf J (Type w)} (φ ψ : Y ⟶ G)
    (h : ∀ (U : C) (y : Y.obj.obj (op U)), ∃ r : R.obj.obj (op U),
      u.hom.app (op U) r = φ.hom.app (op U) y ∧ v.hom.app (op U) r = ψ.hom.app (op U) y)

@[reassoc (attr := simp)]
lemma liftOfSectionwise_fst : liftOfSectionwise hinj φ ψ h ≫ u = φ := by
  ext U y
  exact (h U.unop y).choose_spec.1

@[reassoc (attr := simp)]
lemma liftOfSectionwise_snd : liftOfSectionwise hinj φ ψ h ≫ v = ψ := by
  ext U y
  exact (h U.unop y).choose_spec.2

end lift

/-- A pair `u v : R ⟶ G` of morphisms of sheaves of sets is an internal equivalence relation
in the category of sheaves if and only if, for every object `U` of the site, the map
`(u_U, v_U) : R(U) → G(U) × G(U)` is injective and its image is an equivalence relation on
`G(U)`. -/
theorem isEquivalenceRelation_iff_forall :
    IsEquivalenceRelation u v ↔ ∀ U : C,
      Function.Injective (fun r : R.obj.obj (op U) => (u.hom.app (op U) r, v.hom.app (op U) r)) ∧
        _root_.Equivalence (TypeCat.Rel.ofPair (u.hom.app (op U)) (v.hom.app (op U))) := by
  constructor
  · intro h U
    let F := (sheafSections J (Type w)).obj (op U)
    have : PreservesLimitsOfShape (Discrete WalkingPair) F :=
      inferInstanceAs (PreservesLimitsOfShape _
        (sheafToPresheaf J (Type w) ⋙ (evaluation _ _).obj (op U)))
    have : PreservesLimitsOfShape WalkingCospan F :=
      inferInstanceAs (PreservesLimitsOfShape _
        (sheafToPresheaf J (Type w) ⋙ (evaluation _ _).obj (op U)))
    exact Types.isEquivalenceRelation_iff.1 (isEquivalenceRelation_map F u v h)
  · intro H
    have hinj : ∀ U : C, Function.Injective
        (fun r : R.obj.obj (op U) => (u.hom.app (op U) r, v.hom.app (op U) r)) :=
      fun U => (H U).1
    refine EquivalenceRelation.isEquivalenceRelation
      { right_cancellation := fun Y f g h₁ h₂ => by
          ext U y
          exact hinj U.unop (Prod.ext congr((($h₁).hom.app U) y) congr((($h₂).hom.app U) y))
        r := liftOfSectionwise hinj (𝟙 G) (𝟙 G) fun U x => (H U).2.refl x
        s := liftOfSectionwise hinj v u fun U r => (H U).2.symm ⟨r, rfl, rfl⟩
        c := PullbackCone.mk _ _ (pullback.condition (f := v) (g := u))
        isLimit := pullbackIsPullback v u
        t := liftOfSectionwise hinj (pullback.fst v u ≫ u) (pullback.snd v u ≫ v) fun U x =>
          (H U).2.trans ⟨_, rfl, rfl⟩ (by
            have hx : v.hom.app (op U) ((pullback.fst v u).hom.app (op U) x) =
                u.hom.app (op U) ((pullback.snd v u).hom.app (op U) x) :=
              congr((($(pullback.condition (f := v) (g := u))).hom.app (op U)) x)
            exact ⟨(pullback.snd v u).hom.app (op U) x, hx.symm, rfl⟩) }

end Sheaf

end CategoryTheory

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {R G : Sheaf (SmallEtale.topology B S hS) (Type w)} {u v : R ⟶ G}

/-- A pair `u v : R ⟶ G` of morphisms of étale sheaves of sets on `S` represents an equivalence
relation (it is an internal equivalence relation in the category of étale sheaves of sets) if and
only if, for every étale `S`-scheme `U`, the map `(u_U, v_U) : R(U) → G(U) × G(U)` is injective
and its image is an equivalence relation on the set `G(U)`. -/
@[weil "def_fk104_sheaf_equivalence_relation"]
theorem SmallEtale.isEquivalenceRelation_iff_forall :
    IsEquivalenceRelation u v ↔ ∀ U : SmallEtale B S hS,
      Function.Injective (fun r : R.obj.obj (op U) => (u.hom.app (op U) r, v.hom.app (op U) r)) ∧
        _root_.Equivalence (TypeCat.Rel.ofPair (u.hom.app (op U)) (v.hom.app (op U))) :=
  Sheaf.isEquivalenceRelation_iff_forall

end AlgebraicGeometry
