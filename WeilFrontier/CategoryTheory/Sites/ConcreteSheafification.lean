module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.CoveringMorphism
public import WeilFrontier.AlgebraicGeometry.Sites.CoveringSectionsMap
public import WeilFrontier.Defs.CategoryTheory.Sites.Plus

/-!
# Restricting a class of the plus construction to a member of its sieve

Let `P` be a presheaf on a site `(C, J)` with values in a concrete category `D` (sets or
abelian groups in the application to the étale site), let `S` be a covering sieve on `X`
and `x` a matching family of `P` on `S`, with class `mk x` in `P⁺(X)`. For every
morphism `f : Y ⟶ X` belonging to `S`, the restriction of `mk x` along `f` is the image
of the component `x_f ∈ P(Y)` under the canonical map `θ : P ⟶ P⁺`.

The proof: the pull-back of `S` along `f` is the maximal sieve on `Y`, and the pulled-back
family is the family of restrictions of `x_f`.

## Main results

* `CategoryTheory.GrothendieckTopology.Plus.map_mk_eq_toPlus_app`: for `f ∈ S`,
  `P⁺(f)(mk x) = θ_Y (x_f)`.

## Implementation notes

The plus construction is Mathlib's `CategoryTheory.GrothendieckTopology.plusObj`, the
colimit over covering sieves of the multiequalizers `Meq P S`; the map `θ` is
`CategoryTheory.GrothendieckTopology.toPlus`. The content is Mathlib's
`CategoryTheory.GrothendieckTopology.Plus.toPlus_apply`, restated here with the member
given as a morphism together with a proof of membership.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §2.
-/

@[expose] public section

namespace CategoryTheory.GrothendieckTopology.Plus

open Limits

universe t w' w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable {FD : D → D → Type*} {CD : D → Type t} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
variable [ConcreteCategory.{t} D FD]
variable [∀ {X : C} (S : J.Cover X),
  PreservesLimitsOfShape (WalkingMulticospan S.shape) (forget D)]
variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

/-- The restriction of the class `mk x` of a matching family `x` on a covering sieve `S`
along a morphism `f` of `S` is `θ` applied to the component `x_f`. -/
@[weil "lem_fk102_plus_restriction_member"]
theorem map_mk_eq_toPlus_app {X Y : C} {P : Cᵒᵖ ⥤ D} (S : J.Cover X) (x : Meq P S)
    (f : Y ⟶ X) (hf : (S : Sieve X) f) :
    (J.plusObj P).map f.op (mk x) = (J.toPlus P).app (Opposite.op Y) (x ⟨Y, f, hf⟩) :=
  (toPlus_apply S x ⟨Y, f, hf⟩).symm

end CategoryTheory.GrothendieckTopology.Plus

end

/-! ### Equality of classes in the plus construction -/

/-!
# Equality of classes in the plus construction

Let `A` be a commutative ring, `F` a presheaf on the étale category `Et(A)`, `B` an object of
`Et(A)`, `𝔅₁`, `𝔅₂` coverings of `B` and `sₗ ∈ F(𝔅ₗ)`. Then `[𝔅₁, s₁] = [𝔅₂, s₂]` in `F̃(B)` if
and only if there are a covering `𝔅₃` of `B` and morphisms of coverings `φₗ : 𝔅ₗ ⟶ 𝔅₃` with
`φ₁_* s₁ = φ₂_* s₂`.

For presheaves of sets, the relation "`(𝔅₁, s₁) ≈ (𝔅₂, s₂)` if such `𝔅₃, φ₁, φ₂` exist" is an
equivalence relation: transitivity uses that the coverings of `B` are directed
(`Covering.cocone_objs`) and that two morphisms of coverings `𝔅 ⟶ 𝔅'` induce the same map
`F(𝔅) → F(𝔅')` (`Covering.HomOver.sectionsMap_eq`). It contains the generating relation of
`F̃(B)` and is contained in the equivalence relation it generates, so it is that relation.

For presheaves of abelian groups, an element `x` of `⨁_𝔅 F(𝔅)` can be pushed to any covering `T`
receiving a morphism from every covering in the support of `x`, giving `∑_𝔅 φ_𝔅* (x_𝔅) ∈ F(T)`,
independent of the morphisms `φ_𝔅` chosen. The elements whose push to some such `T` vanishes form
a subgroup containing the generating relations, which gives the claim.

## Main results

- `AlgebraicGeometry.EtaleCategory.plusConstruction.mk_eq_mk_iff_exists`: the criterion for
  presheaves of sets.
- `AlgebraicGeometry.EtaleCategory.addPlusConstruction.mk_eq_mk_iff_exists`: the criterion for
  presheaves of abelian groups.

## Implementation notes

Mathlib's `CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists` is the analogous criterion
for the plus construction indexed by covering sieves; the statements here are for the colimit over
the category `Cov(B)` of covering families, which is not filtered as a category (parallel
morphisms of coverings need not be equal), only after applying `𝔅 ↦ F(𝔅)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}} {B : EtaleCategory A}

open Covering

namespace plusConstruction

variable {F : EtaleCategory A ⥤ Type v}

/-- **Equality in the plus construction** (presheaves of sets). `[𝔅₁, s₁] = [𝔅₂, s₂]` in `F̃(B)`
if and only if there are a covering `𝔅₃` of `B` and morphisms of coverings `φₗ : 𝔅ₗ ⟶ 𝔅₃` with
`φ₁_* s₁ = φ₂_* s₂`. -/
@[weil "lem_fk101_plus_construction_equal_iff"]
theorem mk_eq_mk_iff_exists {𝔅₁ 𝔅₂ : Covering.{w} B} (s₁ : coveringSections F 𝔅₁.map)
    (s₂ : coveringSections F 𝔅₂.map) :
    mk 𝔅₁ s₁ = mk 𝔅₂ s₂ ↔ ∃ (𝔅₃ : Covering.{w} B) (φ₁ : 𝔅₁ ⟶ 𝔅₃) (φ₂ : 𝔅₂ ⟶ 𝔅₃),
      HomOver.sectionsMap F φ₁ s₁ = HomOver.sectionsMap F φ₂ s₂ := by
  constructor
  · intro h
    rw [mk_eq_mk_iff] at h
    -- the relation `≈` on pairs `(𝔅, s)`
    let R : (Σ 𝔅 : Covering.{w} B, coveringSections F 𝔅.map) →
        (Σ 𝔅 : Covering.{w} B, coveringSections F 𝔅.map) → Prop :=
      fun p q ↦ ∃ (𝔅₃ : Covering.{w} B) (φ₁ : p.1 ⟶ 𝔅₃) (φ₂ : q.1 ⟶ 𝔅₃),
        HomOver.sectionsMap F φ₁ p.2 = HomOver.sectionsMap F φ₂ q.2
    have hR : Equivalence R := by
      refine ⟨fun p ↦ ⟨p.1, 𝟙 _, 𝟙 _, rfl⟩, fun ⟨𝔅₃, φ₁, φ₂, e⟩ ↦ ⟨𝔅₃, φ₂, φ₁, e.symm⟩, ?_⟩
      rintro p q r ⟨𝔅₃, φ₁, φ₂, e⟩ ⟨𝔅₅, ψ₂, ψ₄, e'⟩
      obtain ⟨𝔅₆, χ, χ', -⟩ := Covering.cocone_objs 𝔅₃ 𝔅₅
      refine ⟨𝔅₆, φ₁ ≫ χ, ψ₄ ≫ χ', ?_⟩
      rw [sectionsMap_comp', sectionsMap_comp', e, ← e', ← sectionsMap_comp',
        ← sectionsMap_comp']
      exact congrFun (HomOver.sectionsMap_eq F (φ₂ ≫ χ) (ψ₂ ≫ χ')) q.2
    have hle : ∀ p q, Relation.EqvGen (sectionsFunctor.{w} F B).ColimitTypeRel p q → R p q := by
      intro p q hpq
      induction hpq with
      | rel p q hpq =>
        obtain ⟨φ, e⟩ := hpq
        exact ⟨q.1, φ, 𝟙 _, ((sectionsMap_id' F q.2).trans e).symm⟩
      | refl p => exact hR.refl p
      | symm p q _ ih => exact hR.symm ih
      | trans p q r _ _ ih ih' => exact hR.trans ih ih'
    exact hle _ _ h
  · rintro ⟨𝔅₃, φ₁, φ₂, e⟩
    rw [← mk_sectionsMap φ₁, ← mk_sectionsMap φ₂, e]

end plusConstruction

namespace addPlusConstruction

variable (F : EtaleCategory A ⥤ AddCommGrpCat.{v})

/-- The homomorphism `F(𝔅) → F(T)` induced by some morphism of coverings `𝔅 ⟶ T` if there is
one (it does not depend on the choice), and `0` otherwise. -/
def toTarget (T 𝔅 : Covering.{w} B) :
    (sectionsAddFunctor.{w} F B).obj 𝔅 ⟶ (sectionsAddFunctor.{w} F B).obj T :=
  open Classical in
  if h : Nonempty (𝔅 ⟶ T) then (sectionsAddFunctor.{w} F B).map h.some else 0

lemma toTarget_eq {T 𝔅 : Covering.{w} B} (φ : 𝔅 ⟶ T) :
    toTarget F T 𝔅 = (sectionsAddFunctor.{w} F B).map φ := by
  have h : Nonempty (𝔅 ⟶ T) := ⟨φ⟩
  simp only [toTarget, h, ↓reduceDIte]
  exact congrArg AddCommGrpCat.ofHom (HomOver.sectionsAddMonoidHom_eq F _ _)

/-- The push `∑_𝔅 φ_𝔅* (x_𝔅) ∈ F(T)` of an element `x` of `⨁_𝔅 F(𝔅)` to a covering `T`. -/
def pushTo [DecidableEq (Covering.{w} B)] (T : Covering.{w} B) :
    DFinsupp (fun 𝔅 ↦ (sectionsAddFunctor.{w} F B).obj 𝔅) →+
      (sectionsAddFunctor.{w} F B).obj T :=
  DFinsupp.sumAddHom fun 𝔅 ↦ (toTarget F T 𝔅).hom

lemma pushTo_single [DecidableEq (Covering.{w} B)] {T 𝔅 : Covering.{w} B} (φ : 𝔅 ⟶ T)
    (s : (sectionsAddFunctor.{w} F B).obj 𝔅) :
    pushTo F T (DFinsupp.single 𝔅 s) = (sectionsAddFunctor.{w} F B).map φ s := by
  rw [pushTo, DFinsupp.sumAddHom_single, toTarget_eq F φ]

open Classical in
lemma pushTo_eq_of_hom [DecidableEq (Covering.{w} B)] {T T' : Covering.{w} B}
    (x : DFinsupp (fun 𝔅 ↦ (sectionsAddFunctor.{w} F B).obj 𝔅))
    (hx : ∀ 𝔅 ∈ x.support, Nonempty (𝔅 ⟶ T)) (ψ : T ⟶ T') :
    pushTo F T' x = (sectionsAddFunctor.{w} F B).map ψ (pushTo F T x) := by
  rw [pushTo, pushTo, DFinsupp.sumAddHom_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
    DFinsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun 𝔅 h𝔅 ↦ ?_
  obtain ⟨φ⟩ := hx 𝔅 h𝔅
  rw [toTarget_eq F φ, toTarget_eq F (φ ≫ ψ), Functor.map_comp, AddCommGrpCat.hom_comp]
  rfl

open Classical in
/-- Every element of the subgroup of relations of `⨁_𝔅 F(𝔅)` pushes to `0` in some covering
receiving morphisms from all coverings in its support. -/
lemma exists_pushTo_eq_zero [DecidableEq (Covering.{w} B)] (T₀ : Covering.{w} B)
    {x : DFinsupp (fun 𝔅 ↦ (sectionsAddFunctor.{w} F B).obj 𝔅)}
    (hx : x ∈ AddCommGrpCat.Colimits.Relations (sectionsAddFunctor.{w} F B)) :
    ∃ T : Covering.{w} B, (∀ 𝔅 ∈ x.support, Nonempty (𝔅 ⟶ T)) ∧ pushTo F T x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨𝔅, 𝔅', u, a, rfl⟩ := hx
    refine ⟨𝔅', fun 𝔅'' h ↦ ?_, ?_⟩
    · rw [DFinsupp.mem_support_iff, DFinsupp.sub_apply] at h
      by_cases h₁ : 𝔅'' = 𝔅'
      · subst h₁; exact ⟨𝟙 _⟩
      by_cases h₂ : 𝔅'' = 𝔅
      · subst h₂; exact ⟨u⟩
      exfalso
      exact h (by simp [DFinsupp.single_apply, Ne.symm h₁, Ne.symm h₂])
    · rw [map_sub, pushTo_single F (𝟙 𝔅'), pushTo_single F u, CategoryTheory.Functor.map_id,
        sub_eq_zero]
      rfl
  | zero => exact ⟨T₀, by simp, map_zero _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨T₁, h₁, e₁⟩ := ihx
    obtain ⟨T₂, h₂, e₂⟩ := ihy
    refine ⟨T₁.inf T₂, fun 𝔅 h𝔅 ↦ ?_, ?_⟩
    · rcases Finset.mem_union.1 (DFinsupp.support_add h𝔅) with h | h
      · exact (h₁ 𝔅 h).map (· ≫ toInfLeft T₁ T₂)
      · exact (h₂ 𝔅 h).map (· ≫ toInfRight T₁ T₂)
    · rw [map_add, pushTo_eq_of_hom F x h₁ (toInfLeft T₁ T₂),
        pushTo_eq_of_hom F y h₂ (toInfRight T₁ T₂), e₁, e₂, map_zero, map_zero, add_zero]
  | neg x _ ih =>
    obtain ⟨T, h, e⟩ := ih
    exact ⟨T, by rwa [DFinsupp.support_neg], by rw [map_neg, e, neg_zero]⟩

/-- **Equality in the plus construction** (presheaves of abelian groups). `[𝔅₁, s₁] = [𝔅₂, s₂]`
in `F̃(B)` if and only if there are a covering `𝔅₃` of `B` and morphisms of coverings
`φₗ : 𝔅ₗ ⟶ 𝔅₃` with `φ₁_* s₁ = φ₂_* s₂`. -/
@[weil "lem_fk101_plus_construction_equal_iff"]
theorem mk_eq_mk_iff_exists {𝔅₁ 𝔅₂ : Covering.{w} B}
    (s₁ : coveringSectionsAddSubgroup F 𝔅₁.map) (s₂ : coveringSectionsAddSubgroup F 𝔅₂.map) :
    mk 𝔅₁ s₁ = mk 𝔅₂ s₂ ↔ ∃ (𝔅₃ : Covering.{w} B) (φ₁ : 𝔅₁ ⟶ 𝔅₃) (φ₂ : 𝔅₂ ⟶ 𝔅₃),
      HomOver.sectionsAddMonoidHom F φ₁ s₁ = HomOver.sectionsAddMonoidHom F φ₂ s₂ := by
  constructor
  · intro h
    let := Classical.decEq (Covering.{w} B)
    let t₁ : (sectionsAddFunctor.{w} F B).obj 𝔅₁ := s₁
    let t₂ : (sectionsAddFunctor.{w} F B).obj 𝔅₂ := s₂
    have h' : -DFinsupp.single 𝔅₁ t₁ + DFinsupp.single 𝔅₂ t₂ ∈
        AddCommGrpCat.Colimits.Relations (sectionsAddFunctor.{w} F B) :=
      QuotientAddGroup.eq.1 h
    obtain ⟨T, hT, e⟩ := exists_pushTo_eq_zero F 𝔅₁ h'
    let ψ : T ⟶ (T.inf 𝔅₁).inf 𝔅₂ := toInfLeft T 𝔅₁ ≫ toInfLeft _ 𝔅₂
    let φ₁ : 𝔅₁ ⟶ (T.inf 𝔅₁).inf 𝔅₂ := toInfRight T 𝔅₁ ≫ toInfLeft _ 𝔅₂
    let φ₂ : 𝔅₂ ⟶ (T.inf 𝔅₁).inf 𝔅₂ := toInfRight _ 𝔅₂
    refine ⟨_, φ₁, φ₂, ?_⟩
    have e' := pushTo_eq_of_hom F _ hT ψ
    rw [e, map_zero, map_add, map_neg, pushTo_single F φ₁, pushTo_single F φ₂] at e'
    exact neg_add_eq_zero.1 e'
  · rintro ⟨𝔅₃, φ₁, φ₂, e⟩
    rw [← mk_sectionsAddMonoidHom φ₁, ← mk_sectionsAddMonoidHom φ₂, e]

end addPlusConstruction

end EtaleCategory

end AlgebraicGeometry
