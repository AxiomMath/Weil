module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.PointedCoveringMorphism
public import Weil.Attr

/-!
# Two pointed Galois covering spaces are dominated by a third

Let `s` be a geometric point of a scheme `X` and let `(Y₁, α₁)`, `(Y₂, α₂)` be pointed Galois
covering spaces of `(X, s)`. Then there are a pointed Galois covering space `(Y₃, α₃)` of `(X, s)`
and mappings of pointed covering spaces `(Y₃, α₃) → (Y₁, α₁)` and `(Y₃, α₃) → (Y₂, α₂)`.

Over a connected base this is the cofilteredness of Mathlib's category of pointed Galois objects
(`CategoryTheory.PreGaloisCategory.PointedGaloisObject`) of the Galois category of covering spaces
with the geometric fibre functor at `s`, transported along
`AlgebraicGeometry.GeometricPoint.PointedGaloisCoveringSpace.equivPointedGaloisObject`.

For an arbitrary base `X` one reduces to that case. A covering space `p₁ : Y₁ ⟶ X` is finite
and étale, hence a closed and open map, so its image `U` is open and closed in `X`; it is
connected since `Y₁` is. The image of `Y₂` is connected and meets `U` at the point under `s`, so
it lies in `U`. The inclusion `ι : U ⟶ X` is an open and closed immersion, so composition with
`ι` identifies covering spaces of `U` with the covering spaces of `X` whose image lies in `U`,
and under this identification a covering space is Galois over `U` if and only if it is Galois
over `X`: composition with `ι` is fully faithful, so the automorphism groups agree, and the
geometric points of `X` over which the composite has a nonempty fibre all come from `U`, with
the same fibres.

## Main results

* `AlgebraicGeometry.GeometricPoint.PointedGaloisCoveringSpace.exists_isHom_isHom` — two
  pointed Galois covering spaces of `(X, s)` admit mappings of pointed covering spaces from a
  third one.
* `AlgebraicGeometry.GeometricPoint.PointedGaloisCoveringSpace.exists_cone` — the same
  statement in the category of pointed Galois covering spaces.
* `AlgebraicGeometry.Scheme.CoveringSpace.isGalois_compose_iff` — for an open and closed
  immersion `ι : U ⟶ X`, a covering space of `U` is Galois if and only if its composite with `ι`
  is a Galois covering space of `X`.

## Implementation notes

The source proves the statement by taking a connected covering space dominating `Y₁` and `Y₂`,
then a Galois covering space dominating it, and adjusting the base points with the transitive
action of `G(Y₂/X)` on the fibre. Over a connected base that argument is the proof of Mathlib's
`CategoryTheory.PreGaloisCategory.PointedGaloisObject` cofilteredness, which is used here; the
reduction to a connected base replaces the source's directedness statement for connected
covering spaces sharing a geometric point.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

/-- A geometric point of `X` whose image lies in the image of an open
immersion `ι : U ⟶ X` is `t₀ ∘ ι` for a geometric point `t₀` of `U`. -/
lemma exists_map_eq_of_range_subset {X U : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
    (t : GeometricPoint X) (h : Set.range t.hom ⊆ Set.range ι) :
    ∃ t₀ : GeometricPoint U, t₀.map ι = t := by
  refine ⟨⟨t.residueField, IsOpenImmersion.lift ι t.hom h⟩, ?_⟩
  cases t
  simp only [GeometricPoint.map, IsOpenImmersion.lift_fac]

end GeometricPoint

namespace Scheme.CoveringSpace

variable {X U : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι] [IsFinite ι]

/-- Composition with an open and closed immersion `ι : U ⟶ X`, as a functor `Cov(U) ⥤ Cov(X)`. -/
abbrev compose : U.CoveringSpace ⥤ X.CoveringSpace :=
  finiteEtaleCompose (f := ι) ⟨inferInstance, inferInstance⟩

/-- Composition with an open and closed immersion is fully faithful. -/
def fullyFaithfulCompose : (compose ι).FullyFaithful where
  preimage {W W'} g := MorphismProperty.Over.homMk g.left (by
    rw [← cancel_mono ι]
    exact (Category.assoc _ _ _).trans (MorphismProperty.Over.w g))

/-- A covering space of `X` whose image lies in the open and closed subscheme `U`, as a covering
space of `U`. -/
def restrict (Y : X.CoveringSpace) (h : Set.range Y.hom ⊆ Set.range ι) : U.CoveringSpace :=
  haveI : IsFinite (IsOpenImmersion.lift ι Y.hom h ≫ ι) := by
    rw [IsOpenImmersion.lift_fac]; infer_instance
  haveI : Etale (IsOpenImmersion.lift ι Y.hom h ≫ ι) := by
    rw [IsOpenImmersion.lift_fac]; infer_instance
  haveI := IsFinite.of_comp (IsOpenImmersion.lift ι Y.hom h) ι
  haveI := Etale.of_comp (IsOpenImmersion.lift ι Y.hom h) ι
  mk (IsOpenImmersion.lift ι Y.hom h)

lemma restrict_hom (Y : X.CoveringSpace) (h : Set.range Y.hom ⊆ Set.range ι) :
    (restrict ι Y h).hom = IsOpenImmersion.lift ι Y.hom h :=
  rfl

lemma compose_obj_restrict (Y : X.CoveringSpace) (h : Set.range Y.hom ⊆ Set.range ι) :
    (compose ι).obj (restrict ι Y h) = Y := by
  obtain ⟨⟨L, R, f⟩, p⟩ := Y
  have hf : IsOpenImmersion.lift ι f h ≫ ι = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨⟨⟩⟩ := R
  change (⟨⟨L, ⟨PUnit.unit⟩, IsOpenImmersion.lift ι f h ≫ ι⟩, ?_⟩ : X.CoveringSpace) = _
  congr

/-- The geometric points of a covering space `W` of `U` over `t` are those of its composite with
`ι` over `t ∘ ι`. -/
def fiberEquivCompose (W : U.CoveringSpace) (t : GeometricPoint U) :
    (finiteEtaleFiberFunctor t).obj W ≃
      (finiteEtaleFiberFunctor (t.map ι)).obj ((compose ι).obj W) where
  toFun a := ⟨a.1, by
    change a.1 ≫ W.hom ≫ ι = t.hom ≫ ι
    rw [← Category.assoc, a.2]⟩
  invFun b := ⟨b.1, by
    rw [← cancel_mono ι]
    exact (Category.assoc _ _ _).trans b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A covering space of `U` is Galois if and only if its composite with the open and closed
immersion `ι : U ⟶ X` is a Galois covering space of `X`. -/
theorem isGalois_compose_iff (W : U.CoveringSpace) :
    IsGalois ((compose ι).obj W) ↔ IsGalois W := by
  let e := (fullyFaithfulCompose ι).autMulEquivOfFullyFaithful W
  have hcard : Nat.card (Aut W) = Nat.card (Aut ((compose ι).obj W)) := Nat.card_congr e.toEquiv
  constructor
  · intro h
    have := h.finite_aut
    refine ⟨h.connectedSpace, Finite.of_equiv _ e.symm.toEquiv, ?_⟩
    intro t ⟨a⟩
    rw [Nat.card_congr (fiberEquivCompose ι W t), hcard]
    exact h.hasDegree (t.map ι) ⟨fiberEquivCompose ι W t a⟩
  · intro h
    have := h.finite_aut
    refine ⟨h.connectedSpace, Finite.of_equiv _ e.toEquiv, ?_⟩
    intro t ⟨b⟩
    have hr : Set.range t.hom ⊆ Set.range ι := by
      have hb : t.hom = (b.1 ≫ W.hom) ≫ ι := ((Category.assoc _ _ _).trans b.2).symm
      rw [hb, Scheme.Hom.comp_base, TopCat.coe_comp]
      exact Set.range_comp_subset_range _ _
    obtain ⟨t₀, rfl⟩ := GeometricPoint.exists_map_eq_of_range_subset ι t hr
    rw [← Nat.card_congr (fiberEquivCompose ι W t₀), ← hcard]
    exact h.hasDegree t₀ ⟨(fiberEquivCompose ι W t₀).symm b⟩

end Scheme.CoveringSpace

namespace GeometricPoint.PointedGaloisCoveringSpace

open Scheme.CoveringSpace

/-- Over a connected base, any two pointed Galois covering spaces are dominated by a third. -/
theorem exists_cone_of_connectedSpace {X : Scheme.{u}} [ConnectedSpace X] {s : GeometricPoint X}
    (P₁ P₂ : s.PointedGaloisCoveringSpace) :
    ∃ P₃ : s.PointedGaloisCoveringSpace, Nonempty (P₃ ⟶ P₁) ∧ Nonempty (P₃ ⟶ P₂) := by
  let e := equivPointedGaloisObject s
  obtain ⟨Q, f₁, f₂, -⟩ := IsCofilteredOrEmpty.cone_objs (e.functor.obj P₁) (e.functor.obj P₂)
  exact ⟨e.inverse.obj Q, ⟨e.inverse.map f₁ ≫ (e.unitIso.app P₁).inv⟩,
    ⟨e.inverse.map f₂ ≫ (e.unitIso.app P₂).inv⟩⟩

/-- Pointed Galois covering spaces of `(X, s)` lying over a connected open and closed subscheme
`U` of `X` through `s` are dominated by a third one. -/
theorem exists_cone_of_isOpenImmersion {X U : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
    [IsFinite ι] [ConnectedSpace U] (s₀ : GeometricPoint U)
    (P₁ P₂ : (s₀.map ι).PointedGaloisCoveringSpace)
    (h₁ : Set.range P₁.obj.cover.hom ⊆ Set.range ι)
    (h₂ : Set.range P₂.obj.cover.hom ⊆ Set.range ι) :
    ∃ P₃ : (s₀.map ι).PointedGaloisCoveringSpace, Nonempty (P₃ ⟶ P₁) ∧ Nonempty (P₃ ⟶ P₂) := by
  let R : ∀ (P : (s₀.map ι).PointedGaloisCoveringSpace)
      (_ : Set.range P.obj.cover.hom ⊆ Set.range ι), s₀.PointedGaloisCoveringSpace :=
    fun P h ↦ ⟨PointedCoveringSpace.mk (restrict ι P.obj.cover h) P.obj.point (by
      change P.obj.point ≫ IsOpenImmersion.lift ι P.obj.cover.hom h = s₀.hom
      rw [← cancel_mono ι, Category.assoc, IsOpenImmersion.lift_fac]
      exact PointedCoveringSpace.point_comp_hom P.obj), by
      rw [← isGalois_compose_iff ι, compose_obj_restrict]
      exact P.property⟩
  obtain ⟨Q, ⟨g₁⟩, ⟨g₂⟩⟩ := exists_cone_of_connectedSpace (R P₁ h₁) (R P₂ h₂)
  let P₃ : (s₀.map ι).PointedGaloisCoveringSpace :=
    ⟨PointedCoveringSpace.mk ((compose ι).obj Q.obj.cover) Q.obj.point (by
      change Q.obj.point ≫ Q.obj.cover.hom ≫ ι = s₀.hom ≫ ι
      rw [← Category.assoc, PointedCoveringSpace.point_comp_hom]),
      (isGalois_compose_iff ι _).2 Q.property⟩
  have lift : ∀ (P : (s₀.map ι).PointedGaloisCoveringSpace)
      (h : Set.range P.obj.cover.hom ⊆ Set.range ι), (Q ⟶ R P h) → Nonempty (P₃ ⟶ P) := by
    intro P h g
    refine ⟨ObjectProperty.homMk (PointedCoveringSpace.homMk g.hom.1.left ?_ ?_)⟩
    · change g.hom.1.left ≫ P.obj.cover.hom = Q.obj.cover.hom ≫ ι
      rw [← IsOpenImmersion.lift_fac ι P.obj.cover.hom h]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ι) (MorphismProperty.Over.w g.hom.1))
    · exact PointedCoveringSpace.point_comp_left g.hom
  exact ⟨P₃, lift P₁ h₁ g₁, lift P₂ h₂ g₂⟩

/-- **Two pointed Galois covering spaces are dominated by a third**, in the category of pointed
Galois covering spaces: for `P₁`, `P₂` there is `P₃` with morphisms `P₃ ⟶ P₁` and `P₃ ⟶ P₂`. -/
@[weil "lem_fka1_pointed_galois_category_preorder"]
theorem exists_cone {X : Scheme.{u}} {s : GeometricPoint X}
    (P₁ P₂ : s.PointedGaloisCoveringSpace) :
    ∃ P₃ : s.PointedGaloisCoveringSpace, Nonempty (P₃ ⟶ P₁) ∧ Nonempty (P₃ ⟶ P₂) := by
  have hc₁ : ConnectedSpace P₁.obj.cover.left := P₁.property.connectedSpace
  have hc₂ : ConnectedSpace P₂.obj.cover.left := P₂.property.connectedSpace
  have hclopen : IsClopen (Set.range P₁.obj.cover.hom) :=
    ⟨P₁.obj.cover.hom.isClosedMap.isClosed_range, P₁.obj.cover.hom.isOpenMap.isOpen_range⟩
  obtain ⟨V, hV⟩ : ∃ V : X.Opens, Set.range V.ι = Set.range P₁.obj.cover.hom :=
    ⟨⟨_, hclopen.isOpen⟩, Scheme.Opens.range_ι _⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [hV]; exact hclopen.isClosed)
  have : ConnectedSpace V := by
    have hconn : _root_.IsConnected (Set.range P₁.obj.cover.hom) :=
      @isConnected_range _ _ _ _ hc₁ _ P₁.obj.cover.hom.continuous
    rw [← hV, Scheme.Opens.range_ι] at hconn
    exact Subtype.connectedSpace hconn
  have hs₁ : s.hom = P₁.obj.point ≫ P₁.obj.cover.hom :=
    (PointedCoveringSpace.point_comp_hom _).symm
  have hs₂ : s.hom = P₂.obj.point ≫ P₂.obj.cover.hom :=
    (PointedCoveringSpace.point_comp_hom _).symm
  have h₂ : Set.range P₂.obj.cover.hom ⊆ Set.range V.ι := by
    rw [hV]
    refine (@isPreconnected_range _ _ _ _ hc₂.toPreconnectedSpace _
      P₂.obj.cover.hom.continuous).subset_isClopen hclopen ?_
    obtain ⟨x⟩ : Nonempty s.source := inferInstance
    refine ⟨s.hom x, ⟨P₂.obj.point x, ?_⟩, ⟨P₁.obj.point x, ?_⟩⟩
    · rw [hs₂]; rfl
    · rw [hs₁]; rfl
  have hs : Set.range s.hom ⊆ Set.range V.ι := by
    rw [hs₁, Scheme.Hom.comp_base, TopCat.coe_comp, hV]
    exact Set.range_comp_subset_range _ _
  obtain ⟨s₀, rfl⟩ := GeometricPoint.exists_map_eq_of_range_subset V.ι s hs
  exact exists_cone_of_isOpenImmersion V.ι s₀ P₁ P₂ hV.ge h₂

/-- **Two pointed Galois covering spaces are dominated by a third.** For pointed Galois covering
spaces `(Y₁, α₁)`, `(Y₂, α₂)` of `(X, s)` there are a pointed Galois covering space `(Y₃, α₃)` of
`(X, s)` and mappings of pointed covering spaces `(Y₃, α₃) → (Y₁, α₁)` and
`(Y₃, α₃) → (Y₂, α₂)`. -/
@[weil "lem_fka1_pointed_galois_category_preorder"]
theorem exists_isHom_isHom {X : Scheme.{u}} {s : GeometricPoint X}
    (P₁ P₂ : s.PointedGaloisCoveringSpace) :
    ∃ (P₃ : s.PointedGaloisCoveringSpace) (f₁ : P₃.obj.cover.left ⟶ P₁.obj.cover.left)
      (f₂ : P₃.obj.cover.left ⟶ P₂.obj.cover.left),
      PointedCoveringSpace.IsHom P₃.obj P₁.obj f₁ ∧
        PointedCoveringSpace.IsHom P₃.obj P₂.obj f₂ := by
  obtain ⟨P₃, ⟨g₁⟩, ⟨g₂⟩⟩ := exists_cone P₁ P₂
  exact ⟨P₃, _, _, (homEquivIsHom P₃ P₁ g₁).2, (homEquivIsHom P₃ P₂ g₂).2⟩

end GeometricPoint.PointedGaloisCoveringSpace

end AlgebraicGeometry
