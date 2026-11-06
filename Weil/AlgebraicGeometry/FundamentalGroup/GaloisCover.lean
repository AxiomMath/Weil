module

public import Weil.AlgebraicGeometry.FundamentalGroup.PointedMorphismUnique
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import Weil.Attr
public import Weil.AlgebraicGeometry.FundamentalGroup.CoveringMorphismFiberSurjective
public import Weil.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import Weil.AlgebraicGeometry.FundamentalGroup.CoveringFiberNonemptyConnectedBase
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.ConstantSheaf

/-!
# The Galois group of a Galois covering space acts simply transitively on its fibres

Let `p : Y ⟶ X` be a Galois covering space, `s` a geometric point of `X` and `a ∈ Y(s)` a
geometric point of `Y` over `s`. Then `σ ↦ σ ∘ a` is a bijection `G(Y/X) ≃ Y(s)` from the group
of automorphisms of `Y` over `X` onto the geometric fibre.

It is injective because two automorphisms agreeing on `a` are mappings of pointed covering
spaces out of the connected pointed covering space `(Y, a)` with the same target, hence equal;
and it is surjective because `Y(s)` is nonempty, so it has `#G(Y/X)` elements, a finite number.

## Main definitions

* `AlgebraicGeometry.Scheme.CoveringSpace.IsGalois.autEquivFiber` — the bijection
  `G(Y/X) ≃ Y(s)`, `σ ↦ σ ∘ a`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.IsGalois.bijective_map_fiber` — for a Galois covering
  space `Y` and `a ∈ Y(s)`, the map `G(Y/X) → Y(s)`, `σ ↦ σ ∘ a`, is bijective.

## Implementation notes

No connectedness of the base `X` is assumed, unlike
`AlgebraicGeometry.Scheme.CoveringSpace.IsGalois.bijective_evaluation`, which goes through the
Galois category of covering spaces of a connected scheme.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace Scheme.CoveringSpace

variable {X : Scheme.{u}} {Y : X.CoveringSpace} {s : GeometricPoint X}

namespace IsGalois

/-- Automorphisms of a covering space with connected source agreeing at one geometric point
are equal. -/
theorem aut_eq_of_map_fiber_eq [ConnectedSpace Y.left] (a : (finiteEtaleFiberFunctor s).obj Y)
    {σ τ : Aut Y} (h : (finiteEtaleFiberFunctor s).map σ.hom a =
      (finiteEtaleFiberFunctor s).map τ.hom a) : σ = τ := by
  let P : s.PointedCoveringSpace := ⟨Y, a⟩
  let Q : s.PointedCoveringSpace := ⟨Y, (finiteEtaleFiberFunctor s).map σ.hom a⟩
  have hσ : GeometricPoint.PointedCoveringSpace.IsHom P Q σ.hom.left :=
    ⟨MorphismProperty.Over.w σ.hom, rfl⟩
  have hτ : GeometricPoint.PointedCoveringSpace.IsHom P Q τ.hom.left :=
    ⟨MorphismProperty.Over.w τ.hom, congrArg Subtype.val h.symm⟩
  have : ConnectedSpace P.cover.left := ‹ConnectedSpace Y.left›
  exact Iso.ext (MorphismProperty.Over.Hom.ext (hσ.eq_of_connectedSpace hτ))

/-- **The Galois group acts simply transitively on the fibres.** For a Galois covering space
`Y ⟶ X`, a geometric point `s` of `X` and `a ∈ Y(s)`, the map `G(Y/X) → Y(s)`, `σ ↦ σ ∘ a`, is
bijective. -/
@[weil "lem_fka1_galois_group_acts_transitively_fiber"]
theorem bijective_map_fiber (h : IsGalois Y) (a : (finiteEtaleFiberFunctor s).obj Y) :
    Function.Bijective (fun σ : Aut Y ↦ (finiteEtaleFiberFunctor s).map σ.hom a) := by
  have := h.connectedSpace
  have := h.finite_aut
  have hinj : Function.Injective (fun σ : Aut Y ↦ (finiteEtaleFiberFunctor s).map σ.hom a) :=
    fun _ _ hστ ↦ aut_eq_of_map_fiber_eq a hστ
  have hcard : Nat.card ((finiteEtaleFiberFunctor s).obj Y) = Nat.card (Aut Y) :=
    h.hasDegree s ⟨a⟩
  have : Finite ((finiteEtaleFiberFunctor s).obj Y) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_ne_zero.2 ⟨inferInstance, ‹_›⟩)
  exact hinj.bijective_of_nat_card_le hcard.le

/-- The bijection `G(Y/X) ≃ Y(s)`, `σ ↦ σ ∘ a`, for a Galois covering space `Y` and `a ∈ Y(s)`. -/
def autEquivFiber (h : IsGalois Y) (a : (finiteEtaleFiberFunctor s).obj Y) :
    Aut Y ≃ (finiteEtaleFiberFunctor s).obj Y :=
  Equiv.ofBijective _ (h.bijective_map_fiber a)

@[simp]
lemma autEquivFiber_apply_coe (h : IsGalois Y) (a : (finiteEtaleFiberFunctor s).obj Y)
    (σ : Aut Y) : (h.autEquivFiber a σ).1 = a.1 ≫ σ.hom.left :=
  rfl

end IsGalois

end Scheme.CoveringSpace

end AlgebraicGeometry

end

/-! ### Morphisms from a Galois covering space into a covering space -/

/-!
# Morphisms from a Galois covering space into a covering space

Let `X` be a connected scheme, `s` a geometric point of `X`, `(Z, α)` a pointed Galois covering
space of `(X, s)` and `Y` a covering space of `X` such that every connected component of `Y`
receives an `X`-morphism from `Z`. Then evaluation at the base point,
`Hom_X(Z, Y) → Y(s)`, `f ↦ α ≫ f`, is a bijection.

Injectivity holds because `Z` is connected, so a mapping of pointed covering spaces out of
`(Z, α)` is unique. For surjectivity, let `y ∈ Y(s)` and let `f : Z ⟶ Y` be an `X`-morphism
landing in the connected component of the image point of `y`. The morphism `f` is finite and
étale, so its image is open and closed; being nonempty and contained in a connected component,
it is that component, so it contains the point of `y`. The fibre of `f` over `y` is then a
nonempty finite étale scheme over the spectrum of an algebraically closed field, so it has a
rational point, which gives `z ∈ Z(s)` with `z ≫ f = y`. As `Z` is Galois, `z = α ≫ σ` for an
automorphism `σ` of `Z` over `X`, and `σ ≫ f` is sent to `y`.

## Main results

* `AlgebraicGeometry.GeometricPoint.PointedGaloisCoveringSpace.bijective_fiberFunctor_map` —
  evaluation at the base point `Hom_X(Z, Y) → Y(s)` is bijective.

## Implementation notes

A connected component of `Y` is described by a point `y` of `Y` as `connectedComponent y`, and an
`X`-morphism `Z ⟶ Y_i` into it as an `X`-morphism `Z ⟶ Y` whose image lies in
`connectedComponent y`. For a noetherian base the connected components are open subschemes and
this is the same as an `X`-morphism into the component; in general it does not need the
components to be open.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

namespace PointedGaloisCoveringSpace

variable {X : Scheme.{u}} {s : GeometricPoint X}

/-- **Morphisms from a Galois covering space are determined by the image of the base point.**
Let `X` be connected, `(Z, α)` a pointed Galois covering space of `(X, s)` and `Y` a covering
space of `X` such that every connected component of `Y` receives an `X`-morphism from `Z`. Then
`Hom_X(Z, Y) → Y(s)`, `f ↦ α ≫ f`, is bijective. -/
@[weil "lem_fka1_hom_from_galois_to_cover_bijective"]
theorem bijective_fiberFunctor_map [ConnectedSpace X] (P : s.PointedGaloisCoveringSpace)
    (Y : X.CoveringSpace)
    (h : ∀ y : Y.left, ∃ f : P.obj.cover ⟶ Y, Set.range f.left.base ⊆ connectedComponent y) :
    Function.Bijective (fun f : P.obj.cover ⟶ Y ↦
      (fiberFunctor s).map ((MorphismProperty.Over.forget _ _ X).map f)
        ⟨P.obj.point, P.obj.point_comp_hom⟩) := by
  have hZ : ConnectedSpace P.obj.cover.left := P.isGalois.connectedSpace
  constructor
  · intro f g hfg
    have hfg' : P.obj.point ≫ f.left = P.obj.point ≫ g.left := congrArg Subtype.val hfg
    let Q : s.PointedCoveringSpace :=
      PointedCoveringSpace.mk Y (P.obj.point ≫ f.left) (by simp)
    have hf : PointedCoveringSpace.IsHom P.obj Q f.left :=
      ⟨Scheme.CoveringSpace.left_comp_hom f, rfl⟩
    have hg : PointedCoveringSpace.IsHom P.obj Q g.left :=
      ⟨Scheme.CoveringSpace.left_comp_hom g, hfg'.symm⟩
    have := hf.eq_of_connectedSpace hg
    exact (Scheme.CoveringSpace.homEquiv _ _).injective (Subtype.ext this)
  · rintro ⟨(y : s.source ⟶ Y.left), (hy : y ≫ Y.hom = s.hom)⟩
    obtain ⟨pt⟩ : Nonempty s.source := inferInstance
    obtain ⟨f, hf⟩ := h (y.base pt)
    obtain ⟨z₀⟩ : Nonempty P.obj.cover.left := hZ.toNonempty
    have : IsFinite f.left := isFinite_hom_left f
    have : Etale f.left := etale_hom_left f
    have hclopen : IsClopen (Set.range f.left.base) :=
      ⟨f.left.isClosedMap.isClosed_range, f.left.isOpenMap.isOpen_range⟩
    have hmem : y.base pt ∈ Set.range f.left.base := by
      have h₀ : f.left.base z₀ ∈ connectedComponent (y.base pt) := hf ⟨z₀, rfl⟩
      have h₁ : y.base pt ∈ connectedComponent (f.left.base z₀) := by
        rw [← connectedComponent_eq h₀]
        exact mem_connectedComponent
      exact hclopen.connectedComponent_subset ⟨z₀, rfl⟩ h₁
    obtain ⟨z₁, hz₁⟩ := hmem
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f.left) (g := y) z₁ pt hz₁
    let V : (s.source).CoveringSpace := Scheme.CoveringSpace.mk (pullback.snd f.left y)
    have : Nonempty V.left := ⟨w⟩
    let t : GeometricPoint s.source := ⟨s.residueField, 𝟙 _⟩
    obtain ⟨⟨β, hβ⟩⟩ := nonempty_finiteEtaleFiber_of_nonempty_left t V
    let γ : s.source ⟶ pullback f.left y := β
    have hβ' : γ ≫ pullback.snd f.left y = 𝟙 _ := hβ
    let z : s.source ⟶ P.obj.cover.left := γ ≫ pullback.fst f.left y
    have hzf : z ≫ f.left = y := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hβ', Category.id_comp]
    have hz : z ≫ P.obj.cover.hom = s.hom := by
      rw [← Scheme.CoveringSpace.left_comp_hom f, ← Category.assoc, hzf, hy]
    obtain ⟨σ, hσ⟩ := (Scheme.CoveringSpace.IsGalois.bijective_evaluation P.isGalois
      (s := s) ⟨P.obj.point, P.obj.point_comp_hom⟩).2 ⟨z, hz⟩
    have hσ' : P.obj.point ≫ σ.hom.left = z := congrArg Subtype.val hσ
    refine ⟨σ.hom ≫ f, Subtype.ext ?_⟩
    change P.obj.point ≫ σ.hom.left ≫ f.left = y
    rw [← Category.assoc, hσ', hzf]

end PointedGaloisCoveringSpace

end GeometricPoint

end AlgebraicGeometry

end

/-! ### Existence of pointed Galois covering spaces -/

/-!
# Existence of pointed Galois covering spaces

Let `X` be a locally noetherian scheme and `s : Spec Ω ⟶ X` a geometric point. The connected
component `X₀` of `X` containing the image of `s` is open (a locally noetherian space is locally
connected) and closed, so the inclusion `j : X₀ ⟶ X` of the open subscheme is an open and closed
immersion, hence finite and étale: `X₀` is a covering space of `X`. It is nonempty and connected,
and since `j` is a monomorphism its automorphism group is trivial and each geometric fibre has at
most one element, so `X₀` has degree `1 = #G(X₀/X)` and is Galois. The geometric point `s`
factors through `j`, which makes `X₀` a pointed Galois covering space of `(X, s)`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.connectedComponentCover s` — the covering space of `X` given
  by the connected component of `X` containing the image of `s`.
* `AlgebraicGeometry.GeometricPoint.connectedComponentPointedGaloisCoveringSpace s` — that
  covering space, pointed by the factorisation of `s` through it.

## Main results

* `AlgebraicGeometry.GeometricPoint.isGalois_connectedComponentCover` — the connected
  component containing the image of `s` is a Galois covering space.
* `AlgebraicGeometry.GeometricPoint.nonempty_pointedGaloisCoveringSpace` — every geometric
  point of a locally noetherian scheme has a pointed Galois covering space.

## Implementation notes

The source states the result for noetherian separated schemes; only the openness of connected
components is used, which holds for every locally noetherian scheme, so the result is stated in
that generality.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (s : GeometricPoint X)

/-- The connected component of `X` containing the image of the geometric point `s`, as an open
subset of `X`. -/
def connectedComponentOpens : X.Opens :=
  haveI := IsLocallyNoetherianSpace.locallyConnectedSpace X
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X)
  ⟨connectedComponent (s.hom default), isOpen_connectedComponent⟩

@[simp]
lemma coe_connectedComponentOpens :
    (s.connectedComponentOpens : Set X) = connectedComponent (s.hom default) :=
  rfl

instance isClosedImmersion_connectedComponentOpens_ι :
    IsClosedImmersion s.connectedComponentOpens.ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, coe_connectedComponentOpens]
    exact isClosed_connectedComponent)

instance : IsFinite s.connectedComponentOpens.ι := inferInstance

/-- The connected component of `X` containing the image of `s`, as a covering space of `X`. -/
abbrev connectedComponentCover : X.CoveringSpace :=
  Scheme.CoveringSpace.mk s.connectedComponentOpens.ι

lemma range_hom_subset_connectedComponentOpens :
    Set.range s.hom ⊆ Set.range s.connectedComponentOpens.ι := by
  rw [Scheme.Opens.range_ι, coe_connectedComponentOpens]
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y default]
  exact mem_connectedComponent

/-- The factorisation of `s` through the connected component containing its image. -/
def connectedComponentPoint : s.source ⟶ s.connectedComponentCover.left :=
  (IsOpenImmersion.lift s.connectedComponentOpens.ι s.hom
    s.range_hom_subset_connectedComponentOpens : s.source ⟶ s.connectedComponentOpens.toScheme)

@[reassoc (attr := simp)]
lemma connectedComponentPoint_comp :
    s.connectedComponentPoint ≫ s.connectedComponentCover.hom = s.hom :=
  IsOpenImmersion.lift_fac s.connectedComponentOpens.ι _ _

instance connectedSpace_connectedComponentCover :
    ConnectedSpace s.connectedComponentCover.left :=
  isConnected_iff_connectedSpace.1 isConnected_connectedComponent

instance subsingleton_hom_connectedComponentCover (Y : X.CoveringSpace) :
    Subsingleton (Y ⟶ s.connectedComponentCover) :=
  ⟨fun f g ↦ by
    apply (Scheme.CoveringSpace.homEquiv _ _).injective
    apply Subtype.ext
    exact (cancel_mono s.connectedComponentOpens.ι).1
      ((Scheme.CoveringSpace.left_comp_hom f).trans (Scheme.CoveringSpace.left_comp_hom g).symm)⟩

instance subsingleton_aut_connectedComponentCover :
    Subsingleton (Aut s.connectedComponentCover) :=
  ⟨fun σ _ ↦ Iso.ext (Subsingleton.elim (α := s.connectedComponentCover ⟶ _)
    (show s.connectedComponentCover ≅ s.connectedComponentCover from σ).hom _)⟩

lemma subsingleton_fiber_connectedComponentCover (t : GeometricPoint X) :
    Subsingleton ((finiteEtaleFiberFunctor t).obj s.connectedComponentCover) :=
  ⟨fun a b ↦ by
    apply Subtype.ext
    exact (cancel_mono s.connectedComponentOpens.ι).1 (a.2.trans b.2.symm)⟩

/-- The connected component containing the image of a geometric point is a Galois covering
space. -/
theorem isGalois_connectedComponentCover : s.connectedComponentCover.IsGalois where
  connectedSpace := inferInstance
  finite_aut := Finite.of_subsingleton
  hasDegree t ht := by
    have := s.subsingleton_fiber_connectedComponentCover t
    have h₁ : Nat.card (Aut s.connectedComponentCover) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
    rw [h₁]
    exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ht⟩

/-- The pointed Galois covering space of `(X, s)` given by the connected component of `X`
containing the image of `s`, pointed by the factorisation of `s` through it. -/
def connectedComponentPointedGaloisCoveringSpace : s.PointedGaloisCoveringSpace :=
  ⟨PointedCoveringSpace.mk s.connectedComponentCover s.connectedComponentPoint
    s.connectedComponentPoint_comp, s.isGalois_connectedComponentCover⟩

/-- **Existence of pointed Galois covering spaces.** Every geometric point `s` of a locally
noetherian scheme `X` has a pointed Galois covering space. -/
@[weil "lem_fka1_pointed_galois_exists"]
theorem nonempty_pointedGaloisCoveringSpace : Nonempty s.PointedGaloisCoveringSpace :=
  ⟨s.connectedComponentPointedGaloisCoveringSpace⟩

end GeometricPoint

end AlgebraicGeometry

end

/-! ### A Galois covering space dominating every connected component -/

/-!
# A Galois covering space dominating every connected component

Let `X` be a connected scheme, `s` a geometric point of `X` and `p : Y ⟶ X` a covering space.
Then there is a pointed Galois covering space `(Z, α)` of `(X, s)` with an `X`-morphism from `Z`
to every connected component of `Y`.

The finite étale `X`-schemes form a Galois category with fibre functor the geometric fibre at
`s`, and its pointed Galois objects form a cofiltered category. Every connected component `C` of
`Y` contains a point of the geometric fibre `Y(s)`: a Galois object `A` mapping onto a point of
`C` is connected, so its image lies in `C`, and its fibre at `s` is nonempty. For each of the
finitely many points `a ∈ Y(s)` choose a pointed Galois object `(A_a, α_a)` with a morphism
`A_a ⟶ Y` sending `α_a` to `a`; a pointed Galois object `(Z, α)` dominating all of them has, for
each component `C`, a morphism `Z ⟶ Y` whose (connected) image meets `C`, hence lies in `C`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.exists_fiber_mem_connectedComponent` — every connected
  component of a covering space of a connected scheme meets every geometric fibre.
* `AlgebraicGeometry.Scheme.CoveringSpace.exists_pointedGaloisCoveringSpace_range_subset` — a
  pointed Galois covering space with an `X`-morphism to `Y` landing in any given connected
  component.
* `AlgebraicGeometry.Scheme.CoveringSpace.exists_pointedGaloisCoveringSpace_hom_connectedComponent`
  — for `X` noetherian, the same with an `X`-morphism into the open subscheme on each connected
  component.

## Implementation notes

An `X`-morphism from a connected `Z` to a connected component `C` of `Y` is recorded as an
`X`-morphism `Z ⟶ Y` with image in `C`; when `C` is open this is the same as an `X`-morphism to
the open subscheme on `C`, which is the second form, stated for `X` noetherian as in the source.
The first form needs no hypothesis on `X` beyond connectedness.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

public section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

namespace Scheme.CoveringSpace

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- Every connected component of a covering space `Y` of a connected scheme `X` meets every
geometric fibre of `Y`: for each `y : Y` and each geometric point `s` of `X` there is a point
`a ∈ Y(s)` whose image lies in the connected component of `y`. -/
theorem exists_fiber_mem_connectedComponent (s : GeometricPoint X) (Y : X.CoveringSpace)
    (y : Y.left) :
    ∃ a : (finiteEtaleFiberFunctor s).obj Y, ∀ p, a.1 p ∈ connectedComponent y := by
  let t : GeometricPoint X := (Y.left.algClosedPoint y).map (𝟙 Y.left ≫ Y.hom)
  obtain ⟨A, f, b, hA, hb⟩ := exists_hom_from_galois_of_fiber
    (finiteEtaleFiberFintypeFunctor X t) Y (fiberPointOfComp y (𝟙 Y.left))
  have : ConnectedSpace A.left := connectedSpace_left_of_isConnected A inferInstance
  have hy : y ∈ Set.range f.left := by
    have h1 : b.1 ≫ f.left = (Y.left.algClosedPoint y).hom ≫ 𝟙 Y.left :=
      congrArg Subtype.val hb
    obtain ⟨p⟩ : Nonempty (t.source : Scheme.{u}) := inferInstance
    refine ⟨b.1 p, ?_⟩
    rw [Category.comp_id] at h1
    have := congrArg (fun g : t.source ⟶ Y.left => g p) h1
    simp only [Scheme.Hom.comp_apply, Scheme.algClosedPoint_hom] at this
    exact this.trans (Scheme.algClosedPointHom_apply _ _ p)
  obtain ⟨⟨α, hα⟩⟩ := nonempty_fiberFunctor_obj A s
  have hconn : _root_.IsPreconnected (Set.range f.left) :=
    isPreconnected_range f.left.continuous
  refine ⟨⟨α ≫ f.left,
    (Category.assoc _ _ _).trans ((congrArg (α ≫ ·) (left_comp_hom f)).trans hα)⟩, fun p => ?_⟩
  have hsub := hconn.subset_connectedComponent hy
  exact hsub ⟨α p, rfl⟩

/-- **A Galois covering space dominating every connected component.** Let `X` be a connected
scheme, `s` a geometric point of `X` and `Y` a covering space of `X`. Then there is a pointed
Galois covering space `(Z, α)` of `(X, s)` with, for every connected component `C` of `Y`, an
`X`-morphism `Z ⟶ Y` with image in `C`. -/
@[weil "lem_fka1_galois_cover_dominating_components"]
theorem exists_pointedGaloisCoveringSpace_range_subset (s : GeometricPoint X)
    (Y : X.CoveringSpace) :
    ∃ P : s.PointedGaloisCoveringSpace, ∀ y : Y.left,
      ∃ f : P.obj.cover ⟶ Y, Set.range f.left ⊆ connectedComponent y := by
  classical
  let F := finiteEtaleFiberFintypeFunctor X s
  have hA : ∀ a : F.obj Y, ∃ (A : PointedGaloisObject F) (f : A.obj ⟶ Y), F.map f A.pt = a :=
    fun a => by
      obtain ⟨A, f, b, hA, hb⟩ := exists_hom_from_galois_of_fiber F Y a
      exact ⟨⟨A, b, hA⟩, f, hb⟩
  choose A f hf using hA
  have : Nonempty (PointedGaloisObject F) := by
    obtain ⟨A₀, -, b₀, h₀, -⟩ := exists_hom_from_galois_of_fiber F (mk (𝟙 X))
      (⟨s.hom, Category.comp_id _⟩ : finiteEtaleFiber s (mk (𝟙 X)))
    exact ⟨⟨A₀, b₀, h₀⟩⟩
  have : IsCofiltered (PointedGaloisObject F) := {}
  have : Fintype (F.obj Y) := Fintype.ofFinite _
  obtain ⟨Z, hZ⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image A)
  refine ⟨(GeometricPoint.PointedGaloisCoveringSpace.ofPointedGaloisObject s).obj Z,
    fun y => ?_⟩
  obtain ⟨a, ha⟩ : ∃ a : F.obj Y, ∀ p, a.1 p ∈ connectedComponent y :=
    exists_fiber_mem_connectedComponent s Y y
  obtain ⟨g⟩ := hZ (Finset.mem_image_of_mem A (Finset.mem_univ a))
  refine ⟨g.val ≫ f a, ?_⟩
  have : ConnectedSpace Z.obj.left :=
    connectedSpace_left_of_isConnected Z.obj inferInstance
  have key : F.map (g.val ≫ f a) Z.pt = a := by
    rw [F.map_comp, FintypeCat.comp_apply, g.comp, hf]
  have key' : Z.pt.1 ≫ (g.val ≫ f a).left = a.1 := congrArg Subtype.val key
  obtain ⟨p⟩ : Nonempty (s.source : Scheme.{u}) := inferInstance
  have hmem : a.1 p ∈ Set.range (g.val ≫ f a).left :=
    ⟨Z.pt.1 p, by rw [← key', Scheme.Hom.comp_apply]⟩
  rw [connectedComponent_eq (ha p)]
  exact (isPreconnected_range (g.val ≫ f a).left.continuous).subset_connectedComponent hmem

/-- **A Galois covering space dominating every connected component, open form.** Let `X` be a
connected noetherian scheme, `s` a geometric point of `X` and `Y` a covering space of `X`. The
connected components of `Y` are open; there is a pointed Galois covering space `(Z, α)` of
`(X, s)` with an `X`-morphism from `Z` to the open subscheme on every connected component of
`Y`. -/
@[weil "lem_fka1_galois_cover_dominating_components"]
theorem exists_pointedGaloisCoveringSpace_hom_connectedComponent [IsNoetherian X]
    (s : GeometricPoint X) (Y : X.CoveringSpace) :
    ∃ P : s.PointedGaloisCoveringSpace, ∀ y : Y.left,
      ∃ f : P.obj.cover.left ⟶
          (⟨connectedComponent y, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent y⟩ :
            Y.left.Opens),
        f ≫ Scheme.Opens.ι _ ≫ Y.hom = P.obj.cover.hom := by
  obtain ⟨P, hP⟩ := exists_pointedGaloisCoveringSpace_range_subset s Y
  refine ⟨P, fun y => ?_⟩
  obtain ⟨f, hf⟩ := hP y
  let U : Y.left.Opens :=
    ⟨connectedComponent y, TopologicalSpace.NoetherianSpace.isOpen_connectedComponent y⟩
  refine ⟨IsOpenImmersion.lift U.ι f.left (by rwa [Scheme.Opens.range_ι]), ?_⟩
  rw [IsOpenImmersion.lift_fac_assoc, left_comp_hom]

end Scheme.CoveringSpace

end AlgebraicGeometry

end
