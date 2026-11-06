module

public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.PointedCoveringMorphism
public import Weil.Attr

/-!
# Galois covering spaces

A covering space `p : Y ⟶ X` (a finite étale morphism) is *Galois* if `Y` is nonempty and
connected, the group `G(Y/X) = Aut Y` of automorphisms of `Y` over `X` is finite, and `Y` has
degree `#G(Y/X)`: every nonempty geometric fibre `Y(s)` has exactly `#G(Y/X)` elements.

Over a connected base `X` the finite étale `X`-schemes form a Galois category, and a covering
space is Galois in this sense exactly when it is a Galois object of that category in the sense
of `CategoryTheory.PreGaloisCategory.IsGalois`: a connected object on whose fibres its
automorphism group acts transitively. Indeed, for a connected `Y` the action of `Aut Y` on a
nonempty fibre `Y(s)` is free, so it is transitive if and only if `#Aut Y = #Y(s)`.

A *pointed Galois covering space* of `(X, s)` is a pointed covering space `(Y, α)` with `Y`
Galois; with the morphisms of pointed covering spaces they form a full subcategory of the
category of pointed covering spaces. Over a connected base this category is equivalent to
Mathlib's category `CategoryTheory.PreGaloisCategory.PointedGaloisObject` of the geometric fibre
functor at `s`.

## Main definitions

* `AlgebraicGeometry.Scheme.CoveringSpace.IsGalois Y` — the covering space `Y` is Galois.
* `AlgebraicGeometry.GeometricPoint.PointedGaloisCoveringSpace s` — the category of pointed
  Galois covering spaces of `(X, s)`.

## Main results

* `AlgebraicGeometry.Scheme.CoveringSpace.isGalois_iff_isGalois` — over a connected base, a
  covering space is Galois if and only if it is a Galois object of the Galois category of
  covering spaces.
* `AlgebraicGeometry.Scheme.CoveringSpace.IsGalois.natCard_fiber_eq` — every geometric fibre of a
  Galois covering space of a connected scheme has `#G(Y/X)` elements.
* `AlgebraicGeometry.GeometricPoint.PointedGaloisCoveringSpace.equivPointedGaloisObject` — over
  a connected base, pointed Galois covering spaces are Mathlib's pointed Galois objects of the
  geometric fibre functor.

## Implementation notes

Nonemptiness of `Y` is part of `ConnectedSpace`, so it is not a separate field. The group
`G(Y/X)` is the automorphism group `Aut Y` of `Y` in the category `Cov(X)` of covering spaces,
which is a full subcategory of the schemes over `X`, so it is the group of automorphisms of `Y`
over `X`. Geometric points take values in algebraically closed fields, following the Stacks
project; the source allows separably closed fields, which does not change the size of a
geometric fibre.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

namespace Scheme.CoveringSpace

variable {X : Scheme.{u}}

/-- **Galois covering spaces.** A covering space `Y` of `X` is *Galois* if `Y` is nonempty and
connected, its group `G(Y/X) = Aut Y` of automorphisms over `X` is finite, and `Y` has degree
`#G(Y/X)`. -/
@[weil "def_fka1_galois_covering"]
structure IsGalois (Y : X.CoveringSpace) : Prop where
  /-- The source of a Galois covering space is nonempty and connected. -/
  connectedSpace : ConnectedSpace Y.left
  /-- The automorphism group of a Galois covering space is finite. -/
  finite_aut : Finite (Aut Y)
  /-- A Galois covering space has degree the order of its automorphism group. -/
  hasDegree : HasDegree Y (Nat.card (Aut Y))

namespace IsGalois

variable {Y : X.CoveringSpace}

/-- The source of a Galois covering space is nonempty. -/
theorem nonempty (h : IsGalois Y) : Nonempty Y.left :=
  h.connectedSpace.toNonempty

/-- A Galois covering space is a connected object of the category of covering spaces. -/
theorem isConnected (h : IsGalois Y) : PreGaloisCategory.IsConnected Y :=
  @isConnected_of_connectedSpace_left _ Y h.connectedSpace

end IsGalois

section Connected

variable [ConnectedSpace X]

/-- **Galois covering spaces are the Galois objects.** Over a connected base, a covering space is
Galois if and only if it is a Galois object of the Galois category `Cov(X)`. -/
@[weil "def_fka1_galois_covering"]
theorem isGalois_iff_isGalois (Y : X.CoveringSpace) :
    IsGalois Y ↔ PreGaloisCategory.IsGalois Y := by
  constructor
  · intro h
    have := h.isConnected
    have := h.finite_aut
    obtain ⟨y⟩ := h.nonempty
    let s : GeometricPoint X := X.algClosedPoint (Y.hom y)
    let F := finiteEtaleFiberFintypeFunctor X s
    obtain ⟨a⟩ := nonempty_fiber_of_isConnected F Y
    have hcard : Nat.card (Aut Y) = Nat.card (F.obj Y) :=
      (h.hasDegree s ⟨a⟩).symm
    have hbij : Function.Bijective (fun f : Aut Y ↦ F.map f.hom a) :=
      (Function.Injective.bijective_of_nat_card_le
        (evaluation_aut_injective_of_isConnected F Y a) hcard.ge)
    rw [isGalois_iff_pretransitive F Y]
    refine ⟨fun x z ↦ ?_⟩
    obtain ⟨σ, hσ⟩ := hbij.2 x
    obtain ⟨τ, hτ⟩ := hbij.2 z
    refine ⟨τ * σ⁻¹, ?_⟩
    change (τ * σ⁻¹) • x = z
    rw [← hσ, ← hτ]
    change (τ * σ⁻¹) • (σ • a) = τ • a
    rw [smul_smul, inv_mul_cancel_right]
  · intro h
    refine ⟨connectedSpace_left_of_isConnected Y inferInstance, inferInstance, ?_⟩
    intro s ⟨a⟩
    let F := finiteEtaleFiberFintypeFunctor X s
    exact (Nat.card_eq_of_bijective _ (evaluation_aut_bijective_of_isGalois F Y a)).symm

/-- Every geometric fibre of a Galois covering space of a connected scheme has `#G(Y/X)`
elements. -/
theorem IsGalois.natCard_fiber_eq {Y : X.CoveringSpace} (h : IsGalois Y) (s : GeometricPoint X) :
    Nat.card ((finiteEtaleFiberFunctor s).obj Y) = Nat.card (Aut Y) :=
  have := h.isConnected
  h.hasDegree s (nonempty_fiber_of_isConnected (finiteEtaleFiberFintypeFunctor X s) Y)

/-- Over a connected base, a Galois covering space `Y` is simply transitive under `G(Y/X)` on each
geometric fibre: evaluation at a geometric point `a ∈ Y(s)` is a bijection `G(Y/X) ≃ Y(s)`. -/
theorem IsGalois.bijective_evaluation {Y : X.CoveringSpace} (h : IsGalois Y)
    {s : GeometricPoint X} (a : (finiteEtaleFiberFunctor s).obj Y) :
    Function.Bijective (fun σ : Aut Y ↦ (finiteEtaleFiberFunctor s).map σ.hom a) :=
  have := (isGalois_iff_isGalois Y).1 h
  evaluation_aut_bijective_of_isGalois (finiteEtaleFiberFintypeFunctor X s) Y a

end Connected

end Scheme.CoveringSpace

namespace GeometricPoint

variable {X : Scheme.{u}} (s : GeometricPoint X)

/-- **Pointed Galois covering spaces.** A pointed Galois covering space of `(X, s)` is a pointed
covering space `(Y, α)` with `Y` Galois. They form the full subcategory of the category of pointed
covering spaces on these objects, so a morphism is a morphism of pointed covering spaces. -/
@[weil "def_fka1_galois_covering"]
abbrev PointedGaloisCoveringSpace : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun P : s.PointedCoveringSpace ↦ P.cover.IsGalois

namespace PointedGaloisCoveringSpace

variable {s}

/-- The underlying pointed covering space of a pointed Galois covering space. -/
abbrev toPointedCoveringSpace (P : s.PointedGaloisCoveringSpace) : s.PointedCoveringSpace :=
  P.obj

/-- The underlying covering space of a pointed Galois covering space is Galois. -/
theorem isGalois (P : s.PointedGaloisCoveringSpace) : P.obj.cover.IsGalois :=
  P.property

/-- The morphisms `P ⟶ Q` of pointed Galois covering spaces are exactly the mappings of pointed
covering spaces `P → Q` between the underlying schemes. -/
def homEquivIsHom (P Q : s.PointedGaloisCoveringSpace) :
    (P ⟶ Q) ≃
      {f : P.obj.cover.left ⟶ Q.obj.cover.left // PointedCoveringSpace.IsHom P.obj Q.obj f} :=
  (ObjectProperty.fullyFaithfulι _).homEquiv.trans (PointedCoveringSpace.homEquivIsHom P.obj Q.obj)

@[simp]
lemma homEquivIsHom_apply_coe {P Q : s.PointedGaloisCoveringSpace} (f : P ⟶ Q) :
    (homEquivIsHom P Q f : P.obj.cover.left ⟶ Q.obj.cover.left) = f.hom.1.left :=
  rfl

section Connected

variable [ConnectedSpace X]

variable (s) in
/-- Pointed Galois covering spaces as pointed Galois objects of the Galois category `Cov(X)` with
the geometric fibre functor at `s`. -/
def toPointedGaloisObject :
    s.PointedGaloisCoveringSpace ⥤ PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s) where
  obj P :=
    { obj := P.obj.cover
      pt := P.obj.2
      isGalois := (Scheme.CoveringSpace.isGalois_iff_isGalois _).1 P.property }
  map f := { val := f.hom.1, comp := f.hom.2 }

variable (s) in
/-- Pointed Galois objects of the Galois category `Cov(X)` with the geometric fibre functor at `s`
as pointed Galois covering spaces. -/
def ofPointedGaloisObject :
    PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s) ⥤ s.PointedGaloisCoveringSpace where
  obj A := ⟨⟨A.obj, A.pt⟩, (Scheme.CoveringSpace.isGalois_iff_isGalois _).2 A.isGalois⟩
  map f := ObjectProperty.homMk ⟨f.val, f.comp⟩

variable (s) in
/-- **Pointed Galois covering spaces are pointed Galois objects.** Over a connected base, the
category of pointed Galois covering spaces of `(X, s)` is equivalent to Mathlib's category of
pointed Galois objects of `Cov(X)` for the geometric fibre functor at `s`. -/
def equivPointedGaloisObject :
    s.PointedGaloisCoveringSpace ≌ PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s) where
  functor := toPointedGaloisObject s
  inverse := ofPointedGaloisObject s
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

end Connected

end PointedGaloisCoveringSpace

end GeometricPoint

end AlgebraicGeometry

end
