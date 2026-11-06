module

public import WeilFrontier.Defs.AlgebraicGeometry.FundamentalGroup.FundamentalGroup
public import Mathlib.CategoryTheory.Galois.Action
public import Weil.Attr

/-!
# The action of `π₁(X, s)` on geometric fibres

Let `Y → X` be a covering space, `g ∈ π₁(X, s)` and `y, y' ∈ Y(s)`. Then `g` *moves `y` to `y'`*,
written `g · y = y'`, if there are a pointed Galois covering space `(Z, α)` of `(X, s)` and an
`X`-morphism `f : Z ⟶ Y` with `f ∘ α = y` and `f ∘ g_{(Z, α)}⁻¹ ∘ α = y'`; such a pair
`((Z, α), f)` is a *witness* for `g · y = y'`.

Over a connected base, `π₁(X, s)` is identified with the automorphism group of the geometric
fibre functor `F` at `s` by `AlgebraicGeometry.GeometricPoint.fundamentalGroupMulEquivAut`, and
`g` moves `y` to `y'` exactly when the automorphism of `F` attached to `g` sends `y` to `y'`: the
relation is the graph of Mathlib's action of `Aut F` on the fibres
(`CategoryTheory.PreGaloisCategory.functorToAction`).

## Main definitions

* `AlgebraicGeometry.GeometricPoint.MovesWitness g y y'` — the witnesses for `g · y = y'`.
* `AlgebraicGeometry.GeometricPoint.Moves g y y'` — `g` moves `y` to `y'`.

## Main results

* `AlgebraicGeometry.GeometricPoint.moves_iff_hom_app_eq` — over a connected base, `g` moves `y`
  to `y'` if and only if the automorphism of the fibre functor attached to `g` sends `y` to `y'`.
* `AlgebraicGeometry.GeometricPoint.moves_iff_smul_eq` — the same statement for the action of
  `Aut F` on the fibres through `functorToAction`.

## Implementation notes

The composite `f ∘ g_{(Z, α)}⁻¹ ∘ α` is the image of the base point `α ∈ Z(s)` under the map of
fibres induced by the `X`-morphism `g_{(Z, α)}⁻¹ ≫ f : Z ⟶ Y`. Geometric points take values in
algebraically closed fields, following the Stacks project; the source allows separably closed
fields.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} {s : GeometricPoint X}

/-- **Witnesses for `g · y = y'`.** A witness that `g ∈ π₁(X, s)` moves `y ∈ Y(s)` to `y' ∈ Y(s)`
is a pointed Galois covering space `(Z, α)` of `(X, s)` with an `X`-morphism `f : Z ⟶ Y` such
that `f ∘ α = y` and `f ∘ g_{(Z, α)}⁻¹ ∘ α = y'`. -/
@[weil "def_fka1_fiber_pi1_action"]
structure MovesWitness (g : s.fundamentalGroup) {Y : X.CoveringSpace}
    (y y' : (finiteEtaleFiberFunctor s).obj Y) where
  /-- The pointed Galois covering space `(Z, α)`. -/
  galois : s.PointedGaloisCoveringSpace
  /-- The `X`-morphism `f : Z ⟶ Y`. -/
  hom : galois.obj.cover ⟶ Y
  /-- `f ∘ α = y`. -/
  map_point : (finiteEtaleFiberFunctor s).map hom galois.obj.2 = y
  /-- `f ∘ g_{(Z, α)}⁻¹ ∘ α = y'`. -/
  map_inv_point :
    (finiteEtaleFiberFunctor s).map ((g.1 galois)⁻¹.hom ≫ hom) galois.obj.2 = y'

/-- **The action of `π₁(X, s)` on `Y(s)`.** `g ∈ π₁(X, s)` *moves* `y ∈ Y(s)` to `y' ∈ Y(s)`,
written `g · y = y'`, if there is a witness for it: a pointed Galois covering space `(Z, α)` of
`(X, s)` and an `X`-morphism `f : Z ⟶ Y` with `f ∘ α = y` and `f ∘ g_{(Z, α)}⁻¹ ∘ α = y'`. -/
@[weil "def_fka1_fiber_pi1_action"]
def Moves (g : s.fundamentalGroup) {Y : X.CoveringSpace}
    (y y' : (finiteEtaleFiberFunctor s).obj Y) : Prop :=
  Nonempty (MovesWitness g y y')

theorem moves_iff_nonempty_movesWitness (g : s.fundamentalGroup) {Y : X.CoveringSpace}
    (y y' : (finiteEtaleFiberFunctor s).obj Y) :
    Moves g y y' ↔ Nonempty (MovesWitness g y y') :=
  Iff.rfl

theorem MovesWitness.moves {g : s.fundamentalGroup} {Y : X.CoveringSpace}
    {y y' : (finiteEtaleFiberFunctor s).obj Y} (w : MovesWitness g y y') : Moves g y y' :=
  ⟨w⟩

section Connected

variable [ConnectedSpace X]

/-- The automorphism of the fibre functor attached to `g ∈ π₁(X, s)` sends the image `f ∘ α` of
the base point of a pointed Galois covering space `(Z, α)` under an `X`-morphism `f : Z ⟶ Y` to
`f ∘ g_{(Z, α)}⁻¹ ∘ α`. -/
private theorem fundamentalGroupMulEquivAut_hom_app_map_point (g : s.fundamentalGroup)
    (P : s.PointedGaloisCoveringSpace) {Y : X.CoveringSpace} (f : P.obj.cover ⟶ Y) :
    (fundamentalGroupMulEquivAut s g).hom.app Y
        ((finiteEtaleFiberFintypeFunctor X s).map f P.obj.2) =
      (finiteEtaleFiberFunctor s).map ((g.1 P)⁻¹.hom ≫ f) P.obj.2 := by
  have h := ConcreteCategory.congr_hom ((fundamentalGroupMulEquivAut s g).hom.naturality f)
    P.obj.2
  exact h.trans (congrArg (fun z ↦ (finiteEtaleFiberFintypeFunctor X s).map f z)
    (fundamentalGroupMulEquivAut_hom_app_point g P))

/-- **`g · y` is the action of the fibre-functor automorphism.** Over a connected base, `g`
moves `y` to `y'` if and only if the automorphism of the geometric fibre functor attached to `g`
by `fundamentalGroupMulEquivAut` sends `y` to `y'`. -/
@[weil "def_fka1_fiber_pi1_action"]
theorem moves_iff_hom_app_eq (g : s.fundamentalGroup) {Y : X.CoveringSpace}
    (y y' : (finiteEtaleFiberFunctor s).obj Y) :
    Moves g y y' ↔
      (fundamentalGroupMulEquivAut s g).hom.app Y
        (show (finiteEtaleFiberFintypeFunctor X s).obj Y from y) = y' := by
  constructor
  · rintro ⟨⟨P, f, rfl, rfl⟩⟩
    exact fundamentalGroupMulEquivAut_hom_app_map_point g P f
  · intro h
    obtain ⟨A, f, a, hA, hfa⟩ :=
      exists_hom_from_galois_of_fiber (finiteEtaleFiberFintypeFunctor X s) Y y
    let P : s.PointedGaloisCoveringSpace :=
      ⟨⟨A, a⟩, (Scheme.CoveringSpace.isGalois_iff_isGalois A).2 hA⟩
    refine ⟨⟨P, f, hfa, ?_⟩⟩
    rw [← h, ← fundamentalGroupMulEquivAut_hom_app_map_point]
    exact congrArg _ hfa

/-- Over a connected base, `g` moves `y` to `y'` if and only if `y'` is the image of `y` under
the action of the automorphism of the fibre functor attached to `g` on the fibre `Y(s)`, as an
object of `Action FintypeCat (Aut F)` through `functorToAction`. -/
theorem moves_iff_smul_eq (g : s.fundamentalGroup) {Y : X.CoveringSpace}
    (y y' : (finiteEtaleFiberFunctor s).obj Y) :
    Moves g y y' ↔
      (fundamentalGroupMulEquivAut s g) •
        (show ((functorToAction (finiteEtaleFiberFintypeFunctor X s)).obj Y).V from y) = y' :=
  moves_iff_hom_app_eq g y y'

/-- Over a connected base, `g` moves `y` to the image of `y` under the automorphism of the fibre
functor attached to `g`. -/
theorem moves_hom_app (g : s.fundamentalGroup) {Y : X.CoveringSpace}
    (y : (finiteEtaleFiberFunctor s).obj Y) :
    Moves g y ((fundamentalGroupMulEquivAut s g).hom.app Y
      (show (finiteEtaleFiberFintypeFunctor X s).obj Y from y)) :=
  (moves_iff_hom_app_eq g y _).2 rfl

end Connected

end GeometricPoint

end AlgebraicGeometry

end
