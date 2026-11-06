module

public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.FundamentalGroup
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.GaloisCover
public import Weil.Attr

/-!
# The natural mapping `π₁(X, s) → G(Y/X)`

Let `s` be a geometric point of a scheme `X` and `(Y, α)` a pointed Galois covering space of
`(X, s)`. An element `σ` of the fundamental group `π₁(X, s)` is a compatible family
`σ = (σ_{(Y, α)})` of automorphisms of the pointed Galois covering spaces, and the natural mapping
`p_{(Y, α)} : π₁(X, s) → G(Y/X)` sends `σ` to its component `σ_{(Y, α)}`. It is a group
homomorphism, the restriction to `π₁(X, s)` of the projection of `P(X, s) = ∏ G(Y/X)` to the
factor of `(Y, α)`, and it is continuous for the discrete topology on `G(Y/X)`.

Over a connected base, under the identification of `π₁(X, s)` with Mathlib's group `AutGalois` of
compatible families over the pointed Galois objects, `p_{(Y, α)}` is Mathlib's projection
`CategoryTheory.PreGaloisCategory.AutGalois.π`; under the identification of `π₁(X, s)` with the
automorphism group of the geometric fibre functor, `p_{(Y, α)}(σ)` is the unique automorphism of
the Galois object `Y` whose inverse moves `α` as the automorphism attached to `σ` does.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.fundamentalGroupProjection P` — the natural mapping
  `p_{(Y, α)} : π₁(X, s) →* G(Y/X)` for a pointed Galois covering space `P = (Y, α)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.isRestrictionAlong_fundamentalGroupProjection` — for a
  mapping `f : (Z, γ) → (Y, α)` of pointed Galois covering spaces, `p_{(Y, α)}(σ)` is the
  restriction of `p_{(Z, γ)}(σ)` along `f`.
* `AlgebraicGeometry.GeometricPoint.isOpen_preimage_fundamentalGroupProjection` — `p_{(Y, α)}` is
  continuous for the discrete topology on `G(Y/X)`.
* `AlgebraicGeometry.GeometricPoint.fundamentalGroupProjection_eq_π` — over a connected base,
  `p_{(Y, α)}` is Mathlib's `AutGalois.π`.
* `AlgebraicGeometry.GeometricPoint.fundamentalGroupMulEquivAut_hom_app_point_eq` — over a
  connected base, the automorphism of the fibre functor attached to `σ` moves `α` by
  `p_{(Y, α)}(σ)⁻¹`, and `p_{(Y, α)}(σ)` is determined by this.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

namespace GeometricPoint

variable {X : Scheme.{u}} {s : GeometricPoint X}

/-- **The natural mapping `p_{(Y, α)} : π₁(X, s) → G(Y/X)`.** For a pointed Galois covering space
`P = (Y, α)` of `(X, s)`, the group homomorphism sending `σ ∈ π₁(X, s)` to its component
`σ_{(Y, α)}`. -/
@[weil "def_fka1_fundamental_group_projection"]
def fundamentalGroupProjection (P : s.PointedGaloisCoveringSpace) :
    s.fundamentalGroup →* Aut P.obj.cover :=
  (GaloisAutomorphismProduct.proj P).comp s.fundamentalGroup.subtype

@[simp]
theorem fundamentalGroupProjection_apply (P : s.PointedGaloisCoveringSpace)
    (σ : s.fundamentalGroup) : fundamentalGroupProjection P σ = σ.1 P :=
  rfl

/-- For a mapping `f : (Z, γ) → (Y, α)` of pointed Galois covering spaces, `p_{(Y, α)}(σ)` is a
restriction of `p_{(Z, γ)}(σ)` along `f`. -/
theorem isRestrictionAlong_fundamentalGroupProjection {P Q : s.PointedGaloisCoveringSpace}
    (f : P ⟶ Q) (σ : s.fundamentalGroup) :
    Aut.IsRestrictionAlong f.hom.1 (fundamentalGroupProjection P σ)
      (fundamentalGroupProjection Q σ) :=
  σ.2 f

/-- For a mapping `f : (Z, γ) → (Y, α)` of pointed Galois covering spaces,
`p_{(Y, α)}(σ) ∘ f = f ∘ p_{(Z, γ)}(σ)` as morphisms of schemes. -/
theorem comp_fundamentalGroupProjection_hom_left {P Q : s.PointedGaloisCoveringSpace}
    (f : P ⟶ Q) (σ : s.fundamentalGroup) :
    f.hom.1.left ≫ (fundamentalGroupProjection Q σ).hom.left =
      (fundamentalGroupProjection P σ).hom.left ≫ f.hom.1.left :=
  (s.mem_fundamentalGroup_iff_isHom σ.1).1 σ.2 P Q f.hom.1.left
    (PointedCoveringSpace.isHom_left f.hom)

/-- The natural mapping `p_{(Y, α)}` is continuous for the discrete topology on `G(Y/X)`: the
preimage of every subset of `G(Y/X)` is open in `π₁(X, s)`. -/
theorem isOpen_preimage_fundamentalGroupProjection (P : s.PointedGaloisCoveringSpace)
    (S : Set (Aut P.obj.cover)) : IsOpen (fundamentalGroupProjection P ⁻¹' S) :=
  (GaloisAutomorphismProduct.isOpen_preimage_proj P S).preimage continuous_subtype_val

/-- The kernel of `p_{(Y, α)}` is an open subgroup of `π₁(X, s)`. -/
theorem isOpen_ker_fundamentalGroupProjection (P : s.PointedGaloisCoveringSpace) :
    IsOpen ((fundamentalGroupProjection P).ker : Set s.fundamentalGroup) :=
  isOpen_preimage_fundamentalGroupProjection P {1}

section Connected

variable [ConnectedSpace X]

/-- Over a connected base, the natural mapping `p_{(Y, α)}` is Mathlib's projection
`AutGalois.π` to the pointed Galois object `(Y, α)` of `Cov(X)`, through the identification of
`π₁(X, s)` with `AutGalois`. -/
theorem fundamentalGroupProjection_eq_π (P : s.PointedGaloisCoveringSpace) :
    fundamentalGroupProjection P =
      (AutGalois.π (finiteEtaleFiberFintypeFunctor X s)
          ((PointedGaloisCoveringSpace.toPointedGaloisObject s).obj P)).comp
        (fundamentalGroupMulEquivAutGalois s).toMonoidHom :=
  rfl

/-- Over a connected base, Mathlib's projection `AutGalois.π` to a pointed Galois object `A` of
`Cov(X)` is the natural mapping of the corresponding pointed Galois covering space. -/
theorem π_eq_fundamentalGroupProjection
    (A : PointedGaloisObject (finiteEtaleFiberFintypeFunctor X s)) :
    AutGalois.π (finiteEtaleFiberFintypeFunctor X s) A =
      (fundamentalGroupProjection ((PointedGaloisCoveringSpace.ofPointedGaloisObject s).obj A)).comp
        (fundamentalGroupMulEquivAutGalois s).symm.toMonoidHom :=
  rfl

/-- Over a connected base, the automorphism of the fibre functor attached to `σ ∈ π₁(X, s)` moves
the base point `α` of `(Y, α)` by `p_{(Y, α)}(σ)⁻¹`. -/
theorem fundamentalGroupMulEquivAut_hom_app_point_eq (σ : s.fundamentalGroup)
    (P : s.PointedGaloisCoveringSpace) :
    (fundamentalGroupMulEquivAut s σ).hom.app P.obj.cover P.obj.2 =
      (finiteEtaleFiberFintypeFunctor X s).map (fundamentalGroupProjection P σ)⁻¹.hom P.obj.2 :=
  fundamentalGroupMulEquivAut_hom_app_point σ P

/-- Over a connected base, `p_{(Y, α)}(σ)` is the unique automorphism `g` of the Galois covering
space `Y` such that `g⁻¹` moves `α` as the automorphism of the fibre functor attached to `σ`
does. -/
theorem fundamentalGroupProjection_eq_iff (σ : s.fundamentalGroup)
    (P : s.PointedGaloisCoveringSpace) (g : Aut P.obj.cover) :
    fundamentalGroupProjection P σ = g ↔
      (finiteEtaleFiberFintypeFunctor X s).map g⁻¹.hom P.obj.2 =
        (fundamentalGroupMulEquivAut s σ).hom.app P.obj.cover P.obj.2 := by
  have : IsGalois P.obj.cover := (Scheme.CoveringSpace.isGalois_iff_isGalois _).1 P.property
  rw [fundamentalGroupMulEquivAut_hom_app_point_eq]
  constructor
  · rintro rfl
    rfl
  · intro h
    have := evaluation_aut_injective_of_isConnected (finiteEtaleFiberFintypeFunctor X s)
      P.obj.cover P.obj.2 h
    exact inv_injective this.symm

end Connected

end GeometricPoint

end AlgebraicGeometry

end
