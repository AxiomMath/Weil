module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# Lifting geometric points along étale morphisms

Let `φ : U ⟶ X` be an étale morphism of schemes and `x : Spec k ⟶ X` a morphism from the
spectrum of a separably closed field `k`, with image point `x₀ ∈ X`. If `x₀` lies in the image
of `φ`, then `x` lifts along `φ`: there is `u : Spec k ⟶ U` with `u ≫ φ = x`. More precisely,
every point `y ∈ U` with `φ y = x₀` is the image of such a lift. In particular, for a geometric
point `s` of `X` lying over a point of the image of `φ`, the pair `(U, u)` is an étale
neighbourhood of `s`.

The proof: the residue field extension `κ(x₀) → κ(y)` is finite separable since `φ` is étale,
so the embedding `κ(x₀) → k` extends to `κ(y) → k` because `k` is separably closed; composing
`Spec k ⟶ Spec κ(y) ⟶ U` gives the lift.

## Main results

* `AlgebraicGeometry.exists_lift_of_etale_of_isSepClosed`: a morphism from the spectrum of a
  separably closed field whose image point lies in the image of an étale morphism lifts along it.
* `AlgebraicGeometry.GeometricPoint.exists_lift_of_etale_of_liesOver`: the same for geometric
  points; `AlgebraicGeometry.GeometricPoint.etaleNeighborhoodOfMemRange` is the resulting étale
  neighbourhood `(U, u)`.

## Implementation notes

The factorization through a prescribed point of the fibre is Mathlib's
`AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`, which is reused. The statement
for separably closed fields is the source's; geometric points
(`AlgebraicGeometry.GeometricPoint`) take values in algebraically closed fields, which are
separably closed.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Lifting along étale morphisms.** Let `φ : U ⟶ X` be étale and `x : Spec k ⟶ X` with `k`
separably closed. If the image point of `x` lies in the image of `φ`, then `x` factors through
`φ`. -/
@[weil "lem_fk104_geometric_point_lifts_to_etale"]
theorem exists_lift_of_etale_of_isSepClosed {U X : Scheme.{u}} (φ : U ⟶ X) [Etale φ]
    {k : Type u} [Field k] [IsSepClosed k] (x : Spec (.of k) ⟶ X)
    (hx : x default ∈ Set.range φ) :
    ∃ u : Spec (.of k) ⟶ U, u ≫ φ = x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨u, hu, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed φ x y hy
  exact ⟨u, hu⟩

namespace GeometricPoint

/-- **Geometric points lift to étale neighbourhoods.** If `φ : U ⟶ X` is étale and the geometric
point `s` of `X` lies over a point `x₀` in the image of `φ`, then `s` lifts to `u : Spec k ⟶ U`
with `u ≫ φ = s`, so that `(U, u)` is an étale neighbourhood of `s`
(`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood`, built by
`AlgebraicGeometry.GeometricPoint.etaleNeighborhoodOfMemRange`). -/
@[weil "lem_fk104_geometric_point_lifts_to_etale"]
theorem exists_lift_of_etale_of_liesOver {U X : Scheme.{u}} (φ : U ⟶ X) [Etale φ]
    (s : GeometricPoint X) {x₀ : X} (hs : s.LiesOver x₀) (hx₀ : x₀ ∈ Set.range φ) :
    ∃ u : s.source ⟶ U, u ≫ φ = s.hom :=
  exists_lift_of_etale_of_isSepClosed φ s.hom (hs ▸ hx₀)

/-- The étale neighbourhood `(U, u)` of a geometric point `s` lying over a point in the image of
an étale morphism `φ : U ⟶ X`, with `u` a lift of `s` chosen by
`AlgebraicGeometry.GeometricPoint.exists_lift_of_etale_of_liesOver`. -/
noncomputable def etaleNeighborhoodOfMemRange {U X : Scheme.{u}} (φ : U ⟶ X) [Etale φ]
    (s : GeometricPoint X) {x₀ : X} (hs : s.LiesOver x₀) (hx₀ : x₀ ∈ Set.range φ) :
    EtaleNeighborhood s where
  scheme := U
  toBase := φ
  point := (exists_lift_of_etale_of_liesOver φ s hs hx₀).choose
  point_comp := (exists_lift_of_etale_of_liesOver φ s hs hx₀).choose_spec

@[simp]
lemma etaleNeighborhoodOfMemRange_scheme {U X : Scheme.{u}} (φ : U ⟶ X) [Etale φ]
    (s : GeometricPoint X) {x₀ : X} (hs : s.LiesOver x₀) (hx₀ : x₀ ∈ Set.range φ) :
    (etaleNeighborhoodOfMemRange φ s hs hx₀).scheme = U :=
  rfl

@[simp]
lemma etaleNeighborhoodOfMemRange_toBase {U X : Scheme.{u}} (φ : U ⟶ X) [Etale φ]
    (s : GeometricPoint X) {x₀ : X} (hs : s.LiesOver x₀) (hx₀ : x₀ ∈ Set.range φ) :
    (etaleNeighborhoodOfMemRange φ s hs hx₀).toBase = φ :=
  rfl

end GeometricPoint

end AlgebraicGeometry
