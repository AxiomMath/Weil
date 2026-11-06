module

public import WeilFrontier.Defs.AlgebraicGeometry.Sites.EtalePoint
public import Weil.Attr

/-!
# The point test presheaf is a sheaf

Let `x` be a geometric point of a scheme `X` and `S` a set. The presheaf `𝒮_{x,S}` on the
small étale site of `X` sends an étale `X`-scheme `U` to the set `Map(U(x), S)` of maps from the
set `U(x)` of lifts of `x` to `U` into `S`, with restriction along `h : V ⟶ U` given by
`c ↦ c ∘ h_*`. It is a sheaf for the étale topology.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.pointTestPresheaf`: the presheaf `U ↦ (U(x) → S)`.
* `AlgebraicGeometry.GeometricPoint.pointTestPresheafIso`: its identification with the
  underlying presheaf of the skyscraper sheaf `AlgebraicGeometry.GeometricPoint.pointTestSheaf`
  (for `S` in the universe of `X`).
* `AlgebraicGeometry.GeometricPoint.pointTestPresheafIsoSkyscraper`: for `S` in an arbitrary
  universe, its identification with Mathlib's skyscraper presheaf with value `ULift S`.

## Main results

* `AlgebraicGeometry.GeometricPoint.isSheaf_pointTestPresheaf`: `𝒮_{x,S}` is an étale sheaf.

## Implementation notes

The source checks the disjoint-union and surjective-descent conditions by hand. Here the
presheaf is identified with the underlying presheaf of Mathlib's skyscraper sheaf at the point
of the small étale site defined by `x`, whose fibre functor is `U ↦ U(x)`; being a sheaf is
invariant under isomorphism of presheaves. The site is Mathlib's `smallEtaleTopology X`.
The set `S` lives in an arbitrary universe `w`, independent of the universe `u` of `X`, and
`𝒮_{x,S}` takes values in `Type (max u w)`; the skyscraper presheaf is then taken with value
`ULift.{u} S`, products indexed by the `u`-small sets `U(x)` existing in `Type (max u w)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w u

namespace AlgebraicGeometry.GeometricPoint

variable {X : Scheme.{u}} (x : GeometricPoint X)

/-- The point test presheaf `𝒮_{x,S}` : `U ↦ Map(U(x), S)`, with restriction along `h : V ⟶ U`
given by `c ↦ c ∘ h_*`. -/
def pointTestPresheaf (S : Type w) : X.Etaleᵒᵖ ⥤ Type (max u w) where
  obj U := x.Lifts U.unop → S
  map h := TypeCat.ofHom fun c => c ∘ Lifts.map (x := x) h.unop
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma pointTestPresheaf_obj (S : Type w) (U : X.Etaleᵒᵖ) :
    (x.pointTestPresheaf S).obj U = (x.Lifts U.unop → S) :=
  rfl

@[simp]
lemma pointTestPresheaf_map_apply (S : Type w) {U V : X.Etaleᵒᵖ} (h : U ⟶ V)
    (c : (x.pointTestPresheaf S).obj U) :
    (x.pointTestPresheaf S).map h c = c ∘ Lifts.map (x := x) h.unop :=
  rfl

/-- The point test presheaf is the underlying presheaf of the skyscraper sheaf
`x.pointTestSheaf S`. -/
def pointTestPresheafIso (S : Type u) :
    (x.pointTestSheaf S).obj ≅ x.pointTestPresheaf S :=
  NatIso.ofComponents (fun U => (x.pointTestSheafObjEquiv S U.unop).toIso) fun h => by
    ext c
    exact x.pointTestSheafObjEquiv_map S h.unop c

/-- For a set `S` in an arbitrary universe, the sections over `U` of the skyscraper presheaf
with value `S` (lifted to the universe `max u w`) at `x.sitePoint` are the maps `U(x) → S`. -/
def skyscraperPresheafObjEquiv (S : Type w) (U : X.Etale) :
    (x.sitePoint.skyscraperPresheaf (ULift.{u} S)).obj (op U) ≃ (x.Lifts U → S) :=
  (Types.productIso.{u, max u w} fun _ : x.sitePoint.fiber.obj U => ULift.{u} S).toEquiv.trans
    ((x.liftsEquivFiber U).symm.arrowCongr Equiv.ulift)

lemma skyscraperPresheafObjEquiv_apply (S : Type w) (U : X.Etale)
    (c : (x.sitePoint.skyscraperPresheaf (ULift.{u} S)).obj (op U)) (v : x.Lifts U) :
    x.skyscraperPresheafObjEquiv S U c v =
      (Pi.π (fun _ : x.sitePoint.fiber.obj U => ULift.{u} S) (x.liftsEquivFiber U v) c).down := by
  rfl

/-- For a set `S` in an arbitrary universe, the point test presheaf is the skyscraper
presheaf with value `S` (lifted to the universe `max u w`) at the point `x.sitePoint`. -/
def pointTestPresheafIsoSkyscraper (S : Type w) :
    x.sitePoint.skyscraperPresheaf (ULift.{u} S) ≅ x.pointTestPresheaf S :=
  NatIso.ofComponents (fun U => (x.skyscraperPresheafObjEquiv S U.unop).toIso) fun h => by
    ext c
    funext v
    change x.skyscraperPresheafObjEquiv S _ _ v = x.skyscraperPresheafObjEquiv S _ c _
    rw [skyscraperPresheafObjEquiv_apply, skyscraperPresheafObjEquiv_apply, liftsEquivFiber_map]
    have key : (x.sitePoint.skyscraperPresheaf (ULift.{u} S)).map h ≫
        Pi.π (fun _ : x.sitePoint.fiber.obj _ => ULift.{u} S) (x.liftsEquivFiber _ v) =
        Pi.π (fun _ : x.sitePoint.fiber.obj _ => ULift.{u} S)
          (x.sitePoint.fiber.map h.unop (x.liftsEquivFiber _ v)) := by
      simp only [GrothendieckTopology.Point.skyscraperPresheafFunctor_obj_map]
      exact (Pi.map'_comp_π _ _ _).trans (Category.comp_id _)
    exact congrArg ULift.down (ConcreteCategory.congr_hom key c)

/-- **The point test presheaf is a sheaf.** For every geometric point `x` of `X` and every set
`S`, the presheaf `𝒮_{x,S} : U ↦ Map(U(x), S)` is a sheaf on the small étale site of `X`. -/
@[weil "lem_fk104_point_test_sheaf_is_sheaf"]
theorem isSheaf_pointTestPresheaf (S : Type w) :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (x.pointTestPresheaf S) :=
  (Presheaf.isSheaf_of_iso_iff (x.pointTestPresheafIsoSkyscraper S)).mp
    (x.sitePoint.isSheaf_skyscraperPresheaf _)

end AlgebraicGeometry.GeometricPoint

end
