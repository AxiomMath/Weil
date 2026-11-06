module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import Weil.Attr

/-!
# The point test sheaf of a geometric point

Let `x : Spec k ⟶ X` be a geometric point of a scheme `X` and `S` a set. For an étale
`X`-scheme `U`, let `U(x)` be the set of `X`-morphisms `Spec k ⟶ U`, i.e. the lifts of `x`
to `U`; a morphism `h : V ⟶ U` of étale `X`-schemes induces `h_* : V(x) → U(x)`, `v ↦ v ≫ h`.
The point test sheaf `𝒮_{x,S}` is the presheaf `U ↦ Map(U(x), S)` on the small étale site of
`X`, with restriction `c ↦ c ∘ h_*`. It is the skyscraper sheaf with value `S` at the point of
the small étale site defined by `x`, whose fibre functor is `U ↦ U(x)`; in particular it is a
sheaf, and it is right adjoint to the stalk functor at `x`.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.Lifts`: the set `U(x)` of lifts of `x` to an étale
  `X`-scheme `U`.
* `AlgebraicGeometry.GeometricPoint.Lifts.map`: the map `h_* : V(x) → U(x)`.
* `AlgebraicGeometry.GeometricPoint.sitePoint`: the point of the small étale site of `X`
  defined by `x`.
* `AlgebraicGeometry.GeometricPoint.pointTestSheaf`: the sheaf `𝒮_{x,S}`.
* `AlgebraicGeometry.GeometricPoint.pointTestSheafObjEquiv`: the identification
  `𝒮_{x,S}(U) ≃ (U(x) → S)`.

## Main results

* `AlgebraicGeometry.GeometricPoint.pointTestSheafObjEquiv_map`: under this identification,
  restriction along `h : V ⟶ U` is `c ↦ c ∘ h_*`.

## Implementation notes

The sheaf is Mathlib's skyscraper sheaf `(pointSmallEtale x.hom).skyscraperSheafFunctor.obj S`
on `smallEtaleTopology X`. Its sections over `U` are the categorical product of copies of `S`
indexed by `U(x)`, which is identified with the function type `U(x) → S` by
`CategoryTheory.Limits.Types.productIso`. Geometric points take values in algebraically closed
fields, following the Stacks project (Tag 03PO).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

/- The point test sheaf lives
on Mathlib's `smallEtaleTopology X` (site of all étale `X`-schemes), where Mathlib's
`pointSmallEtale` and skyscraper sheaves exist; no site point of StacksFrontier's `SmallEtale`
exists yet. -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.GeometricPoint

variable {X : Scheme.{u}} (x : GeometricPoint X)

/-- The set `U(x)` of lifts of the geometric point `x` to an étale `X`-scheme `U`: the
`X`-morphisms `Spec k ⟶ U`. -/
@[weil "def_fk104_point_test_sheaf"]
def Lifts (U : X.Etale) : Type u :=
  {u : Spec (.of x.residueField) ⟶ U.left // u ≫ U.hom = x.hom}

variable {x}

/-- The map `h_* : V(x) → U(x)`, `v ↦ v ≫ h`, induced by a morphism `h : V ⟶ U`. -/
@[weil "def_fk104_point_test_sheaf"]
def Lifts.map {U V : X.Etale} (h : V ⟶ U) (v : x.Lifts V) : x.Lifts U :=
  ⟨v.1 ≫ h.left, by rw [Category.assoc, MorphismProperty.Over.w h, v.2]⟩

@[simp]
lemma Lifts.map_coe {U V : X.Etale} (h : V ⟶ U) (v : x.Lifts V) :
    (Lifts.map h v).1 = v.1 ≫ h.left :=
  rfl

variable (x)

/-- The point of the small étale site of `X` defined by the geometric point `x`. -/
abbrev sitePoint : (Scheme.smallEtaleTopology X).Point :=
  Scheme.pointSmallEtale x.hom

/-- The fibre of `x.sitePoint` at `U` is the set `U(x)` of lifts of `x` to `U`. -/
def liftsEquivFiber (U : X.Etale) : x.Lifts U ≃ x.sitePoint.fiber.obj U where
  toFun v := Over.homMk v.1 v.2
  invFun f := ⟨f.left, Over.w f⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma liftsEquivFiber_map {U V : X.Etale} (h : V ⟶ U) (v : x.Lifts V) :
    x.liftsEquivFiber U (Lifts.map h v) = x.sitePoint.fiber.map h (x.liftsEquivFiber V v) :=
  rfl

/-- **The point test sheaf** `𝒮_{x,S}` of a geometric point `x` and a set `S`: the sheaf
`U ↦ Map(U(x), S)` on the small étale site, i.e. the skyscraper sheaf with value `S` at the
point defined by `x`. -/
@[weil "def_fk104_point_test_sheaf"]
abbrev pointTestSheaf (S : Type u) : Sheaf (Scheme.smallEtaleTopology X) (Type u) :=
  x.sitePoint.skyscraperSheafFunctor.obj S

/-- The sections of `𝒮_{x,S}` over `U` are the maps `U(x) → S`. -/
@[weil "def_fk104_point_test_sheaf"]
def pointTestSheafObjEquiv (S : Type u) (U : X.Etale) :
    (x.pointTestSheaf S).obj.obj (op U) ≃ (x.Lifts U → S) :=
  (Types.productIso.{u, u} fun _ : x.sitePoint.fiber.obj U => S).toEquiv.trans
    ((x.liftsEquivFiber U).arrowCongr (Equiv.refl S)).symm

@[simp]
lemma pointTestSheafObjEquiv_apply (S : Type u) (U : X.Etale)
    (c : (x.pointTestSheaf S).obj.obj (op U)) (v : x.Lifts U) :
    x.pointTestSheafObjEquiv S U c v =
      Pi.π (fun _ : x.sitePoint.fiber.obj U => S) (x.liftsEquivFiber U v) c := by
  rfl

/-- **Restriction in the point test sheaf.** Restriction of a section along `h : V ⟶ U` is
`c ↦ c ∘ h_*`. -/
@[weil "def_fk104_point_test_sheaf"]
lemma pointTestSheafObjEquiv_map (S : Type u) {U V : X.Etale} (h : V ⟶ U)
    (c : (x.pointTestSheaf S).obj.obj (op U)) :
    x.pointTestSheafObjEquiv S V ((x.pointTestSheaf S).obj.map h.op c) =
      x.pointTestSheafObjEquiv S U c ∘ Lifts.map h := by
  funext v
  simp only [pointTestSheafObjEquiv_apply, Function.comp_apply, liftsEquivFiber_map]
  have key : (x.pointTestSheaf S).obj.map h.op ≫
      Pi.π (fun _ : x.sitePoint.fiber.obj V => S) (x.liftsEquivFiber V v) =
      Pi.π (fun _ : x.sitePoint.fiber.obj U => S)
        (x.sitePoint.fiber.map h (x.liftsEquivFiber V v)) := by
    change (x.sitePoint.skyscraperPresheafFunctor.obj S).map h.op ≫ _ = _
    simp only [GrothendieckTopology.Point.skyscraperPresheafFunctor_obj_map]
    exact (Pi.map'_comp_π _ _ _).trans (Category.comp_id _)
  exact ConcreteCategory.congr_hom key c

end AlgebraicGeometry.GeometricPoint

end
