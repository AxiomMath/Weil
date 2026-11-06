module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.AlgebraicGeometry.Sites.StalkUnchangedAlgebraicClosure

/-!
# Separably closed versus algebraically closed geometric points

Freitag–Kiehl define a geometric point of a scheme `S` as a morphism `Spec k ⟶ S` from the
spectrum of a *separably* closed field; Mathlib's points of the small étale site,
`AlgebraicGeometry.Scheme.pointSmallEtale`, are defined for such morphisms. StacksFrontier's
`AlgebraicGeometry.GeometricPoint`, the convention of this library, asks for an
*algebraically* closed field. This file shows that the difference is invisible to stalks:

* every separably closed point `y : Spec k ⟶ S` factors through the algebraically closed
  geometric point `AlgebraicGeometry.GeometricPoint.ofIsSepClosed y`, whose field is an
  algebraic closure of `k` and which lies over the same point of `S`;
* the two points of the small étale site are isomorphic, so the stalks agree, naturally in the
  sheaf, on Mathlib's site and on the bounded site of [Stacks, Tag 021B];
* hence a property of stalks invariant under isomorphism holds at every separably closed
  point if and only if it holds at every algebraically closed geometric point.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.ofIsSepClosed`: the algebraically closed geometric point
  through which a separably closed point factors.
* `AlgebraicGeometry.GeometricPoint.pointSmallEtaleOfIsSepClosedIso`: the isomorphism of points
  of Mathlib's small étale site.
* `AlgebraicGeometry.GeometricPoint.sheafFiberOfIsSepClosedIso`: the stalk at `y` is the stalk
  at `ofIsSepClosed y`, naturally in the sheaf.
* `AlgebraicGeometry.GeometricPoint.sheafFiberSheafEquivOfIsSepClosedIso`: the same, with the
  stalk at `ofIsSepClosed y` taken on the bounded small étale site.

## Main results

* `AlgebraicGeometry.GeometricPoint.forall_isSepClosed_iff_forall`: a stalk property invariant
  under isomorphism holds at all separably closed points iff at all geometric points.
* `AlgebraicGeometry.GeometricPoint.forall_isSepClosed_iff_forall_smallEtale`: the same with the
  geometric-point stalks read on the bounded small étale site.

## Implementation notes

The isomorphism of points is `AlgebraicGeometry.Scheme.isIso_pointSmallEtaleHomOfFac` of
`Weil.AlgebraicGeometry.Sites.StalkUnchangedAlgebraicClosure` (FK I.3, the stalk is unchanged
under passage
to an algebraic closure). Quantification over separably closed fields is over fields in the
universe `u` of the scheme, as for `AlgebraicGeometry.Scheme.pointSmallEtale`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u' u

namespace AlgebraicGeometry.GeometricPoint

variable {S : Scheme.{u}} {k : Type u} [Field k]

/-- The morphism `Spec k̄ ⟶ Spec k` induced by an algebraic closure `k̄` of `k`. -/
abbrev algebraicClosureι (k : Type u) [Field k] :
    Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- **A separably closed point factors through an algebraically closed geometric point.** For
`y : Spec k ⟶ S` with `k` separably closed, the geometric point `Spec k̄ ⟶ Spec k ⟶ S`, where
`k̄` is an algebraic closure of `k`. -/
def ofIsSepClosed (y : Spec (.of k) ⟶ S) : GeometricPoint S where
  residueField := AlgebraicClosure k
  hom := algebraicClosureι k ≫ y

@[simp]
lemma ofIsSepClosed_residueField (y : Spec (.of k) ⟶ S) :
    (ofIsSepClosed y).residueField = AlgebraicClosure k :=
  rfl

lemma ofIsSepClosed_hom (y : Spec (.of k) ⟶ S) :
    (ofIsSepClosed y).hom = algebraicClosureι k ≫ y :=
  rfl

/-- The geometric point `ofIsSepClosed y` lies over the image of `y`. -/
lemma liesOver_ofIsSepClosed_iff (y : Spec (.of k) ⟶ S) (x : S) :
    (ofIsSepClosed y).LiesOver x ↔ y default = x := by
  change (algebraicClosureι k ≫ y) default = x ↔ y default = x
  rw [Scheme.Hom.comp_apply, Subsingleton.elim (algebraicClosureι k default) default]

variable [IsSepClosed k]

/-- **The two points of Mathlib's small étale site agree.** The point of `ofIsSepClosed y` is
isomorphic to the point of `y`: every lift of `Spec k̄ ⟶ S` to an étale `S`-scheme descends
uniquely to a lift of `y`. -/
def pointSmallEtaleOfIsSepClosedIso (y : Spec (.of k) ⟶ S) :
    Scheme.pointSmallEtale (ofIsSepClosed y).hom ≅ Scheme.pointSmallEtale y :=
  haveI := Scheme.isIso_pointSmallEtaleHomOfFac (ofIsSepClosed y).hom y
    (algebraicClosureι k) rfl
  asIso (Scheme.pointSmallEtaleHomOfFac (ofIsSepClosed y).hom y (algebraicClosureι k) rfl)

section Stalks

variable (A : Type u') [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

/-- **The stalk at a separably closed point is the stalk at an algebraically closed geometric
point.** For `y : Spec k ⟶ S` with `k` separably closed, the stalk of a sheaf on Mathlib's small
étale site at `y` is its stalk at the geometric point `ofIsSepClosed y`, naturally in the sheaf;
on germs, the germ at `(U, u)` goes to the germ at `(U, u ∘ (Spec k̄ ⟶ Spec k))`. -/
def sheafFiberOfIsSepClosedIso (y : Spec (.of k) ⟶ S) :
    (Scheme.pointSmallEtale y).sheafFiber (A := A) ≅ (ofIsSepClosed y).toPoint.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ A)
    (Scheme.presheafFiberIsoAlgebraicClosure (A := A) y)

/-- The per-sheaf form of `AlgebraicGeometry.GeometricPoint.sheafFiberOfIsSepClosedIso`. -/
def sheafFiber_obj_ofIsSepClosed_iso (y : Spec (.of k) ⟶ S)
    (F : Sheaf S.smallEtaleTopology A) :
    (Scheme.pointSmallEtale y).sheafFiber.obj F ≅ (ofIsSepClosed y).toPoint.sheafFiber.obj F :=
  (sheafFiberOfIsSepClosedIso A y).app F

variable [HasLimitsOfSize.{u, u} A] (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- **The stalk at a separably closed point, read on the bounded small étale site.** For a sheaf
`F` on the bounded small étale site of [Stacks, Tag 021B], the stalk of its transport to
Mathlib's site at a separably closed point `y` is the stalk of `F` at the point
`AlgebraicGeometry.geometricPointSitePoint` of the algebraically closed geometric point
`ofIsSepClosed y`. -/
def sheafFiberSheafEquivOfIsSepClosedIso (y : Spec (.of k) ⟶ S) :
    (SmallEtale.sheafEquiv B S hS A).functor ⋙ (Scheme.pointSmallEtale y).sheafFiber ≅
      (geometricPointSitePoint B S hS (ofIsSepClosed y)).sheafFiber :=
  Functor.isoWhiskerLeft _ (sheafFiberOfIsSepClosedIso A y) ≪≫
    SmallEtale.sheafEquivFunctorCompSheafFiberIso B S hS A (ofIsSepClosed y)

end Stalks

section Quantifiers

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

/-- **Separably closed and algebraically closed geometric points test the same stalk
properties.** A property of objects of `A` invariant under isomorphism holds for the stalks of a
sheaf on Mathlib's small étale site at every separably closed point `Spec k ⟶ S` if and only if
it holds at every geometric point (with algebraically closed field) of
`AlgebraicGeometry.GeometricPoint`. -/
theorem forall_isSepClosed_iff_forall (P : A → Prop) (hP : ∀ {X Y : A}, (X ≅ Y) → P X → P Y)
    (F : Sheaf S.smallEtaleTopology A) :
    (∀ (k : Type u) [Field k] [IsSepClosed k] (y : Spec (.of k) ⟶ S),
        P ((Scheme.pointSmallEtale y).sheafFiber.obj F)) ↔
      ∀ s : GeometricPoint S, P (s.toPoint.sheafFiber.obj F) :=
  ⟨fun h s ↦ h s.residueField s.hom, fun h _ _ _ y ↦
    hP (sheafFiber_obj_ofIsSepClosed_iso A y F).symm (h (ofIsSepClosed y))⟩

variable [HasLimitsOfSize.{u, u} A] (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- **The same, with geometric-point stalks read on the bounded small étale site.** A property
of objects invariant under isomorphism holds for the stalks of a sheaf `F` on Mathlib's small
étale site at every separably closed point if and only if it holds for the stalks of its
restriction to the bounded small étale site of [Stacks, Tag 021B] at every geometric point. -/
theorem forall_isSepClosed_iff_forall_smallEtale (P : A → Prop)
    (hP : ∀ {X Y : A}, (X ≅ Y) → P X → P Y) (F : Sheaf S.smallEtaleTopology A) :
    (∀ (k : Type u) [Field k] [IsSepClosed k] (y : Spec (.of k) ⟶ S),
        P ((Scheme.pointSmallEtale y).sheafFiber.obj F)) ↔
      ∀ s : GeometricPoint S, P ((geometricPointSitePoint B S hS s).sheafFiber.obj
        ((SmallEtale.sheafEquiv B S hS A).inverse.obj F)) := by
  rw [forall_isSepClosed_iff_forall P hP F]
  exact forall_congr' fun s ↦
    ⟨hP (SmallEtale.sheafFiber_sheafEquiv_inverse_obj_iso B S hS A s F).symm,
      hP (SmallEtale.sheafFiber_sheafEquiv_inverse_obj_iso B S hS A s F)⟩

/-- **The bounded-site form.** For a sheaf `F` on the bounded small étale site, a stalk property
invariant under isomorphism holds at every separably closed point of its transport to Mathlib's
site if and only if it holds at every geometric point of `F` itself. -/
theorem forall_isSepClosed_sheafEquiv_iff_forall (P : A → Prop)
    (hP : ∀ {X Y : A}, (X ≅ Y) → P X → P Y) (F : Sheaf (SmallEtale.topology B S hS) A) :
    (∀ (k : Type u) [Field k] [IsSepClosed k] (y : Spec (.of k) ⟶ S),
        P ((Scheme.pointSmallEtale y).sheafFiber.obj ((SmallEtale.sheafEquiv B S hS A).functor.obj
          F))) ↔
      ∀ s : GeometricPoint S, P ((geometricPointSitePoint B S hS s).sheafFiber.obj F) := by
  rw [forall_isSepClosed_iff_forall P hP]
  exact forall_congr' fun s ↦
    ⟨hP (SmallEtale.sheafFiber_sheafEquiv_functor_obj_iso B S hS A s F),
      hP (SmallEtale.sheafFiber_sheafEquiv_functor_obj_iso B S hS A s F).symm⟩

end Quantifiers

end AlgebraicGeometry.GeometricPoint
