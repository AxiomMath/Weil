module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Attr

/-!
# The stalk at an étale geometric point

Let `x : Spec Ω ⟶ S` be a geometric point of a scheme `S` which is itself an étale morphism.
Then `(Spec Ω, x)` is an object of the small étale site of `S`, and together with the identity
lift it is an initial étale neighbourhood of `x`: a morphism of neighbourhoods
`(Spec Ω, id) ⟶ (U, u)` is an `S`-morphism `h : Spec Ω ⟶ U` with `id ≫ h = u`, so `h = u`.
Consequently, for every presheaf `P` on the small étale site, the colimit computing the stalk
`P_x` is attained at this neighbourhood: the canonical germ map `P(Spec Ω → S) ⟶ P_x` is an
isomorphism (a bijection for presheaves of sets).

## Main results

* `CategoryTheory.GrothendieckTopology.Point.isIso_toPresheafFiber_of_isInitial`: for any point
  of any site, the germ map at an initial object of the category of elements of the fiber
  functor is an isomorphism.
* `AlgebraicGeometry.Scheme.isIso_pointSmallEtale_toPresheafFiber_of_etale`: the statement on
  Mathlib's small étale site `S.Etale`, at the point `Scheme.pointSmallEtale x`.
* `AlgebraicGeometry.isIso_geometricPointSitePoint_toPresheafFiber_of_isIso`: the statement on
  the bounded small étale site `AlgebraicGeometry.SmallEtale B S hS`, at the site point
  `AlgebraicGeometry.geometricPointSitePoint` of a geometric point `s`: the germ at an object
  `X` with a lift `x` of `s` which is an isomorphism `Spec Ω ≅ X` is an isomorphism.
* `AlgebraicGeometry.isIso_geometricPointSitePoint_toPresheafFiber_of_etale`: the same at the
  object `Spec Ω` itself, when `s` is étale and `Spec Ω` lies in the big étale site.

## Implementation notes

The stalk is `CategoryTheory.GrothendieckTopology.Point.presheafFiber`, the colimit over the
opposite of the category of elements of the fiber functor, which is the category of étale
neighbourhoods; the germ map is `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber`.
The coefficient category is arbitrary (with the colimits defining the stalk); for presheaves of
sets an isomorphism is a bijection (`CategoryTheory.isIso_iff_bijective`).

On the bounded site an object is a scheme of the big étale site, so `Spec Ω` is an object of it
only up to the size bound; the statement for an object `X` with an invertible lift of `s` covers
every object isomorphic over `S` to `Spec Ω`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.8
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- If `(X, x)` is an initial object of the category of elements of the fiber functor of a
point `Φ`, the stalk of every presheaf at `Φ` is its value at `X`: the germ map is an
isomorphism. -/
theorem isIso_toPresheafFiber_of_isInitial (X : C) (x : Φ.fiber.obj X)
    (h : IsInitial (show Φ.fiber.Elements from ⟨X, x⟩)) (P : Cᵒᵖ ⥤ A) :
    IsIso (Φ.toPresheafFiber X x P) :=
  (Φ.isColimitPresheafFiberCocone P).isIso_ι_app_of_isTerminal (op ⟨X, x⟩) h.op

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry

namespace Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ S)
  [Etale x]

/-- The identity of `Spec Ω`, as a lift of the étale geometric point `x` to the object
`Etale.mk x` of the small étale site. -/
def pointSmallEtaleEtaleMkIdElement :
    (pointSmallEtale x).fiber.obj (Etale.mk x) :=
  Over.homMk (𝟙 _) (by change 𝟙 _ ≫ x = x; simp)

/-- An étale geometric point `x`, with its identity lift, is an initial étale neighbourhood of
itself. -/
def isInitialPointSmallEtaleEtaleMk :
    IsInitial (show (pointSmallEtale x).fiber.Elements from
      ⟨Etale.mk x, pointSmallEtaleEtaleMkIdElement x⟩) := by
  refine IsInitial.ofUniqueHom
    (fun U ↦ CategoryOfElements.homMk _ U
      (MorphismProperty.Over.homMk U.2.left (Over.w U.2)) ?_) (fun U m ↦ ?_)
  · apply Over.OverMorphism.ext
    change 𝟙 _ ≫ U.2.left = U.2.left
    exact Category.id_comp _
  · apply CategoryOfElements.ext
    apply MorphismProperty.Over.Hom.ext
    have h : 𝟙 _ ≫ m.1.left = U.2.left := congrArg (fun b ↦ b.left) m.2
    exact (Category.id_comp m.1.left).symm.trans h

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

/-- **Stalk at an étale geometric point** (FK I.8). If a geometric point `x : Spec Ω ⟶ S`
(`Ω` separably closed) is étale, then for every presheaf `P` on the small étale site of `S`
the canonical map `P(Spec Ω → S) ⟶ P_x` to the stalk is an isomorphism. -/
@[weil "lem_fk108_stalk_at_etale_geometric_point"]
theorem isIso_pointSmallEtale_toPresheafFiber_of_etale (P : S.Etaleᵒᵖ ⥤ A) :
    IsIso ((pointSmallEtale x).toPresheafFiber (Etale.mk x)
      (pointSmallEtaleEtaleMkIdElement x) P) :=
  (pointSmallEtale x).isIso_toPresheafFiber_of_isInitial _ _
    (isInitialPointSmallEtaleEtaleMk x) P

/-- For a presheaf of sets, the canonical map from the sections over an étale geometric point
to the stalk there is bijective. -/
theorem bijective_pointSmallEtale_toPresheafFiber_of_etale (P : S.Etaleᵒᵖ ⥤ Type u) :
    Function.Bijective ((pointSmallEtale x).toPresheafFiber (Etale.mk x)
      (pointSmallEtaleEtaleMkIdElement x) P) :=
  (isIso_iff_bijective _).mp (isIso_pointSmallEtale_toPresheafFiber_of_etale x P)

end Scheme

section SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- If a lift `x : Spec Ω ⟶ X` of the geometric point `s` to an object `X` of the small étale
site is an isomorphism, then `(X, x)` is an initial étale neighbourhood of `s`: the unique
morphism of neighbourhoods to `(U, u)` is `x⁻¹ ≫ u`. -/
def isInitialGeometricPointSitePointOfIsIso (X : SmallEtale B S hS)
    (x : (geometricPointSitePoint B S hS s).fiber.obj X) [IsIso x.1] :
    IsInitial (show (geometricPointSitePoint B S hS s).fiber.Elements from ⟨X, x⟩) := by
  have key : ∀ (U : (geometricPointSitePoint B S hS s).fiber.Elements),
      ∃! h : X ⟶ U.1, x.1 ≫ (SmallEtale.toScheme B S hS).map h = U.2.1 := by
    intro U
    have hw : B.inclusion.preimage (inv x.1 ≫ U.2.1) ≫ U.1.obj.hom = X.obj.hom := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage, Category.assoc, U.2.2,
        IsIso.inv_comp_eq, x.2]
    refine ⟨ObjectProperty.homMk (Over.homMk (B.inclusion.preimage (inv x.1 ≫ U.2.1)) hw),
      ?_, fun m hm ↦ ?_⟩
    · change x.1 ≫ B.inclusion.map (B.inclusion.preimage (inv x.1 ≫ U.2.1)) = U.2.1
      rw [Functor.map_preimage, IsIso.hom_inv_id_assoc]
    · apply (SmallEtale.toScheme B S hS).map_injective
      change (SmallEtale.toScheme B S hS).map m =
        B.inclusion.map (B.inclusion.preimage (inv x.1 ≫ U.2.1))
      rw [Functor.map_preimage, IsIso.eq_inv_comp, hm]
  refine IsInitial.ofUniqueHom
    (fun U ↦ CategoryOfElements.homMk _ U (key U).choose
      (Subtype.ext (key U).choose_spec.1)) (fun U m ↦ ?_)
  apply CategoryOfElements.ext
  exact (key U).unique (congrArg Subtype.val m.2) (key U).choose_spec.1

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{u, u} A]

/-- **Stalk at an étale geometric point** (FK I.8), on the bounded small étale site. If an
object `X` of the small étale site of `S` carries a lift `x` of the geometric point `s` which is
an isomorphism `Spec Ω ≅ X` (so `X` is `Spec Ω → S` up to isomorphism over `S`), then for every
presheaf `P` the germ map `P(X) ⟶ P_s` to the stalk is an isomorphism. -/
@[weil "lem_fk108_stalk_at_etale_geometric_point"]
theorem isIso_geometricPointSitePoint_toPresheafFiber_of_isIso (X : SmallEtale B S hS)
    (x : (geometricPointSitePoint B S hS s).fiber.obj X) [IsIso x.1]
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    IsIso ((geometricPointSitePoint B S hS s).toPresheafFiber X x P) :=
  (geometricPointSitePoint B S hS s).isIso_toPresheafFiber_of_isInitial _ _
    (isInitialGeometricPointSitePointOfIsIso B S hS s X x) P

/-- The geometric point `s`, when it is étale and its source lies in the big étale site, as an
object of the small étale site of `S`. -/
def GeometricPoint.toSmallEtale [Etale s.hom] (h : B.Contains s.source) : SmallEtale B S hS :=
  ⟨Over.mk (Y := B.obj s.source h) (ObjectProperty.homMk s.hom), by
    change Etale s.hom; infer_instance⟩

/-- The identity lift of `s` to the object `GeometricPoint.toSmallEtale`. -/
def GeometricPoint.toSmallEtaleIdElement [Etale s.hom] (h : B.Contains s.source) :
    (geometricPointSitePoint B S hS s).fiber.obj (s.toSmallEtale B S hS h) :=
  ⟨𝟙 _, Category.id_comp _⟩

instance [Etale s.hom] (h : B.Contains s.source) :
    IsIso (s.toSmallEtaleIdElement B S hS h).1 :=
  inferInstanceAs (IsIso (𝟙 _))

/-- **Stalk at an étale geometric point** (FK I.8), at the object `Spec Ω → S` itself: if the
geometric point `s` is étale and `Spec Ω` lies in the big étale site, the germ map
`P(Spec Ω → S) ⟶ P_s` at the identity lift is an isomorphism for every presheaf `P`. -/
theorem isIso_geometricPointSitePoint_toPresheafFiber_of_etale [Etale s.hom]
    (h : B.Contains s.source) (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    IsIso ((geometricPointSitePoint B S hS s).toPresheafFiber (s.toSmallEtale B S hS h)
      (s.toSmallEtaleIdElement B S hS h) P) :=
  isIso_geometricPointSitePoint_toPresheafFiber_of_isIso B S hS s _ _ P

end SmallEtale

end AlgebraicGeometry
