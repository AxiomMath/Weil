module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian

/-!
# Comparison of the small étale site of Stacks with Mathlib's

Let `B` be a big étale site containing a scheme `S`. The library carries two small étale sites
of `S`: the bounded one `AlgebraicGeometry.SmallEtale B S hS` of [Stacks, Tag 021B], which is
the convention of this library, and Mathlib's `S.Etale` with `S.smallEtaleTopology`, where
Mathlib's points `AlgebraicGeometry.Scheme.pointSmallEtale`, sheafification and skyscraper
sheaves live. The inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite` is a dense subsite
inclusion (StacksFrontier, `AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`), so the two
sites have equivalent categories of sheaves (`AlgebraicGeometry.SmallEtale.sheafEquiv`). This
file collects, for an arbitrary coefficient category, what downstream cohomology needs to move
statements across that equivalence:

* the stalk at a geometric point agrees on both sides, in both directions of the equivalence;
* the cohomology groups agree, naturally in the sheaf.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafEquivFunctorCompSheafFiberIso`: for a sheaf on the bounded
  site, the stalk of its transport to Mathlib's site at a geometric point `s` is its own stalk
  at the point `AlgebraicGeometry.geometricPointSitePoint` of `s`.
* `AlgebraicGeometry.SmallEtale.sheafEquivInverseCompSheafFiberIso`: for a sheaf on Mathlib's
  site, the stalk of its restriction to the bounded site is its stalk at
  `Scheme.pointSmallEtale s.hom`.
* `AlgebraicGeometry.SmallEtale.cohomologyAddEquiv`: `H^n(S.Etale, F) ≃+ H^n(SmallEtale, F|)`
  for an abelian sheaf `F` on Mathlib's site, with naturality
  `AlgebraicGeometry.SmallEtale.cohomologyAddEquiv_map`.

## Implementation notes

The stalk comparison is StacksFrontier's `AlgebraicGeometry.sheafFiberIsoOfAdjOfFiberIso` applied
to the fibre comparison `AlgebraicGeometry.toEtaleSiteFiberIso`, exactly as in StacksFrontier's
module-valued `AlgebraicGeometry.sheafEquivCompSheafFiberIso` and abelian
`AlgebraicGeometry.sheafEquivCompSmallEtaleStalkAbIso`; here it is stated for every coefficient
category with `u`-limits and `u`-colimits and for an unbundled `S`. The cohomology comparison is
StacksFrontier's `Stacks.Cohomology.DenseSubsite.hAddEquiv`; the `HasExt` instances are binders,
as in StacksFrontier, since the universe of the `Ext`-groups is not determined by the site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v' u' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comma categories `StructuredArrow X (toEtaleSite B S hS).op` are essentially small, so a
coefficient category with `u`-limits has limits of their shape; this is what the instances of
the dense subsite inclusion ask for. (StacksFrontier's
`AlgebraicGeometry.SmallEtale.hasLimitsOfShape_structuredArrow_toEtaleSite` is the case
`A = AddCommGrpCat.{u}`, stated as a theorem.) -/
instance hasLimitsOfShape_structuredArrow_toEtaleSite_of_hasLimitsOfSize (A : Type u')
    [Category.{v'} A]
    [HasLimitsOfSize.{u, u} A] (X : (S.Etale)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (toEtaleSite B S hS).op) A :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The inclusion into Mathlib's site is continuous. -/
instance isContinuous_toEtaleSite' :
    (toEtaleSite B S hS).IsContinuous (topology B S hS) S.smallEtaleTopology :=
  isContinuous_toEtaleSite B S hS

/-- Restriction of sheaves along the inclusion into Mathlib's site is an equivalence. -/
instance isEquivalence_sheafPushforwardContinuous_toEtaleSite (A : Type u') [Category.{v'} A]
    [HasLimitsOfSize.{u, u} A] :
    ((toEtaleSite B S hS).sheafPushforwardContinuous A (topology B S hS)
      S.smallEtaleTopology).IsEquivalence :=
  inferInstance

/-- The inverse of `AlgebraicGeometry.SmallEtale.sheafEquiv` is restriction of sheaves along the
inclusion `AlgebraicGeometry.SmallEtale.toEtaleSite`. -/
theorem sheafEquiv_inverse (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] :
    (sheafEquiv B S hS A).inverse =
      (toEtaleSite B S hS).sheafPushforwardContinuous A (topology B S hS)
        S.smallEtaleTopology :=
  rfl

section Stalks

variable (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A]
  (s : GeometricPoint S)

/-- **Stalks agree across the comparison of the two small étale sites.** For a sheaf `F` on the
bounded small étale site and a geometric point `s`, the stalk of the transported sheaf on
Mathlib's site at the point `Scheme.pointSmallEtale s.hom` is the stalk of `F` at the point
`AlgebraicGeometry.geometricPointSitePoint B S hS s` of the bounded site, naturally in `F`. -/
def sheafEquivFunctorCompSheafFiberIso :
    (sheafEquiv B S hS A).functor ⋙ (Scheme.pointSmallEtale s.hom).sheafFiber ≅
      (geometricPointSitePoint B S hS s).sheafFiber :=
  sheafFiberIsoOfAdjOfFiberIso (geometricPointSitePoint B S hS s)
    (Scheme.pointSmallEtale s.hom) (toEtaleSite B S hS) (toEtaleSiteFiberIso B S hS s)
    (sheafEquiv B S hS A).toAdjunction

/-- **Stalks agree across the comparison, read from Mathlib's site.** For a sheaf `F` on
Mathlib's small étale site and a geometric point `s`, the stalk of its restriction to the
bounded site at `AlgebraicGeometry.geometricPointSitePoint B S hS s` is the stalk of `F` at
`Scheme.pointSmallEtale s.hom`, naturally in `F`. -/
def sheafEquivInverseCompSheafFiberIso :
    (sheafEquiv B S hS A).inverse ⋙ (geometricPointSitePoint B S hS s).sheafFiber ≅
      (Scheme.pointSmallEtale s.hom).sheafFiber :=
  Functor.isoWhiskerLeft (sheafEquiv B S hS A).inverse
      (sheafEquivFunctorCompSheafFiberIso B S hS A s).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquiv B S hS A).counitIso _ ≪≫ Functor.leftUnitor _

/-- The per-sheaf form of `AlgebraicGeometry.SmallEtale.sheafEquivFunctorCompSheafFiberIso`. -/
def sheafFiber_sheafEquiv_functor_obj_iso (F : Sheaf (topology B S hS) A) :
    (Scheme.pointSmallEtale s.hom).sheafFiber.obj ((sheafEquiv B S hS A).functor.obj F) ≅
      (geometricPointSitePoint B S hS s).sheafFiber.obj F :=
  (sheafEquivFunctorCompSheafFiberIso B S hS A s).app F

/-- The per-sheaf form of `AlgebraicGeometry.SmallEtale.sheafEquivInverseCompSheafFiberIso`. -/
def sheafFiber_sheafEquiv_inverse_obj_iso (F : Sheaf S.smallEtaleTopology A) :
    (geometricPointSitePoint B S hS s).sheafFiber.obj ((sheafEquiv B S hS A).inverse.obj F) ≅
      (Scheme.pointSmallEtale s.hom).sheafFiber.obj F :=
  (sheafEquivInverseCompSheafFiberIso B S hS A s).app F

/-- A morphism of sheaves on the bounded site induces an isomorphism on the stalk at the point
`AlgebraicGeometry.geometricPointSitePoint B S hS s` iff its transport to Mathlib's site induces
an isomorphism on the stalk at `Scheme.pointSmallEtale s.hom`. -/
theorem isIso_sheafFiber_map_sheafEquiv_functor_iff {F G : Sheaf (topology B S hS) A}
    (φ : F ⟶ G) :
    IsIso ((Scheme.pointSmallEtale s.hom).sheafFiber.map
        ((sheafEquiv B S hS A).functor.map φ)) ↔
      IsIso ((geometricPointSitePoint B S hS s).sheafFiber.map φ) :=
  NatIso.isIso_map_iff (sheafEquivFunctorCompSheafFiberIso B S hS A s) φ

/-- A morphism of sheaves on Mathlib's site induces an isomorphism on the stalk at
`Scheme.pointSmallEtale s.hom` iff its restriction to the bounded site induces an isomorphism on
the stalk at `AlgebraicGeometry.geometricPointSitePoint B S hS s`. -/
theorem isIso_sheafFiber_map_sheafEquiv_inverse_iff {F G : Sheaf S.smallEtaleTopology A}
    (φ : F ⟶ G) :
    IsIso ((geometricPointSitePoint B S hS s).sheafFiber.map
        ((sheafEquiv B S hS A).inverse.map φ)) ↔
      IsIso ((Scheme.pointSmallEtale s.hom).sheafFiber.map φ) :=
  NatIso.isIso_map_iff (sheafEquivInverseCompSheafFiberIso B S hS A s) φ

end Stalks

section Cohomology

variable [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})]
  [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]

/-- **Cohomology agrees across the comparison of the two small étale sites.** For an abelian
sheaf `F` on Mathlib's small étale site, `H^n(S.Etale, F)` is the cohomology of its restriction
to the bounded small étale site of [Stacks, Tag 021B]. -/
def cohomologyAddEquiv (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    F.H n ≃+ ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.obj F).H n :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv (topology B S hS) S.smallEtaleTopology
    (toEtaleSite B S hS) F n

/-- The cohomology comparison `AlgebraicGeometry.SmallEtale.cohomologyAddEquiv` is natural in
the sheaf. -/
theorem cohomologyAddEquiv_map {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ) (x : F.H n) :
    cohomologyAddEquiv B S hS G n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.map φ) n
        (cohomologyAddEquiv B S hS F n x) :=
  Stacks.Cohomology.DenseSubsite.hAddEquiv_map (topology B S hS) S.smallEtaleTopology
    (toEtaleSite B S hS) φ n x

/-- Cohomology on the bounded site, read on Mathlib's: for an abelian sheaf `F` on the bounded
small étale site, its cohomology is that of its transport to Mathlib's site. -/
def cohomologyAddEquivOfSmallEtale (F : Sheaf (topology B S hS) AddCommGrpCat.{u}) (n : ℕ) :
    F.H n ≃+ ((sheafEquiv B S hS AddCommGrpCat.{u}).functor.obj F).H n :=
  ((Sheaf.functorH (topology B S hS) n).mapIso
      ((sheafEquiv B S hS AddCommGrpCat.{u}).unitIso.app F)).addCommGroupIsoToAddEquiv.trans
    (cohomologyAddEquiv B S hS ((sheafEquiv B S hS AddCommGrpCat.{u}).functor.obj F) n).symm

end Cohomology

end AlgebraicGeometry.SmallEtale
