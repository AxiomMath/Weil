module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.AffineTransitionLimit
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDirectedLimit
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# The strict localization system is a projective system of schemes

Let `S` be a locally noetherian scheme in a big étale site `B` and `s` a geometric point of `S`.
The connected affine étale neighbourhoods `(U, u)` of `s` form a cofiltered system of noetherian
affine schemes with affine transition morphisms, and the strict henselization
`Spec 𝒪^{sh}_{S,s}`, a noetherian affine scheme, is its limit. Hence the strict localization
system is a projective system of schemes with limit `Spec 𝒪^{sh}_{S,s} = lim U`.

## Main results

* `AlgebraicGeometry.essentiallySmall_connectedAffineEtaleNeighborhood`: the connected affine
  étale neighbourhoods of `s` form an essentially small category.
* `AlgebraicGeometry.isNoetherian_strictLocalizationDiagram_obj`: each connected affine étale
  neighbourhood of a geometric point of a locally noetherian scheme is noetherian.
* `AlgebraicGeometry.isNoetherianRing_etaleLocalRing`: the étale local ring at a geometric
  point of a locally noetherian scheme is noetherian.
* `AlgebraicGeometry.isNoetherian_strictHenselization`: the strict henselization at a geometric
  point of a locally noetherian scheme is noetherian.
* `AlgebraicGeometry.isProjectiveSystemWithLimit_strictLocalization`: the strict localization
  system, indexed by a small model of the connected affine étale neighbourhoods, is a projective
  system of schemes with limit the strict henselization.

## Implementation notes

A projective system of schemes (`AlgebraicGeometry.IsProjectiveSystemWithLimit`) is indexed by a
small category, while the category `AlgebraicGeometry.ConnectedAffineEtaleNeighborhood` of
connected affine neighbourhoods has a large type of objects. It is essentially small, and its
small model `AlgebraicGeometry.ConnectedAffineEtaleNeighborhoodIndex` — one object for each
isomorphism class of connected affine neighbourhoods — plays the role of the set of
representatives `I_x` of the source. The source assumes `S` noetherian and separated; only
locally noetherian is used, since every connected affine neighbourhood is affine, hence
separated, and quasi-compact.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4]
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The connected affine étale neighbourhoods of a geometric point form an essentially small
category. -/
instance essentiallySmall_connectedAffineEtaleNeighborhood :
    EssentiallySmall.{u} (ConnectedAffineEtaleNeighborhood B S hS s) :=
  essentiallySmall_of_fully_faithful (connectedAffineEtaleNeighborhoodInclusion B S hS s)

/-- A small model of the category of connected affine étale neighbourhoods of a geometric point:
one object for each isomorphism class. -/
abbrev ConnectedAffineEtaleNeighborhoodIndex : Type u :=
  SmallModel.{u} (ConnectedAffineEtaleNeighborhood B S hS s)

/-- The equivalence between the small model and the category of connected affine étale
neighbourhoods. -/
abbrev connectedAffineEtaleNeighborhoodIndexEquiv :
    ConnectedAffineEtaleNeighborhoodIndex B S hS s ≌ ConnectedAffineEtaleNeighborhood B S hS s :=
  (equivSmallModel.{u} (ConnectedAffineEtaleNeighborhood B S hS s)).symm

/-- The strict localization system, indexed by the small model of the connected affine étale
neighbourhoods. -/
abbrev strictLocalizationSmallDiagram :
    ConnectedAffineEtaleNeighborhoodIndex B S hS s ⥤ Scheme.{u} :=
  (connectedAffineEtaleNeighborhoodIndexEquiv B S hS s).functor ⋙ strictLocalizationDiagram B S hS s

/-- The strict localization cone, indexed by the small model of the connected affine étale
neighbourhoods. -/
abbrev strictLocalizationSmallCone : Cone (strictLocalizationSmallDiagram B S hS s) :=
  (strictLocalizationCone B S hS s).whisker
    (connectedAffineEtaleNeighborhoodIndexEquiv B S hS s).functor

/-- Each connected affine étale neighbourhood of a geometric point of a locally noetherian scheme
is noetherian: it is affine and étale over a locally noetherian scheme. -/
instance isNoetherian_strictLocalizationDiagram_obj [IsLocallyNoetherian S]
    (V : ConnectedAffineEtaleNeighborhood B S hS s) :
    IsNoetherian ((strictLocalizationDiagram B S hS s).obj V) := by
  let f : (strictLocalizationDiagram B S hS s).obj V ⟶ S := B.inclusion.map V.1.1.obj.hom
  have hf : Etale f := V.1.1.property
  have : IsLocallyNoetherian ((strictLocalizationDiagram B S hS s).obj V) :=
    LocallyOfFiniteType.isLocallyNoetherian f
  exact { }

/-- The étale local ring at a geometric point of a locally noetherian scheme is noetherian: it
is a strict henselization of a noetherian local ring. -/
instance isNoetherianRing_etaleLocalRing [IsLocallyNoetherian S] :
    IsNoetherianRing ↥(etaleLocalRing B S hS s) :=
  IsLocalRing.isNoetherianRing_of_isHenselization
    (A := ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
    (ResidueField ↥(etaleLocalRing B S hS s))

/-- The strict henselization at a geometric point of a locally noetherian scheme is noetherian. -/
instance isNoetherian_strictHenselization [IsLocallyNoetherian S] :
    IsNoetherian (strictHenselization B S hS s) :=
  inferInstance

/-- **The strict localization system is a projective system of schemes**: for a geometric point
`s` of a locally noetherian scheme `S`, the connected affine étale neighbourhoods of `s`, indexed
by a set of representatives of their isomorphism classes, form a projective system of schemes
with limit the strict henselization `Spec 𝒪^{sh}_{S,s}`. -/
@[weil "lem_fk104_strict_localization_is_projective_system"]
theorem isProjectiveSystemWithLimit_strictLocalization [IsLocallyNoetherian S] :
    IsProjectiveSystemWithLimit (strictLocalizationSmallDiagram B S hS s)
      (strictLocalizationSmallCone B S hS s) := by
  have : IsCofiltered (ConnectedAffineEtaleNeighborhoodIndex B S hS s) :=
    IsCofiltered.of_equivalence (connectedAffineEtaleNeighborhoodIndexEquiv B S hS s).symm
  have : ∀ {i j : ConnectedAffineEtaleNeighborhoodIndex B S hS s} (f : i ⟶ j),
      IsAffineHom ((strictLocalizationSmallDiagram B S hS s).map f) := fun _ =>
    isAffineHom_strictLocalizationDiagram_map B S hS s _
  have : ∀ i, IsNoetherian ((strictLocalizationSmallDiagram B S hS s).obj i) :=
    fun _ => isNoetherian_strictLocalizationDiagram_obj B S hS s _
  have : ∀ i, ((strictLocalizationSmallDiagram B S hS s).obj i).IsSeparated :=
    fun i => (inferInstance : ((strictLocalizationDiagram B S hS s).obj
      ((connectedAffineEtaleNeighborhoodIndexEquiv B S hS s).functor.obj i)).IsSeparated)
  have : IsNoetherian (strictLocalizationSmallCone B S hS s).pt :=
    isNoetherian_strictHenselization B S hS s
  have : (strictLocalizationSmallCone B S hS s).pt.IsSeparated :=
    (inferInstance : (strictHenselization B S hS s).IsSeparated)
  exact .of_isLimit ((strictLocalizationConeIsLimit B S hS s).whiskerEquivalence
    (connectedAffineEtaleNeighborhoodIndexEquiv B S hS s))

end AlgebraicGeometry
