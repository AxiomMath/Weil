module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDirectedLimit
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents

/-!
# The strict localization system of a geometric point

Let `S` be a scheme in a big étale site `B` and `s` a geometric point of `S`. The *strict
localization system* of `s` is the inverse system formed by the étale neighbourhoods `(U, u)` of
`s` whose underlying scheme `U` is affine and connected, with the morphisms of neighbourhoods
between them, together with the strict henselization `Spec 𝒪^{sh}_{S,s}` and its canonical
morphisms into each `U`, which on global functions are the coprojections
`Γ(U, 𝒪_U) → 𝒪^{sh}_{S,s}` of the colimit defining the strict local ring.

When `S` is locally noetherian, every étale neighbourhood of `s` is refined by a connected affine
one (the connected component of the lift of `s` in an affine étale neighbourhood is open and
closed, hence affine), so the connected affine neighbourhoods form a cofiltered category, initial
among all étale neighbourhoods, and the strict henselization is the limit of the system.

## Main definitions

* `AlgebraicGeometry.IsConnectedAffineEtaleNeighborhood`: the étale neighbourhoods of `s` whose
  underlying scheme is affine and connected.
* `AlgebraicGeometry.ConnectedAffineEtaleNeighborhood`: the full subcategory they span, the index
  category of the strict localization system.
* `AlgebraicGeometry.strictLocalizationDiagram`: the inverse system of schemes `U`.
* `AlgebraicGeometry.strictLocalizationCone`: the cone on it with vertex the strict henselization
  and legs the canonical morphisms into the neighbourhoods.

## Main results

* `AlgebraicGeometry.exists_isConnectedAffineEtaleNeighborhood_hom`: over a locally noetherian
  scheme, every étale neighbourhood of `s` is refined by a connected affine one.
* `AlgebraicGeometry.isCofiltered_connectedAffineEtaleNeighborhood` and
  `AlgebraicGeometry.initial_connectedAffineEtaleNeighborhoodInclusion`: the index category is
  cofiltered and initial among all étale neighbourhoods.
* `AlgebraicGeometry.strictLocalizationConeIsLimit`: the strict henselization is the limit of the
  strict localization system.
* `AlgebraicGeometry.strictLocalizationCone_π_appTop`: the legs are the coprojections on global
  functions.

## Implementation notes

Instead of a set of representatives of the isomorphism classes of connected affine
neighbourhoods, preordered by the existence of a morphism, with a chosen morphism for each
relation, the index is the full subcategory of connected affine neighbourhoods itself. Its
cofinality in the category of all étale neighbourhoods is what the limit statements use; the
directed preorder of the source is recovered by any initial functor from a directed set
(`CategoryTheory.IsFiltered.exists_directed`), as for the affine system
`AlgebraicGeometry.affineEtaleNeighborhoodDirectedSystem`. The source assumes `S` noetherian
and separated; the definition needs no hypothesis, and cofinality needs only that `S` is locally
noetherian.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4]
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The étale neighbourhoods of a geometric point whose underlying scheme is affine and
connected. -/
def IsConnectedAffineEtaleNeighborhood : ObjectProperty (geometricPointFiber B S hS s).Elements :=
  fun V => IsAffine ((etaleNeighborhoodDiagram B S hS s).obj V) ∧
    ConnectedSpace ((etaleNeighborhoodDiagram B S hS s).obj V)

/-- **The index category of the strict localization system**: the connected affine étale
neighbourhoods of a geometric point, with the morphisms of neighbourhoods between them. -/
@[weil "def_fk104_strict_localization_projective_system"]
abbrev ConnectedAffineEtaleNeighborhood : Type (u + 1) :=
  (IsConnectedAffineEtaleNeighborhood B S hS s).FullSubcategory

/-- The inclusion of the connected affine étale neighbourhoods into all étale neighbourhoods. -/
abbrev connectedAffineEtaleNeighborhoodInclusion :
    ConnectedAffineEtaleNeighborhood B S hS s ⥤ (geometricPointFiber B S hS s).Elements :=
  (IsConnectedAffineEtaleNeighborhood B S hS s).ι

/-- **The strict localization system of a geometric point**: the inverse system of the
underlying schemes of its connected affine étale neighbourhoods. -/
@[weil "def_fk104_strict_localization_projective_system"]
abbrev strictLocalizationDiagram : ConnectedAffineEtaleNeighborhood B S hS s ⥤ Scheme.{u} :=
  connectedAffineEtaleNeighborhoodInclusion B S hS s ⋙ etaleNeighborhoodDiagram B S hS s

/-- Each scheme of the strict localization system is affine. -/
instance (V : ConnectedAffineEtaleNeighborhood B S hS s) :
    IsAffine ((strictLocalizationDiagram B S hS s).obj V) :=
  V.2.1

/-- Each scheme of the strict localization system is connected. -/
instance (V : ConnectedAffineEtaleNeighborhood B S hS s) :
    ConnectedSpace ((strictLocalizationDiagram B S hS s).obj V) :=
  V.2.2

/-- The transition morphisms of the strict localization system are affine. -/
instance isAffineHom_strictLocalizationDiagram_map
    {V W : ConnectedAffineEtaleNeighborhood B S hS s} (m : V ⟶ W) :
    IsAffineHom ((strictLocalizationDiagram B S hS s).map m) :=
  inferInstance

/-- **The strict localization system with its limit**: the cone on the strict localization
system with vertex the strict henselization `Spec 𝒪^{sh}_{S,s}` and legs the canonical morphisms
into the connected affine neighbourhoods. -/
@[weil "def_fk104_strict_localization_projective_system"]
def strictLocalizationCone : Cone (strictLocalizationDiagram B S hS s) :=
  (strictHenselizationCone B S hS s).whisker (connectedAffineEtaleNeighborhoodInclusion B S hS s)

/-- The vertex of the strict localization cone is the strict henselization. -/
@[simp]
theorem strictLocalizationCone_pt :
    (strictLocalizationCone B S hS s).pt = strictHenselization B S hS s :=
  rfl

/-- The leg of the strict localization cone at a connected affine neighbourhood `(U, u)` is the
unique morphism from the strict henselization to `U` over `S` carrying the canonical geometric
point of the strict henselization to `u`. -/
theorem strictLocalizationCone_π_app (V : ConnectedAffineEtaleNeighborhood B S hS s) :
    (strictLocalizationCone B S hS s).π.app V =
      strictHenselizationNeighborhoodLift B S hS s
        ((geometricPointNeighborhoodInclusion B S hS s).obj V.1).1
        ((geometricPointNeighborhoodInclusion B S hS s).obj V.1).2 :=
  strictHenselizationCone_π_app_eq_neighborhoodLift_elements B S hS s V.1

/-- **The legs of the strict localization cone are the coprojections on global functions**:
restricting a global function on a connected affine neighbourhood along the leg and reading it
in the strict local ring is the structure map of the colimit defining that ring. -/
theorem strictLocalizationCone_π_appTop (V : ConnectedAffineEtaleNeighborhood B S hS s)
    (b : Γ((strictLocalizationDiagram B S hS s).obj V, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of ↥(etaleLocalRing B S hS s))).hom.hom
        (((strictLocalizationCone B S hS s).π.app V).appTop.hom b) =
      (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) (op V.1)).hom b :=
  strictHenselizationCone_π_appTop B S hS s V.1 b

/-! ### Cofinality over a locally noetherian base -/

/-- An open and closed subscheme of an affine scheme is affine. -/
theorem isAffine_of_isClosed_opens {X : Scheme.{u}} [IsAffine X] (W : X.Opens)
    (hW : IsClosed (W : Set X)) : IsAffine W := by
  have : IsClosedImmersion W.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  exact isAffine_of_isAffineHom W.ι

/-- **Every étale neighbourhood of a geometric point of a locally noetherian scheme is refined by
a connected affine one**: in an affine refinement, the connected component of the lift of the
point is open and closed, hence an affine open subscheme. -/
theorem exists_isConnectedAffineEtaleNeighborhood_hom [IsLocallyNoetherian S]
    (U : (geometricPointFiber B S hS s).Elements) :
    ∃ V : (geometricPointFiber B S hS s).Elements,
      IsConnectedAffineEtaleNeighborhood B S hS s V ∧ Nonempty (V ⟶ U) := by
  obtain ⟨V, hVa, ⟨g⟩⟩ := exists_affine_etaleNeighborhood B S hS s U
  let X : Scheme.{u} := (SmallEtale.toScheme B S hS).obj V.1
  have : IsAffine X := hVa
  let f : X ⟶ S := B.inclusion.map V.1.obj.hom
  have hf : Etale f := V.1.property
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let x : X := V.2.1 (default : s.source)
  let W : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  have hWa : IsAffine W := isAffine_of_isClosed_opens W isClosed_connectedComponent
  have hWc : ConnectedSpace W :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := x))
  have hrange : Set.range V.2.1 ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default]
    exact mem_connectedComponent
  let y : s.source ⟶ W := IsOpenImmersion.lift W.ι V.2.1 hrange
  have hy : y ≫ W.ι = V.2.1 := IsOpenImmersion.lift_fac W.ι V.2.1 hrange
  have hjf : Etale (W.ι ≫ B.inclusion.map V.1.obj.hom) := inferInstance
  have hR : B.Contains W :=
    (Scheme.size_le_of_locallyOfFiniteType (W.ι ≫ B.inclusion.map V.1.obj.hom)).trans_lt hS
  let V' : SmallEtale B S hS :=
    ⟨Over.mk (ObjectProperty.homMk (W.ι ≫ B.inclusion.map V.1.obj.hom) :
      B.obj W hR ⟶ B.obj S hS), hjf⟩
  have hyS : y ≫ B.inclusion.map V'.obj.hom = s.hom := by
    change y ≫ (W.ι ≫ B.inclusion.map V.1.obj.hom) = s.hom
    rw [← Category.assoc, hy]
    exact V.2.2
  refine ⟨⟨V', ⟨y, hyS⟩⟩, ⟨hWa, hWc⟩, ⟨?_ ≫ g⟩⟩
  refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk W.ι) ?_), Subtype.ext hy⟩
  apply ObjectProperty.hom_ext
  rfl

/-- Over a locally noetherian scheme, the connected affine étale neighbourhoods of a geometric
point form a cofiltered category. -/
instance isCofiltered_connectedAffineEtaleNeighborhood [IsLocallyNoetherian S] :
    IsCofiltered (ConnectedAffineEtaleNeighborhood B S hS s) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (connectedAffineEtaleNeighborhoodInclusion B S hS s) fun U => by
      obtain ⟨V, hV, hm⟩ := exists_isConnectedAffineEtaleNeighborhood_hom B S hS s U
      exact ⟨⟨V, hV⟩, hm⟩

/-- Over a locally noetherian scheme, the inclusion of the connected affine étale neighbourhoods
of a geometric point into all its étale neighbourhoods is initial. -/
instance initial_connectedAffineEtaleNeighborhoodInclusion [IsLocallyNoetherian S] :
    (connectedAffineEtaleNeighborhoodInclusion B S hS s).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    (connectedAffineEtaleNeighborhoodInclusion B S hS s) fun U => by
      obtain ⟨V, hV, hm⟩ := exists_isConnectedAffineEtaleNeighborhood_hom B S hS s U
      exact ⟨⟨V, hV⟩, hm⟩

/-- **The strict henselization is the limit of the strict localization system** of a geometric
point of a locally noetherian scheme. -/
def strictLocalizationConeIsLimit [IsLocallyNoetherian S] :
    IsLimit (strictLocalizationCone B S hS s) :=
  (Functor.Initial.isLimitWhiskerEquiv (connectedAffineEtaleNeighborhoodInclusion B S hS s)
    (strictHenselizationCone B S hS s)).symm (strictHenselizationConeIsLimit B S hS s)

end AlgebraicGeometry
