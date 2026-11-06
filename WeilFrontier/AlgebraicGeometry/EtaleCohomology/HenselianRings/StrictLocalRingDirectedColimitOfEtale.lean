/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Presentable.Directed
public import WeilFrontier.AlgebraicGeometry.Morphisms.Etale
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.StalkColimits
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import Weil.Attr

/-!
# The strict local ring as a directed colimit of étale algebras

Let `x` be a geometric point of an affine scheme `Spec R`. The strict local ring `𝒪̃_{Spec R, x}`
(`AlgebraicGeometry.strictLocalRing`) is the colimit of the rings of functions `Γ(U, 𝒪_U)` over the
étale neighbourhoods `(U, u)` of `x`. Restricting to the affine étale neighbourhoods, which are
cofinal, the rings `Γ(U, 𝒪_U)` are étale `R`-algebras and the transition maps are maps of
`R`-algebras. The category of affine étale neighbourhoods is essentially small and cofiltered,
and every small filtered category receives a final functor from a directed partially ordered set
(`CategoryTheory.IsFiltered.exists_directed`). Hence `𝒪̃_{Spec R, x}` is, as an `R`-algebra, the
colimit of a directed system of étale `R`-algebras indexed by a directed partially ordered set.

## Main definitions

* `AlgebraicGeometry.strictLocalRingSpecAlgebra`: the `R`-algebra structure of the strict local
  ring of `Spec R` at a geometric point, through the germ of the functions on `Spec R`.

## Main results

* `AlgebraicGeometry.exists_directed_etale_colimit_iso_strictLocalRing`: the strict local ring of
  `Spec R` at a geometric point is isomorphic, as an `R`-algebra, to the colimit of a directed
  system of étale `R`-algebras indexed by a directed partially ordered set.

## Implementation notes

The directed system is a functor `E : I ⥤ CommAlgCat R` out of a directed partially ordered set,
so that the identities `E (i ≤ i) = id` and `E (j ≤ l) ∘ E (i ≤ j) = E (i ≤ l)` are the functor
laws; its colimit is taken in the category of commutative `R`-algebras. The source indexes the
system by isomorphism classes of connected affine étale neighbourhoods, ordered by the existence
of a (then unique) morphism; here the index is any directed set with a final functor to the small
model of the category of affine étale neighbourhoods of the bounded small étale site, which needs
neither connectedness nor the noetherian hypothesis on `R`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.2 and I.4
-/

/- FK's noetherian hypothesis on `C₀` is
dropped (generalization); FK's directed preordered set is a directed partial order here. -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace GeometricPoint.EtaleNeighborhood

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (s : GeometricPoint S)

/-- A quasi-compact étale neighbourhood, as an element of the fibre functor of the point of the
bounded small étale site. -/
private def boundedElement (U : EtaleNeighborhood s) [CompactSpace U.scheme] :
    (geometricPointSitePoint B S hS s).fiber.Elements :=
  have hU : B.Contains U.scheme :=
    (Scheme.size_le_of_locallyOfFiniteType U.toBase).trans_lt hS
  ⟨⟨Over.mk (ObjectProperty.homMk U.toBase : B.obj U.scheme hU ⟶ B.obj S hS),
    (inferInstance : Etale U.toBase)⟩, ⟨U.point, U.point_comp⟩⟩

private def boundedElementHom (U : EtaleNeighborhood s) [CompactSpace U.scheme] :
    (ofGeometricPointSitePointFiberElements B hS s).obj (boundedElement B hS s U) ⟶ U :=
  homMk (𝟙 U.scheme) (Category.id_comp _) (Category.comp_id _)

private def boundedElementInv (U : EtaleNeighborhood s) [CompactSpace U.scheme] :
    U ⟶ (ofGeometricPointSitePointFiberElements B hS s).obj (boundedElement B hS s U) :=
  homMk (𝟙 U.scheme) (Category.id_comp _) (Category.comp_id _)

/-- The elements of the fibre functor of the point of the bounded small étale site whose
underlying scheme is affine. -/
private def IsAffineElement : ObjectProperty (geometricPointSitePoint B S hS s).fiber.Elements :=
  fun e => IsAffine ((ofGeometricPointSitePointFiberElements B hS s).obj e).scheme

private lemma exists_isAffineElement_hom (e : (geometricPointSitePoint B S hS s).fiber.Elements) :
    ∃ a : (IsAffineElement B hS s).FullSubcategory, Nonempty (a.obj ⟶ e) := by
  set U := (ofGeometricPointSitePointFiberElements B hS s).obj e
  obtain ⟨R, j, hj, hy, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := U.point.base default) (U := ⊤) (by simp)
  have hrange : Set.range U.point.base ⊆ Set.range j.base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default]
    exact hy
  have hfac : IsOpenImmersion.lift j U.point hrange ≫ j = U.point :=
    IsOpenImmersion.lift_fac j U.point hrange
  let V : EtaleNeighborhood s :=
    { scheme := Spec R
      toBase := j ≫ U.toBase
      point := IsOpenImmersion.lift j U.point hrange
      point_comp := by rw [← Category.assoc, hfac, U.point_comp] }
  have hVU : V ⟶ U := homMk (U := V) j rfl hfac
  refine ⟨⟨boundedElement B hS s V, (inferInstance : IsAffine (Spec R))⟩,
    ⟨(ofGeometricPointSitePointFiberElements B hS s).preimage
      (boundedElementHom B hS s V ≫ hVU)⟩⟩

private instance isCofiltered_isAffineElement :
    IsCofiltered (IsAffineElement B hS s).FullSubcategory where
  cone_objs a b := by
    obtain ⟨c, ⟨f⟩⟩ := exists_isAffineElement_hom B hS s (IsCofiltered.min a.obj b.obj)
    exact ⟨c, ObjectProperty.homMk (f ≫ IsCofiltered.minToLeft _ _),
      ObjectProperty.homMk (f ≫ IsCofiltered.minToRight _ _), trivial⟩
  cone_maps {a b} f g := by
    obtain ⟨c, ⟨h⟩⟩ := exists_isAffineElement_hom B hS s (IsCofiltered.eq f.hom g.hom)
    refine ⟨c, ObjectProperty.homMk (h ≫ IsCofiltered.eqHom f.hom g.hom), ?_⟩
    ext1
    change (h ≫ IsCofiltered.eqHom f.hom g.hom) ≫ f.hom =
      (h ≫ IsCofiltered.eqHom f.hom g.hom) ≫ g.hom
    rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
  nonempty := by
    obtain ⟨e⟩ :=
      (IsCofiltered.nonempty : Nonempty (geometricPointSitePoint B S hS s).fiber.Elements)
    obtain ⟨a, -⟩ := exists_isAffineElement_hom B hS s e
    exact ⟨a⟩

private instance initial_ι_isAffineElement : (IsAffineElement B hS s).ι.Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (exists_isAffineElement_hom B hS s)

private instance essentiallySmall_isAffineElement :
    EssentiallySmall.{u} (IsAffineElement B hS s).FullSubcategory :=
  essentiallySmall_of_fully_faithful (IsAffineElement B hS s).ι

/-- The trivial étale neighbourhood `(S, s)` of `s`. -/
private def trivialNeighborhood : EtaleNeighborhood s where
  scheme := S
  toBase := 𝟙 S
  point := s.hom
  point_comp := Category.comp_id _

private instance [CompactSpace S] : CompactSpace (trivialNeighborhood s).scheme :=
  inferInstanceAs (CompactSpace S)

/-- The trivial étale neighbourhood `(S, s)`, as an element of the fibre functor of the point of
the bounded small étale site. -/
private def topElement [CompactSpace S] : (geometricPointSitePoint B S hS s).fiber.Elements :=
  boundedElement B hS s (trivialNeighborhood s)

/-- Every element maps to `topElement`, by its structure morphism. -/
private def toTopElement [CompactSpace S] (e : (geometricPointSitePoint B S hS s).fiber.Elements) :
    e ⟶ topElement B hS s :=
  (ofGeometricPointSitePointFiberElements B hS s).preimage
    (homMk (V := trivialNeighborhood s)
      ((ofGeometricPointSitePointFiberElements B hS s).obj e).toBase
      (Category.comp_id _) ((ofGeometricPointSitePointFiberElements B hS s).obj e).point_comp ≫
      boundedElementInv B hS s (trivialNeighborhood s))

private lemma strictLocalRingDiagram_map_toTopElement [CompactSpace S]
    (e : (geometricPointSitePoint B S hS s).fiber.Elements) :
    (strictLocalRingDiagram B S hS s).map (toTopElement B hS s e).op =
      ((ofGeometricPointSitePointFiberElements B hS s).obj e).toBase.appTop := by
  change ((ofGeometricPointSitePointFiberElements B hS s).map
    (toTopElement B hS s e)).hom.appTop = _
  rw [toTopElement, Functor.map_preimage]
  change Scheme.Hom.appTop
    (((ofGeometricPointSitePointFiberElements B hS s).obj e).toBase ≫ 𝟙 _) = _
  rw [Category.comp_id]

end GeometricPoint.EtaleNeighborhood

section Spec

open GeometricPoint.EtaleNeighborhood

variable {B : BigEtaleSite.{u}} (R : Type u) [CommRing R] (hX : B.Contains (Spec (.of R)))
  (x : GeometricPoint (Spec (.of R)))

/-- The strict local ring of `Spec R` at a geometric point `x` is an `R`-algebra, through the germ
at the trivial étale neighbourhood `(Spec R, x)` of the functions on `Spec R`. -/
@[instance_reducible]
def strictLocalRingSpecAlgebra : Algebra R (strictLocalRing B (Spec (.of R)) hX x) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫
    (strictLocalRingCocone B (Spec (.of R)) hX x).ι.app (op (topElement B hX x))).hom.toAlgebra

/-- The structure map `R ⟶ Γ(U, 𝒪_U)` of an étale neighbourhood. -/
private def structureMap (e : (geometricPointSitePoint B (Spec (.of R)) hX x).fiber.Elements) :
    CommRingCat.of R ⟶ (strictLocalRingDiagram B (Spec (.of R)) hX x).obj (op e) :=
  (Scheme.ΓSpecIso (.of R)).inv ≫
    ((ofGeometricPointSitePointFiberElements B hX x).obj e).toBase.appTop

private lemma structureMap_comp_ι
    (e : (geometricPointSitePoint B (Spec (.of R)) hX x).fiber.Elements) :
    structureMap R hX x e ≫ (strictLocalRingCocone B (Spec (.of R)) hX x).ι.app (op e) =
      (Scheme.ΓSpecIso (.of R)).inv ≫
        (strictLocalRingCocone B (Spec (.of R)) hX x).ι.app (op (topElement B hX x)) := by
  have h := (strictLocalRingCocone B (Spec (.of R)) hX x).w (toTopElement B hX x e).op
  erw [strictLocalRingDiagram_map_toTopElement] at h
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h)

private lemma structureMap_comp_map
    {e e' : (geometricPointSitePoint B (Spec (.of R)) hX x).fiber.Elements}
    (f : e' ⟶ e) :
    structureMap R hX x e ≫ (strictLocalRingDiagram B (Spec (.of R)) hX x).map f.op =
      structureMap R hX x e' := by
  change _ ≫ _ ≫ ((ofGeometricPointSitePointFiberElements B hX x).map f).hom.appTop = _
  rw [← Scheme.Hom.comp_appTop, ((ofGeometricPointSitePointFiberElements B hX x).map f).over]
  rfl

/-- The rings of functions `Γ(U, 𝒪_U)` on the affine étale neighbourhoods of the bounded small
étale site, as objects under `R`. -/
private def underDiagram :
    (IsAffineElement B hX x).FullSubcategoryᵒᵖ ⥤ Under (CommRingCat.of R) :=
  ((IsAffineElement B hX x).ι.op ⋙ strictLocalRingDiagram B (Spec (.of R)) hX x).toUnder
    (CommRingCat.of R) (fun a => structureMap R hX x a.unop.obj)
    (fun g => structureMap_comp_map R hX x g.unop.hom)

/-- **The strict local ring is a directed colimit of étale algebras.** Let `x` be a geometric
point of the affine scheme `Spec R`. There are a directed partially ordered set `I` and a functor
`E : I ⥤ CommAlgCat R` sending every `i` to an étale `R`-algebra `E i` (and every `i ≤ j` to an
`R`-algebra map `E i ⟶ E j`, with `E (i ≤ i) = id` and `E (j ≤ l) ∘ E (i ≤ j) = E (i ≤ l)`), whose
colimit is isomorphic, as an `R`-algebra, to the strict local ring `𝒪̃_{Spec R, x}`. -/
@[weil "lem_fk107_strict_local_ring_directed_colimit_of_etale"]
theorem exists_directed_etale_colimit_iso_strictLocalRing :
    letI := strictLocalRingSpecAlgebra R hX x
    ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
      (E : I ⥤ CommAlgCat.{u} R), (∀ i, Algebra.Etale R (E.obj i)) ∧
        Nonempty (colimit E ≅ CommAlgCat.of R (strictLocalRing B (Spec (.of R)) hX x)) := by
  let := strictLocalRingSpecAlgebra R hX x
  let P := IsAffineElement B hX x
  let eqv := equivSmallModel.{u} P.FullSubcategoryᵒᵖ
  have : IsFiltered (SmallModel.{u} P.FullSubcategoryᵒᵖ) := IsFiltered.of_equivalence eqv
  obtain ⟨I, _, hdir, hne, Φ, hΦ⟩ :=
    IsFiltered.exists_directed (SmallModel.{u} P.FullSubcategoryᵒᵖ)
  let G : I ⥤ P.FullSubcategoryᵒᵖ := Φ ⋙ eqv.inverse
  let E := G ⋙ underDiagram R hX x ⋙ (commAlgCatEquivUnder (.of R)).inverse
  refine ⟨I, inferInstance, hdir, hne, E, fun i => ?_, ?_⟩
  · have ha : IsAffine ((ofGeometricPointSitePointFiberElements B hX x).obj
        (G.obj i).unop.obj).scheme := (G.obj i).unop.property
    rw [← RingHom.etale_algebraMap]
    change RingHom.Etale ((((ofGeometricPointSitePointFiberElements B hX x).obj
        (G.obj i).unop.obj).toBase.appTop).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
    refine RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _)) ?_
    exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  · have hc : IsColimit ((strictLocalRingCocone B (Spec (.of R)) hX x).whisker P.ι.op) :=
      (Functor.Final.isColimitWhiskerEquiv P.ι.op _).symm
        (isColimitStrictLocalRingCocone B (Spec (.of R)) hX x)
    have hcG := (Functor.Final.isColimitWhiskerEquiv G _).symm hc
    let cU : Cocone (G ⋙ underDiagram R hX x) :=
      { pt := Under.mk ((Scheme.ΓSpecIso (.of R)).inv ≫
          (strictLocalRingCocone B (Spec (.of R)) hX x).ι.app (op (topElement B hX x)))
        ι :=
          { app i := Under.homMk ((strictLocalRingCocone B (Spec (.of R)) hX x).ι.app
                (op (G.obj i).unop.obj)) (structureMap_comp_ι R hX x (G.obj i).unop.obj)
            naturality i j f := by
              ext1
              exact ((strictLocalRingCocone B (Spec (.of R)) hX x).w
                (G.map f).unop.hom.op).trans (Category.comp_id _).symm } }
    have : IsFiltered I := inferInstance
    have : IsConnected I := IsFiltered.isConnected I
    have hU : IsColimit cU := isColimitOfReflects (Under.forget _)
      (hcG.ofIsoColimit (Cocone.ext (Iso.refl _) (fun _ => Category.comp_id _)))
    exact ⟨(colimit.isColimit E).coconePointUniqueUpToIso
      (isColimitOfPreserves (commAlgCatEquivUnder (.of R)).inverse hU)⟩

end Spec

end AlgebraicGeometry
