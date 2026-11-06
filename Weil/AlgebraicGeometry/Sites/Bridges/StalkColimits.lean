module

public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.CategoryTheory.Sites.Point.Skyscraper
public import Weil.CategoryTheory.Sites.PreservesSheafification
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Stalks, colimits, sheafification and étale neighbourhoods on the bounded small étale site

Let `B` be a big étale site containing a scheme `S`, and let `SmallEtale B S hS` be the bounded
small étale site of `S` of [Stacks, Tag 021B]. Its sheaf categories are equivalent to those of
Mathlib's small étale site `S.Etale` (`AlgebraicGeometry.SmallEtale.sheafEquiv`), compatibly
with the stalks at a geometric point `s`: the stalk at Mathlib's point
`AlgebraicGeometry.Scheme.pointSmallEtale s.hom` of the transport of a sheaf is its stalk at the
point `AlgebraicGeometry.geometricPointSitePoint B S hS s` of the bounded site. This file moves
across that comparison the following facts about Mathlib's site:

* the categories of étale sheaves of sets and of abelian groups have small colimits, and the
  stalk at a geometric point commutes with them;
* the forgetful functor from sheaves of `Λ`-modules to abelian sheaves commutes with
  sheafification, and the `Λ`-module sheafification of a presheaf of `Λ`-modules is its abelian
  sheafification with the sheafified scalar endomorphisms;
* the category of étale neighbourhoods of a geometric point `s` receives the category of elements
  of the fibre functor of `geometricPointSitePoint B S hS s` through a fully faithful initial
  functor, compatibly with the forgetful functors to `S.Etale`.

## Main results

* `AlgebraicGeometry.Scheme.bijective_colimit_post_sheafFiber_geometricPointSitePoint`: the
  stalk at a geometric point commutes with small colimits of sheaves on the bounded site;
  `..._type` and `..._addCommGrp` for sheaves of sets and of abelian groups.
* `AlgebraicGeometry.Scheme.etale_sheafify_moduleCat_forget₂_smallEtale`: sheafification of a
  presheaf of `Λ`-modules on the bounded site.
* `AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.ofGeometricPointSitePointFiberElements`:
  the functor from the category of elements of the fibre functor of the bounded site's point to
  étale neighbourhoods, which is fully faithful and initial.

## Implementation notes

The category of étale neighbourhoods of `s` is not equivalent to the category of elements of
the fibre functor of `geometricPointSitePoint B S hS s`: an étale neighbourhood is an arbitrary
scheme of the universe of `S`, while the objects of the bounded site are bounded in size by the
cutoff of `B`. Every étale neighbourhood is dominated by an affine open which is an object of
the bounded site, which is what
makes the comparison functor initial; colimits over the two categories of neighbourhoods
therefore agree. For the same reason there is no forgetful functor from étale neighbourhoods to
the bounded site.

The coefficient categories of the general stalk statement have `u`-limits, which the
equivalence of sheaf categories needs; for sets and abelian groups in a universe containing `u`
this holds automatically.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2, I.4.
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

universe u w r

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

section Colimits

/-- The bounded small étale site form of
`AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtale_type`. -/
theorem hasColimitsOfShape_sheaf_smallEtale_type_sheafEquiv [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) (Type w)] (I : Type u) [Category.{u} I] :
    HasColimitsOfShape I (Sheaf (SmallEtale.topology B S hS) (Type w)) :=
  haveI := hasColimitsOfShape_sheaf_smallEtale_type.{u, w} (S := S) I
  Adjunction.hasColimitsOfShape_of_equivalence (SmallEtale.sheafEquiv B S hS (Type w)).functor

/-- The bounded small étale site form of
`AlgebraicGeometry.Scheme.hasColimitsOfShape_sheaf_smallEtale_addCommGrp`. -/
theorem hasColimitsOfShape_sheaf_smallEtale_addCommGrp_sheafEquiv [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) AddCommGrpCat.{w}] (I : Type u) [Category.{u} I] :
    HasColimitsOfShape I (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{w}) :=
  haveI := hasColimitsOfShape_sheaf_smallEtale_addCommGrp.{u, w} (S := S) I
  Adjunction.hasColimitsOfShape_of_equivalence
    (SmallEtale.sheafEquiv B S hS AddCommGrpCat.{w}).functor

/-- The bounded small étale site form of
`AlgebraicGeometry.Scheme.bijective_colimit_post_sheafFiber_pointSmallEtale`: the stalk at the
point `geometricPointSitePoint B S hS s` commutes with small colimits. -/
theorem bijective_colimit_post_sheafFiber_geometricPointSitePoint
    {A : Type*} [Category A] [HasLimitsOfSize.{u, u} A] [HasColimitsOfSize.{u, u} A]
    {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    (s : GeometricPoint S)
    {I : Type*} [Category I] (K : I ⥤ Sheaf (SmallEtale.topology B S hS) A)
    [HasColimit K] [HasColimit (K ⋙ (geometricPointSitePoint B S hS s).sheafFiber)] :
    Function.Bijective
      (ConcreteCategory.hom (colimit.post K (geometricPointSitePoint B S hS s).sheafFiber)) := by
  set E := SmallEtale.sheafEquiv B S hS A
  set p := pointSmallEtale s.hom
  set q := geometricPointSitePoint B S hS s
  set α : E.functor ⋙ p.sheafFiber ≅ q.sheafFiber :=
    SmallEtale.sheafEquivFunctorCompSheafFiberIso B S hS A s
  have : HasColimit (K ⋙ E.functor) := inferInstance
  have : HasColimit ((K ⋙ E.functor) ⋙ p.sheafFiber) :=
    hasColimit_of_iso (Functor.isoWhiskerLeft K α)
  have : HasColimit (K ⋙ E.functor ⋙ p.sheafFiber) :=
    hasColimit_of_iso (Functor.isoWhiskerLeft K α)
  have h1 := bijective_colimit_post_sheafFiber_pointSmallEtale s.hom (K ⋙ E.functor)
  have h2 : Function.Bijective
      (ConcreteCategory.hom (colimit.post K (E.functor ⋙ p.sheafFiber))) := by
    rw [← colimit.post_post]
    have : IsIso (colimit.post K E.functor) := inferInstance
    rw [ConcreteCategory.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).comp h1
  have key : colimit.post K (E.functor ⋙ p.sheafFiber) ≫ α.hom.app (colimit K) =
      (HasColimit.isoOfNatIso (Functor.isoWhiskerLeft K α)).hom ≫
        colimit.post K q.sheafFiber := by
    ext j
    simp [← α.hom.naturality]
  have h3 : Function.Bijective (ConcreteCategory.hom
      ((HasColimit.isoOfNatIso (Functor.isoWhiskerLeft K α)).hom ≫
        colimit.post K q.sheafFiber)) := by
    rw [← key, ConcreteCategory.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).comp h2
  rw [ConcreteCategory.coe_comp] at h3
  exact (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso
      (HasColimit.isoOfNatIso (Functor.isoWhiskerLeft K α)).hom)).mp h3

/-- The bounded small étale site form of
`AlgebraicGeometry.Scheme.bijective_colimit_post_sheafFiber_pointSmallEtale_type`. -/
theorem bijective_colimit_post_sheafFiber_geometricPointSitePoint_type [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) (Type w)] (s : GeometricPoint S)
    {I : Type u} [Category.{u} I] (K : I ⥤ Sheaf (SmallEtale.topology B S hS) (Type w)) :
    haveI := hasColimitsOfShape_sheaf_smallEtale_type_sheafEquiv.{u, w} B hS I
    Function.Bijective (colimit.post K (geometricPointSitePoint B S hS s).sheafFiber) :=
  haveI := hasColimitsOfShape_sheaf_smallEtale_type_sheafEquiv.{u, w} B hS I
  bijective_colimit_post_sheafFiber_geometricPointSitePoint B hS s K

/-- The bounded small étale site form of
`AlgebraicGeometry.Scheme.bijective_colimit_post_sheafFiber_pointSmallEtale_addCommGrp`. -/
theorem bijective_colimit_post_sheafFiber_geometricPointSitePoint_addCommGrp [UnivLE.{u, w}]
    [HasSheafify (smallEtaleTopology S) AddCommGrpCat.{w}] (s : GeometricPoint S)
    {I : Type u} [Category.{u} I] (K : I ⥤ Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{w}) :
    haveI := hasColimitsOfShape_sheaf_smallEtale_addCommGrp_sheafEquiv.{u, w} B hS I
    Function.Bijective (colimit.post K (geometricPointSitePoint B S hS s).sheafFiber) :=
  haveI := hasColimitsOfShape_sheaf_smallEtale_addCommGrp_sheafEquiv.{u, w} B hS I
  bijective_colimit_post_sheafFiber_geometricPointSitePoint B hS s K

end Colimits

section Sheafification

variable (Λ : Type r) [Ring Λ] [UnivLE.{u + 1, w}]

attribute [local instance] preservesColimits_forget₂_moduleCat
  preservesFilteredColimits_forget_addCommGrpCat preservesFilteredColimits_forget_moduleCat
  hasLimitsOfShape_walkingMulticospan_moduleCat in
/-- The bounded small étale site form of
`AlgebraicGeometry.Scheme.preservesSheafification_forget₂_moduleCat`. -/
instance preservesSheafification_forget₂_moduleCat_smallEtale :
    (SmallEtale.topology B S hS).PreservesSheafification
      (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) :=
  GrothendieckTopology.instPreservesSheafification (SmallEtale.topology B S hS)
    (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})

attribute [local instance] preservesColimits_forget₂_moduleCat
  preservesFilteredColimits_forget_addCommGrpCat preservesFilteredColimits_forget_moduleCat in
/-- The bounded small étale site form of
`AlgebraicGeometry.Scheme.etale_sheafify_moduleCat_forget₂`. -/
theorem etale_sheafify_moduleCat_forget₂_smallEtale
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{w} Λ) :
    toSheafify (SmallEtale.topology B S hS)
          (P ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≫
        (sheafifyComposeIso (SmallEtale.topology B S hS)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom =
      Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS) P)
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ∧
    (∀ l : Λ, sheafifyMap (SmallEtale.topology B S hS)
          (Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l)) ≫
        (sheafifyComposeIso (SmallEtale.topology B S hS)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom =
      (sheafifyComposeIso (SmallEtale.topology B S hS)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) P).hom ≫
        Functor.whiskerLeft (sheafify (SmallEtale.topology B S hS) P)
          (ModuleCat.smulNatTrans Λ l)) ∧
    (∀ l : Λ, Functor.whiskerLeft P (ModuleCat.smulNatTrans Λ l) ≫
        Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS) P)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) =
      Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS) P)
          (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ≫
        Functor.whiskerLeft (sheafify (SmallEtale.topology B S hS) P)
          (ModuleCat.smulNatTrans Λ l)) ∧
    ∀ F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{w} Λ), Function.Bijective
      (fun φ : (presheafToSheaf (SmallEtale.topology B S hS) (ModuleCat.{w} Λ)).obj P ⟶ F ↦
        toSheafify (SmallEtale.topology B S hS) P ≫
          (sheafToPresheaf (SmallEtale.topology B S hS) (ModuleCat.{w} Λ)).map φ) :=
  sheafify_moduleCat_forget₂ (SmallEtale.topology B S hS) Λ P

end Sheafification

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.GeometricPoint.EtaleNeighborhood

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (s : GeometricPoint S)

/-- An element of the fibre functor of the point `geometricPointSitePoint B S hS s` of the
bounded small étale site, as an element of the fibre functor of Mathlib's point
`Scheme.pointSmallEtale s.hom`. -/
def toPointSmallEtaleFiberElements :
    (geometricPointSitePoint B S hS s).fiber.Elements ⥤
      (Scheme.pointSmallEtale s.hom).fiber.Elements where
  obj x := ⟨(SmallEtale.toEtaleSite B S hS).obj x.1,
    (toEtaleSiteFiberIso B S hS s).inv.app x.1 x.2⟩
  map {x y} f := ⟨(SmallEtale.toEtaleSite B S hS).map f.1, by
    have h := NatTrans.naturality_apply (toEtaleSiteFiberIso B S hS s).inv f.1 x.2
    exact h.symm.trans (congrArg _ f.2)⟩

instance : (toPointSmallEtaleFiberElements B hS s).Faithful where
  map_injective {x y} f g h := by
    apply Subtype.ext
    exact (SmallEtale.toEtaleSite B S hS).map_injective (congrArg Subtype.val h)

instance : (toPointSmallEtaleFiberElements B hS s).Full where
  map_surjective {x y} φ := by
    refine ⟨⟨(SmallEtale.toEtaleSite B S hS).preimage φ.1, ?_⟩, ?_⟩
    · apply (ConcreteCategory.bijective_of_isIso
        ((toEtaleSiteFiberIso B S hS s).inv.app y.1)).injective
      have h := NatTrans.naturality_apply (toEtaleSiteFiberIso B S hS s).inv
        ((SmallEtale.toEtaleSite B S hS).preimage φ.1) x.2
      refine h.trans ?_
      rw [Functor.comp_map]
      have hφ : (SmallEtale.toEtaleSite B S hS).map
          ((SmallEtale.toEtaleSite B S hS).preimage φ.1) = φ.1 :=
        (SmallEtale.toEtaleSite B S hS).map_preimage φ.1
      rw [hφ]
      exact φ.2
    · apply Subtype.ext
      exact (SmallEtale.toEtaleSite B S hS).map_preimage φ.1

/-- The bounded small étale site form of
`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.equivFiberElements`: an element of the fibre
functor of the point `geometricPointSitePoint B S hS s` of the bounded small étale site, as an
étale neighbourhood of `s`. -/
def ofGeometricPointSitePointFiberElements :
    (geometricPointSitePoint B S hS s).fiber.Elements ⥤ EtaleNeighborhood s :=
  toPointSmallEtaleFiberElements B hS s ⋙ (equivFiberElements s).inverse

instance : (ofGeometricPointSitePointFiberElements B hS s).Faithful :=
  inferInstanceAs (toPointSmallEtaleFiberElements B hS s ⋙ (equivFiberElements s).inverse).Faithful

instance : (ofGeometricPointSitePointFiberElements B hS s).Full :=
  inferInstanceAs (toPointSmallEtaleFiberElements B hS s ⋙ (equivFiberElements s).inverse).Full

/-- The bounded small étale site form of
`AlgebraicGeometry.GeometricPoint.EtaleNeighborhood.forget`: on elements of the fibre functor of
the bounded site's point, the forgetful functor of étale neighbourhoods is the inclusion of the
bounded site into `S.Etale`. -/
theorem ofGeometricPointSitePointFiberElements_comp_forget :
    ofGeometricPointSitePointFiberElements B hS s ⋙ forget s =
      CategoryOfElements.π _ ⋙ SmallEtale.toEtaleSite B S hS :=
  rfl

/-- Every étale neighbourhood of `s` receives a morphism from an étale neighbourhood coming from
the bounded small étale site. -/
theorem exists_ofGeometricPointSitePointFiberElements_hom (U : EtaleNeighborhood s) :
    ∃ x, Nonempty ((ofGeometricPointSitePointFiberElements B hS s).obj x ⟶ U) := by
  obtain ⟨R, j, hj, hy, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := U.point.base default) (U := ⊤) (by simp)
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ U.toBase)).trans_lt hS
  let V : SmallEtale B S hS :=
    ⟨Over.mk (ObjectProperty.homMk (j ≫ U.toBase) : B.obj (Spec R) hR ⟶ B.obj S hS),
      (inferInstance : Etale (j ≫ U.toBase))⟩
  have hstruct : B.inclusion.map V.obj.hom = j ≫ U.toBase := rfl
  have hrange : Set.range U.point.base ⊆ Set.range j.base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default]
    exact hy
  have hfac : IsOpenImmersion.lift j U.point hrange ≫ j = U.point :=
    IsOpenImmersion.lift_fac j U.point hrange
  refine ⟨⟨V, ⟨IsOpenImmersion.lift j U.point hrange, ?_⟩⟩, ⟨homMk j hstruct.symm hfac⟩⟩
  rw [hstruct, ← Category.assoc, hfac, U.point_comp]

/-- The functor from elements of the fibre functor of the bounded site's point to étale
neighbourhoods is initial: colimits over étale neighbourhoods of `s` may be computed on the
bounded small étale site. -/
instance initial_ofGeometricPointSitePointFiberElements :
    (ofGeometricPointSitePointFiberElements B hS s).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (exists_ofGeometricPointSitePointFiberElements_hom B hS s)

end AlgebraicGeometry.GeometricPoint.EtaleNeighborhood

end
