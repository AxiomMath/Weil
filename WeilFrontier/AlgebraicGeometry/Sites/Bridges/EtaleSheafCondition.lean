module

public import WeilFrontier.CategoryTheory.Sites.IsSheafFor
public import WeilFrontier.AlgebraicGeometry.Sites.Fpqc
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.RepresentableSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical

/-!
# The sheaf condition on the small étale site and on `Et(S)`

Three forms of the sheaf condition are known for presheaves on the étale site [FK, I.2]: by
covering sieves, by étale coverings and fibre products, and the sheaf property of the presheaf
`h_{X'} : U ↦ Hom_S(U, X')` represented by an `S`-scheme. They are proved on Mathlib's small
étale site `X.Etale` (sieves) and on the category `Et(S)` of noetherian separated étale
`S`-schemes (coverings, representables). Here we read them on the small étale site
`AlgebraicGeometry.SmallEtale B S hS` of [Stacks, Tag 021B], and on `Et(S)` with its
Grothendieck topology `AlgebraicGeometry.SmallNoetherianSeparatedEtale.topology` restricted
from the small étale site, which for `S` locally noetherian is a dense subsite.

## Main results

* `AlgebraicGeometry.Scheme.isSheaf_smallEtale_iff_bijective_toSieveCompatible` and its
  `_addCommGrpCat` version: a presheaf on the small étale site is a sheaf if and only if
  `F(U) → F(R)` is bijective for every covering sieve `R`.
* `AlgebraicGeometry.EtalePresheaf.isEtaleSheaf_iff_bijective_toSieveCompatible`: a presheaf of
  sets on `Et(S)` is an étale sheaf in FK's sense if and only if the same holds for the covering
  sieves of `Et(S)`.
* `AlgebraicGeometry.EtalePresheaf.isSheaf_topology_iff_bijective_toPullbackCompatible`: a
  presheaf of sets on `Et(S)` is a sheaf for the topology of `Et(S)` if and only if the covering
  condition holds for every étale covering.
* `AlgebraicGeometry.EtalePresheaf.bijective_toPullbackCompatible_of_smallEtale` and its
  `_addCommGrpCat` version: the restriction to `Et(S)` of a sheaf on the small étale site satisfies
  the covering condition.
* `AlgebraicGeometry.EtalePresheaf.bijective_toPullbackCompatible_iff_exists_smallEtale`: a
  presheaf of sets on `Et(S)` satisfies the covering condition if and only if it is the
  restriction of a sheaf on the small étale site.
* `AlgebraicGeometry.representablePresheaf.isSheaf_topology`: `h_{X'}` is a sheaf on `Et(S)`.
* `AlgebraicGeometry.SmallEtale.isSheaf_representablePresheaf_obj`: `h_{X'}` is a sheaf on the
  small étale site, for every `S`-scheme `X'`.
* `AlgebraicGeometry.representablePresheaf.sheafEquivFunctorObjIso`: the comparison equivalence
  `Sheaf(Et(S)) ≌ Sheaf(SmallEtale)` sends `h_{X'}` on `Et(S)` to `h_{X'}` on the small étale site.

## Implementation notes

For a sheaf `F` on `Et(S)`, the small étale sheaf corresponding to it is
`(AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv B S hS _).functor.obj F`, and the
inverse of that equivalence is restriction along the inclusion `Et(S) ⥤ SmallEtale`. The comparison
lemma needs limits of size `u` in the category of values, so the characterisation of the covering
condition by restriction takes values in `Type (max u v)`.

Restriction to a dense subsite detects sheaves only among sheaves, so the sheaf property of `h_{X'}`
on the whole small étale site is not a formal consequence of the one on `Et(S)`: it is proved by
descent of morphisms of schemes along étale coverings, as on `Et(S)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace Scheme

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small étale site form of
`AlgebraicGeometry.Scheme.isSheaf_smallEtaleTopology_iff_bijective_toSieveCompatible`. -/
theorem isSheaf_smallEtale_iff_bijective_toSieveCompatible
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS) F ↔ ∀ (U : SmallEtale B S hS) (R : Sieve U),
      R ∈ SmallEtale.topology B S hS U → Function.Bijective (Sieve.toSieveCompatible F R) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_iff_bijective_toSieveCompatible _ F

/-- The small étale site form of
`AlgebraicGeometry.Scheme.isSheaf_smallEtaleTopology_iff_bijective_toSieveCompatible_addCommGrpCat`.
-/
theorem isSheaf_smallEtale_iff_bijective_toSieveCompatible_addCommGrpCat
    (F : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS) F ↔ ∀ (U : SmallEtale B S hS) (R : Sieve U),
      R ∈ SmallEtale.topology B S hS U →
        Function.Bijective
          (Sieve.toSieveCompatible (F ⋙ CategoryTheory.forget AddCommGrpCat) R) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget_addCommGrpCat]
  exact Presieve.isSheaf_iff_bijective_toSieveCompatible _ _

end Scheme

namespace EtalePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsLocallyNoetherian S]

/-- The `Et(S)` form, for FK's étale sheaves, of
`AlgebraicGeometry.Scheme.isSheaf_smallEtaleTopology_iff_bijective_toSieveCompatible`. -/
theorem isEtaleSheaf_iff_bijective_toSieveCompatible (F : EtalePresheaf B S hS (Type v)) :
    IsEtaleSheaf F ↔ ∀ (U : SmallNoetherianSeparatedEtale B S hS) (R : Sieve U),
      R ∈ topology B S hS U → Function.Bijective (Sieve.toSieveCompatible F R) :=
  (isSheaf_iff_isEtaleSheaf B S hS F).symm.trans
    (Presieve.isSheaf_iff_bijective_toSieveCompatible _ F)

/-- The topological form on `Et(S)` of
`AlgebraicGeometry.EtalePresheaf.isEtaleSheaf_iff_bijective_toPullbackCompatible`. -/
theorem isSheaf_topology_iff_bijective_toPullbackCompatible
    (F : EtalePresheaf B S hS (Type v)) :
    Presieve.IsSheaf (topology B S hS) F ↔
      ∀ ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ ⦃ι : Type w⦄
        (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U),
        Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i)) →
          Function.Bijective (Presieve.Arrows.toPullbackCompatible F φ) :=
  (isSheaf_iff_isEtaleSheaf B S hS F).trans
    (isEtaleSheaf_iff_bijective_toPullbackCompatible.{w} F)

/-- The small étale site form of
`AlgebraicGeometry.EtalePresheaf.isEtaleSheaf_iff_bijective_toPullbackCompatible`: the
restriction to `Et(S)` of a sheaf of sets on the small étale site satisfies the covering
condition for every étale covering. -/
theorem bijective_toPullbackCompatible_of_smallEtale
    (G : Sheaf (SmallEtale.topology B S hS) (Type v))
    ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ ⦃ι : Type w⦄
    (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U)
    (hφ : Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i))) :
    Function.Bijective
      (Presieve.Arrows.toPullbackCompatible
        ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ G.obj) φ) :=
  (isSheaf_topology_iff_bijective_toPullbackCompatible _).mp
    ((SmallNoetherianSeparatedEtale.inclusion B S hS).op_comp_isSheaf_of_types
      (topology B S hS) _ G) V φ hφ

/-- The small étale site form of
`AlgebraicGeometry.EtalePresheaf.isEtaleSheaf_forget_iff_bijective_toPullbackCompatible`: the
restriction to `Et(S)` of a sheaf of abelian groups on the small étale site satisfies the covering
condition for every étale covering. -/
theorem bijective_toPullbackCompatible_of_smallEtale_addCommGrpCat
    (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ ⦃ι : Type w⦄
    (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U)
    (hφ : Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i))) :
    Function.Bijective
      (Presieve.Arrows.toPullbackCompatible
        ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ G.obj ⋙
          CategoryTheory.forget AddCommGrpCat) φ) := by
  have hG : Presieve.IsSheaf (SmallEtale.topology B S hS)
      (G.obj ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (Presheaf.isSheaf_iff_isSheaf_forget_addCommGrpCat _ _).mp G.property
  exact (isSheaf_topology_iff_bijective_toPullbackCompatible _).mp
    ((SmallNoetherianSeparatedEtale.inclusion B S hS).op_comp_isSheaf_of_isSheaf_type
      (topology B S hS) hG) V φ hφ

/-- The small étale site form of
`AlgebraicGeometry.EtalePresheaf.isEtaleSheaf_iff_bijective_toPullbackCompatible`: a presheaf of
sets on `Et(S)` satisfies the covering condition for every étale covering if and only if it is
the restriction of a sheaf on the small étale site. -/
theorem bijective_toPullbackCompatible_iff_exists_smallEtale
    (F : EtalePresheaf B S hS (Type (max u v))) :
    (∀ ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ ⦃ι : Type w⦄
        (V : ι → SmallNoetherianSeparatedEtale B S hS) (φ : ∀ i, V i ⟶ U),
        Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (φ i)) →
          Function.Bijective (Presieve.Arrows.toPullbackCompatible F φ)) ↔
      ∃ G : Sheaf (SmallEtale.topology B S hS) (Type (max u v)),
        Nonempty ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ G.obj ≅ F) := by
  rw [← isSheaf_topology_iff_bijective_toPullbackCompatible.{w}]
  constructor
  · intro hF
    have hF' : Presheaf.IsSheaf (topology B S hS) F := (isSheaf_iff_isSheaf_of_type _ _).mpr hF
    let E := sheafEquiv B S hS (Type (max u v))
    let F' : Sheaf (topology B S hS) (Type (max u v)) := ⟨F, hF'⟩
    exact ⟨E.functor.obj F', ⟨(sheafToPresheaf _ _).mapIso (E.unitIso.app F').symm⟩⟩
  · rintro ⟨G, ⟨e⟩⟩
    exact (Presieve.isSheaf_iso (topology B S hS) e
      ((SmallNoetherianSeparatedEtale.inclusion B S hS).op_comp_isSheaf_of_types
        (topology B S hS) _ G))

end EtalePresheaf

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- The small étale site form of `AlgebraicGeometry.representablePresheaf.isSheafFor_ofArrows`:
for every `X`-scheme `Z`, the presheaf `h_Z : U ↦ Hom_X(U, Z)` on the small étale site of `X` is
a sheaf. -/
theorem isSheaf_representablePresheaf_obj (Z : Over X) :
    Presheaf.IsSheaf (topology B X hX) ((representablePresheaf B X hX).obj Z) := by
  rw [isSheaf_iff_isSheaf_of_type]
  have := smallEtale_precoverage_stableUnderBaseChange B X hX
  rw [topology, Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro U R hR x hx
  have hsheaf := isSheafFor_toScheme_op_yoneda B X hX Z.left hR
  have hsep := (isSheafFor_toScheme_op_yoneda B X hX X hR).isSeparatedFor
  have hx' : Presieve.FamilyOfElements.Compatible
      (P := (toScheme B X hX).op ⋙ yoneda.obj Z.left) (R := R)
      (fun _ f hf ↦ (x f hf).left) := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact congrArg CommaMorphism.left (hx g₁ g₂ h₁ h₂ hcomm)
  obtain ⟨t, ht, -⟩ := hsheaf _ hx'
  have htf : ∀ ⦃V : SmallEtale B X hX⦄ (f : V ⟶ U) (hf : R f),
      (toScheme B X hX).map f ≫ t = (x f hf).left := fun _ f hf ↦ ht f hf
  have hover : t ≫ Z.hom = ((toOver B X hX).obj U).hom := by
    refine hsep.ext fun V f hf ↦ ?_
    change (toScheme B X hX).map f ≫ t ≫ Z.hom =
      (toScheme B X hX).map f ≫ B.inclusion.map U.obj.hom
    rw [← Category.assoc, htf f hf]
    exact (Over.w (x f hf)).trans (toScheme_map_comp_hom B X hX f).symm
  refine ⟨Over.homMk t hover, fun V f hf ↦ Over.OverMorphism.ext (htf f hf),
    fun g hg ↦ Over.OverMorphism.ext ?_⟩
  refine hsheaf.isSeparatedFor.ext fun V f hf ↦ ?_
  exact (congrArg CommaMorphism.left (hg f hf)).trans (htf f hf).symm

end SmallEtale

namespace representablePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsLocallyNoetherian S]

/-- The topological form on `Et(S)` of
`AlgebraicGeometry.representablePresheaf.isSheafFor_ofArrows`: `h_{X'}` is a sheaf for the
topology of `Et(S)`. -/
theorem isSheaf_topology (X' : Over S) :
    Presieve.IsSheaf (topology B S hS) (representablePresheaf B S hS X') := by
  rw [topology_eq_toGrothendieck_finiteCoverage, Presieve.isSheaf_coverage]
  rintro U R ⟨ι, _, V, φ, rfl, hφ⟩
  exact isSheafFor_ofArrows X' φ fun x ↦ Set.mem_iUnion.mp (hφ ▸ Set.mem_univ x)

/-- The small étale site form of `AlgebraicGeometry.representablePresheaf.isSheafFor_ofArrows`:
the comparison equivalence `Sheaf(Et(S)) ≌ Sheaf(SmallEtale)` sends the sheaf `h_{X'}` on
`Et(S)` to the sheaf `h_{X'}` on the small étale site. -/
def sheafEquivFunctorObjIso (X' : Over S) :
    (sheafEquiv B S hS (Type u)).functor.obj
        ⟨representablePresheaf B S hS X',
          (isSheaf_iff_isSheaf_of_type _ _).mpr (isSheaf_topology X')⟩ ≅
      ⟨(SmallEtale.representablePresheaf B S hS).obj X',
        SmallEtale.isSheaf_representablePresheaf_obj B S hS X'⟩ :=
  (sheafEquiv B S hS (Type u)).functor.mapIso (Iso.refl _) ≪≫
    (sheafEquiv B S hS (Type u)).counitIso.app
      ⟨(SmallEtale.representablePresheaf B S hS).obj X',
        SmallEtale.isSheaf_representablePresheaf_obj B S hS X'⟩

end representablePresheaf

end AlgebraicGeometry
