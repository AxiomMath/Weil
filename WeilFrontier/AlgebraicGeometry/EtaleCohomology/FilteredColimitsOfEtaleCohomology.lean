module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived
public import WeilFrontier.CategoryTheory.Sites.GlobalSections
public import Weil.Attr

/-!
# Étale cohomology commutes with filtered colimits

Let `S` be a quasi-compact and quasi-separated scheme (for instance a noetherian separated
scheme), and let `(F_ν)_{ν ∈ I}` be a filtered system of abelian sheaves on the small étale site
of `S`, with colimit `F` and coprojections `ι_ν : F_ν ⟶ F`. Then for every `i ≥ 0` the maps
`H^i(S, ι_ν)` induce an isomorphism `colim_ν H^i(S, F_ν) ≅ H^i(S, F)`.

Here `H^i(S, -)` is the `i`-th right derived functor of the global sections functor
`F ↦ F(S)`, computed from injective resolutions in the category of abelian sheaves.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_colimit_post_rightDerived_globalSections`: for an abelian
  sheaf system on the small étale site `SmallEtale B S hS` of a quasi-compact quasi-separated
  scheme, the canonical map `colim_ν H^i(S, F_ν) ⟶ H^i(S, colim_ν F_ν)` is an isomorphism.
* `AlgebraicGeometry.SmallEtale.globalSectionsIsoSheafEquivFunctorComp`: global sections on
  `SmallEtale B S hS` are global sections on Mathlib's small étale site of `S` after the
  equivalence of sheaf categories `AlgebraicGeometry.SmallEtale.sheafEquiv`.

## Implementation notes

The statement on Mathlib's small étale site `S.smallEtaleTopology` is
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale` (Stacks 03Q5), whose
proof goes through the Čech-type argument of Stacks 0739 rather than through a colimit of
injective resolutions. It is transported to `SmallEtale B S hS` along the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv`: global sections on `SmallEtale B S hS`, which are
sections over the final object `S ⟶ S`, are sections over its image in `S.Etale`, the right
derived functors of the two section functors correspond under the equivalence, and the
equivalence preserves colimits.

The source assumes `S` noetherian and separated; only quasi-compactness and quasi-separatedness
are used, and both follow from noetherianity. Coefficients are `AddCommGrpCat.{max (u + 1) v}`,
the first universe in which sheafification on the small étale site of `S : Scheme.{u}` is
available from the general theory.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian sheaves on the small étale site `SmallEtale B S hS`, with coefficients in
`AddCommGrpCat.{max (u + 1) v}`, have enough injectives: they are equivalent to abelian sheaves
on Mathlib's small étale site of `S`, which form a Grothendieck abelian category. -/
instance enoughInjectives_sheaf_addCommGrpCat :
    EnoughInjectives (Sheaf (topology B S hS) AddCommGrpCat.{max (u + 1) v}) :=
  EnoughInjectives.of_equivalence (sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).functor

/-- Abelian sheaves on `SmallEtale B S hS` with coefficients in `AddCommGrpCat.{u + 1}` have
enough injectives. This is the case `v = 0` of `enoughInjectives_sheaf_addCommGrpCat`, stated
separately because instance search does not solve `u + 1 = max (u + 1) ?v`. -/
instance enoughInjectives_sheaf_addCommGrpCat_objectUniverse :
    EnoughInjectives (Sheaf (topology B S hS) AddCommGrpCat.{u + 1}) :=
  enoughInjectives_sheaf_addCommGrpCat.{0} B S hS

/-- The inverse of `sheafEquiv`, restriction of sheaves along `toEtaleSite`, is additive. -/
instance additive_sheafEquiv_inverse_addCommGrpCat :
    (sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).inverse.Additive where
  map_add := rfl

/-- The functor of `sheafEquiv` is additive, being an equivalence with additive inverse. -/
instance additive_sheafEquiv_functor_addCommGrpCat :
    (sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).functor.Additive :=
  haveI : (sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).symm.functor.Additive :=
    additive_sheafEquiv_inverse_addCommGrpCat.{v} B S hS
  Equivalence.inverse_additive (sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).symm

/-- Global sections on `SmallEtale B S hS` are sections over the image of the final object in
Mathlib's small étale site, after the equivalence of sheaf categories `sheafEquiv`. -/
noncomputable def globalSectionsIsoSheafEquivFunctorComp :
    globalSections.{max (u + 1) v} B S hS ⋙ 𝟭 _ ≅
      (sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).functor ⋙
        (sheafSections S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
          (op ((toEtaleSite B S hS).obj (final B S hS))) :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}).unitIso _ ≪≫
      Functor.associator _ _ _

/-- The image in `S.Etale` of the final object of `SmallEtale B S hS` is quasi-compact and
separated over `S`: its structure morphism is the identity of `S`. -/
theorem toEtaleSite_obj_final_mem_qcSeparatedOver :
    (toEtaleSite B S hS).obj (final B S hS) ∈ Stacks.EtaleCohomology.qcSeparatedOver S :=
  Stacks.EtaleCohomology.etaleMkId_mem_qcSeparatedOver S

/-- **Étale cohomology commutes with filtered colimits** (FK I.4). Let `S` be a quasi-compact
and quasi-separated scheme, for instance a noetherian separated one, and `F` a filtered system
of abelian sheaves on the small étale site of `S`. For every `i`, the canonical map
`colim_ν H^i(S, F_ν) ⟶ H^i(S, colim_ν F_ν)`, whose `ν`-th component is `H^i(S, ι_ν)` for the
coprojection `ι_ν`, is an isomorphism. Here `H^i(S, -)` is the `i`-th right derived functor of
the global sections functor. -/
@[weil "prop_fk104_cohomology_commutes_filtered_colimits"]
theorem isIso_colimit_post_rightDerived_globalSections [CompactSpace S] [QuasiSeparatedSpace S]
    (i : ℕ) {I : Type (max (u + 1) v)} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ Sheaf (topology B S hS) AddCommGrpCat.{max (u + 1) v}) :
    IsIso (colimit.post F ((globalSections.{max (u + 1) v} B S hS).rightDerived i)) := by
  set E := sheafEquiv B S hS AddCommGrpCat.{max (u + 1) v}
  set G' := (sheafSections S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (op ((toEtaleSite B S hS).obj (final B S hS)))
  have sq := Functor.rightDerivedIsoOfSquare E.functor (globalSections.{max (u + 1) v} B S hS)
    G' (𝟭 _) (globalSectionsIsoSheafEquivFunctorComp.{v} B S hS) i
  have h₁ : IsIso (colimit.post (F ⋙ E.functor) (G'.rightDerived i)) :=
    Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_sheafSections_smallEtale.{v} i _
      (toEtaleSite_obj_final_mem_qcSeparatedOver B S hS) (F ⋙ E.functor)
  have h₂ : IsIso (colimit.post F (E.functor ⋙ G'.rightDerived i)) := by
    rw [← colimit.post_post]
    infer_instance
  exact Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _
    (sq.symm ≪≫ Functor.rightUnitor _)

end AlgebraicGeometry.SmallEtale
