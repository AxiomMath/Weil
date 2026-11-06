module

public import WeilFrontier.AlgebraicGeometry.Sites.EtaleComparison
public import WeilFrontier.AlgebraicGeometry.Sites.SheafificationKernelLocallyZero
public import WeilFrontier.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves

/-!
# Abelian sheaves on the bounded small étale site

Let `B` be a big étale site containing a scheme `S`, and let `SmallEtale B S hS` be the bounded
small étale site of `S`. This file states, on that site, three facts on abelian sheaves and
presheaves of [FK, I.2] which are proved on Mathlib's small étale site `S.Etale`:

* a section of an abelian presheaf killed by sheafification vanishes on the members of a finite
  étale covering, when its domain is quasi-compact;
* every abelian sheaf embeds into an injective abelian sheaf;
* a colimit of a filtered diagram of short exact sequences of abelian sheaves is short exact.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isEtaleCovering_map_eq_zero_of_toSheafify_app_eq_zero`
* `AlgebraicGeometry.SmallEtale.exists_mono_injective_sheaf`
* `AlgebraicGeometry.SmallEtale.shortExact_of_isColimit_sheaf`

## Implementation notes

The coefficients are `AddCommGrpCat.{w}` for any universe `w` with `UnivLE.{u, w}`, as on
Mathlib's site. For `w = u` the category of abelian sheaves on `SmallEtale B S hS` is
Grothendieck abelian (`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf`), which gives
the second and third statements directly; for general `w` they are transported along the
equivalence of sheaf categories `AlgebraicGeometry.SmallEtale.sheafEquiv`, an equivalence
preserving injective objects, monomorphisms, colimits and short exact sequences.

The first statement concerns presheaves, which the equivalence of sheaf categories does not
move; it follows from the general
`CategoryTheory.Presheaf.equalizerSieve_zero_mem_of_toSheafify_app_eq_zero` together with the
description of covering sieves of the bounded site as the sieves jointly surjective on points
(`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`), and the openness of étale
morphisms, which makes the covering finite over a quasi-compact object.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §2.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe t' t w u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section SheafificationKernel

variable [HasWeakSheafify (topology B S hS) AddCommGrpCat.{w}]
  [(topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Transport of
`AlgebraicGeometry.Scheme.exists_isEtaleCovering_map_eq_zero_of_toSheafify_app_eq_zero` to the
bounded small étale site: a section over a quasi-compact object killed by sheafification
vanishes on the members of a finite étale covering. -/
theorem exists_isEtaleCovering_map_eq_zero_of_toSheafify_app_eq_zero
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{w}) {U : SmallEtale B S hS}
    [CompactSpace ((toScheme B S hS).obj U)] {s : P.obj (op U)}
    (hs : (toSheafify (topology B S hS) P).app (op U) s = 0) :
    ∃ (K : Type u) (W : K → SmallEtale B S hS) (ψ : ∀ k, W k ⟶ U),
      Scheme.IsEtaleCovering (fun k ↦ (toScheme B S hS).map (ψ k)) ∧
        ∀ k, P.map (ψ k).op s = 0 := by
  have hR := Presheaf.equalizerSieve_zero_mem_of_toSheafify_app_eq_zero P hs
  choose W g hg hx using fun x ↦ exists_mem_arrows_mem_range B S hS hR x
  have hopen : ∀ x, IsOpen (Set.range ((toScheme B S hS).map (g x))) := fun x ↦
    ((toScheme B S hS).map (g x)).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen
    fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨t, fun k ↦ W k.1, fun k ↦ g k.1, ⟨inferInstance, fun k ↦ inferInstance, ?_⟩,
    fun k ↦ ?_⟩
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hxt, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨⟨x, hxt⟩, hy⟩
  · have := hg k.1
    rw [Presheaf.equalizerSieve_apply, map_zero] at this
    exact this

end SheafificationKernel

section Sheaves

variable [UnivLE.{u, w}]

/-- Transport of `AlgebraicGeometry.Scheme.exists_mono_injective_sheaf_smallEtaleTopology` to the
bounded small étale site: every abelian sheaf admits a monomorphism into an injective abelian
sheaf. -/
theorem exists_mono_injective_sheaf (F : Sheaf (topology B S hS) AddCommGrpCat.{w}) :
    ∃ (I : Sheaf (topology B S hS) AddCommGrpCat.{w}) (f : F ⟶ I), Injective I ∧ Mono f := by
  let E := sheafEquiv B S hS AddCommGrpCat.{w}
  obtain ⟨I, f, hI, hf⟩ := Scheme.exists_mono_injective_sheaf_smallEtaleTopology S (E.functor.obj F)
  exact ⟨E.inverse.obj I, E.unit.app F ≫ E.inverse.map f, (E.symm.map_injective_iff I).2 hI,
    mono_comp _ _⟩

variable {J : Type t} [Category.{t'} J] [IsFiltered J] [EssentiallySmall.{w} J]

/-- Transport of `AlgebraicGeometry.Scheme.shortExact_of_isColimit_sheaf_smallEtaleTopology` to
the bounded small étale site: a colimit of a filtered diagram of short exact sequences of abelian
sheaves is short exact. -/
theorem shortExact_of_isColimit_sheaf
    {F : J ⥤ ShortComplex (Sheaf (topology B S hS) AddCommGrpCat.{w})}
    (hF : ∀ j, (F.obj j).ShortExact) {c : Cocone F} (hc : IsColimit c) :
    c.pt.ShortExact := by
  let E := sheafEquiv B S hS AddCommGrpCat.{w}
  have := hasColimitsOfShape_of_essentiallySmall.{w} J
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{w})
  have := Adjunction.hasColimitsOfShape_of_equivalence (J := J) E.functor
  have h := Scheme.shortExact_of_isColimit_sheaf_smallEtaleTopology S
    (F := F ⋙ E.functor.mapShortComplex) (fun j ↦ (hF j).map_of_exact E.functor)
    (ShortComplex.isColimitOfIsColimitπ (E.functor.mapShortComplex.mapCocone c)
      (isColimitOfPreserves E.functor (isColimitOfPreserves ShortComplex.π₁ hc))
      (isColimitOfPreserves E.functor (isColimitOfPreserves ShortComplex.π₂ hc))
      (isColimitOfPreserves E.functor (isColimitOfPreserves ShortComplex.π₃ hc)))
  exact ShortComplex.shortExact_of_iso (c.pt.mapNatIso E.unitIso.symm)
    (h.map_of_exact E.inverse)

end Sheaves

end AlgebraicGeometry.SmallEtale

end
