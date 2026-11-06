module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.LocalizedGeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Locally constant sheaves on the small étale site

Let `S` be a scheme. A sheaf `F` on the small étale site of `S`, with values in a category `D`
(sets or abelian groups in [FK, I.4]), is *locally constant* if there is an étale covering
`(Uᵢ ⟶ S)ᵢ` such that each restriction `F|Uᵢ` is a constant sheaf.

The notion is `Stacks.ConstantSheaf.IsLocallyConstant` (Stacks 093Q (2)), which asks for a
trivializing covering of *every* object of the site. Since `S` itself is the final object of its
small étale site, and a trivialization over an object restricts to one over every object above
it, a single trivializing covering of `S` suffices. This file proves that, in the form of
[FK, I.4]: a finite family of étale morphisms which is jointly surjective onto `S`.

## Main results

* `AlgebraicGeometry.SmallEtale.isLocallyConstant_of_isEtaleCovering`: a sheaf whose
  restrictions to the members of an étale covering of `S` are constant is locally constant.
* `AlgebraicGeometry.SmallEtale.isLocallyConstant_iff_exists_isEtaleCovering`: over a
  quasi-compact scheme `S`, a sheaf is locally constant if and only if it becomes constant on the
  members of one (finite) étale covering of `S`.

## Implementation notes

The small étale site is `AlgebraicGeometry.SmallEtale B S hS`, whose objects are schemes étale
over `S` in a size-bounded big étale site `B`; the members of a covering are therefore objects of
the site, and the covering condition is stated on their structure morphisms to `S`. The
restriction of a sheaf to an object `U` of the site is the pullback to the localized site
`S_et / U`, `GrothendieckTopology.overPullback`, and constancy is Mathlib's
`CategoryTheory.Sheaf.IsConstant`. The coefficient category is arbitrary.

An étale covering in [FK, I.2] is finite, so the converse direction needs `S` quasi-compact,
which holds for the noetherian schemes of [FK]. Without quasi-compactness the
trivializing coverings given by the definition need not have a finite subcovering.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public section

universe w v' u' u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : Type u'} [Category.{v'} D] [∀ U, HasWeakSheafify ((topology B S hS).over U) D]

/-- The structure morphism to `S` of an object of the small étale site is the underlying
morphism of schemes of the unique map to the final object. -/
lemma inclusion_map_finalIsTerminal_from (U : SmallEtale B S hS) :
    B.inclusion.map ((finalIsTerminal B S hS).from U).hom.left = B.inclusion.map U.obj.hom := by
  have := Over.w ((finalIsTerminal B S hS).from U).hom
  exact congrArg B.inclusion.map (by simpa [final] using this)

/-- **A single étale covering of `S` suffices for local constancy.** If the restrictions of `F`
to the members of an étale covering of `S` are constant, then `F` is locally constant. -/
theorem isLocallyConstant_of_isEtaleCovering {ι : Type w} (U : ι → SmallEtale B S hS)
    (hU : Scheme.IsEtaleCovering fun i ↦ B.inclusion.map (U i).obj.hom)
    (F : Sheaf (topology B S hS) D)
    (hc : ∀ i, Sheaf.IsConstant ((topology B S hS).over (U i))
      (((topology B S hS).overPullback D (U i)).obj F)) :
    Stacks.ConstantSheaf.IsLocallyConstant (topology B S hS) F := by
  refine Stacks.ConstantSheaf.Localization.isLocallyConstant_of_isConstant_cover _ D
    (finalIsTerminal B S hS) F (f := fun i ↦ (finalIsTerminal B S hS).from (U i)) ?_ hc
  refine generate_ofArrows_mem_topology_of_jointlySurjective B S hS U _ fun x ↦ ?_
  obtain ⟨i, hi⟩ := hU.exists_mem_range x
  exact ⟨i, by rwa [inclusion_map_finalIsTerminal_from]⟩

/-- **[FK, I.4] Locally constant sheaves.** Over a quasi-compact scheme `S`, a sheaf on the small
étale site of `S` is locally constant (Stacks 093Q (2)) if and only if there is an étale covering
`(Uᵢ ⟶ S)ᵢ` (finite and jointly surjective) such that every restriction `F|Uᵢ` is constant. -/
@[weil "def_fk104_locally_constant_sheaf"]
theorem isLocallyConstant_iff_exists_isEtaleCovering [CompactSpace S]
    (F : Sheaf (topology B S hS) D) :
    Stacks.ConstantSheaf.IsLocallyConstant (topology B S hS) F ↔
      ∃ (ι : Type u) (U : ι → SmallEtale B S hS),
        Scheme.IsEtaleCovering (fun i ↦ B.inclusion.map (U i).obj.hom) ∧
        ∀ i, Sheaf.IsConstant ((topology B S hS).over (U i))
          (((topology B S hS).overPullback D (U i)).obj F) := by
  refine ⟨fun h ↦ ?_, fun ⟨ι, U, hU, hc⟩ ↦ isLocallyConstant_of_isEtaleCovering U hU F hc⟩
  obtain ⟨I, X, f, hf, hc⟩ := h.exists_cover (final B S hS)
  choose W g hg hx using fun x : S ↦ exists_mem_arrows_mem_range B S hS hf x
  have hrange : ∀ x, Set.range ((toScheme B S hS).map (g x)) =
      Set.range (B.inclusion.map (W x).obj.hom) := fun x ↦ by
    rw [(finalIsTerminal B S hS).hom_ext (g x) ((finalIsTerminal B S hS).from (W x))]
    exact congrArg (fun φ : _ ⟶ S ↦ Set.range φ) (inclusion_map_finalIsTerminal_from (W x))
  have hopen : ∀ x, IsOpen (Set.range ((toScheme B S hS).map (g x))) := fun x ↦ by
    rw [hrange x]
    exact (B.inclusion.map (W x).obj.hom).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := (isCompact_univ (X := S)).elim_finite_subcover
    (fun x ↦ Set.range ((toScheme B S hS).map (g x))) hopen
    fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨t, fun x : t ↦ W x.1, ⟨inferInstance, fun x ↦ inferInstance, ?_⟩, fun x ↦ ?_⟩
  · refine Scheme.iUnion_range_eq_univ_iff.2 fun x ↦ ?_
    obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨⟨y, hyt⟩, hrange y ▸ hy⟩
  · obtain ⟨i, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp (hg x.1)
    have := hc i
    exact Stacks.ConstantSheaf.Localization.isConstant_over_of_isConstant_over _ D h F

end AlgebraicGeometry.SmallEtale
