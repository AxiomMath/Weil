module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.AffineTransitionLimit
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.Constructible
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageConstructibleSetSheafDescent

/-!
# Constructible sheaves on a projective limit come from a finite level

Let `X = lim X_α` be a projective system of schemes with limit, indexed by a directed set. Every
constructible sheaf of sets `F` on the small étale site of `X` is, up to isomorphism, the inverse
image `p_α^* F_α` of a constructible sheaf of sets `F_α` on the small étale site of some `X_α`,
where `p_α : X ⟶ X_α` is the projection.

## Main results

* `AlgebraicGeometry.IsProjectiveSystemWithLimit.exists_isConstructibleSetSheaf_inverseImage_iso`:
  a constructible sheaf of sets on the limit of a projective system of schemes with limit is the
  inverse image of a constructible sheaf of sets on some stage.

## Implementation notes

The schemes of the system live in a big étale site `B`, and sheaves are sheaves on the small
étale sites `SmallEtale.topology B X`. The index set is a preorder `I`, the system being a functor
`Iᵒᵖ ⥤ B.Scheme`: a morphism `α ⟶ β` of `Iᵒᵖ` is a relation `β ≤ α`. That the index set is
nonempty and directed is part of the definition of a projective system with limit (cofilteredness
of `Iᵒᵖ`).

The proof is the general statement for a directed system of quasi-compact quasi-separated schemes
with affine transition morphisms ([Stacks, Tag 09YU], clause (1)): a noetherian scheme is
quasi-compact and quasi-separated, and the cone of a projective system with limit is a limit cone.
The argument there presents the sheaf as a coequalizer of a parallel pair of maps of sheaves
represented by quasi-compact quasi-separated étale schemes (Tag 09Y9), descends the pair of étale
schemes and the two morphisms to a stage (Tags 01ZM, 07RP, 01ZC), and takes the coequalizer
there; this is the argument of [FK] with the representation of a constructible sheaf by an
equivalence relation replaced by a coequalizer presentation.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09YU](https://stacks.math.columbia.edu/tag/09YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme)
  (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Constructible sheaves descend to a finite level.** Let `X = lim X_α` be a projective system
of schemes with limit, indexed by a directed set, and `F` a constructible sheaf of sets on the
small étale site of `X`. There are an index `α` and a constructible sheaf of sets `F_α` on the
small étale site of `X_α` with `p_α^* F_α ≅ F`, where `p_α : X ⟶ X_α` is the projection. -/
@[weil "prop_fk104_constructible_sheaf_descends_to_finite_level"]
theorem IsProjectiveSystemWithLimit.exists_isConstructibleSetSheaf_inverseImage_iso
    (hD : IsProjectiveSystemWithLimit (Dg ⋙ B.inclusion) c)
    (F : Sheaf (SmallEtale.topology B c.pt hX) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B (B.obj c.pt hX) F) :
    ∃ (α : I) (Fα : Sheaf (SmallEtale.topology B (Dg.obj (op α)).obj (Dg.obj (op α)).property)
        (Type (u + 1))),
      IsConstructibleSetSheaf B (Dg.obj (op α)) Fα ∧
        Nonempty ((smallEtaleInverseImage B
          (ObjectProperty.homMk (c.π.app (op α)) : B.obj c.pt hX ⟶ Dg.obj (op α))
          (Type (u + 1))).obj Fα ≅ F) := by
  have := hD.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  have : Nonempty I := IsFiltered.nonempty
  have : IsDirectedOrder I := IsFiltered.isDirectedOrder I
  obtain ⟨hc⟩ := hD.nonempty_isLimit
  have hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  have hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj := fun p =>
    have : IsNoetherian (Dg.obj (op p)).obj := hD.isNoetherian_obj (op p); inferInstance
  have : ∀ (S T : B.Scheme) (f : T ⟶ S),
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := fun _ _ f =>
    (smallEtaleInverseImageAdjunction B f (Type (u + 1))).isRightAdjoint
  exact smallEtaleStagesEssSurj_isConstructibleSetSheaf B Dg c hX hc
    (fun e => hD.isAffineHom_map e) hqc hqs F hF

end AlgebraicGeometry

end
