module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.FiniteLocallyConstantUlift

/-!
# An abelian sheaf represented by a covering space is locally constant

Let `Y ⟶ S` be a covering space, i.e. a finite étale morphism, and let `𝒢` be a sheaf of
abelian groups on the small étale site of `S` whose underlying sheaf of sets is the sheaf `Ỹ`
represented by `Y`. Then `𝒢` is locally constant as a sheaf of abelian groups; in fact it is
finite locally constant.

The underlying sheaf of sets `Ỹ` is finite locally constant: over the members of an étale
covering of `S` which splits `Y` into finitely many sheets, it is the constant sheaf on the set
of sheets. An abelian sheaf whose underlying sheaf of sets is finite locally constant is itself
finite locally constant: refining the covering, the image of the finite set of sheets becomes a
subgroup of the sections.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_of_forget_iso_representedSheaf`: an
  abelian sheaf whose underlying sheaf of sets is represented by an object of the small étale
  site with finite structure morphism is finite locally constant.
* `AlgebraicGeometry.SmallEtale.isLocallyConstant_of_forget_iso_representedSheaf_coveringSpace`:
  an abelian sheaf whose underlying sheaf of sets is represented by a covering space of `S` is
  locally constant.

## Implementation notes

Sheaves of sets and of abelian groups take values in the universe `u` of the schemes, so that
the represented sheaf `Ỹ` is a sheaf of the same kind. The two results of Stacks used here
(Tag 03RV, the direction without descent, and the comparison of an abelian sheaf with its
underlying sheaf of sets) are stated for values in the universe `u + 1`; they are applied to
the universe lift of `𝒢`, and the trivializations are brought back to the universe `u` since
the values are finite. Lifting the universe of abelian groups commutes with sheafification on
the localizations of the small étale site, these being essentially small sites on which the
sheafification isomorphisms are the locally bijective morphisms.

The statement of the source asks for a covering space `Y` of a noetherian scheme; the proof
uses neither the noetherian hypothesis nor the connected components of the members of the
covering.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The localization of the small étale site at an object has sheafification for presheaves of
abelian groups in the universe of the schemes, the site being essentially small. -/
instance hasSheafify_over_addCommGrpCat (U : SmallEtale B S hS) :
    HasSheafify ((topology B S hS).over U) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the localization of the small étale site at an object, the morphisms of presheaves of
abelian groups in the universe of the schemes which sheafification inverts are the locally
bijective ones. -/
instance wEqualsLocallyBijective_over_addCommGrpCat (U : SmallEtale B S hS) :
    ((topology B S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end AlgebraicGeometry.SmallEtale

namespace CategoryTheory

namespace Presheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)

/-- Lifting the universe of a locally injective morphism of presheaves of abelian groups keeps
it locally injective. -/
lemma isLocallyInjective_whiskerRight_addCommGrpCatUliftFunctor [IsLocallyInjective J f] :
    IsLocallyInjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1, u}) where
  equalizerSieve_mem {X} x y h := by
    have h' : f.app X x.down = f.app X y.down := congrArg ULift.down h
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J f x.down y.down h')
    intro Z g hg
    exact congrArg ULift.up hg

/-- Lifting the universe of a locally surjective morphism of presheaves of abelian groups keeps
it locally surjective. -/
lemma isLocallySurjective_whiskerRight_addCommGrpCatUliftFunctor [IsLocallySurjective J f] :
    IsLocallySurjective J (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1, u}) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J f s.down)
    rintro Z g ⟨t, ht⟩
    exact ⟨ULift.up t, congrArg ULift.up ht⟩

end Presheaf

/-- When the sheafification isomorphisms of presheaves of abelian groups are the locally
bijective morphisms in both universes, lifting the universe preserves sheafification. -/
lemma GrothendieckTopology.preservesSheafification_addCommGrpCatUliftFunctor
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} where
  le P Q f hf := by
    rw [J.W_iff_isLocallyBijective] at hf
    obtain ⟨_, _⟩ := hf
    have := Presheaf.isLocallyInjective_whiskerRight_addCommGrpCatUliftFunctor J f
    have := Presheaf.isLocallySurjective_whiskerRight_addCommGrpCatUliftFunctor J f
    exact J.W_of_isLocallyBijective (Functor.whiskerRight f AddCommGrpCat.uliftFunctor.{u + 1, u})

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying sheaf of sets of the universe lift of an abelian sheaf whose underlying sheaf
of sets is `Ũ` is the sheaf represented by `U` in the universe `u + 1`. -/
def forgetUliftIsoSheafifiedYoneda {U : SmallEtale B S hS}
    (G : Sheaf (topology B S hS) AddCommGrpCat.{u})
    (e : (sheafCompose (topology B S hS) (forget AddCommGrpCat.{u})).obj G ≅ representedSheaf U) :
    (sheafCompose (topology B S hS) (forget AddCommGrpCat.{u + 1})).obj
        ((sheafCompose (topology B S hS) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj G) ≅
      (Sheaf.sheafifiedYoneda (topology B S hS)).obj U := by
  refine ?_ ≪≫ (Stacks.EtaleCohomology.sheafifiedYonedaIsoUliftYoneda (topology B S hS) U).symm
  refine (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents (fun X => ?_) ?_)
  · exact (Equiv.ulift.trans (((sheafToPresheaf _ _).mapIso e).app X).toEquiv |>.trans
      Equiv.ulift.symm).toIso
  · intro X Y g
    ext x
    exact congrArg ULift.up (NatTrans.naturality_apply e.hom.hom g x.down)

/-- On the localizations of the small étale site, lifting the universe of abelian groups from
`u` to `u + 1` preserves sheafification. -/
instance preservesSheafification_over_addCommGrpCatUliftFunctor (V : SmallEtale B S hS) :
    ((topology B S hS).over V).PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  GrothendieckTopology.preservesSheafification_addCommGrpCatUliftFunctor _

/-- **An abelian sheaf represented by a finite étale object is finite locally constant.** Let
`U` be an object of the small étale site of `S` whose structure morphism is finite, and `𝒢` a
sheaf of abelian groups on the small étale site whose underlying sheaf of sets is the sheaf `Ũ`
represented by `U`. Then `𝒢` is finite locally constant. -/
theorem isFiniteLocallyConstant_of_forget_iso_representedSheaf {U : SmallEtale B S hS}
    (hU : IsFinite (B.inclusion.map U.obj.hom)) (G : Sheaf (topology B S hS) AddCommGrpCat.{u})
    (e : (sheafCompose (topology B S hS) (forget AddCommGrpCat.{u})).obj G ≅ representedSheaf U) :
    IsFiniteLocallyConstant B S hS G := by
  refine Stacks.ConstantSheaf.isFiniteLocallyConstant_of_sheafCompose_uliftFunctor.{u, u + 1} _ G
    (Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget (topology B S hS) _ ?_)
  exact Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable B ⟨S, hS⟩ _
    ⟨U, hU, ⟨forgetUliftIsoSheafifiedYoneda G e⟩⟩

/-- **An abelian sheaf represented by a covering space is locally constant.** Let `Y ⟶ S` be a
covering space and `𝒢` a sheaf of abelian groups on the small étale site of `S` whose underlying
sheaf of sets is the sheaf `Ỹ` represented by `Y`. Then `𝒢` is locally constant as a sheaf of
abelian groups. -/
@[weil "lem_fka1_abelian_represented_sheaf_locally_constant"]
theorem isLocallyConstant_of_forget_iso_representedSheaf_coveringSpace (Y : S.CoveringSpace)
    (G : Sheaf (topology B S hS) AddCommGrpCat.{u})
    (e : (sheafCompose (topology B S hS) (forget AddCommGrpCat.{u})).obj G ≅
      representedSheaf (smallEtaleOfFiniteEtale (B := B) (X := ⟨S, hS⟩) Y)) :
    IsLocallyConstant B S hS G :=
  (isFiniteLocallyConstant_of_forget_iso_representedSheaf
    (finiteEtaleSiteObject (B := B) (X := ⟨S, hS⟩) Y).2 G e).isLocallyConstant

end AlgebraicGeometry.SmallEtale

end
