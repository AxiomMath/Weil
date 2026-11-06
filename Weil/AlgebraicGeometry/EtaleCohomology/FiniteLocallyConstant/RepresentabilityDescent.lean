module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.LocallyConstantSheafFka1
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Defs.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.BoundedFibreDescent.GeometricFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteEtaleCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.PointFiber
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackULift

/-!
# Locally constant sheaves with finite stalks are represented by covering spaces

Let `S` be a scheme and `F` a sheaf of sets on the small étale site of `S` which is locally
constant and has finite stalks at all geometric points. Then `F` is represented by a covering
space of `S`: there are a finite étale morphism `Y ⟶ S` and an isomorphism `Ỹ ≅ F` of sheaves
on the small étale site of `S`.

The proof has two steps. First, the values of the local trivializations are finite: if
`F|_U ≅ (M)_U` with `U` nonempty, then `M` is the stalk of `F` at a geometric point of `S`
factoring through `U`, which is finite. So `F` is finite locally constant. Second, a finite
locally constant sheaf of sets is represented by a finite étale `S`-scheme (Stacks, Tag 03RV),
which is a covering space of `S`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_coveringSpace_representedSheaf_iso`: a locally constant
  sheaf of sets with finite stalks on the small étale site of `S` is isomorphic to the sheaf
  represented by a covering space of `S`.
* `AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_of_isLocallyConstant`: a locally
  constant sheaf of sets with finite stalks is finite locally constant.
* `AlgebraicGeometry.SmallEtale.exists_isFinite_representedSheaf_iso`: the same representability
  statement, with the representing object an object of the small étale site whose structure
  morphism is finite.

## Implementation notes

Sheaves of sets take values in `Type u`, the universe of the schemes, so that the represented
sheaf `Ỹ` (whose sections are morphisms of `u`-schemes) is a sheaf of the same kind. The small
étale site of `S` and its localizations are essentially small, so sheafification of presheaves
of `Type u` exists on them and inverts exactly the locally bijective morphisms; these two facts
are recorded as instances below. The representability statement of Stacks, Tag 03RV, is stated
for sheaves in `Type (u + 1)`, and is applied to the universe lift of `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A I][FreitagKiehl]
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The localization of the small étale site at an object has sheafification for presheaves of
sets in the universe of the schemes, the site being essentially small. -/
instance hasSheafify_over_type (U : SmallEtale B S hS) :
    HasSheafify ((topology B S hS).over U) (Type u) :=
  hasSheafifyEssentiallySmallSite _ _

/-- On the localization of the small étale site at an object, the morphisms of presheaves of
sets in the universe of the schemes which sheafification inverts are the locally bijective
ones. -/
instance wEqualsLocallyBijective_over_type (U : SmallEtale B S hS) :
    ((topology B S hS).over U).WEqualsLocallyBijective (Type u) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The geometric point `Stacks.Etale.ofPoint y` of an object `U` of the small étale site, at
a point `y` of `U`, is a lift to `U` of its image in `S`. -/
def geometricPointFiberOfPoint (U : SmallEtale B S hS) (y : (toScheme B S hS).obj U) :
    (geometricPointFiber B S hS
      ((Stacks.Etale.ofPoint y).map (B.inclusion.map U.obj.hom : _ ⟶ S))).obj U :=
  ⟨(Stacks.Etale.ofPoint y).hom, rfl⟩

/-- If a sheaf of sets with finite stalks restricts over a nonempty object `U` of the small
étale site to the constant sheaf on `M`, then `M` is finite: it is the stalk of the sheaf at a
geometric point factoring through `U`. -/
theorem finite_of_constantSheaf_iso_overPullback {F : Sheaf (topology B S hS) (Type u)}
    (hF : HasFiniteStalks F) (U : SmallEtale B S hS) (y : (toScheme B S hS).obj U) (M : Type u)
    (e : (constantSheaf ((topology B S hS).over U) (Type u)).obj M ≅
      ((topology B S hS).overPullback (Type u) U).obj F) :
    Finite M := by
  let s := (Stacks.Etale.ofPoint y).map (B.inclusion.map U.obj.hom : _ ⟶ S)
  have := hF s
  exact Finite.of_equiv _ (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver
    (geometricPointSitePoint B S hS s) (geometricPointFiberOfPoint U y) F M e).toEquiv

/-- **A locally constant sheaf of sets with finite stalks is finite locally constant.** -/
theorem isFiniteLocallyConstant_of_isLocallyConstant {F : Sheaf (topology B S hS) (Type u)}
    (hF : IsLocallyConstant B S hS F) (hfin : HasFiniteStalks F) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (topology B S hS) F := by
  obtain ⟨I, U, hU, hc⟩ := (isLocallyConstant_iff_exists_cover F).mp hF
  refine (isFiniteLocallyConstant_iff_exists_cover F).mpr
    ⟨{i // Nonempty ((toScheme B S hS).obj (U i))}, fun i => U i.1, fun x => ?_, fun i => ?_⟩
  · obtain ⟨i, y, hy⟩ := hU x
    exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩
  · obtain ⟨M, ⟨e⟩⟩ := hc i.1
    exact ⟨M, finite_of_constantSheaf_iso_overPullback hfin _ i.2.some M e, ⟨e⟩⟩

/-- Finite local constancy of a sheaf of sets on the small étale site survives the universe
lift from `Type u` to `Type (u + 1)`. -/
theorem isFiniteLocallyConstant_sheafCompose_uliftFunctor {F : Sheaf (topology B S hS) (Type u)}
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant (topology B S hS) F) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (topology B S hS)
      ((sheafCompose (topology B S hS) uliftFunctor.{u + 1, u}).obj F) := by
  constructor
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := h i
  have : Finite E := hE
  have : ((topology B S hS).over (V i)).PreservesSheafification uliftFunctor.{u + 1, u} :=
    GrothendieckTopology.preservesSheafification_uliftFunctor_of_wEqualsLocallyBijective _
  refine ⟨ULift.{u + 1} E, inferInstance, ⟨?_⟩⟩
  exact ((constantCommuteCompose ((topology B S hS).over (V i))
      uliftFunctor.{u + 1, u}).app E).symm ≪≫
    (sheafCompose ((topology B S hS).over (V i)) uliftFunctor.{u + 1, u}).mapIso e

/-- **A locally constant sheaf of sets with finite stalks is representable by a finite étale
object.** There is an object `Y` of the small étale site of `S` whose structure morphism is
finite, with an isomorphism `Ỹ ≅ F`. -/
theorem exists_isFinite_representedSheaf_iso {F : Sheaf (topology B S hS) (Type u)}
    (hF : IsLocallyConstant B S hS F) (hfin : HasFiniteStalks F) :
    ∃ Y : SmallEtale B S hS, IsFinite (B.inclusion.map Y.obj.hom) ∧
      Nonempty (representedSheaf Y ≅ F) := by
  obtain ⟨Y, hY, ⟨e⟩⟩ :=
    (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable B ⟨S, hS⟩ _).mp
      (isFiniteLocallyConstant_sheafCompose_uliftFunctor
        (isFiniteLocallyConstant_of_isLocallyConstant hF hfin))
  refine ⟨Y, hY, ⟨?_⟩⟩
  have e' : (sheafCompose (topology B S hS) uliftFunctor.{u + 1, u}).obj (representedSheaf Y) ≅
      (sheafCompose (topology B S hS) uliftFunctor.{u + 1, u}).obj F :=
    (Stacks.EtaleCohomology.sheafifiedYonedaIsoUliftYoneda (topology B S hS) Y ≪≫
      Iso.refl _).symm ≪≫ e.symm
  exact ((Functor.FullyFaithful.ofFullyFaithful
    (sheafCompose (topology B S hS) uliftFunctor.{u + 1, u})).preimageIso e')

/-- **A locally constant sheaf with finite stalks is represented by a covering space.** Let `F`
be a sheaf of sets on the small étale site of `S` which is locally constant and has finite
stalks. Then there are a covering space `Y ⟶ S` (a finite étale morphism) and an isomorphism
`Ỹ ≅ F`, where `Ỹ` is the sheaf represented by `Y` read as an object of the small étale site. -/
@[weil "lem_fka1_locally_constant_sheaf_representable_by_covering"]
theorem exists_coveringSpace_representedSheaf_iso {F : Sheaf (topology B S hS) (Type u)}
    (hF : IsLocallyConstant B S hS F) (hfin : HasFiniteStalks F) :
    ∃ Y : S.CoveringSpace,
      Nonempty (representedSheaf (smallEtaleOfFiniteEtale (B := B) (X := ⟨S, hS⟩) Y) ≅ F) := by
  obtain ⟨U, hU, ⟨e⟩⟩ := exists_isFinite_representedSheaf_iso hF hfin
  let X : B.Scheme := ⟨S, hS⟩
  let U' : (finiteSmallEtaleObjects B X).FullSubcategory := ⟨U, hU⟩
  let Y := (finiteEtaleFromSmallEtale B X).obj U'
  refine ⟨Y, ⟨?_⟩⟩
  have i : finiteEtaleSiteObject Y ≅ U' :=
    (finiteEtaleFromSmallEtaleFullyFaithful B X).preimageIso (finiteEtaleFromSmallEtaleObjIso Y)
  exact (smallEtaleYoneda B S hS).mapIso ((ObjectProperty.ι _).mapIso i) ≪≫ e

end AlgebraicGeometry.SmallEtale

end
