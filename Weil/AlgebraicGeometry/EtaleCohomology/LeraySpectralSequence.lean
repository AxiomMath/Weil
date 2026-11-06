module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
public import Weil.AlgebraicGeometry.EtaleCohomology.PushforwardAcyclic.Injectivity
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Attr

/-!
# The Leray spectral sequence for a composite of direct images

Let `B` be a big étale site, `f : X ⟶ Y` and `g : Y ⟶ Z` morphisms of it, and `F` an abelian
sheaf on the small étale site of `X`. There is a cohomological spectral sequence of abelian
sheaves on the small étale site of `Z`

```
E₂^{p,q} = R^p g_* (R^q f_* F)  ⟹  R^{p+q} (g ∘ f)_* F.
```

It is the Grothendieck spectral sequence of the composite `g_* ∘ f_*` of the direct images,
which is the direct image `(g ∘ f)_*`. The hypotheses of the Grothendieck spectral sequence
hold: the sheaf categories are Grothendieck abelian, hence have enough injectives; the direct
images are additive; and `f_*` carries injective sheaves to injective sheaves, which are
acyclic for `g_*`.

## Main results

* `AlgebraicGeometry.BigEtaleSite.exists_abutsTo_leraySpectralSequence_comp`: **the Leray
  spectral sequence** `R^p g_* (R^q f_* F) ⟹ R^{p+q} (g ∘ f)_* F`, with its second page in
  terms of the higher direct images `AlgebraicGeometry.BigEtaleSite.higherDirectImage`, its
  vanishing outside the first quadrant, and its abutment.

## Implementation notes

The spectral sequence is a `CohomologicalSpectralSequence` indexed by `ℤ × ℤ`, and convergence
is `CategoryTheory.SpectralSequence.AbutsTo`: each term of the abutment carries a finite
decreasing filtration whose graded pieces are the terms `E_∞^{p,n-p}`. The abutment family is
the `ℤ`-indexed right derived functor `CategoryTheory.Functor.rightDerivedPlus` of `(g ∘ f)_*`,
which vanishes in negative degrees and agrees with `higherDirectImage.{u + 1} B (f ≫ g) n` in degree
`n ≥ 0`; both facts are part of the statement.

The coefficients are `AddCommGrpCat.{u + 1}` for the universe `u` of the schemes of `B`: this
is the universe in which the sheaf categories are Grothendieck abelian and in which the direct
image is known to preserve injectives. The identification `g_* ∘ f_* ≅ (g ∘ f)_*` is
`AlgebraicGeometry.smallEtaleSheafPushforwardCompIso`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.2
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 03QC](https://stacks.math.columbia.edu/tag/03QC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf_succ
-- At the default priority the search for the right derived functors below times out.
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The Leray spectral sequence** for morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of a big étale
site and an abelian sheaf `F` on the small étale site of `X`: there is a cohomological spectral
sequence `E` of abelian sheaves on the small étale site of `Z` with

* second page `E₂^{p,q} ≅ R^p g_* (R^q f_* F)` for `p, q ≥ 0`, the `R^i` being the higher
  direct images `higherDirectImage`, and `E₂^{p,q} = 0` when `p < 0` or `q < 0`;
* abutment `n ↦ R^n (g ∘ f)_* F`, the `ℤ`-indexed right derived functor of the direct image
  along `f ≫ g`, which is `higherDirectImage.{u + 1} B (f ≫ g) n` in degree `n ≥ 0`. -/
@[weil "thm_fk102_leray_spectral_sequence"]
theorem exists_abutsTo_leraySpectralSequence_comp
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) :
    ∃ E : CohomologicalSpectralSequence
        (Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1}) 0,
      (∀ p q : ℕ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
        (higherDirectImage.{u + 1} B g p).obj ((higherDirectImage.{u + 1} B f q).obj F))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 zero_le_two).X (p, q))) ∧
      SpectralSequence.AbutsTo E (fun n =>
        ((B.smallPushforward (f ≫ g) AddCommGrpCat.{u + 1}).rightDerivedPlus n).obj F) ∧
      (∀ n : ℕ, Nonempty
        (((B.smallPushforward (f ≫ g) AddCommGrpCat.{u + 1}).rightDerivedPlus n).obj F ≅
          (higherDirectImage.{u + 1} B (f ≫ g) n).obj F)) := by
  obtain ⟨K, hrest⟩ := Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp
    (B.smallPushforward f AddCommGrpCat.{u + 1}) (B.smallPushforward g AddCommGrpCat.{u + 1})
    (fun I hI => by
      have := hI
      have := injective_smallPushforward_obj B f I
      exact Functor.rightAcyclic_of_injective _ _)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  obtain ⟨E, -, hE₂, habuts⟩ :=
    hrest _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  refine ⟨E, fun p q => ?_, fun p q hpq => ?_, habuts.of_iso fun n => ?_, fun n => ?_⟩
  · obtain ⟨e⟩ := hE₂ p q
    exact ⟨e ≪≫ ((B.smallPushforward g AddCommGrpCat.{u + 1}).rightDerivedPlus p).mapIso
        ((higherDirectImageIsoRightDerivedPlus.{u + 1} B f q).symm.app F) ≪≫
      (higherDirectImageIsoRightDerivedPlus.{u + 1} B g p).symm.app _⟩
  · obtain ⟨e⟩ := hE₂ p q
    refine IsZero.of_iso ?_ e
    rcases hpq with hp | hq
    · exact Functor.isZero_rightDerivedPlus_of_neg _ _ p hp
    · let := (B.smallPushforward g AddCommGrpCat.{u + 1}).commShiftRightDerivedFunctorPlus
      have := (B.smallPushforward g AddCommGrpCat.{u + 1}).isTriangulated_rightDerivedFunctorPlus
      have : ((B.smallPushforward g AddCommGrpCat.{u + 1}).rightDerivedPlus p).Additive := by
        unfold Functor.rightDerivedPlus
        infer_instance
      exact Functor.map_isZero _ (Functor.isZero_rightDerivedPlus_of_neg _ F q hq)
  · exact (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPlusNatIsoOfIso
      (smallEtaleSheafPushforwardCompIso B X Y Z f g AddCommGrpCat.{u + 1}) n).app F
  · exact ⟨(higherDirectImageIsoRightDerivedPlus.{u + 1} B (f ≫ g) n).symm.app F⟩

end AlgebraicGeometry.BigEtaleSite
