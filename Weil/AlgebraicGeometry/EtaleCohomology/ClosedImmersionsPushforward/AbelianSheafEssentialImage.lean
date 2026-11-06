module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.AbelianSheafEssentialImage
public import Weil.CategoryTheory.Sites.Pullback
public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.InverseImageStalk

/-!
# Abelian sheaves supported on a closed subscheme

Let `i : Z ⟶ X` be a closed immersion of schemes of a big étale site and `F` an abelian sheaf
on the small étale site of `X` whose stalk vanishes at every geometric point of `X` whose image
lies in the open complement `X - Z`. Then the unit `F ⟶ i_* i^* F` of the inverse image/direct
image adjunction is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleInverseImageUnit_app_of_isZero_sheafFiber` — the unit
  `F ⟶ i_* i^* F` is an isomorphism when `F` has vanishing stalks off `Z`.

## Implementation notes

Direct image along a closed immersion is fully faithful on abelian sheaves, so the unit of the
adjunction is an isomorphism at `F` exactly when `F` lies in the essential image of `i_*`; that
essential image consists of the sheaves whose support lies in `Z` (Stacks 04CA (2)). Stalks are
the fibres of the site points `AlgebraicGeometry.geometricPointSitePoint` at geometric points
over algebraically closed fields; these are the stalks `AlgebraicGeometry.etaleStalk`
definitionally.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- **An abelian sheaf supported on a closed subscheme is a direct image.** If the stalk of the
abelian sheaf `F` on the small étale site of `X` vanishes at every geometric point of `X` whose
image lies outside the closed subscheme `Z`, then the unit `F ⟶ i_* i^* F` is an isomorphism. -/
@[weil "lem_fk105_sheaf_supported_on_closed_is_pushforward"]
theorem isIso_smallEtaleInverseImageUnit_app_of_isZero_sheafFiber
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
    (hF : ∀ s : GeometricPoint X.obj, s.hom default ∉ Set.range (B.inclusion.map i).base →
      IsZero ((geometricPointSitePoint B X.obj X.property s).sheafFiber.obj F)) :
    IsIso ((smallEtaleInverseImageUnit B i AddCommGrpCat.{u + 1}).app F) := by
  rw [Adjunction.isIso_unit_app_iff_mem_essImage]
  refine (smallEtalePushforward_essImage_iff_abelian B i F).mpr ?_
  rintro x ⟨s, hlies, hnz⟩
  by_contra hx
  exact hnz (hF s (hlies ▸ hx))

end AlgebraicGeometry

end

/-! ### The unit of `i^* ⊣ i_*` at stalks over a closed subscheme -/

/-!
# The unit of `i^* ⊣ i_*` at stalks over a closed subscheme

Let `i : Z ⟶ X` be a closed immersion of schemes of a big étale site `B`, let `F` be a sheaf on
the small étale site of `X` (of sets, of abelian groups, or with values in any category `A` with
the relevant colimits and sheafification), and let `x` be a geometric point of `X` whose image
lies in `Z`. Then the unit `η_F : F ⟶ i_* i^* F` of the adjunction `i^* ⊣ i_*` induces an
isomorphism of stalks `F_x ≅ (i_* i^* F)_x`.

## Main definitions

* `AlgebraicGeometry.smallEtaleInverseImageUnitSheafFiberIso` — the isomorphism
  `F_x ≅ (i_* i^* F)_x` induced by the unit.

## Main results

* `AlgebraicGeometry.isIso_sheafFiber_map_smallEtaleInverseImageUnit_app` — the stalk at `x` of
  the unit `F ⟶ i_* i^* F` is an isomorphism.

## Implementation notes

The source argues through the computation of the stalks of a finite direct image. We argue
instead through the triangle identity: since `i_*` is fully faithful, the counit
`i^* i_* ⟶ 𝟭` is an isomorphism, so `i^*(η_F)` is an isomorphism. As `x = i ∘ z` for a
geometric point `z` of `Z`, and the stalk of `i^* G` at `z` is naturally the stalk of `G` at
`i ∘ z` (`AlgebraicGeometry.smallEtaleInverseImageSheafFiberIso`), the stalk of `η_F` at `x` is
identified with the stalk of `i^*(η_F)` at `z`, an isomorphism.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A] [HasProducts.{u} A]
  [HasWeakSheafify (SmallEtale.topology B Z.obj Z.property) A]

/-- Stalks on the small étale sites are colimits indexed by categories of size `u`. -/
local instance : HasColimitsOfSize.{u, u} A := hasColimitsOfSizeShrink.{u, u, u, u + 1} A

/-- **The unit of `i^* ⊣ i_*` is a stalk isomorphism over a closed subscheme.** For a closed
immersion `i : Z ⟶ X`, a sheaf `F` on the small étale site of `X` and a geometric point `x` of
`X` whose image lies in `Z`, the unit `F ⟶ i_* i^* F` induces an isomorphism of stalks at `x`. -/
@[weil "lem_fk105_closed_immersion_unit_stalk_iso"]
theorem isIso_sheafFiber_map_smallEtaleInverseImageUnit_app
    [IsClosedImmersion (B.inclusion.map i)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A) (x : GeometricPoint X.obj)
    (hx : x.hom default ∈ Set.range (B.inclusion.map i).base) :
    IsIso ((geometricPointSitePoint B X.obj X.property x).sheafFiber.map
      ((smallEtaleInverseImageUnit B i A).app F)) := by
  obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B i x hx
  have hpb : IsIso ((smallEtaleInverseImage B i A).map
      ((smallEtaleInverseImageUnit B i A).app F)) := by
    have h := (smallEtaleInverseImageAdjunction B i A).left_triangle_components F
    have : IsIso ((smallEtaleInverseImage B i A).map
        ((smallEtaleInverseImageAdjunction B i A).unit.app F) ≫
        (smallEtaleInverseImageAdjunction B i A).counit.app
          ((smallEtaleInverseImage B i A).obj F)) := by
      rw [h]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((smallEtaleInverseImageAdjunction B i A).counit.app ((smallEtaleInverseImage B i A).obj F))
  exact (NatIso.isIso_map_iff (smallEtaleInverseImageSheafFiberIso B i z A) _).mpr
    (inferInstanceAs (IsIso ((geometricPointSitePoint B Z.obj Z.property z).sheafFiber.map
      ((smallEtaleInverseImage B i A).map ((smallEtaleInverseImageUnit B i A).app F)))))

/-- **The stalk isomorphism `F_x ≅ (i_* i^* F)_x`** induced by the unit of `i^* ⊣ i_*`, for a
closed immersion `i : Z ⟶ X` and a geometric point `x` of `X` whose image lies in `Z`. -/
@[weil "lem_fk105_closed_immersion_unit_stalk_iso"]
def smallEtaleInverseImageUnitSheafFiberIso
    [IsClosedImmersion (B.inclusion.map i)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A) (x : GeometricPoint X.obj)
    (hx : x.hom default ∈ Set.range (B.inclusion.map i).base) :
    (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj F ≅
      (geometricPointSitePoint B X.obj X.property x).sheafFiber.obj
        ((B.smallPushforward i A).obj ((smallEtaleInverseImage B i A).obj F)) :=
  haveI := isIso_sheafFiber_map_smallEtaleInverseImageUnit_app B i A F x hx
  asIso ((geometricPointSitePoint B X.obj X.property x).sheafFiber.map
    ((smallEtaleInverseImageUnit B i A).app F))

@[simp]
lemma smallEtaleInverseImageUnitSheafFiberIso_hom
    [IsClosedImmersion (B.inclusion.map i)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) A) (x : GeometricPoint X.obj)
    (hx : x.hom default ∈ Set.range (B.inclusion.map i).base) :
    (smallEtaleInverseImageUnitSheafFiberIso B i A F x hx).hom =
      (geometricPointSitePoint B X.obj X.property x).sheafFiber.map
        ((smallEtaleInverseImageUnit B i A).app F) :=
  rfl

end AlgebraicGeometry

end
