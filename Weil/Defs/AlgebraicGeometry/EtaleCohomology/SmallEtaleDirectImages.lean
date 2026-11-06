module

public import Weil.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChange
public import Weil.Defs.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import Weil.Attr

/-!
# Acyclic morphisms

A morphism `g : T ⟶ S` of schemes is *acyclic* if for every abelian sheaf `F` on the small étale
site of `S` which is torsion prime to the residue characteristics of `S`,

* the unit `F ⟶ g_* g^* F` of the adjunction `g^* ⊣ g_*` is an isomorphism, and
* the higher direct images `R^i g_* (g^* F)` vanish for all `i > 0`.

Equivalently, `F ⟶ R g_* g^* F` is a quasi-isomorphism for all such `F`. Smooth morphisms are
the basic examples (smooth base change).

## Main definitions

* `AlgebraicGeometry.BigEtaleSite.IsAcyclic`: the property of a morphism of a big étale site of
  being acyclic.

## Main results

* `AlgebraicGeometry.BigEtaleSite.IsAcyclic.isIso_unit_app`: for an acyclic `g` and a sheaf
  `F` torsion prime to the residue characteristics of the base, `F ⟶ g_* g^* F` is an
  isomorphism.
* `AlgebraicGeometry.BigEtaleSite.IsAcyclic.isZero_higherDirectImage`: for such `g` and `F`,
  `R^i g_* (g^* F) = 0` for `i > 0`.

## Implementation notes

The étale sites are the size-bounded small étale sites `AlgebraicGeometry.SmallEtale` of a big
étale site `B`, the inverse image is `AlgebraicGeometry.smallEtaleInverseImage`, the direct image
`AlgebraicGeometry.BigEtaleSite.smallPushforward`, and the higher direct images are
`AlgebraicGeometry.BigEtaleSite.higherDirectImage`. The coefficients are `AddCommGrpCat.{u + 1}`
for schemes in `Scheme.{u}`: this is the first universe in which the inverse image exists as a
left Kan extension and the sheaf categories have enough injectives.

The source assumes `S` and `T` noetherian; the definition makes sense for any morphism, and the
noetherian hypotheses are carried by the results about acyclic morphisms instead.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u}) {S T : B.Scheme}

/-- **Acyclic morphisms.** A morphism `g : T ⟶ S` of a big étale site is acyclic if for every
abelian sheaf `F` on the small étale site of `S` which is torsion prime to the residue
characteristics of `S`, the unit `F ⟶ g_* g^* F` is an isomorphism and the higher direct images
`R^i g_* (g^* F)` vanish for all `i > 0`. -/
@[weil "def_fk107_acyclic_morphism"]
def IsAcyclic (g : T ⟶ S) : Prop :=
  ∀ F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1},
    SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F →
      IsIso ((smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1}).unit.app F) ∧
        ∀ i : ℕ, 0 < i →
          IsZero ((higherDirectImage.{u + 1} B g i).obj
            ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj F))

variable {B}

/-- The defining property of an acyclic morphism, in terms of its two conditions. -/
theorem isAcyclic_iff (g : T ⟶ S) :
    IsAcyclic B g ↔
      ∀ F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1},
        SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F →
          IsIso ((smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1}).unit.app F) ∧
            ∀ i : ℕ, 0 < i →
              IsZero ((higherDirectImage.{u + 1} B g i).obj
                ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj F)) :=
  Iff.rfl

/-- A morphism satisfying both conditions on every sheaf torsion prime to the residue
characteristics of the base is acyclic. -/
theorem IsAcyclic.mk {g : T ⟶ S}
    (unit : ∀ F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1},
      SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F →
        IsIso ((smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1}).unit.app F))
    (higher : ∀ F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1},
      SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F →
        ∀ i : ℕ, 0 < i → IsZero ((higherDirectImage.{u + 1} B g i).obj
          ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj F))) :
    IsAcyclic B g :=
  fun F hF ↦ ⟨unit F hF, higher F hF⟩

/-- For an acyclic morphism `g` and a sheaf `F` torsion prime to the residue characteristics of
the base, the unit `F ⟶ g_* g^* F` is an isomorphism. -/
theorem IsAcyclic.isIso_unit_app {g : T ⟶ S} (hg : IsAcyclic B g)
    {F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (hF : SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F) :
    IsIso ((smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1}).unit.app F) :=
  (hg F hF).1

/-- For an acyclic morphism `g` and a sheaf `F` torsion prime to the residue characteristics of
the base, `F ≅ g_* g^* F` through the unit. -/
def IsAcyclic.unitIso {g : T ⟶ S} (hg : IsAcyclic B g)
    {F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (hF : SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F) :
    F ≅ (B.smallPushforward g AddCommGrpCat.{u + 1}).obj
      ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj F) :=
  haveI := hg.isIso_unit_app hF
  asIso ((smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1}).unit.app F)

@[simp]
theorem IsAcyclic.unitIso_hom {g : T ⟶ S} (hg : IsAcyclic B g)
    {F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (hF : SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F) :
    (hg.unitIso hF).hom = (smallEtaleInverseImageAdjunction B g AddCommGrpCat.{u + 1}).unit.app F :=
  rfl

/-- For an acyclic morphism `g` and a sheaf `F` torsion prime to the residue characteristics of
the base, `R^i g_* (g^* F) = 0` for all `i > 0`. -/
theorem IsAcyclic.isZero_higherDirectImage {g : T ⟶ S} (hg : IsAcyclic B g)
    {F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (hF : SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F)
    {i : ℕ} (hi : 0 < i) :
    IsZero ((higherDirectImage.{u + 1} B g i).obj
      ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj F)) :=
  (hg F hF).2 i hi

/-- For an acyclic morphism `g` and a sheaf `F` torsion prime to the residue characteristics of
the base, `R^(i + 1) g_* (g^* F) = 0`. -/
theorem IsAcyclic.isZero_higherDirectImage_succ {g : T ⟶ S} (hg : IsAcyclic B g)
    {F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (hF : SmallEtale.IsTorsionPrimeToResidueCharacteristics B S.obj S.property S.obj F)
    (i : ℕ) :
    IsZero ((higherDirectImage.{u + 1} B g (i + 1)).obj
      ((smallEtaleInverseImage B g AddCommGrpCat.{u + 1}).obj F)) :=
  hg.isZero_higherDirectImage hF i.succ_pos

end AlgebraicGeometry.BigEtaleSite
