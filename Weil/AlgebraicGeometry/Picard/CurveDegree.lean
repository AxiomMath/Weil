module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsionExponent
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardShrink

/-!
# The `n`-division points of the Picard group of a scheme

For a scheme `X` and a natural number `n`, the group of `n`-division points of `Pic X` is
`ₙPic X = {[L] ∈ Pic X : L ^ ⊗ n ≅ 𝒪_X} = ker (n : Pic X → Pic X)`,
the kernel of multiplication by `n` on the abelian group `Pic X`.

## Main definitions

* `AlgebraicGeometry.Scheme.picardTorsion X n`: the subgroup `ₙPic X` of
  `Stacks.Picard.ofScheme X`, namely Mathlib's `AddSubgroup.torsionBy` (`(Pic X)[n]`).

## Main results

* `AlgebraicGeometry.Scheme.mem_picardTorsion_iff`: `x ∈ ₙPic X ↔ n • x = 0`.
* `AlgebraicGeometry.Scheme.picardTorsion_eq_ker`: `ₙPic X` is the kernel of multiplication by
  `n`.
* `AlgebraicGeometry.Scheme.picardClass_mem_picardTorsion_iff`: the class of an invertible
  module `L` lies in `ₙPic X` exactly when `L ^ ⊗ n ≅ 𝒪_X`.
* `AlgebraicGeometry.Scheme.picardTorsion_toIntSubmodule`: as a `ℤ`-submodule, `ₙPic X` is
  `Submodule.torsionBy ℤ (Pic X) n`.
* `AlgebraicGeometry.Scheme.picardTorsionAddEquivSchemePicard`: `ₙPic X` is identified with the
  `n`-torsion of the other model `AlgebraicGeometry.schemePicard X` of `Pic X`.

## Implementation notes

`Pic X` is `Stacks.Picard.ofScheme X`, the group of isomorphism classes of invertible
`𝒪_X`-modules under tensor product (Tag 01CX), whose classes are
`Stacks.SheafOfModules.picardClass` and whose tensor powers are
`Stacks.SheafOfModules.TensorPower.tensorPower`. The library also carries the isomorphic model
`AlgebraicGeometry.schemePicard X` (a shrunk carrier); the two `n`-torsion subgroups are matched
along `Stacks.SheafOfModules.picardGroupShrinkAddEquiv`.

The definition makes sense for every `n : ℕ` (for `n = 0` it is all of `Pic X`); the source
states it for `n ≥ 1`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

open Stacks.RingedSpace (structureIsSheaf)

/-- The group `ₙPic X` of `n`-division points of the Picard group of a scheme `X`: the classes
`x` with `n • x = 0`, i.e. the kernel of multiplication by `n` on `Pic X`. -/
@[weil "not_fk105_n_torsion_picard_group"]
abbrev picardTorsion (X : Scheme.{u}) (n : ℕ) : AddSubgroup (Stacks.Picard.ofScheme X) :=
  AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) n

variable {X : Scheme.{u}} {n : ℕ}

theorem mem_picardTorsion_iff (x : Stacks.Picard.ofScheme X) :
    x ∈ picardTorsion X n ↔ n • x = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

/-- `ₙPic X` is the kernel of multiplication by `n` on `Pic X`. -/
@[weil "not_fk105_n_torsion_picard_group"]
theorem picardTorsion_eq_ker (X : Scheme.{u}) (n : ℕ) :
    picardTorsion X n =
      (DistribSMul.toAddMonoidHom (Stacks.Picard.ofScheme X) n).ker :=
  AddSubgroup.ext fun x => (mem_picardTorsion_iff x).trans Iff.rfl

/-- The class of an invertible `𝒪_X`-module `L` lies in `ₙPic X` exactly when
`L ^ ⊗ n ≅ 𝒪_X`. -/
@[weil "not_fk105_n_torsion_picard_group"]
theorem picardClass_mem_picardTorsion_iff
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.toRingedSpace.presheaf (structureIsSheaf X.toRingedSpace)))
    [hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureIsSheaf X.toRingedSpace) L] (n : ℕ) :
    Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
        (structureIsSheaf X.toRingedSpace) L hL ∈ picardTorsion X n ↔
      Nonempty (Stacks.SheafOfModules.TensorPower.tensorPower X.toRingedSpace.presheaf
          (structureIsSheaf X.toRingedSpace) L (n : ℤ) ≅
        SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          X.toRingedSpace.presheaf (structureIsSheaf X.toRingedSpace))) := by
  rw [mem_picardTorsion_iff, ← natCast_zsmul,
    ← Stacks.Picard.classOf_tensorPower, ← Stacks.SheafOfModules.picardClass_zero,
    Stacks.SheafOfModules.picardClass_eq_iff]

/-- As a `ℤ`-submodule, `ₙPic X` is `Submodule.torsionBy ℤ (Pic X) n`, the form in which the
torsion of `Pic X` is stated elsewhere in the library. -/
theorem picardTorsion_toIntSubmodule (X : Scheme.{u}) (n : ℕ) :
    AddSubgroup.toIntSubmodule (picardTorsion X n) =
      Submodule.torsionBy ℤ (Stacks.Picard.ofScheme X) (n : ℤ) :=
  rfl

section SchemePicard

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-- The comparison `Pic X ≃+ schemePicard X` of the two models of the Picard group. -/
abbrev picardAddEquivSchemePicard (X : Scheme.{u}) :
    Stacks.Picard.ofScheme X ≃+ schemePicard X :=
  Stacks.SheafOfModules.picardGroupShrinkAddEquiv X.presheaf
    (AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf X)

theorem picardAddEquivSchemePicard_mem_torsionBy_iff (x : Stacks.Picard.ofScheme X) :
    picardAddEquivSchemePicard X x ∈ AddSubgroup.torsionBy (schemePicard X) n ↔
      x ∈ picardTorsion X n := by
  rw [AddSubgroup.torsionBy.nsmul_iff, mem_picardTorsion_iff, ← map_nsmul,
    AddEquivClass.map_eq_zero_iff]

/-- `ₙPic X` is the `n`-torsion of the model `AlgebraicGeometry.schemePicard X` of `Pic X`. -/
def picardTorsionAddEquivSchemePicard (X : Scheme.{u}) (n : ℕ) :
    picardTorsion X n ≃+ AddSubgroup.torsionBy (schemePicard X) n where
  toFun x := ⟨picardAddEquivSchemePicard X x,
    (picardAddEquivSchemePicard_mem_torsionBy_iff (x : Stacks.Picard.ofScheme X)).2 x.2⟩
  invFun y := ⟨(picardAddEquivSchemePicard X).symm y,
    (picardAddEquivSchemePicard_mem_torsionBy_iff _).1
      (by rw [AddEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem coe_picardTorsionAddEquivSchemePicard_apply (x : picardTorsion X n) :
    (picardTorsionAddEquivSchemePicard X n x : schemePicard X) =
      picardAddEquivSchemePicard X x :=
  rfl

end SchemePicard

end AlgebraicGeometry.Scheme
