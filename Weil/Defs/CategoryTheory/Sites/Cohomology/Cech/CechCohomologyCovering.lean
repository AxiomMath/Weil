module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles

/-!
# Čech cohomology of a covering in the étale category

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes, let
`𝔘 = (Uᵢ → U)_{i ∈ I}` be a family of morphisms of `Et(S)` with target `U`, and let `F` be a
presheaf of abelian groups on `Et(S)`, with Čech complex `Č^•(𝔘, F)` and differentials `d^i`.
Put `Z^i(𝔘, F) = ker d^i`, `B^i(𝔘, F) = im d^{i-1} ∩ ker d^i` and
`Ȟ^i(𝔘, F) = Z^i(𝔘, F) / B^i(𝔘, F)` for `i ≥ 0`, with `d^{-1} = 0`. Since `d^i ∘ d^{i-1} = 0`,
`B^i = im d^{i-1}`, and `Ȟ^i(𝔘, F)` is the `i`-th cohomology of the Čech complex.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomology`: the Čech cohomology
  `Ȟ^i(𝔘, F)`, the `i`-th homology object of `Č^•(𝔘, F)`, for presheaves with values in any
  abelian category with products.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCycles`: the cocycles `Z^i(𝔘, F)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechBoundaries`: the coboundaries
  `B^i(𝔘, F) = im d^{i-1} ∩ ker d^i`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechBoundaries_eq_range`: `B^i = im d^{i-1}`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechBoundaries_zero`: `B^0 = 0`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomologyAddEquiv`: for presheaves of
  abelian groups, `Ȟ^i(𝔘, F) ≅ Z^i(𝔘, F) / B^i(𝔘, F)`.

## Implementation notes

The Čech complex is indexed by `ℕ`. In degree `0` the incoming differential is
`d 0 0 = 0` (the indices are not related by `ComplexShape.up ℕ`), which encodes the convention
`d^{-1} = 0`; with natural-number subtraction `d (i - 1) i` is therefore the incoming
differential in every degree. The cohomology is `Stacks.CechSite.cechCohomology`, i.e. the
abstract homology of the complex; the identification with the explicit quotient
`Z^i / B^i` of the source is the additive equivalence `cechCohomologyAddEquiv`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe a w v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : SmallNoetherianSeparatedEtale B S hS} (E : PreZeroHypercover.{w} U)

/-- **Čech cohomology `Ȟ^i(𝔘, F)` of a covering.** For a family `E = (Uᵢ ⟶ U)_{i}` of
morphisms of `Et(S)` with target `U` and a presheaf `F` on `Et(S)` with values in an abelian
category with products (abelian groups being the case `AddCommGrpCat`), the `i`-th homology of
the Čech complex `Č^•(𝔘, F)`. -/
@[weil "def_fk102_cech_cohomology_covering"]
noncomputable abbrev cechCohomology {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
    [Abelian A] (F : EtalePresheaf B S hS A) (i : ℕ) : A :=
  Stacks.CechSite.cechCohomology E F i

section AddCommGrp

variable [HasProducts.{w} AddCommGrpCat.{a}] (F : EtalePresheaf B S hS AddCommGrpCat.{a})

/-- The Čech cocycles `Z^i(𝔘, F) = ker d^i` of a presheaf of abelian groups. -/
@[weil "def_fk102_cech_cohomology_covering"]
noncomputable def cechCycles (i : ℕ) : AddSubgroup ((cechComplex E F).X i) :=
  ((cechComplex E F).d i (i + 1)).hom.ker

/-- The Čech coboundaries `B^i(𝔘, F) = im d^{i-1} ∩ ker d^i` of a presheaf of abelian groups;
in degree `0` the incoming differential `d 0 0` is zero. -/
@[weil "def_fk102_cech_cohomology_covering"]
noncomputable def cechBoundaries (i : ℕ) : AddSubgroup ((cechComplex E F).X i) :=
  ((cechComplex E F).d (i - 1) i).hom.range ⊓ cechCycles E F i

lemma mem_cechCycles_iff {i : ℕ} (x : (cechComplex E F).X i) :
    x ∈ cechCycles E F i ↔ (cechComplex E F).d i (i + 1) x = 0 :=
  Iff.rfl

/-- Every coboundary is a cocycle: `B^i = im d^{i-1}`. -/
lemma cechBoundaries_eq_range (i : ℕ) :
    cechBoundaries E F i = ((cechComplex E F).d (i - 1) i).hom.range := by
  refine inf_eq_left.mpr ?_
  rintro _ ⟨y, rfl⟩
  change ((cechComplex E F).d (i - 1) i ≫ (cechComplex E F).d i (i + 1)) y = 0
  rw [HomologicalComplex.d_comp_d]
  rfl

lemma cechBoundaries_le_cechCycles (i : ℕ) : cechBoundaries E F i ≤ cechCycles E F i :=
  inf_le_right

/-- In degree `0` there are no coboundaries. -/
lemma cechBoundaries_zero : cechBoundaries E F 0 = ⊥ := by
  rw [cechBoundaries_eq_range, Nat.zero_sub,
    (cechComplex E F).shape 0 0 (by simp)]
  ext x
  simp

/-- **`Ȟ^i(𝔘, F) = Z^i(𝔘, F) / B^i(𝔘, F)`.** For a presheaf of abelian groups the Čech
cohomology is the quotient of the cocycles by the coboundaries. -/
@[weil "def_fk102_cech_cohomology_covering"]
noncomputable def cechCohomologyAddEquiv (i : ℕ) :
    (cechCohomology (A := AddCommGrpCat.{a}) E F i : Type a) ≃+
      (cechCycles E F i ⧸ (cechBoundaries E F i).addSubgroupOf (cechCycles E F i)) :=
  (Stacks.CechSite.homologyEquivQuotient (cechComplex E F) (i - 1) i (i + 1)
    (by rcases i with _ | i <;> simp) (by simp)).trans
    (@QuotientAddGroup.congr _ _ _ _ _ _ (@AddSubgroup.normal_of_isAddCommutative _ _
      ⟨⟨fun a b ↦ Subtype.ext (add_comm a.1 b.1)⟩⟩ _) _
      (AddEquiv.addSubgroupCongr rfl) (by
      rw [cechBoundaries_eq_range]
      ext ⟨x, hx⟩
      simp only [AddMonoidHom.mem_range, AddSubgroup.mem_addSubgroupOf]
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, hy⟩
        exact ⟨y, congrArg Subtype.val hy⟩
      · rintro ⟨y, hy⟩
        exact ⟨_, ⟨y, rfl⟩, Subtype.ext hy⟩))

end AddCommGrp

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
