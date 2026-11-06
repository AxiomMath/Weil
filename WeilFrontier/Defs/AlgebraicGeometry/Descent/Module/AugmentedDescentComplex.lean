module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Descent.Module.AugmentedDescentComplex

/-!
# The Amitsur complex of a ring homomorphism

Let `A → B` be a homomorphism of commutative rings and `M` an `A`-module. The *Amitsur complex*
of `B / A` with coefficients in `M` is the cochain complex of `A`-modules

`0 → M → B ⊗[A] M → B ⊗[A] B ⊗[A] M → B ⊗[A] B ⊗[A] B ⊗[A] M → ⋯`

whose first map is `m ↦ 1 ⊗ m` and whose differential on `B^{⊗(n + 1)} ⊗[A] M` is the
alternating sum `∑ᵢ (-1)ⁱ δᵢ` of the `n + 2` maps `δᵢ` inserting a `1` into the `i`-th of the
`B`-factors. In the lowest degree the differential is `b ⊗ m ↦ 1 ⊗ b ⊗ m - b ⊗ 1 ⊗ m`.

The complex is the augmented descent complex `Stacks.Descent.augmentedDescentComplex`: the
alternating coface map complex of the Čech conerve of `A → B` tensored with `M`, augmented by
`M` in degree zero. This file names it and records the description of its terms and
differentials in terms of tensor powers.

## Main definitions

* `Algebra.amitsurComplex A B M`: the Amitsur complex, indexed by `ℕ` with `M` in degree `0`.
* `Algebra.amitsurComplexXIso A B M n`: its degree-`(n + 1)` term is `B^{⊗(n + 1)} ⊗[A] M`.

## Main results

* `Algebra.amitsurComplex_X_zero`: the degree-zero term is `M`.
* `Algebra.amitsurComplex_d_zero_one`: the first map is `m ↦ 1 ⊗ m`.
* `Algebra.amitsurComplex_d_succ`: the differential on `B^{⊗(n + 1)} ⊗[A] M` is the alternating
  sum of the insertions of a `1`.
* `Algebra.amitsurComplex_d_one_two_tmul`: in the lowest degree it is
  `b ⊗ m ↦ 1 ⊗ b ⊗ m - b ⊗ 1 ⊗ m`.

## Implementation notes

The `B`-factors stand to the left of `M`, so the term written `M ⊗ B^{⊗(n + 1)}` in the source
is `B^{⊗(n + 1)} ⊗[A] M` here; the two differ by the braiding `TensorProduct.comm`, which
commutes with the insertions of a `1`. The positions of the `B`-factors are numbered from the
left, as in the source: `Stacks.Descent.tensorInsertOne A B n 0` is `x ↦ 1 ⊗ x`. The ring
homomorphism `A → B` is an `Algebra A B` instance, and the complex is indexed by `ℕ`, so the
source's degree `n` (with `M` in degree `-1`) is degree `n + 1` here. Exactness of the complex
for a faithfully flat or a split extension is proved downstream; the cosimplicial description
gives `d ≫ d = 0`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III][FK88]
* [Stacks Project, Tag 023K](https://stacks.math.columbia.edu/tag/023K)
-/

@[expose] public section

open CategoryTheory AlgebraicTopology Stacks.Descent
open scoped TensorProduct

universe u v

namespace Algebra

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (M : Type (max u v)) [AddCommGroup M] [Module A M]

/-- **The Amitsur complex** `0 → M → B ⊗[A] M → B ⊗[A] B ⊗[A] M → ⋯` of the ring
homomorphism `A → B` with coefficients in the `A`-module `M`, with `M` in degree `0`. The first
map is `m ↦ 1 ⊗ m`, and the differential on `B^{⊗(n + 1)} ⊗[A] M` is the alternating sum of
the insertions of a `1` into the `B`-factors. -/
@[weil "def_fka3_amitsur_complex"]
noncomputable abbrev amitsurComplex : CochainComplex (ModuleCat.{max u v} A) ℕ :=
  augmentedDescentComplex A B M

/-- The degree-zero term of the Amitsur complex is the coefficient module. -/
@[weil "def_fka3_amitsur_complex"]
lemma amitsurComplex_X_zero : (amitsurComplex A B M).X 0 = ModuleCat.of A M :=
  rfl

/-- The degree-`(n + 1)` term of the Amitsur complex is `B^{⊗(n + 1)} ⊗[A] M`. -/
@[weil "def_fka3_amitsur_complex"]
noncomputable def amitsurComplexXIso (n : ℕ) :
    ModuleCat.of A ((tensorPowerAlg A B n : Type u) ⊗[A] M) ≅ (amitsurComplex A B M).X (n + 1) :=
  augmentedDescentComplexXIso A B M n

/-- **The first map of the Amitsur complex is `m ↦ 1 ⊗ m`.** -/
@[weil "def_fka3_amitsur_complex"]
lemma amitsurComplex_d_zero_one (m : M) :
    (amitsurComplex A B M).d 0 1 m =
      (amitsurComplexXIso A B M 0).hom ((1 : (tensorPowerAlg A B 0 : Type u)) ⊗ₜ[A] m) :=
  augmentedDescentComplex_d_zero_one_eq A B M m

/-- **The differential of the Amitsur complex on `B^{⊗(n + 1)} ⊗[A] M`** is the alternating sum
`∑ᵢ (-1)ⁱ δᵢ` of the maps `δᵢ = tensorInsertOne A B n i ⊗ id_M` inserting a `1` into the `i`-th
of the `B`-factors, `0 ≤ i ≤ n + 1`. -/
@[weil "def_fka3_amitsur_complex"]
theorem amitsurComplex_d_succ (n : ℕ) :
    (amitsurComplexXIso A B M n).hom ≫ (amitsurComplex A B M).d (n + 1) (n + 2) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (tensorModuleFunctor A M).map (tensorInsertOne A B n i)) ≫
        (amitsurComplexXIso A B M (n + 1)).hom :=
  augmentedDescentComplexXIso_d A B M n

/-- The map `δᵢ ⊗ id_M` acts on a pure tensor by inserting a `1` into the `B`-factors. -/
lemma tensorModuleFunctor_map_tensorInsertOne_tmul (n : ℕ) (i : Fin (n + 2))
    (x : (tensorPowerAlg A B n : Type u)) (m : M) :
    (tensorModuleFunctor A M).map (tensorInsertOne A B n i) (x ⊗ₜ[A] m) =
      (tensorInsertOne A B n i).hom x ⊗ₜ[A] m :=
  rfl

/-- **In the lowest degree the differential of the Amitsur complex is
`b ⊗ m ↦ 1 ⊗ b ⊗ m - b ⊗ 1 ⊗ m`.** -/
@[weil "def_fka3_amitsur_complex"]
theorem amitsurComplex_d_one_two_tmul (b : B) (m : M) :
    (amitsurComplex A B M).d 1 2 ((amitsurComplexXIso A B M 0).hom (b ⊗ₜ[A] m)) =
      (amitsurComplexXIso A B M 1).hom
        (((1 : B) ⊗ₜ[A] b : B ⊗[A] B) ⊗ₜ[A] m - ((b ⊗ₜ[A] (1 : B) : B ⊗[A] B)) ⊗ₜ[A] m) := by
  have key (x : (tensorPowerAlg A B 0 : Type u)) :
      (amitsurComplex A B M).d 1 2 ((amitsurComplexXIso A B M 0).hom (x ⊗ₜ[A] m)) =
        (amitsurComplexXIso A B M 1).hom
          ((tensorInsertOne A B 0 0).hom x ⊗ₜ[A] m - (tensorInsertOne A B 0 1).hom x ⊗ₜ[A] m) := by
    exact congr($(augmentedDescentComplexXIso_zero_d A B M) (x ⊗ₜ[A] m))
  refine (key b).trans (congrArg _ ?_)
  exact congrArg₂ (· - ·) (congrArg (· ⊗ₜ[A] m) (tensorInsertOne_zero_apply A B 0 b))
    (congrArg (· ⊗ₜ[A] m) (tensorInsertOne_zero_one_apply A B b))

end Algebra
