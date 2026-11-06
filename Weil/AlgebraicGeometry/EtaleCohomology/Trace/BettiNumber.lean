module

public import Weil.AlgebraicGeometry.ComplexPoints.Betti.ArtinComparison
public import Weil.AlgebraicGeometry.ComplexPoints.Betti.IntegralCohomologyFG
public import Weil.AlgebraicGeometry.EtaleCohomology.Trace.BettiNumberGoodReduction
public import Weil.Attr

/-!
# The degree of `P_ν` is the Betti number

Let `S₀` be smooth and projective over a finite field `κ`, arising by good reduction of a smooth
projective scheme `Y` over `ℂ`, and let `ℓ ≠ char κ` be a prime. Then the degree of
`P_ν(t) = det(1 - t F_ν | H^ν(S₀ ⊗ κ̄, ℚ_ℓ))` is the `ν`-th Betti number
`b_ν(Y) = dim_ℂ H^ν(Y(ℂ), ℂ)` of `Y`, the dimension of the sheaf cohomology of the constant
sheaf `ℂ` on the analytic space `Y(ℂ)`.

## Main results

* `Weil.natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber`: `deg P_ν = b_ν(Y)`.
* `AlgebraicGeometry.Scheme.finiteDimensional_complexCohomology`: `H^ν(Y(ℂ), ℂ)` is
  finite-dimensional for `Y` smooth projective over `ℂ`, so `b_ν(Y)` is an honest dimension.
* `Weil.natDegree_rationalFrobeniusCharpolyReverse_eq_finrank_complexCohomology`: the same
  statement with this finiteness made explicit.

## Implementation notes

`Scheme.bettiNumber y ν` is `Module.finrank ℂ (Scheme.complexCohomology y ν)`, and
`Module.finrank` is `0` on an infinite-dimensional space. The equation `deg P_ν = b_ν(Y)` alone
therefore does not say that `H^ν(Y(ℂ), ℂ)` is finite-dimensional; the corollaries at the end of
this file state it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.7.
-/

@[expose] public section

open AlgebraicGeometry Stacks.EtaleCohomology CategoryTheory TopologicalSpace

namespace Weil

/-- **`deg P_ν = b_ν(Y)`** (FK IV.1.7). Let `S₀` be smooth and projective over the finite field
`κ`, arising by good reduction of the smooth projective scheme `Y` over `ℂ`, and `ℓ ≠ char κ` a
prime. Then the degree of `P_ν(t) = det(1 - t F_ν | H^ν(S₀ ⊗ κ̄, ℚ_ℓ))` is the `ν`-th Betti
number of `Y`, the dimension of `H^ν(Y(ℂ), ℂ)`. -/
@[weil "lem_fk401_char_poly_degree_betti_number"]
theorem natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber
    (B : BigEtaleSite.{0}) (S₀ : B.Scheme) {κ : Type} [Field κ] [Fintype κ]
    (s₀ : S₀.1 ⟶ Spec (.of κ)) [Smooth s₀] [IsProper s₀] (hs₀ : IsProjective s₀)
    {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [Smooth y] (hy : IsProjective y)
    (h : Scheme.ArisesByGoodReduction s₀ y) (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar κ)] (ν : ℕ) :
    (Weil.rationalFrobeniusCharpolyReverse B S₀ s₀ ℓ ν).natDegree = Scheme.bettiNumber y ν :=
  natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber_of_artinComparison
    Scheme.artinComparison Scheme.integralCohomologyFGOfProjective B S₀ s₀ hs₀ y hy h ℓ ν

end Weil

namespace AlgebraicGeometry.Scheme

/-- **The complex cohomology of a smooth projective scheme over `ℂ` is finite-dimensional.** For
`Y` smooth and projective over `ℂ`, `H^ν(Y(ℂ), ℂ)` is a finite-dimensional `ℂ`-vector space in
every degree: it is `ℂ ⊗_ℤ H^ν(Y(ℂ), ℤ)` (`Y(ℂ)` is compact Hausdorff), and `H^ν(Y(ℂ), ℤ)` is
finitely generated (`Y(ℂ)` is a compact neighbourhood retract in a Euclidean space).

This is stated separately because `bettiNumber y ν` is a `Module.finrank`, which is `0` on an
infinite-dimensional space, so `bettiNumber y ν` alone does not show finiteness. -/
theorem finiteDimensional_complexCohomology {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [Smooth y]
    (hy : IsProjective y) (ν : ℕ) : FiniteDimensional ℂ (complexCohomology y ν) := by
  have := ComplexPoints.compactSpace_of_isProjective hy
  have := ComplexPoints.t2Space_of_isProjective hy
  let _ := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) (ModuleCat.{0} ℂ))
  let _ := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  have hℤ : Module.Finite ℤ (analyticCohomologyConstant y (AddCommGrpCat.of ℤ) ν) :=
    Module.Finite.iff_addGroup_fg.2 (integralCohomologyFG_of_smooth_of_isProjective ‹_› hy ν)
  let iso : AddCommGrpCat.of (ULift.{0} ℤ) ≅ AddCommGrpCat.of ℤ :=
    (AddEquiv.ulift.{0, 0} (α := ℤ)).toAddCommGrpIso
  let e := Sheaf.H.addEquivOfIso _ ((constantSheaf
    (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0}).mapIso iso) ν
  have hU := Module.Finite.equiv (R := ℤ)
    (M := analyticCohomologyConstant y (AddCommGrpCat.of ℤ) ν) e.symm.toIntLinearEquiv
  exact Module.Finite.equiv (CompactHausdorffCohomology.extConstantSheafComplexLinearEquiv
    (X := TopCat.of (ComplexPoints y)) ν).symm

/-- **The Betti number of a smooth projective scheme over `ℂ` is the dimension of a
finite-dimensional space**: `H^ν(Y(ℂ), ℂ)` is finite-dimensional and `b_ν(Y)` is its dimension.
Stated because `Module.finrank` is `0` on infinite-dimensional spaces, so the definition of
`bettiNumber` alone does not show finiteness. -/
theorem finiteDimensional_complexCohomology_and_bettiNumber_eq_finrank {Y : Scheme.{0}}
    (y : Y ⟶ Spec (.of ℂ)) [Smooth y] (hy : IsProjective y) (ν : ℕ) :
    FiniteDimensional ℂ (complexCohomology y ν) ∧
      bettiNumber y ν = Module.finrank ℂ (complexCohomology y ν) :=
  ⟨finiteDimensional_complexCohomology y hy ν, rfl⟩

end AlgebraicGeometry.Scheme

namespace Weil

/-- **`deg P_ν = dim_ℂ H^ν(Y(ℂ), ℂ)`, with `H^ν(Y(ℂ), ℂ)` finite-dimensional.** Under the
hypotheses of `natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber` (FK IV.1.7), the
complex cohomology `H^ν(Y(ℂ), ℂ)` is finite-dimensional and the degree of `P_ν` is its
dimension. This makes explicit what `Module.finrank` (which is `0` on infinite-dimensional spaces)
leaves implicit in `natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber`. -/
theorem natDegree_rationalFrobeniusCharpolyReverse_eq_finrank_complexCohomology
    (B : BigEtaleSite.{0}) (S₀ : B.Scheme) {κ : Type} [Field κ] [Fintype κ]
    (s₀ : S₀.1 ⟶ Spec (.of κ)) [Smooth s₀] [IsProper s₀] (hs₀ : IsProjective s₀)
    {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [Smooth y] (hy : IsProjective y)
    (h : Scheme.ArisesByGoodReduction s₀ y) (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ℓ ≠ ringChar κ)] (ν : ℕ) :
    FiniteDimensional ℂ (Scheme.complexCohomology y ν) ∧
      (Weil.rationalFrobeniusCharpolyReverse B S₀ s₀ ℓ ν).natDegree =
        Module.finrank ℂ (Scheme.complexCohomology y ν) :=
  ⟨Scheme.finiteDimensional_complexCohomology y hy ν,
    natDegree_rationalFrobeniusCharpolyReverse_eq_bettiNumber B S₀ s₀ hs₀ y hy h ℓ ν⟩

end Weil
