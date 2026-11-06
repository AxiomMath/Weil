/-
Copyright (c) 2026 Weil formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Weil.AlgebraicGeometry.ComplexPoints.CurveCohomologicalDimension
public import Weil.AlgebraicGeometry.ComplexPoints.RiemannSurface
public import Weil.AlgebraicGeometry.ComplexPoints.Compact
public import Weil.Geometry.Manifold.Sheaf.HolomorphicCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# Cohomology of the holomorphic units on a smooth projective complex curve

Let `C` be a smooth projective curve over `ℂ`, and give its complex points `C(ℂ)` their
structure of a compact Riemann surface. Then the cohomology of the sheaf `𝒪^×` of nowhere
vanishing holomorphic functions on `C(ℂ)` vanishes in every degree `q ≥ 2`, and so does the
cohomology of the sheaf `𝒪` of holomorphic functions.

The proof uses the exponential sequence `0 → ℤ → 𝒪 → 𝒪^× → 0`. Its long exact cohomology
sequence contains `H^q(C(ℂ), 𝒪) → H^q(C(ℂ), 𝒪^×) → H^{q+1}(C(ℂ), ℤ)`. For `q ≥ 2` the first
group vanishes by the Dolbeault resolution of `𝒪` on a compact Riemann surface, and the last
group vanishes because `C(ℂ)` has cohomological dimension at most two.

## Main results

* `ComplexManifold.subsingleton_H_holomorphicUnitsSheaf_of_subsingleton`: on any complex
  manifold, `H^q(M, 𝒪^×) = 0` as soon as `H^q(M, 𝒪) = 0` and `H^{q+1}(M, ℤ) = 0`.
* `AlgebraicGeometry.Scheme.ComplexPoints.subsingleton_H_constantSheaf_of_isProjective`:
  `H^n(C(ℂ), A) = 0` for `n ≥ 3`, for any `Ext` universe and with no dimension hypothesis.
* `AlgebraicGeometry.Scheme.ComplexPoints.subsingleton_H_holomorphicSheafAb_of_isProjective`:
  `H^q(C(ℂ), 𝒪) = 0` for `q ≥ 2`.
* `AlgebraicGeometry.Scheme.ComplexPoints.subsingleton_H_holomorphicUnitsSheaf_of_isProjective`:
  `H^q(C(ℂ), 𝒪^×) = 0` for `q ≥ 2`.

## Implementation notes

A smooth curve is a scheme smooth of relative dimension one over `ℂ`; it need not be
connected. When `C` is empty, every sheaf on `C(ℂ)` is zero; otherwise `C` has dimension one,
which is the form in which the cohomological dimension bound is available. The cohomology is
taken with respect to any choice of `Ext` universe.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §11,
  proof of Theorem 11.6.
* [forster1981] O. Forster, *Lectures on Riemann Surfaces*, §15.
-/

@[expose] public section

universe w' u v

open CategoryTheory Abelian Limits TopologicalSpace Opposite
open scoped Manifold

namespace ComplexManifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type} [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (TopCat.of M)) AddCommGrpCat.{0})]

/-- On a complex manifold, `H^q(M, 𝒪^×)` vanishes when `H^q(M, 𝒪)` and `H^{q+1}(M, ℤ)` do,
by the long exact sequence of the exponential sequence. -/
theorem subsingleton_H_holomorphicUnitsSheaf_of_subsingleton (q : ℕ)
    (hO : Subsingleton (Sheaf.H.{w'} (holomorphicSheafAb I M) q))
    (hZ : Subsingleton (Sheaf.H.{w'} ((constantSheaf (Opens.grothendieckTopology (TopCat.of M))
      AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)) (q + 1))) :
    Subsingleton (Sheaf.H.{w'} (holomorphicUnitsSheaf I M) q) := by
  have hS := exponentialSequence_shortExact I M
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS x rfl
    (@Subsingleton.elim _ hZ _ _)
  rw [← hx₂, @Subsingleton.elim _ hO x₂ 0]
  exact Ext.zero_comp _ _ _ _ _

end ComplexManifold

/-- `Ext` into a zero object vanishes. -/
theorem CategoryTheory.Abelian.Ext.subsingleton_of_isZero_right {𝒞 : Type u} [Category.{v} 𝒞]
    [Abelian 𝒞] [HasExt.{w'} 𝒞]
    (X : 𝒞) {Y : 𝒞} (hY : IsZero Y) (n : ℕ) : Subsingleton (Ext.{w'} X Y n) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  rw [← Ext.comp_mk₀_id x, show 𝟙 Y = 0 from hY.eq_of_src _ _, Ext.mk₀_zero, Ext.comp_zero]

/-- On the empty topological space every abelian sheaf is zero. -/
theorem TopCat.Sheaf.isZero_of_isEmpty (X : TopCat.{0}) [IsEmpty X]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) : IsZero F := by
  refine IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf _ _) F
    (Functor.isZero _ fun U => ?_)
  have hU : unop U = ⊥ := Opens.ext (Set.eq_empty_of_isEmpty _)
  exact (TopCat.Sheaf.isTerminalOfEqEmpty F hU).isZero

namespace AlgebraicGeometry.Scheme.ComplexPoints

variable {C : Scheme.{0}} (c : C ⟶ Spec (.of ℂ))

variable [SmoothOfRelativeDimension 1 c]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints c))) AddCommGrpCat.{0})]

/-- **`H^q(C(ℂ), 𝒪) = 0` for `q ≥ 2`**, for `C` a smooth projective curve over `ℂ`. -/
theorem subsingleton_H_holomorphicSheafAb_of_isProjective (hc : IsProjective c) {q : ℕ}
    (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w'} (ComplexManifold.holomorphicSheafAb 𝓘(ℂ) (ComplexPoints c)) q) := by
  have := compactSpace_of_isProjective hc
  have : IsSeparated c := hc.isSeparated
  exact RiemannSurface.subsingleton_H_holomorphicSheafAb (ComplexPoints c) q hq

/-- `H^n(C(ℂ), A) = 0` for `n ≥ 3` and every abelian group `A`, for `C` a smooth projective curve
over `ℂ`, in any `Ext` universe. -/
theorem subsingleton_H_constantSheaf_of_isProjective (hc : IsProjective c)
    (A : AddCommGrpCat.{0}) {n : ℕ} (hn : 3 ≤ n) :
    Subsingleton (Sheaf.H.{w'} ((constantSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoints c))) AddCommGrpCat.{0}).obj A) n) := by
  rcases isEmpty_or_nonempty C with hC | hC
  · have : IsEmpty (ComplexPoints c) :=
      ⟨fun p => isEmptyElim (p.hom (Classical.arbitrary (Spec (.of ℂ))))⟩
    exact Ext.subsingleton_of_isZero_right _
      (TopCat.Sheaf.isZero_of_isEmpty (TopCat.of (ComplexPoints c)) _) n
  · have hdim : topologicalKrullDim C = 1 := by
      exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 c
    have := SmoothOfRelativeDimension.smooth 1 c
    have h := subsingleton_analyticCohomologyConstant_of_smooth_of_isProjective c hc hdim A hn
    let _ := IsGrothendieckAbelian.hasExt.{0}
      (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints c))) AddCommGrpCat.{0})
    exact (Equiv.subsingleton_congr Ext.chgUniv.{w', 0}).1 h

/-- **`H^q(C(ℂ), 𝒪^×) = 0` for `q ≥ 2`**, for `C` a smooth projective curve over `ℂ`: the
cohomology of the sheaf of nowhere vanishing holomorphic functions on the compact Riemann
surface `C(ℂ)` vanishes in degrees at least two. -/
theorem subsingleton_H_holomorphicUnitsSheaf_of_isProjective (hc : IsProjective c) {q : ℕ}
    (hq : 2 ≤ q) :
    Subsingleton
      (Sheaf.H.{w'} (ComplexManifold.holomorphicUnitsSheaf 𝓘(ℂ) (ComplexPoints c)) q) :=
  ComplexManifold.subsingleton_H_holomorphicUnitsSheaf_of_subsingleton _ _ q
    (subsingleton_H_holomorphicSheafAb_of_isProjective c hc hq)
    (subsingleton_H_constantSheaf_of_isProjective c hc _ (by omega))

end AlgebraicGeometry.Scheme.ComplexPoints
