module

public import Weil.Attr
public import Weil.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnitySecondCohomology

/-!
# `H²(X, μ_n)` of a smooth curve is `Pic X / n Pic X`

Let `X` be a smooth curve over an algebraically closed field `k` and `n ≥ 1` an integer
invertible in `k`. The Kummer sequence gives the exact sequence
`Pic X →ⁿ Pic X → H²(X, μ_n) → 0`
(`Stacks.Kummer.exact_globalUnits_sheafH_rootsOfUnity_picard_of_smoothCurve`), so the Kummer
boundary `Pic X → H²(X, μ_n)` is onto with kernel `n Pic X`, and it induces an isomorphism
`Pic X / n Pic X ≅ H²(X, μ_n)`.

## Main definitions

* `Stacks.Kummer.picardQuotientAddEquivSheafHTwoRootsOfUnity`: the isomorphism
  `Coker(Pic X →ⁿ Pic X) ≅ H²(X, μ_n)` induced by the Kummer boundary.

## Main results

* `Stacks.Kummer.picardQuotientAddEquivSheafHTwoRootsOfUnity_mk`: the isomorphism is induced by
  `Stacks.Kummer.picardToSheafHTwoRootsOfUnity`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I, §5.
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe w v u

namespace Stacks.Kummer

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f]
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {n : ℕ} (hn : IsUnit (n : k))

/-- **`H²(X, μ_n) ≅ Pic X / n Pic X` on a smooth curve.** Let `X` be a smooth curve over an
algebraically closed field `k` and `n ≥ 1` invertible in `k`. The Kummer boundary
`Pic X → H²(X, μ_n)` induces an isomorphism from the cokernel of multiplication by `n` on
`Pic X` onto `H²(X, μ_n)`. -/
@[weil "lem_fk105_smooth_curve_h2_mu_n_coker_n_pic"]
def picardQuotientAddEquivSheafHTwoRootsOfUnity :
    Picard.ofScheme X ⧸ (nsmulAddMonoidHom n : Picard.ofScheme X →+ Picard.ofScheme X).range ≃+
      Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} X n) 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq
      ((exact_globalUnits_sheafH_rootsOfUnity_picard_of_smoothCurve.{w, v, u} f hn).2.2.2.1
        |>.addMonoidHom_ker_eq).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (exact_globalUnits_sheafH_rootsOfUnity_picard_of_smoothCurve.{w, v, u} f hn).2.2.2.2)

/-- The isomorphism `Pic X / n Pic X ≅ H²(X, μ_n)` sends the class of `[ℒ]` to its Kummer
boundary. -/
@[weil "lem_fk105_smooth_curve_h2_mu_n_coker_n_pic"]
theorem picardQuotientAddEquivSheafHTwoRootsOfUnity_mk (p : Picard.ofScheme X) :
    picardQuotientAddEquivSheafHTwoRootsOfUnity.{w, v, u} f hn (QuotientAddGroup.mk p) =
      picardToSheafHTwoRootsOfUnity.{w, v, u} X (ne_zero_of_isUnit_natCast hn)
        (isUnit_natCast_globalSections X n f hn) p :=
  rfl

end Stacks.Kummer

end
