module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.Curves.SmoothCurveHIGmVanish
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.CohomologySequence

/-!
# Higher vanishing for the roots of unity on a smooth curve

Let `k` be an algebraically closed field, `X` a smooth curve over `k` (separated, quasi-compact,
smooth of relative dimension one, not assumed connected, complete or affine) and `n ≥ 1` an
integer invertible in `k`. Then `H^q_étale(X, μ_n) = 0` for every `q > 2`.

Since `n` is a unit of `k`, it is a unit of `Γ(X, 𝒪_X)`, so the Kummer sequence
`0 → μ_n → 𝐆_m → 𝐆_m → 0` is exact on the small étale site. Its long exact cohomology sequence
contains the exact segment `H^{q-1}(X, 𝐆_m) → H^q(X, μ_n) → H^q(X, 𝐆_m)`, whose outer terms
vanish for `q > 2` because `H^i(X, 𝐆_m) = 0` for `i ≥ 2` on a smooth curve.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_rootsOfUnitySheaf_of_smoothOfRelativeDimension_one`:
  `H^q_étale(X, μ_n) = 0` for `q > 2` on a smooth curve over an algebraically closed field.

## Implementation notes

The sheaves `μ_n` and `𝐆_m` are `Stacks.Kummer.rootsOfUnitySheaf X n` and
`Stacks.Kummer.multiplicativeSheaf X` on Mathlib's small étale site `X.smallEtaleTopology`, with
coefficients in `AddCommGrpCat.{max (u + 1) v}` and cohomology in any `Ext` universe, as for the
vanishing of `H^q(X, 𝐆_m)` it is deduced from. The curve need not be connected; for an integral
curve the statement is [Stacks, Tag 03RQ], the clause `q ≥ 3`
(`Stacks.Kummer.subsingleton_sheafH_rootsOfUnitySheaf_of_isCurve`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Higher vanishing for `μ_n` on a smooth curve.** Let `X` be a smooth curve over an
algebraically closed field `k` (`f : X ⟶ Spec k` separated, quasi-compact and smooth of relative
dimension one, `X` not necessarily connected) and let `n` be invertible in `k`. Then
`H^q_étale(X, μ_n) = 0` for every `q > 2`. -/
@[weil "lem_fk105_smooth_curve_hq_mu_n_vanish_q_gt_2"]
theorem subsingleton_sheafH_rootsOfUnitySheaf_of_smoothOfRelativeDimension_one
    [IsSeparated f] [QuasiCompact f] [SmoothOfRelativeDimension 1 f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {n : ℕ} (hn : IsUnit (n : k)) (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{w} (Stacks.Kummer.rootsOfUnitySheaf.{u, v} X n) q) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hX : IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hn.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  exact Stacks.Kummer.subsingleton_sheafH_rootsOfUnitySheaf X hn0 hX p
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one f p (by omega))
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothOfRelativeDimension_one f (p + 1)
      (by omega))

end AlgebraicGeometry
