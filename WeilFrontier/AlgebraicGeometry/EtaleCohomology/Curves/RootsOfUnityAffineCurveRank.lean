module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurveRank
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurvePicardScheme
public import StacksFrontier.AlgebraicGeometry.Picard.PicardSchemeCurve
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible
public import Weil.Attr

/-!
# Multiplication by `n` on the Picard group of an affine curve is surjective

Let `k` be an algebraically closed field, `n ≥ 1`, and `X` an affine smooth connected curve over
`k`. Then every class in `Pic(X)` is divisible by `n`.

The proof is the classical one. Let `X ⊆ X̄` be the smooth projective compactification. Since `X`
is affine it is not proper, so `X̄ ∖ X` contains a closed point `x₀`. Every class of `Pic(X)` is
the restriction of a class `p` of `Pic(X̄)`, and `p - (deg p) [𝒪(x₀)]` has the same restriction
and lies in `Pic⁰(X̄)`. The latter is the group of `k`-points of the Jacobian `Pic⁰_{X̄/k}`, an
abelian variety, whose group of rational points is divisible over an algebraically closed field.

## Main results

* `AlgebraicGeometry.exists_nsmul_eq_curvePicardDegreeZero_of_isAlgClosed`: `Pic⁰(X̄)` of a smooth
  projective curve over an algebraically closed field is divisible by every `n ≥ 1`.
* `AlgebraicGeometry.surjective_nsmul_schemePicard_of_isAffine`: multiplication by `n ≥ 1` on
  `Pic(X)` of an affine smooth connected curve over an algebraically closed field is surjective.

## Implementation notes

The divisibility of `Pic⁰(X̄)` is proved for every `n ≥ 1`, not only for `n` invertible in `k`:
it uses that multiplication by a nonzero integer on an abelian variety is surjective
(`Stacks.Groupoids.exists_pow_eq`) rather than its flatness.

## References

* [FK, Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5]
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Stacks.PicardFunctor Stacks.AbelMap
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- **`Pic⁰(X̄)` is divisible**: for a smooth projective curve `X̄` over an algebraically closed
field `k` and every `n ≥ 1`, every degree-zero class is `n` times a class. -/
theorem exists_nsmul_eq_curvePicardDegreeZero_of_isAlgClosed (k : Type u) [Field k]
    [IsAlgClosed k] {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar]
    [Smooth fbar] [IsProjectiveVariety k fbar] {n : ℕ} (hn : n ≠ 0) :
    ∀ x ∈ curvePicardDegreeZero k Xbar fbar, ∃ y, n • y = x := by
  obtain ⟨B, hXb, hk, fb, hfb, ⟨σ, hσ⟩, hgi⟩ := exists_bigFppfSite_picardData fbar
  subst hfb
  obtain ⟨hrep, hproper, hsmooth, hint, -⟩ :=
    picardDegreeZero_inputs_of_isSepClosed B hXb hk fb σ hσ
  have := isAbelianVariety_picardDegreeZero B hXb hk fb σ hσ hproper hsmooth hint
  intro x hx
  obtain ⟨a, ha⟩ := (bijective_picardDegreeZeroPoints B hXb hk fb σ hσ).2 ⟨x, hx⟩
  obtain ⟨b, rfl⟩ := Stacks.Groupoids.exists_pow_eq k
    (picardDegreeZeroSubgroup B hXb hk fb σ hσ).carrier.X n hn a
  have hpow : ∀ m : ℕ, picardDegreeZeroPoints B hXb hk fb σ hσ (b ^ m) =
      m • picardDegreeZeroPoints B hXb hk fb σ hσ b := by
    have h1 : picardDegreeZeroPoints B hXb hk fb σ hσ 1 = 0 := by
      have h := picardDegreeZeroPoints_mul B hXb hk fb σ hσ 1 1
      rw [mul_one] at h
      exact left_eq_add.mp h
    intro m
    induction m with
    | zero => rw [pow_zero, h1, zero_smul]
    | succ m ih => rw [pow_succ, picardDegreeZeroPoints_mul, ih, succ_nsmul]
  refine ⟨(picardDegreeZeroPoints B hXb hk fb σ hσ b).1, ?_⟩
  have h := congrArg Subtype.val ha
  rw [hpow] at h
  simpa using h

/-- **Multiplication by `n` on the Picard group of an affine curve is surjective.** Let `k` be an
algebraically closed field, `n ≥ 1`, and `X` an affine smooth connected `k`-scheme of dimension
one. Then `Pic(X) → Pic(X)`, `c ↦ n c`, is surjective. -/
@[weil "lem_fk105_affine_curve_multiplication_n_pic_surjective"]
theorem surjective_nsmul_schemePicard_of_isAffine (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsAffine X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1) {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective fun c : schemePicard X => n • c := by
  have : IrreducibleSpace X := irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace f
  have : IsNormal X := isNormal_of_smooth_over_field f
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have : IsCurve k f := { toIsVariety := { }, topologicalKrullDim_eq_one := hdim }
  obtain ⟨-, Y, q, j, hj, hjq, hq, hproj, -, hqs, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k f
      (isRegular_of_smooth_over_field f)
  have := hj
  have := hq
  have := hqs
  have : IsProjectiveVariety k q := { isProjective := hproj }
  have : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have : IsNoetherian X := AffineCurveRankData.isNoetherian k f
  have : IsNoetherian Y := AffineCurveRankData.isNoetherian k q
  intro c
  obtain ⟨y, hy⟩ := exists_nsmul_eq_schemePicard_of_picardDegreeZero k f q j hjq n
    (exists_nsmul_eq_curvePicardDegreeZero_of_isAlgClosed k q (by omega)) c
  exact ⟨y, hy.symm⟩

end AlgebraicGeometry
