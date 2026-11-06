module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityCurvesFinal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Projective

/-!
# Vanishing of `H²(X, μ_n)` on an affine smooth curve

Let `k` be an algebraically closed field, `n ≥ 1` an integer prime to the characteristic of `k`,
and `X` an affine smooth connected curve over `k`. Then `H^q_ét(X, μ_n) = 0` for every `q ≥ 2`;
in particular `H²_ét(X, μ_n) = 0`.

Here `μ_n` is the kernel of the `n`-th power map of the Kummer sequence `μ_n ⟶ 𝐆_m ⟶ 𝐆_m` on the
small étale site of `X` cut out of a big étale site, `(AlgebraicGeometry.kummerSmallEtale E X hX
n).X₁`, and a connected smooth curve is an integral one (`AlgebraicGeometry.IsCurve`).

## Main results

* `AlgebraicGeometry.subsingleton_etaleH_rootsOfUnity_of_isAffine_of_two_le`:
  `H^q_ét(X, μ_n) = 0` for `q ≥ 2`.
* `AlgebraicGeometry.subsingleton_etaleH_two_rootsOfUnity_of_isAffine`: `H²_ét(X, μ_n) = 0`.

## Implementation notes

The source deduces the vanishing from `H²(X, μ_n) ≅ Pic(X)/n Pic(X)` and the `n`-divisibility of
`Pic(X)` for an affine curve. We obtain it from clause (3) of [Stacks, Tag 03RR], which takes a
smooth projective compactification of `X` as data; that compactification exists by
[Stacks, Tag 0H1F], `X` being regular because it is smooth over a field and `k` being perfect.
The hypothesis "`n ≥ 1` prime to the characteristic" is written `IsUnit (n : k)`, which is
equivalent to it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I, §5.
* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Tag 0H1F](https://stacks.math.columbia.edu/tag/0H1F)
-/

@[expose] public section

open CategoryTheory

universe t u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsAffine X] (E : BigEtaleSite.{u}) (hX : E.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]

include f in
/-- **The étale cohomology of `μ_n` on an affine smooth curve vanishes in degrees `q ≥ 2`.**
Let `k` be algebraically closed, `n` invertible in `k` and `X` an affine smooth curve over `k`.
Then `H^q_ét(X, μ_n) = 0` for every `q ≥ 2`. -/
theorem subsingleton_etaleH_rootsOfUnity_of_isAffine_of_two_le (hn : IsUnit (n : k))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ q) := by
  obtain ⟨-, Y, p, j, hj, hjp, hcurve, hproj, -, hsmooth, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k f
      (isRegular_of_smooth_over_field f)
  have : IsOpenImmersion j := hj
  have : IsCurve k p := hcurve
  have : Smooth p := hsmooth
  have : IsProjectiveVariety k p := (isProjectiveVariety_iff_isProjectiveMorphism k p).2 hproj
  exact (etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification k X f E hX n hn p j
    hjp _ rfl).2.2 q hq

include f in
/-- **`H²(X, μ_n) = 0` for an affine smooth connected curve.** Let `k` be an algebraically closed
field, `n ≥ 1` an integer prime to the characteristic of `k` (that is, `n` invertible in `k`),
and `X` an affine smooth connected curve over `k`. Then `H²_ét(X, μ_n) = 0`. -/
@[weil "lem_fk105_affine_curve_h2_mu_n_vanish"]
theorem subsingleton_etaleH_two_rootsOfUnity_of_isAffine (hn : IsUnit (n : k)) :
    Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ 2) :=
  subsingleton_etaleH_rootsOfUnity_of_isAffine_of_two_le k X f E hX n hn 2 le_rfl

end AlgebraicGeometry

end

/-! ### Finiteness of `H¹_ét(X, μ_n)` on an affine smooth curve -/

/-!
# Finiteness of `H¹_ét(X, μ_n)` on an affine smooth curve

Let `k` be an algebraically closed field, `n ≥ 1` an integer invertible in `k`, and `X` an affine
smooth curve over `k`. Then the étale cohomology group `H¹_ét(X, μ_n)` is finite.

## Main results

* `AlgebraicGeometry.finite_etaleH1_rootsOfUnity_affineSmoothCurve`: `H¹_ét(X, μ_n)` is finite.

## Implementation notes

The roots-of-unity sheaf `μ_n` is the kernel term `(kummerSmallEtale E X hX n).X₁` of the Kummer
sequence on the small étale site `SmallEtale.topology E X hX` cut out of a big étale site `E`.

The source deduces finiteness from the exact sequence
`Γ(X, 𝒪_X)ˣ →ⁿ Γ(X, 𝒪_X)ˣ → H¹(X, μ_n) → Pic X →ⁿ Pic X`, finiteness of `Pic(X)[n]` and of the
cokernel of the `n`-th power map on the global units. Here the stronger statement
`H¹_ét(X, μ_n) ≅ (𝐙/n𝐙)^{2g + r - 1}` ([Stacks, Tag 03RR]) is used instead, applied to the
smooth projective compactification of `X` ([Stacks, Tag 0H1F]); both routes go through the same
exact sequence.

A smooth connected curve over a field is integral, so "smooth connected curve" is expressed by
`IsCurve k f` (an integral separated scheme of finite type of dimension one) together with
`Smooth f`. The hypothesis "`n` prime to the characteristic of `k`, `n ≥ 1`" is `IsUnit (n : k)`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5.
* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Tag 0H1F](https://stacks.math.columbia.edu/tag/0H1F)
-/

@[expose] public section

open CategoryTheory

universe t u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsAffine X] (E : BigEtaleSite.{u}) (hX : E.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]

include f in
/-- **`H¹_ét(X, μ_n)` is finite** for an affine smooth curve `X` over an algebraically closed
field `k` and `n` invertible in `k`. -/
@[weil "lem_fk105_affine_curve_h1_mu_n_finite"]
theorem finite_etaleH1_rootsOfUnity_affineSmoothCurve (hn : IsUnit (n : k)) :
    Finite (Sheaf.H (kummerSmallEtale E X hX n).X₁ 1) := by
  obtain ⟨-, Y, q, j, hj, hjq, hcY, hpY, -, hsY, -, -⟩ :=
    exists_smooth_isProjectiveMorphism_compactification_of_perfectField k f
      (isRegular_of_smooth_over_field f)
  have := hcY
  have := hsY
  have := hj
  have : IsProjectiveVariety k q := (isProjectiveVariety_iff k q).mpr ⟨inferInstance, hpY⟩
  have hn0 : NeZero n := ⟨fun h => by simp [h] at hn⟩
  obtain ⟨-, ⟨e⟩, -⟩ := etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification k X f
    E hX n hn q j hjq _ rfl
  exact Finite.of_equiv _ e.toEquiv.symm

end AlgebraicGeometry
