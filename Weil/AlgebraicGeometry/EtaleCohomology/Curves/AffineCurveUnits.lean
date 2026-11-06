module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurveRank
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible
public import Weil.Attr

/-!
# The units of an affine smooth curve modulo `n`-th powers

Let `k` be an algebraically closed field, `n ≥ 1`, and `X` an affine smooth connected curve over
`k`. Then the cokernel of the `n`-th power map on `Γ(X, 𝒪_X)^*` is finite.

The proof is the classical one. `X` is integral (smooth and connected), so it has a smooth
projective compactification `X ⊆ X̄` with `X̄ ∖ X = {x₀, …, x_r}` a nonempty finite set of closed
points. The orders of vanishing at the punctures give a homomorphism `Γ(X, 𝒪_X)^* → ℤ^{r+1}`
whose kernel consists of the constants `k^*` (Hartogs on the normal curve `X̄` and
`Γ(X̄, 𝒪_{X̄}) = k`), all of which are `n`-th powers since `k` is algebraically closed. A group
`A` with a homomorphism to a finitely generated free abelian group whose kernel is contained in
`nA` has `A/nA` embedded in `R/nR`, `R` the (finitely generated) image, and `R/nR` is finite.

## Main results

* `AlgebraicGeometry.finite_quotient_nsmul_of_ker_le`: the group-theoretic step.
* `AlgebraicGeometry.finite_units_quotient_powMonoidHom_range`: the cokernel of the `n`-th power
  map on the units of an affine smooth connected curve over an algebraically closed field is
  finite.

## Implementation notes

The ingredients about the compactification are those of [Stacks, Tag 03RR]: the compactification
is [Stacks, Tag 0H1F], the orders at the punctures are
`AlgebraicGeometry.AffineCurveRankData.ordHom`, and the fact that a unit with all orders zero is
an `n`-th power is `AlgebraicGeometry.AffineCurveRankData.exists_nsmul_eq_of_ordHom_eq_zero`.
No hypothesis on `n` beyond `n ≥ 1` is needed.

## References

* [FK, Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5]
* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.AffineCurveRankData

universe u

namespace AlgebraicGeometry

/-- **`A/nA` is finite** when `A` maps to `ℤ^m` with kernel contained in `nA`: `A/nA` embeds in
`R/nR`, where `R ⊆ ℤ^m` is the image, a finitely generated group. -/
theorem finite_quotient_nsmul_of_ker_le {A : Type*} [AddCommGroup A] {m n : ℕ} (hn : 0 < n)
    (φ : A →+ (Fin m → ℤ)) (hker : ∀ a, φ a = 0 → ∃ v, a = n • v) :
    Finite (A ⧸ (n • AddMonoidHom.id A).range) := by
  set R := φ.range
  set N : AddSubgroup R := (n • AddMonoidHom.id R).range
  have hRfg : AddGroup.FG R := by
    have : Module.Finite ℤ R.toIntSubmodule := Module.IsNoetherian.finite ℤ _
    exact Module.Finite.iff_addGroup_fg.mp this
  have hfin : Finite (R ⧸ N) := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun x => ?_
    induction x using QuotientAddGroup.induction_on with
    | H r =>
      refine (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨n, hn, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨r, rfl⟩
  let ψ : A →+ R ⧸ N := (QuotientAddGroup.mk' N).comp φ.rangeRestrict
  have hle : (n • AddMonoidHom.id A).range ≤ ψ.ker := by
    rintro _ ⟨b, rfl⟩
    rw [AddMonoidHom.mem_ker]
    simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, map_nsmul, ψ]
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨_, rfl⟩
  let ψ' := QuotientAddGroup.lift _ ψ hle
  refine Finite.of_injective ψ' ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    change ψ a = 0 at hx
    obtain ⟨⟨_, ⟨b, rfl⟩⟩, hb⟩ := (QuotientAddGroup.eq_zero_iff _).1 hx
    have hab : φ (a - n • b) = 0 := by
      have := congrArg Subtype.val hb
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, AddSubgroup.coe_nsmul] at this
      rw [map_sub, map_nsmul, this, AddMonoidHom.coe_rangeRestrict, sub_self]
    obtain ⟨v, hv⟩ := hker _ hab
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨b + v, by simp [← hv]⟩

/-- `G/G^n` is finite when `Additive G / n • Additive G` is. -/
theorem finite_quotient_powMonoidHom_range_of_additive {G : Type*} [CommGroup G] (n : ℕ)
    (h : Finite (Additive G ⧸ (n • AddMonoidHom.id (Additive G)).range)) :
    Finite (G ⧸ (powMonoidHom n : G →* G).range) := by
  let F : Additive G ⧸ (n • AddMonoidHom.id (Additive G)).range →
      G ⧸ (powMonoidHom n : G →* G).range :=
    Quotient.map' (fun a : Additive G => a.toMul) fun a b hab => by
      rw [QuotientAddGroup.leftRel_apply] at hab
      rw [QuotientGroup.leftRel_apply]
      obtain ⟨c, hc⟩ := hab
      refine ⟨c.toMul, ?_⟩
      have := congrArg Additive.toMul hc
      simpa [toMul_nsmul] using this
  refine Finite.of_surjective F ?_
  · intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨QuotientAddGroup.mk (Additive.ofMul g), rfl⟩

/-- **The cokernel of the `n`-th power map on the units of an affine smooth connected curve over
an algebraically closed field is finite.** Here `X` is a smooth `k`-scheme which is connected,
affine and of dimension one, and `n ≥ 1` is arbitrary. -/
@[weil "lem_fk105_affine_curve_unit_cokernel_finite"]
theorem finite_units_quotient_powMonoidHom_range (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsAffine X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1) {n : ℕ} (hn : 0 < n) :
    Finite (Γ(X, ⊤)ˣ ⧸ (powMonoidHom n : Γ(X, ⊤)ˣ →* Γ(X, ⊤)ˣ).range) := by
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
  have : IsDominant j := isDominant_of_isOpenImmersion_of_isIntegral j
  obtain ⟨r', -, x, hxinj, hxS, hxg⟩ := exists_punctures k f q j hjq _ rfl
  exact finite_quotient_powMonoidHom_range_of_additive n
    (finite_quotient_nsmul_of_ker_le hn (ordHom j x)
      (exists_nsmul_eq_of_ordHom_eq_zero k f q j x hxinj hxS hxg hn))

end AlgebraicGeometry
