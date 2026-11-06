module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormulaFinal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTraceFormulaPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius

/-!
# The trace formula for the sheaf of the trivial representation

Let `X` be a connected Noetherian scheme, separated of finite type over a finite field `k` with
`p ^ q` elements, `k̄` an algebraic closure of `k`, `ℓ ≠ p` a prime and `ℱ_1` the lisse ℓ-adic
sheaf of the trivial representation `1 : π₁(X, x̄) → GL_r(ℚ_ℓ)`. At every closed point `y` the
geometric Frobenius acts on the stalk of `ℱ_1` with characteristic polynomial `(T - 1) ^ r`, so
each of its powers has trace `r`. The trace formula for the powers of Frobenius therefore reads

`∑ᵢ (-1)ⁱ Tr((π_X^*)^N | Hⁱ_c(X_k̄, ℱ_1)) = r · ∑_{deg y ∣ N} deg y`

for every `N ≥ 1`; for `r = 1` the right hand side is the number of points of `X` over the
extension of degree `N` of `k`.

## Main results

* `Stacks.EtaleCohomology.LinearMap.trace_pow_of_charpoly_eq_X_sub_one_pow`: an endomorphism
  with characteristic polynomial `(T - 1) ^ r` has all powers of trace `r`.
* `Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_pow_rationalFrobenius_representationSheaf_one`:
  the trace formula for `(π_X^*)^N` on `ℱ_1`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- An endomorphism `φ` of a finite dimensional vector space whose characteristic polynomial is
`(T - 1) ^ r` has `Tr(φ ^ m) = r` for every `m`: `φ - 1` is nilpotent by Cayley–Hamilton, so
`φ ^ m - 1` is nilpotent and has trace zero, and the dimension is the degree `r`. -/
theorem LinearMap.trace_pow_of_charpoly_eq_X_sub_one_pow {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (φ : Module.End K V) {r : ℕ}
    (h : φ.charpoly = (Polynomial.X - 1) ^ r) (m : ℕ) :
    LinearMap.trace K V (φ ^ m) = r := by
  have hdim : Module.finrank K V = r := by
    rw [← LinearMap.charpoly_natDegree φ, h, natDegree_pow, ← C_1, natDegree_X_sub_C, mul_one]
  have hnil : IsNilpotent (φ - 1) := by
    refine ⟨r, ?_⟩
    have := LinearMap.aeval_self_charpoly φ
    rwa [h, map_pow, map_sub, aeval_X, map_one] at this
  have hnil' : IsNilpotent (φ ^ m - 1) := by
    rw [← geom_sum_mul]
    exact Commute.isNilpotent_mul_left (Commute.sub_right (Commute.sum_left _ _ _
      fun i _ => (Commute.refl φ).pow_left i) (Commute.one_right _)) hnil
  have h0 := (LinearMap.isNilpotent_trace_of_isNilpotent hnil').eq_zero
  rwa [map_sub, LinearMap.trace_one, hdim, sub_eq_zero] at h0

section Stalk

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- The geometric Frobenius at a closed point `y` acts on the stalk of the sheaf `ℱ_1` of the
trivial representation with characteristic polynomial `(T - 1) ^ r`. -/
theorem LAdicSheaf.charpoly_rationalStalkFrobenius_representationSheaf_one
    (y : closedPoints X.1) :
    (LAdicSheaf.rationalStalkFrobenius B X ℓ
        (LAdicSheaf.representationSheaf B X x (1 : EtaleFundamentalGroup X.1 x →*
          GL (Fin r) ℚ_[ℓ]) continuous_const) y.1
        (finite_residueField f y.1 y.2)).charpoly = (Polynomial.X - 1) ^ r := by
  rw [charpoly_rationalStalkFrobenius_representationSheaf_eq B X x f _ continuous_const y]
  simp [Matrix.charpoly_one]

end Stalk

section TrivialRepresentation

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsNoetherian X.1]

/-- **The trace formula for the powers of Frobenius on the sheaf of the trivial representation.**
Let `X` be a connected Noetherian scheme, separated of finite type over a finite field `k` with
`p ^ q` elements, `k̄` an algebraic closure of `k`, `ℓ ≠ p` a prime and `ℱ_1` the lisse ℓ-adic
sheaf of the trivial representation `1 : π₁(X, x̄) → GL_r(ℚ_ℓ)`. Then for every `N ≥ 1`,
`∑ᵢ (-1)ⁱ Tr((π_X^*)^N | Hⁱ_c(X_k̄, ℱ_1)) = r · ∑_{deg y ∣ N} deg y`, the sum over the closed
points `y` of `X`. -/
theorem LAdicSheaf.finsum_trace_pow_rationalFrobenius_representationSheaf_one (hℓp : ℓ ≠ p)
    (N : ℕ) (hN : N ≠ 0) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
        ((LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
          (LAdicSheaf.representationSheaf B X x (1 : EtaleFundamentalGroup X.1 x →*
            GL (Fin r) ℚ_[ℓ]) continuous_const) i).hom ^ N) =
      ((r * ∑ᶠ (y : closedPoints X.1) (_ : residueDegree f y.1 ∣ N), residueDegree f y.1 : ℕ) :
        ℚ_[ℓ]) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  rw [← LAdicSheaf.finsum_trace_pow_eq_of_traceFormula B X ℓ f j kbar p q hcard _
    (fun k' _ _ _ _ _ _ _ _ q' hcard' => ?_) N hN]
  · classical
    have hfin : (Function.support fun y : closedPoints X.1 =>
        if residueDegree f y.1 ∣ N then residueDegree f y.1 else 0).Finite := by
      refine (finite_setOf_closedPoints_residueDegree_le f N).subset fun y hy => ?_
      have hd : residueDegree f y.1 ∣ N := by
        by_contra hd
        exact hy (by simp [hd])
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hd
    simp only [finsum_eq_if]
    have hcast : ((∑ᶠ y : closedPoints X.1,
        r * if residueDegree f y.1 ∣ N then residueDegree f y.1 else 0 : ℕ) : ℚ_[ℓ]) =
        ∑ᶠ y : closedPoints X.1,
          ((r * if residueDegree f y.1 ∣ N then residueDegree f y.1 else 0 : ℕ) : ℚ_[ℓ]) :=
      (Nat.castAddMonoidHom ℚ_[ℓ]).map_finsum
        (hfin.subset (Function.support_mul_subset_right _ _))
    rw [mul_finsum, hcast]
    refine finsum_congr fun y => ?_
    split_ifs
    · rw [LinearMap.trace_pow_of_charpoly_eq_X_sub_one_pow _
        (LAdicSheaf.charpoly_rationalStalkFrobenius_representationSheaf_one B X x ℓ r f y)]
      simp [mul_comm]
    · simp
  · have : IsAlgClosure k' kbar := ⟨this, Algebra.IsAlgebraic.tower_top (K := k) k'⟩
    exact (LAdicSheaf.traceFormula B (fieldExtensionScheme B X f k') ℓ
      (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p q'
      hcard' hℓp _).2.2

end TrivialRepresentation

end Stacks.EtaleCohomology

end
