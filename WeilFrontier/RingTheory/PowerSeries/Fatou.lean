module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.Algebra.Field.ZMod

/-!
# Fatou's lemma and a Gauss lemma for polynomials with constant term one

Let `Z ∈ ℤ⟦X⟧` with constant term `1`. If `Z` is rational over `ℚ`, i.e. `B₀ * Z = A₀` for
polynomials `A₀, B₀ ∈ ℚ[X]` with `B₀ ≠ 0`, then (Fatou's lemma) `Z` is already the quotient of two
integer polynomials `A, B ∈ ℤ[X]` with constant term `1` that are coprime over `ℚ`.

The proof first divides `A₀` and `B₀` by their greatest common divisor, and then scales the
denominator to a primitive integer polynomial `B₁`. The numerator `A₁ = B₁ * Z` then has integer
coefficients, and a Bézout relation `U * A₁ + V * B₁ = m` with `m ∈ ℤ ∖ {0}` gives
`B₁ * W = m` in `ℤ⟦X⟧`. Reducing modulo a prime `p` dividing `B₁(0)` and using that `𝔽_p⟦X⟧` is a
domain leads to a contradiction (by induction on `|m|`), so `B₁(0) = ±1`.

We also prove a Gauss lemma: a factor `r ∈ ℚ[X]` with `r(0) = 1` of an integer polynomial with
constant term `1` has integer coefficients.

## Main results

* `PowerSeries.exists_int_coprime_mul_eq_of_rat`: Fatou's lemma.
* `Polynomial.exists_map_eq_of_dvd_of_coeff_zero_eq_one`: a rational factor with constant
  term `1` of an integer polynomial with constant term `1` is integral.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

@[expose] public section

open Polynomial
open scoped PowerSeries

/-- Clearing denominators of a rational polynomial. -/
private lemma exists_int_map_eq_C_mul (r : ℚ[X]) :
    ∃ b : ℤ, b ≠ 0 ∧ ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = C (b : ℚ) * r := by
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) r
  refine ⟨b, nonZeroDivisors.ne_zero hb,
    IsLocalization.integerNormalization (nonZeroDivisors ℤ) r, ?_⟩
  rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hq, zsmul_eq_mul, ← C_eq_intCast]

/-- A nonzero rational polynomial is a nonzero multiple of a primitive integer polynomial. -/
private lemma exists_isPrimitive_map_eq_C_mul {r : ℚ[X]} (hr : r ≠ 0) :
    ∃ c : ℚ, c ≠ 0 ∧ ∃ p : ℤ[X], p.IsPrimitive ∧ p.map (Int.castRingHom ℚ) = C c * r := by
  obtain ⟨b, hb, q, hq⟩ := exists_int_map_eq_C_mul r
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero, eq_comm, mul_eq_zero, C_eq_zero] at hq
    exact hq.elim (fun h => hb (by exact_mod_cast h)) hr
  have hc0 : q.content ≠ 0 := by rwa [Ne, content_eq_zero_iff]
  refine ⟨(b : ℚ) / q.content, div_ne_zero (by exact_mod_cast hb) (by exact_mod_cast hc0),
    q.primPart, isPrimitive_primPart q, ?_⟩
  have h := hq
  rw [eq_C_content_mul_primPart q, Polynomial.map_mul, map_C, eq_intCast] at h
  have hc : (q.content : ℚ) ≠ 0 := by exact_mod_cast hc0
  apply mul_left_cancel₀ (show C (q.content : ℚ) ≠ 0 by rwa [Ne, C_eq_zero])
  rw [h, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ hc]

/-- A power series with integer coefficients that is a polynomial over `ℚ` is a polynomial
over `ℤ`. -/
private lemma exists_polynomial_of_map_eq {f : ℤ⟦X⟧} {P : ℚ[X]}
    (h : PowerSeries.map (Int.castRingHom ℚ) f = P) :
    ∃ Q : ℤ[X], (Q : ℤ⟦X⟧) = f ∧ Q.map (Int.castRingHom ℚ) = P := by
  have hQ : ((PowerSeries.trunc (P.natDegree + 1) f : ℤ[X]) : ℤ⟦X⟧) = f := by
    ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · have : ((PowerSeries.coeff n f : ℤ) : ℚ) = 0 := by
        rw [← eq_intCast (Int.castRingHom ℚ), ← PowerSeries.coeff_map, h, Polynomial.coeff_coe]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
      exact_mod_cast this.symm
  refine ⟨_, hQ, ?_⟩
  rw [← Polynomial.coe_inj, polynomial_map_coe, hQ, h]

/-- An integer Bézout relation for integer polynomials coprime over `ℚ`. -/
private lemma exists_int_bezout {P Q : ℤ[X]}
    (h : IsCoprime (P.map (Int.castRingHom ℚ)) (Q.map (Int.castRingHom ℚ))) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ U V : ℤ[X], U * P + V * Q = C m := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨b₁, hb₁, U, hU⟩ := exists_int_map_eq_C_mul u
  obtain ⟨b₂, hb₂, V, hV⟩ := exists_int_map_eq_C_mul v
  refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, C b₂ * U, C b₁ * V, ?_⟩
  apply Polynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_C, hU, hV]
  simp only [eq_intCast, Int.cast_mul, C_mul]
  linear_combination (C (b₁ : ℚ) * C (b₂ : ℚ)) * huv

/-- If `B₁ * W = m` in `ℤ⟦X⟧` with `B₁` primitive and `m ≠ 0`, then no prime divides `B₁(0)`. -/
private lemma not_dvd_coeff_zero_of_mul_eq_C {B₁ : ℤ[X]} (hB : B₁.IsPrimitive) {p : ℕ}
    (hp : p.Prime) : ∀ (m : ℤ), m ≠ 0 → ∀ W : ℤ⟦X⟧, (B₁ : ℤ⟦X⟧) * W = PowerSeries.C m →
      ¬ (p : ℤ) ∣ B₁.coeff 0 := by
  have := Fact.mk hp
  intro m
  induction hn : m.natAbs using Nat.strong_induction_on generalizing m with
  | _ n ih =>
  intro hm W h hdvd
  by_cases hpm : (p : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hpm
    have hm' : m' ≠ 0 := right_ne_zero_of_mul hm
    -- `B₁` does not vanish modulo `p`
    have hB₁ : PowerSeries.map (Int.castRingHom (ZMod p)) (B₁ : ℤ⟦X⟧) ≠ 0 := by
      intro h0
      have : Polynomial.C (p : ℤ) ∣ B₁ := by
        rw [C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (PowerSeries.coeff i) h0
        rw [PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero, eq_intCast,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at this
        exact this
      have hu := hB _ this
      rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
      exact hp.one_lt.ne' hu
    have hW : PowerSeries.map (Int.castRingHom (ZMod p)) W = 0 := by
      have := congrArg (PowerSeries.map (Int.castRingHom (ZMod p))) h
      rw [map_mul, PowerSeries.map_C, eq_intCast, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self, zero_mul, map_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hB₁
    have hWdvd : ∀ k, (p : ℤ) ∣ PowerSeries.coeff k W := by
      intro k
      have := congrArg (PowerSeries.coeff k) hW
      rwa [PowerSeries.coeff_map, map_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    set W' : ℤ⟦X⟧ := PowerSeries.mk fun k => PowerSeries.coeff k W / p
    have hWW' : W = PowerSeries.C (p : ℤ) * W' := by
      ext k
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hWdvd k)]
    have h' : (B₁ : ℤ⟦X⟧) * W' = PowerSeries.C m' := by
      apply mul_left_cancel₀ (show PowerSeries.C (p : ℤ) ≠ 0 by
        rw [Ne, ← map_zero PowerSeries.C, PowerSeries.C_injective.eq_iff]
        exact_mod_cast hp.ne_zero)
      rw [← map_mul, ← h, hWW']
      ring
    refine ih m'.natAbs ?_ m' rfl hm' W' h' hdvd
    rw [← hn, Int.natAbs_mul, Int.natAbs_natCast]
    exact lt_mul_left (Int.natAbs_pos.mpr hm') hp.one_lt
  · apply hpm
    have := congrArg PowerSeries.constantCoeff h
    rw [map_mul, Polynomial.constantCoeff_coe, PowerSeries.constantCoeff_C] at this
    rw [← this]
    exact dvd_mul_of_dvd_left hdvd _

/-- **Fatou's lemma**: a power series with integer coefficients and constant term 1 that is
rational over ℚ is the quotient of two coprime integer polynomials with constant term 1. -/
theorem PowerSeries.exists_int_coprime_mul_eq_of_rat (Z : ℤ⟦X⟧)
    (hZ : PowerSeries.constantCoeff Z = 1)
    {A₀ B₀ : ℚ[X]} (hB₀ : B₀ ≠ 0)
    (h : (B₀ : ℚ⟦X⟧) * PowerSeries.map (Int.castRingHom ℚ) Z = A₀) :
    ∃ A B : ℤ[X], A.coeff 0 = 1 ∧ B.coeff 0 = 1 ∧
      IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) ∧
      (B : ℤ⟦X⟧) * Z = A := by
  set φ := Int.castRingHom ℚ
  -- Step 1: divide by the gcd
  set g := gcd A₀ B₀
  have hg : g ≠ 0 := fun h0 => hB₀ ((gcd_eq_zero_iff _ _).mp h0).2
  have hcop : IsCoprime (A₀ / g) (B₀ / g) := isCoprime_div_gcd_div_gcd hB₀
  have hA₀ : g * (A₀ / g) = A₀ := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hB₀' : g * (B₀ / g) = B₀ := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right _ _)
  have hB'0 : B₀ / g ≠ 0 := fun h0 => hB₀ (by rw [← hB₀', h0, mul_zero])
  have h' : ((B₀ / g : ℚ[X]) : ℚ⟦X⟧) * PowerSeries.map φ Z = (A₀ / g : ℚ[X]) := by
    apply mul_left_cancel₀ (show (g : ℚ⟦X⟧) ≠ 0 by rwa [Ne, Polynomial.coe_eq_zero_iff])
    rw [← mul_assoc, ← Polynomial.coe_mul, ← Polynomial.coe_mul, hA₀, hB₀', h]
  -- Step 2: a primitive integer denominator, and the integer numerator
  obtain ⟨c, hc, B₁, hB₁prim, hB₁⟩ := exists_isPrimitive_map_eq_C_mul hB'0
  obtain ⟨A₁, hA₁, hA₁map⟩ : ∃ A₁ : ℤ[X], (A₁ : ℤ⟦X⟧) = (B₁ : ℤ⟦X⟧) * Z ∧
      A₁.map φ = Polynomial.C c * (A₀ / g) := by
    apply exists_polynomial_of_map_eq
    rw [map_mul, ← polynomial_map_coe, hB₁, Polynomial.coe_mul, mul_assoc, h',
      Polynomial.coe_mul]
  have hcop₁ : IsCoprime (A₁.map φ) (B₁.map φ) := by
    rw [hA₁map, hB₁, isCoprime_mul_unit_left (isUnit_C.mpr hc.isUnit)]
    exact hcop
  -- Step 3: the constant term of `B₁` is a unit
  obtain ⟨m, hm, U, V, hUV⟩ := exists_int_bezout hcop₁
  have hW : (B₁ : ℤ⟦X⟧) * ((U : ℤ⟦X⟧) * Z + V) = PowerSeries.C m := by
    rw [← Polynomial.coe_C, ← hUV, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
      hA₁]
    ring
  have he : IsUnit (B₁.coeff 0) := by
    rw [Int.isUnit_iff_natAbs_eq]
    by_contra hne
    have hp := Nat.minFac_prime hne
    exact not_dvd_coeff_zero_of_mul_eq_C hB₁prim hp m hm _ hW
      (Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _))
  set e := B₁.coeff 0
  have hee : e * e = 1 := Int.isUnit_mul_self he
  have hBZ : ((Polynomial.C e * B₁ : ℤ[X]) : ℤ⟦X⟧) * Z = ((Polynomial.C e * A₁ : ℤ[X]) : ℤ⟦X⟧) := by
    rw [Polynomial.coe_mul, Polynomial.coe_mul, hA₁, mul_assoc]
  refine ⟨Polynomial.C e * A₁, Polynomial.C e * B₁, ?_, by rw [Polynomial.coeff_C_mul, hee], ?_,
    hBZ⟩
  · have := congrArg PowerSeries.constantCoeff hBZ
    rw [map_mul, Polynomial.constantCoeff_coe, Polynomial.constantCoeff_coe, hZ, mul_one,
      Polynomial.coeff_C_mul, hee] at this
    exact this.symm
  · have heq : IsUnit (Polynomial.C (e : ℚ)) := isUnit_C.mpr (he.map (Int.castRingHom ℚ))
    rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, eq_intCast,
      isCoprime_mul_unit_left heq]
    exact hcop₁

/-- **Gauss**: a rational factor with constant term 1 of an integer polynomial with constant
term 1 is integral. -/
theorem Polynomial.exists_map_eq_of_dvd_of_coeff_zero_eq_one {A : ℤ[X]} (hA : A.coeff 0 = 1)
    {r : ℚ[X]} (hr : r.coeff 0 = 1) (hd : r ∣ A.map (Int.castRingHom ℚ)) :
    ∃ s : ℤ[X], s.map (Int.castRingHom ℚ) = r := by
  have hr0 : r ≠ 0 := fun h0 => by simp [h0] at hr
  obtain ⟨c, hc, p, hp, hpr⟩ := exists_isPrimitive_map_eq_C_mul hr0
  have hAprim : A.IsPrimitive := fun a ha =>
    isUnit_of_dvd_one (hA ▸ (C_dvd_iff_dvd_coeff a A).mp ha 0)
  have hpA : p ∣ A := by
    rw [Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hp, hpr,
      (isUnit_C.mpr hc.isUnit).mul_left_dvd]
    exact hd
  obtain ⟨s, hs⟩ := hpA
  have hu : IsUnit (p.coeff 0) := by
    have := congrArg (Polynomial.coeff · 0) hs
    simp only [mul_coeff_zero, hA] at this
    exact IsUnit.of_mul_eq_one _ this.symm
  have hc' : (p.coeff 0 : ℚ) = c := by
    have := congrArg (Polynomial.coeff · 0) hpr
    simpa [hr] using this
  refine ⟨C (p.coeff 0) * p, ?_⟩
  rw [Polynomial.map_mul, map_C, eq_intCast, hpr, ← hc', ← mul_assoc, ← C_mul, ← Int.cast_mul,
    Int.isUnit_mul_self hu, Int.cast_one, C_1, one_mul]
