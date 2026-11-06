module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Data.Int.ConditionallyCompleteOrder

/-!
# The order of an element along a map out of a local ring

Let `(A, 𝔪)` be a local ring and `ι : A →+* L` a ring homomorphism. For `m : ℤ` put
`I_m = ι(𝔪 ^ m)` if `m ≥ 0`, and `I_m = {h ∈ L | h · ι(𝔪 ^ (-m)) ⊆ ι(A)}` if `m < 0`.
The order of `g : L` is `sup {m ∈ ℤ | g ∈ I_m}`, an element of `ℤ ∪ {±∞}` (with `sup ∅ = -∞`).

When `A` is a discrete valuation ring and `L` its fraction field, the order of a nonzero `g` is
the exponent of the normalized discrete valuation of `g`. In particular, at a point `x` of
coheight `1` of a locally Noetherian integral scheme whose stalk is a discrete valuation ring,
the order along the map from the stalk to the function field is Mathlib's order of vanishing
`AlgebraicGeometry.Scheme.ord`.

## Main definitions

- `IsLocalRing.ordAlongSet ι m`: the set `I_m ⊆ L`.
- `IsLocalRing.ordAlong ι g`: the order of `g : L` along `ι`, in `WithBot (WithTop ℤ)`.

## Main results

- `IsLocalRing.ordAlong_zero`: the order of `0` is `⊤`.
- `IsLocalRing.ordAlong_eq_coe_of_forall`: `ordAlong ι g = n` as soon as `g ∈ I_m ↔ m ≤ n`.
- `IsDiscreteValuationRing.mem_ordAlongSet_algebraMap_iff`: over a discrete valuation ring with
  fraction field `K`, `g ∈ I_m` iff `v g ≤ exp (-m)` for the normalized valuation `v`.
- `IsDiscreteValuationRing.ordAlong_algebraMap_of_ne_zero`: the order of `g ≠ 0` is
  `-log (v g)`, i.e. `log (Ring.ordFrac A g)`.
- `AlgebraicGeometry.Scheme.ordAlong_algebraMap_stalk_functionField`: on a locally Noetherian
  integral scheme, at a point of coheight `1` with discrete valuation ring stalk, the order of a
  nonzero rational function along `𝒪_{X,x} → K(X)` is `Scheme.ord f x`.

## Implementation notes

The value set `ℤ ∪ {±∞}` is `WithBot (WithTop ℤ)`, a complete linear order, so the supremum is
`sSup` and the empty supremum is `⊥`. The ideal power `𝔪 ^ (-m)` for `m < 0` is indexed by the
natural number `(-m).toNat`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Ch. I, §5.
-/

@[expose] public section

open IsLocalRing WithZero

namespace IsLocalRing

variable {A L : Type*} [CommRing A] [IsLocalRing A] [Semiring L] (ι : A →+* L)

/-- The set `I_m`: the image `ι (𝔪 ^ m)` for `m ≥ 0`, and for `m < 0` the set of `h` with
`h * ι a ∈ ι A` for every `a ∈ 𝔪 ^ (-m)`. -/
@[weil "def_fk105_order_function"]
def ordAlongSet (m : ℤ) : Set L :=
  if 0 ≤ m then ι '' ((maximalIdeal A ^ m.toNat : Ideal A) : Set A)
  else {h | ∀ a ∈ maximalIdeal A ^ (-m).toNat, h * ι a ∈ Set.range ι}

/-- The order of `g : L` along a ring homomorphism `ι` out of a local ring: the supremum in
`ℤ ∪ {±∞}` of the integers `m` with `g ∈ ordAlongSet ι m`. -/
@[weil "def_fk105_order_function"]
noncomputable def ordAlong (g : L) : WithBot (WithTop ℤ) :=
  sSup ((fun m : ℤ => ((m : WithTop ℤ) : WithBot (WithTop ℤ))) '' {m | g ∈ ordAlongSet ι m})

variable {ι}

lemma mem_ordAlongSet_of_nonneg {m : ℤ} (hm : 0 ≤ m) {g : L} :
    g ∈ ordAlongSet ι m ↔ ∃ a ∈ maximalIdeal A ^ m.toNat, ι a = g := by
  simp [ordAlongSet, hm]

lemma mem_ordAlongSet_of_neg {m : ℤ} (hm : m < 0) {g : L} :
    g ∈ ordAlongSet ι m ↔ ∀ a ∈ maximalIdeal A ^ (-m).toNat, g * ι a ∈ Set.range ι := by
  simp [ordAlongSet, not_le.mpr hm]

lemma zero_mem_ordAlongSet (m : ℤ) : (0 : L) ∈ ordAlongSet ι m := by
  rcases le_or_gt 0 m with hm | hm
  · exact (mem_ordAlongSet_of_nonneg hm).2 ⟨0, Submodule.zero_mem _, map_zero ι⟩
  · exact (mem_ordAlongSet_of_neg hm).2 fun _ _ => ⟨0, by simp⟩

/-- If `g ∈ I_m` exactly for `m ≤ n`, the order of `g` is `n`. -/
lemma ordAlong_eq_coe_of_forall {g : L} {n : ℤ} (h : ∀ m, g ∈ ordAlongSet ι m ↔ m ≤ n) :
    ordAlong ι g = ((n : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  refine IsGreatest.csSup_eq ⟨⟨n, (h n).2 le_rfl, rfl⟩, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  exact WithBot.coe_le_coe.2 (WithTop.coe_le_coe.2 ((h m).1 hm))

/-- If `g` lies in every `I_m`, its order is `⊤`. -/
lemma ordAlong_eq_top_of_forall {g : L} (h : ∀ m, g ∈ ordAlongSet ι m) : ordAlong ι g = ⊤ := by
  refine sSup_eq_top.2 fun b hb => ?_
  induction b using WithBot.recBotCoe with
  | bot => exact ⟨_, ⟨0, h 0, rfl⟩, WithBot.bot_lt_coe _⟩
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd hb (lt_irrefl _)
    | coe k =>
      exact ⟨_, ⟨k + 1, h _, rfl⟩,
        WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (lt_add_one k))⟩

@[simp]
lemma ordAlong_zero : ordAlong ι (0 : L) = ⊤ :=
  ordAlong_eq_top_of_forall zero_mem_ordAlongSet

end IsLocalRing

namespace IsDiscreteValuationRing

open IsDedekindDomain.HeightOneSpectrum

variable {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

private lemma mem_maximalIdeal_pow_iff (a : A) (k : ℕ) :
    a ∈ IsLocalRing.maximalIdeal A ^ k ↔
      (maximalIdeal A).valuation K (algebraMap A K a) ≤ exp (-(k : ℤ)) := by
  rw [valuation_of_algebraMap, intValuation_le_pow_iff_mem]
  rfl

/-- Over a discrete valuation ring `A` with fraction field `K`, `g ∈ I_m` iff the normalized
valuation of `g` is at most `exp (-m)`. -/
theorem mem_ordAlongSet_algebraMap_iff (g : K) (m : ℤ) :
    g ∈ IsLocalRing.ordAlongSet (algebraMap A K) m ↔
      (maximalIdeal A).valuation K g ≤ exp (-m) := by
  set v := (maximalIdeal A).valuation K
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [IsLocalRing.mem_ordAlongSet_of_nonneg hm, Int.toNat_natCast]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (mem_maximalIdeal_pow_iff a k).1 ha
    · intro hg
      have h1 : v g ≤ 1 := hg.trans (by simp [← exp_zero])
      obtain ⟨a, rfl⟩ := exists_lift_of_le_one h1
      exact ⟨a, (mem_maximalIdeal_pow_iff a k).2 hg, rfl⟩
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 hm.le)
    rw [IsLocalRing.mem_ordAlongSet_of_neg hm, hk, Int.toNat_natCast]
    have hexp : (exp (-(k : ℤ)) : ℤᵐ⁰) = (exp (k : ℤ))⁻¹ := exp_neg _
    constructor
    · intro hg
      obtain ⟨π, hπ⟩ := valuation_exists_uniformizer' K (maximalIdeal A)
      have hπk : π ^ k ∈ IsLocalRing.maximalIdeal A ^ k := by
        rw [mem_maximalIdeal_pow_iff (K := K), map_pow, map_pow, hπ, ← exp_nsmul]
        simp
      obtain ⟨b, hb⟩ := hg _ hπk
      have hle : v (g * algebraMap A K (π ^ k)) ≤ 1 := hb ▸ valuation_le_one _ b
      rw [map_mul, map_pow, map_pow, hπ, ← exp_nsmul, smul_neg, nsmul_eq_mul, mul_one, hexp,
        mul_inv_le_iff₀ (by simp)] at hle
      simpa using hle
    · intro hg a ha
      apply exists_lift_of_le_one
      rw [map_mul]
      have ha' := (mem_maximalIdeal_pow_iff (K := K) a k).1 ha
      calc v g * v (algebraMap A K a) ≤ exp (k : ℤ) * exp (-(k : ℤ)) :=
            mul_le_mul' hg ha'
        _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

/-- Over a discrete valuation ring `A` with fraction field `K`, the order of a nonzero `g` along
`algebraMap A K` is `-log (v g)` for the normalized valuation `v`. -/
theorem ordAlong_algebraMap_of_ne_zero {g : K} (hg : g ≠ 0) :
    IsLocalRing.ordAlong (algebraMap A K) g =
      ((-log ((maximalIdeal A).valuation K g) : ℤ) : WithTop ℤ) := by
  apply IsLocalRing.ordAlong_eq_coe_of_forall
  intro m
  have hv : (maximalIdeal A).valuation K g ≠ 0 := by simpa using hg
  rw [mem_ordAlongSet_algebraMap_iff, ← exp_log hv, exp_le_exp, log_exp]
  omega

/-- The order along `algebraMap A K` of a nonzero `g` is `log (Ring.ordFrac A g)`. -/
theorem ordAlong_algebraMap_eq_log_ordFrac {g : K} (hg : g ≠ 0) :
    IsLocalRing.ordAlong (algebraMap A K) g = ((log (Ring.ordFrac A g) : ℤ) : WithTop ℤ) := by
  rw [ordAlong_algebraMap_of_ne_zero hg, Ring.ordFrac_eq_valuation_inv, log_inv]

end IsDiscreteValuationRing

namespace AlgebraicGeometry.Scheme

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

/-- At a point `x` of coheight `1` with discrete valuation ring stalk, the order of a nonzero
rational function `f` along `𝒪_{X,x} → K(X)` is the order of vanishing `Scheme.ord f x`. -/
theorem ordAlong_algebraMap_stalk_functionField {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] {f : X.functionField} (hf : f ≠ 0) :
    IsLocalRing.ordAlong (algebraMap (X.presheaf.stalk x) X.functionField) f = ord f x := by
  rw [IsDiscreteValuationRing.ordAlong_algebraMap_eq_log_ordFrac hf]
  congr 2
  have h0 : Ring.ordFrac (X.presheaf.stalk x) f ≠ 0 := by simpa using hf
  symm
  rw [ord_eq_iff hx hf]
  change Ring.ordFrac (X.presheaf.stalk x) f = _
  rw [← exp_log h0]
  rfl

end AlgebraicGeometry.Scheme
