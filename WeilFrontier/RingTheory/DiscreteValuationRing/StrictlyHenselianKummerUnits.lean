module

public import WeilFrontier.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.DiscreteValuationRing.StrictlyHenselianKummerUnits
public import Weil.Attr

/-!
# Units of a strictly Henselian local ring are `n`-th powers

Let `A` be a strictly Henselian local ring and `n` an integer invertible in `A`. Every unit `u`
of `A` is the `n`-th power of a unit: the polynomial `X ^ n - u` is separable over the separably
closed residue field, so it has a simple root there, which lifts to `A` by Hensel's lemma; the
lift is a unit since its residue is a nonzero `n`-th root of the residue of `u`.

## Main results

* `StrictlyHenselianLocalRing.exists_unit_pow_eq`: every unit of a strictly Henselian local ring
  is the `n`-th power of a unit, for every natural number `n` invertible in the ring.

## Implementation notes

The root lifting is `Stacks.StrictlyHenselianKummer.exists_pow_eq_of_isUnit`, stated for a
Henselian local ring with separably closed residue field; a root of `X ^ n - u` with `u` a unit
is automatically a unit when `n ≠ 0`, and when `n = 0` the hypothesis forces `A` to be trivial.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK], I.7
-/

@[expose] public section

namespace StrictlyHenselianLocalRing

variable {A : Type*} [CommRing A] [StrictlyHenselianLocalRing A]

/-- **Units of a strictly Henselian local ring are `n`-th powers**: if `n` is invertible in `A`,
every unit `u` of `A` is `w ^ n` for a unit `w`. -/
@[weil "lem_fk107_strictly_henselian_units_nth_powers"]
theorem exists_unit_pow_eq {n : ℕ} (hn : IsUnit (n : A)) (u : Aˣ) : ∃ w : Aˣ, w ^ n = u := by
  obtain ⟨b, hb⟩ := Stacks.StrictlyHenselianKummer.exists_pow_eq_of_isUnit A hn u.isUnit
  rcases eq_or_ne n 0 with rfl | hn0
  · have : Subsingleton A := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 (by exact_mod_cast hn))
    exact ⟨1, Subsingleton.elim _ _⟩
  · have hbu : IsUnit b := (isUnit_pow_iff hn0).1 (hb ▸ u.isUnit)
    exact ⟨hbu.unit, Units.ext (by simpa using hb)⟩

end StrictlyHenselianLocalRing

end
