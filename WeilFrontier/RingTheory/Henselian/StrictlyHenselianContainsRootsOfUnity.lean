module

public import StacksFrontier.RingTheory.DiscreteValuationRing.StrictlyHenselianKummerUnits
public import WeilFrontier.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import Weil.Attr

/-!
# Roots of unity in strictly Henselian local rings

Let `A` be a strictly Henselian local ring with residue field `k` and `n` an integer invertible
in `A`. Then `A` contains an element `ζ` with `ζ ^ n = 1` such that `ζ ^ d - 1` is a unit for
every `0 < d < n`. Indeed `X ^ n - 1` is separable over the separably closed field `k`, so `k`
contains a primitive `n`-th root of unity `ω`; it is a simple root of `X ^ n - 1`, so it lifts by
Hensel's lemma to a root `ζ` of `X ^ n - 1` in `A`. For `0 < d < n` the residue `ω ^ d - 1` of
`ζ ^ d - 1` is nonzero, so `ζ ^ d - 1` lies outside the maximal ideal.

## Main results

* `StrictlyHenselianLocalRing.exists_isPrimitiveRoot_isUnit_pow_sub_one`: a strictly Henselian
  local ring contains a primitive `n`-th root of unity `ζ` with `ζ ^ d - 1` a unit for
  `0 < d < n`, for every `n` invertible in it.

## Implementation notes

The source assumes `A` noetherian; the proof does not use it, and the statement here carries no
noetherian hypothesis. The conclusion also records that `ζ` is a primitive `n`-th root of unity
in `A`, which contains the source's `ζ ^ n = 1`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK], I.6
-/

@[expose] public section

open IsLocalRing

namespace StrictlyHenselianLocalRing

variable {A : Type*} [CommRing A] [StrictlyHenselianLocalRing A]

/-- A strictly Henselian local ring contains, for every `n` invertible in it, a primitive `n`-th
root of unity `ζ` such that `ζ ^ d - 1` is a unit for every `0 < d < n`. -/
@[weil "lem_fk106_strictly_henselian_contains_roots_of_unity"]
theorem exists_isPrimitiveRoot_isUnit_pow_sub_one {n : ℕ} (hn : IsUnit (n : A)) :
    ∃ ζ : A, IsPrimitiveRoot ζ n ∧ ∀ d : ℕ, 0 < d → d < n → IsUnit (ζ ^ d - 1) := by
  have hnk : ((n : ResidueField A)) ≠ 0 := by
    simpa using (hn.map (residue A)).ne_zero
  have : NeZero (n : ResidueField A) := ⟨hnk⟩
  have := IsSepClosed.hasEnoughRootsOfUnity (ResidueField A) n
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField A) n
  obtain ⟨b₀, rfl⟩ := residue_surjective z
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnk
  have hb₀u : IsUnit b₀ := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff]
    intro h0
    have := hz.pow_eq_one
    rw [h0, zero_pow hn0] at this
    exact zero_ne_one this
  obtain ⟨ζ, hζ, hres⟩ := Stacks.StrictlyHenselianKummer.exists_pow_eq_of_residue A hn 1 b₀
    (by rw [hz.pow_eq_one, map_one]) hb₀u
  refine ⟨ζ, (IsPrimitiveRoot.iff_def ζ n).2 ⟨hζ, fun l hl => ?_⟩, fun d hd hdn => ?_⟩
  · exact hz.dvd_of_pow_eq_one l (by rw [← hres, ← map_pow, hl, map_one])
  · rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, map_sub, map_pow, map_one, hres,
      sub_eq_zero]
    exact hz.pow_ne_one_of_pos_of_lt hd.ne' hdn

end StrictlyHenselianLocalRing

end
