module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import Weil.AlgebraicGeometry.Thickenings.PicardSequence

/-!
# The unit sequence of the adic reductions of a scheme

Let `A` be a ring, `I ⊆ A` an ideal and `X` a scheme over `Spec A`. Write
`X_m = X ⊗_A A / I ^ m` for `m ≥ 1`, so that `X_1` is the fibre of `X` over `V(I)`. The
canonical closed immersions `X_1 ⟶ X_m ⟶ X_{m+1}` are homeomorphisms, since the ideals
`I / I ^ m` and `I ^ m / I ^ (m + 1)` are nilpotent. Since `m ≥ 1`, the ideal sheaf
`𝒥 = I ^ m 𝒪_X / I ^ (m + 1) 𝒪_X` of `X_m` in `X_{m+1}` has square zero, so `α ↦ 1 + α` is a
homomorphism from `𝒥` to the units, and the sequence of Zariski sheaves of abelian groups

`0 ⟶ 𝒥 ⟶ 𝒪_{X_{m+1}}^* ⟶ 𝒪_{X_m}^* ⟶ 1`

is exact.

## Main definitions

* `AlgebraicGeometry.adicBaseChangeIter`: the composite `X_{n+1} ⟶ X_{n+k+1}` of the
  canonical maps between consecutive adic reductions.

## Main results

* `AlgebraicGeometry.isClosedImmersion_adicBaseChangeIter` and
  `AlgebraicGeometry.isHomeomorph_adicBaseChangeIter`: the maps between adic reductions are
  closed immersions and homeomorphisms.
* `AlgebraicGeometry.shortExact_thickeningShortComplex_adicBaseChangeSucc`: the sequence
  `0 ⟶ 𝒥 ⟶ 𝒪_{X_{m+1}}^* ⟶ 𝒪_{X_m}^* ⟶ 1` is short exact.

## Implementation notes

The reduction `X ⊗_A A / I ^ m` (`m ≥ 1`) is `AlgebraicGeometry.adicBaseChange A I f (m - 1)`,
so indices are shifted by one; the special fibre is `AlgebraicGeometry.adicBaseChange A I f 0`.

The sequence is `Stacks.Thickenings.thickeningShortComplex` of the first-order thickening
`AlgebraicGeometry.adicBaseChangeSucc A I f n : X_{n+1} ⟶ X_{n+2}`. It is a sequence of sheaves
on the underlying space of `X_{n+2}`: the ideal sheaf `Stacks.Thickenings.idealAddSheaf`, the
units of `𝒪_{X_{n+2}}`, and the pushforward of the units of `𝒪_{X_{n+1}}`. The underlying maps
of all the reductions are homeomorphisms (`AlgebraicGeometry.isHomeomorph_adicBaseChangeIter`),
which identifies this with the sequence on the common space of the source. Its first map is
`α ↦ 1 + α` on sections (`Stacks.Thickenings.idealToUnitsSheafHom_app`).

The source works over a strictly Henselian Noetherian local ring with `I` its maximal ideal and
`X` projective; none of these hypotheses is used.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6.1, proof, p. 64]
* [Stacks Project, Tag 0C6R](https://stacks.math.columbia.edu/tag/0C6R)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

open Stacks.Thickenings (IsFirstOrderThickening)

variable (A : Type u) [CommRing A] (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The canonical map `X_{n+1} ⟶ X_{n+k+1}` from the reduction of `X` modulo `I ^ (n + 1)` to
the reduction modulo `I ^ (n + k + 1)`: the composite of the maps between consecutive
reductions. -/
def adicBaseChangeIter (n : ℕ) : (k : ℕ) → adicBaseChange A I f n ⟶ adicBaseChange A I f (n + k)
  | 0 => 𝟙 _
  | k + 1 => adicBaseChangeIter n k ≫ adicBaseChangeSucc A I f (n + k)

@[simp]
theorem adicBaseChangeIter_zero (n : ℕ) : adicBaseChangeIter A I f n 0 = 𝟙 _ := rfl

theorem adicBaseChangeIter_succ (n k : ℕ) :
    adicBaseChangeIter A I f n (k + 1) =
      adicBaseChangeIter A I f n k ≫ adicBaseChangeSucc A I f (n + k) := rfl

@[simp]
theorem adicBaseChangeIter_one (n : ℕ) :
    adicBaseChangeIter A I f n 1 = adicBaseChangeSucc A I f n := by
  simp [adicBaseChangeIter_succ]

/-- The maps between adic reductions are closed immersions. -/
@[weil "lem_fk106_units_thickening_exact_sequence"]
instance isClosedImmersion_adicBaseChangeIter (n k : ℕ) :
    IsClosedImmersion (adicBaseChangeIter A I f n k) := by
  induction k with
  | zero => rw [adicBaseChangeIter_zero]; infer_instance
  | succ k ih =>
    rw [adicBaseChangeIter_succ]
    have : IsClosedImmersion (adicBaseChangeSucc A I f (n + k)) :=
      (isFirstOrderThickening_adicBaseChangeSucc I f (n + k)).1
    infer_instance

/-- The maps between adic reductions are homeomorphisms; in particular the closed immersions
`X_1 ⟶ X_m` and `X_m ⟶ X_{m+1}` from the special fibre are. -/
@[weil "lem_fk106_units_thickening_exact_sequence"]
theorem isHomeomorph_adicBaseChangeIter (n k : ℕ) :
    IsHomeomorph (adicBaseChangeIter A I f n k) := by
  induction k with
  | zero => rw [adicBaseChangeIter_zero]; exact IsHomeomorph.id
  | succ k ih =>
    rw [adicBaseChangeIter_succ, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (isHomeomorph_of_isFirstOrderThickening
      (isFirstOrderThickening_adicBaseChangeSucc I f (n + k))).comp ih

/-- **The unit sequence of consecutive adic reductions.** For `m = n + 1 ≥ 1`, with
`𝒥 = I ^ m 𝒪_X / I ^ (m + 1) 𝒪_X` the ideal sheaf of `X_m` in `X_{m+1}`, the sequence of
sheaves of abelian groups `0 ⟶ 𝒥 ⟶ 𝒪_{X_{m+1}}^* ⟶ 𝒪_{X_m}^* ⟶ 1`, with first map
`α ↦ 1 + α` and second map restriction of units, is short exact. -/
@[weil "lem_fk106_units_thickening_exact_sequence"]
theorem shortExact_thickeningShortComplex_adicBaseChangeSucc (n : ℕ) :
    (Stacks.Thickenings.thickeningShortComplex (adicBaseChangeSucc A I f n)
      (isFirstOrderThickening_adicBaseChangeSucc I f n)).ShortExact :=
  Stacks.Thickenings.thickeningShortComplex_shortExact _ _

end AlgebraicGeometry

end
