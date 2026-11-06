module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Weil.Attr

/-!
# Twisted-equivariant dualities

Let `V`, `W` be finite-dimensional vector spaces over a field `K`, with endomorphisms `F_V`, `F_W`,
and let `c ∈ Kˣ`. A bilinear form `β : V × W → K` is a *`c`-duality for `(F_V, F_W)`* if both maps
`V → W*`, `x ↦ β(x, ·)`, and `W → V*`, `y ↦ β(·, y)`, are injective, and
`β(F_V x, F_W y) = c β(x, y)` for all `x ∈ V`, `y ∈ W`. Poincaré duality in `ℓ`-adic cohomology
gives such a pairing between `H^ν` and `H^{2n-ν}` of a smooth projective variety, with `F` the
Frobenius and `c = q^n`.

In finite dimension the two injectivity conditions say exactly that `β` is a perfect pairing
(`LinearMap.IsPerfPair`).

## Main definitions

* `LinearMap.IsFrobeniusDuality`: `B` is a `c`-duality for `(f, g)`.

## Main results

* `LinearMap.IsFrobeniusDuality.isPerfPair`: a `c`-duality is a perfect pairing.
* `LinearMap.IsFrobeniusDuality.of_isPerfPair`: a perfect pairing satisfying the equivariance
  equation is a `c`-duality.
* `LinearMap.isFrobeniusDuality_iff`: the characterisation by `IsPerfPair`.
* `LinearMap.IsFrobeniusDuality.flip`: `B.flip` is a `c`-duality for `(g, f)`.

## Implementation notes

The pairing is a bilinear map `B : V →ₗ[K] W →ₗ[K] K`; the map `W → V*` is `B.flip`. The
definition does not need finite dimension; the comparison with perfect pairings does.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

@[expose] public section

namespace LinearMap

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- `B : V × W → K` is a `c`-duality for the endomorphisms `(f, g)`: both maps `V → W*` and
`W → V*` induced by `B` are injective, and `B (f x) (g y) = c * B x y` for all `x`, `y`. -/
@[weil "def_fk401_frobenius_duality"]
structure IsFrobeniusDuality (B : V →ₗ[K] W →ₗ[K] K) (f : Module.End K V) (g : Module.End K W)
    (c : Kˣ) : Prop where
  /-- The map `V → W*`, `x ↦ B x`, is injective. -/
  injective_left : Function.Injective B
  /-- The map `W → V*`, `y ↦ B (·) y`, is injective. -/
  injective_right : Function.Injective B.flip
  /-- The equivariance `B (f x) (g y) = c * B x y`. -/
  map_map : ∀ x y, B (f x) (g y) = (c : K) * B x y

namespace IsFrobeniusDuality

variable {B : V →ₗ[K] W →ₗ[K] K} {f : Module.End K V} {g : Module.End K W} {c : Kˣ}

/-- The pairing `B.flip : W × V → K` is a `c`-duality for `(g, f)`. -/
theorem flip (h : B.IsFrobeniusDuality f g c) : B.flip.IsFrobeniusDuality g f c where
  injective_left := h.injective_right
  injective_right := by rw [LinearMap.flip_flip]; exact h.injective_left
  map_map x y := h.map_map y x

/-- The left kernel of a `c`-duality is trivial. -/
theorem eq_zero_of_forall_left (h : B.IsFrobeniusDuality f g c) {x : V}
    (hx : ∀ y, B x y = 0) : x = 0 :=
  h.injective_left (by ext y; simp [hx y])

/-- The right kernel of a `c`-duality is trivial. -/
theorem eq_zero_of_forall_right (h : B.IsFrobeniusDuality f g c) {y : W}
    (hy : ∀ x, B x y = 0) : y = 0 :=
  h.flip.eq_zero_of_forall_left hy

/-- In finite dimension, a `c`-duality is a perfect pairing. -/
theorem isPerfPair [FiniteDimensional K V] (h : B.IsFrobeniusDuality f g c) : B.IsPerfPair :=
  LinearMap.IsPerfPair.of_injective h.injective_left h.injective_right

/-- A perfect pairing satisfying `B (f x) (g y) = c * B x y` is a `c`-duality for `(f, g)`. -/
theorem of_isPerfPair [B.IsPerfPair] (hfg : ∀ x y, B (f x) (g y) = (c : K) * B x y) :
    B.IsFrobeniusDuality f g c where
  injective_left := (LinearMap.IsPerfPair.bijective_left B).injective
  injective_right := (LinearMap.IsPerfPair.bijective_right B).injective
  map_map := hfg

end IsFrobeniusDuality

/-- In finite dimension, `B` is a `c`-duality for `(f, g)` if and only if it is a perfect pairing
and `B (f x) (g y) = c * B x y` for all `x`, `y`. -/
theorem isFrobeniusDuality_iff [FiniteDimensional K V]
    {B : V →ₗ[K] W →ₗ[K] K} {f : Module.End K V} {g : Module.End K W} {c : Kˣ} :
    B.IsFrobeniusDuality f g c ↔ B.IsPerfPair ∧ ∀ x y, B (f x) (g y) = (c : K) * B x y :=
  ⟨fun h => ⟨h.isPerfPair, h.map_map⟩, fun ⟨_, h⟩ => .of_isPerfPair h⟩

end LinearMap
