module

public import Weil.Defs.LinearAlgebra.PerfectPairing.Basic

/-!
# Operations on twisted-equivariant dualities

Let `B : V × W → K` be a `c`-duality for endomorphisms `(f, g)`, i.e. a pairing with trivial left
and right kernels such that `B (f x) (g y) = c * B x y`. This file records the elementary
operations preserving this notion.

## Main results

* `LinearMap.IsFrobeniusDuality.compl₁₂_linearEquiv`: transport of a `c`-duality along linear
  equivalences `V' ≃ V`, `W' ≃ W` intertwining the endomorphisms.
* `LinearMap.IsFrobeniusDuality.pow`: a `c`-duality for `(f, g)` is a `c ^ m`-duality for
  `(f ^ m, g ^ m)`.
* `LinearMap.IsFrobeniusDuality.of_isPerfPair_natCast`: a perfect pairing with
  `B (f x) (g y) = c * B x y` for a natural number `c` nonzero in `K` is a `c`-duality.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter IV, §1.
-/

@[expose] public section

namespace LinearMap

namespace IsFrobeniusDuality

variable {K V W V' W' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W] [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
  {B : V →ₗ[K] W →ₗ[K] K} {f : Module.End K V} {g : Module.End K W} {c : Kˣ}

/-- A `c`-duality for `(f, g)` transports along linear equivalences `eV : V' ≃ V`,
`eW : W' ≃ W` intertwining `f'` with `f` and `g'` with `g`. -/
theorem compl₁₂_linearEquiv (h : B.IsFrobeniusDuality f g c) (eV : V' ≃ₗ[K] V)
    (eW : W' ≃ₗ[K] W) {f' : Module.End K V'} {g' : Module.End K W'}
    (hf : ∀ x, eV (f' x) = f (eV x)) (hg : ∀ y, eW (g' y) = g (eW y)) :
    (B.compl₁₂ eV.toLinearMap eW.toLinearMap).IsFrobeniusDuality f' g' c where
  injective_left x₁ x₂ hx := by
    apply eV.injective
    apply h.injective_left
    ext y
    simpa using LinearMap.congr_fun hx (eW.symm y)
  injective_right y₁ y₂ hy := by
    apply eW.injective
    apply h.injective_right
    ext x
    simpa using LinearMap.congr_fun hy (eV.symm x)
  map_map x y := by
    simp only [compl₁₂_apply, LinearEquiv.coe_coe, hf, hg]
    exact h.map_map _ _

/-- A `c`-duality for `(f, g)` transports to a `c`-duality for the conjugates
`eV.symm.conj f`, `eW.symm.conj g` of the pairing pulled back along `eV`, `eW`. -/
theorem compl₁₂_conj (h : B.IsFrobeniusDuality f g c) (eV : V' ≃ₗ[K] V)
    (eW : W' ≃ₗ[K] W) :
    (B.compl₁₂ eV.toLinearMap eW.toLinearMap).IsFrobeniusDuality
      (eV.symm.conj f) (eW.symm.conj g) c :=
  h.compl₁₂_linearEquiv eV eW (fun x => by simp [LinearEquiv.conj_apply])
    (fun y => by simp [LinearEquiv.conj_apply])

/-- A `c`-duality for `(f, g)` is a `c ^ m`-duality for `(f ^ m, g ^ m)`. -/
theorem pow (h : B.IsFrobeniusDuality f g c) (m : ℕ) :
    B.IsFrobeniusDuality (f ^ m) (g ^ m) (c ^ m) where
  injective_left := h.injective_left
  injective_right := h.injective_right
  map_map x y := by
    induction m generalizing x y with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h.map_map,
        pow_succ, Units.val_mul, mul_assoc]

/-- A perfect pairing with `B (f x) (g y) = c * B x y`, for a natural number `c` nonzero in `K`,
is a `c`-duality for `(f, g)`. -/
theorem of_isPerfPair_natCast [B.IsPerfPair] {c : ℕ} (hc : (c : K) ≠ 0)
    (hfg : ∀ x y, B (f x) (g y) = (c : K) * B x y) :
    B.IsFrobeniusDuality f g (Units.mk0 (c : K) hc) :=
  .of_isPerfPair hfg

/-- If `B` is a `c`-duality for `(f, g)` and `g` is the identity, then `f` is multiplication by
`c`. -/
theorem eq_smul_id_of_right_eq_id (h : B.IsFrobeniusDuality f g c) (hg : g = LinearMap.id) :
    f = (c : K) • LinearMap.id := by
  ext x
  refine sub_eq_zero.1 (h.eq_zero_of_forall_left fun y => ?_)
  have := h.map_map x y
  rw [hg, LinearMap.id_apply] at this
  simp [this]

/-- If `B` is a `c`-duality for `(f, g)` and `f` is the identity, then `g` is multiplication by
`c`. -/
theorem eq_smul_id_of_left_eq_id (h : B.IsFrobeniusDuality f g c) (hf : f = LinearMap.id) :
    g = (c : K) • LinearMap.id :=
  h.flip.eq_smul_id_of_right_eq_id hf

end IsFrobeniusDuality

end LinearMap
