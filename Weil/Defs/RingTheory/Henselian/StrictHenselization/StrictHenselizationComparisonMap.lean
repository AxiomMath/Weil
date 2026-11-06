module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.StrictHenselization.AtPrime

/-!
# Comparison maps from a Henselization tensor a finite algebra to strict Henselizations

Let `A` be a local ring, `B` an `A`-algebra, `k` a separably closed field, `φ : A → k` a local
homomorphism and `(Ã, φ̃)` a Henselization of `A` with respect to `φ`. For each `A`-algebra
homomorphism `ψ : B → k` (that is, each ring homomorphism with `ψ ∘ (A → B) = φ`), let
`B̃_ψ` be the strict Henselization of `B` at `ψ`, with its structure map `ι_ψ : B → B̃_ψ` and its
homomorphism `ψ̃ : B̃_ψ → k`. A *comparison map* is a ring homomorphism
`Θ : Ã ⊗_A B → ∏_ψ B̃_ψ` whose `ψ`-component `Θ_ψ` satisfies `Θ_ψ (1 ⊗ b) = ι_ψ b` and
`ψ̃ (Θ_ψ (a ⊗ 1)) = φ̃ a` for all `a ∈ Ã`, `b ∈ B`.

## Main definitions

* `IsLocalRing.HomOver φ B`: the set `Hom_A(B, k)` of ring homomorphisms `ψ : B → k` with
  `ψ ∘ (A → B) = φ`.
* `IsLocalRing.strictHenselizationProduct φ B`: the product `∏_{ψ ∈ Hom_A(B, k)} B̃_ψ`.
* `IsLocalRing.IsStrictHenselizationComparison φ̃ Θ`: `Θ` is a comparison map.

## Main results

* `IsLocalRing.isStrictHenselizationComparison_iff_comp_includeRight`: the first condition says
  exactly that `Θ ∘ (b ↦ 1 ⊗ b)` is the product of the structure maps `ι_ψ`.
* `IsLocalRing.IsStrictHenselizationComparison.hom_apply_tmul`: the value of `ψ̃ ∘ Θ_ψ` on a pure
  tensor `a ⊗ b` is `φ̃ a · ψ b`.

## Implementation notes

The source assumes `A` noetherian and `A → B` finite, and `(Ã, φ̃)` a Henselization of `A` with
respect to `φ`. None of this is needed to state the two conditions, so the predicate is defined
for any local ring `A`, any `A`-algebra `B`, and any `A`-algebra `Ã` with a homomorphism
`φ̃ : Ã → k`; the source's comparison maps are those with `(Ã, φ̃)` a Henselization along `φ`
(`IsLocalRing.IsHenselizationAlong`). The set `Hom_A(B, k)` is taken with `k` an `A`-algebra
through `φ`, encoded as the subtype `IsLocalRing.HomOver φ B`, and `B̃_ψ` is the chosen model
`RingHom.strictHenselizationAt ψ`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
-/

@[expose] public section

open TensorProduct

universe u v w x

namespace IsLocalRing

variable {A : Type u} [CommRing A] {k : Type v} [Field k] (φ : A →+* k)
  (B : Type w) [CommRing B] [Algebra A B]

/-- The set `Hom_A(B, k)` of `A`-algebra homomorphisms `B → k`, where `k` is an `A`-algebra
through `φ : A → k`: the ring homomorphisms `ψ : B → k` with `ψ ∘ (A → B) = φ`. -/
abbrev HomOver : Type (max w v) :=
  {ψ : B →+* k // ψ.comp (algebraMap A B) = φ}

/-- The product `∏_{ψ ∈ Hom_A(B, k)} B̃_ψ` of the strict Henselizations of `B` at the
`A`-algebra homomorphisms `ψ : B → k`. -/
abbrev strictHenselizationProduct [IsSepClosed k] : Type (max w v) :=
  ∀ ψ : HomOver φ B, (ψ : B →+* k).strictHenselizationAt

variable {φ B}

/-- **Comparison map.** Let `φ : A → k` be a homomorphism to a separably closed field, `B` an
`A`-algebra and `φ̃ : Ã → k` a homomorphism from an `A`-algebra `Ã` (in the source, `(Ã, φ̃)` is
the Henselization of `A` with respect to `φ`). A ring homomorphism
`Θ : Ã ⊗_A B → ∏_{ψ ∈ Hom_A(B, k)} B̃_ψ` is a comparison map if for every `ψ`, the `ψ`-component
`Θ_ψ` satisfies `Θ_ψ (1 ⊗ b) = ι_ψ b` and `ψ̃ (Θ_ψ (a ⊗ 1)) = φ̃ a`, where `ι_ψ : B → B̃_ψ` is the
structure map and `ψ̃ : B̃_ψ → k` the induced homomorphism. -/
@[weil "def_fk103_strict_henselization_comparison_map"]
structure IsStrictHenselizationComparison [IsSepClosed k] {Ã : Type x} [CommRing Ã] [Algebra A Ã]
    (φ' : Ã →+* k) (Θ : Ã ⊗[A] B →+* strictHenselizationProduct φ B) : Prop where
  /-- `Θ_ψ (1 ⊗ b) = ι_ψ b`. -/
  apply_one_tmul : ∀ (ψ : HomOver φ B) (b : B),
    Θ (1 ⊗ₜ b) ψ = algebraMap B (ψ : B →+* k).strictHenselizationAt b
  /-- `ψ̃ (Θ_ψ (a ⊗ 1)) = φ̃ a`. -/
  hom_apply_tmul_one : ∀ (ψ : HomOver φ B) (a : Ã),
    (ψ : B →+* k).strictHenselizationAtHom (Θ (a ⊗ₜ 1) ψ) = φ' a

variable [IsSepClosed k] {Ã : Type x} [CommRing Ã] [Algebra A Ã] {φ' : Ã →+* k}
  {Θ : Ã ⊗[A] B →+* strictHenselizationProduct φ B}

/-- The first condition of a comparison map says that `Θ ∘ (b ↦ 1 ⊗ b)` is the product of the
structure maps `ι_ψ : B → B̃_ψ`. -/
theorem isStrictHenselizationComparison_iff_comp_includeRight :
    IsStrictHenselizationComparison φ' Θ ↔
      Θ.comp (Algebra.TensorProduct.includeRight.toRingHom : B →+* Ã ⊗[A] B) =
          RingHom.pi (fun ψ : HomOver φ B => algebraMap B (ψ : B →+* k).strictHenselizationAt) ∧
        ∀ (ψ : HomOver φ B) (a : Ã),
          (ψ : B →+* k).strictHenselizationAtHom (Θ (a ⊗ₜ 1) ψ) = φ' a := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨RingHom.ext fun b => funext fun ψ => ?_, h₂⟩
    simpa [RingHom.pi_apply] using h₁ ψ b
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun ψ b => ?_, h₂⟩
    have := congrFun (RingHom.congr_fun h₁ b) ψ
    simpa [RingHom.pi_apply] using this

namespace IsStrictHenselizationComparison

variable (h : IsStrictHenselizationComparison φ' Θ)
include h

/-- `ψ̃ (Θ_ψ (1 ⊗ b)) = ψ b`. -/
theorem hom_apply_one_tmul (ψ : HomOver φ B) (b : B) :
    (ψ : B →+* k).strictHenselizationAtHom (Θ (1 ⊗ₜ b) ψ) = (ψ : B →+* k) b := by
  rw [h.apply_one_tmul, RingHom.strictHenselizationAtHom_algebraMap]

/-- On a pure tensor, `ψ̃ (Θ_ψ (a ⊗ b)) = φ̃ a · ψ b`. -/
theorem hom_apply_tmul (ψ : HomOver φ B) (a : Ã) (b : B) :
    (ψ : B →+* k).strictHenselizationAtHom (Θ (a ⊗ₜ b) ψ) = φ' a * (ψ : B →+* k) b := by
  have : a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : B)) * ((1 : Ã) ⊗ₜ[A] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, map_mul, Pi.mul_apply, map_mul, h.hom_apply_tmul_one, h.hom_apply_one_tmul]

/-- On a pure tensor, `Θ_ψ (a ⊗ b) = Θ_ψ (a ⊗ 1) · ι_ψ b`. -/
theorem apply_tmul (ψ : HomOver φ B) (a : Ã) (b : B) :
    Θ (a ⊗ₜ b) ψ = Θ (a ⊗ₜ 1) ψ * algebraMap B (ψ : B →+* k).strictHenselizationAt b := by
  have : a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : B)) * ((1 : Ã) ⊗ₜ[A] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, map_mul, Pi.mul_apply, h.apply_one_tmul]

end IsStrictHenselizationComparison

end IsLocalRing
