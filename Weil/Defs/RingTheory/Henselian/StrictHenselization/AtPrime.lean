module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.AtPrime

/-!
# The strict Henselization of a ring at a homomorphism to a field

Let `B` be a ring, `k` a field and `ψ : B → k` a ring homomorphism. The kernel `𝔫 = ker ψ` is a
prime ideal, and `ψ` induces the local homomorphism `ψ_𝔫 : B_𝔫 → k`, `b / s ↦ ψ(b) ψ(s)⁻¹`. The
*strict Henselization of `B` at `ψ`* is the Henselization `B̃_ψ` of the local ring `B_𝔫` with
respect to `ψ_𝔫`, together with the induced maps `ι_ψ : B → B_𝔫 → B̃_ψ` and `ψ̃ : B̃_ψ → k`; these
satisfy `ψ̃ ∘ ι_ψ = ψ`. For `k` separably closed, `B̃_ψ` is a strict henselization of `B_𝔫`.

## Main definitions

* `RingHom.liftLocalizationAtKer ψ`: the local homomorphism `ψ_𝔫 : B_𝔫 → k`.
* `RingHom.IsStrictHenselizationAt ψ B̃ ψ̃`: `(B̃, ψ̃)` is a Henselization of `B_𝔫` with respect to
  `ψ_𝔫`, i.e. a strict Henselization of `B` at `ψ`.
* `RingHom.strictHenselizationAt ψ`: for `k` separably closed, the chosen strict Henselization of
  `B` at `ψ`; it is the strict henselization `StacksDraft.strictHenselizationAtPrime B (ker ψ)` of
  `B` at the prime `ker ψ`, a `B`-algebra through `ι_ψ : B → B_𝔫 → B̃_ψ`.
* `RingHom.strictHenselizationAtHom ψ`: the induced homomorphism `ψ̃ : B̃_ψ → k`.

## Main results

* `RingHom.isStrictHenselizationAt_strictHenselizationAt`: `(B̃_ψ, ψ̃)` is a strict Henselization
  of `B` at `ψ`.
* `RingHom.strictHenselizationAtHom_comp_algebraMap`: `ψ̃ ∘ ι_ψ = ψ`.
* `RingHom.IsStrictHenselizationAt.comp_algebraMap`: the same for any strict Henselization at `ψ`.

## Implementation notes

The source assumes `B` noetherian and `k` separably closed. Neither is needed for the
characterizing predicate `RingHom.IsStrictHenselizationAt`, which is stated for any field `k`. The
chosen model needs `k` separably closed: it is the strict henselization of `B_𝔫` with respect to
the absolute separable closure of `κ(𝔫)`, and its homomorphism to `k` comes from an embedding of
that separable closure into `k` over `κ(𝔫)`, which exists exactly because `k` is separably closed.
By uniqueness of henselizations (Stacks 08HT) any two strict Henselizations at `ψ` are isomorphic
over `B_𝔫`, so the choice of model does not matter.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3.2
* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace RingHom

/-- The kernel of a homomorphism to a field is a prime ideal. -/
instance ker_isPrime_of_field {B : Type u} [CommRing B] {k : Type v} [Field k] (ψ : B →+* k) :
    (RingHom.ker ψ).IsPrime :=
  RingHom.ker_isPrime ψ

variable {B : Type u} [CommRing B] {k : Type v} [Field k] (ψ : B →+* k)

/-- The local homomorphism `ψ_𝔫 : B_𝔫 → k`, `b / s ↦ ψ(b) ψ(s)⁻¹`, induced by a homomorphism
`ψ : B → k` to a field on the localization of `B` at the prime `𝔫 = ker ψ`. -/
noncomputable def liftLocalizationAtKer : Localization.AtPrime (RingHom.ker ψ) →+* k :=
  IsLocalization.lift (M := (RingHom.ker ψ).primeCompl)
    (S := Localization.AtPrime (RingHom.ker ψ)) (g := ψ)
    fun s => isUnit_iff_ne_zero.2 fun h => s.2 h

@[simp]
theorem liftLocalizationAtKer_algebraMap (b : B) :
    ψ.liftLocalizationAtKer (algebraMap B (Localization.AtPrime (RingHom.ker ψ)) b) = ψ b :=
  IsLocalization.lift_eq _ _

theorem liftLocalizationAtKer_comp_algebraMap :
    ψ.liftLocalizationAtKer.comp (algebraMap B (Localization.AtPrime (RingHom.ker ψ))) = ψ :=
  IsLocalization.lift_comp _

instance isLocalHom_liftLocalizationAtKer : IsLocalHom ψ.liftLocalizationAtKer where
  map_nonunit x hx := by
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl x
    have hs : IsUnit (ψ s) := isUnit_iff_ne_zero.2 fun h => s.2 h
    have hspec : ψ.liftLocalizationAtKer
        (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) b s) * ψ s = ψ b := by
      rw [← liftLocalizationAtKer_algebraMap ψ s, ← map_mul, IsLocalization.mk'_spec,
        liftLocalizationAtKer_algebraMap]
    have hb : b ∈ (RingHom.ker ψ).primeCompl := fun h =>
      (hx.mul hs).ne_zero (hspec.trans (RingHom.mem_ker.1 h))
    exact (IsLocalization.AtPrime.isUnit_mk'_iff _ _ b s).2 hb

/-- **The strict Henselization of a ring at a homomorphism to a field.** For `ψ : B → k`, a pair
`(B̃, ψ̃)` of a local `B_𝔫`-algebra `B̃` and a homomorphism `ψ̃ : B̃ → k` is a strict Henselization
of `B` at `ψ` if it is a Henselization of the local ring `B_𝔫`, `𝔫 = ker ψ`, with respect to the
induced local homomorphism `ψ_𝔫 : B_𝔫 → k`. -/
@[weil "def_fk103_strict_henselization_at_homomorphism"]
abbrev IsStrictHenselizationAt (B' : Type w) [CommRing B'] [IsLocalRing B']
    [Algebra (Localization.AtPrime (RingHom.ker ψ)) B'] (ψ' : B' →+* k) : Prop :=
  IsHenselizationAlong ψ.liftLocalizationAtKer B' ψ'

/-- **`ψ̃ ∘ ι_ψ = ψ`** for any strict Henselization `(B̃, ψ̃)` of `B` at `ψ`, where `ι_ψ` is the
structure map `B → B_𝔫 → B̃`. -/
theorem IsStrictHenselizationAt.comp_algebraMap {ψ : B →+* k} {B' : Type w} [CommRing B']
    [IsLocalRing B']
    [Algebra (Localization.AtPrime (RingHom.ker ψ)) B'] [Algebra B B']
    [IsScalarTower B (Localization.AtPrime (RingHom.ker ψ)) B'] {ψ' : B' →+* k}
    (h : ψ.IsStrictHenselizationAt B' ψ') : ψ'.comp (algebraMap B B') = ψ := by
  rw [IsScalarTower.algebraMap_eq B (Localization.AtPrime (RingHom.ker ψ)) B', ← RingHom.comp_assoc,
    h.ψ_comp_algebraMap, liftLocalizationAtKer_comp_algebraMap]

theorem IsStrictHenselizationAt.apply_algebraMap {ψ : B →+* k} {B' : Type w} [CommRing B']
    [IsLocalRing B']
    [Algebra (Localization.AtPrime (RingHom.ker ψ)) B'] [Algebra B B']
    [IsScalarTower B (Localization.AtPrime (RingHom.ker ψ)) B'] {ψ' : B' →+* k}
    (h : ψ.IsStrictHenselizationAt B' ψ') (b : B) : ψ' (algebraMap B B' b) = ψ b :=
  RingHom.congr_fun h.comp_algebraMap b

/-- For `k` separably closed, a strict Henselization of `B` at `ψ` is a strict henselization of
the local ring `B_𝔫`: its residue field is a separable closure of `κ(𝔫)`. -/
theorem IsStrictHenselizationAt.isHenselization_separableClosure [IsSepClosed k] {ψ : B →+* k}
    {B' : Type w} [CommRing B'] [IsLocalRing B']
    [Algebra (Localization.AtPrime (RingHom.ker ψ)) B'] {ψ' : B' →+* k}
    (h : ψ.IsStrictHenselizationAt B' ψ') :
    IsHenselization (Localization.AtPrime (RingHom.ker ψ))
      (SeparableClosure (ResidueField (Localization.AtPrime (RingHom.ker ψ)))) B' :=
  IsHenselizationAlong.isHenselization_separableClosure h

section Chosen

variable [IsSepClosed k]

/-- **The strict Henselization `B̃_ψ` of `B` at `ψ`**, for `k` separably closed: the strict
henselization of `B` at the prime `ker ψ`, with its `B`-algebra structure through
`ι_ψ : B → B_𝔫 → B̃_ψ`. -/
@[weil "def_fk103_strict_henselization_at_homomorphism"]
abbrev strictHenselizationAt : Type u :=
  StacksDraft.strictHenselizationAtPrime B (RingHom.ker ψ)

instance isHenselization_residueSeparableClosure_strictHenselizationAt :
    IsHenselization (Localization.AtPrime (RingHom.ker ψ))
      (residueSeparableClosure ψ.liftLocalizationAtKer) ψ.strictHenselizationAt :=
  IsHenselization.of_residueAlgEquiv
    (IsSepClosure.equiv (ResidueField (Localization.AtPrime (RingHom.ker ψ)))
      (SeparableClosure (ResidueField (Localization.AtPrime (RingHom.ker ψ))))
      (residueSeparableClosure ψ.liftLocalizationAtKer))

theorem exists_isStrictHenselizationAt_strictHenselizationAt :
    ∃ ψ' : ψ.strictHenselizationAt →+* k, ψ.IsStrictHenselizationAt ψ.strictHenselizationAt ψ' :=
  IsHenselization.exists_isHenselizationAlong ψ.liftLocalizationAtKer

/-- The homomorphism `ψ̃ : B̃_ψ → k` induced by `ψ` on the strict Henselization of `B` at `ψ`. -/
@[weil "def_fk103_strict_henselization_at_homomorphism"]
noncomputable def strictHenselizationAtHom : ψ.strictHenselizationAt →+* k :=
  (exists_isStrictHenselizationAt_strictHenselizationAt ψ).choose

/-- `(B̃_ψ, ψ̃)` is a strict Henselization of `B` at `ψ`. -/
@[weil "def_fk103_strict_henselization_at_homomorphism"]
theorem isStrictHenselizationAt_strictHenselizationAt :
    ψ.IsStrictHenselizationAt ψ.strictHenselizationAt ψ.strictHenselizationAtHom :=
  (exists_isStrictHenselizationAt_strictHenselizationAt ψ).choose_spec

/-- **`ψ̃ ∘ ι_ψ = ψ`.** -/
@[weil "def_fk103_strict_henselization_at_homomorphism"]
theorem strictHenselizationAtHom_comp_algebraMap :
    ψ.strictHenselizationAtHom.comp (algebraMap B ψ.strictHenselizationAt) = ψ :=
  (isStrictHenselizationAt_strictHenselizationAt ψ).comp_algebraMap

@[simp]
theorem strictHenselizationAtHom_algebraMap (b : B) :
    ψ.strictHenselizationAtHom (algebraMap B ψ.strictHenselizationAt b) = ψ b :=
  RingHom.congr_fun (strictHenselizationAtHom_comp_algebraMap ψ) b

/-- The map `ψ̃ : B̃_ψ → k` is local. -/
instance isLocalHom_strictHenselizationAtHom : IsLocalHom ψ.strictHenselizationAtHom :=
  (isStrictHenselizationAt_strictHenselizationAt ψ).isLocalHom_ψ

/-- The kernel of `ψ̃ : B̃_ψ → k` is the maximal ideal of `B̃_ψ`. -/
theorem ker_strictHenselizationAtHom :
    RingHom.ker ψ.strictHenselizationAtHom = maximalIdeal ψ.strictHenselizationAt :=
  (isStrictHenselizationAt_strictHenselizationAt ψ).ker_ψ

end Chosen

end RingHom
