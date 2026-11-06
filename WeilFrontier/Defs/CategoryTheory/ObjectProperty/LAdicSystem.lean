module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.FiniteLength
public import StacksFrontier.CategoryTheory.Abelian.StrictLAdicTower
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.FullSubcategory
public import Weil.Attr

/-!
# `l`-adic systems

Let `Λ` be a commutative ring and `l ∈ Λ`. A projective system `F = (F_n, u_n)_{n ∈ ℤ}` of
`l`-power torsion `Λ`-modules is an *`l`-adic system* if

* `F_n = 0` for `n < 0`;
* `l^{n+1} F_n = 0` for all `n ≥ 0`;
* for all `n ≥ 0` the transition map `u_{n+1} : F_{n+1} → F_n` is surjective with kernel
  `l^{n+1} F_{n+1}`, so that it induces an isomorphism `F_{n+1} / l^{n+1} F_{n+1} ≅ F_n`;
* every `F_n` is a `Λ`-module of finite length.

The middle two conditions say that the restriction of `F` to the non-negative degrees is a strict
`l`-adic tower in the sense of `CategoryTheory.LAdicTower.IsStrict`, when `l` is the image of a
natural number.

## Main definitions

* `CategoryTheory.ProjectiveSystem.IsLAdicSystem`: the predicate that a projective system is an
  `l`-adic system.
* `CategoryTheory.ProjectiveSystem.tower`: the restriction of a projective system to the
  non-negative degrees, as a tower `ℕᵒᵖ ⥤ ModuleCat Λ`.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.quotEquiv`: the isomorphism
  `F_{n+1} / l^{n+1} F_{n+1} ≃ F_n` induced by the transition map.

## Main results

* `CategoryTheory.ProjectiveSystem.isStrict_tower_iff`: for `l` the image of a natural number
  `ℓ`, the conditions on the non-negative degrees say exactly that the restricted tower is
  strict `ℓ`-adic.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.isStrict`: the restricted tower of an `l`-adic
  system is strict `ℓ`-adic.

## Implementation notes

The source fixes `Λ = ℤ_l`; the definition is stated for any commutative ring `Λ` and any `l`.
The map `u_{n+1}` is written as the image of `n ≤ n + 1` under the functor `ℤᵒᵖ ⥤ ModuleCat Λ`,
so that its target is the term `F_n` on the nose. The kernel condition is the equality of the
kernel of `u_{n+1}` with the range of multiplication by `l^{n+1}`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The map `F_n ⟶ F_m` of a projective system, for `m ≤ n`. -/
abbrev mapLE (F : ProjectiveSystem.{v} Λ l) {m n : ℤ} (h : m ≤ n) : F.term n ⟶ F.term m :=
  F.obj.map (homOfLE h).op

/-- An object `F = (F_n, u_n)` of the category of projective systems of `l`-power torsion
`Λ`-modules is an *`l`-adic system* if `F_n = 0` for `n < 0`, `l^{n+1} F_n = 0` for `n ≥ 0`,
each `u_{n+1} : F_{n+1} → F_n` (`n ≥ 0`) is surjective with kernel `l^{n+1} F_{n+1}`, and every
`F_n` is a `Λ`-module of finite length. -/
@[weil "def_fk112_l_adic_system"]
structure IsLAdicSystem (F : ProjectiveSystem.{v} Λ l) : Prop where
  /-- `F_n = 0` for `n < 0`. -/
  isZero_of_neg : ∀ n : ℤ, n < 0 → IsZero (F.term n)
  /-- `l^{n+1} F_n = 0` for `n ≥ 0`. -/
  pow_smul_eq_zero : ∀ (n : ℕ) (x : F.term n), l ^ (n + 1) • x = 0
  /-- The transition `u_{n+1} : F_{n+1} → F_n` is surjective. -/
  surjective : ∀ n : ℕ,
    Function.Surjective (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom
  /-- The kernel of `u_{n+1} : F_{n+1} → F_n` is `l^{n+1} F_{n+1}`. -/
  ker_eq : ∀ n : ℕ, LinearMap.ker (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom =
    LinearMap.range (l ^ (n + 1) • LinearMap.id : F.term (n + 1 : ℕ) →ₗ[Λ] F.term (n + 1 : ℕ))
  /-- Every `F_n` is a `Λ`-module of finite length. -/
  isFiniteLength : ∀ n : ℤ, IsFiniteLength Λ (F.term n)

/-- The restriction of a projective system to the non-negative degrees, as a tower. -/
abbrev tower (F : ProjectiveSystem.{v} Λ l) : ℕᵒᵖ ⥤ ModuleCat.{v} Λ :=
  (Nat.mono_cast (α := ℤ)).functor.op ⋙ F.obj

lemma towerMap_tower_succ (F : ProjectiveSystem.{v} Λ l) (n : ℕ) :
    towerMap F.tower (Nat.le_succ n) = F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega) := rfl

namespace IsLAdicSystem

variable {F : ProjectiveSystem.{v} Λ l} (hF : IsLAdicSystem F)
include hF

lemma mem_ker_iff (n : ℕ) (x : F.term (n + 1 : ℕ)) :
    (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom x = 0 ↔
      ∃ y : F.term (n + 1 : ℕ), l ^ (n + 1) • y = x := by
  rw [← LinearMap.mem_ker, hF.ker_eq n]
  simp

/-- The isomorphism `F_{n+1} / l^{n+1} F_{n+1} ≃ F_n` induced by `u_{n+1}`. -/
noncomputable def quotEquiv (n : ℕ) :
    (F.term (n + 1 : ℕ) ⧸ LinearMap.range
      (l ^ (n + 1) • LinearMap.id : F.term (n + 1 : ℕ) →ₗ[Λ] F.term (n + 1 : ℕ))) ≃ₗ[Λ]
      F.term n :=
  (Submodule.quotEquivOfEq _ _ (hF.ker_eq n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (hF.surjective n))

@[simp]
lemma quotEquiv_mk (n : ℕ) (x : F.term (n + 1 : ℕ)) :
    hF.quotEquiv n (Submodule.Quotient.mk x) =
      (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom x := rfl

end IsLAdicSystem

/-- For `l` the image of a natural number `ℓ`, the conditions of an `l`-adic system on the
non-negative degrees (`l^{n+1} F_n = 0`, and `u_{n+1}` surjective with kernel `l^{n+1} F_{n+1}`)
say exactly that the restricted tower is strict `ℓ`-adic. -/
theorem isStrict_tower_iff {ℓ : ℕ} (F : ProjectiveSystem.{v} Λ (ℓ : Λ)) :
    LAdicTower.IsStrict F.tower ℓ ↔
      (∀ (n : ℕ) (x : F.term n), (ℓ : Λ) ^ (n + 1) • x = 0) ∧
      (∀ n : ℕ, Function.Surjective (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom) ∧
      (∀ n : ℕ, LinearMap.ker (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom =
        LinearMap.range ((ℓ : Λ) ^ (n + 1) • LinearMap.id :
          F.term (n + 1 : ℕ) →ₗ[Λ] F.term (n + 1 : ℕ))) := by
  have hann : ∀ n : ℕ, ℓ ^ (n + 1) • 𝟙 (towerObj F.tower n) = 0 ↔
      ∀ x : F.term n, (ℓ : Λ) ^ (n + 1) • x = 0 := by
    intro n
    constructor
    · intro h x
      have := congrArg (fun f => f.hom x) h
      simpa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using this
    · intro h
      ext x
      simpa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using h x
  have hexact : ∀ n : ℕ, ∀ (h0 : (ℓ ^ (n + 1) • 𝟙 (towerObj F.tower (n + 1))) ≫
      towerMap F.tower (Nat.le_succ n) = 0),
      (ShortComplex.mk _ _ h0).Exact ↔
        LinearMap.ker (F.mapLE (m := n) (n := (n + 1 : ℕ)) (by omega)).hom ≤
          LinearMap.range ((ℓ : Λ) ^ (n + 1) • LinearMap.id :
            F.term (n + 1 : ℕ) →ₗ[Λ] F.term (n + 1 : ℕ)) := by
    intro n h0
    rw [ShortComplex.moduleCat_exact_iff]
    constructor
    · intro h x hx
      obtain ⟨y, hy⟩ := h x hx
      exact ⟨y, by simpa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hy⟩
    · intro h x hx
      obtain ⟨y, hy⟩ := h hx
      exact ⟨y, by simpa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hy⟩
  constructor
  · intro hS
    refine ⟨fun n => (hann n).1 (hS.annihilated n), fun n => ?_, fun n => ?_⟩
    · have := hS.epi n
      exact (ModuleCat.epi_iff_surjective _).1 this
    · refine le_antisymm ((hexact n _).1 (hS.shortComplex_exact n)) ?_
      rintro _ ⟨y, rfl⟩
      have h := LAdicTower.nsmul_id_comp_eq_zero hS.annihilated n
      have := congrArg (fun f => f.hom y) h
      simp only [ModuleCat.hom_comp, ModuleCat.hom_nsmul, ModuleCat.hom_id, ModuleCat.hom_zero,
        LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply,
        map_nsmul] at this
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow,
        Nat.cast_smul_eq_nsmul, map_nsmul]
      exact this
  · rintro ⟨h1, h2, h3⟩
    have hann' : ∀ n : ℕ, ℓ ^ (n + 1) • 𝟙 (towerObj F.tower n) = 0 := fun n => (hann n).2 (h1 n)
    refine ⟨hann', fun n X x hx => ?_, fun n => (ModuleCat.epi_iff_surjective _).2 (h2 n)⟩
    have hE := (hexact n (LAdicTower.nsmul_id_comp_eq_zero hann' n)).2 (h3 n).le
    exact hE.exact_up_to_refinements x hx

/-- The restriction to the non-negative degrees of an `l`-adic system, `l` the image of a
natural number `ℓ`, is a strict `ℓ`-adic tower. -/
theorem IsLAdicSystem.isStrict {ℓ : ℕ} {F : ProjectiveSystem.{v} Λ (ℓ : Λ)}
    (hF : IsLAdicSystem F) : LAdicTower.IsStrict F.tower ℓ :=
  (isStrict_tower_iff F).2 ⟨hF.pow_smul_eq_zero, hF.surjective, hF.ker_eq⟩

end ProjectiveSystem

end CategoryTheory
