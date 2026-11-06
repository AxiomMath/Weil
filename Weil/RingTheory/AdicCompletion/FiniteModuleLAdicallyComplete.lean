module

public import Weil.Attr
public import Weil.Defs.RingTheory.AdicCompletion.Basic
public import Weil.Defs.Algebra.Category.ModuleCat.Limits
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Finite modules are `l`-adically complete

Let `Λ` be a commutative ring and `l ∈ Λ`. For a `Λ`-module `M` there is the natural map
`M → lim S(M) = lim_n M / l^{n+1} M`, `x ↦ (x mod l^{n+1})_n`, from `M` to the projective limit of
its projective system `S(M)`. It is an isomorphism as soon as `M` is `(l)`-adically complete:
injectivity is the Hausdorff property `⋂_n l^n M = 0`, surjectivity is the convergence of the
Cauchy sequence formed by lifts of the components of a compatible family.

If `Λ` is noetherian and `(l)`-adically complete (for instance `Λ = ℤ_ℓ` and `l = ℓ`), every
finitely generated `Λ`-module is `(l)`-adically complete: by Krull's intersection theorem
`⋂_n l^n M = 0` (since `l` lies in the Jacobson radical of the complete ring `Λ`), and a finite
module over a complete ring with vanishing intersection is complete. Hence for a finitely
generated `Λ`-module `M` the map `M → lim S(M)` is an isomorphism.

## Main definitions

* `CategoryTheory.ProjectiveSystem.toLimOfModule l M`: the map `M → lim S(M)`,
  `x ↦ (x mod l^{n+1})_n`.

## Main results

* `CategoryTheory.ProjectiveSystem.bijective_toLimOfModule_of_isAdicComplete`: for an
  `(l)`-adically complete `M`, the map `M → lim S(M)` is bijective.
* `CategoryTheory.ProjectiveSystem.bijective_toLimOfModule`: for a finitely generated module over
  a noetherian `(l)`-adically complete ring, the map `M → lim S(M)` is bijective.
* `CategoryTheory.ProjectiveSystem.toLimOfModuleEquiv`: the resulting isomorphism
  `M ≃ lim S(M)`.
* `PadicInt.bijective_toLimOfModule`: the case `Λ = ℤ_ℓ`, `l = ℓ`.

## Implementation notes

The source proves surjectivity by choosing a surjection `Λ^k → M` and passing to the limit using
the Mittag-Leffler property of the kernel system. We use instead that a finite module over an
`(l)`-adically complete ring with `⋂_n l^n M = 0` is `(l)`-adically complete
(`isAdicComplete_of_iInf_smul_eq_bot`, whose proof goes through the surjection
`Λ^∧ ⊗ M → M^∧`), and then show directly that the map to the limit of `S(M)` is bijective for
every `(l)`-adically complete module. The statement is proved for a noetherian `(l)`-adically
complete ring `Λ`, which contains the source's case `Λ = ℤ_ℓ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] (l : Λ)

/-- The natural map `M → lim S(M) = lim_n M / l^{n+1} M`, `x ↦ (x mod l^{n+1})_n`. -/
@[weil "lem_fk112_finite_module_l_adically_complete"]
def toLimOfModule (M : ModuleCat.{v} Λ) :
    M →ₗ[Λ] ModuleCat.sectionsSubmodule ((ofModule l).obj M).obj where
  toFun x := ⟨fun _ => Submodule.Quotient.mk x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {l}

@[simp]
lemma toLimOfModule_apply (M : ModuleCat.{v} Λ) (x : M) (n : ℤᵒᵖ) :
    (toLimOfModule l M x).1 n = Submodule.Quotient.mk x := rfl

/-- If `M` is `(l)`-adically complete, the map `M → lim S(M)` is bijective. -/
theorem bijective_toLimOfModule_of_isAdicComplete (M : ModuleCat.{v} Λ)
    [IsAdicComplete (Ideal.span {l}) M] : Function.Bijective (toLimOfModule l M) := by
  set I := Ideal.span {l}
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine IsHausdorff.haus (I := I) inferInstance x fun n => ?_
    rw [SModEq.sub_mem, sub_zero]
    have h := congrArg (fun s => s.1 (op (n : ℤ))) hx
    simp only [toLimOfModule_apply] at h
    change (Submodule.Quotient.mk x : M ⧸ (I ^ ((n : ℤ) + 1).toNat • ⊤ : Submodule Λ M)) = 0 at h
    rw [Submodule.Quotient.mk_eq_zero, show ((n : ℤ) + 1).toNat = n + 1 by omega] at h
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) h
  · intro s
    -- lifts of the components of `s`
    have hlift : ∀ k : ℕ, ∃ y : M,
        (Submodule.Quotient.mk y : M ⧸ (I ^ ((k : ℤ) + 1).toNat • ⊤ : Submodule Λ M)) =
          s.1 (op (k : ℤ)) := fun k => Submodule.Quotient.mk_surjective _ _
    choose f hf using hlift
    -- the lifts are compatible modulo `I^{m+1} M`
    have hcomp : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (I ^ (m + 1) • ⊤ : Submodule Λ M)] := by
      intro m n hmn
      have hs := s.2 (homOfLE (by exact_mod_cast hmn : (m : ℤ) ≤ n)).op
      rw [← hf n, ← hf m] at hs
      change (Submodule.Quotient.mk (f n) :
        M ⧸ (I ^ ((m : ℤ) + 1).toNat • ⊤ : Submodule Λ M)) = Submodule.Quotient.mk (f m) at hs
      rw [show ((m : ℤ) + 1).toNat = m + 1 by omega] at hs
      exact (SModEq.def.mpr hs).symm
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance
      (f := f) fun {m n} hmn =>
        SModEq.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ m)))
          (hcomp hmn)
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    obtain ⟨n⟩ := n
    rcases lt_or_ge n 0 with hn | hn
    · exact (ModuleCat.isZero_iff_subsingleton.mp (isZero_ofModule_term M hn)).elim _ _
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [toLimOfModule_apply, ← hf k]
      change (Submodule.Quotient.mk L :
        M ⧸ (I ^ ((k : ℤ) + 1).toNat • ⊤ : Submodule Λ M)) = Submodule.Quotient.mk (f k)
      rw [show ((k : ℤ) + 1).toNat = k + 1 by omega]
      exact SModEq.def.mp ((hcomp (Nat.le_succ k)).trans (hL (k + 1))).symm

variable (l) in
/-- For a finitely generated module `M` over a noetherian `(l)`-adically complete ring `Λ`, the
map `M → lim S(M) = lim_n M / l^{n+1} M`, `x ↦ (x mod l^{n+1})_n`, is bijective. -/
@[weil "lem_fk112_finite_module_l_adically_complete"]
theorem bijective_toLimOfModule [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {l}) Λ]
    (M : ModuleCat.{v} Λ) [Module.Finite Λ M] : Function.Bijective (toLimOfModule l M) := by
  have : IsAdicComplete (Ideal.span {l}) M :=
    isAdicComplete_of_iInf_smul_eq_bot _
      (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ (IsAdicComplete.le_jacobson_bot _))
  exact bijective_toLimOfModule_of_isAdicComplete M

variable (l) in
/-- For a finitely generated module `M` over a noetherian `(l)`-adically complete ring `Λ`, the
isomorphism `M ≃ lim S(M)`, `x ↦ (x mod l^{n+1})_n`. -/
noncomputable def toLimOfModuleEquiv [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {l}) Λ]
    (M : ModuleCat.{v} Λ) [Module.Finite Λ M] :
    M ≃ₗ[Λ] ModuleCat.sectionsSubmodule ((ofModule l).obj M).obj :=
  LinearEquiv.ofBijective (toLimOfModule l M) (bijective_toLimOfModule l M)

@[simp]
lemma toLimOfModuleEquiv_apply [IsNoetherianRing Λ] [IsAdicComplete (Ideal.span {l}) Λ]
    (M : ModuleCat.{v} Λ) [Module.Finite Λ M] (x : M) :
    toLimOfModuleEquiv l M x = toLimOfModule l M x := rfl

end ProjectiveSystem

end CategoryTheory

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- `ℤ_p` is `p`-adically complete. -/
instance isAdicComplete_span_p : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← maximalIdeal_eq_span_p]
  infer_instance

/-- For a finitely generated `ℤ_p`-module `M`, the map `M → lim_n M / p^{n+1} M` is bijective. -/
theorem bijective_toLimOfModule (M : ModuleCat.{v} ℤ_[p]) [Module.Finite ℤ_[p] M] :
    Function.Bijective (CategoryTheory.ProjectiveSystem.toLimOfModule (p : ℤ_[p]) M) :=
  CategoryTheory.ProjectiveSystem.bijective_toLimOfModule _ M

end PadicInt

end
