module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.ObjectProperty.LAdicSystem
public import WeilFrontier.Defs.Algebra.Category.ModuleCat.Limits
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit

/-!
# An `l`-adic system is the system of quotients of its limit

Let `F = (F_n, u_n)` be an `l`-adic system and `M = lim F` its projective limit. For every
`n ≥ 0` the projection `π_n : M → F_n` is surjective with kernel `l^{n+1} M`, so that it
induces an isomorphism `σ_n : M / l^{n+1} M ≃ F_n`.

## Main definitions

* `CategoryTheory.ProjectiveSystem.limProj F n`: the projection `π_n : lim F → F_n`.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.limQuotEquiv`: the isomorphism
  `σ_n : M / l^{n+1} M ≃ F_n` induced by `π_n`.

## Main results

* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.surjective_limProj`: `π_n` is surjective.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.ker_limProj`: the kernel of `π_n` is
  `l^{n+1} M`.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.limQuotEquiv_mk`: `σ_n` is induced by `π_n`.

## Implementation notes

The source deduces the kernel computation from the Mittag-Leffler property of the kernel
system `(F_m[l^{n+1}])_m`, which holds as the `F_m` have finite length. Here it is deduced from
[StacksProject 09B8] (`Stacks.AdicCompletion.InverseLimit.InverseSystem.quotientEquiv`), for the
finitely generated ideal `(l)`, applied to the reindexed tower `k ↦ F_{k-1}`: its transition
maps `F_k → F_{k-1}` are surjective with kernel `l^k F_k`, and `F_{-1} = 0`. That argument does
not use the finite length of the `F_n`, so neither do the results here.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
* [StacksProject] The Stacks project, Tag 09B8.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The projection `π_n : lim F → F_n` from the projective limit of a projective system. -/
def limProj (F : ProjectiveSystem.{v} Λ l) (n : ℤ) :
    ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] F.term n :=
  (LinearMap.proj (op n)).comp (ModuleCat.sectionsSubmodule F.obj).subtype

@[simp]
lemma limProj_apply (F : ProjectiveSystem.{v} Λ l) (n : ℤ)
    (x : ModuleCat.sectionsSubmodule F.obj) : F.limProj n x = x.1 (op n) := rfl

lemma mapLE_self (F : ProjectiveSystem.{v} Λ l) (a : ℤ) : F.mapLE (le_refl a) = 𝟙 _ := by
  rw [mapLE, ← F.obj.map_id]; rfl

lemma mapLE_mapLE_apply (F : ProjectiveSystem.{v} Λ l) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c)
    (x : F.term c) :
    (F.mapLE hab).hom ((F.mapLE hbc).hom x) = (F.mapLE (hab.trans hbc)).hom x := by
  rw [← F.mapLE_comp hab hbc]
  rfl

lemma pow_smul_top_eq_range {M : Type*} [AddCommGroup M] [Module Λ M] (r : Λ) (k : ℕ) :
    Ideal.span {r} ^ k • (⊤ : Submodule Λ M) =
      LinearMap.range (r ^ k • LinearMap.id : M →ₗ[Λ] M) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]

namespace IsLAdicSystem

variable {F : ProjectiveSystem.{v} Λ l} (hF : IsLAdicSystem F)
include hF

/-- Every map `F_b → F_a`, `a ≤ b`, of an `l`-adic system is surjective. -/
lemma surjective_mapLE_int {a b : ℤ} (h : a ≤ b) :
    Function.Surjective (F.mapLE h).hom := by
  rcases lt_or_ge a 0 with ha | ha
  · intro y
    have hz := ModuleCat.isZero_iff_subsingleton.1 (hF.isZero_of_neg a ha)
    exact ⟨0, Subsingleton.elim _ _⟩
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    exact hF.surjective_mapLE m h

/-- The kernel of a map `F_b → F_a`, `a ≤ b`, of an `l`-adic system is `l^{a+1} F_b` (read as
`F_b` when `a < 0`). -/
lemma ker_mapLE_int {a b : ℤ} (h : a ≤ b) :
    LinearMap.ker (F.mapLE h).hom =
      LinearMap.range (l ^ (a + 1).toNat • LinearMap.id : F.term b →ₗ[Λ] F.term b) := by
  rcases lt_or_ge a 0 with ha | ha
  · have h0 : (a + 1).toNat = 0 := by omega
    have hz := ModuleCat.isZero_iff_subsingleton.1 (hF.isZero_of_neg a ha)
    rw [h0]
    ext x
    simp only [LinearMap.mem_ker, pow_zero, one_smul, LinearMap.range_id, Submodule.mem_top,
      iff_true]
    exact Subsingleton.elim _ _
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega]
    exact hF.ker_mapLE m h

/-- The tower `k ↦ F_{k-1}`, `k ∈ ℕ`, of an `l`-adic system, as an inverse system in the sense
of [StacksProject 09B8] for the ideal `(l)`. -/
noncomputable abbrev reindexedSystem : Stacks.AdicCompletion.InverseLimit.InverseSystem
    (Ideal.span {l}) where
  M k := F.term ((k : ℤ) - 1)
  π k := (F.mapLE (by push_cast; omega : (k : ℤ) - 1 ≤ ((k + 1 : ℕ) : ℤ) - 1)).hom
  surjective k := hF.surjective_mapLE_int _
  ker_π k := by
    rw [pow_smul_top_eq_range, hF.ker_mapLE_int _]
    congr 3
    omega


/-- A compatible family of the reindexed tower is compatible with all its maps. -/
lemma mapLE_apply_of_mem_limit {s : ∀ k, hF.reindexedSystem.M k}
    (hs : s ∈ hF.reindexedSystem.limit) (i j : ℕ) (hij : i ≤ j)
    (h : (i : ℤ) - 1 ≤ (j : ℤ) - 1) : (F.mapLE h).hom (s j) = s i := by
  induction j, hij using Nat.le_induction with
  | base => rw [mapLE_self]; rfl
  | succ j hij ih =>
    rw [← F.mapLE_comp (b := (j : ℤ) - 1) (by omega) (by push_cast; omega), ModuleCat.hom_comp,
      LinearMap.comp_apply]
    exact (congrArg _ (hs j)).trans (ih (by omega))

/-- The projective limit of an `l`-adic system is the limit of its reindexed tower
`k ↦ F_{k-1}`. -/
noncomputable def limEquivReindexed :
    ModuleCat.sectionsSubmodule F.obj ≃ₗ[Λ] hF.reindexedSystem.limit where
  toFun x := ⟨fun k => x.1 (op ((k : ℤ) - 1)), fun k => x.2 _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun s := ⟨fun a => (F.mapLE (by omega : a.unop ≤ ((a.unop.toNat + 1 : ℕ) : ℤ) - 1)).hom
      (s.1 (a.unop.toNat + 1)), by
    rintro ⟨a⟩ ⟨b⟩ f
    have hba : b ≤ a := leOfHom f.unop
    obtain rfl : f = (homOfLE hba).op := Subsingleton.elim _ _
    change (F.mapLE hba).hom ((F.mapLE _).hom (s.1 (a.toNat + 1))) =
      (F.mapLE _).hom (s.1 (b.toNat + 1))
    rw [← hF.mapLE_apply_of_mem_limit s.2 (b.toNat + 1) (a.toNat + 1) (by omega) (by omega),
      mapLE_mapLE_apply, mapLE_mapLE_apply]⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    exact x.2 (homOfLE _).op
  right_inv s := by
    refine Subtype.ext (funext fun k => ?_)
    exact hF.mapLE_apply_of_mem_limit s.2 k (((k : ℤ) - 1).toNat + 1) (by omega) _

@[simp]
lemma coe_limEquivReindexed_apply (x : ModuleCat.sectionsSubmodule F.obj) (k : ℕ) :
    (hF.limEquivReindexed x).1 k = x.1 (op ((k : ℤ) - 1)) := rfl

/-- For an `l`-adic system `F` and `n ≥ 0`, the projection `π_n : lim F → F_n` is
surjective. -/
theorem surjective_limProj (n : ℕ) : Function.Surjective (F.limProj n) := by
  intro y
  obtain ⟨s, hs⟩ := hF.reindexedSystem.proj_surjective (n + 1)
    ((F.mapLE (by push_cast; omega : ((n + 1 : ℕ) : ℤ) - 1 ≤ n)).hom y)
  refine ⟨hF.limEquivReindexed.symm s, ?_⟩
  change (F.mapLE _).hom (s.1 ((n : ℤ).toNat + 1)) = y
  have e := hF.mapLE_apply_of_mem_limit s.2 (n + 1) ((n : ℤ).toNat + 1) (by omega)
    (by push_cast; omega)
  have h3 : (n : ℤ) ≤ ((n + 1 : ℕ) : ℤ) - 1 := by push_cast; omega
  calc _ = (F.mapLE h3).hom ((F.mapLE (by push_cast; omega :
          ((n + 1 : ℕ) : ℤ) - 1 ≤ (((n : ℤ).toNat + 1 : ℕ) : ℤ) - 1)).hom
          (s.1 ((n : ℤ).toNat + 1))) := by
        rw [mapLE_mapLE_apply]
    _ = (F.mapLE h3).hom (hF.reindexedSystem.proj (n + 1) s) := by rw [e]; rfl
    _ = y := by rw [hs, mapLE_mapLE_apply, mapLE_self]; rfl

/-- For an `l`-adic system `F` and `n ≥ 0`, the kernel of the projection `π_n : M → F_n`,
`M = lim F`, is `l^{n+1} M`. -/
theorem ker_limProj (n : ℕ) :
    LinearMap.ker (F.limProj n) =
      LinearMap.range (l ^ (n + 1) • LinearMap.id :
        ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule F.obj) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have hx' : hF.limEquivReindexed x ∈ LinearMap.ker (hF.reindexedSystem.proj (n + 1)) := by
      rw [LinearMap.mem_ker]
      change x.1 (op (((n + 1 : ℕ) : ℤ) - 1)) = 0
      rw [← x.2 (homOfLE (by push_cast; omega : ((n + 1 : ℕ) : ℤ) - 1 ≤ n)).op]
      rw [LinearMap.mem_ker, limProj_apply] at hx
      change (F.mapLE _).hom _ = 0
      rw [hx, map_zero]
    rw [hF.reindexedSystem.ker_proj ⟨{l}, by simp⟩ (n + 1)] at hx'
    have := Submodule.mem_map_of_mem (f := hF.limEquivReindexed.symm.toLinearMap) hx'
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range,
      pow_smul_top_eq_range] at this
    simpa using this
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    exact hF.pow_smul_eq_zero n _

/-- For an `l`-adic system `F`, `M = lim F` and `n ≥ 0`, the isomorphism
`σ_n : M / l^{n+1} M ≃ F_n` induced by the projection `π_n : M → F_n`
(`limQuotEquiv_mk`). -/
@[weil "lem_fk112_l_adic_system_from_limit"]
noncomputable def limQuotEquiv (n : ℕ) :
    (ModuleCat.sectionsSubmodule F.obj ⧸ LinearMap.range (l ^ (n + 1) • LinearMap.id :
        ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule F.obj)) ≃ₗ[Λ]
      F.term n :=
  (Submodule.quotEquivOfEq _ _ (hF.ker_limProj n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (hF.surjective_limProj n))

/-- The isomorphism `σ_n : M / l^{n+1} M ≃ F_n` sends the class of `x ∈ M` to `π_n(x)`. -/
@[weil "lem_fk112_l_adic_system_from_limit", simp]
lemma limQuotEquiv_mk (n : ℕ) (x : ModuleCat.sectionsSubmodule F.obj) :
    hF.limQuotEquiv n (Submodule.Quotient.mk x) = F.limProj n x := rfl

end IsLAdicSystem

end ProjectiveSystem

end CategoryTheory
