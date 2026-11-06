module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.LAdicSystem
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ShiftNaturalMap

/-!
# Iterated transition maps of an `l`-adic system

Let `F = (F_n, u_n)` be an `l`-adic system. For `n ≥ 0` and `r ≥ 0` the natural map
`ε^r_{F,n} = u_{n+1} ∘ ⋯ ∘ u_{n+r} : F_{n+r} → F_n` is surjective with kernel `l^{n+1} F_{n+r}`,
so that it induces an isomorphism `F_{n+r} / l^{n+1} F_{n+r} ≃ F_n`.

## Main results

* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.surjective_mapLE`,
  `CategoryTheory.ProjectiveSystem.IsLAdicSystem.ker_mapLE`: for `0 ≤ m ≤ k` the map
  `F_k → F_m` of an `l`-adic system is surjective with kernel `l^{m+1} F_k`.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.surjective_natMap_app`,
  `CategoryTheory.ProjectiveSystem.IsLAdicSystem.ker_natMap_app`: the natural map
  `ε^r_{F,n} : F_{n+r} → F_n` is surjective with kernel `l^{n+1} F_{n+r}`.

## Implementation notes

The proof is by induction on the length of the transition, as in the source. The same
statements for strict `ℓ`-adic towers, `ℓ` a natural number, are
`CategoryTheory.LAdicTower.IsStrict.towerMap_epi` and
`CategoryTheory.LAdicTower.IsStrict.towerMap_exact`; the direct proof here covers every
`l ∈ Λ`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

lemma mapLE_comp (F : ProjectiveSystem.{v} Λ l) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    F.mapLE hbc ≫ F.mapLE hab = F.mapLE (hab.trans hbc) := by
  rw [mapLE, mapLE, mapLE, ← F.obj.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

namespace IsLAdicSystem

variable {F : ProjectiveSystem.{v} Λ l} (hF : IsLAdicSystem F)
include hF

private lemma surjective_ker_mapLE_nat (m : ℕ) :
    ∀ (k : ℕ) (h : m ≤ k), Function.Surjective (F.mapLE (m := m) (n := k) (by omega)).hom ∧
      LinearMap.ker (F.mapLE (m := m) (n := k) (by omega)).hom ≤
        LinearMap.range (l ^ (m + 1) • LinearMap.id : F.term k →ₗ[Λ] F.term k) := by
  intro k h
  induction k, h using Nat.le_induction with
  | base =>
    have e : F.mapLE (m := m) (n := m) le_rfl = 𝟙 _ := by
      rw [mapLE, ← F.obj.map_id]; rfl
    refine ⟨?_, ?_⟩
    · rw [e]; exact fun x => ⟨x, rfl⟩
    · intro x hx
      rw [e] at hx
      exact ⟨0, by simpa using hx.symm⟩
  | succ k hmk ih =>
    obtain ⟨ihs, ihk⟩ := ih
    have hc := F.mapLE_comp (a := m) (b := k) (c := (k + 1 : ℕ)) (by omega) (by omega)
    rw [← hc]
    refine ⟨?_, ?_⟩
    · rw [ModuleCat.hom_comp, LinearMap.coe_comp]
      exact ihs.comp (hF.surjective k)
    · intro x hx
      rw [LinearMap.mem_ker, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
      obtain ⟨y, hy⟩ := ihk hx
      obtain ⟨y', rfl⟩ := hF.surjective k y
      have hz : (F.mapLE (m := k) (n := (k + 1 : ℕ)) (by omega)).hom
          (x - l ^ (m + 1) • y') = 0 := by
        rw [map_sub, map_smul, ← hy]
        simp
      obtain ⟨z, hz⟩ := (hF.mem_ker_iff k _).1 hz
      refine ⟨y' + l ^ (k - m) • z, ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_add, smul_smul]
      rw [← pow_add, show m + 1 + (k - m) = k + 1 by omega, hz]
      abel

/-- For `0 ≤ m ≤ k`, the map `F_k → F_m` of an `l`-adic system is surjective. -/
theorem surjective_mapLE (m : ℕ) {k : ℤ} (h : (m : ℤ) ≤ k) :
    Function.Surjective (F.mapLE h).hom := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k)
  exact (hF.surjective_ker_mapLE_nat m j (by omega)).1

/-- For `0 ≤ m ≤ k`, the kernel of the map `F_k → F_m` of an `l`-adic system is
`l^{m+1} F_k`. -/
theorem ker_mapLE (m : ℕ) {k : ℤ} (h : (m : ℤ) ≤ k) :
    LinearMap.ker (F.mapLE h).hom =
      LinearMap.range (l ^ (m + 1) • LinearMap.id : F.term k →ₗ[Λ] F.term k) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ k)
    exact (hF.surjective_ker_mapLE_nat m j (by omega)).2
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
    exact hF.pow_smul_eq_zero m _

/-- For `n, r ≥ 0`, the natural map `ε^r_{F,n} : F_{n+r} → F_n` of an `l`-adic system is
surjective. -/
@[weil "lem_fk112_l_adic_transition_surjective_kernel"]
theorem surjective_natMap_app (n r : ℕ) :
    Function.Surjective (app (natMap F r) n).hom := by
  rw [natMap_app]
  exact hF.surjective_mapLE n _

/-- For `n, r ≥ 0`, the kernel of the natural map `ε^r_{F,n} : F_{n+r} → F_n` of an `l`-adic
system is `l^{n+1} F_{n+r}`. -/
@[weil "lem_fk112_l_adic_transition_surjective_kernel"]
theorem ker_natMap_app (n r : ℕ) :
    LinearMap.ker (app (natMap F r) n).hom =
      LinearMap.range (l ^ (n + 1) • LinearMap.id :
        F.term (n + r) →ₗ[Λ] F.term (n + r)) := by
  rw [natMap_app]
  exact hF.ker_mapLE n _

end IsLAdicSystem

end ProjectiveSystem

end CategoryTheory
