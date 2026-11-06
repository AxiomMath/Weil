module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.ObjectProperty.LAdicSystem
public import WeilFrontier.CategoryTheory.Preadditive.ArZeroMorphismCriterion

/-!
# Morphisms from an `l`-adic system to a strict system in the Artin–Rees category

Let `F` be an `l`-adic system and `G` a projective system of `l`-power torsion `Λ`-modules
with `G_{-1} = 0` and `l^{n+1} G_n = 0` for all `n ≥ 0`. Then the canonical functor `q` to the
Artin–Rees category induces a bijection `Hom(F, G) ≃ Hom_AR(F, G)`, `g ↦ [0, g]`.

Injectivity: if `q(g) = 0` then `g ∘ ε^t_F = 0` for some `t`, and every component of
`ε^t_F` is surjective, so `g = 0`. Surjectivity: an A–R morphism `[r, f]` with `f : F[r] ⟶ G`
factors as `f = g ∘ ε^r_F`, since each component `ε^r_{F,n} : F_{n+r} → F_n` is surjective
and `f_n` kills its kernel (for `n ≥ 0` this kernel is `l^{n+1} F_{n+r}`, killed because
`l^{n+1} G_n = 0`; for `n < 0` the component `f_n` itself vanishes, as it factors through
`G_{-1} = 0` on the image of a surjection); then `[r, f] = [0, g]`.

## Main results

* `CategoryTheory.ProjectiveSystem.exists_comp_eq_of_surjective`: a morphism `f : F' ⟶ G`
  factors through a componentwise surjective `e : F' ⟶ F` whose kernels `f` kills.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.surjective_natMap_app_int`: every component
  `ε^r_{F,n}`, `n ∈ ℤ`, of the natural map of an `l`-adic system is surjective.
* `CategoryTheory.ProjectiveSystem.IsLAdicSystem.bijective_toArCategory_map`: the map
  `q : Hom(F, G) → Hom_AR(F, G)` is bijective.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- A morphism `f : F' ⟶ G` of projective systems factors through a morphism `e : F' ⟶ F`
whose components are surjective, provided each component of `f` kills the kernel of the
corresponding component of `e`. -/
theorem exists_comp_eq_of_surjective {F' F G : ProjectiveSystem.{v} Λ l} (e : F' ⟶ F)
    (f : F' ⟶ G) (he : ∀ n, Function.Surjective (app e n).hom)
    (hf : ∀ n (x : F'.term n), (app e n).hom x = 0 → (app f n).hom x = 0) :
    ∃ g : F ⟶ G, e ≫ g = f := by
  have hepi : ∀ n, Epi (app e n) := fun n => (ModuleCat.epi_iff_surjective _).2 (he n)
  have hker : ∀ n, Limits.kernel.ι (app e n) ≫ app f n = 0 := fun n => by
    ext x
    have h := congrArg (fun φ => φ.hom x) (Limits.kernel.condition (app e n))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    simpa using hf n _ h
  let g : ∀ n, F.term n ⟶ G.term n := fun n => Abelian.epiDesc (app e n) (app f n) (hker n)
  have hg : ∀ n, app e n ≫ g n = app f n := fun n => Abelian.comp_epiDesc _ _ _
  refine ⟨homMk g fun n => ?_, hom_ext fun n => by simpa using hg n⟩
  rw [← cancel_epi (app e n), ← Category.assoc, hg, app_transition, app_transition_assoc,
    hg]

namespace IsLAdicSystem

variable {F : ProjectiveSystem.{v} Λ l} (hF : IsLAdicSystem F)
include hF

/-- For all `m ≤ k` in `ℤ`, the map `F_k → F_m` of an `l`-adic system is surjective: for
`m ≥ 0` by the transition maps, and for `m < 0` since `F_m = 0`. -/
theorem surjective_mapLE_int {m k : ℤ} (h : m ≤ k) : Function.Surjective (F.mapLE h).hom := by
  rcases lt_or_ge m 0 with hm | hm
  · intro y
    exact ⟨0, (ModuleCat.subsingleton_of_isZero (hF.isZero_of_neg m hm)).elim _ _⟩
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact hF.surjective_mapLE j h

/-- Every component `ε^r_{F,n} : F_{n+r} → F_n`, `n ∈ ℤ`, of the natural map of an `l`-adic
system is surjective. -/
theorem surjective_natMap_app_int (r : ℕ) (n : ℤ) :
    Function.Surjective (app (natMap F r) n).hom := by
  rw [natMap_app]
  exact hF.surjective_mapLE_int _

/-- If `ε^t_F ∘ g = 0` for an `l`-adic system `F`, then `g = 0`. -/
theorem eq_zero_of_natMap_comp_eq_zero {G : ProjectiveSystem.{v} Λ l} {t : ℕ} {g : F ⟶ G}
    (h : natMap F t ≫ g = 0) : g = 0 := by
  refine hom_ext fun n => ?_
  have hepi : Epi (app (natMap F t) n) :=
    (ModuleCat.epi_iff_surjective _).2 (hF.surjective_natMap_app_int t n)
  rw [← cancel_epi (app (natMap F t) n), ← comp_app, h]
  rfl

/-- **Morphisms from an `l`-adic system in the A–R category.** Let `F` be an `l`-adic system and
`G` a projective system with `G_{-1} = 0` and `l^{n+1} G_n = 0` for all `n ≥ 0`. Then the
canonical functor `q` to the Artin–Rees category induces a bijection
`Hom(F, G) → Hom_AR(F, G)`, `g ↦ [0, g]`. -/
@[weil "lem_fk112_hom_l_adic_equals_ar_hom"]
theorem bijective_toArCategory_map {G : ProjectiveSystem.{v} Λ l} (hG : IsZero (G.term (-1)))
    (hGl : ∀ (n : ℕ) (x : G.term n), l ^ (n + 1) • x = 0) :
    Function.Bijective (fun g : F ⟶ G => (toArCategory Λ l).map g) := by
  refine ⟨?_, ?_⟩
  · change Function.Injective ((toArCategory Λ l).mapAddHom (X := F) (Y := G))
    refine (injective_iff_map_eq_zero _).2 fun g hg => ?_
    obtain ⟨t, ht⟩ := (toArCategory_map_eq_zero_iff g).1 hg
    exact hF.eq_zero_of_natMap_comp_eq_zero ht
  · intro φ
    obtain ⟨r, f, rfl⟩ := ArCategory.homMk_surjective φ
    -- `f_n = 0` for `n < 0`: it factors through `G_{-1} = 0` on the image of a surjection.
    have hneg : ∀ n : ℤ, n < 0 → app f n = 0 := by
      intro n hn
      have hnat := f.hom.naturality (homOfLE (show n ≤ -1 by omega)).op
      change F.mapLE (show n + r ≤ -1 + r by omega) ≫ app f n =
        app f (-1) ≫ G.mapLE (show n ≤ -1 by omega) at hnat
      rw [hG.eq_of_tgt (app f (-1)) 0, zero_comp] at hnat
      have hepi : Epi (F.mapLE (show n + r ≤ -1 + r by omega)) :=
        (ModuleCat.epi_iff_surjective _).2 (hF.surjective_mapLE_int _)
      exact (cancel_epi (F.mapLE (show n + r ≤ -1 + r by omega))).1 (hnat.trans comp_zero.symm)
    obtain ⟨g, hg⟩ := exists_comp_eq_of_surjective (natMap F r) f
      (hF.surjective_natMap_app_int r) fun n x hx => by
        rcases lt_or_ge n 0 with hn | hn
        · rw [hneg n hn]; rfl
        · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
          have hx' : x ∈ LinearMap.ker (app (natMap F r) m).hom := hx
          rw [hF.ker_natMap_app m r] at hx'
          obtain ⟨y, rfl⟩ := hx'
          rw [LinearMap.smul_apply, LinearMap.id_apply]
          exact ((app f m).hom.map_smul _ _).trans (hGl m _)
    refine ⟨g, ?_⟩
    change ArCategory.homMk 0 (natMap F 0 ≫ g) = _
    rw [← ArCategory.homMk_shiftMap_comp (Nat.zero_le r), shiftMap_comp_natMap_assoc, hg]

end IsLAdicSystem

end ProjectiveSystem

end CategoryTheory
