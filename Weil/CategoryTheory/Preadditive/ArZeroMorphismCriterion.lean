module

public import Weil.Attr
public import Weil.CategoryTheory.Preadditive.Biproducts

/-!
# Morphisms killed by the canonical functor to the Artin–Rees category

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules and
`q : 𝒫 ⥤ AR` the canonical functor to the Artin–Rees category. A morphism `f : F ⟶ G` of `𝒫`
satisfies `q(f) = 0` if and only if `f ∘ ε^t_F = 0` for some `t ≥ 0`, where `ε^t_F : F[t] ⟶ F`
is the natural map of the shifted system.

## Main results

* `CategoryTheory.ProjectiveSystem.toArCategory_map_eq_zero_iff`: `q(f) = 0` if and only if
  there is `t ≥ 0` with `f ∘ ε^t_F = 0`.
* `CategoryTheory.ProjectiveSystem.ArCategory.homMk_eq_zero_iff`: more generally, the A–R
  morphism `[r, f]` is zero if and only if `f ∘ (F[t] ⟶ F[r]) = 0` for some `t ≥ r`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- The A–R morphism `[r, f]` is zero if and only if `f` vanishes after precomposition with
`F[t] ⟶ F[r]` for some `t ≥ r`. -/
lemma ArCategory.homMk_eq_zero_iff {F G : ProjectiveSystem.{v} Λ l} {r : ℕ}
    (f : (shift (r : ℤ)).obj F ⟶ G) :
    ArCategory.homMk r f = 0 ↔ ∃ (t : ℕ) (h : r ≤ t), shiftMap F h ≫ f = 0 := by
  rw [← ArCategory.homMk_zero (F := F) (G := G) r]
  change ArHom.mk r f = ArHom.mk r 0 ↔ _
  rw [ArHom.mk_eq_mk_iff_rel]
  refine ⟨fun ⟨t, hr, _, e⟩ => ⟨t, hr, e.trans Limits.comp_zero⟩,
    fun ⟨t, hr, e⟩ => ⟨t, hr, hr, e.trans Limits.comp_zero.symm⟩⟩

/-- **Morphisms killed by the canonical functor to the A–R category**: a morphism `f : F ⟶ G` of
projective systems satisfies `q(f) = 0` if and only if there is `t ≥ 0` with
`f ∘ ε^t_F = 0`. -/
@[weil "lem_fk112_ar_zero_morphism_criterion"]
theorem toArCategory_map_eq_zero_iff {F G : ProjectiveSystem.{v} Λ l} (f : F ⟶ G) :
    (toArCategory Λ l).map f = 0 ↔ ∃ t : ℕ, natMap F t ≫ f = 0 := by
  refine (ArCategory.homMk_eq_zero_iff (natMap F 0 ≫ f)).trans ?_
  constructor
  · rintro ⟨t, h, e⟩
    exact ⟨t, by rwa [shiftMap_comp_natMap_assoc] at e⟩
  · rintro ⟨t, e⟩
    exact ⟨t, Nat.zero_le t, by rwa [shiftMap_comp_natMap_assoc]⟩

end ProjectiveSystem

end CategoryTheory
