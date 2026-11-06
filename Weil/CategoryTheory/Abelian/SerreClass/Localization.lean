module

public import Weil.Attr
public import Weil.CategoryTheory.Preadditive.ArZeroMorphismCriterion
public import Weil.CategoryTheory.Limits.Preserves.FunctorCategory
public import Weil.Defs.CategoryTheory.ObjectProperty.ArIsomorphism
public import Weil.CategoryTheory.Abelian.ArKernel

/-!
# Cokernels in the Artin–Rees category

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules and
`q : 𝒫 ⥤ AR` the canonical functor to the Artin–Rees category. If `φ = [r, f] : F ⟶ G` is an
A–R morphism with representative `f : F[r] ⟶ G`, and `p : G ⟶ C` is a cokernel of `f` in `𝒫`,
then `q(p) : G ⟶ C` is a cokernel of `φ` in the A–R category.

## Main results

* `CategoryTheory.ProjectiveSystem.ArCategory.isColimitToArCategoryMapCokernelCofork`: `q` sends
  a cokernel of a morphism of `𝒫` to a cokernel in the A–R category.
* `CategoryTheory.ProjectiveSystem.ArCategory.isColimitCokernelCoforkHomMk`: if `p` is a
  cokernel of `f : F[r] ⟶ G` in `𝒫`, then `q(p)` is a cokernel of `[r, f]`.

## Implementation notes

The source writes `[r, f] = q(f) ∘ q(ε^r_F)⁻¹` and checks the universal property of `q(p)` for
`q(f)`. Here the universal property is checked directly on representatives: an A–R morphism
`[s, h] : G ⟶ T` with `[s, h] ∘ q(f) = 0` satisfies `h ∘ f[s] ∘ (F[r][t] ⟶ F[r][s]) = 0` for
some `t ≥ s`, so `h ∘ (G[t] ⟶ G[s])` kills `f[t]` and factors through the cokernel `p[t]` of
`f[t]` (the shift is exact). The passage from `q(f)` to `[r, f]` is the factorization
`[r, f] = [r, id_{F[r]}] ∘ q(f)` by the epimorphism (indeed isomorphism) `[r, id_{F[r]}]`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

namespace ArCategory

/-- `[r, f] = [r, id_{F[r]}] ∘ q(f)` for `f : F[r] ⟶ G`. -/
lemma homMk_eq_homMk_id_comp {F G : ProjectiveSystem.{v} Λ l} {r : ℕ}
    (f : (shift (r : ℤ)).obj F ⟶ G) :
    homMk r f = homMk r (𝟙 _) ≫ (toArCategory Λ l).map f := by
  refine Eq.trans ?_ (homMk_comp_homMk (𝟙 _) (natMap _ 0 ≫ f)).symm
  rw [Functor.map_id, Category.id_comp, shiftShift_comp_natMap_zero_assoc, homMk_shiftMap_comp]

/-- `q(ε^r_F) ∘ [r, id_{F[r]}]` is the identity of `F`. -/
lemma homMk_id_comp_toArCategory_map_natMap (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    homMk r (𝟙 _) ≫ (toArCategory Λ l).map (natMap F r) = 𝟙 (of F) := by
  rw [← homMk_eq_homMk_id_comp, ArCategory.homMk_natMap]

/-- `[r, id_{F[r]}] ∘ q(ε^r_F)` is the identity of `F[r]`. -/
lemma toArCategory_map_natMap_comp_homMk_id (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    (toArCategory Λ l).map (natMap F r) ≫ homMk r (𝟙 _) = 𝟙 (of ((shift (r : ℤ)).obj F)) := by
  rw [toArCategory_map_comp_homMk, Category.comp_id, shift_map_natMap, ArCategory.homMk_natMap]

/-- The A–R morphism `[r, id_{F[r]}] : F ⟶ F[r]` is an isomorphism, with inverse `q(ε^r_F)`. -/
instance isIso_homMk_id (F : ProjectiveSystem.{v} Λ l) (r : ℕ) :
    IsIso (homMk (F := F) r (𝟙 ((shift (r : ℤ)).obj F))) :=
  ⟨⟨_, homMk_id_comp_toArCategory_map_natMap F r, toArCategory_map_natMap_comp_homMk_id F r⟩⟩

variable {G C : ProjectiveSystem.{v} Λ l}

/-- If `p : G ⟶ C` is an epimorphism of `𝒫` and `q(p) ∘ [s, c] = 0`, then `[s, c] = 0`. -/
lemma homMk_eq_zero_of_toArCategory_map_comp_eq_zero {p : G ⟶ C} [Epi p]
    {T : ProjectiveSystem.{v} Λ l} {s : ℕ} (c : (shift (s : ℤ)).obj C ⟶ T)
    (e : (toArCategory Λ l).map p ≫ homMk s c = 0) : homMk s c = 0 := by
  have e : homMk s ((shift (s : ℤ)).map p ≫ c) = 0 :=
    (toArCategory_map_comp_homMk p c).symm.trans e
  obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff _).1 e
  rw [← shiftMap_naturality_assoc] at e
  have e : shiftMap C hst ≫ c = 0 :=
    (cancel_epi ((shift (t : ℤ)).map p)).1 (e.trans Limits.comp_zero.symm)
  rw [← homMk_shiftMap_comp hst, e, homMk_zero]

/-- The image under `q` of an epimorphism of `𝒫` is an epimorphism of the A–R category. -/
instance epi_toArCategory_map (p : G ⟶ C) [Epi p] : Epi ((toArCategory Λ l).map p) := by
  refine ⟨fun {T} χ χ' e => ?_⟩
  obtain ⟨T⟩ := T
  rw [← sub_eq_zero] at e ⊢
  rw [← Preadditive.comp_sub] at e
  generalize χ - χ' = χ at e ⊢
  induction χ using hom_induction with
  | h s c => exact homMk_eq_zero_of_toArCategory_map_comp_eq_zero (p := p) c e

/-- If `p : G ⟶ C` is a cokernel of `f : F ⟶ G` in `𝒫`, every A–R morphism `ψ : G ⟶ T` with
`ψ ∘ q(f) = 0` factors through `q(p)`. -/
lemma exists_toArCategory_map_comp_eq_of_isColimit {F : ProjectiveSystem.{v} Λ l} {f : F ⟶ G}
    {p : G ⟶ C} {w : f ≫ p = 0} (hp : IsColimit (CokernelCofork.ofπ p w))
    {T : ProjectiveSystem.{v} Λ l} (ψ : of G ⟶ of T)
    (hψ : (toArCategory Λ l).map f ≫ ψ = 0) :
    ∃ k : of C ⟶ of T, (toArCategory Λ l).map p ≫ k = ψ := by
  obtain ⟨s, h, rfl⟩ := homMk_surjective ψ
  have e : homMk s ((shift (s : ℤ)).map f ≫ h) = 0 :=
    (toArCategory_map_comp_homMk f h).symm.trans hψ
  obtain ⟨t, hst, e⟩ := (homMk_eq_zero_iff _).1 e
  rw [← shiftMap_naturality_assoc] at e
  obtain ⟨k, hk⟩ := CokernelCofork.IsColimit.desc'
    (CokernelCofork.mapIsColimit _ hp (shift (t : ℤ))) (shiftMap G hst ≫ h) e
  refine ⟨homMk t k, (toArCategory_map_comp_homMk p k).trans ?_⟩
  change homMk t ((shift (t : ℤ)).map p ≫ k) = homMk s h
  rw [show (shift (t : ℤ)).map p ≫ k = shiftMap G hst ≫ h from hk, homMk_shiftMap_comp]

/-- **`q` preserves cokernels**: if `p : G ⟶ C` is a cokernel of `f : F ⟶ G` in `𝒫`, then
`q(p)` is a cokernel of `q(f)` in the A–R category. -/
noncomputable def isColimitToArCategoryMapCokernelCofork {F : ProjectiveSystem.{v} Λ l}
    {f : F ⟶ G} {p : G ⟶ C} {w : f ≫ p = 0} (hp : IsColimit (CokernelCofork.ofπ p w)) :
    IsColimit (CokernelCofork.ofπ ((toArCategory Λ l).map p)
      (by rw [← Functor.map_comp, w, Functor.map_zero]) :
        CokernelCofork ((toArCategory Λ l).map f)) :=
  have : Epi p := epi_of_isColimit_cofork hp
  CokernelCofork.IsColimit.ofπ _ _
    (fun {T} ψ hψ => Classical.choose
      (exists_toArCategory_map_comp_eq_of_isColimit hp (T := T.obj) ψ hψ))
    (fun {T} ψ hψ => Classical.choose_spec
      (exists_toArCategory_map_comp_eq_of_isColimit hp (T := T.obj) ψ hψ))
    (fun {T} ψ hψ m hm => by
      rw [← cancel_epi ((toArCategory Λ l).map p), hm]
      exact (Classical.choose_spec
        (exists_toArCategory_map_comp_eq_of_isColimit hp (T := T.obj) ψ hψ)).symm)

/-- **The cokernel of an A–R morphism, from a representative.** Let `φ = [r, f] : F ⟶ G` be an
A–R morphism with representative `f : F[r] ⟶ G`, and let `p : G ⟶ C` be a cokernel of `f` in
`𝒫`. Then `q(p) : G ⟶ C` is a cokernel of `φ` in the A–R category. -/
@[weil "lem_fk112_ar_cokernel_of_representative"]
noncomputable def isColimitCokernelCoforkHomMk {F : ProjectiveSystem.{v} Λ l} {r : ℕ}
    {f : (shift (r : ℤ)).obj F ⟶ G} {p : G ⟶ C} {w : f ≫ p = 0}
    (hp : IsColimit (CokernelCofork.ofπ p w)) :
    IsColimit (CokernelCofork.ofπ ((toArCategory Λ l).map p)
      (by rw [homMk_comp_toArCategory_map, w, homMk_zero]; rfl) : CokernelCofork (homMk r f)) :=
  isCokernelEpiComp (isColimitToArCategoryMapCokernelCofork hp) (homMk r (𝟙 _))
    (hg := inferInstanceAs (Epi (homMk r (𝟙 _)))) (homMk_eq_homMk_id_comp f)

end ArCategory

end ProjectiveSystem

end CategoryTheory
