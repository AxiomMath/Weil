module

public import Weil.CategoryTheory.Abelian.EffaceableComparison

/-!
# The effaceability criterion without a degree-zero hypothesis

Let `ε : 𝒜 ⥤ ℬ` be an exact additive functor between abelian categories, `A : 𝒜`, and
`c^n_F : Ext^n(A, F) → Ext^n(ε A, ε F)` the map induced by `ε`. Let `P` be a property of objects
of `𝒜` stable under quotients (for every short exact `0 → F → G → Q → 0` with `F`, `G` in `P`,
also `Q` is in `P`), such that every `F` in `P` admits a monomorphism `F ⟶ G` into an object `G`
in `P` on which every `c^n_G` is bijective. Then `c^0_F` is already bijective for every `F` in
`P`, so the effaceability criterion
`CategoryTheory.Functor.mapExtAddHom_bijective_of_effaceable` applies without its degree-zero
hypothesis: `c^n_F` is bijective for every `F` in `P` and every `n`.

In degree zero, `Ext^0(A, -)` is `Hom(A, -)`, and postcomposition with a monomorphism is
injective on it. Injectivity of `c^0_F`: if `F ⟶ G` is the chosen embedding, then
`c^0_G ∘ (i ∘ -) = (ε i ∘ -) ∘ c^0_F` with `c^0_G` bijective and `i ∘ -` injective. Surjectivity
of `c^0_F`: given `y : Ext^0(ε A, ε F)`, write `ε i ∘ y = c^0_G x`; with `Q` the cokernel of `i`,
the image of `x` in `Ext^0(A, Q)` is sent by `c^0_Q` to `ε p ∘ ε i ∘ y = 0`, and `c^0_Q` is
injective by the first step (`Q` is in `P`), so `x = i ∘ x'` by left exactness of `Hom(A, -)`;
then `ε i ∘ c^0_F x' = ε i ∘ y`, and `ε i ∘ -` is injective since `ε` preserves monomorphisms.

## Main results

* `CategoryTheory.Functor.mapExtAddHom_zero_bijective_of_effaceable`: bijectivity in degree
  zero on `P`.
* `CategoryTheory.Functor.mapExtAddHom_bijective_of_effaceable'`: the effaceability criterion
  for `ε.mapExtAddHom A F n` without the degree-zero hypothesis.
* `CategoryTheory.Functor.mapExtOfIso_bijective_of_effaceable'`: the same for the transported
  comparison map `ε.mapExtOfIso e F n`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Abelian

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ]
variable (ε : 𝒜 ⥤ ℬ) [ε.Additive] [PreservesFiniteLimits ε] [PreservesFiniteColimits ε]
variable [HasExt.{w} 𝒜] [HasExt.{w'} ℬ]

namespace Functor

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀

/-- The degree-zero comparison maps commute with postcomposition by a morphism. -/
private lemma mapExtAddHom_zero_postcomp (A : 𝒜) {F G : 𝒜} (i : F ⟶ G) (x : Ext.{w} A F 0) :
    ε.mapExtAddHom.{w, w'} A G 0 ((Ext.mk₀ i).postcomp A (add_zero 0) x) =
      (Ext.mk₀ (ε.map i)).postcomp (ε.obj A) (add_zero 0) (ε.mapExtAddHom.{w, w'} A F 0 x) := by
  cat_disch

/-- If `F` embeds into `G` and `c^0_G` is bijective, then `c^0_F` is injective. -/
private lemma mapExtAddHom_zero_injective_of_mono (A : 𝒜) {F G : 𝒜} (i : F ⟶ G) [Mono i]
    (hG : Function.Injective (ε.mapExtAddHom.{w, w'} A G 0)) :
    Function.Injective (ε.mapExtAddHom.{w, w'} A F 0) := by
  intro x y hxy
  apply Ext.postcomp_mk₀_injective_of_mono A i
  apply hG
  rw [mapExtAddHom_zero_postcomp, mapExtAddHom_zero_postcomp, hxy]

/-- **Degree zero of the effaceability criterion.** Let `P` be a property of objects of `𝒜`
stable under quotients. If every `F` in `P` embeds into some `G` in `P` for which every
`ε.mapExtAddHom A G n` is bijective, then `ε.mapExtAddHom A F 0` is bijective for every `F` in
`P`. -/
theorem mapExtAddHom_zero_bijective_of_effaceable (A : 𝒜) (P : ObjectProperty 𝒜)
    (hP : ∀ S : ShortComplex 𝒜, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hemb : ∀ F, P F → ∃ (G : 𝒜) (i : F ⟶ G), Mono i ∧ P G ∧
      ∀ n, Function.Bijective (ε.mapExtAddHom.{w, w'} A G n))
    (F : 𝒜) (hF : P F) : Function.Bijective (ε.mapExtAddHom.{w, w'} A F 0) := by
  have hinj : ∀ F, P F → Function.Injective (ε.mapExtAddHom.{w, w'} A F 0) := by
    intro F hF
    obtain ⟨G, i, hi, -, hGb⟩ := hemb F hF
    exact ε.mapExtAddHom_zero_injective_of_mono A i (hGb 0).1
  refine ⟨hinj F hF, fun y ↦ ?_⟩
  obtain ⟨G, i, hi, hG, hGb⟩ := hemb F hF
  let S := ShortComplex.mk _ _ (cokernel.condition i)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
  have hQ : P S.X₃ := hP S hS hF hG
  have hεi : Mono (ε.map i) := inferInstance
  obtain ⟨x, hx⟩ := (hGb 0).2 ((Ext.mk₀ (ε.map i)).postcomp (ε.obj A) (add_zero 0) y)
  -- the image of `x` in `Ext^0(A, Q)` vanishes
  have hx0 : (Ext.mk₀ S.g).postcomp A (add_zero 0) x = 0 := by
    apply hinj _ hQ
    rw [map_zero, mapExtAddHom_zero_postcomp, hx]
    change (((y.comp (Ext.mk₀ (ε.map i)) (add_zero 0)).comp (Ext.mk₀ (ε.map S.g))
      (add_zero 0))) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← ε.map_comp]
    simp [S]
  obtain ⟨x', hx'⟩ : ∃ x', (Ext.mk₀ S.f).postcomp A (add_zero 0) x' = x :=
    ((ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.covariant_sequence_exact₂' A hS 0) x).mp hx0
  refine ⟨x', Ext.postcomp_mk₀_injective_of_mono (ε.obj A) (ε.map i) ?_⟩
  change (Ext.mk₀ (ε.map S.f)).postcomp (ε.obj A) (add_zero 0) _ = _
  rw [← mapExtAddHom_zero_postcomp, hx', hx]

/-- **Effaceability criterion**, without a degree-zero hypothesis. Let `P` be a property of
objects of `𝒜` stable under quotients (for every short exact `0 → F → G → Q → 0` with `F`, `G`
in `P`, also `Q` is in `P`). If every `F` in `P` embeds into some `G` in `P` for which every
`ε.mapExtAddHom A G n` is bijective, then `ε.mapExtAddHom A F n` is bijective for every `F` in
`P` and every `n`. -/
theorem mapExtAddHom_bijective_of_effaceable' (A : 𝒜) (P : ObjectProperty 𝒜)
    (hP : ∀ S : ShortComplex 𝒜, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hemb : ∀ F, P F → ∃ (G : 𝒜) (i : F ⟶ G), Mono i ∧ P G ∧
      ∀ n, Function.Bijective (ε.mapExtAddHom.{w, w'} A G n))
    (n : ℕ) (F : 𝒜) (hF : P F) : Function.Bijective (ε.mapExtAddHom.{w, w'} A F n) :=
  ε.mapExtAddHom_bijective_of_effaceable A P hP
    (ε.mapExtAddHom_zero_bijective_of_effaceable A P hP hemb) hemb n F hF

/-- **Effaceability criterion**, for the comparison map `ε.mapExtOfIso e F n` transported along
`e : ε.obj A ≅ B`, without a degree-zero hypothesis. Let `P` be a property of objects of `𝒜`
stable under quotients. If every `F` in `P` embeds into some `G` in `P` on which the comparison
map is bijective in every degree, then it is bijective on `P` in every degree. -/
theorem mapExtOfIso_bijective_of_effaceable' {A : 𝒜} {B : ℬ} (e : ε.obj A ≅ B)
    (P : ObjectProperty 𝒜)
    (hP : ∀ S : ShortComplex 𝒜, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (hemb : ∀ F, P F → ∃ (G : 𝒜) (i : F ⟶ G), Mono i ∧ P G ∧
      ∀ n, Function.Bijective (ε.mapExtOfIso.{w, w'} e G n))
    (n : ℕ) (F : 𝒜) (hF : P F) : Function.Bijective (ε.mapExtOfIso.{w, w'} e F n) := by
  have hemb' : ∀ F, P F → ∃ (G : 𝒜) (i : F ⟶ G), Mono i ∧ P G ∧
      ∀ n, Function.Bijective (ε.mapExtAddHom.{w, w'} A G n) := by
    intro F hF
    obtain ⟨G, i, hi, hG, hGb⟩ := hemb F hF
    exact ⟨G, i, hi, hG, fun m ↦ (ε.mapExtOfIso_bijective_iff e G m).1 (hGb m)⟩
  rw [mapExtOfIso_bijective_iff]
  exact ε.mapExtAddHom_bijective_of_effaceable' A P hP hemb' n F hF

end Functor

end CategoryTheory
