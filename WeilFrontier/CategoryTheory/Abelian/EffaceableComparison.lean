module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Comparison of `Ext` groups along an exact functor, by effaceability

Let `ε : 𝒜 ⥤ ℬ` be an exact additive functor between abelian categories, `A : 𝒜`, and
`e : ε.obj A ≅ B`. For `F : 𝒜` and `n : ℕ` the functor induces the comparison map
`c^n_F : Ext^n(A, F) → Ext^n(B, ε F)`, the map `Ext.mapExactFunctor ε` followed by
precomposition with `e⁻¹`.

Let `P` be a property of objects of `𝒜` stable under quotients, in the sense that for every
short exact sequence `0 → F → G → Q → 0` with `F` and `G` in `P`, `Q` is in `P`. Assume that
`c^0_F` is bijective for every `F` in `P`, and that every `F` in `P` admits a monomorphism
`F ⟶ G` into an object `G` in `P` for which every `c^n_G` is bijective. Then `c^n_F` is bijective
for every `F` in `P` and every `n`.

The proof is by induction on `n`. Given `F` in `P`, choose `F ⟶ G` as above, with cokernel `Q`
(in `P`). The comparison maps commute with the maps of the covariant long exact `Ext` sequences
of `0 → F → G → Q → 0` and of its image under `ε` (Mathlib's `Ext.mapExactFunctor_comp`,
`Ext.mapExactFunctor_mk₀` and `Ext.mapExactFunctor_extClass`). The four lemma applied to
`Ext^n(A, G) → Ext^n(A, Q) → Ext^{n+1}(A, F) → Ext^{n+1}(A, G)` gives injectivity of `c^{n+1}`
on all of `P`; the four lemma applied to
`Ext^n(A, Q) → Ext^{n+1}(A, F) → Ext^{n+1}(A, G) → Ext^{n+1}(A, Q)` then gives surjectivity.

## Main definitions

* `CategoryTheory.Functor.mapExtOfIso ε e F n`: the comparison map
  `Ext^n(A, F) →+ Ext^n(B, ε.obj F)` attached to `e : ε.obj A ≅ B`.

## Main results

* `CategoryTheory.Functor.mapExtAddHom_bijective_of_effaceable`: the effaceability criterion
  for `ε.mapExtAddHom A F n`.
* `CategoryTheory.Functor.mapExtOfIso_bijective_of_effaceable`: the same for the transported
  comparison map `ε.mapExtOfIso e F n`.
* `CategoryTheory.Functor.mapExtOfIso_bijective_of_effaceable_of_forall`: the case where the
  class is all of `𝒜`.

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

/-- The comparison map `Ext^n(A, F) → Ext^n(B, ε F)` induced by the exact functor `ε` and an
isomorphism `e : ε.obj A ≅ B`: the map `Ext.mapExactFunctor ε` followed by precomposition with
`e⁻¹`. -/
noncomputable def mapExtOfIso {A : 𝒜} {B : ℬ} (e : ε.obj A ≅ B) (F : 𝒜) (n : ℕ) :
    Ext.{w} A F n →+ Ext.{w'} B (ε.obj F) n :=
  ((Ext.mk₀ e.inv).precomp (ε.obj F) (zero_add n)).comp (ε.mapExtAddHom A F n)

lemma mapExtOfIso_apply {A : 𝒜} {B : ℬ} (e : ε.obj A ≅ B) (F : 𝒜) (n : ℕ) (x : Ext.{w} A F n) :
    ε.mapExtOfIso e F n x = (Ext.mk₀ e.inv).comp (x.mapExactFunctor ε) (zero_add n) :=
  rfl

/-- `ε.mapExtOfIso e F n` is bijective if and only if `ε.mapExtAddHom A F n` is. -/
lemma mapExtOfIso_bijective_iff {A : 𝒜} {B : ℬ} (e : ε.obj A ≅ B) (F : 𝒜) (n : ℕ) :
    Function.Bijective (ε.mapExtOfIso e F n) ↔ Function.Bijective (ε.mapExtAddHom A F n) := by
  have hpre : Function.Bijective
      ((Ext.mk₀ e.inv).precomp (ε.obj F) (zero_add n) : Ext.{w'} (ε.obj A) (ε.obj F) n → _) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨(Ext.mk₀ e.hom).precomp (ε.obj F) (zero_add n), fun x ↦ ?_, fun x ↦ ?_⟩
    · simp [Ext.mk₀_comp_mk₀_assoc]
    · simp [Ext.mk₀_comp_mk₀_assoc]
  change Function.Bijective (_ ∘ _) ↔ _
  exact ⟨fun h ↦ (Function.Bijective.of_comp_iff' hpre _).1 h,
    fun h ↦ hpre.comp h⟩

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀
  Ext.mapExactFunctor_extClass

/-- **Effaceability criterion.** Let `P` be a property of objects of `𝒜` stable under quotients
(for every short exact `0 → F → G → Q → 0` with `F`, `G` in `P`, also `Q` is in `P`). If
`ε.mapExtAddHom A F 0` is bijective for every `F` in `P`, and every `F` in `P` embeds into some
`G` in `P` for which every `ε.mapExtAddHom A G n` is bijective, then `ε.mapExtAddHom A F n` is
bijective for every `F` in `P` and every `n`. -/
theorem mapExtAddHom_bijective_of_effaceable (A : 𝒜) (P : ObjectProperty 𝒜)
    (hP : ∀ S : ShortComplex 𝒜, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (h₀ : ∀ F, P F → Function.Bijective (ε.mapExtAddHom.{w, w'} A F 0))
    (hemb : ∀ F, P F → ∃ (G : 𝒜) (i : F ⟶ G), Mono i ∧ P G ∧
      ∀ n, Function.Bijective (ε.mapExtAddHom.{w, w'} A G n))
    (n : ℕ) (F : 𝒜) (hF : P F) : Function.Bijective (ε.mapExtAddHom.{w, w'} A F n) := by
  induction n generalizing F with
  | zero => exact h₀ F hF
  | succ n ih =>
    -- the short exact sequence `0 → F → G → Q → 0` attached to an embedding of `F`
    have key : ∀ F, P F → ∃ (S : ShortComplex 𝒜) (hS : S.ShortExact), S.X₁ = F ∧ P S.X₂ ∧
        P S.X₃ ∧ ∀ m, Function.Bijective (ε.mapExtAddHom.{w, w'} A S.X₂ m) := by
      intro F hF
      obtain ⟨G, i, hi, hG, hGb⟩ := hemb F hF
      let S := ShortComplex.mk _ _ (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      exact ⟨S, hS, rfl, hG, hP S hS hF hG, hGb⟩
    -- injectivity of `c^{n+1}` on `P`
    have hinj : ∀ F, P F → Function.Injective (ε.mapExtAddHom.{w, w'} A F (n + 1)) := by
      intro F hF
      obtain ⟨S, hS, rfl, hG, hQ, hGb⟩ := key F hF
      exact AddMonoidHom.injective_of_surjective_of_injective_of_injective
        ((Ext.mk₀ S.g).postcomp A (add_zero n)) (hS.extClass.postcomp A rfl)
        ((Ext.mk₀ S.f).postcomp A (add_zero (n + 1)))
        ((Ext.mk₀ (S.map ε).g).postcomp (ε.obj A) (add_zero n))
        ((hS.map_of_exact ε).extClass.postcomp (ε.obj A) rfl)
        ((Ext.mk₀ (S.map ε).f).postcomp (ε.obj A) (add_zero (n + 1)))
        (ε.mapExtAddHom A S.X₂ n) (ε.mapExtAddHom A S.X₃ n) (ε.mapExtAddHom A S.X₁ (n + 1))
        (ε.mapExtAddHom A S.X₂ (n + 1))
        (by cat_disch) (by cat_disch) (by cat_disch)
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₁' A hS n (n + 1) rfl))
        ((ShortComplex.ab_exact_iff_function_exact _).mp
          (Ext.covariant_sequence_exact₃' (ε.obj A) (hS.map_of_exact ε) n (n + 1) rfl))
        (hGb n).2 (ih _ hQ).1 (hGb (n + 1)).1
    refine ⟨hinj F hF, ?_⟩
    obtain ⟨S, hS, rfl, hG, hQ, hGb⟩ := key F hF
    exact AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
      (hS.extClass.postcomp A rfl) ((Ext.mk₀ S.f).postcomp A (add_zero (n + 1)))
      ((Ext.mk₀ S.g).postcomp A (add_zero (n + 1)))
      ((hS.map_of_exact ε).extClass.postcomp (ε.obj A) rfl)
      ((Ext.mk₀ (S.map ε).f).postcomp (ε.obj A) (add_zero (n + 1)))
      ((Ext.mk₀ (S.map ε).g).postcomp (ε.obj A) (add_zero (n + 1)))
      (ε.mapExtAddHom A S.X₃ n) (ε.mapExtAddHom A S.X₁ (n + 1))
      (ε.mapExtAddHom A S.X₂ (n + 1)) (ε.mapExtAddHom A S.X₃ (n + 1))
      (by cat_disch) (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₂' A hS (n + 1)))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₁' (ε.obj A) (hS.map_of_exact ε) n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₂' (ε.obj A) (hS.map_of_exact ε) (n + 1)))
      (ih _ hQ).2 (hGb (n + 1)).2 (hinj _ hQ)

/-- **Effaceability criterion**, for the comparison map `ε.mapExtOfIso e F n` transported along
`e : ε.obj A ≅ B`. Let `P` be a property of objects of `𝒜` stable under quotients. If the
comparison map is bijective in degree `0` on `P`, and every `F` in `P` embeds into some `G` in
`P` on which the comparison map is bijective in every degree, then it is bijective on `P` in
every degree. -/
theorem mapExtOfIso_bijective_of_effaceable {A : 𝒜} {B : ℬ} (e : ε.obj A ≅ B)
    (P : ObjectProperty 𝒜)
    (hP : ∀ S : ShortComplex 𝒜, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
    (h₀ : ∀ F, P F → Function.Bijective (ε.mapExtOfIso.{w, w'} e F 0))
    (hemb : ∀ F, P F → ∃ (G : 𝒜) (i : F ⟶ G), Mono i ∧ P G ∧
      ∀ n, Function.Bijective (ε.mapExtOfIso.{w, w'} e G n))
    (n : ℕ) (F : 𝒜) (hF : P F) : Function.Bijective (ε.mapExtOfIso.{w, w'} e F n) := by
  rw [mapExtOfIso_bijective_iff]
  refine ε.mapExtAddHom_bijective_of_effaceable A P hP
    (fun F hF ↦ (ε.mapExtOfIso_bijective_iff e F 0).1 (h₀ F hF)) (fun F hF ↦ ?_) n F hF
  obtain ⟨G, i, hi, hG, hGb⟩ := hemb F hF
  exact ⟨G, i, hi, hG, fun m ↦ (ε.mapExtOfIso_bijective_iff e G m).1 (hGb m)⟩

/-- **Effaceability criterion**, for the class of all objects: if the comparison map is
bijective in degree `0`, and every object embeds into one on which the comparison map is
bijective in every degree, then the comparison map is bijective in every degree. -/
theorem mapExtOfIso_bijective_of_effaceable_of_forall {A : 𝒜} {B : ℬ} (e : ε.obj A ≅ B)
    (h₀ : ∀ F, Function.Bijective (ε.mapExtOfIso.{w, w'} e F 0))
    (hemb : ∀ F, ∃ (G : 𝒜) (i : F ⟶ G), Mono i ∧
      ∀ n, Function.Bijective (ε.mapExtOfIso.{w, w'} e G n))
    (n : ℕ) (F : 𝒜) : Function.Bijective (ε.mapExtOfIso.{w, w'} e F n) :=
  ε.mapExtOfIso_bijective_of_effaceable e ⊤ (fun _ _ _ _ ↦ trivial) (fun F _ ↦ h₀ F)
    (fun F _ ↦ by
      obtain ⟨G, i, hi, hGb⟩ := hemb F
      exact ⟨G, i, hi, trivial, hGb⟩) n F trivial

end Functor

end CategoryTheory
