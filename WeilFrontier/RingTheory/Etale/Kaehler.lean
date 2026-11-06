module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Weil.Attr

/-!
# Kähler differentials of a localization

Let `A → B` be a ring homomorphism, `𝔭 ⊆ B` a prime ideal and `𝔮 = 𝔭 ∩ A`. We show that
`Ω[B_𝔭 ⁄ A_𝔮] ≅ (Ω[B ⁄ A])_𝔭` as `B_𝔭`-modules.

The proof has two steps. First, localization of Kähler differentials
(`KaehlerDifferential.isLocalizedModule_map`) identifies `Ω[B_𝔭 ⁄ A]` with `(Ω[B ⁄ A])_𝔭`.
Second, when `Ω[A' ⁄ A]` vanishes (for instance when `A'` is a localization of `A`), the
canonical surjection `Ω[B' ⁄ A] → Ω[B' ⁄ A']` is an isomorphism for every `A'`-algebra `B'`: by
the first fundamental exact sequence its kernel is the image of `B' ⊗[A'] Ω[A' ⁄ A] = 0`.

## Main results

* `KaehlerDifferential.map_bijective_of_subsingleton`: if `Ω[A' ⁄ A]` is trivial then
  `Ω[B ⁄ A] → Ω[B ⁄ A']` is bijective.
* `KaehlerDifferential.mapEquivOfSubsingleton`: the resulting `B`-linear isomorphism.
* `KaehlerDifferential.localizationAtPrimeEquiv`: `Ω[B_𝔭 ⁄ A_𝔮] ≃ₗ[B_𝔭] (Ω[B ⁄ A])_𝔭`.

## References

* [H. Matsumura, *Commutative Ring Theory*][matsumura1989], Exercise 25.4.
* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1.
-/

@[expose] public section

open TensorProduct

namespace KaehlerDifferential

section BaseChange

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

/-- If `Ω[A ⁄ R]` is trivial (e.g. `A` is a localization of `R`), then for any `A`-algebra `B` the
canonical map `Ω[B ⁄ R] → Ω[B ⁄ A]` is bijective. -/
theorem map_bijective_of_subsingleton [Subsingleton Ω[A⁄R]] :
    Function.Bijective (map R A B B) := by
  refine ⟨?_, map_surjective R A B⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, rfl⟩ := (exact_mapBaseChange_map R A B x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- If `Ω[A ⁄ R]` is trivial (e.g. `A` is a localization of `R`), then for any `A`-algebra `B` the
canonical map `Ω[B ⁄ R] → Ω[B ⁄ A]` is a `B`-linear isomorphism. -/
noncomputable def mapEquivOfSubsingleton [Subsingleton Ω[A⁄R]] : Ω[B⁄R] ≃ₗ[B] Ω[B⁄A] :=
  LinearEquiv.ofBijective (map R A B B) (map_bijective_of_subsingleton R A B)

@[simp]
theorem mapEquivOfSubsingleton_apply [Subsingleton Ω[A⁄R]] (x : Ω[B⁄R]) :
    mapEquivOfSubsingleton R A B x = map R A B B x := rfl

theorem mapEquivOfSubsingleton_D [Subsingleton Ω[A⁄R]] (b : B) :
    mapEquivOfSubsingleton R A B (D R B b) = D A B b := by
  simp

end BaseChange

section AtPrime

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (q : Ideal A) [q.IsPrime] (p : Ideal B) [p.IsPrime] [p.LiesOver q]
  [Algebra (Localization.AtPrime q) (Localization.AtPrime p)] [Localization.AtPrime.IsLiesOverAlgebra q p]

/-- Let `A → B` be a ring homomorphism, `p` a prime of `B` lying over the prime `q` of `A`.
Then `Ω[B_p ⁄ A_q] ≅ (Ω[B ⁄ A])_p` as `B_p`-modules. -/
@[weil "lem_fk101_kahler_differentials_localize"]
noncomputable def localizationAtPrimeEquiv :
    Ω[Localization.AtPrime p⁄Localization.AtPrime q] ≃ₗ[Localization.AtPrime p]
      LocalizedModule p.primeCompl Ω[B⁄A] :=
  have : Subsingleton Ω[Localization.AtPrime q⁄A] :=
    have := Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.AtPrime q) q.primeCompl
    inferInstance
  (mapEquivOfSubsingleton A (Localization.AtPrime q) (Localization.AtPrime p)).symm.trans
    (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
      (IsLocalizedModule.iso p.primeCompl (map A A B (Localization.AtPrime p))).symm)

theorem localizationAtPrimeEquiv_D_algebraMap (b : B) :
    localizationAtPrimeEquiv q p (D _ _ (algebraMap B (Localization.AtPrime p) b)) =
      LocalizedModule.mk (D A B b) 1 := by
  have : Subsingleton Ω[Localization.AtPrime q⁄A] :=
    have := Algebra.FormallyEtale.of_isLocalization (Rₘ := Localization.AtPrime q) q.primeCompl
    inferInstance
  have h : (mapEquivOfSubsingleton A (Localization.AtPrime q) (Localization.AtPrime p)).symm
      (D _ _ (algebraMap B (Localization.AtPrime p) b)) =
      map A A B (Localization.AtPrime p) (D A B b) := by
    rw [LinearEquiv.symm_apply_eq, map_D, mapEquivOfSubsingleton_D]
  simp only [localizationAtPrimeEquiv, LinearEquiv.trans_apply, h,
    LinearEquiv.extendScalarsOfIsLocalization_apply, IsLocalizedModule.iso_symm_apply]

end AtPrime

end KaehlerDifferential
