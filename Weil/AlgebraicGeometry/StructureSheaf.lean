module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksFrontier.RingTheory.Henselian.NormalDomainOfHenselization
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.FieldTheory.PBasisDifferentials

/-!
# Sections of the henselian line over the inverse image of the regular locus

Let `A` be an excellent normal domain with regular locus `V = {𝔭 | A_𝔭 regular} ⊆ Spec A`, which is
open since `A` is J-1, and let `R = A{t}` be the henselian line, the henselization of
`A[t]_{(𝔪_A, t)}`. Let `U ⊆ Spec R` be the inverse image of `V`. Then `U` contains every prime of
`R` of height at most `1`, and restriction `R = Γ(Spec R, 𝒪) → Γ(U, 𝒪)` is an isomorphism.

The proof has two parts. First, `A → R` is flat, so heights can only drop under contraction
(going down), and a prime of height at most `1` of a normal noetherian domain has a regular
localization (a field or a discrete valuation ring); hence `U` contains all primes of height at
most `1`. Second, `R` is a normal noetherian domain, and for such a ring `D` and an open
`W ⊆ Spec D` containing every prime of height at most `1`, the restriction `D → Γ(W, 𝒪)` is
bijective (algebraic Hartogs): a section is a fraction `f/g` near every point of `W`, all these
fractions agree in the fraction field `K` of `D`, and the common element of `K` lies in `D_𝔮` for
every height-one prime `𝔮`, hence in `D = ⋂ D_𝔮`.

## Main definitions

* `PrimeSpectrum.regularLocusOpens A h`: the regular locus of a J-1 ring, as an open subset of
  its spectrum.

## Main results

* `AlgebraicGeometry.StructureSheaf.bijective_algebraMap_sections_of_height_le_one_mem`,
  `AlgebraicGeometry.isIso_Spec_presheaf_map_of_height_le_one_mem`: algebraic Hartogs for a
  normal noetherian domain.
* `AlgebraicGeometry.height_le_one_mem_and_isIso_presheaf_map_of_flat`: the statement for any
  flat extension `A → R` of normal noetherian domains.
* `AlgebraicGeometry.height_le_one_mem_and_isIso_presheaf_map_of_isHenselization`: the statement
  for the henselization of `A[T_σ]_𝔭`, which includes the henselian line `A{t}`.

## Implementation notes

The henselization of `A[T_σ]_𝔭` is `IsLocalRing.IsHenselization` at the residue field of
`A[T_σ]_𝔭`. The result is stated for every finite set of variables `σ` and every prime `𝔭`; the
henselian line `A{t}` is the case `σ = Fin 1`, `𝔭 = (𝔪_A, t)`. Neither the henselian property nor
locality of `A` is needed.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], proof of I.7.7
-/

/- The Hartogs helper here states the algebraic Hartogs lemma for normal domains (sections over
an open containing all primes of height at most one), which is also proved in
`Weil.AlgebraicGeometry.Properties.Regular`. -/

@[expose] public section

universe u

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

namespace AlgebraicGeometry.StructureSheaf

variable {D : Type u} [CommRing D]

/-- A section of the structure sheaf of `Spec D` over `W` is, near each point `x ∈ W`, a single
fraction `f / g` with `g ∉ x`, on the whole of `W ∩ D(g)`. -/
theorem exists_eq_mk_of_mem (W : Opens (PrimeSpectrum.Top D))
    (s : (structureSheafInType D D).obj.obj (op W)) (x : PrimeSpectrum D) (hx : x ∈ W) :
    ∃ f g : D, g ∉ x.asIdeal ∧ ∀ (y : W) (hy : g ∉ y.1.asIdeal),
      s.1 y = LocalizedModule.mk f ⟨g, hy⟩ := by
  obtain ⟨g, hxg, i, f, h⟩ := exists_const W s x hx
  refine ⟨f, g, hxg, fun y hy => ?_⟩
  have := congrArg (fun t => t.1 ⟨y.1, hy⟩) h
  exact this.symm

/-- The section `d` of the structure sheaf takes the value `d / 1` at every point. -/
theorem algebraMap_sections_apply (W : Opens (PrimeSpectrum.Top D)) (d : D) (y : W) :
    (algebraMap D ((structureSheafInType D D).obj.obj (op W)) d).1 y =
      LocalizedModule.mk d 1 :=
  rfl

/-- **Algebraic Hartogs.** Let `D` be a normal noetherian domain and `W ⊆ Spec D` an open subset
containing every prime of height at most `1`. Then `D → Γ(W, 𝒪)` is bijective. -/
theorem bijective_algebraMap_sections_of_height_le_one_mem [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (W : Opens (PrimeSpectrum.Top D))
    (hW : ∀ p : PrimeSpectrum D, p.asIdeal.height ≤ 1 → p ∈ W) :
    Function.Bijective (algebraMap D ((structureSheafInType D D).obj.obj (op W))) := by
  let g₀ : PrimeSpectrum D := ⟨⊥, Ideal.isPrime_bot⟩
  have hg₀ : g₀ ∈ W := hW g₀ (by simp [g₀, Ideal.height_bot])
  have hg₀' : ∀ c : D, c ≠ 0 → c ∉ g₀.asIdeal := fun c hc h => hc h
  refine ⟨fun a b hab => ?_, fun s => ?_⟩
  · have := congrArg (fun t => t.1 ⟨g₀, hg₀⟩) hab
    simp only [algebraMap_sections_apply] at this
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp this
    have hu0 : (u : D) ≠ 0 := fun h => u.2 (by simp [g₀, h])
    simpa [Submonoid.smul_def, hu0] using hu
  · obtain ⟨f₀, c₀, hc₀, h₀⟩ := exists_eq_mk_of_mem W s g₀ hg₀
    have hc₀0 : c₀ ≠ 0 := fun h => hc₀ (by simp [g₀, h])
    -- every local fraction of `s` agrees with `f₀ / c₀` in the fraction field
    have cross : ∀ (y : PrimeSpectrum D) (hy : y ∈ W), ∃ f c : D, c ∉ y.asIdeal ∧
        c₀ * f = c * f₀ ∧ ∀ (z : W) (hz : c ∉ z.1.asIdeal),
          s.1 z = LocalizedModule.mk f ⟨c, hz⟩ := by
      intro y hy
      obtain ⟨f, c, hc, h⟩ := exists_eq_mk_of_mem W s y hy
      have hc0 : c ≠ 0 := fun h => hc (h ▸ y.asIdeal.zero_mem)
      refine ⟨f, c, hc, ?_, h⟩
      have e := (h ⟨g₀, hg₀⟩ (hg₀' c hc0)).symm.trans (h₀ ⟨g₀, hg₀⟩ hc₀)
      obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp e
      have hu0 : (u : D) ≠ 0 := fun h => u.2 (by simp [g₀, h])
      simp only [Submonoid.smul_def, smul_eq_mul] at hu
      exact mul_left_cancel₀ hu0 hu
    let K := FractionRing D
    have hmem : algebraMap D K f₀ * (algebraMap D K c₀)⁻¹ ∈
        (⨅ p : PrimeSpectrum D, ⨅ _ : p.asIdeal.height = 1,
          Localization.subalgebra.ofField K _ p.asIdeal.primeCompl_le_nonZeroDivisors) := by
      refine Algebra.mem_iInf.mpr fun p => Algebra.mem_iInf.mpr fun hp => ?_
      obtain ⟨f, c, hc, hfc, -⟩ := cross p (hW p hp.le)
      have hc0 : c ≠ 0 := fun h => hc (h ▸ p.asIdeal.zero_mem)
      refine ⟨f, c, hc, ?_⟩
      have h1 : algebraMap D K c ≠ 0 := by simpa using hc0
      have h2 : algebraMap D K c₀ ≠ 0 := by simpa using hc₀0
      rw [eq_mul_inv_iff_mul_eq₀ h1, mul_right_comm, mul_inv_eq_iff_eq_mul₀ h2, ← map_mul,
        ← map_mul]
      congr 1
      linear_combination -hfc
    rw [((associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot K).2.1)]
      at hmem
    obtain ⟨d, hd⟩ := Algebra.mem_bot.mp hmem
    have hdc : d * c₀ = f₀ := by
      apply IsFractionRing.injective D K
      have h2 : algebraMap D K c₀ ≠ 0 := by simpa using hc₀0
      rw [map_mul, hd]
      exact inv_mul_cancel_right₀ h2 _
    refine ⟨d, Subtype.ext (funext fun z => ?_)⟩
    obtain ⟨f, c, hc, hfc, h⟩ := cross z.1 z.2
    rw [algebraMap_sections_apply, h z hc]
    have hf : f = c * d := by
      apply mul_left_cancel₀ hc₀0
      rw [hfc, ← hdc]; ring
    rw [hf]
    exact LocalizedModule.mk_eq.mpr ⟨1, by simp [Submonoid.smul_def]⟩

end AlgebraicGeometry.StructureSheaf

/-- For an extension with going down, the contraction of a prime has height at most its height. -/
theorem Ideal.height_under_le_of_hasGoingDown {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] :
    (P.under R).height ≤ P.height := by
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
  exact le_self_add

/-- An excellent ring is J-1: its regular locus is open. -/
theorem IsExcellent.isJ1 {A : Type u} [CommRing A] (h : IsExcellent A) : IsJ1 A :=
  h.1.2.2 A

/-- A normal noetherian domain is regular at every prime of height at most `1`. -/
private theorem isRegularLocalRing_atPrime_of_height_le_one' {A : Type u} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (p : Ideal A) [p.IsPrime]
    (hp : p.height ≤ 1) : IsRegularLocalRing (Localization.AtPrime p) := by
  rcases (show p.height = 0 ∨ p.height = 1 by
    rcases eq_or_lt_of_le hp with h | h
    · exact Or.inr h
    · exact Or.inl (Order.lt_one_iff.mp h)) with h | h
  · rw [Ideal.height_eq_zero_iff_eq_bot] at h
    subst h
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot, Submodule.spanFinrank_bot]
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  · exact MonogenicN1.isRegularLocalRing_of_height_eq_one p h

namespace AlgebraicGeometry

/-- **Algebraic Hartogs**, for the scheme `Spec D`: if `D` is a normal noetherian domain and the
open `W ⊆ Spec D` contains every prime of height at most `1`, then the restriction
`Γ(Spec D, ⊤) → Γ(Spec D, W)` is an isomorphism. -/
theorem isIso_Spec_presheaf_map_of_height_le_one_mem (D : Type u) [CommRing D] [IsDomain D]
    [IsNoetherianRing D] [IsIntegrallyClosed D] (W : (Spec (CommRingCat.of D)).Opens)
    (hW : ∀ p : PrimeSpectrum D, p.asIdeal.height ≤ 1 → p ∈ W) :
    IsIso ((Spec (CommRingCat.of D)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have h := StructureSheaf.bijective_algebraMap_sections_of_height_le_one_mem W hW
  refine (Function.Bijective.of_comp_iff _
    (StructureSheaf.algebraMap_obj_top_bijective (R := D))).mp ?_
  exact h

end AlgebraicGeometry

/-- The regular locus `{𝔭 | A_𝔭 is regular}` of a J-1 ring `A`, as an open subset of `Spec A`. -/
def PrimeSpectrum.regularLocusOpens (A : Type u) [CommRing A] (h : IsJ1 A) :
    Opens (PrimeSpectrum A) :=
  ⟨{p | IsRegularLocalRing (Localization.AtPrime p.asIdeal)}, h⟩

/-- Membership in the regular locus. -/
theorem PrimeSpectrum.mem_regularLocusOpens {A : Type u} [CommRing A] (h : IsJ1 A)
    (p : PrimeSpectrum A) :
    p ∈ PrimeSpectrum.regularLocusOpens A h ↔ IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

namespace AlgebraicGeometry

/-- For a flat extension `A → R` with `A` a normal noetherian J-1 domain and `R` noetherian, every
prime of `R` of height at most `1` lies over the regular locus of `A`. -/
theorem height_le_one_mem_preimage_regularLocusOpens_of_flat (A R : Type u) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (hA : IsJ1 A) [CommRing R]
    [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (P : PrimeSpectrum R)
    (hP : P.asIdeal.height ≤ 1) :
    P ∈ Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ
      (PrimeSpectrum.regularLocusOpens A hA : (Spec (CommRingCat.of A)).Opens) := by
  change IsRegularLocalRing (Localization.AtPrime (P.asIdeal.under A))
  exact isRegularLocalRing_atPrime_of_height_le_one' _
    ((Ideal.height_under_le_of_hasGoingDown P.asIdeal).trans hP)

/-- Let `A → R` be a flat extension of normal noetherian domains with `A` J-1, and `U ⊆ Spec R` the
inverse image of the regular locus of `A`. Then `U` contains every prime of `R` of height at most
`1`, and the restriction `Γ(Spec R, ⊤) → Γ(Spec R, U)` is an isomorphism. -/
theorem height_le_one_mem_and_isIso_presheaf_map_of_flat (A R : Type u) [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (hA : IsJ1 A) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra A R] [Module.Flat A R] :
    (∀ P : PrimeSpectrum R, P.asIdeal.height ≤ 1 →
      P ∈ Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ
        (PrimeSpectrum.regularLocusOpens A hA : (Spec (CommRingCat.of A)).Opens)) ∧
    IsIso ((Spec (CommRingCat.of R)).presheaf.map (homOfLE (le_top :
      Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ
        (PrimeSpectrum.regularLocusOpens A hA : (Spec (CommRingCat.of A)).Opens) ≤ ⊤)).op) :=
  have h := height_le_one_mem_preimage_regularLocusOpens_of_flat A R hA
  ⟨h, isIso_Spec_presheaf_map_of_height_le_one_mem R _ h⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

open IsLocalRing in
/-- Let `A` be an excellent normal domain, `𝔭` a prime of a polynomial ring `A[T_σ]` in finitely
many variables, and `R` the henselization of `A[T_σ]_𝔭` (for `σ = Fin 1` and `𝔭 = (𝔪_A, T)`
this is the henselian line `A{t}`). Let `V ⊆ Spec A` be the regular locus and `U ⊆ Spec R` its
inverse image. Then `U` contains every prime of `R` of height at most `1`, and the restriction
map `Γ(Spec R, ⊤) → Γ(Spec R, U)` is an isomorphism. -/
@[weil "lem_fk107_henselian_line_sections_regular_locus"]
theorem height_le_one_mem_and_isIso_presheaf_map_of_isHenselization {σ : Type u} [Finite σ]
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (hA : IsExcellent A)
    (p : Ideal (MvPolynomial σ A)) [p.IsPrime]
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra (Localization.AtPrime p) R]
    [IsHenselization (Localization.AtPrime p) (ResidueField (Localization.AtPrime p)) R]
    [Algebra A R] [IsScalarTower A (Localization.AtPrime p) R] :
    (∀ P : PrimeSpectrum R, P.asIdeal.height ≤ 1 →
      P ∈ Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ
        (PrimeSpectrum.regularLocusOpens A hA.isJ1 : (Spec (CommRingCat.of A)).Opens)) ∧
    IsIso ((Spec (CommRingCat.of R)).presheaf.map (homOfLE (le_top :
      Spec.map (CommRingCat.ofHom (algebraMap A R)) ⁻¹ᵁ
      (PrimeSpectrum.regularLocusOpens A hA.isJ1 : (Spec (CommRingCat.of A)).Opens) ≤ ⊤)).op) := by
  have : IsNoetherianRing A := hA.1.1
  have : IsIntegrallyClosed (MvPolynomial σ A) := by
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
    have := Stacks.FieldTheory.PBasisDifferentials.isIntegrallyClosed_mvPolynomial A n
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.renameEquiv A e).toRingEquiv.symm
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  have : Module.Flat A (Localization.AtPrime p) := Module.Flat.trans A (MvPolynomial σ A) _
  have : Module.Flat (Localization.AtPrime p) R :=
    IsHenselization.flat (L := ResidueField (Localization.AtPrime p))
  have : Module.Flat A R := Module.Flat.trans A (Localization.AtPrime p) R
  have : IsNoetherianRing R := isNoetherianRing_of_isHenselization (A := Localization.AtPrime p)
    (ResidueField (Localization.AtPrime p))
  obtain ⟨_, _⟩ := StacksDraft.isDomain_and_isIntegrallyClosed_of_isHenselization
    (R := Localization.AtPrime p) (H := R)
  exact height_le_one_mem_and_isIso_presheaf_map_of_flat A R hA.isJ1

end AlgebraicGeometry
