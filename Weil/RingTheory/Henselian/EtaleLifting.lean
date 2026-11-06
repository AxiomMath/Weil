module

public import Weil.Attr
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.RingTheory.Etale.Basic
public import Weil.Defs.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import Weil.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian

/-!
# Local-étale algebras lift to Henselian local rings

Let `R → F` be a local homomorphism from a noetherian local ring to a Henselian local ring, let
`R → E` be a local-étale homomorphism (`RingHom.IsEtaleLocalHom`), and let
`e : κ(E) → κ(F)` be a homomorphism of `κ(R)`-algebras. Then there is a local `R`-algebra
homomorphism `u : E → F` inducing `e` on residue fields.

## Main results

* `IsLocalRing.exists_algHom_residue_eq_of_isEtaleLocalHom`: the lift `u`, together with its
  locality and the compatibility `residue (u x) = e (residue x)`.

## Implementation notes

The source assumes `F` strictly Henselian; only the Henselian property is used, so the statement
is made for `HenselianLocalRing F`, and applies to strictly Henselian `F` through the instance
`StrictlyHenselianLocalRing F → HenselianLocalRing F`. No noetherian hypothesis on `F` is needed.

The proof does not pass through the localized tensor product `(E ⊗_R F)_Q` of the source. Instead
`E` is written as the localization `A_q` of a finite type `R`-algebra `A` at a prime `q`
(essential finite type). Flatness and unramifiedness of `R → A_q` make `A` étale at `q`, so some
`A_g` with `g ∉ q` is étale over `R`. The residue datum lifts uniquely along the étale `R → A_g`
into the Henselian `F`, and the lift extends to `A_q = E` because every element outside `q` maps
to a unit of `F`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
* [Stacks Project, Tag 08HQ](https://stacks.math.columbia.edu/tag/08HQ)
-/

public section

open IsLocalRing

namespace IsLocalRing

variable {R E F : Type*} [CommRing R] [CommRing E] [CommRing F] [Algebra R E] [Algebra R F]
  [IsNoetherianRing R] [IsNoetherianRing E] [IsLocalRing R] [IsLocalRing E] [HenselianLocalRing F]
  [IsLocalHom (algebraMap R E)] [IsLocalHom (algebraMap R F)]

/-- Let `R → F` be a local homomorphism from a noetherian local ring to a Henselian local ring,
`R → E` local-étale, and `e : κ(E) → κ(F)` a `κ(R)`-algebra homomorphism. Then there is a local
`R`-algebra homomorphism `u : E → F` inducing `e` on residue fields. -/
@[weil "lem_fk103_local_etale_lifts_to_strictly_henselian"]
theorem exists_algHom_residue_eq_of_isEtaleLocalHom (hE : (algebraMap R E).IsEtaleLocalHom)
    (e : ResidueField E →ₐ[ResidueField R] ResidueField F) :
    ∃ u : E →ₐ[R] F, IsLocalHom (u : E →+* F) ∧ ∀ x, residue F (u x) = e (residue E x) := by
  obtain ⟨hflat, hunr, hess⟩ := hE
  rw [RingHom.flat_algebraMap_iff] at hflat
  rw [RingHom.formallyUnramified_algebraMap] at hunr
  rw [RingHom.essFiniteType_algebraMap] at hess
  -- `E` is the localization of the finite type `R`-algebra `A` at the prime `q`.
  set A := Algebra.EssFiniteType.subalgebra R E
  set M := Algebra.EssFiniteType.submonoid R E
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  set q : Ideal A := (maximalIdeal E).comap (algebraMap A E)
  have hM : M = q.primeCompl := by
    ext x
    change IsUnit (algebraMap A E x) ↔ algebraMap A E x ∉ maximalIdeal E
    exact (mem_nonunits_iff.not.trans not_not).symm
  have hloc : IsLocalization.AtPrime E q := by
    unfold IsLocalization.AtPrime; rw [← hM]; infer_instance
  set p : Ideal R := maximalIdeal R
  have hqp : q.LiesOver p := by
    constructor
    change p = (maximalIdeal E).comap ((algebraMap A E).comp (algebraMap R A))
    rw [← IsScalarTower.algebraMap_eq]
    exact (IsLocalRing.maximalIdeal_comap (algebraMap R E)).symm
  -- `A_q ≃ E` as `R`-algebras.
  let φ : Localization.AtPrime q ≃ₐ[R] E :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) E).restrictScalars R
  have : Algebra.IsUnramifiedAt R q := Algebra.FormallyUnramified.of_equiv φ.symm
  have : Module.Flat R (Localization.AtPrime q) := Module.Flat.of_linearEquiv φ.toLinearEquiv
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).2 inferInstance
  have hEt : Algebra.IsEtaleAt R q := Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal p q
    ((Algebra.isUnramifiedAt_iff_map_eq R p q).mp inferInstance).2
  obtain ⟨g, hg, hgEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) q
  -- Elements outside `q` become units in `E`.
  have hunitE : ∀ a : A, a ∉ q → IsUnit (algebraMap A E a) := fun a ha =>
    (mem_nonunits_iff.not.trans not_not).mp ha
  set B := Localization.Away g
  -- The `R`-algebra map `A_g → E`.
  let ι : B →ₐ[R] E := IsLocalization.liftAlgHom (M := Submonoid.powers g)
    (f := IsScalarTower.toAlgHom R A E) (by
      rintro ⟨_, n, rfl⟩
      exact (hunitE g hg).pow n)
  have hι : ∀ a : A, ι (algebraMap A B a) = algebraMap A E a := fun a =>
    IsLocalization.lift_eq _ a
  -- The residue datum on `A_g`.
  let τ : E →ₐ[R] ResidueField F :=
    (e.restrictScalars R).comp (IsScalarTower.toAlgHom R E (ResidueField E))
  obtain ⟨f, hf, -⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale (τ.comp ι)
  let f₀ : A →ₐ[R] F := f.comp (IsScalarTower.toAlgHom R A B)
  have hf₀ : ∀ a : A, residue F (f₀ a) = e (residue E (algebraMap A E a)) := fun a => by
    change residue F (f (algebraMap A B a)) = _
    rw [hf]
    change e (residue E (ι (algebraMap A B a))) = _
    rw [hι]
  have hunits : ∀ y : M, IsUnit (f₀ y) := fun y => by
    have h1 : IsUnit (residue F (f₀ y)) := by
      rw [hf₀]
      exact ((y.2 : IsUnit (algebraMap A E y)).map (residue E)).map e
    exact isUnit_of_map_unit (residue F) _ h1
  let u : E →ₐ[R] F := IsLocalization.liftAlgHom (M := M) (f := f₀) hunits
  have hres : ∀ x, residue F (u x) = e (residue E x) := by
    have : (residue F).comp (u : E →+* F) = (e : ResidueField E →+* ResidueField F).comp
        (residue E) := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      change residue F (IsLocalization.lift hunits (algebraMap A E a)) = _
      rw [IsLocalization.lift_eq]
      exact hf₀ a
    exact fun x => RingHom.congr_fun this x
  refine ⟨u, ⟨fun x hx => ?_⟩, hres⟩
  have h1 : IsUnit (e (residue E x)) := by
    rw [← hres]; exact hx.map (residue F)
  have h2 : IsUnit (residue E x) := by
    rw [isUnit_iff_ne_zero] at h1 ⊢
    exact fun h => h1 (by rw [h, map_zero])
  exact isUnit_of_map_unit (residue E) _ h2

end IsLocalRing

/-! ### Local-étale algebras map uniquely into Henselian local rings -/

/-!
# Local-étale algebras map uniquely into Henselian local rings

Let `R → E` be a local-étale homomorphism of noetherian local rings
(`RingHom.IsEtaleLocalHom`) and let `F` be a Henselian local `R`-algebra. Two local
`R`-algebra homomorphisms `u v : E → F` inducing the same homomorphism of residue fields
`κ(E) → κ(F)` are equal. In particular this holds when `F` is strictly Henselian
(`StrictlyHenselianLocalRing`).

## Main results

* `AlgHom.eq_of_residueField_map_eq_of_isEtaleLocalHom`: two local `R`-algebra maps from a
  local-étale `R`-algebra to a Henselian local ring that agree on residue fields are equal.

## Implementation notes

The source assumes `F` strictly Henselian (and noetherian) and `R → F` local; the statement here
only needs `F` Henselian, and no condition on `R → F`. The proof does not pass through the
base change `(E ⊗[R] F)_Q`. Instead, `E` is written as the localization `A_q` of a finite type
`R`-subalgebra `A` at the prime `q = A ∩ 𝔪(E)`; then `A` is étale over `R` at `q`, so some
`A_g` with `g ∉ q` is étale over `R`. The restrictions of `u` and `v` to `A_g` reduce to the same
`R`-algebra map `A_g → κ(F)`, so they agree by the uniqueness of lifts of residue-field points of
étale algebras to Henselian local rings
(`HenselianLocalRing.existsUnique_algHom_residue_of_etale`), and hence `u = v` since `E` is a
localization of `A`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
* [Stacks Project, Tag 08HQ](https://stacks.math.columbia.edu/tag/08HQ)
-/

public section

open IsLocalRing

namespace AlgHom

variable {R E F : Type*} [CommRing R] [CommRing E] [CommRing F] [Algebra R E] [Algebra R F]
  [IsNoetherianRing R] [IsNoetherianRing E] [IsLocalRing R] [IsLocalRing E]
  [IsLocalHom (algebraMap R E)] [HenselianLocalRing F]

/-- Let `R → E` be a local-étale homomorphism of noetherian local rings and `F` a Henselian
local `R`-algebra. Two local `R`-algebra homomorphisms `u v : E → F` inducing the same map of
residue fields `κ(E) → κ(F)` are equal. -/
@[weil "lem_fk103_local_etale_maps_to_strictly_henselian_unique"]
theorem eq_of_residueField_map_eq_of_isEtaleLocalHom (hE : (algebraMap R E).IsEtaleLocalHom)
    (u v : E →ₐ[R] F) [IsLocalHom (u : E →+* F)] [IsLocalHom (v : E →+* F)]
    (h : ResidueField.map (u : E →+* F) = ResidueField.map (v : E →+* F)) : u = v := by
  obtain ⟨hflat, hunr, hess⟩ := hE
  have : Module.Flat R E := RingHom.flat_algebraMap_iff.mp hflat
  have : Algebra.FormallyUnramified R E := RingHom.formallyUnramified_algebraMap.mp hunr
  have : Algebra.EssFiniteType R E := RingHom.essFiniteType_algebraMap.mp hess
  set A := Algebra.EssFiniteType.subalgebra R E
  set q : Ideal A := (maximalIdeal E).comap (algebraMap A E)
  have hM : Algebra.EssFiniteType.submonoid R E = q.primeCompl := by
    ext x
    simp [Algebra.EssFiniteType.submonoid, q, Ideal.primeCompl, mem_maximalIdeal, mem_nonunits_iff,
      IsUnit.mem_submonoid_iff]
  have hloc : IsLocalization q.primeCompl E := hM ▸ Algebra.EssFiniteType.isLocalization R E
  -- `E` is the localization of `A` at `q`; transport to `Localization.AtPrime q`.
  let e : Localization.AtPrime q ≃ₐ[A] E := IsLocalization.algEquiv q.primeCompl _ E
  let eR : Localization.AtPrime q ≃ₐ[R] E := e.restrictScalars R
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_equiv eR.symm
  have : Module.Flat R (Localization.AtPrime q) := Module.Flat.of_linearEquiv eR.toLinearEquiv
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let p : Ideal R := q.comap (algebraMap R A)
  have : q.LiesOver p := ⟨rfl⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let : Localization.AtPrime.IsLiesOverAlgebra p q := inferInstance
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).2 inferInstance
  have hU : Algebra.IsUnramifiedAt R q := ‹Algebra.FormallyUnramified R (Localization.AtPrime q)›
  have : Algebra.IsEtaleAt R q := Algebra.IsEtaleAt.of_flat_of_map_eq_maximalIdeal p q
    ((Algebra.isUnramifiedAt_iff_map_eq R p q).mp hU).2
  obtain ⟨g, hg, hge⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) q
  have hgu : IsUnit (algebraMap A E g) := by
    by_contra hn
    exact hg (by simpa [q, mem_maximalIdeal, mem_nonunits_iff] using hn)
  let φ₀ : Localization.Away g →+* E := IsLocalization.Away.lift g hgu
  have hφ₀ (x : A) : φ₀ (algebraMap A (Localization.Away g) x) = algebraMap A E x :=
    IsLocalization.lift_eq _ x
  let φ : Localization.Away g →ₐ[R] E :=
    { φ₀ with
      commutes' := fun r => by
        change φ₀ (algebraMap R (Localization.Away g) r) = _
        rw [IsScalarTower.algebraMap_apply R A (Localization.Away g), hφ₀,
          ← IsScalarTower.algebraMap_apply] }
  have hφ (x : A) : φ (algebraMap A (Localization.Away g) x) = algebraMap A E x := hφ₀ x
  let ψ : Localization.Away g →ₐ[R] ResidueField F :=
    (IsScalarTower.toAlgHom R F (ResidueField F)).comp (u.comp φ)
  have key := HenselianLocalRing.existsUnique_algHom_residue_of_etale ψ
  have h1 : u.comp φ = v.comp φ := by
    refine key.unique (fun a => ?_) (fun a => ?_)
    · simp [ψ, ResidueField.algebraMap_eq]
    · have hv := ResidueField.map_residue (v : E →+* F) (φ a)
      have hu := ResidueField.map_residue (u : E →+* F) (φ a)
      rw [← h] at hv
      simp only [AlgHom.coe_comp, Function.comp_apply, ψ, IsScalarTower.coe_toAlgHom',
        ResidueField.algebraMap_eq]
      simpa using hv.symm.trans hu
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext q.primeCompl
  ext x
  have := congrArg (fun f : Localization.Away g →ₐ[R] F => f (algebraMap A _ x)) h1
  simpa [hφ] using this

end AlgHom
