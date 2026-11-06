module

public import Weil.Attr
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# An étale algebra over a smooth algebra is smooth

Let `P` be a smooth `A`-algebra and `P → E` an étale homomorphism. Then `E` is a smooth
`A`-algebra: an étale algebra is smooth, and smoothness is stable under composition.

## Main results

* `Algebra.Smooth.of_etale_of_smooth`: if `P` is smooth over `A` and `E` is étale over `P`, then
  `E` is smooth over `A`.
* `RingHom.Smooth.comp_of_etale`: the same statement for ring homomorphisms.

## Implementation notes

Smoothness is Mathlib's `Algebra.Smooth` (formally smooth and of finite presentation) and
étaleness is `Algebra.Etale`; for finitely generated algebras over noetherian rings these agree
with the definitions of the source (flatness with geometrically regular fibres, resp. flat,
finitely generated and unramified at every prime). No noetherian hypothesis is needed here.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

namespace Algebra.Smooth

/-- An étale algebra `E` over a smooth `A`-algebra `P` is a smooth `A`-algebra. -/
@[weil "lem_fk107_etale_over_smooth_algebra_is_smooth"]
theorem of_etale_of_smooth (A P E : Type*) [CommRing A] [CommRing P] [CommRing E]
    [Algebra A P] [Algebra P E] [Algebra A E] [IsScalarTower A P E]
    [Algebra.Smooth A P] [Algebra.Etale P E] : Algebra.Smooth A E :=
  Algebra.Smooth.comp A P E

end Algebra.Smooth

namespace RingHom.Smooth

/-- If `f : A → P` is smooth and `g : P → E` is étale, then `g ∘ f : A → E` is smooth. -/
@[weil "lem_fk107_etale_over_smooth_algebra_is_smooth"]
theorem comp_of_etale {A P E : Type*} [CommRing A] [CommRing P] [CommRing E]
    {f : A →+* P} {g : P →+* E} (hf : f.Smooth) (hg : g.Etale) : (g.comp f).Smooth :=
  hf.comp ((RingHom.etale_iff_formallyUnramified_and_smooth g).mp hg).2

end RingHom.Smooth

end

/-! ### Polynomial algebras are smooth -/

/-!
# Polynomial algebras are smooth

For every commutative ring `A` and every finite type `σ`, the polynomial algebra
`A[X_i : i ∈ σ]` is a smooth `A`-algebra: it is formally smooth and of finite presentation.

We also record the form in which smoothness is phrased in [FK]: the polynomial algebra is a flat
`A`-module, and for every field `K` with an `A`-algebra structure (in particular every field
extension of a residue field `κ(𝔭)`), the base change `K ⊗[A] A[X_i : i ∈ σ] ≅ K[X_i : i ∈ σ]`
is a regular ring.

## Main results

* `MvPolynomial.smooth`: `Algebra.Smooth A (MvPolynomial σ A)` for finite `σ`.
* `MvPolynomial.isRegularRing_tensorProduct_of_field`: `K ⊗[A] MvPolynomial σ A` is a regular
  ring for every field `K` that is an `A`-algebra.

## Implementation notes

Smoothness is Mathlib's `Algebra.Smooth` (formally smooth and finitely presented). Mathlib
provides `Algebra.FormallySmooth` and `Algebra.FinitePresentation` for `MvPolynomial σ A` as
instances, but not the bundled `Algebra.Smooth` instance, which `MvPolynomial.smooth` supplies.
The variables are indexed by an arbitrary finite type rather than `Fin n`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace MvPolynomial

variable (A : Type u) [CommRing A] (σ : Type v) [Finite σ]

/-- A polynomial algebra in finitely many variables over a ring `A` is a smooth `A`-algebra. -/
@[weil "lem_fk107_polynomial_algebra_smooth"]
instance smooth : Algebra.Smooth A (MvPolynomial σ A) where

/-- For a field `K` that is an `A`-algebra, the base change `K ⊗[A] A[X_i : i ∈ σ]` of a
polynomial algebra in finitely many variables is a regular ring. -/
theorem isRegularRing_tensorProduct_of_field (K : Type w) [Field K] [Algebra A K] :
    IsRegularRing (K ⊗[A] MvPolynomial σ A) :=
  IsRegularRing.of_ringEquiv
    (scalarRTensorAlgEquiv (R := A) (N := K) (σ := σ)).symm.toRingEquiv

end MvPolynomial

end

/-! ### Base change of smooth algebras (flat, geometrically regular fibres) -/

/-!
# Base change of smooth algebras (flat, geometrically regular fibres)

Let `A → C` be a finitely generated flat algebra whose fibres are
geometrically regular: for every prime `𝔭 ⊆ A` and every field extension `K ⊇ κ(𝔭)` the ring
`C ⊗[A] K` is regular. For a ring homomorphism `A → A'` with `A'` noetherian, the base change
`A' ⊗[A] C` has the same three properties over `A'`.

The proof follows the source: finite generation and flatness are stable under base change,
and for a prime `𝔭' ⊆ A'` and a field `K ⊇ κ(𝔭')` the field `K` is an extension of `κ(𝔭)`,
`𝔭` the contraction of `𝔭'`, while `K ⊗[A'] (A' ⊗[A] C) ≅ K ⊗[A] C`.

## Main results

- `Algebra.finiteType_flat_isRegularRing_fibres_baseChange`: the base change statement.

## Implementation notes

The notion of smoothness used here is the one of the source (finitely generated, flat, with
geometrically regular fibres over a noetherian base); it is spelled out in the hypotheses
rather than packaged as a new definition, since it agrees with Mathlib's `Algebra.Smooth`
(for which the base change is the instance `Algebra.Smooth.baseChange`) only through the
comparison theorem between the two notions. The source assumes `A` noetherian; the proof
does not use it, so the hypothesis is dropped. The field `K` ranges over a fixed universe `w`,
the same in the hypothesis and the conclusion. The base change is written `A' ⊗[A] C`
(left factor `A'`) rather than `C ⊗[A] A'`, so that it carries Mathlib's `A'`-algebra
structure.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7.
-/

@[expose] public section

universe u v u' w

open TensorProduct

namespace Algebra

/-- Base change of a smooth algebra in the sense of flatness plus geometrically regular
fibres: if `C` is a finitely generated flat `A`-algebra such that
`C ⊗[A] K` is regular for every prime `𝔭 ⊆ A` and every field extension `K` of `κ(𝔭)`, and
`A → A'` is a ring homomorphism with `A'` noetherian, then `A' ⊗[A] C` is a noetherian,
finitely generated, flat `A'`-algebra such that `(A' ⊗[A] C) ⊗[A'] K` is regular for every
prime `𝔭' ⊆ A'` and every field extension `K` of `κ(𝔭')`. -/
@[weil "lem_fk107_smooth_algebra_base_change"]
theorem finiteType_flat_isRegularRing_fibres_baseChange
    {A : Type u} {C : Type v} {A' : Type u'} [CommRing A] [CommRing C] [CommRing A']
    [Algebra A C] [Algebra A A'] [IsNoetherianRing A']
    (hfg : Algebra.FiniteType A C) (hflat : Module.Flat A C)
    (hreg : ∀ (p : Ideal A) [p.IsPrime] (K : Type w) [Field K] [Algebra A K]
      [Algebra p.ResidueField K] [IsScalarTower A p.ResidueField K],
      IsRegularRing (C ⊗[A] K)) :
    IsNoetherianRing (A' ⊗[A] C) ∧ Algebra.FiniteType A' (A' ⊗[A] C) ∧
      Module.Flat A' (A' ⊗[A] C) ∧
      ∀ (p' : Ideal A') [p'.IsPrime] (K : Type w) [Field K] [Algebra A' K]
        [Algebra p'.ResidueField K] [IsScalarTower A' p'.ResidueField K],
        IsRegularRing ((A' ⊗[A] C) ⊗[A'] K) := by
  have hfg' : Algebra.FiniteType A' (A' ⊗[A] C) := inferInstance
  refine ⟨Algebra.FiniteType.isNoetherianRing A' _, hfg', inferInstance, ?_⟩
  intro p' _ K _ _ _ _
  let p : Ideal A := p'.comap (algebraMap A A')
  let : Algebra A K := ((algebraMap A' K).comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra p.ResidueField K :=
    ((algebraMap p'.ResidueField K).comp
      (Ideal.ResidueField.map p p' (algebraMap A A') rfl)).toAlgebra
  have : IsScalarTower A p.ResidueField K := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    change algebraMap A' K (algebraMap A A' a) =
      algebraMap p'.ResidueField K
        (Ideal.ResidueField.map p p' (algebraMap A A') rfl (algebraMap A p.ResidueField a))
    rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply A' p'.ResidueField K]
  have := hreg p K
  let e : (A' ⊗[A] C) ⊗[A'] K ≃+* C ⊗[A] K :=
    ((Algebra.TensorProduct.comm A' (A' ⊗[A] C) K).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A A' K K C).toRingEquiv).trans
      (Algebra.TensorProduct.comm A K C).toRingEquiv
  exact IsRegularRing.of_ringEquiv e.symm

end Algebra
