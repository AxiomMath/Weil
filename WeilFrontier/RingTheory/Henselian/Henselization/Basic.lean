module

public import Weil.Attr
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import WeilFrontier.Defs.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import WeilFrontier.Defs.RingTheory.Henselian.Henselization.Defs
public import WeilFrontier.RingTheory.Henselian.QuasiFinite
public import WeilFrontier.RingTheory.Ideal.GoingUp

/-!
# Localizations of a finite algebra base changed to a strict Henselization

Let `A` be a local ring, `B` a finite `A`-algebra, `k` a separably closed field, `φ : A → k` a
local homomorphism and `(Ã, ψ)` the Henselization of `A` with respect to `φ`, so that `Ã` is a
strictly henselian local ring. Put `T = Ã ⊗[A] B`. For every maximal ideal `M` of `T` the
localization `T_M` is a strictly henselian local ring, and its residue field is a purely
inseparable extension of the residue field of `Ã`.

Indeed `T` is finite over `Ã`, so `T_M` is henselian and finite over `Ã`, and `Ã → T_M` is local.
The residue field of `T_M` is then a finite, hence algebraic, extension of the separably closed
residue field of `Ã`, so it is purely inseparable over it and separably closed.

## Main results

* `IsLocalRing.isLocalHom_algebraMap_localization_atPrime_of_isIntegral`: for an integral
  algebra `S` over a local ring `R` and a maximal ideal `M` of `S`, the map `R → S_M` is local.
* `IsLocalRing.IsHenselizationAlong.strictlyHenselianLocalRing_localization_tensorProduct`:
  `T_M` is strictly henselian.
* `IsLocalRing.IsHenselizationAlong.isPurelyInseparable_residueField_localization_tensorProduct`:
  the residue field of `T_M` is purely inseparable over that of `Ã`.

## Implementation notes

The source assumes `A` noetherian; the statement holds without it, and is stated so.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.3
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w x

namespace IsLocalRing

/-- For an integral algebra `S` over a local ring `R` and a maximal ideal `M` of `S`, the
structure map `R → S_M` is a local homomorphism. -/
instance isLocalHom_algebraMap_localization_atPrime_of_isIntegral {R : Type*} [CommRing R]
    [IsLocalRing R] {S : Type*} [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (M : Ideal S) [M.IsMaximal] : IsLocalHom (algebraMap R (Localization.AtPrime M)) := by
  rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime M)]
  exact isLocalHom_algebraMap_localization_comp_of_isIntegral (algebraMap R S)
    (Algebra.IsIntegral.isIntegral) M

namespace IsHenselizationAlong

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
  [Module.Finite A B] {k : Type w} [Field k] [IsSepClosed k] {φ : A →+* k} [IsLocalHom φ]
  {Ã : Type x} [CommRing Ã] [IsLocalRing Ã] [Algebra A Ã] {ψ : Ã →+* k}

theorem strictlyHenselianLocalRing (h : IsHenselizationAlong φ Ã ψ) :
    StrictlyHenselianLocalRing Ã :=
  have := h.henselian
  have := h.isSepClosed_residueField
  StrictlyHenselianLocalRing.of_isSepClosed_residueField Ã

omit [IsSepClosed k] in
/-- `T_M` is a finite `Ã`-module, for `T = Ã ⊗[A] B` and a maximal ideal `M` of `T`. -/
theorem module_finite_localization_tensorProduct (h : IsHenselizationAlong φ Ã ψ)
    (M : Ideal (Ã ⊗[A] B)) [M.IsMaximal] : Module.Finite Ã (Localization.AtPrime M) :=
  have := h.henselian
  HenselianLocalRing.module_finite_of_isLocalization_atPrime_of_isMaximal Ã (Ã ⊗[A] B) M _

/-- **Localizations of a finite algebra base changed to a strict Henselization.** Let `B` be a
finite `A`-algebra and `(Ã, ψ)` the Henselization of `A` with respect to a local homomorphism
`φ : A → k` to a separably closed field. For every maximal ideal `M` of `T = Ã ⊗[A] B`, the
localization `T_M` is strictly henselian. -/
@[weil "lem_fk103_strict_henselization_tensor_factors_strictly_henselian"]
theorem strictlyHenselianLocalRing_localization_tensorProduct (h : IsHenselizationAlong φ Ã ψ)
    (M : Ideal (Ã ⊗[A] B)) [M.IsMaximal] :
    StrictlyHenselianLocalRing (Localization.AtPrime M) := by
  have := h.henselian
  have := h.isSepClosed_residueField
  have := h.module_finite_localization_tensorProduct (B := B) M
  have : HenselianLocalRing (Localization.AtPrime M) :=
    HenselianLocalRing.of_isLocalization_atPrime_of_finite (R := Ã) M _
  have : Algebra.IsAlgebraic (ResidueField Ã) (ResidueField (Localization.AtPrime M)) :=
    inferInstance
  have : IsSepClosed (ResidueField (Localization.AtPrime M)) :=
    Algebra.IsAlgebraic.isSepClosed (F := ResidueField Ã)
  exact StrictlyHenselianLocalRing.of_isSepClosed_residueField _

/-- **The residue fields of the localizations of a finite algebra base changed to a strict
Henselization.** In the situation of `strictlyHenselianLocalRing_localization_tensorProduct`,
the residue field of `T_M` is a purely inseparable extension of the residue field of `Ã`. -/
@[weil "lem_fk103_strict_henselization_tensor_factors_strictly_henselian"]
theorem isPurelyInseparable_residueField_localization_tensorProduct
    (h : IsHenselizationAlong φ Ã ψ) (M : Ideal (Ã ⊗[A] B)) [M.IsMaximal] :
    IsPurelyInseparable (ResidueField Ã) (ResidueField (Localization.AtPrime M)) := by
  have := h.isSepClosed_residueField
  have := h.module_finite_localization_tensorProduct (B := B) M
  infer_instance

end IsHenselizationAlong

end IsLocalRing
