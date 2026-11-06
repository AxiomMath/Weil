module

public import Weil.Attr
public import Weil.CategoryTheory.Sites.SheafCohomology.Basic
public import Weil.Defs.AlgebraicGeometry.Scheme
public import Weil.RingTheory.Henselian.Henselization.KeyLemmaLineCoordinateRing
public import Weil.RingTheory.Henselian.Henselization.HenselianLineFaithfullyFlat

/-!
# `H⁰` of a constant sheaf on the generic henselian line

Let `A` be an excellent henselian local domain with field of fractions `K`, let `L ⊇ K` be a
finite field extension, let `A{t}` be the henselization of `A[t]` at the origin and let
`X_L = Spec (A{t} ⊗_A L)`. For every abelian group `M`, the map `M → H⁰(X_L, M_{X_L})` sending
`m` to the constant section `m` is an isomorphism.

Indeed `H⁰(X_L, M_{X_L})` is the group of locally constant maps `|X_L| → M`. Writing `A_L` for
the integral closure of `A` in `L`, the ring `A{t} ⊗_A L` is a localization of the integral
domain `A_L{t}`; it is nonzero because `A → A{t}` is faithfully flat, so it is an integral
domain. Hence `X_L` is nonempty and irreducible, in particular connected, and a locally constant
map on it is constant.

## Main results

* `AlgebraicGeometry.bijective_hZeroLocallyConstantSheafAbAddEquiv_symm_const_henselianLineGeneric`:
  `M → H⁰(X_L, M_{X_L})`, `m ↦ m`, is bijective.

## Implementation notes

The étale cohomology is taken on the small étale site `SmallEtale E X_L hX` of a big étale site
`E` containing `X_L`, and the constant sheaf is the sheaf of locally constant `M`-valued maps.
The source's quotient field `κ` is any field `K` with `IsFractionRing A K`; noetherianity of `A`
is implied by excellence.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

public section

open CategoryTheory MvPolynomial
open scoped TensorProduct

universe w u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsDomain A] [HenselianLocalRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type u} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
  {B : Type u} [CommRing B] [IsLocalRing B] [Algebra (LocalizationAtOrigin A (Fin 1)) B]
  [Algebra A B] [IsScalarTower A (LocalizationAtOrigin A (Fin 1)) B]

include K in
/-- `A{t} ⊗_A L` is an integral domain, given the integral closure `C` of `A` in `L`. -/
private theorem isDomain_tensorProduct_of_isIntegralClosure (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A (Fin 1) B) (C : Type u) [CommRing C] [HenselianLocalRing C]
    [Algebra A C] [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    IsDomain (B ⊗[A] L) := by
  classical
  obtain ⟨B', _, _, _, hB'⟩ := exists_isHenselianPolynomialRing C (Fin 1)
  let : Algebra C B' :=
    ((algebraMap (LocalizationAtOrigin C (Fin 1)) B').comp
      (algebraMap C (LocalizationAtOrigin C (Fin 1)))).toAlgebra
  have : IsScalarTower C (LocalizationAtOrigin C (Fin 1)) B' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨⟨e, -⟩, hloc, hdom⟩ :=
    exists_ringEquiv_tensorProduct_of_isIntegralClosure (K := K) (L := L) (C := C) hA hB hB'
  have : Module.FaithfullyFlat A B := hB.faithfullyFlat
  have : Nontrivial (B ⊗[A] L) := Module.FaithfullyFlat.lTensor_nontrivial A B L
  have : Nontrivial (B' ⊗[C] L) := e.injective.nontrivial
  have : IsDomain (B' ⊗[C] L) := by
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (B' ⊗[C] L)
      (M := Algebra.algebraMapSubmonoid B' (Algebra.algebraMapSubmonoid C (nonZeroDivisors A)))
      fun s hs => mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    subst h0
    have := IsLocalization.uniqueOfZeroMem (S := B' ⊗[C] L) hs
    exact not_subsingleton (B' ⊗[C] L) inferInstance
  exact e.toMulEquiv.isDomain (B' ⊗[C] L)

include K in
/-- `A{t} ⊗_A L` is an integral domain. -/
private theorem isDomain_tensorProduct_of_isHenselianPolynomialRing (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A (Fin 1) B) : IsDomain (B ⊗[A] L) := by
  have : HenselianLocalRing (integralClosure A L) :=
    IsIntegralClosure.henselianLocalRing A L (integralClosure A L)
  exact isDomain_tensorProduct_of_isIntegralClosure (K := K) hA hB (integralClosure A L)

include K in
/-- `X_L = Spec (A{t} ⊗_A L)` is connected. -/
private theorem connectedSpace_henselianLineGeneric (hA : IsExcellent A)
    (hB : IsHenselianPolynomialRing A (Fin 1) B) : ConnectedSpace (henselianLineGeneric A B L) := by
  have := isDomain_tensorProduct_of_isHenselianPolynomialRing (K := K) (L := L) hA hB
  infer_instance

include K in
/-- **`H⁰` of a constant sheaf on the generic henselian line.** Let `A` be an excellent henselian
local domain with field of fractions `K`, `L` a finite extension of `K`, `B = A{t}` the
henselization of `A[t]` at the origin and `X_L = Spec (B ⊗_A L)`. For every abelian group `M`,
the map `M → H⁰(X_L, M_{X_L})` sending `m` to the class of the constant section `m` is
bijective. -/
@[weil "lem_fk107_key_lemma_h0_line"]
theorem bijective_hZeroLocallyConstantSheafAbAddEquiv_symm_const_henselianLineGeneric
    (hA : IsExcellent A) (hB : IsHenselianPolynomialRing A (Fin 1) B) (E : BigEtaleSite.{u})
    (hX : E.Contains (henselianLineGeneric A B L)) (M : Type u) [AddCommGroup M]
    [HasExt.{w} (Sheaf (SmallEtale.topology E (henselianLineGeneric A B L) hX)
      AddCommGrpCat.{u})] :
    Function.Bijective fun m : M =>
      (SmallNoetherianSeparatedEtale.hZeroLocallyConstantSheafAbAddEquiv E
        (henselianLineGeneric A B L) hX M).symm (LocallyConstant.const _ m) := by
  have := connectedSpace_henselianLineGeneric (K := K) (L := L) hA hB
  obtain ⟨x⟩ := (inferInstance : Nonempty (henselianLineGeneric A B L))
  refine (AddEquiv.bijective _).comp ⟨fun m n h => ?_, fun f => ⟨f x, (f.eq_const x).symm⟩⟩
  simpa using congrArg (fun g : LocallyConstant _ M => g x) h

end AlgebraicGeometry
