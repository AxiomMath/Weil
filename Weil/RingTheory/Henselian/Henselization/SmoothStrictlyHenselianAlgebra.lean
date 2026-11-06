module

public import Weil.Attr
public import Weil.Defs.RingTheory.Henselian.Henselization.SmoothStrictlyHenselianAlgebra
public import Weil.RingTheory.Henselian.Henselization.HenselizationResidueFieldSeparableAlgebraic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Weil.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.RingTheory.Etale.IndEtaleTensorProduct
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Residue fields of sh-smooth algebras with algebraic residue extension

Let `A → B` be a local homomorphism of local rings, with the residue field of `A` separably
closed (for instance `A` strictly Henselian), and let `B` be sh-smooth over `A`: `B` is the strict
Henselization of a localization `C` of a smooth `A`-algebra at a prime, with `A → C` local. If the
residue field `κ(B)` is algebraic over `κ(A)`, then `κ(B)` is a finite purely inseparable extension
of `κ(A)`.

The residue field `κ(C)` is a field essentially of finite type over `κ(A)`; it embeds into
`κ(B)`, so it is algebraic, hence finite, over `κ(A)`, and therefore purely inseparable and
separably closed. The residue field of the Henselization is separable algebraic over `κ(C)`, hence
equal to `κ(C)`.

## Main results

* `Algebra.IsShSmooth.finite_isPurelyInseparable_residueField`: `κ(B)` is finite and purely
  inseparable over `κ(A)`.
* `Algebra.IsShSmooth.finite_residueField`: `κ(B)` is finite over `κ(A)`.

## Implementation notes

The source assumes `A` and `B` strictly Henselian. Only the separable closedness of the residue
field of `A` and the locality of `B` are used; a strictly Henselian local ring `A` provides the
former through `StrictlyHenselianLocalRing`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Algebra.IsShSmooth

variable {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- The residue field of a localization of a smooth `A`-algebra, with `A → C` local, is
essentially of finite type over the residue field of `A`. -/
theorem essFiniteType_residueField_of_isSmoothLocalization {C : Type u} [CommRing C]
    [IsLocalRing C] [Algebra A C] [IsLocalHom (algebraMap A C)] (hC : IsSmoothLocalization A C) :
    Algebra.EssFiniteType (ResidueField A) (ResidueField C) := by
  obtain ⟨C₀, _, _, _, q, _, ⟨f⟩⟩ := hC
  have : Algebra.EssFiniteType A (Localization.AtPrime q) :=
    Algebra.EssFiniteType.comp A C₀ _
  have : Algebra.EssFiniteType A C := Algebra.EssFiniteType.of_surjective f.toAlgHom f.surjective
  have : Algebra.EssFiniteType C (ResidueField C) :=
    Algebra.EssFiniteType.of_surjective (Algebra.ofId C (ResidueField C)) residue_surjective
  have : Algebra.EssFiniteType A (ResidueField C) := Algebra.EssFiniteType.comp A C _
  exact Algebra.EssFiniteType.of_comp A (ResidueField A) (ResidueField C)

/-- **Residue fields of sh-smooth algebras.** Let `A → B` be a local homomorphism of local rings
with `κ(A)` separably closed (e.g. of strictly Henselian local rings), `B` sh-smooth over `A`, and
`κ(B)` algebraic over `κ(A)`. Then `κ(B)` is a finite purely inseparable extension of `κ(A)`. -/
@[weil "lem_fk107_sh_smooth_algebraic_residue_finite_purely_inseparable"]
theorem finite_isPurelyInseparable_residueField [IsSepClosed (ResidueField A)]
    (h : IsShSmooth A B) [Algebra.IsAlgebraic (ResidueField A) (ResidueField B)] :
    Module.Finite (ResidueField A) (ResidueField B) ∧
      IsPurelyInseparable (ResidueField A) (ResidueField B) := by
  refine ⟨?_, inferInstance⟩
  obtain ⟨C, _, _, _, hC, _, k, _, _, φ, _, Csh, _, _, _, _, _, ψ, hψ, ⟨e⟩⟩ := h
  have := hψ.isLocalHom_algebraMap
  have : IsLocalHom (algebraMap A Csh) := by
    rw [IsScalarTower.algebraMap_eq A C Csh]
    infer_instance
  -- `κ(B) ≅ κ(Csh)` over `κ(A)`.
  let e' : ResidueField B ≃ₐ[ResidueField A] ResidueField Csh := ResidueField.mapAlgEquiv' e
  have : Algebra.IsAlgebraic (ResidueField A) (ResidueField Csh) :=
    Algebra.IsAlgebraic.of_injective e'.symm.toAlgHom e'.symm.injective
  -- `κ(C)` is algebraic, hence finite, over `κ(A)`, and separably closed.
  have : Algebra.IsAlgebraic (ResidueField A) (ResidueField C) :=
    Algebra.IsAlgebraic.tower_bot_of_injective (algebraMap (ResidueField C) _).injective
      (A := ResidueField Csh)
  have : Algebra.EssFiniteType (ResidueField A) (ResidueField C) :=
    essFiniteType_residueField_of_isSmoothLocalization hC
  have : Module.Finite (ResidueField A) (ResidueField C) :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : IsSepClosed (ResidueField C) := Algebra.IsAlgebraic.isSepClosed (F := ResidueField A)
  -- `κ(Csh)` is separable over `κ(C)`, hence equal to it.
  have : Algebra.IsSeparable (ResidueField C) (ResidueField Csh) := hψ.isSeparable_residueField
  have hbij := IsSepClosed.algebraMap_bijective (ResidueField C) (ResidueField Csh)
  have : Module.Finite (ResidueField C) (ResidueField Csh) :=
    Module.Finite.of_surjective (Algebra.linearMap (ResidueField C) (ResidueField Csh)) hbij.2
  have : Module.Finite (ResidueField A) (ResidueField Csh) :=
    Module.Finite.trans (ResidueField C) (ResidueField Csh)
  exact Module.Finite.equiv e'.symm.toLinearEquiv

/-- Under the hypotheses of `Algebra.IsShSmooth.finite_isPurelyInseparable_residueField`, the
residue field of `B` is finite over that of `A`. -/
theorem finite_residueField [IsSepClosed (ResidueField A)] (h : IsShSmooth A B)
    [Algebra.IsAlgebraic (ResidueField A) (ResidueField B)] :
    Module.Finite (ResidueField A) (ResidueField B) :=
  (finite_isPurelyInseparable_residueField h).1

end Algebra.IsShSmooth

end

/-! ### Sh-smooth algebras under finite base change -/

/-!
# Sh-smooth algebras under finite base change

Let `A` be a strictly Henselian local ring, `B` an `A`-algebra which is sh-smooth over `A`, and
`A₁` a local `A`-algebra, finite as an `A`-module. Then `A₁` and `A₁ ⊗[A] B` are strictly
Henselian local rings, `A₁ → A₁ ⊗[A] B` is local, and `A₁ ⊗[A] B` is sh-smooth over `A₁`.

The proof rests on a statement about tensor products of local rings. Let `R → S` be a local
homomorphism of local rings and `T` a local `R`-algebra, finite over `R`, whose residue field is
purely inseparable over that of `R`. Then `T ⊗[R] S` is a local ring, both maps into it are local,
and its residue field is purely inseparable over that of `S`. Indeed every maximal ideal of
`T ⊗[R] S` contains `𝔪(T)` and `𝔪(S)` (by integrality), and in `κ(T) ⊗[R] κ(S)` some `q`-power
`y ^ q ^ n` of every element lies in `1 ⊗ κ(S)` (`q` the exponential characteristic), which forces
a unique maximal ideal.

Writing `B ≅ Csh` for a strict Henselization `Csh` of a local, essentially smooth `A`-algebra `C`,
the ring `C₁ = A₁ ⊗[A] C` is then local and essentially smooth over `A₁`, and `A₁ ⊗[A] Csh` is a
strict Henselization of `C₁`: it is ind-étale over `C₁` by base change, henselian as a local ring
finite over `Csh`, and its residue field is separable over `κ(C₁)` (it is generated by `κ(C₁)` and
the separable extension `κ(Csh)` of `κ(C)`) and separably closed (purely inseparable over the
separably closed `κ(Csh)`).

## Main results

* `Algebra.TensorProduct.isLocalRing_of_isPurelyInseparable`: `T ⊗[R] S` is local.
* `Algebra.TensorProduct.isLocalHom_algebraMap_of_isPurelyInseparable`,
  `Algebra.TensorProduct.isLocalHom_includeRight_of_isPurelyInseparable`: the maps from `T` and
  from `S` are local.
* `Algebra.TensorProduct.exists_pow_residue_eq_residue_one_tmul`: a `q`-power of every element of
  the residue field of `T ⊗[R] S` comes from `κ(S)`.
* `Algebra.IsSmoothLocalization.tensorProduct`: a localization of a smooth algebra stays one
  after base change, when the base change is local.
* `Algebra.IsShSmooth.tensorProduct_of_module_finite`: sh-smoothness is stable under finite local
  base change.

## Implementation notes

The source assumes moreover that `A → B` is a local homomorphism of strictly Henselian local
rings, that `κ(B)` is algebraic over `κ(A)`, that `A₁` is free over `A` with `A → A₁` local, and
that `κ(A₁) ≅ κ(B)` as `κ(A)`-algebras. These are not used: `A → A₁` is local because `A₁` is
integral over `A`, and `κ(A₁)` is purely inseparable over `κ(A)` because it is algebraic over the
separably closed field `κ(A)`, which is all the proof needs. The tensor product is written
`A₁ ⊗[A] B` rather than `B ⊗[A] A₁`, so that its `A₁`-algebra structure is the standard one.
The rings `A` and `A₁` are taken in one universe, as `Algebra.IsShSmooth` takes its auxiliary rings
in the universe of the base.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.7
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v

namespace Algebra.TensorProduct

section Frobenius

variable {R : Type*} [CommRing R] {L K : Type*} [CommRing L] [Field K] [Algebra R L]
  [Algebra R K]

/-- If a `q`-power of every element of `L` comes from `R`, then a `q`-power of every element of
`L ⊗[R] K` lies in `1 ⊗ K`. -/
theorem exists_pow_eq_one_tmul (q : ℕ) [ExpChar K q]
    (hL : ∀ l : L, ∃ n : ℕ, ∃ r : R, l ^ q ^ n = algebraMap R L r) (y : L ⊗[R] K) :
    ∃ n : ℕ, ∃ k : K, y ^ q ^ n = (1 : L) ⊗ₜ k := by
  rcases subsingleton_or_nontrivial (L ⊗[R] K) with h | h
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  have : ExpChar (L ⊗[R] K) q :=
    expChar_of_injective_ringHom (f := (includeRight : K →ₐ[R] L ⊗[R] K).toRingHom)
      (RingHom.injective _) q
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul l k =>
    obtain ⟨n, r, hr⟩ := hL l
    refine ⟨n, algebraMap R K r * k ^ q ^ n, ?_⟩
    rw [tmul_pow, hr, Algebra.algebraMap_eq_smul_one, smul_tmul, Algebra.smul_def]
  | add y z hy hz =>
    obtain ⟨a, u, hu⟩ := hy
    obtain ⟨b, w, hw⟩ := hz
    refine ⟨a + b, u ^ q ^ b + w ^ q ^ a, ?_⟩
    rw [add_pow_expChar_pow, pow_add, pow_mul, hu, mul_comm, pow_mul, hw, tmul_pow, tmul_pow,
      one_pow, one_pow, tmul_add]

end Frobenius

section Integral

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The map `S → T ⊗[R] S` is integral when `T` is finite over `R`. -/
theorem isIntegral_includeRight [Module.Finite R T] :
    (includeRight : S →ₐ[R] T ⊗[R] S).toRingHom.IsIntegral := by
  have h1 : (algebraMap S (S ⊗[R] T)).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  have h2 := RingHom.IsIntegral.trans _ _ h1 (RingHom.isIntegral_of_surjective
    (Algebra.TensorProduct.comm R S T).toRingEquiv.toRingHom
    (Algebra.TensorProduct.comm R S T).toRingEquiv.surjective)
  have heq : (includeRight : S →ₐ[R] T ⊗[R] S).toRingHom =
      (Algebra.TensorProduct.comm R S T).toRingEquiv.toRingHom.comp (algebraMap S (S ⊗[R] T)) :=
    RingHom.ext fun s => by simp
  rw [heq]
  exact h2

end Integral

section LocalRing

variable {R S T : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [CommRing T] [IsLocalRing T] [Algebra R S] [Algebra R T] [IsLocalHom (algebraMap R S)]

/-- The map `T ⊗[R] S → κ(T) ⊗[R] κ(S)`. -/
noncomputable abbrev residueTensorMap : T ⊗[R] S →ₐ[R] ResidueField T ⊗[R] ResidueField S :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R T (ResidueField T))
    (IsScalarTower.toAlgHom R S (ResidueField S))

omit [IsLocalRing R] [IsLocalHom (algebraMap R S)] in
/-- The kernel of `T ⊗[R] S → κ(T) ⊗[R] κ(S)` lies in every ideal containing `𝔪(T) ⊗ 1` and
`1 ⊗ 𝔪(S)`. -/
theorem ker_residueTensorMap_le (P : Ideal (T ⊗[R] S))
    (hT : ∀ t ∈ maximalIdeal T, t ⊗ₜ (1 : S) ∈ P) (hS : ∀ s ∈ maximalIdeal S, (1 : T) ⊗ₜ s ∈ P) :
    RingHom.ker (residueTensorMap (R := R) (S := S) (T := T)) ≤ P := by
  have hkT : RingHom.ker (IsScalarTower.toAlgHom R T (ResidueField T)) = maximalIdeal T := by
    ext x
    simp [RingHom.mem_ker, residue_eq_zero_iff]
  have hkS : RingHom.ker (IsScalarTower.toAlgHom R S (ResidueField S)) = maximalIdeal S := by
    ext x
    simp [RingHom.mem_ker, residue_eq_zero_iff]
  rw [residueTensorMap, Algebra.TensorProduct.map_ker _ _ (residue_surjective) (residue_surjective),
    hkT, hkS, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  exact ⟨fun t ht => hT t ht, fun s hs => hS s hs⟩

variable [Module.Finite R T]

omit [IsLocalRing R] [IsLocalRing T] [IsLocalHom (algebraMap R S)] in
/-- A maximal ideal of `T ⊗[R] S` contains `1 ⊗ 𝔪(S)`. -/
theorem one_tmul_mem_of_isMaximal (M : Ideal (T ⊗[R] S)) [M.IsMaximal] (s : S)
    (hs : s ∈ maximalIdeal S) : (1 : T) ⊗ₜ s ∈ M := by
  have : (M.comap (includeRight : S →ₐ[R] T ⊗[R] S).toRingHom).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ isIntegral_includeRight M
  rw [← IsLocalRing.eq_maximalIdeal this] at hs
  simpa using hs

/-- A maximal ideal of `T ⊗[R] S` contains `𝔪(T) ⊗ 1`. -/
theorem tmul_one_mem_of_isMaximal (M : Ideal (T ⊗[R] S)) [M.IsMaximal] (t : T)
    (ht : t ∈ maximalIdeal T) : t ⊗ₜ (1 : S) ∈ M := by
  let P : Ideal T := M.comap (algebraMap T (T ⊗[R] S))
  have hR : P.comap (algebraMap R T) = maximalIdeal R := by
    refine le_antisymm (le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.comap_ne_top _
      (Ideal.IsMaximal.ne_top ‹_›)))) fun r hr => ?_
    have h1 : algebraMap R S r ∈ maximalIdeal S := fun hu =>
      hr (isUnit_of_map_unit (algebraMap R S) r hu)
    have h2 := one_tmul_mem_of_isMaximal M _ h1
    rw [Ideal.mem_comap, Ideal.mem_comap, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one, smul_tmul,
      ← Algebra.algebraMap_eq_smul_one]
    exact h2
  have : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P
    (hR ▸ inferInstance)
  rw [← IsLocalRing.eq_maximalIdeal this] at ht
  simpa [P] using ht

variable [IsLocalHom (algebraMap R T)] [IsPurelyInseparable (ResidueField R) (ResidueField T)]

omit [Module.Finite R T] in
/-- A `q`-power of every element of `T ⊗[R] S` is congruent to an element of `1 ⊗ S` modulo the
kernel of `T ⊗[R] S → κ(T) ⊗[R] κ(S)`. -/
theorem exists_pow_sub_one_tmul_mem_ker (q : ℕ) [ExpChar (ResidueField R) q] (x : T ⊗[R] S) :
    ∃ n : ℕ, ∃ s : S, x ^ q ^ n - (1 : T) ⊗ₜ s ∈
      RingHom.ker (residueTensorMap (R := R) (S := S) (T := T)) := by
  have : ExpChar (ResidueField S) q :=
    expChar_of_injective_ringHom (f := ResidueField.map (algebraMap R S)) (RingHom.injective _) q
  have hL : ∀ l : ResidueField T, ∃ n : ℕ, ∃ r : R,
      l ^ q ^ n = algebraMap R (ResidueField T) r := by
    intro l
    obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem (ResidueField R) q l
    obtain ⟨r, rfl⟩ := residue_surjective c
    refine ⟨n, r, ?_⟩
    rw [← hc]
    simp only [ResidueField.algebraMap_residue]
    rfl
  obtain ⟨n, k, hk⟩ := exists_pow_eq_one_tmul q hL (residueTensorMap x)
  obtain ⟨s, rfl⟩ := residue_surjective k
  refine ⟨n, s, ?_⟩
  rw [RingHom.mem_ker, map_sub, map_pow, hk, residueTensorMap, Algebra.TensorProduct.map_tmul,
    map_one, sub_eq_zero]
  rfl

omit [Module.Finite R T] in
/-- An ideal `I ≠ ⊤` of `T ⊗[R] S` containing `𝔪(T) ⊗ 1` and `1 ⊗ 𝔪(S)` lies in every prime with
the same property. -/
theorem le_of_maximalIdeal_tmul_mem (P : Ideal (T ⊗[R] S)) [P.IsPrime]
    (hPT : ∀ t ∈ maximalIdeal T, t ⊗ₜ (1 : S) ∈ P) (hPS : ∀ s ∈ maximalIdeal S, (1 : T) ⊗ₜ s ∈ P)
    (I : Ideal (T ⊗[R] S)) (hI : I ≠ ⊤)
    (hIT : ∀ t ∈ maximalIdeal T, t ⊗ₜ (1 : S) ∈ I) (hIS : ∀ s ∈ maximalIdeal S, (1 : T) ⊗ₜ s ∈ I) :
    I ≤ P := by
  obtain ⟨q, _⟩ := ExpChar.exists (ResidueField R)
  intro x hx
  obtain ⟨n, s, hs⟩ := exists_pow_sub_one_tmul_mem_ker q x
  have hsI : (1 : T) ⊗ₜ s ∈ I := by
    have := sub_mem (I.pow_mem_of_mem hx (q ^ n) (pow_pos (expChar_pos (ResidueField R) q) n))
      (ker_residueTensorMap_le I hIT hIS hs)
    simpa using this
  have hsm : s ∈ maximalIdeal S := by
    refine le_maximalIdeal (J := I.comap (includeRight : S →ₐ[R] T ⊗[R] S).toRingHom)
      (Ideal.comap_ne_top _ hI) ?_
    simpa using hsI
  have hxP : x ^ q ^ n ∈ P := by
    have := add_mem (ker_residueTensorMap_le P hPT hPS hs) (hPS s hsm)
    simpa using this
  exact ‹P.IsPrime›.mem_of_pow_mem _ hxP

omit [Module.Finite R T] in
/-- `T ⊗[R] S` is a nonzero ring. -/
theorem nontrivial_of_isPurelyInseparable : Nontrivial (T ⊗[R] S) := by
  let Ω := AlgebraicClosure (ResidueField S)
  let : Algebra (ResidueField R) Ω :=
    ((algebraMap (ResidueField S) Ω).comp (algebraMap (ResidueField R) (ResidueField S))).toAlgebra
  have : Algebra.IsAlgebraic (ResidueField R) (ResidueField T) :=
    IsPurelyInseparable.isAlgebraic _ _
  let σ : ResidueField T →ₐ[ResidueField R] Ω := IsAlgClosed.lift
  let : Algebra R Ω :=
    ((algebraMap (ResidueField S) Ω).comp (algebraMap R (ResidueField S))).toAlgebra
  let φ : S →ₐ[R] Ω :=
    { (algebraMap (ResidueField S) Ω).comp (residue S) with commutes' := fun _ => rfl }
  let ψ : T →ₐ[R] Ω :=
    { (σ : ResidueField T →+* Ω).comp (residue T) with
      commutes' := fun r => by
        have h1 : residue T (algebraMap R T r) =
            algebraMap (ResidueField R) (ResidueField T) (residue R r) := by simp
        have h2 : residue S (algebraMap R S r) =
            algebraMap (ResidueField R) (ResidueField S) (residue R r) := by simp
        change σ (residue T (algebraMap R T r)) =
          algebraMap (ResidueField S) Ω (residue S (algebraMap R S r))
        rw [h1, h2, σ.commutes]
        rfl }
  exact (productMap ψ φ).toRingHom.domain_nontrivial

/-- **The tensor product with a finite local algebra with purely inseparable residue field is
local.** Let `R → S` be a local homomorphism of local rings and `T` a local `R`-algebra, finite
over `R`, with `κ(T)` purely inseparable over `κ(R)`. Then `T ⊗[R] S` is a local ring. -/
theorem isLocalRing_of_isPurelyInseparable : IsLocalRing (T ⊗[R] S) := by
  have := nontrivial_of_isPurelyInseparable (R := R) (S := S) (T := T)
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (T ⊗[R] S)
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun J hJ => ?_⟩
  exact hJ.eq_of_le hM.ne_top (le_of_maximalIdeal_tmul_mem M (tmul_one_mem_of_isMaximal M)
    (one_tmul_mem_of_isMaximal M) J hJ.ne_top (tmul_one_mem_of_isMaximal J)
    (one_tmul_mem_of_isMaximal J))

variable [IsLocalRing (T ⊗[R] S)]

omit [IsLocalHom (algebraMap R T)] [IsPurelyInseparable (ResidueField R) (ResidueField T)] in
/-- The map `T → T ⊗[R] S` is local. -/
theorem isLocalHom_algebraMap_of_isPurelyInseparable :
    IsLocalHom (algebraMap T (T ⊗[R] S)) := by
  refine ((local_hom_TFAE (algebraMap T (T ⊗[R] S))).out 1 4).2 fun t ht => ?_
  exact tmul_one_mem_of_isMaximal (maximalIdeal _) t ht

omit [IsLocalRing R] [IsLocalRing T] [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]
  [IsPurelyInseparable (ResidueField R) (ResidueField T)] in
/-- The map `S → T ⊗[R] S` is local. -/
theorem isLocalHom_includeRight_of_isPurelyInseparable :
    IsLocalHom (includeRight : S →ₐ[R] T ⊗[R] S).toRingHom := by
  refine ((local_hom_TFAE (includeRight : S →ₐ[R] T ⊗[R] S).toRingHom).out 1 4).2 fun s hs => ?_
  exact one_tmul_mem_of_isMaximal (maximalIdeal _) s hs

/-- A `q`-power of every element of the residue field of `T ⊗[R] S` is the residue of an element
of `1 ⊗ S`. -/
theorem exists_pow_residue_eq_residue_one_tmul (q : ℕ) [ExpChar (ResidueField R) q]
    (z : ResidueField (T ⊗[R] S)) :
    ∃ n : ℕ, ∃ s : S, z ^ q ^ n = residue (T ⊗[R] S) ((1 : T) ⊗ₜ s) := by
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨n, s, hs⟩ := exists_pow_sub_one_tmul_mem_ker q x
  refine ⟨n, s, ?_⟩
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact ker_residueTensorMap_le _ (tmul_one_mem_of_isMaximal _) (one_tmul_mem_of_isMaximal _) hs

end LocalRing

end Algebra.TensorProduct

namespace Algebra

/-- **Localizations of smooth algebras under base change.** If `C` is the localization of a smooth
`A`-algebra at a prime and `A₁ ⊗[A] C` is a local ring, then `A₁ ⊗[A] C` is the localization of a
smooth `A₁`-algebra at a prime. -/
theorem IsSmoothLocalization.tensorProduct {A A₁ C : Type u} [CommRing A] [CommRing A₁]
    [CommRing C] [Algebra A A₁] [Algebra A C] (h : IsSmoothLocalization A C)
    [IsLocalRing (A₁ ⊗[A] C)] : IsSmoothLocalization A₁ (A₁ ⊗[A] C) := by
  obtain ⟨C₀, _, _, _, q, _, ⟨e⟩⟩ := h
  let D := A₁ ⊗[A] Localization.AtPrime q
  let f : D ≃ₐ[A₁] A₁ ⊗[A] C := Algebra.TensorProduct.congr AlgEquiv.refl e
  have : IsLocalRing D := f.symm.toRingEquiv.isLocalRing
  refine IsSmoothLocalization.of_algEquiv ?_ f
  let : Algebra (A₁ ⊗[A] C₀) D :=
    (Algebra.TensorProduct.map (AlgHom.id A₁ A₁)
      (IsScalarTower.toAlgHom A C₀ (Localization.AtPrime q))).toRingHom.toAlgebra
  have : IsScalarTower A₁ (A₁ ⊗[A] C₀) D :=
    .of_algebraMap_eq fun _ => by simp [RingHom.algebraMap_toAlgebra, D]
  have : IsLocalization (q.primeCompl.map
      (Algebra.TensorProduct.includeRight (R := A) (A := A₁))) D :=
    IsLocalization.tensorProduct_tensorProduct_right A A₁ q.primeCompl (Localization.AtPrime q)
      (by ext; simp [RingHom.algebraMap_toAlgebra])
  have hself : IsLocalization.AtPrime D (maximalIdeal D) :=
    IsLocalization.self fun x hx => (IsUnit.mem_submonoid_iff x).mpr <| by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hx
  let q' : Ideal (A₁ ⊗[A] C₀) := (maximalIdeal D).comap (algebraMap (A₁ ⊗[A] C₀) D)
  have hT : IsLocalization.AtPrime D q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (q.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := A₁))) D (maximalIdeal D)
  exact ⟨A₁ ⊗[A] C₀, inferInstance, inferInstance, inferInstance, q', inferInstance,
    ⟨(IsLocalization.algEquiv q'.primeCompl _ D).restrictScalars A₁⟩⟩

end Algebra

namespace Algebra.IsShSmooth

open Algebra.TensorProduct

/-- **Sh-smoothness under finite base change.** Let `A` be a strictly Henselian local ring, `B` an
`A`-algebra which is sh-smooth over `A`, and `A₁` a local `A`-algebra which is finite as an
`A`-module. Then `A₁` and `A₁ ⊗[A] B` are strictly Henselian local rings, the map
`A₁ → A₁ ⊗[A] B` is local, and `A₁ ⊗[A] B` is sh-smooth over `A₁`. -/
@[weil "lem_fk107_smooth_strictly_henselian_finite_base_change"]
theorem tensorProduct_of_module_finite {A A₁ : Type u} {B : Type v} [CommRing A]
    [StrictlyHenselianLocalRing A] [CommRing A₁] [IsLocalRing A₁] [Algebra A A₁]
    [Module.Finite A A₁] [CommRing B] [Algebra A B] (h : IsShSmooth A B) :
    StrictlyHenselianLocalRing A₁ ∧ StrictlyHenselianLocalRing (A₁ ⊗[A] B) ∧
      IsLocalHom (algebraMap A₁ (A₁ ⊗[A] B)) ∧ IsShSmooth A₁ (A₁ ⊗[A] B) := by
  have : IsLocalHom (algebraMap A A₁) := by
    have : (maximalIdeal A₁).comap (algebraMap A A₁) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
    exact ((local_hom_TFAE (algebraMap A A₁)).out 1 5).2 this
  have : IsPurelyInseparable (ResidueField A) (ResidueField A₁) := inferInstance
  obtain ⟨q, _⟩ := ExpChar.exists (ResidueField A)
  obtain ⟨C, _, _, _, hC, hCl, Csh, _, _, _, _, _, hsh, ⟨e⟩⟩ :=
    isShSmooth_iff_isHenselization.mp h
  have : IsLocalHom (algebraMap C Csh) :=
    IsLocalRing.IsHenselization.isLocalHom (R := C) (L := SeparableClosure (ResidueField C))
      (Rh := Csh)
  have : IsLocalHom (algebraMap A Csh) := by
    rw [IsScalarTower.algebraMap_eq A C Csh]
    infer_instance
  -- the local rings `C₁ = A₁ ⊗[A] C` and `Csh₁ = A₁ ⊗[A] Csh`
  have : IsLocalRing (A₁ ⊗[A] C) := isLocalRing_of_isPurelyInseparable
  have : IsLocalRing (A₁ ⊗[A] Csh) := isLocalRing_of_isPurelyInseparable
  have hC₁ : IsLocalHom (algebraMap A₁ (A₁ ⊗[A] C)) :=
    isLocalHom_algebraMap_of_isPurelyInseparable
  have hsh₁ : IsLocalHom (algebraMap A₁ (A₁ ⊗[A] Csh)) :=
    isLocalHom_algebraMap_of_isPurelyInseparable
  have hCr : IsLocalHom (includeRight : C →ₐ[A] A₁ ⊗[A] C).toRingHom :=
    isLocalHom_includeRight_of_isPurelyInseparable
  have hshr : IsLocalHom (includeRight : Csh →ₐ[A] A₁ ⊗[A] Csh).toRingHom :=
    isLocalHom_includeRight_of_isPurelyInseparable
  let : Algebra (A₁ ⊗[A] C) (A₁ ⊗[A] Csh) :=
    (Algebra.TensorProduct.map (AlgHom.id A₁ A₁)
      (IsScalarTower.toAlgHom A C Csh)).toRingHom.toAlgebra
  have hmap : ∀ (a : A₁) (c : C),
      algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] Csh) (a ⊗ₜ c) = a ⊗ₜ algebraMap C Csh c := fun _ _ => rfl
  have : IsScalarTower A₁ (A₁ ⊗[A] C) (A₁ ⊗[A] Csh) := .of_algebraMap_eq fun a => by
    change a ⊗ₜ (1 : Csh) = algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] Csh) (a ⊗ₜ (1 : C))
    rw [hmap, map_one]
  -- the map `C₁ → Csh₁` is local
  have : IsLocalHom (algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] Csh)) := by
    let P := (maximalIdeal (A₁ ⊗[A] Csh)).comap (algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] Csh))
    have : P.IsPrime := Ideal.comap_isPrime _ _
    have hPT : ∀ t ∈ maximalIdeal A₁, t ⊗ₜ (1 : C) ∈ P := fun t ht => by
      change algebraMap _ _ (t ⊗ₜ (1 : C)) ∈ maximalIdeal _
      rw [hmap, map_one]
      exact fun hu => ht (isUnit_of_map_unit (algebraMap A₁ (A₁ ⊗[A] Csh)) t hu)
    have hPS : ∀ s ∈ maximalIdeal C, (1 : A₁) ⊗ₜ s ∈ P := fun s hs => by
      change algebraMap _ _ ((1 : A₁) ⊗ₜ s) ∈ maximalIdeal _
      rw [hmap]
      have h1 : algebraMap C Csh s ∈ maximalIdeal Csh := fun hu =>
        hs (isUnit_of_map_unit (algebraMap C Csh) s hu)
      exact fun hu => h1
        (isUnit_of_map_unit (includeRight : Csh →ₐ[A] A₁ ⊗[A] Csh).toRingHom _ hu)
    exact ((local_hom_TFAE _).out 1 4).2 (le_of_maximalIdeal_tmul_mem P hPT hPS _
      (Ideal.IsMaximal.ne_top inferInstance) (tmul_one_mem_of_isMaximal _)
      (one_tmul_mem_of_isMaximal _))
  -- the residue field of `Csh₁` is separably closed
  obtain ⟨eC, heC⟩ := hsh.exists_residueFieldEquiv
  have : IsSepClosed (ResidueField Csh) := IsSepClosed.of_ringEquiv eC.symm
  have : ExpChar (ResidueField Csh) q :=
    expChar_of_injective_ringHom (f := ResidueField.map (algebraMap A Csh)) (RingHom.injective _) q
  have hsc : IsSepClosed (ResidueField (A₁ ⊗[A] Csh)) := by
    let : Algebra (ResidueField Csh) (ResidueField (A₁ ⊗[A] Csh)) :=
      (ResidueField.map (includeRight : Csh →ₐ[A] A₁ ⊗[A] Csh).toRingHom).toAlgebra
    have : IsPurelyInseparable (ResidueField Csh) (ResidueField (A₁ ⊗[A] Csh)) := by
      rw [isPurelyInseparable_iff_pow_mem _ q]
      intro z
      obtain ⟨n, s, hs⟩ := exists_pow_residue_eq_residue_one_tmul q z
      exact ⟨n, residue Csh s, (ResidueField.map_residue _ s).trans hs.symm⟩
    have := IsPurelyInseparable.isAlgebraic (ResidueField Csh) (ResidueField (A₁ ⊗[A] Csh))
    exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField Csh)
  -- the residue field of `Csh₁` is separable over that of `C₁`
  have hsep : Algebra.IsSeparable (ResidueField (A₁ ⊗[A] C)) (ResidueField (A₁ ⊗[A] Csh)) := by
    let ιC := ResidueField.map (includeRight : C →ₐ[A] A₁ ⊗[A] C).toRingHom
    let ιsh := ResidueField.map (includeRight : Csh →ₐ[A] A₁ ⊗[A] Csh).toRingHom
    let θ : SeparableClosure (ResidueField C) →+* ResidueField (A₁ ⊗[A] Csh) :=
      ιsh.comp eC.toRingHom
    have hθ : θ.comp (algebraMap (ResidueField C) (SeparableClosure (ResidueField C))) =
        (algebraMap (ResidueField (A₁ ⊗[A] C)) (ResidueField (A₁ ⊗[A] Csh))).comp ιC := by
      refine RingHom.ext fun x => ?_
      obtain ⟨c, rfl⟩ := residue_surjective x
      change ιsh (eC _) = algebraMap _ _ (ιC (residue C c))
      rw [heC, ResidueField.map_residue, ResidueField.map_residue,
        ResidueField.algebraMap_residue]
      rfl
    have hmem : ∀ x : A₁ ⊗[A] Csh, residue _ x ∈
        separableClosure (ResidueField (A₁ ⊗[A] C)) (ResidueField (A₁ ⊗[A] Csh)) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        rw [map_add]
        exact add_mem hx hy
      | tmul a c =>
        have hac : a ⊗ₜ[A] c =
            algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] Csh) (a ⊗ₜ 1) * ((1 : A₁) ⊗ₜ c) := by
          rw [hmap, map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [hac, map_mul, ← ResidueField.algebraMap_residue]
        refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
        rw [mem_separableClosure_iff]
        have hz : residue _ ((1 : A₁) ⊗ₜ[A] c) = θ (eC.symm (residue Csh c)) := by
          change _ = ιsh (eC (eC.symm _))
          rw [RingEquiv.apply_symm_apply, ResidueField.map_residue]
          rfl
        rw [hz]
        set w := eC.symm (residue Csh c)
        have hw : (minpoly (ResidueField C) w).Separable :=
          Algebra.IsSeparable.isSeparable (ResidueField C) w
        have hroot : Polynomial.aeval (θ w) ((minpoly (ResidueField C) w).map ιC) = 0 := by
          rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hθ, ← Polynomial.hom_eval₂,
            ← Polynomial.aeval_def, minpoly.aeval, map_zero]
        exact hw.map.of_dvd (minpoly.dvd _ _ hroot)
    exact ⟨fun z => by
      obtain ⟨x, rfl⟩ := residue_surjective z
      exact mem_separableClosure_iff.mp (hmem x)⟩
  have : IsSepClosure (ResidueField (A₁ ⊗[A] C)) (ResidueField (A₁ ⊗[A] Csh)) := ⟨hsc, hsep⟩
  -- `Csh₁` is henselian, being finite over `Csh`
  have hhens : HenselianLocalRing (A₁ ⊗[A] Csh) := by
    let : Algebra Csh (A₁ ⊗[A] Csh) := (includeRight : Csh →ₐ[A] A₁ ⊗[A] Csh).toRingHom.toAlgebra
    have : Algebra.IsIntegral Csh (A₁ ⊗[A] Csh) :=
      algebraMap_isIntegral_iff.mp isIntegral_includeRight
    have := hsh.henselian
    exact HenselianLocalRing.of_isIntegral (A := Csh)
  -- `Csh₁` is a strict Henselization of `C₁`
  have hH : IsLocalRing.IsHenselization (A₁ ⊗[A] C) (SeparableClosure (ResidueField (A₁ ⊗[A] C)))
      (A₁ ⊗[A] Csh) :=
    ⟨hhens, StacksDraft.indEtale_tensorProduct_right A C Csh A₁ hmap
      hsh.ind_etale,
      ⟨(IsSepClosure.equiv (ResidueField (A₁ ⊗[A] C)) (SeparableClosure _)
        (ResidueField (A₁ ⊗[A] Csh))).toRingEquiv, fun x => by simp⟩⟩
  -- transport to `A₁ ⊗[A] B`
  let F : A₁ ⊗[A] B ≃ₐ[A₁] A₁ ⊗[A] Csh := Algebra.TensorProduct.congr AlgEquiv.refl e
  have : IsLocalRing (A₁ ⊗[A] B) := F.symm.toRingEquiv.isLocalRing
  have : HenselianLocalRing (A₁ ⊗[A] B) := HenselianLocalRing.of_ringEquiv F.symm.toRingEquiv
  have : IsSepClosed (ResidueField (A₁ ⊗[A] B)) :=
    IsSepClosed.of_ringEquiv (ResidueField.mapEquiv F.toRingEquiv)
  refine ⟨StrictlyHenselianLocalRing.of_module_finite A A₁,
    StrictlyHenselianLocalRing.of_isSepClosed_residueField _, ⟨fun a ha => ?_⟩,
    isShSmooth_iff_isHenselization.mpr ⟨A₁ ⊗[A] C, inferInstance, inferInstance, inferInstance,
      hC.tensorProduct, hC₁, A₁ ⊗[A] Csh, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, hH, ⟨F⟩⟩⟩
  have := ha.map F
  rw [F.commutes] at this
  exact isUnit_of_map_unit (algebraMap A₁ (A₁ ⊗[A] Csh)) a this

end Algebra.IsShSmooth
