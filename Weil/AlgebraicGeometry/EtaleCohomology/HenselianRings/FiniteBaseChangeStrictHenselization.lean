/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeLocalRings
public import Weil.Attr

/-!
# The strict local rings of a finite morphism of affine schemes

Let `R → S` be a finite ring homomorphism, `f : X = Spec S ⟶ Y = Spec R`, and `y` a geometric
point of `Y` with algebraically closed field `k`. The lifts of `y` through `f` are finitely many
geometric points `x₁, …, xₙ` of `X`. The strict local rings `Õ = Õ_{Y,y}` and `Õ_ν = Õ_{X,x_ν}`
carry evaluations `ỹ : Õ → k`, `x̃_ν : Õ_ν → k` and germ maps `R → Õ`, `S → Õ_ν` of global
functions. This file proves that

`Õ ⊗_R S ≅ ∏_ν Õ_ν`,

by an isomorphism whose `ν`-th component sends `1 ⊗ s` to the germ of `s` and is compatible with
the evaluations on `Õ ⊗ 1`.

The proof is algebraic. The ring `T = Õ ⊗_R S` is finite over the strictly henselian local ring
`Õ`, hence a finite product `∏_i B_i` of strictly henselian local rings, and its homomorphisms to
`k` over `ỹ` correspond to the factors. They also correspond to the lifts of `y`, so the lifts
index the factors. The homomorphism `T → Õ_ν` induced by the map of strict local rings
`Õ → Õ_ν` along `f` and by the germ map `S → Õ_ν` factors through the factor `B_ν` of its lift,
and `B_ν → Õ_ν` is an isomorphism: `Õ_ν` is ind-étale over the local ring `𝒪_{X, x_ν}` and
henselian, so the universal property of a henselization gives an inverse `Õ_ν → B_ν`, and the
two composites are identities by the uniqueness in the same universal property, applied over
`𝒪_{X, x_ν}` and over `𝒪_{Y, y}`.

## Main results

* `AlgebraicGeometry.exists_ringEquiv_tensorProduct_strictLocalRing_pi`: the isomorphism
  `Õ_{Y,y} ⊗_R S ≅ ∏_ν Õ_{X,x_ν}`.
* `AlgebraicGeometry.Spec.toStrictLocalRing_eq_strictLocalRingCocone_ι`: the germ map
  `R → Õ_{Y,y}` used there is the colimit map at the étale neighbourhood `(Y, y)`.
* `StrictlyHenselianLocalRing.exists_ringEquiv_tensorProduct_pi_of_indEtale`: the underlying
  statement of commutative algebra, for a strictly henselian local ring ind-étale over a
  localization of `R` and henselian local rings ind-étale over localizations of `S`.
* `StrictlyHenselianLocalRing.bijective_of_indEtale`: the identification of one factor.
* `Pi.exists_ringHom_eq_comp_evalRingHom`: a homomorphism from a finite product to a local ring
  whose residue character factors through a projection factors through that projection.

## Implementation notes

Geometric points take values in algebraically closed fields, as in
`AlgebraicGeometry.GeometricPoint`. The source works with a separably closed field `k` and assumes
that every point of `Spec (k ⊗_R S)` has residue field `k`; for `k` algebraically closed this
holds automatically, since `k ⊗_R S` is finite over `k`, so the hypothesis does not appear. The
lifts of `y` are the morphisms `Spec k ⟶ X` over `y`, regarded as geometric points of `X` by
`AlgebraicGeometry.geometricPointLift`; their finiteness is not needed for the statement.

The source takes `R → Õ` and `S → Õ_ν` to be the colimit maps at the neighbourhoods `(Y, y)` and
`(X, x_ν)`. Here they are `AlgebraicGeometry.Spec.toStrictLocalRing`, the germ in the Zariski
local ring followed by its map to the strict local ring, which is how the étale local ring is
compared with the Zariski one; `AlgebraicGeometry.Spec.toStrictLocalRing_eq_strictLocalRingCocone_ι`
identifies the two. The homomorphism `Õ → Õ_ν` used in the proof is
`AlgebraicGeometry.etaleLocalRingHom`, the map of étale local rings induced by `f` at `x_ν`.

The proof does not pass through the source's comparison map `Θ` for henselizations with respect
to a homomorphism to `k`: the factors of `Õ ⊗_R S` are compared with the strict local rings
directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK1988], I.3.2
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

public section

open IsLocalRing TensorProduct

universe u

/-- A ring homomorphism from a finite product into a local ring, whose composite with a
homomorphism to a field factors through the projection to the factor `i`, itself factors through
that projection. -/
theorem Pi.exists_ringHom_eq_comp_evalRingHom {ι : Type*} {B : ι → Type*}
    [∀ i, CommRing (B i)] {C : Type*} [CommRing C] [IsLocalRing C] {K : Type*} [Field K]
    (F : (∀ i, B i) →+* C) (χ : C →+* K) (i : ι) (z : B i →+* K)
    (h : χ.comp F = z.comp (Pi.evalRingHom B i)) :
    ∃ φ : B i →+* C, F = φ.comp (Pi.evalRingHom B i) := by
  classical
  set E : ∀ j, B j := Pi.single i 1 with hE
  have hEE : E * E = E := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [E]
    · simp [E, Pi.single_eq_of_ne hj]
  have hχu : χ (F (1 - E)) = 0 := by
    have := congrArg (fun g => g (1 - E)) h
    simp only [RingHom.comp_apply, Pi.evalRingHom_apply] at this
    rw [this]
    simp [E]
  have hnu : F (1 - E) ∈ nonunits C := fun hu => by
    have h2 := hu.map χ
    rw [hχu] at h2
    exact not_isUnit_zero h2
  have hmul : F (1 - E) * (1 - F (1 - E)) = 0 := by
    rw [← map_one F, ← map_sub, ← map_mul]
    have : (1 - E) * (1 - (1 - E)) = 0 := by
      rw [sub_sub_cancel, sub_mul, one_mul, hEE, sub_self]
    rw [this, map_zero]
  have hu0 : F (1 - E) = 0 :=
    ((isUnit_one_sub_self_of_mem_nonunits _ hnu).mul_left_eq_zero).mp hmul
  have hFE : F E = 1 := by
    have : F 1 - F E = 0 := by rw [← map_sub]; exact hu0
    rw [map_one] at this
    exact (sub_eq_zero.mp this).symm
  have hsingle : ∀ c : ∀ j, B j, c * E = Pi.single i (c i) := by
    intro c
    funext j
    by_cases hj : j = i
    · subst hj; simp [E]
    · simp [E, Pi.single_eq_of_ne hj]
  refine ⟨{ toFun := fun b => F (Pi.single i b), map_one' := hFE,
             map_mul' := fun a b => by rw [Pi.single_mul, map_mul],
             map_zero' := by simp,
             map_add' := fun a b => by rw [Pi.single_add, map_add] }, ?_⟩
  ext c
  change F c = F (Pi.single i (c i))
  rw [← hsingle, map_mul, hFE, mul_one]

section Core

variable {R S R₀ O Bi S₀ Ox : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing R₀] [Algebra R R₀] (M : Submonoid R) [IsLocalization M R₀]
  [CommRing O] [Algebra R₀ O] [Algebra R O] [IsScalarTower R R₀ O]
  [CommRing Bi] [StrictlyHenselianLocalRing Bi]
  [CommRing S₀] [IsLocalRing S₀] [Algebra S S₀] (q : Ideal S) [q.IsPrime]
  [IsLocalization.AtPrime S₀ q]
  [CommRing Ox] [HenselianLocalRing Ox] [Algebra S₀ Ox] [IsLocalHom (algebraMap S₀ Ox)]
  [Algebra.IsSeparable (ResidueField S₀) (ResidueField Ox)]

include M q in
/-- **A factor of `Õ ⊗_R S` is the strict henselization it maps to.** Let `O` be ind-étale over a
localization `R₀` of `R`, let `π : O ⊗_R S → Bi` be a surjection onto a strictly henselian local
ring, and let `Ox` be a henselian local ring, ind-étale over the localization `S₀ = S_q`, with
residue field separable over that of `S₀`. A local homomorphism `φ : Bi → Ox` which restricts on
`S` to the structure map of `Ox`, and on `O` to a homomorphism `h` compatible with the maps from
`R`, is an isomorphism. -/
theorem StrictlyHenselianLocalRing.bijective_of_indEtale
    (hO : (CommAlgCat.etale.{u} R₀).ind.{u} (CommAlgCat.of R₀ O))
    (π : O ⊗[R] S →+* Bi) (hπ : Function.Surjective π)
    (hOx : (CommAlgCat.etale.{u} S₀).ind.{u} (CommAlgCat.of S₀ Ox))
    (h : O →+* Ox)
    (hcompat : h.comp (algebraMap R O) =
      ((algebraMap S₀ Ox).comp (algebraMap S S₀)).comp (algebraMap R S))
    (φ : Bi →+* Ox) [IsLocalHom φ]
    (hφ1 : ∀ a, φ (π (a ⊗ₜ 1)) = h a)
    (hφ2 : ∀ s, φ (π (1 ⊗ₜ s)) = algebraMap S₀ Ox (algebraMap S S₀ s)) :
    Function.Bijective φ := by
  classical
  -- the localization map `S₀ → Bi`
  have hunit : ∀ s : q.primeCompl,
      IsUnit ((π.comp (Algebra.TensorProduct.includeRight : S →ₐ[R] O ⊗[R] S).toRingHom) s) := by
    intro s
    apply (isUnit_map_iff φ _).mp
    change IsUnit (φ (π (1 ⊗ₜ (s : S))))
    rw [hφ2]
    exact (IsLocalization.map_units S₀ s).map _
  let ψ : S₀ →+* Bi := IsLocalization.lift (M := q.primeCompl) hunit
  have hψ : ∀ s, ψ (algebraMap S S₀ s) = π (1 ⊗ₜ s) := fun s =>
    IsLocalization.lift_eq (M := q.primeCompl) hunit s
  have hφψ : φ.comp ψ = algebraMap S₀ Ox :=
    IsLocalization.ringHom_ext q.primeCompl (RingHom.ext fun s => by
      simp only [RingHom.comp_apply, hψ, hφ2])
  let : Algebra S₀ Bi := ψ.toAlgebra
  have hψalg : algebraMap S₀ Bi = ψ := rfl
  have : IsLocalHom (φ.comp (algebraMap S₀ Bi)) := by
    rw [hψalg, hφψ]; infer_instance
  have : IsLocalHom (algebraMap S₀ Bi) := isLocalHom_of_comp _ φ
  -- the residue field extension `κ(Bi) → κ(Ox)` is an isomorphism
  let θ : ResidueField Bi →+* ResidueField Ox := ResidueField.map φ
  let : Algebra (ResidueField Bi) (ResidueField Ox) := θ.toAlgebra
  have : IsScalarTower (ResidueField S₀) (ResidueField Bi) (ResidueField Ox) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    obtain ⟨s, rfl⟩ := residue_surjective c
    rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue]
    change _ = θ _
    rw [ResidueField.map_residue, hψalg, ← RingHom.comp_apply φ ψ, hφψ]
  have : Algebra.IsSeparable (ResidueField Bi) (ResidueField Ox) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField S₀) _ _
  have hθ : Function.Surjective θ :=
    IsSepClosed.algebraMap_surjective (ResidueField Bi) (ResidueField Ox)
  have hθres : ∀ b, θ (residue Bi b) = residue Ox (φ b) := fun b => ResidueField.map_residue φ b
  -- the inverse `g : Ox → Bi`, from the universal property of `Ox` over `S₀`
  let p : Ox →ₐ[S₀] ResidueField Ox := { toRingHom := residue Ox, commutes' := fun _ => rfl }
  let φA : Bi →ₐ[S₀] Ox :=
    { toRingHom := φ
      commutes' := fun r => by
        change φ (ψ r) = _
        rw [← RingHom.comp_apply φ ψ, hφψ] }
  let p' : Bi →ₐ[S₀] ResidueField Ox := p.comp φA
  have hp' : Function.Surjective p' := by
    intro y
    obtain ⟨c, rfl⟩ := hθ y
    obtain ⟨b, rfl⟩ := residue_surjective c
    exact ⟨b, (hθres b).symm⟩
  obtain ⟨g, hg, -⟩ := HenselianLocalRing.existsUnique_algHom_comp_of_ind_etale hOx p p' hp'
  have hφg : ∀ a, φ (g a) = a := by
    obtain ⟨g₀, -, huniq⟩ :=
      HenselianLocalRing.existsUnique_algHom_comp_of_ind_etale hOx p p residue_surjective
    have h1 : φA.comp g = g₀ := huniq _ (by
      change p.comp (φA.comp g) = p
      rw [← AlgHom.comp_assoc]; exact hg)
    have h2 : AlgHom.id S₀ Ox = g₀ := huniq _ (AlgHom.comp_id p)
    intro a
    exact congrArg (fun m : Ox →ₐ[S₀] Ox => m a) (h1.trans h2.symm)
  -- `g ∘ φ` is the identity of `Bi`
  have hgφ : ∀ b, g (φ b) = b := by
    let ν : O →+* Bi := π.comp Algebra.TensorProduct.includeLeftRingHom
    let : Algebra R₀ Bi := (ν.comp (algebraMap R₀ O)).toAlgebra
    let m1 : O →ₐ[R₀] Bi := { toRingHom := ν, commutes' := fun _ => rfl }
    have hcomm2 : ((g : Ox →+* Bi).comp h).comp (algebraMap R₀ O) = ν.comp (algebraMap R₀ O) := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun r => ?_)
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R R₀ O]
      rw [← RingHom.comp_apply h (algebraMap R O), hcompat]
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
      change ψ _ = π (algebraMap R O r ⊗ₜ 1)
      rw [hψ, Algebra.algebraMap_eq_smul_one (A := O), TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
    let m2 : O →ₐ[R₀] Bi :=
      { toRingHom := (g : Ox →+* Bi).comp h
        commutes' := fun r => congrArg (fun m : R₀ →+* Bi => m r) hcomm2 }
    let p'' : Bi →ₐ[R₀] ResidueField Bi := { toRingHom := residue Bi, commutes' := fun _ => rfl }
    obtain ⟨m₀, -, huniq⟩ := HenselianLocalRing.existsUnique_algHom_comp_of_ind_etale hO
      (p''.comp m1) p'' residue_surjective
    have hm1 : m1 = m₀ := huniq _ rfl
    have hm2 : m2 = m₀ := huniq _ (by
      ext a
      apply θ.injective
      change θ (residue Bi (g (h a))) = θ (residue Bi (π (a ⊗ₜ 1)))
      rw [hθres, hθres, hφg, hφ1])
    have hν : ∀ a, g (h a) = π (a ⊗ₜ 1) := fun a =>
      congrArg (fun m : O →ₐ[R₀] Bi => m a) (hm2.trans hm1.symm)
    have hext : ((g : Ox →+* Bi).comp φ).comp π = π := by
      refine Algebra.TensorProduct.ringHom_ext (RingHom.ext fun a => ?_) (RingHom.ext fun s => ?_)
      · change g (φ (π (a ⊗ₜ 1))) = π (a ⊗ₜ 1)
        rw [hφ1, hν]
      · change g (φ (π (1 ⊗ₜ s))) = π (1 ⊗ₜ s)
        rw [hφ2, AlgHom.commutes]
        exact hψ s
    intro b
    obtain ⟨t, rfl⟩ := hπ b
    exact congrArg (fun m : O ⊗[R] S →+* Bi => m t) hext
  exact ⟨fun b₁ b₂ hb => by rw [← hgφ b₁, hb, hgφ b₂], fun a => ⟨g a, hφg a⟩⟩

end Core

section Assembly

variable {R S R₀ O : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  [CommRing R₀] [Algebra R R₀] (M : Submonoid R) [IsLocalization M R₀]
  [CommRing O] [StrictlyHenselianLocalRing O] [Algebra R₀ O] [Algebra R O] [IsScalarTower R R₀ O]
  {k : Type u} [Field k] [IsAlgClosed k]
  {L : Type*} (S₀ : L → Type u) [∀ x, CommRing (S₀ x)] [∀ x, IsLocalRing (S₀ x)]
  [∀ x, Algebra S (S₀ x)] (q : L → Ideal S) [∀ x, (q x).IsPrime]
  [∀ x, IsLocalization.AtPrime (S₀ x) (q x)]
  (Ox : L → Type u) [∀ x, CommRing (Ox x)] [∀ x, HenselianLocalRing (Ox x)]
  [∀ x, Algebra (S₀ x) (Ox x)] [∀ x, IsLocalHom (algebraMap (S₀ x) (Ox x))]
  [∀ x, Algebra.IsSeparable (ResidueField (S₀ x)) (ResidueField (Ox x))]

include M q in
/-- **The tensor product of a strictly henselian local ring with a finite algebra, as a product
of henselizations.** Let `O` be a strictly henselian local ring, ind-étale over a localization
`R₀` of `R`, with a local homomorphism `ε : O → k` to an algebraically closed field, and let `S`
be a finite `R`-algebra. Suppose given, for each `x` in an index set `L`, a henselian local ring
`Ox x`, ind-étale over a localization `S₀ x = S_{q x}` with separable residue field extension,
with homomorphisms `h x : O → Ox x` and `εx x : Ox x → k`, compatible with the maps from `R` and
with `ε`, such that `x ↦ εx x ∘ (S → Ox x)` is a bijection from `L` onto the homomorphisms
`S → k` over `R → O → k`. Then `O ⊗_R S ≅ ∏_x Ox x`, by the homomorphisms `h x` on `O` and the
structure maps on `S`. -/
theorem StrictlyHenselianLocalRing.exists_ringEquiv_tensorProduct_pi_of_indEtale
    (hO : (CommAlgCat.etale.{u} R₀).ind.{u} (CommAlgCat.of R₀ O)) (ε : O →+* k) [IsLocalHom ε]
    (hOx : ∀ x, (CommAlgCat.etale.{u} (S₀ x)).ind.{u} (CommAlgCat.of (S₀ x) (Ox x)))
    (h : ∀ x, O →+* Ox x) (εx : ∀ x, Ox x →+* k) [∀ x, IsLocalHom (εx x)]
    (hcompat : ∀ x, (h x).comp (algebraMap R O) =
      ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))).comp (algebraMap R S))
    (heval : ∀ x, (εx x).comp (h x) = ε)
    (hinj : ∀ x x', (εx x).comp ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))) =
      (εx x').comp ((algebraMap (S₀ x') (Ox x')).comp (algebraMap S (S₀ x'))) → x = x')
    (hsurj : ∀ χ : S →+* k, χ.comp (algebraMap R S) = ε.comp (algebraMap R O) →
      ∃ x, (εx x).comp ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))) = χ) :
    ∃ Ξ : O ⊗[R] S ≃+* ∀ x, Ox x,
      (∀ x a, Ξ (a ⊗ₜ 1) x = h x a) ∧
      (∀ x s, Ξ (1 ⊗ₜ s) x = algebraMap (S₀ x) (Ox x) (algebraMap S (S₀ x) s)) := by
  classical
  obtain ⟨ι, hι, Bf, _, _, _, hfin, ⟨e⟩⟩ :=
    exists_algEquiv_pi_strictHenselian_of_module_finite O (O ⊗[R] S)
  have := hι
  have := hfin
  have : ∀ i, IsLocalHom (algebraMap O (Bf i)) := fun i =>
    isLocalHom_algebraMap_of_finite_local O (Bf i)
  -- the comparison maps `Φ x : O ⊗_R S → Ox x`
  let σ : ∀ x, S →+* Ox x := fun x => (algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))
  let Φ : ∀ x, O ⊗[R] S →+* Ox x := fun x =>
    letI : Algebra R (Ox x) := ((σ x).comp (algebraMap R S)).toAlgebra
    (Algebra.TensorProduct.lift
      ({ toRingHom := h x
         commutes' := fun r => congrArg (fun m : R →+* Ox x => m r) (hcompat x) } :
        O →ₐ[R] Ox x)
      ({ toRingHom := σ x, commutes' := fun _ => rfl } : S →ₐ[R] Ox x)
      (fun _ _ => Commute.all _ _)).toRingHom
  have hΦ1 : ∀ x a, Φ x (a ⊗ₜ 1) = h x a := fun x a => by simp [Φ]
  have hΦ2 : ∀ x s, Φ x (1 ⊗ₜ s) = σ x s := fun x s => by simp [Φ]
  have htmul : ∀ r : R, (algebraMap R O r ⊗ₜ[R] (1 : S)) = 1 ⊗ₜ algebraMap R S r := fun r => by
    rw [Algebra.algebraMap_eq_smul_one (A := O), TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one]
  -- their characters
  let es : (∀ i, Bf i) →+* O ⊗[R] S := e.symm.toRingEquiv.toRingHom
  have hes : ∀ c, e (es c) = c := fun c => e.apply_symm_apply c
  let ψ : ∀ x, (∀ i, Bf i) →+* k := fun x => ((εx x).comp (Φ x)).comp es
  have hψ : ∀ x, (ψ x).comp (algebraMap O (∀ i, Bf i)) = ε := fun x => RingHom.ext fun a => by
    change εx x (Φ x (e.symm (algebraMap O (∀ i, Bf i) a))) = ε a
    rw [AlgEquiv.commutes]
    change εx x (Φ x (a ⊗ₜ 1)) = ε a
    rw [hΦ1]
    exact RingHom.congr_fun (heval x) a
  choose zz hzz using fun x => (existsUnique_factor_ringHom_pi Bf ε (ψ x) (hψ x)).exists
  let τ : L → ι := fun x => (zz x).1
  -- `Φ x` factors through the projection to the factor `τ x`
  have hfac : ∀ x, ∃ φ : Bf (τ x) →+* Ox x,
      (Φ x).comp es = φ.comp (Pi.evalRingHom Bf (τ x)) := fun x =>
    Pi.exists_ringHom_eq_comp_evalRingHom _ (εx x) (τ x) (zz x).2 (hzz x).2
  choose φ hφ using hfac
  have hφt : ∀ x t, φ x (e t (τ x)) = Φ x t := fun x t => by
    have := RingHom.congr_fun (hφ x) (e t)
    simp only [RingHom.comp_apply, Pi.evalRingHom_apply] at this
    rw [← this]
    change Φ x (e.symm (e t)) = Φ x t
    rw [e.symm_apply_apply]
  have hεφ : ∀ x, (εx x).comp (φ x) = (zz x).2 := fun x => RingHom.ext fun b => by
    have h1 := RingHom.congr_fun (hφ x) (Pi.single (τ x) b)
    have h2 : εx x (Φ x (es (Pi.single (τ x) b))) = (zz x).2 (Pi.single (τ x) b (τ x)) :=
      RingHom.congr_fun (hzz x).2 _
    rw [Pi.single_eq_same] at h2
    simp only [RingHom.comp_apply, Pi.evalRingHom_apply, Pi.single_eq_same] at h1
    change εx x (φ x b) = _
    rw [← h1]
    exact h2
  have hφloc : ∀ x, IsLocalHom (φ x) := fun x => by
    have : IsLocalHom (zz x).2 := isLocalHom_of_ringHom_to_field_of_finite_local_algebra O
      (Bf (τ x)) k ε (zz x).2 (hzz x).1
    have : IsLocalHom ((εx x).comp (φ x)) := by rw [hεφ x]; infer_instance
    exact isLocalHom_of_comp (φ x) (εx x)
  -- each `φ x` is an isomorphism
  have hbij : ∀ x, Function.Bijective (φ x) := fun x =>
    StrictlyHenselianLocalRing.bijective_of_indEtale M (q x) hO
      ((Pi.evalRingHom Bf (τ x)).comp e.toRingEquiv.toRingHom)
      (fun b => ⟨es (Pi.single (τ x) b), by
        change e (e.symm _) (τ x) = b
        rw [e.apply_symm_apply, Pi.single_eq_same]⟩)
      (hOx x) (h x) (hcompat x) (φ x)
      (fun a => (hφt x _).trans (hΦ1 x a)) (fun s => (hφt x _).trans (hΦ2 x s))
  -- characters of a factor are unique
  have key : ∀ {i j : ι} (_ : i = j) (a : Bf i →+* k) (b : Bf j →+* k),
      a.comp (algebraMap O (Bf i)) = ε → b.comp (algebraMap O (Bf j)) = ε →
      a.comp (Pi.evalRingHom Bf i) = b.comp (Pi.evalRingHom Bf j) := by
    intro i j hij a b ha hb
    subst hij
    rw [unique_ringHom_to_algClosed_of_finite_local_algebra O (Bf i) k ε a b ha hb]
  have hψΦ : ∀ x t, ψ x (e t) = εx x (Φ x t) := fun x t => by
    change εx x (Φ x (e.symm (e t))) = _
    rw [e.symm_apply_apply]
  -- `τ` is a bijection
  have hτinj : Function.Injective τ := by
    intro x x' hxx
    have hψeq : ψ x = ψ x' := (hzz x).2.trans
      ((key hxx _ _ (hzz x).1 (hzz x').1).trans (hzz x').2.symm)
    refine hinj x x' (RingHom.ext fun s => ?_)
    have := RingHom.congr_fun hψeq (e (1 ⊗ₜ s))
    rw [hψΦ, hψΦ, hΦ2, hΦ2] at this
    exact this
  have hτsurj : Function.Surjective τ := by
    intro i
    obtain ⟨a, ha⟩ := exists_ringHom_to_algClosed_of_finite_local_algebra
      (R := O) (S := Bf i) (k := k) ε
    have hae : ∀ o, a (e (o ⊗ₜ 1) i) = ε o := fun o => by
      have : e (o ⊗ₜ[R] (1 : S)) = algebraMap O (∀ i, Bf i) o := e.commutes o
      rw [this]
      exact RingHom.congr_fun ha o
    let χ : S →+* k := ((a.comp (Pi.evalRingHom Bf i)).comp e.toRingEquiv.toRingHom).comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] O ⊗[R] S).toRingHom
    have hχ : χ.comp (algebraMap R S) = ε.comp (algebraMap R O) := RingHom.ext fun r => by
      change a (e (1 ⊗ₜ algebraMap R S r) i) = ε (algebraMap R O r)
      rw [← htmul, hae]
    obtain ⟨x, hx⟩ := hsurj χ hχ
    have hψx : ψ x = a.comp (Pi.evalRingHom Bf i) := by
      have hT : (εx x).comp (Φ x) =
          ((a.comp (Pi.evalRingHom Bf i)).comp e.toRingEquiv.toRingHom) := by
        refine Algebra.TensorProduct.ringHom_ext (RingHom.ext fun o => ?_)
          (RingHom.ext fun s => ?_)
        · change εx x (Φ x (o ⊗ₜ 1)) = a (e (o ⊗ₜ 1) i)
          rw [hΦ1, hae]
          exact RingHom.congr_fun (heval x) o
        · change εx x (Φ x (1 ⊗ₜ s)) = χ s
          rw [hΦ2, ← hx]
          rfl
      refine RingHom.ext fun c => ?_
      change εx x (Φ x (es c)) = _
      rw [← RingHom.comp_apply (εx x) (Φ x), hT]
      change a (e (e.symm c) i) = a (c i)
      rw [e.apply_symm_apply]
    have huniq := (existsUnique_factor_ringHom_pi Bf ε (ψ x) (hψ x)).unique (hzz x)
      (y₂ := ⟨i, a⟩) ⟨ha, hψx⟩
    exact ⟨x, congrArg Sigma.fst huniq⟩
  -- assembling the isomorphism
  let τe : L ≃ ι := Equiv.ofBijective τ ⟨hτinj, hτsurj⟩
  let e' : O ⊗[R] S ≃+* ∀ x, Bf (τ x) :=
    e.toRingEquiv.trans (RingEquiv.piCongrLeft Bf τe).symm
  let Ξ : O ⊗[R] S ≃+* ∀ x, Ox x :=
    e'.trans (RingEquiv.piCongrRight fun x => RingEquiv.ofBijective (φ x) (hbij x))
  have hΞ : ∀ t x, Ξ t x = Φ x t := fun t x => by
    rw [← hφt]
    rfl
  exact ⟨Ξ, fun x a => by rw [hΞ, hΦ1], fun x s => by rw [hΞ, hΦ2]; rfl⟩

end Assembly

namespace AlgebraicGeometry

open CategoryTheory

section Glue

variable {A : Type u} [CommRing A]

/-- The germ map `A = Γ(Spec A, ⊤) → 𝒪_{Spec A, p}` of global functions at a point. -/
@[expose] noncomputable def Spec.globalToStalk (p : Spec (.of A)) :
    A →+* (Spec (.of A)).presheaf.stalk p :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (Spec (.of A)).presheaf.germ ⊤ p trivial).hom

/-- The local ring of `Spec A` at `p` is the localization of `A` at `p`, through the germ map of
global functions. -/
theorem Spec.isLocalization_globalToStalk (p : PrimeSpectrum A) :
    letI := (Spec.globalToStalk p).toAlgebra
    IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk p) p.asIdeal := by
  let := (Spec.globalToStalk p).toAlgebra
  let e : Localization.AtPrime p.asIdeal ≃ₐ[A] (Spec (.of A)).presheaf.stalk p :=
    { (Spec.stalkIso (.of A) p).symm.commRingCatIsoToRingEquiv with
      commutes' := fun a => by
        have := congrArg (fun m => m.hom a) (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of A) p)
        exact this }
  exact IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl e

/-- Evaluating at the closed point of `Spec K` a germ of a global function of `Spec A` along
`z : Spec K ⟶ Spec A` is applying the ring homomorphism `A → K` of `z`. -/
theorem Spec.stalkClosedPointTo_comp_globalToStalk {K : Type u} [Field K]
    (z : Spec (.of K) ⟶ Spec (.of A)) :
    (Scheme.stalkClosedPointTo z).hom.comp (Spec.globalToStalk (z (IsLocalRing.closedPoint K))) =
      (Spec.preimage z).hom := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = z := ⟨_, Spec.map_preimage z⟩
  have := Scheme.germ_stalkClosedPointTo_Spec φ
  rw [Spec.preimage_map]
  ext a
  have h := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (.of A)).inv a)) this
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine h.trans ?_
  simp

/-- The germ maps of global functions commute with the maps of local rings induced by
`Spec A' ⟶ Spec A`. -/
theorem Spec.stalkMap_comp_globalToStalk {A' : Type u} [CommRing A'] (φ : A →+* A')
    (p : Spec (.of A')) :
    ((Spec.map (CommRingCat.ofHom φ)).stalkMap p).hom.comp
        (Spec.globalToStalk ((Spec.map (CommRingCat.ofHom φ)) p)) =
      (Spec.globalToStalk p).comp φ := by
  ext a
  have h := Scheme.Hom.germ_stalkMap (Spec.map (CommRingCat.ofHom φ)) ⊤ p trivial
  have h2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (.of A)).inv a)) h
  simp only [Spec.globalToStalk, CommRingCat.hom_comp, RingHom.comp_apply] at this ⊢
  rw [this]
  have := congrArg (fun m => m.hom a) h2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [show φ a = (CommRingCat.ofHom φ).hom a from rfl, this]
  rfl

variable (B : BigEtaleSite.{u}) (hA : B.Contains (Spec (.of A)))

/-- A transport principle: a property of a homomorphism out of the étale local ring at
`⟨k, a⟩` holds for its transport to `⟨k, b⟩` along `a = b`. -/
theorem etaleLocalRingHomCongr_induction {k : Type u} [Field k] [IsAlgClosed k]
    {a b : Spec (.of k) ⟶ Spec (.of A)} (hab : a = b) {T : Type u} [CommRing T]
    (φ : ↥(etaleLocalRing B (Spec (.of A)) hA { residueField := k, hom := a }) →+* T)
    (P : ∀ c : Spec (.of k) ⟶ Spec (.of A),
      (↥(etaleLocalRing B (Spec (.of A)) hA { residueField := k, hom := c }) →+* T) → Prop)
    (hP : P a φ) :
    P b (etaleLocalRingHomCongr B hA
      (congrArg (fun c => ({ residueField := k, hom := c } : GeometricPoint (Spec (.of A)))) hab)
      φ) := by
  subst hab
  exact hP

/-- **The map `R → Õ_{Spec R, y}`** from global functions to the strict local ring at a
geometric point: the germ of a global function in the Zariski local ring at the underlying
point, followed by the map of that local ring to the strict local ring. -/
@[expose] noncomputable def Spec.toStrictLocalRing (y : GeometricPoint (Spec (.of A))) :
    A →+* strictLocalRing B (Spec (.of A)) hA y :=
  (structureSheafStalkFromLocalRing B _ hA y).comp
    (Spec.globalToStalk (y.hom (IsLocalRing.closedPoint y.residueField)))

/-- The étale neighbourhood `(S, s)` of a geometric point `s` of `S`: the identity of `S`,
pointed by `s`. -/
@[expose] noncomputable def GeometricPoint.selfEtaleNeighborhood {X : Scheme.{u}}
    (hX : B.Contains X) (s : GeometricPoint X) : (geometricPointFiber B X hX s).Elements :=
  ⟨⟨Over.mk (𝟙 (B.obj X hX)), by change Etale (𝟙 X); infer_instance⟩,
    ⟨s.hom, Category.comp_id _⟩⟩

/-- **The germ map of global functions is the colimit map at the neighbourhood `(Spec A, y)`.**
The map `A → Õ_{Spec A, y}` through the Zariski local ring is the component, at the étale
neighbourhood `(Spec A, y)` given by the identity, of the colimit cocone presenting the strict
local ring, after `A ≅ Γ(Spec A, ⊤)`. -/
@[weil "lem_fk103_finite_strict_local_ring_tensor_decomposition"]
theorem Spec.toStrictLocalRing_eq_strictLocalRingCocone_ι (y : GeometricPoint (Spec (.of A))) :
    Spec.toStrictLocalRing B hA y =
      ((strictLocalRingCocone B _ hA y).ι.app
          (Opposite.op (GeometricPoint.selfEtaleNeighborhood B hA y))).hom.comp
        (Scheme.ΓSpecIso (.of A)).inv.hom := by
  ext a
  apply structureSheafStalkFromLocalRing_germ
  dsimp only
  change ((𝟙 (Spec (.of A)) : Spec (.of A) ⟶ Spec (.of A)).stalkMap _).hom
      (Spec.globalToStalk _ a) = (Spec (.of A)).presheaf.germ ⊤ _ trivial _
  have h := Scheme.Hom.germ_stalkMap (𝟙 (Spec (.of A))) ⊤
    (y.hom (IsLocalRing.closedPoint y.residueField)) trivial
  have := congrArg (fun m => m.hom ((Scheme.ΓSpecIso (.of A)).inv a)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp
  rfl

/-- Evaluating the image of a global function in the strict local ring at the geometric point
is applying the ring homomorphism `A → k` of the geometric point. -/
theorem Spec.toGeometricField_comp_toStrictLocalRing (y : GeometricPoint (Spec (.of A))) :
    (structureSheafStalkToGeometricField B _ hA y).comp (Spec.toStrictLocalRing B hA y) =
      (Spec.preimage y.hom).hom := by
  rw [Spec.toStrictLocalRing, ← RingHom.comp_assoc, ← CommRingCat.hom_ofHom
    ((structureSheafStalkToGeometricField B _ hA y).comp _),
    ofHom_toGeometricField_comp_fromLocalRing]
  exact Spec.stalkClosedPointTo_comp_globalToStalk y.hom

end Glue

section Main

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  (B : BigEtaleSite.{u}) (hY : B.Contains (Spec (.of R))) (hX : B.Contains (Spec (.of S)))

/-- **The strict local rings of a finite morphism of affine schemes.** Let `R → S` be finite,
`f : X = Spec S ⟶ Y = Spec R`, and `y` a geometric point of `Y` with field `k`. Let
`x₁, …, xₙ` be the lifts `Spec k ⟶ X` of `y` through `f`, `Õ = Õ_{Y,y}` and `Õ_ν = Õ_{X,x_ν}`
the strict local rings, `ỹ : Õ → k` and `x̃_ν : Õ_ν → k` the evaluations, and `R → Õ`,
`S → Õ_ν` the germ maps of global functions. Then there is a ring isomorphism
`Ξ : Õ ⊗_R S ≅ ∏_ν Õ_ν` with `Ξ_ν(1 ⊗ s)` the image of `s` in `Õ_ν` and
`x̃_ν(Ξ_ν(a ⊗ 1)) = ỹ(a)`. -/
@[weil "lem_fk103_finite_strict_local_ring_tensor_decomposition"]
theorem exists_ringEquiv_tensorProduct_strictLocalRing_pi
    (y : GeometricPoint (Spec (.of R))) :
    letI : Algebra R (strictLocalRing B (Spec (.of R)) hY y) :=
      (Spec.toStrictLocalRing B hY y).toAlgebra
    ∃ Ξ : strictLocalRing B (Spec (.of R)) hY y ⊗[R] S ≃+*
        ∀ x : {g : y.source ⟶ Spec (.of S) //
          g ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = y.hom},
          strictLocalRing B (Spec (.of S)) hX (geometricPointLift _ y x),
      (∀ x s, Ξ (1 ⊗ₜ s) x = Spec.toStrictLocalRing B hX (geometricPointLift _ y x) s) ∧
      (∀ x a, structureSheafStalkToGeometricField B _ hX (geometricPointLift _ y x)
          (Ξ (a ⊗ₜ 1) x) = structureSheafStalkToGeometricField B _ hY y a) := by
  classical
  let _ : Algebra R ↥(etaleLocalRing B _ hY y) := (Spec.toStrictLocalRing B hY y).toAlgebra
  let f : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let L := {g : y.source ⟶ Spec (.of S) // g ≫ f = y.hom}
  let xg : L → GeometricPoint (Spec (.of S)) := fun x => geometricPointLift f y x
  -- the base: `R₀ = 𝒪_{Y, y}` and `O = Õ_{Y,y}`
  let ypt : Spec (.of R) := y.hom (IsLocalRing.closedPoint y.residueField)
  let _ : Algebra R ((Spec (.of R)).presheaf.stalk ypt) := (Spec.globalToStalk ypt).toAlgebra
  have : ypt.asIdeal.IsPrime := ypt.isPrime
  have := Spec.isLocalization_globalToStalk (A := R) ypt
  have : StrictlyHenselianLocalRing ↥(etaleLocalRing B _ hY y) :=
    etaleLocalRing_strictHenselian B _ hY y
  have : IsScalarTower R ((Spec (.of R)).presheaf.stalk ypt) ↥(etaleLocalRing B _ hY y) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hO := StacksDraft.indEtale_iff.mp (indEtale_etaleLocalRing B _ hY y)
  let ε := structureSheafStalkToGeometricField B _ hY y
  have : IsLocalHom ε := structureSheafStalkToGeometricField_isLocalHom B _ hY y
  -- the factors: `S₀ x = 𝒪_{X, x}` and `Ox x = Õ_{X,x}`
  let xpt : L → Spec (.of S) := fun x => (xg x).hom (IsLocalRing.closedPoint y.residueField)
  let S₀ : L → Type u := fun x => (Spec (.of S)).presheaf.stalk (xpt x)
  let _ : ∀ x, CommRing (S₀ x) := fun x =>
    inferInstanceAs (CommRing ↥((Spec (.of S)).presheaf.stalk (xpt x)))
  have : ∀ x, IsLocalRing (S₀ x) := fun x =>
    inferInstanceAs (IsLocalRing ↥((Spec (.of S)).presheaf.stalk (xpt x)))
  let _ : ∀ x, Algebra S (S₀ x) := fun x => (Spec.globalToStalk (xpt x)).toAlgebra
  have : ∀ x, (xpt x).asIdeal.IsPrime := fun x => (xpt x).isPrime
  have : ∀ x, IsLocalization.AtPrime (S₀ x) (xpt x).asIdeal := fun x =>
    Spec.isLocalization_globalToStalk (A := S) (xpt x)
  let Ox : L → Type u := fun x => ↥(etaleLocalRing B _ hX (xg x))
  let _ : ∀ x, CommRing (Ox x) := fun x =>
    inferInstanceAs (CommRing ↥(etaleLocalRing B _ hX (xg x)))
  have : ∀ x, HenselianLocalRing (Ox x) := fun x =>
    inferInstanceAs (HenselianLocalRing ↥(etaleLocalRing B _ hX (xg x)))
  let _ : ∀ x, Algebra (S₀ x) (Ox x) := fun x => etaleLocalRingAlgebra B _ hX (xg x)
  have : ∀ x, IsLocalHom (algebraMap (S₀ x) (Ox x)) := fun x =>
    isLocalHom_algebraMap_etaleLocalRing B _ hX (xg x)
  have hOx : ∀ x, (CommAlgCat.etale.{u} (S₀ x)).ind.{u} (CommAlgCat.of (S₀ x) (Ox x)) :=
    fun x => StacksDraft.indEtale_iff.mp (indEtale_etaleLocalRing B _ hX (xg x))
  have : ∀ x, Algebra.IsSeparable (ResidueField (S₀ x)) (ResidueField (Ox x)) := fun x =>
    (isSepClosure_residueField_etaleLocalRing B _ hX (xg x)).separable
  let εx : ∀ x, Ox x →+* y.residueField := fun x =>
    structureSheafStalkToGeometricField B _ hX (xg x)
  have : ∀ x, IsLocalHom (εx x) := fun x =>
    structureSheafStalkToGeometricField_isLocalHom B _ hX (xg x)
  -- the homomorphisms `h x : Õ_{Y,y} → Õ_{X,x}`
  let h : ∀ x, ↥(etaleLocalRing B _ hY y) →+* Ox x := fun x =>
    etaleLocalRingHomCongr B hY (geometricPointLift_map f y x)
      (etaleLocalRingHom B hX hY f (xg x))
  have heval : ∀ x, (εx x).comp (h x) = ε := fun x =>
    etaleLocalRingHomCongr_induction B hY x.2 (etaleLocalRingHom B hX hY f (xg x))
      (fun c ψ => (εx x).comp ψ = structureSheafStalkToGeometricField B _ hY
        { residueField := y.residueField, hom := c })
      (toGeometricField_comp_etaleLocalRingHom B hX hY f (xg x))
  have hcompat : ∀ x, (h x).comp (algebraMap R ↥(etaleLocalRing B _ hY y)) =
      ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))).comp (algebraMap R S) := fun x =>
    etaleLocalRingHomCongr_induction B hY x.2 (etaleLocalRingHom B hX hY f (xg x))
      (fun c ψ => ψ.comp (Spec.toStrictLocalRing B hY
        { residueField := y.residueField, hom := c }) =
          ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))).comp (algebraMap R S))
      (by
        have h1 := etaleLocalRingHom_comp_fromLocalRing B hX hY f (xg x)
        have h2 := Spec.stalkMap_comp_globalToStalk (algebraMap R S) (xpt x)
        refine RingHom.ext fun r => ?_
        have e1 := RingHom.congr_fun h1 (Spec.globalToStalk (f (xpt x)) r)
        have e2 := RingHom.congr_fun h2 r
        simp only [RingHom.comp_apply] at e1 e2
        exact e1.trans (congrArg (structureSheafStalkFromLocalRing B _ hX (xg x)) e2))
  -- the characters of the lifts
  have hχ : ∀ x, (εx x).comp ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))) =
      (Spec.preimage x.1).hom := fun x =>
    Spec.toGeometricField_comp_toStrictLocalRing B hX (xg x)
  have hερ : ε.comp (algebraMap R ↥(etaleLocalRing B _ hY y)) = (Spec.preimage y.hom).hom :=
    Spec.toGeometricField_comp_toStrictLocalRing B hY y
  have hinj : ∀ x x', (εx x).comp ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))) =
      (εx x').comp ((algebraMap (S₀ x') (Ox x')).comp (algebraMap S (S₀ x'))) → x = x' := by
    intro x x' hxx
    rw [hχ, hχ] at hxx
    apply Subtype.ext
    rw [← Spec.map_preimage x.1, ← Spec.map_preimage x'.1, CommRingCat.hom_ext hxx]
  have hsurj : ∀ χ : S →+* y.residueField,
      χ.comp (algebraMap R S) = ε.comp (algebraMap R ↥(etaleLocalRing B _ hY y)) →
      ∃ x, (εx x).comp ((algebraMap (S₀ x) (Ox x)).comp (algebraMap S (S₀ x))) = χ := by
    intro χ hχR
    have hx : Spec.map (CommRingCat.ofHom χ) ≫ f = y.hom := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hχR, hερ, CommRingCat.ofHom_hom,
        Spec.map_preimage]
    refine ⟨⟨Spec.map (CommRingCat.ofHom χ), hx⟩, ?_⟩
    rw [hχ]
    simp
  obtain ⟨Ξ, h1, h2⟩ := StrictlyHenselianLocalRing.exists_ringEquiv_tensorProduct_pi_of_indEtale
    (R₀ := (Spec (.of R)).presheaf.stalk ypt) ypt.asIdeal.primeCompl S₀
    (fun x => (xpt x).asIdeal) Ox hO ε hOx h εx hcompat heval hinj hsurj
  refine ⟨Ξ, fun x s => h2 x s, fun x a => ?_⟩
  rw [h1]
  exact RingHom.congr_fun (heval x) a

end Main

end AlgebraicGeometry
