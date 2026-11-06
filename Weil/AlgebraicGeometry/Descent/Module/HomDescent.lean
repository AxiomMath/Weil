module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Descent.Module.HomDescent
public import Weil.AlgebraicGeometry.Descent.FpqcFullyFaithful.AmitsurEqualizer

/-!
# Descent of homomorphisms of modules along a faithfully flat ring map

Let `R → B` be a faithfully flat map of commutative rings and let `M`, `N` be `R`-modules. The
sequence
`Hom_R(M, N) → Hom_B(B ⊗[R] M, B ⊗[R] N) ⇉ Hom_{B ⊗[R] B}((B ⊗[R] B) ⊗[R] M, (B ⊗[R] B) ⊗[R] N)`,
whose first map is base change `f ↦ f_B` and whose two parallel maps are the pullbacks `e₁`, `e₂`
along the two inclusions `B → B ⊗[R] B`, is exact: base change is injective, and its image is
the set of `ψ` with `e₁ ψ = e₂ ψ`.

## Main results

* `Stacks.Descent.range_baseChange_eq_setOf_homBaseChangeIncludeLeft_eq`: the image of base
  change is the equalizer of `e₁` and `e₂`.
* `Stacks.Descent.injective_baseChange_and_range_eq_setOf_homBaseChangeIncludeLeft_eq`: the
  sequence is exact.

## Implementation notes

The source writes the base ring on the right (`M ⊗ B`); following Mathlib's
`LinearMap.baseChange` it stands on the left here (`B ⊗[R] M`). The proof is the one of the
source, carried out in `Stacks.Descent.exists_baseChange_eq` and
`Stacks.Descent.baseChange_injective_of_faithfullyFlat`.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.3]
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

public section

open scoped TensorProduct

universe u v w w'

namespace Stacks.Descent

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {M : Type w} [AddCommGroup M] [Module R M] {N : Type w'} [AddCommGroup N] [Module R N]
  [Module.FaithfullyFlat R B]

variable (R B M N) in
/-- For a faithfully flat `R → B`, the `B`-linear maps `B ⊗[R] M → B ⊗[R] N` that are base
changes of `R`-linear maps `M → N` are exactly those whose two pullbacks to `B ⊗[R] B` agree. -/
theorem range_baseChange_eq_setOf_homBaseChangeIncludeLeft_eq :
    Set.range (fun f : M →ₗ[R] N => f.baseChange B) =
      {ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N | homBaseChangeIncludeLeft ψ = homBaseChangeIncludeRight ψ} := by
  ext ψ
  constructor
  · rintro ⟨f, rfl⟩
    exact homBaseChangeIncludeLeft_baseChange_eq_includeRight f
  · exact exists_baseChange_eq R B ψ

variable (R B M N) in
/-- **Descent of homomorphisms of modules along a faithfully flat ring map.** For a faithfully
flat `R → B` and `R`-modules `M`, `N`, the sequence
`Hom_R(M, N) → Hom_B(B ⊗[R] M, B ⊗[R] N) ⇉ Hom_{B ⊗[R] B}((B ⊗[R] B) ⊗[R] M, (B ⊗[R] B) ⊗[R] N)`
is exact: base change `f ↦ f_B` is injective, and its image is the set of `ψ` whose pullbacks
along the two inclusions `B → B ⊗[R] B` agree. -/
@[weil "lem_fka3_descent_hom_modules_affine"]
theorem injective_baseChange_and_range_eq_setOf_homBaseChangeIncludeLeft_eq :
    Function.Injective (fun f : M →ₗ[R] N => f.baseChange B) ∧
      Set.range (fun f : M →ₗ[R] N => f.baseChange B) =
        {ψ : B ⊗[R] M →ₗ[B] B ⊗[R] N |
          homBaseChangeIncludeLeft ψ = homBaseChangeIncludeRight ψ} :=
  ⟨baseChange_injective_of_faithfullyFlat R B,
    range_baseChange_eq_setOf_homBaseChangeIncludeLeft_eq R B M N⟩

end Stacks.Descent

end

/-! ### Descent of algebra homomorphisms along a faithfully flat ring map -/

/-!
# Descent of algebra homomorphisms along a faithfully flat ring map

Let `R → B` be a faithfully flat map of commutative rings and let `C`, `C'` be commutative
`R`-algebras. A `B`-algebra homomorphism `φ : B ⊗[R] C → B ⊗[R] C'` has two pullbacks
`e₁ φ`, `e₂ φ` to `B ⊗[R] B`, the base changes of the underlying `B`-linear map along
`b ↦ b ⊗ 1` and `b ↦ 1 ⊗ b`; they are `B ⊗[R] B`-algebra homomorphisms. The sequence
`Hom_{R-alg}(C, C') → Hom_{B-alg}(B ⊗ C, B ⊗ C') ⇉ Hom_{B⊗B-alg}((B ⊗ B) ⊗ C, (B ⊗ B) ⊗ C')`
is exact: `ψ ↦ ψ_B = id_B ⊗ ψ` is injective, and its image is the set of `φ` with
`e₁ φ = e₂ φ`.

## Main definitions

* `Stacks.Descent.algHomBaseChange`: the base change along an `R`-algebra map `i : B → T` of a
  `B`-algebra homomorphism `B ⊗[R] C → B ⊗[R] C'`, as a `T`-algebra homomorphism; its
  underlying linear map is `Stacks.Descent.homBaseChange`.
* `Stacks.Descent.algHomBaseChangeIncludeLeft`, `Stacks.Descent.algHomBaseChangeIncludeRight`:
  the pullbacks `e₁`, `e₂` as `B ⊗[R] B`-algebra homomorphisms.

## Main results

* `Stacks.Descent.map_id_injective_of_faithfullyFlat`: `ψ ↦ ψ_B` is injective.
* `Stacks.Descent.exists_map_id_eq_iff`: `φ` is of the form `ψ_B` exactly when `e₁ φ = e₂ φ`.
* `Stacks.Descent.baseChangeAlgHomEquiv`: the resulting bijection between `R`-algebra maps
  `C → C'` and `B`-algebra maps `B ⊗[R] C → B ⊗[R] C'` with `e₁ φ = e₂ φ`.

## Implementation notes

As in `Stacks.Descent.homBaseChangeIncludeLeft`, the base ring stands on the left
(`B ⊗[R] C` for the source's `C ⊗ B`), and the base change of `ψ` is
`Algebra.TensorProduct.map (AlgHom.id B B) ψ`. The descended map is the one given by descent of
module homomorphisms (`Stacks.Descent.exists_baseChange_eq`); it is multiplicative because
`c ↦ 1 ⊗ c` is injective for faithfully flat `B`.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A.3]
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open scoped TensorProduct

open Algebra.TensorProduct

namespace Stacks.Descent

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [Algebra R B]
  {C : Type*} [CommRing C] [Algebra R C] {C' : Type*} [CommRing C'] [Algebra R C']
  {T : Type*} [CommRing T] [Algebra R T]

/-- `i ⊗ id` is the underlying linear map of the algebra map `Algebra.TensorProduct.map i id`. -/
theorem rTensor_algHom_eq_map (i : B →ₐ[R] T) (x : B ⊗[R] C') :
    LinearMap.rTensor C' i.toLinearMap x = Algebra.TensorProduct.map i (AlgHom.id R C') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp
  | add x y hx hy => simp [hx, hy]

/-- The base change of a `B`-algebra homomorphism along an `R`-algebra map `i : B → T` is
multiplicative. -/
theorem homBaseChange_map_mul (i : B →ₐ[R] T) (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C')
    (x y : T ⊗[R] C) :
    homBaseChange R B i φ.toLinearMap (x * y) =
      homBaseChange R B i φ.toLinearMap x * homBaseChange R B i φ.toLinearMap y := by
  refine LinearMap.map_mul_of_map_mul_tmul (fun t₁ t₂ c₁ c₂ => ?_) x y
  simp only [homBaseChange_tmul, AlgHom.toLinearMap_apply]
  rw [show (1 : B) ⊗ₜ[R] (c₁ * c₂) = (1 ⊗ₜ c₁) * (1 ⊗ₜ c₂) by simp, map_mul,
    rTensor_algHom_eq_map, rTensor_algHom_eq_map, rTensor_algHom_eq_map, map_mul,
    smul_mul_smul_comm]

/-- The base change of a `B`-algebra homomorphism along an `R`-algebra map `i : B → T` is
unital. -/
theorem homBaseChange_map_one (i : B →ₐ[R] T) (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    homBaseChange R B i φ.toLinearMap 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, homBaseChange_tmul, one_smul, AlgHom.toLinearMap_apply,
    ← Algebra.TensorProduct.one_def, map_one, rTensor_algHom_eq_map, map_one]

/-- The base change along an `R`-algebra map `i : B → T` of a `B`-algebra homomorphism
`φ : B ⊗[R] C → B ⊗[R] C'`: the `T`-algebra homomorphism `T ⊗[R] C → T ⊗[R] C'` whose underlying
linear map is `Stacks.Descent.homBaseChange R B i φ`. -/
noncomputable def algHomBaseChange (i : B →ₐ[R] T) (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    T ⊗[R] C →ₐ[T] T ⊗[R] C' :=
  AlgHom.ofLinearMap (homBaseChange R B i φ.toLinearMap) (homBaseChange_map_one R B i φ)
    (homBaseChange_map_mul R B i φ)

@[simp]
theorem toLinearMap_algHomBaseChange (i : B →ₐ[R] T) (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    (algHomBaseChange R B i φ).toLinearMap = homBaseChange R B i φ.toLinearMap :=
  rfl

theorem algHomBaseChange_apply (i : B →ₐ[R] T) (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C')
    (x : T ⊗[R] C) : algHomBaseChange R B i φ x = homBaseChange R B i φ.toLinearMap x :=
  rfl

/-- Two algebra base changes of `φ` agree exactly when the underlying module base changes do. -/
theorem algHomBaseChange_eq_iff (i i' : B →ₐ[R] T) (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    algHomBaseChange R B i φ = algHomBaseChange R B i' φ ↔
      homBaseChange R B i φ.toLinearMap = homBaseChange R B i' φ.toLinearMap := by
  rw [← toLinearMap_algHomBaseChange, ← toLinearMap_algHomBaseChange]
  exact AlgHom.toLinearMap_injective.eq_iff.symm

variable {R B}

/-- The underlying linear map of the base change `ψ_B = id_B ⊗ ψ` of an `R`-algebra map is the
base change of the underlying linear map. -/
theorem toLinearMap_map_id (ψ : C →ₐ[R] C') :
    (Algebra.TensorProduct.map (AlgHom.id B B) ψ).toLinearMap = ψ.toLinearMap.baseChange B := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

/-- The algebra base change of `ψ_B` along `i` is `ψ_T`. -/
theorem algHomBaseChange_map_id (i : B →ₐ[R] T) (ψ : C →ₐ[R] C') :
    algHomBaseChange R B i (Algebra.TensorProduct.map (AlgHom.id B B) ψ) =
      Algebra.TensorProduct.map (AlgHom.id T T) ψ := by
  apply AlgHom.toLinearMap_injective
  rw [toLinearMap_algHomBaseChange, toLinearMap_map_id, toLinearMap_map_id,
    homBaseChange_baseChange]

variable (R B) in
/-- The pullback `e₁ φ` of a `B`-algebra homomorphism `φ : B ⊗[R] C → B ⊗[R] C'` along
`b ↦ b ⊗ 1`, as a `B ⊗[R] B`-algebra homomorphism. -/
@[weil "lem_fka3_descent_algebra_homs"]
noncomputable abbrev algHomBaseChangeIncludeLeft (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    (B ⊗[R] B) ⊗[R] C →ₐ[B ⊗[R] B] (B ⊗[R] B) ⊗[R] C' :=
  algHomBaseChange R B (includeLeft : B →ₐ[R] B ⊗[R] B) φ

variable (R B) in
/-- The pullback `e₂ φ` of a `B`-algebra homomorphism `φ : B ⊗[R] C → B ⊗[R] C'` along
`b ↦ 1 ⊗ b`, as a `B ⊗[R] B`-algebra homomorphism. -/
@[weil "lem_fka3_descent_algebra_homs"]
noncomputable abbrev algHomBaseChangeIncludeRight (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    (B ⊗[R] B) ⊗[R] C →ₐ[B ⊗[R] B] (B ⊗[R] B) ⊗[R] C' :=
  algHomBaseChange R B (includeRight : B →ₐ[R] B ⊗[R] B) φ

/-- The algebra pullback `e₁ φ` has the module pullback `e₁` of `φ` as underlying linear map. -/
theorem toLinearMap_algHomBaseChangeIncludeLeft (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    (algHomBaseChangeIncludeLeft R B φ).toLinearMap = homBaseChangeIncludeLeft φ.toLinearMap :=
  rfl

/-- The algebra pullback `e₂ φ` has the module pullback `e₂` of `φ` as underlying linear map. -/
theorem toLinearMap_algHomBaseChangeIncludeRight (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    (algHomBaseChangeIncludeRight R B φ).toLinearMap = homBaseChangeIncludeRight φ.toLinearMap :=
  rfl

/-- The two algebra pullbacks of `φ` agree exactly when its two module pullbacks do. -/
theorem algHomBaseChangeIncludeLeft_eq_includeRight_iff (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    algHomBaseChangeIncludeLeft R B φ = algHomBaseChangeIncludeRight R B φ ↔
      homBaseChangeIncludeLeft φ.toLinearMap = homBaseChangeIncludeRight φ.toLinearMap :=
  algHomBaseChange_eq_iff R B _ _ φ

/-- The two pullbacks agree on a base change `ψ_B`. -/
theorem algHomBaseChangeIncludeLeft_map_id_eq_includeRight (ψ : C →ₐ[R] C') :
    algHomBaseChangeIncludeLeft R B (Algebra.TensorProduct.map (AlgHom.id B B) ψ) =
      algHomBaseChangeIncludeRight R B (Algebra.TensorProduct.map (AlgHom.id B B) ψ) := by
  simp only [algHomBaseChangeIncludeLeft, algHomBaseChangeIncludeRight, algHomBaseChange_map_id]

variable [Module.FaithfullyFlat R B]

variable (B C C') in
/-- **Descent of algebra homomorphisms, faithfulness.** For a faithfully flat `R → B`, the base
change `ψ ↦ ψ_B` of `R`-algebra homomorphisms `C → C'` is injective. -/
@[weil "lem_fka3_descent_algebra_homs"]
theorem map_id_injective_of_faithfullyFlat :
    Function.Injective
      (fun ψ : C →ₐ[R] C' => Algebra.TensorProduct.map (AlgHom.id B B) ψ) := by
  intro ψ ψ' h
  apply AlgHom.toLinearMap_injective
  apply baseChange_injective_of_faithfullyFlat R B
  simp only [← toLinearMap_map_id]
  exact congrArg AlgHom.toLinearMap h

/-- **Descent of algebra homomorphisms, fullness.** For a faithfully flat `R → B`, a `B`-algebra
homomorphism `φ : B ⊗[R] C → B ⊗[R] C'` is the base change `ψ_B` of an `R`-algebra
homomorphism `ψ : C → C'` if and only if its two pullbacks `e₁ φ`, `e₂ φ` to `B ⊗[R] B` agree. -/
@[weil "lem_fka3_descent_algebra_homs"]
theorem exists_map_id_eq_iff (φ : B ⊗[R] C →ₐ[B] B ⊗[R] C') :
    (∃ ψ : C →ₐ[R] C', Algebra.TensorProduct.map (AlgHom.id B B) ψ = φ) ↔
      algHomBaseChangeIncludeLeft R B φ = algHomBaseChangeIncludeRight R B φ := by
  constructor
  · rintro ⟨ψ, rfl⟩
    exact algHomBaseChangeIncludeLeft_map_id_eq_includeRight ψ
  · intro h
    obtain ⟨f, hf⟩ := exists_baseChange_eq R B φ.toLinearMap
      ((algHomBaseChangeIncludeLeft_eq_includeRight_iff φ).mp h)
    have key : ∀ c : C, (1 : B) ⊗ₜ[R] f c = φ (1 ⊗ₜ c) := fun c => by
      rw [← AlgHom.toLinearMap_apply, ← hf]
      simp
    have inj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := B) C'
    have hone : f 1 = 1 := inj <| by
      change (1 : B) ⊗ₜ[R] f 1 = (1 : B) ⊗ₜ[R] 1
      rw [key, ← Algebra.TensorProduct.one_def, map_one, Algebra.TensorProduct.one_def]
    have hmul : ∀ x y : C, f (x * y) = f x * f y := fun x y => inj <| by
      change (1 : B) ⊗ₜ[R] f (x * y) = (1 : B) ⊗ₜ[R] (f x * f y)
      rw [key, show (1 : B) ⊗ₜ[R] (x * y) = (1 ⊗ₜ x) * (1 ⊗ₜ y) by simp, map_mul, ← key, ← key,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine ⟨AlgHom.ofLinearMap f hone hmul, AlgHom.toLinearMap_injective ?_⟩
    rw [toLinearMap_map_id, ← hf]
    rfl

/-- **Descent of algebra homomorphisms along a faithfully flat ring map**, as a bijection:
`R`-algebra maps `C → C'` are exactly the `B`-algebra maps `B ⊗[R] C → B ⊗[R] C'` whose two
pullbacks to `B ⊗[R] B` agree. -/
noncomputable def baseChangeAlgHomEquiv :
    (C →ₐ[R] C') ≃
      {φ : B ⊗[R] C →ₐ[B] B ⊗[R] C' //
        algHomBaseChangeIncludeLeft R B φ = algHomBaseChangeIncludeRight R B φ} :=
  Equiv.ofBijective
    (fun ψ => ⟨Algebra.TensorProduct.map (AlgHom.id B B) ψ,
      algHomBaseChangeIncludeLeft_map_id_eq_includeRight ψ⟩)
    ⟨fun _ _ h => map_id_injective_of_faithfullyFlat B C C' (Subtype.ext_iff.mp h),
     fun φ => ((exists_map_id_eq_iff φ.1).mpr φ.2).imp fun _ hψ => Subtype.ext hψ⟩

@[simp]
theorem baseChangeAlgHomEquiv_apply_coe (ψ : C →ₐ[R] C') :
    (baseChangeAlgHomEquiv (B := B) ψ : B ⊗[R] C →ₐ[B] B ⊗[R] C') =
      Algebra.TensorProduct.map (AlgHom.id B B) ψ :=
  rfl

end Stacks.Descent

end
