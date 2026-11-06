module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Weil.Attr

/-!
# Admissible projective systems of complexes

Let `Λ` be a commutative ring and `l ∈ Λ`, and write `Λ_n = Λ / l^{n+1} Λ`. A projective system
`(K_n, u_n)_{n ∈ ℤ}` of cochain complexes of `Λ`-modules, with `u_n : K_n ⟶ K_{n-1}`, is
*admissible* if

1. `K_n = 0` for `n < 0`;
2. `l^{n+1} K_n = 0` for `n ≥ 0`, so that every term `K_n^v` is a `Λ_n`-module;
3. every term `K_n^v` is a flat `Λ_n`-module;
4. there is a bound `r ≥ 0` with `K_n^v = 0` for `v > r` or `v < -r`, for all `n`;
5. every cohomology module `H^v(K_n)` is a finite `Λ`-module;
6. for every `n ≥ 0` the morphism `K_{n+1} ⊗_{Λ_{n+1}} Λ_n ⟶ K_n` induced by `u_{n+1}` is a
   quasi-isomorphism.

In the source `Λ = ℤ_l` and `l` is the prime `l`, so that `Λ_n = ℤ/l^{n+1}`.

## Main definitions

* `CochainComplex.reductionMap`: for a projective system `K` of complexes and `n ≥ 0` with
  `l^{n+1} K_n = 0`, the morphism `K_{n+1} / l^{n+1} K_{n+1} ⟶ K_n` induced by `u_{n+1}`.
* `CochainComplex.IsAdmissibleSystem l K`: the system `K` is admissible.

## Main results

* `CochainComplex.IsAdmissibleSystem.smul_id_eq_zero`: `l^{n+1}` kills `K_n` as a complex.
* `CochainComplex.IsAdmissibleSystem.isZero_X_of_lt`, `isZero_X_of_gt`: the uniform bound.
* `CochainComplex.IsAdmissibleSystem.quasiIso_reductionMap`: condition 6.

## Implementation notes

A projective system indexed by `ℤ` is a functor `ℤᵒᵖ ⥤ CochainComplex (ModuleCat Λ) ℤ`, as for
projective systems of modules (`CategoryTheory.ProjectiveSystem`); the map `u_{n+1}` is the image
of the morphism `op (n + 1) ⟶ op n`.

The source's `K_{n+1} ⊗_{Λ_{n+1}} Λ_n` is written as the cokernel, in the abelian category of
complexes, of multiplication by `l^{n+1}` on `K_{n+1}`; degreewise this is
`K_{n+1}^v / l^{n+1} K_{n+1}^v = K_{n+1}^v ⊗_{Λ_{n+1}} Λ_n`. The `Λ_n`-module structure on a term
killed by `l^{n+1}` is `Module.IsTorsionBySet.module`. The ring `Λ` is any commutative ring and
`l` any element of it; the source's case is `Λ = ℤ_[l]`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CochainComplex

variable {Λ : Type u} [CommRing Λ] (l : Λ)

/-- The morphism `op (n + 1) ⟶ op n` of `ℤᵒᵖ`, whose image under a projective system is the
transition map `u_{n+1}`. -/
abbrev succOpHom (n : ℤ) : (op (n + 1) : ℤᵒᵖ) ⟶ op n :=
  (homOfLE (Int.le_add_one le_rfl)).op

/-- If `l^{n+1}` kills every term of `K_n`, then `l^{n+1} • 𝟙 K_n = 0`. -/
lemma smul_id_eq_zero_of_isTorsionBy {K : CochainComplex (ModuleCat.{v} Λ) ℤ} (a : Λ)
    (h : ∀ v, Module.IsTorsionBy Λ (K.X v) a) : a • 𝟙 K = 0 := by
  ext v x
  exact h v (x := x)

/-- For a projective system `K` of complexes and `n` with `l^{n+1} K_n = 0`, the morphism
`K_{n+1} / l^{n+1} K_{n+1} ⟶ K_n` induced by the transition map `u_{n+1}`; the quotient is the
cokernel of multiplication by `l^{n+1}`, i.e. `K_{n+1} ⊗_{Λ_{n+1}} Λ_n`. -/
noncomputable def reductionMap (K : ℤᵒᵖ ⥤ CochainComplex (ModuleCat.{v} Λ) ℤ) (n : ℕ)
    (h : ∀ v, Module.IsTorsionBy Λ ((K.obj (op (n : ℤ))).X v) (l ^ (n + 1))) :
    cokernel (l ^ (n + 1) • 𝟙 (K.obj (op ((n : ℤ) + 1)))) ⟶ K.obj (op (n : ℤ)) :=
  cokernel.desc _ (K.map (succOpHom (n : ℤ))) <| by
    rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id (K.map _),
      ← Linear.comp_smul, smul_id_eq_zero_of_isTorsionBy _ h, comp_zero]

@[reassoc (attr := simp)]
lemma π_reductionMap (K : ℤᵒᵖ ⥤ CochainComplex (ModuleCat.{v} Λ) ℤ) (n : ℕ)
    (h : ∀ v, Module.IsTorsionBy Λ ((K.obj (op (n : ℤ))).X v) (l ^ (n + 1))) :
    cokernel.π _ ≫ reductionMap l K n h = K.map (succOpHom (n : ℤ)) :=
  cokernel.π_desc _ _ _

/-- A projective system `(K_n, u_n)_{n ∈ ℤ}` of cochain complexes of `Λ`-modules is *admissible*
(with respect to `l`) if `K_n = 0` for `n < 0`; `l^{n+1} K_n = 0` for `n ≥ 0`; every term
`K_n^v` is a flat `Λ / l^{n+1}`-module; the terms vanish outside `[-r, r]` for a bound `r`
independent of `n`; every `H^v(K_n)` is a finite `Λ`-module; and every reduction
`K_{n+1} ⊗_{Λ_{n+1}} Λ_n ⟶ K_n` of the transition maps is a quasi-isomorphism. -/
@[weil "def_fk112_admissible_complex_system"]
structure IsAdmissibleSystem (K : ℤᵒᵖ ⥤ CochainComplex (ModuleCat.{v} Λ) ℤ) : Prop where
  /-- (i) `K_n = 0` for `n < 0`. -/
  isZero_of_neg : ∀ n : ℤ, n < 0 → IsZero (K.obj (op n))
  /-- (ii) `l^{n+1} K_n = 0` for `n ≥ 0`. -/
  isTorsionBy : ∀ (n : ℕ) (v : ℤ), Module.IsTorsionBy Λ ((K.obj (op (n : ℤ))).X v) (l ^ (n + 1))
  /-- (iii) every term `K_n^v` is a flat `Λ / l^{n+1}`-module. -/
  flat : ∀ (n : ℕ) (v : ℤ),
    letI := Module.IsTorsionBySet.module
      ((Module.isTorsionBySet_span_singleton_iff (l ^ (n + 1))).2 (isTorsionBy n v))
    Module.Flat (Λ ⧸ Ideal.span {l ^ (n + 1)}) ((K.obj (op (n : ℤ))).X v)
  /-- (iv) a bound `r ≥ 0` with `K_n^v = 0` for `v > r` or `v < -r`, for all `n`. -/
  exists_bound : ∃ r : ℕ, ∀ n : ℤ,
    (K.obj (op n)).IsStrictlyLE (r : ℤ) ∧ (K.obj (op n)).IsStrictlyGE (-(r : ℤ))
  /-- (v) every `H^v(K_n)` is a finite `Λ`-module. -/
  finite_homology : ∀ n v : ℤ, Module.Finite Λ ((K.obj (op n)).homology v)
  /-- (vi) the reduction `K_{n+1} ⊗_{Λ_{n+1}} Λ_n ⟶ K_n` of `u_{n+1}` is a quasi-isomorphism. -/
  quasiIso : ∀ n : ℕ, QuasiIso (reductionMap l K n (isTorsionBy n))

namespace IsAdmissibleSystem

variable {l} {K : ℤᵒᵖ ⥤ CochainComplex (ModuleCat.{v} Λ) ℤ}

/-- `l^{n+1}` kills the complex `K_n` of an admissible system. -/
lemma smul_id_eq_zero (hK : IsAdmissibleSystem l K) (n : ℕ) :
    l ^ (n + 1) • 𝟙 (K.obj (op (n : ℤ))) = 0 :=
  smul_id_eq_zero_of_isTorsionBy _ (hK.isTorsionBy n)

lemma pow_smul_eq_zero (hK : IsAdmissibleSystem l K) (n : ℕ) (v : ℤ)
    (x : (K.obj (op (n : ℤ))).X v) : l ^ (n + 1) • x = 0 :=
  hK.isTorsionBy n v (x := x)

lemma isZero_X_of_neg (hK : IsAdmissibleSystem l K) {n : ℤ} (hn : n < 0) (v : ℤ) :
    IsZero ((K.obj (op n)).X v) :=
  (HomologicalComplex.eval _ _ v).map_isZero (hK.isZero_of_neg n hn)

/-- The terms of an admissible system vanish above a bound independent of `n`. -/
lemma isZero_X_of_gt (hK : IsAdmissibleSystem l K) :
    ∃ r : ℕ, ∀ (n v : ℤ), (r : ℤ) < v → IsZero ((K.obj (op n)).X v) := by
  obtain ⟨r, hr⟩ := hK.exists_bound
  refine ⟨r, fun n v hv => ?_⟩
  have := (hr n).1
  exact (K.obj (op n)).isZero_of_isStrictlyLE r v hv

/-- The terms of an admissible system vanish below a bound independent of `n`. -/
lemma isZero_X_of_lt (hK : IsAdmissibleSystem l K) :
    ∃ r : ℕ, ∀ (n v : ℤ), v < -(r : ℤ) → IsZero ((K.obj (op n)).X v) := by
  obtain ⟨r, hr⟩ := hK.exists_bound
  refine ⟨r, fun n v hv => ?_⟩
  have := (hr n).2
  exact (K.obj (op n)).isZero_of_isStrictlyGE (-(r : ℤ)) v hv

/-- The terms of an admissible system vanish outside `[-r, r]` for one bound `r`. -/
lemma exists_isZero_X (hK : IsAdmissibleSystem l K) :
    ∃ r : ℕ, ∀ (n v : ℤ), ((r : ℤ) < v ∨ v < -(r : ℤ)) → IsZero ((K.obj (op n)).X v) := by
  obtain ⟨r, hr⟩ := hK.exists_bound
  refine ⟨r, fun n v hv => ?_⟩
  obtain ⟨h₁, h₂⟩ := hr n
  rcases hv with hv | hv
  · exact (K.obj (op n)).isZero_of_isStrictlyLE r v hv
  · exact (K.obj (op n)).isZero_of_isStrictlyGE (-(r : ℤ)) v hv

lemma quasiIso_reductionMap (hK : IsAdmissibleSystem l K) (n : ℕ) :
    QuasiIso (reductionMap l K n (hK.isTorsionBy n)) :=
  hK.quasiIso n

end IsAdmissibleSystem

end CochainComplex
