module

public import Weil.Attr
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The trace of an endomorphism of a finitely generated `ℤ_[ℓ]`-module

Let `V` be a finitely generated `ℤ_[ℓ]`-module and `φ : V → V` a `ℤ_[ℓ]`-linear map. Then
`ℚ_[ℓ] ⊗[ℤ_[ℓ]] V` is a finite-dimensional `ℚ_[ℓ]`-vector space and `φ ⊗ ℚ_[ℓ]` is a
`ℚ_[ℓ]`-linear endomorphism of it. The trace of `φ` is the trace of `φ ⊗ ℚ_[ℓ]`, an element of
`ℚ_[ℓ]`. The trace of `φ` over `ℤ_[ℓ]` itself would be wrong for a module with torsion, so the
base change to `ℚ_[ℓ]` is essential: the torsion part of `V` dies in `ℚ_[ℓ] ⊗[ℤ_[ℓ]] V`.

## Main definitions

* `LinearMap.ladicTrace`: the trace `Tr_{ℚ_ℓ}(φ ⊗ ℚ_ℓ) ∈ ℚ_[ℓ]` of a `ℤ_[ℓ]`-linear endomorphism.

## Main results

* `LinearMap.ladicTrace_def`: the trace is `LinearMap.trace ℚ_[ℓ] _ (φ.baseChange ℚ_[ℓ])`.
* `LinearMap.ladicTrace_add`, `LinearMap.ladicTrace_smul`, `LinearMap.ladicTrace_zero`: the trace
  is `ℤ_[ℓ]`-linear in `φ`.
* `LinearMap.ladicTrace_mul_comm`: `Tr(φψ) = Tr(ψφ)`.
* `LinearMap.ladicTrace_one`: the trace of the identity is `dim_{ℚ_ℓ} (ℚ_[ℓ] ⊗ V)`.
* `LinearMap.ladicTrace_eq_algebraMap_trace`: for `V` free, the trace is the image of the trace
  of `φ` over `ℤ_[ℓ]`.

## Implementation notes

The definition is an `abbrev` for the composite `LinearMap.trace ∘ LinearMap.baseChange`, which is
the form in which traces of `ℤ_[ℓ]`-linear endomorphisms appear in the trace formulas of the
Stacks project formalisation; statements may use either form interchangeably. Finite generation
of `V` is not needed to state the definition (`LinearMap.trace` is zero on endomorphisms of
spaces without a finite basis), only for its properties.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], II.4
-/

@[expose] public section

open TensorProduct

namespace LinearMap

variable {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module ℤ_[ℓ] V]

variable (ℓ) in
/-- The trace of a `ℤ_[ℓ]`-linear endomorphism `φ` of `V`: the trace of the `ℚ_[ℓ]`-linear map
`φ ⊗ ℚ_[ℓ]` of `ℚ_[ℓ] ⊗[ℤ_[ℓ]] V`. -/
@[weil "def_fk204_trace_endomorphism_zl_module"]
noncomputable abbrev ladicTrace (φ : V →ₗ[ℤ_[ℓ]] V) : ℚ_[ℓ] :=
  LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] V) (φ.baseChange ℚ_[ℓ])

theorem ladicTrace_def (φ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ φ = LinearMap.trace ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] V) (φ.baseChange ℚ_[ℓ]) :=
  rfl

@[simp]
theorem ladicTrace_zero : ladicTrace ℓ (0 : V →ₗ[ℤ_[ℓ]] V) = 0 := by
  simp [ladicTrace_def]

@[simp]
theorem ladicTrace_add (φ ψ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ (φ + ψ) = ladicTrace ℓ φ + ladicTrace ℓ ψ := by
  simp [ladicTrace_def, baseChange_add]

@[simp]
theorem ladicTrace_neg (φ : V →ₗ[ℤ_[ℓ]] V) : ladicTrace ℓ (-φ) = -ladicTrace ℓ φ := by
  simp [ladicTrace_def, baseChange_neg]

@[simp]
theorem ladicTrace_sub (φ ψ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ (φ - ψ) = ladicTrace ℓ φ - ladicTrace ℓ ψ := by
  simp [ladicTrace_def, baseChange_sub]

@[simp]
theorem ladicTrace_smul (r : ℤ_[ℓ]) (φ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ (r • φ) = (r : ℚ_[ℓ]) * ladicTrace ℓ φ := by
  rw [ladicTrace_def, baseChange_smul, ← algebraMap_smul ℚ_[ℓ] r, map_smul, ladicTrace_def,
    smul_eq_mul]
  rfl

theorem ladicTrace_mul_comm (φ ψ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ (φ * ψ) = ladicTrace ℓ (ψ * φ) := by
  simp only [ladicTrace_def, baseChange_mul]
  exact LinearMap.trace_mul_comm _ _ _

theorem ladicTrace_comp_comm (φ ψ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ (φ ∘ₗ ψ) = ladicTrace ℓ (ψ ∘ₗ φ) :=
  ladicTrace_mul_comm φ ψ

@[simp]
theorem ladicTrace_one [Module.Finite ℤ_[ℓ] V] :
    ladicTrace ℓ (1 : V →ₗ[ℤ_[ℓ]] V) = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] V) := by
  rw [ladicTrace_def, baseChange_one, LinearMap.trace_one]

@[simp]
theorem ladicTrace_id [Module.Finite ℤ_[ℓ] V] :
    ladicTrace ℓ (LinearMap.id : V →ₗ[ℤ_[ℓ]] V) = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℤ_[ℓ]] V) :=
  ladicTrace_one

theorem ladicTrace_pow_def (φ : V →ₗ[ℤ_[ℓ]] V) (n : ℕ) :
    ladicTrace ℓ (φ ^ n) = LinearMap.trace ℚ_[ℓ] _ (φ.baseChange ℚ_[ℓ] ^ n) := by
  rw [ladicTrace_def, baseChange_pow]

/-- For a free module of finite rank, the trace of `φ ⊗ ℚ_[ℓ]` is the trace of `φ` over `ℤ_[ℓ]`,
viewed in `ℚ_[ℓ]`. -/
theorem ladicTrace_eq_algebraMap_trace [Module.Free ℤ_[ℓ] V] [Module.Finite ℤ_[ℓ] V]
    (φ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ φ = ((LinearMap.trace ℤ_[ℓ] V φ : ℤ_[ℓ]) : ℚ_[ℓ]) :=
  LinearMap.trace_baseChange φ ℚ_[ℓ]

/-- The trace of an endomorphism conjugated by a linear equivalence. -/
theorem ladicTrace_conj {W : Type*} [AddCommGroup W] [Module ℤ_[ℓ] W] [Module.Finite ℤ_[ℓ] V]
    (e : V ≃ₗ[ℤ_[ℓ]] W) (φ : V →ₗ[ℤ_[ℓ]] V) :
    ladicTrace ℓ (e.conj φ) = ladicTrace ℓ φ := by
  rw [ladicTrace_def, ladicTrace_def, ← LinearMap.trace_conj' _ (e.baseChange ℤ_[ℓ] ℚ_[ℓ] V W)]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply]

end LinearMap
