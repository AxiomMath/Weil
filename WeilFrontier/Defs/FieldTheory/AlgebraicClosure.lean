module

public import Weil.Attr
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Function fields in one variable

Let `k` be a field. A *function field in one variable over the constant field `k`* is a field
extension `K / k` which is finitely generated, of transcendence degree one, and in which `k` is
algebraically closed: every element of `K` algebraic over `k` already lies in `k`.

## Main definitions

- `IsFunctionFieldOneVariable k K`: `K` is a function field in one variable over the constant
  field `k`.

## Main results

- `IsFunctionFieldOneVariable.iff`: the three defining conditions, with the constant-field
  condition stated as `algebraicClosure k K = ⊥`.
- `IsFunctionFieldOneVariable.algebraicClosure_eq_bot`,
  `IsFunctionFieldOneVariable.integralClosure_eq_bot`: `k` is its own algebraic closure in `K`.
- `IsFunctionFieldOneVariable.isIntegrallyClosedIn`: `k` is integrally closed in `K`.
- `IsFunctionFieldOneVariable.transcendental`: `K` is transcendental over `k`.
- `IsFunctionFieldOneVariable.of_isAlgClosed`: over an algebraically closed field `k`, a finitely
  generated extension of transcendence degree one is a function field in one variable over `k`
  (the constant-field condition is automatic).

## Implementation notes

Finite generation of `K` as a field extension of `k` is expressed by Mathlib's
`Algebra.EssFiniteType k K`, which for fields is equivalent to `(⊤ : IntermediateField k K).FG`
(`IntermediateField.fg_top_iff`); this is the convention of Mathlib and of the transcendence
degree one results the consumers use (Tsen's theorem). The class extends
`Algebra.EssFiniteType k K`, so that instance is available from a function field hypothesis.

This is not Mathlib's `FunctionField`, which is a finite extension of a rational function field
`RatFunc F` and imposes no condition on the constants.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public section

universe u v

/-- `K` is a *function field in one variable over the constant field `k`*: the field extension
`K / k` is finitely generated (`Algebra.EssFiniteType k K`), of transcendence degree one, and every
element of `K` algebraic over `k` lies in (the image of) `k`. -/
@[weil "def_fk101_function_field_one_variable"]
class IsFunctionFieldOneVariable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] : Prop
    extends Algebra.EssFiniteType k K where
  /-- `K` has transcendence degree one over `k`. -/
  trdeg_eq_one : Algebra.trdeg k K = 1
  /-- `k` is algebraically closed in `K`. -/
  mem_range_of_isAlgebraic : ∀ x : K, IsAlgebraic k x → x ∈ (algebraMap k K).range

namespace IsFunctionFieldOneVariable

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- In a function field in one variable, the algebraic closure of `k` in `K` is `k`. -/
theorem algebraicClosure_eq_bot [IsFunctionFieldOneVariable k K] :
    algebraicClosure k K = ⊥ := by
  refine bot_unique fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := mem_range_of_isAlgebraic x (mem_algebraicClosure_iff.mp hx)
  exact IntermediateField.algebraMap_mem _ y

/-- A field extension is a function field in one variable iff it is finitely generated, of
transcendence degree one, and the algebraic closure of `k` in `K` is `k`. -/
theorem iff :
    IsFunctionFieldOneVariable k K ↔ Algebra.EssFiniteType k K ∧ Algebra.trdeg k K = 1 ∧
      algebraicClosure k K = ⊥ := by
  refine ⟨fun h ↦ ⟨h.toEssFiniteType, h.trdeg_eq_one, algebraicClosure_eq_bot⟩, ?_⟩
  rintro ⟨hfg, htr, hbot⟩
  refine { toEssFiniteType := hfg, trdeg_eq_one := htr, mem_range_of_isAlgebraic := ?_ }
  intro x hx
  have : x ∈ (⊥ : IntermediateField k K) := hbot ▸ mem_algebraicClosure_iff.mpr hx
  exact IntermediateField.mem_bot.mp this

/-- In a function field in one variable, the integral closure of `k` in `K` is `k`. -/
theorem integralClosure_eq_bot [IsFunctionFieldOneVariable k K] :
    integralClosure k K = ⊥ := by
  rw [← algebraicClosure_toSubalgebra, algebraicClosure_eq_bot, IntermediateField.bot_toSubalgebra]

/-- In a function field in one variable, `k` is integrally closed in `K`. -/
theorem isIntegrallyClosedIn [IsFunctionFieldOneVariable k K] : IsIntegrallyClosedIn k K := by
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k K).injective, fun {x} hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := mem_range_of_isAlgebraic x hx.isAlgebraic
  exact ⟨y, hy⟩

/-- A function field in one variable is transcendental over its constant field. -/
theorem transcendental [IsFunctionFieldOneVariable k K] : Algebra.Transcendental k K :=
  trdeg_ne_zero_iff.mp (by simp [trdeg_eq_one (k := k) (K := K)])

/-- Over an algebraically closed field `k`, every finitely generated extension `K / k` of
transcendence degree one is a function field in one variable over `k`: the constant-field
condition holds automatically. -/
theorem of_isAlgClosed [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (h : Algebra.trdeg k K = 1) : IsFunctionFieldOneVariable k K :=
  iff.mpr ⟨inferInstance, h, IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩

/-- Over an algebraically closed field `k`, a field extension `K / k` is a function field in one
variable iff it is finitely generated of transcendence degree one. -/
theorem iff_of_isAlgClosed [IsAlgClosed k] :
    IsFunctionFieldOneVariable k K ↔ Algebra.EssFiniteType k K ∧ Algebra.trdeg k K = 1 :=
  ⟨fun h ↦ ⟨h.toEssFiniteType, h.trdeg_eq_one⟩, fun ⟨_, h⟩ ↦ of_isAlgClosed h⟩

end IsFunctionFieldOneVariable

end
