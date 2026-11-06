module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionRationalSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ConstantSystem
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily

/-!
# The zeta function of a scheme of finite type over a finite field

Let `k` be a finite field, `ℓ` a prime and `X` a scheme of finite type over `k`. The zeta
function of `X` is the `L`-function of the constant `ℚ_ℓ`-sheaf `ℚ_{ℓ,X} = Λ_X ⊗ ℚ_ℓ`:

`Z_X(T) = L(X, ℚ_{ℓ,X}) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) | ℚ_{ℓ,x̄}) ⁻¹ ∈ ℚ_ℓ⟦T⟧`,

the product over the closed points of `X`, `deg x = [κ(x) : k]`, `π_x^*` the geometric Frobenius
acting on the stalk of the constant sheaf at a geometric point over `x`.

The constant `ℓ`-adic sheaf is `Stacks.EtaleCohomology.LAdicSheaf.constantSystem`, the strict
system `(ℤ/ℓⁿ⁺¹)_X`, and the `L`-function of a `ℚ_ℓ`-sheaf given by an `ℓ`-adic model is
`Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction`; the zeta function is the latter evaluated
at the former.

## Main definitions

* `Weil.zetaFunction`: the zeta function `Z_X(T) ∈ ℚ_ℓ⟦T⟧` of a scheme `X` of finite type over a
  finite field.

## Main results

* `Weil.constantCoeff_zetaFunction`: `Z_X(0) = 1`.
* `Weil.isUnit_zetaFunction`: `Z_X(T)` is a unit of `ℚ_ℓ⟦T⟧`.
* `Weil.coeff_zetaFunction_eq`: each coefficient of `Z_X(T)` is computed by any finite
  subproduct of the Euler product containing the closed points of small enough degree.

## Implementation notes

The scheme is an object `X` of a big étale site `B` (`X : B.Scheme`), the convention of the
`ℓ`-adic sheaves used here; for a bare scheme `X₀` one takes
`B = AlgebraicGeometry.BigEtaleSite.containing X₀`. The `ℓ`-adic model of `ℚ_{ℓ,X}` is fixed to
be `Λ_X` itself, so the independence of the `L`-series from the model is not needed to define
`Z_X`. Finite type is `LocallyOfFiniteType f` and `QuasiCompact f` for the structure morphism
`f : X ⟶ Spec k`; the noetherian, quasi-compact and quasi-separated hypotheses the constant
system needs follow from it.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1.
* [Stacks Project, Tag 03UX](https://stacks.math.columbia.edu/tag/03UX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology

universe u

namespace Weil

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

variable {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f]

omit [Fact ℓ.Prime] [Finite k] in
/-- A scheme of finite type over a finite field is noetherian. -/
theorem isNoetherian_of_finiteType {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X :=
  SmallNoetherianSeparatedEtale.isNoetherian_of_hom f

/-- The zeta function `Z_X(T) ∈ ℚ_ℓ⟦T⟧` of a scheme `X` of finite type over a finite field `k`:
the `L`-function of the constant `ℚ_ℓ`-sheaf on `X`, i.e. the Euler product
`∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) | ℚ_{ℓ,x̄}) ⁻¹` over the closed points of `X`. -/
@[weil "def_fk401_zeta_function"]
def zetaFunction : PowerSeries (Padic ℓ) :=
  haveI := isNoetherian_of_finiteType f
  LAdicSheaf.rationalLFunction B X ℓ (LAdicSheaf.constantSystem B X ℓ) f

theorem zetaFunction_def [IsNoetherian X.1] :
    zetaFunction B X ℓ f =
      LAdicSheaf.rationalLFunction B X ℓ (LAdicSheaf.constantSystem B X ℓ) f :=
  rfl

/-- The zeta function has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_zetaFunction :
    PowerSeries.constantCoeff (zetaFunction B X ℓ f) = 1 :=
  haveI := isNoetherian_of_finiteType f
  LAdicSheaf.constantCoeff_rationalLFunction B X ℓ _ f

/-- The zeta function is a unit of `ℚ_ℓ⟦T⟧`. -/
theorem isUnit_zetaFunction : IsUnit (zetaFunction B X ℓ f) :=
  haveI := isNoetherian_of_finiteType f
  LAdicSheaf.isUnit_rationalLFunction B X ℓ _ f

/-- The Euler product defining the zeta function converges: the coefficient of `T ^ j` is the
coefficient of the product of the local factors over any finite set of closed points containing
those of degree at most `j`. -/
theorem coeff_zetaFunction_eq [IsNoetherian X.1] {j : ℕ} {t : Finset (closedPoints X.1)}
    (ht : (LAdicSheaf.frobeniusMatrices B X ℓ (LAdicSheaf.constantSystem B X ℓ)
      f).eulerSystem.support j ⊆ t) :
    PowerSeries.coeff j (zetaFunction B X ℓ f) =
      PowerSeries.coeff j (∏ x ∈ t,
        (LAdicSheaf.frobeniusMatrices B X ℓ (LAdicSheaf.constantSystem B X ℓ) f).localFactor x) :=
  LAdicSheaf.coeff_rationalLFunction_eq B X ℓ _ f ht

end Weil

end
