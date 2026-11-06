/-
Copyright (c) 2026 Tony Yue YU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tony Yue YU
-/
module

public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import WeilFrontier.Defs.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Weil.Attr

/-!
# The reduction of a scheme is purely inseparable over it

For every scheme `X`, the canonical closed immersion `X_red ⟶ X` is a (finite) purely
inseparable morphism: it is finite and universally injective, being a closed immersion, and it is
surjective, since every prime ideal contains the nilradical.

## Main results

* `AlgebraicGeometry.Scheme.isPurelyInseparable_reductionι`: the closed immersion
  `X.reductionι : X.reduction ⟶ X` is purely inseparable.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §3.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- For every scheme `X`, the canonical closed immersion `X_red ⟶ X` is purely inseparable. -/
@[weil "lem_fk103_reduction_purely_inseparable"]
theorem isPurelyInseparable_reductionι : X.reductionι.IsPurelyInseparable :=
  ⟨inferInstance, inferInstance, ⟨X.surjective_reductionι⟩⟩

end AlgebraicGeometry.Scheme

end
