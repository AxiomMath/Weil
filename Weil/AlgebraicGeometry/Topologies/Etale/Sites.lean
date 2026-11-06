module

public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Morphisms of the étale category are étale

Every morphism `h : (U, u) ⟶ (V, v)` of the étale category `Et(S)` of noetherian separated
étale `S`-schemes is an étale morphism of schemes `U ⟶ V`: since `h ≫ v = u` and both `u` and
`v` are étale, `h` is étale by cancellation of étale morphisms.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.etale_toScheme_map` — the underlying
  morphism of schemes of a morphism of `Et(S)` is étale.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms of `Et(S)` are étale.** For a morphism `h : (U, u) ⟶ (V, v)` of the étale
category, the morphism of schemes `U ⟶ V` is étale. -/
@[weil "lem_fk102_et_morphisms_are_etale"]
instance etale_toScheme_map {U V : SmallNoetherianSeparatedEtale B S hS} (h : U ⟶ V) :
    Etale ((toScheme B S hS).map h) := by
  have : Etale ((toScheme B S hS).map h ≫ structureMorphism V) := by
    rw [toScheme_map_comp_structureMorphism]; infer_instance
  exact Etale.of_comp _ (structureMorphism V)

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
