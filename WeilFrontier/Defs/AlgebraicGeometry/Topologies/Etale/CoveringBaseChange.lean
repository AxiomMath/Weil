module

public import WeilFrontier.Defs.AlgebraicGeometry.Sites.Etale
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtaleFibreProductInEt
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Weil.Attr

/-!
# Base change of étale coverings in `Et(S)`

Let `(ψₖ : Wₖ ⟶ U)_{k ∈ K}` be a family of morphisms of the étale category `Et(S)` of
noetherian separated étale `S`-schemes which is an étale covering of `U`, and let `g : W ⟶ U`
be a morphism of `Et(S)`. Then the fibre products `Wₖ ×_U W` are objects of `Et(S)`, the second
projections `eₖ : Wₖ ×_U W ⟶ W` are morphisms of `Et(S)`, and `(eₖ)_{k ∈ K}` is an étale
covering of `W`: given `w ∈ W`, choose `k` and `x ∈ Wₖ` with `ψₖ(x) = g(w)`; some point of
`Wₖ ×_U W` lies over `(x, w)`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isEtaleCovering_pullbackSnd`: the base change
  of an étale covering of `U` along a morphism `g : W ⟶ U` of `Et(S)` is an étale covering of `W`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Base change of étale coverings in `Et(S)`** (FK I.2). If the morphisms
`ψ k : W k ⟶ U` of `Et(S)` form an étale covering of `U` and `g : W ⟶ U` is a morphism of
`Et(S)`, then the projections `pullbackSnd (ψ k) g : W k ×_U W ⟶ W`, which are morphisms of
`Et(S)`, form an étale covering of `W`. -/
@[weil "lem_fk102_covering_base_change"]
theorem isEtaleCovering_pullbackSnd {K : Type*} {U W : SmallNoetherianSeparatedEtale B S hS}
    {Wₖ : K → SmallNoetherianSeparatedEtale B S hS} (ψ : ∀ k, Wₖ k ⟶ U)
    (hψ : Scheme.IsEtaleCovering fun k ↦ (toScheme B S hS).map (ψ k)) (g : W ⟶ U) :
    Scheme.IsEtaleCovering fun k ↦ (toScheme B S hS).map (pullbackSnd (ψ k) g) := by
  refine ⟨hψ.finite, fun k ↦ inferInstance, ?_⟩
  rw [Scheme.iUnion_range_eq_univ_iff]
  intro w
  obtain ⟨k, x, hx⟩ := hψ.exists_mem_range ((toScheme B S hS).map g w)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback x w hx
  exact ⟨k, z, by rw [toScheme_map_pullbackSnd]; exact hz⟩

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end
