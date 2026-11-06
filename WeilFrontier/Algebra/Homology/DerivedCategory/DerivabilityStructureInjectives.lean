/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilFrontier.Defs.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Weil.Attr

/-!
# Existence of injective resolutions of bounded below complexes

Let `C` be an abelian category with enough injectives. Every cochain complex `K` whose image in
the derived category lies in `D⁺(C)` admits an injective resolution: a bounded below complex
`I` of injective objects together with a quasi-isomorphism `K ⟶ I`.

The proof: if `Hⁱ(K) = 0` for `i < n`, the canonical truncation map `K ⟶ τ_{≥ n} K` is a
quasi-isomorphism onto a complex which is strictly in degrees `≥ n`; the latter has a
quasi-isomorphism into a complex of injectives strictly in degrees `≥ n`, and the composite is
the required resolution.

## Main results

* `CochainComplex.InjectiveResolutionPlus.nonempty_of_isGE`: a complex `K` with `K.IsGE n`
  (vanishing cohomology in degrees `< n`) has an injective resolution.
* `CochainComplex.InjectiveResolutionPlus.nonempty_of_plus`: a complex whose image in
  `DerivedCategory C` lies in the bounded below subcategory has an injective resolution.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], Appendix A II.
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex.InjectiveResolutionPlus

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

/-- A cochain complex whose cohomology vanishes in degrees `< n` has an injective resolution,
whose complex of injectives is moreover strictly in degrees `≥ n`. -/
theorem exists_isStrictlyGE_of_isGE (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    ∃ R : InjectiveResolutionPlus K, R.cocomplex.IsStrictlyGE n := by
  obtain ⟨L, hL, i, hi⟩ :=
    CochainComplex.Plus.exists_quasiIso_injective ⟨K.truncGE n, ⟨n, inferInstance⟩⟩ n
  have hi' : QuasiIso i.hom := by
    change HomologicalComplex.quasiIso C _ i.hom at hi
    rwa [HomologicalComplex.mem_quasiIso_iff] at hi
  have : QuasiIso (K.πTruncGE n) := (K.quasiIso_πTruncGE_iff n).2 inferInstance
  refine ⟨{ I := L, ι := K.πTruncGE n ≫ i.hom }, ?_⟩
  change CochainComplex.IsStrictlyGE
    (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj L.obj) n
  rwa [← isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)] at hL

/-- A cochain complex whose cohomology vanishes in degrees `< n` has an injective
resolution. -/
theorem nonempty_of_isGE (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    Nonempty (InjectiveResolutionPlus K) :=
  let ⟨R, _⟩ := exists_isStrictlyGE_of_isGE K n
  ⟨R⟩

/-- Assume `C` has enough injectives. Every cochain complex `K` whose image in the derived
category lies in `D⁺(C)` has an injective resolution. -/
@[weil "lem_fka2_injective_resolution_exists"]
theorem nonempty_of_plus [HasDerivedCategory C] (K : CochainComplex C ℤ)
    (hK : (DerivedCategory.TStructure.t : Triangulated.TStructure (DerivedCategory C)).plus
      (DerivedCategory.Q.obj K)) :
    Nonempty (InjectiveResolutionPlus K) := by
  obtain ⟨n, hn⟩ := hK
  have : (DerivedCategory.Q.obj K).IsGE n := ⟨hn.1⟩
  have : K.IsGE n := (DerivedCategory.isGE_Q_obj_iff K n).1 inferInstance
  exact nonempty_of_isGE K n

end CochainComplex.InjectiveResolutionPlus
