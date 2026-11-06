module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sections killed by sheafification are locally zero

Let `P` be a presheaf of abelian groups on a site. If a section `s ∈ P(U)` maps to `0` in the
sheafification of `P`, then `s` vanishes locally: the sieve of arrows `g : V ⟶ U` with
`g^* s = 0` covers `U`. On the small étale site of a scheme `X` and for `U` quasi-compact this
gives a finite étale covering `(Uᵢ ⟶ U)ᵢ` with `s|_{Uᵢ} = 0` for every `i` [FK, I.2].

## Main results

* `CategoryTheory.Presheaf.equalizerSieve_zero_mem_of_toSheafify_app_eq_zero`: a section
  killed by `toSheafify J P` vanishes on a covering sieve.
* `AlgebraicGeometry.Scheme.exists_isEtaleCovering_map_eq_zero_of_toSheafify_app_eq_zero`:
  on the small étale site, for quasi-compact `U`, such a section vanishes on the members of a
  finite étale covering of `U`.

## Implementation notes

The sheafification is Mathlib's `CategoryTheory.toSheafify`, the unit of the sheafification
adjunction. For presheaves of abelian groups on the small étale site with values in a universe
where the plus construction is available (e.g. `AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`),
this is the plus construction applied twice; the result is stated under the hypotheses
`HasWeakSheafify` and `WEqualsLocallyBijective`, which hold in that case. The proof is
Mathlib's local injectivity of `toSheafify`,
`GrothendieckTopology.instIsLocallyInjectiveToSheafify`, together with the description of
covering sieves of quasi-compact objects by finite étale
coverings, `AlgebraicGeometry.Scheme.mem_smallEtaleTopology_iff_exists_isEtaleCovering`.

The étale site is Mathlib's `X.Etale` with `X.smallEtaleTopology`; the objects of [FK] are
noetherian, hence quasi-compact, which is the hypothesis `CompactSpace U.left`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
-/

@[expose] public section

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A section of a presheaf of abelian groups whose image in the sheafification is `0`
vanishes on a covering sieve: the sieve of arrows `g` with `g^* s = 0` covers. -/
lemma equalizerSieve_zero_mem_of_toSheafify_app_eq_zero (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    {U : Cᵒᵖ} {s : P.obj U} (hs : (toSheafify J P).app U s = 0) :
    equalizerSieve (F := P) s 0 ∈ J U.unop :=
  Presheaf.IsLocallyInjective.equalizerSieve_mem (φ := toSheafify J P) s 0
    (by rw [hs, map_zero])

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
  [X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Sections killed by sheafification are locally zero** [FK, I.2]. Let `P` be a presheaf of
abelian groups on the small étale site of `X`, `U` a quasi-compact object and `s ∈ P(U)` whose
image in the sheafification of `P` is `0`. Then there is a finite étale covering
`(ψₖ : Wₖ ⟶ U)ₖ` with `ψₖ^* s = 0` for every `k`. -/
@[weil "lem_fk102_sheafification_kernel_locally_zero"]
theorem exists_isEtaleCovering_map_eq_zero_of_toSheafify_app_eq_zero
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{w}) {U : X.Etale} [CompactSpace U.left] {s : P.obj (op U)}
    (hs : (toSheafify X.smallEtaleTopology P).app (op U) s = 0) :
    ∃ (K : Type u) (W : K → X.Etale) (ψ : ∀ k, W k ⟶ U),
      IsEtaleCovering (fun k ↦ (ψ k).left) ∧ ∀ k, P.map (ψ k).op s = 0 := by
  obtain ⟨K, W, ψ, hψ, h⟩ := (mem_smallEtaleTopology_iff_exists_isEtaleCovering _).1
    (Presheaf.equalizerSieve_zero_mem_of_toSheafify_app_eq_zero P hs)
  refine ⟨K, W, ψ, hψ, fun k ↦ ?_⟩
  have := h k
  rw [Presheaf.equalizerSieve_apply, map_zero] at this
  exact this

end AlgebraicGeometry.Scheme

end
