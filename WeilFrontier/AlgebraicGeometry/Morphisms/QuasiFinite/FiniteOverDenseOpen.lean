module

public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteOverDenseOpen
public import WeilFrontier.AlgebraicGeometry.Morphisms.EtaleMorphismQuasiFinite
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Étale schemes are finite over a dense open

Let `X` be a scheme. An étale morphism `f : Y ⟶ X` with noetherian source is quasi-finite, so
it becomes finite after restriction over a dense open subscheme of `X`. Finiteness is preserved
by further restriction to a smaller open, and two dense opens meet in a dense open; hence for two
objects `R`, `Y` of the étale category `Et(X)` there is one dense open `U ⊆ X` over which both
`R ×_X U ⟶ U` and `Y ×_X U ⟶ U` are finite. When `X` is irreducible a dense open is the same
as a nonempty open.

## Main results

* `AlgebraicGeometry.IsFinite.restrict_of_le`: a morphism finite over an open `U` of its target
  is finite over every smaller open.
* `AlgebraicGeometry.Etale.exists_dense_open_isFinite`: an étale morphism with noetherian
  source is finite over a dense open of its target.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.exists_nonempty_open_isFinite_restrict`: for
  `X` irreducible and `R`, `Y` in `Et(X)`, there is a nonempty (and dense) open `U ⊆ X` over
  which both structure morphisms are finite.

## Implementation notes

The fibre product `R ×_X U` with an open `U ⊆ X` is Mathlib's restriction `f ∣_ U` of the
structure morphism `f` over `U`, which is canonically the base change of `f` along the inclusion
of `U`. Instead of Zariski's main theorem and the closure argument of Freitag–Kiehl, finiteness
over a dense open of a quasi-finite morphism is [Stacks, Tag 03I1]. The conclusion is stronger
than Freitag–Kiehl's: the open is dense, and nonemptiness follows from irreducibility.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03I1](https://stacks.math.columbia.edu/tag/03I1)
-/

@[expose] public section

open TopologicalSpace CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism finite over an open `U` of its target is finite over every open `V ≤ U`. -/
theorem IsFinite.restrict_of_le {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (hU : IsFinite (f ∣_ U)) : IsFinite (f ∣_ V) := by
  have hl : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) :=
    Stacks.Morphisms.isFinite_isZariskiLocalAtTarget
  have : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    hl.toRespects
  have h₁ : IsFinite ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) :=
    IsZariskiLocalAtTarget.restrict (P := @IsFinite) hU _
  have h₂ := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h₁
  have hV : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right] using hVU
  rwa [hV] at h₂

/-- An étale morphism with noetherian source is finite over a dense open of its target. -/
theorem Etale.exists_dense_open_isFinite {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    [NoetherianSpace Y] : ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (f ∣_ U) := by
  obtain ⟨h₁, h₂, h₃⟩ := Etale.locallyOfFiniteType_and_locallyQuasiFinite_and_quasiCompact f
  exact exists_dense_open_isFinite_of_quasiFinite f

/-- Two étale morphisms with noetherian sources are both finite over one dense open of their
common target. -/
theorem Etale.exists_dense_open_isFinite_and_isFinite {X R Y : Scheme.{u}} (r : R ⟶ X)
    (f : Y ⟶ X) [Etale r] [Etale f] [NoetherianSpace R] [NoetherianSpace Y] :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (r ∣_ U) ∧ IsFinite (f ∣_ U) := by
  obtain ⟨U₁, hU₁, hr⟩ := Etale.exists_dense_open_isFinite r
  obtain ⟨U₂, hU₂, hf⟩ := Etale.exists_dense_open_isFinite f
  refine ⟨U₁ ⊓ U₂, ?_, hr.restrict_of_le r inf_le_left, hf.restrict_of_le f inf_le_right⟩
  simpa using hU₁.inter_of_isOpen_left hU₂ U₁.isOpen

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- **Objects of `Et(X)` are finite over a nonempty open.** Let `X` be irreducible and `R`, `Y`
objects of the étale category `Et(X)`. Then there is a nonempty open `U ⊆ X`, which is moreover
dense, such that `R ×_X U ⟶ U` and `Y ×_X U ⟶ U` are finite. -/
@[weil "lem_fk104_etale_equivalence_relation_finite_over_dense_open"]
theorem exists_nonempty_open_isFinite_restrict [IrreducibleSpace X]
    (R Y : SmallNoetherianSeparatedEtale B X hX) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Dense (U : Set X) ∧
      IsFinite (structureMorphism R ∣_ U) ∧ IsFinite (structureMorphism Y ∣_ U) := by
  obtain ⟨U, hU, hR, hY⟩ :=
    Etale.exists_dense_open_isFinite_and_isFinite (structureMorphism R) (structureMorphism Y)
  exact ⟨U, hU.nonempty, hU, hR, hY⟩

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
