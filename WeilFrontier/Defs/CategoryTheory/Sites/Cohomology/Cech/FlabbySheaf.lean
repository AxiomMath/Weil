module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.Etale
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyCovering

/-!
# Flabby sheaves on the étale category

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes. A sheaf `F` of
abelian groups on `Et(S)` is *flabby* if for every object `U` of `Et(S)`, every étale covering
`𝔘` of `U` (a finite family of morphisms of `Et(S)` with target `U` whose images cover `U`) and
every `ν ≥ 1`, the Čech cohomology `Ȟ^ν(𝔘, F)` vanishes. This is Čech acyclicity on all
coverings; it is not the topological notion of a flasque sheaf (surjective restriction maps).

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.IsFlabby`: a presheaf on `Et(S)` with values
  in an abelian category is flabby if its positive-degree Čech cohomology on every étale
  covering of every object of `Et(S)` vanishes.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.IsFlabby.isZero_cechCohomology`: the
  vanishing of `Ȟ^ν(𝔘, F)` for a flabby `F`, an étale covering `𝔘` and `ν > 0`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.IsFlabby.of_iso`: flabbiness is invariant
  under isomorphism of presheaves.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isFlabby_of_isZero`: the zero presheaf is
  flabby.

## Implementation notes

The predicate is stated for presheaves, since the condition only involves the sections of `F`;
a sheaf `F` is flabby when its underlying presheaf is. It is stated for presheaves with values
in an arbitrary abelian category `A` with products indexed by the universe of its morphisms,
abelian groups being the case `A = AddCommGrpCat`; this also covers sheaves of `Λ`-modules.
The étale coverings are families `E : PreZeroHypercover U` indexed in that universe whose
underlying family of schemes is an étale covering (`AlgebraicGeometry.Scheme.IsEtaleCovering`);
since étale coverings are finite, every étale covering is isomorphic to one of this form, so
the choice of index universe loses nothing.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{v'} A]

/-- **Flabby sheaves.** A presheaf `F` on the étale category `Et(S)` with values in an abelian
category (for instance abelian groups) is *flabby* if for every object `U`, every étale
covering `𝔘 = (Uᵢ ⟶ U)ᵢ` of `U` and every `ν ≥ 1`, the Čech cohomology `Ȟ^ν(𝔘, F)` is zero. -/
@[weil "def_fk102_flabby_sheaf"]
def IsFlabby (F : EtalePresheaf B S hS A) : Prop :=
  ∀ ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ (E : PreZeroHypercover.{v'} U),
    Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (E.f i)) →
      ∀ ν : ℕ, 0 < ν → IsZero (cechCohomology E F ν)

variable {F G : EtalePresheaf B S hS A}

lemma isFlabby_iff :
    IsFlabby F ↔
      ∀ ⦃U : SmallNoetherianSeparatedEtale B S hS⦄ (E : PreZeroHypercover.{v'} U),
        Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (E.f i)) →
          ∀ ν : ℕ, 0 < ν → IsZero (cechCohomology E F ν) :=
  Iff.rfl

/-- The positive-degree Čech cohomology of a flabby presheaf on an étale covering vanishes. -/
lemma IsFlabby.isZero_cechCohomology (hF : IsFlabby F) {U : SmallNoetherianSeparatedEtale B S hS}
    {E : PreZeroHypercover.{v'} U}
    (hE : Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (E.f i))) {ν : ℕ} (hν : 0 < ν) :
    IsZero (cechCohomology E F ν) :=
  hF E hE ν hν

/-- Flabbiness is invariant under isomorphism of presheaves. -/
lemma IsFlabby.of_iso (e : F ≅ G) (hF : IsFlabby F) : IsFlabby G := by
  intro U E hE ν hν
  exact (hF E hE ν hν).of_iso
    ((HomologicalComplex.homologyFunctor A _ ν).mapIso
      ((Stacks.CechSite.cechComplexFunctor E).mapIso e)).symm

lemma isFlabby_congr (e : F ≅ G) : IsFlabby F ↔ IsFlabby G :=
  ⟨IsFlabby.of_iso e, IsFlabby.of_iso e.symm⟩

/-- The zero presheaf is flabby. -/
lemma isFlabby_of_isZero (hF : IsZero F) : IsFlabby F := by
  intro U E _ ν _
  refine (HomologicalComplex.ExactAt.of_isZero ?_).isZero_homology
  rw [cechComplex_X, IsZero.iff_id_eq_zero]
  exact Pi.hom_ext _ _ fun _ ↦ (hF.obj _).eq_of_tgt _ _

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
