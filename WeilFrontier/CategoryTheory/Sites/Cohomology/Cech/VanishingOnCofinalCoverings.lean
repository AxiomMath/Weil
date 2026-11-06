module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.Cech
public import WeilFrontier.CategoryTheory.Sites.RestrictionIsSheaf
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Cech.FlabbySheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject

/-!
# Flabby sheaves on the étale category are acyclic

Let `Et(S)` be the étale category of noetherian separated étale `S`-schemes and `F` a flabby
abelian sheaf on `Et(S)`, i.e. one whose positive-degree Čech cohomology vanishes on every étale
covering of every object. For `U ∈ Et(S)` the cohomology `H^ν(U, F|_U)` of the restriction of
`F` to `Et(U)` vanishes for every `ν ≥ 1`.

The proof is Cartan's criterion in the form of Stacks 03F9, applied on `Et(U)` to the class of
all objects and the étale coverings: these are cofinal among covering sieves, because the
objects of `Et(U)` are quasi-compact, and their fibre products stay in `Et(U)`. Flabbiness of
`F|_U` follows from that of `F`, since a covering in `Et(U)` is a covering in `Et(S)` with the
same fibre products, hence the same Čech complex. Finally `Et(U)` has the terminal object
`(U, id)`, over which cohomology is global cohomology.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.finalIsTerminal`: the final object `(S, id)`
  of `Et(S)` (`AlgebraicGeometry.SmallNoetherianSeparatedEtale.final`), for a noetherian
  separated scheme `S`, is terminal.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.IsFlabby.restrict`: the restriction `F|_U`
  of a flabby presheaf is flabby.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.IsFlabby.isZero_H'`: for `S` locally
  noetherian, `H^ν(V, F) = 0` for a flabby abelian sheaf `F` on `Et(S)`, every `V ∈ Et(S)` and
  `ν ≥ 1`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.IsFlabby.subsingleton_H_restrict`:
  `H^ν(U, F|_U) = 0` for a flabby abelian sheaf `F` on `Et(S)`, `U ∈ Et(S)` and `ν ≥ 1`.

## Implementation notes

Cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf
`ℤ`, on the site `Et(U)` with its topology restricted from the small étale site; the `HasExt`
instance is a hypothesis, following Mathlib's policy. The source deduces the vanishing from
Cartan's lemma, i.e. an isomorphism between Čech and derived-functor cohomology; Stacks 03F9
gives the vanishing directly from the vanishing of Čech cohomology on a cofinal system of
coverings, which is all that is used here. No hypothesis on `S` is needed for the main result,
since the criterion is applied on `Et(U)` and `U` is noetherian.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v' u' u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Final

variable (B S hS) [IsNoetherian S] [S.IsSeparated]

/-- `(S, id)` is a terminal object of `Et(S)`. -/
noncomputable def finalIsTerminal : IsTerminal (final B S hS) :=
  IsTerminal.ofUniqueHom
    (fun V ↦ (homEquiv V (final B S hS)).symm ⟨structureMorphism V, by
      change structureMorphism V ≫ 𝟙 S = _
      exact Category.comp_id _⟩)
    (fun V g ↦ (homEquiv V (final B S hS)).injective (Subtype.ext (by
      have := toScheme_map_comp_structureMorphism g
      exact (Category.comp_id _).symm.trans this)))

end Final

section Abelian

variable (B S hS)

/-- Sheafification of abelian presheaves on `Et(S)` exists: `Et(S)` is essentially small. -/
instance hasSheafify : HasSheafify (topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Abelian sheaves on `Et(S)` form an abelian category. -/
noncomputable instance abelian_sheaf : Abelian (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  sheafIsAbelian

/-- Abelian sheaves on `Et(S)` form a Grothendieck abelian category: `Et(S)` is essentially
small. -/
instance isGrothendieckAbelian_sheaf :
    IsGrothendieckAbelian.{u} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

instance wEqualsLocallyBijective : (topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

end Abelian

section Postcompose

variable (U : SmallNoetherianSeparatedEtale B S hS)

/-- The functor `Et(U) ⥤ Et(S)` preserves connected limits, in particular finite wide
pullbacks: it is the equivalence `Et(U) ≌ Et(S)/U` followed by the forgetful functor. -/
instance preservesLimitsOfShape_postcompose (J : Type) [SmallCategory J] [IsConnected J] :
    PreservesLimitsOfShape J (postcompose U) := by
  rw [← toOver'_comp_forget]
  infer_instance

end Postcompose

section Flabby

variable {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{v'} A]

/-- **The restriction of a flabby presheaf is flabby.** For `U ∈ Et(S)`, a covering of an
object of `Et(U)` is also a covering in `Et(S)`, with the same fibre products, so the Čech
complexes of `F|_U` on `Et(U)` are Čech complexes of `F` on `Et(S)`. -/
theorem IsFlabby.restrict {F : EtalePresheaf B S hS A} (hF : IsFlabby F)
    (U : SmallNoetherianSeparatedEtale B S hS) : IsFlabby (EtalePresheaf.restrict F U) := by
  intro V E hE ν hν
  exact Stacks.CechSite.cechCohomology_isZero_of_isZero_of_functor (postcompose U) E F
    (fun n i ↦ Stacks.CechSite.isIso_cechProductMapOfFunctor _ _ n i) ν
    (hF (E.map (postcompose U)) hE ν hν)

end Flabby

section Vanishing

variable [IsLocallyNoetherian S]

/-- Every covering sieve of an object `U` of `Et(S)` contains the sieve generated by an étale
covering of `U`, indexed in the universe of the schemes. -/
theorem exists_isEtaleCovering_sieve₀_le {U : SmallNoetherianSeparatedEtale B S hS}
    (R : Sieve U) (hR : R ∈ topology B S hS U) :
    ∃ E : PreZeroHypercover.{u} U,
      Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (E.f i)) ∧
        E.sieve₀ ∈ topology B S hS U ∧ E.sieve₀ ≤ R := by
  obtain ⟨P, ⟨ι, _, V, φ, rfl, hφ⟩, hle⟩ := exists_finite_subfamily B S hS R hR
  refine ⟨⟨ι, V, φ⟩, ⟨inferInstance, fun _ ↦ inferInstance, hφ⟩, ?_, ?_⟩
  · rw [mem_topology_iff]
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hφ ▸ Set.mem_univ x)
    exact ⟨V i, φ i, Sieve.ofArrows_mk _ _ i, hi⟩
  · exact Sieve.generate_le_iff _ _ |>.mpr hle

/-- **Flabby sheaves are acyclic.** For a locally noetherian scheme `S` and a flabby abelian
sheaf `F` on `Et(S)`, the cohomology `H^ν(V, F)` vanishes for every `V ∈ Et(S)` and `ν ≥ 1`. -/
theorem IsFlabby.isZero_H' [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})]
    {F : Sheaf (topology B S hS) AddCommGrpCat.{u}} (hF : IsFlabby F.obj)
    (V : SmallNoetherianSeparatedEtale B S hS) {ν : ℕ} (hν : 0 < ν) : IsZero (F.H' ν V) :=
  Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives
    (topology B S hS) Set.univ
    (fun U ↦ {E | Scheme.IsEtaleCovering (fun i ↦ (toScheme B S hS).map (E.1.f i))})
    (fun _ _ _ _ ↦ inferInstance)
    (fun _ _ ↦ ⟨trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩)
    (fun U _ R hR ↦ by
      obtain ⟨E, hE, hE', hle⟩ := exists_isEtaleCovering_sieve₀_le R hR
      exact ⟨⟨E, hE'⟩, hE, hle⟩)
    F (fun E hE p hp ↦ hF E.1 hE p hp) V trivial ν hν

end Vanishing

/-- **The cohomology of a flabby sheaf vanishes in positive degrees.** Let `F` be a flabby
abelian sheaf on `Et(S)` and `U ∈ Et(S)`. Then `H^ν(U, F|_U) = 0` for every `ν ≥ 1`, where
`F|_U` is the restriction of `F` to `Et(U)`. -/
@[weil "lem_fk102_flabby_cohomology_vanishes"]
theorem IsFlabby.subsingleton_H_restrict {F : EtaleSheaf B S hS AddCommGrpCat.{u}}
    (hF : IsFlabby F.obj) (U : SmallNoetherianSeparatedEtale B S hS)
    [HasExt.{w} (Sheaf (topology B U.obj.obj.left.1 U.obj.obj.left.property) AddCommGrpCat.{u})]
    {ν : ℕ} (hν : 0 < ν) : Subsingleton (Sheaf.H.{w} (EtaleSheaf.restrict F U) ν) := by
  have : IsNoetherian U.obj.obj.left.1 := inferInstanceAs (IsNoetherian ((toScheme B S hS).obj U))
  have : U.obj.obj.left.1.IsSeparated := inferInstanceAs ((toScheme B S hS).obj U).IsSeparated
  have h := (hF.restrict U).isZero_H' (F := EtaleSheaf.restrict F U) (final _ _ _) hν
  have := AddCommGrpCat.subsingleton_of_isZero h
  exact (Stacks.Cohomology.TerminalCohomology.h'AddEquivH _ _ ν _
    (finalIsTerminal _ _ _)).symm.toEquiv.subsingleton

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
