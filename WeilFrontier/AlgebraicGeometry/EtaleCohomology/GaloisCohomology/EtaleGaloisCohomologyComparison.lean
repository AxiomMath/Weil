module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.EtaleGaloisCohomologyComparison

/-!
# Étale cohomology of a field is Galois cohomology

Let `K` be a field, `K̄` a separable closure, `G = Gal(K̄/K)` and `Φ` the equivalence between
abelian sheaves on the small étale site of `Spec K` and discrete `G`-modules given by
`𝓕 ↦ 𝓕(K̄)`. For every abelian sheaf `𝓕` and every `q ≥ 0` there is an isomorphism
`H^q(K, 𝓕) ≅ H^q(G, 𝓕(K̄))`, natural in `𝓕`, where `H^q(K, 𝓕) = R^qΓ_K(𝓕)` is the classical
right derived functor of the sections functor `Γ_K : 𝓕 ↦ 𝓕(K)` and `H^q(G, -)` is the `q`-th
right derived functor of the invariants `M ↦ M^G` on discrete `G`-modules.

The proof: `Γ_K` is the global sections functor of the site (`Spec K` is its final object),
which is `Φ` followed by `G`-invariants; an equivalence of abelian categories is exact and
preserves injectives, so it passes through right derived functors.

## Main definitions

- `AlgebraicGeometry.etaleSectionsRightDerivedIsoGaloisCohomologyFunctor`: the isomorphism of
  functors `R^qΓ_K ≅ Φ ⋙ H^q(G, -)`.
- `AlgebraicGeometry.etaleCohomologyAddEquivGaloisCohomology`: its component at a sheaf `𝓕`,
  `H^q(K, 𝓕) ≃+ H^q(G, 𝓕(K̄))`.

## Main results

- `AlgebraicGeometry.etaleCohomologyAddEquivGaloisCohomology_naturality`: the component
  isomorphisms commute with the maps induced by a morphism of sheaves.

## Implementation notes

The site is the small étale site `SmallEtale B (Spec K) hK` of a big étale site `B`, with
coefficients `AddCommGrpCat.{u + 1}`, the universe of its objects. `𝓕(K̄)` with its Galois action
is the stalk at a geometric point `sbar` of `Spec K` (a morphism from the spectrum of an
algebraically closed field); `G` is `GeometricPoint.absoluteGaloisGroup sbar`, the Galois group
of the separable closure of `K` in the field of `sbar`, with the Krull topology. The functor `Φ`
is `AlgebraicGeometry.etaleContinuousGModuleEquivalence`.

Galois cohomology `H^q(G, M)` is `continuousGroupCohomology`, the `q`-th right derived
functor of the invariants on discrete `G`-modules. Its identification with the cohomology of
continuous cochains is a separate statement.

The same comparison with `H^q(K, 𝓕)` read as Mathlib's sheaf cohomology `CategoryTheory.Sheaf.H`
is `AlgebraicGeometry.etaleSheafCohomologyAddEquivContinuousGroupCohomology`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1.14
* [The Stacks Project, Tag 03QU][stacks-project]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

attribute [local instance]
  enoughInjectives_etaleSheaf_objectUniverse
  additive_etaleGlobalSectionsFunctor
  additive_etaleContinuousGModuleEquivalenceFunctor

/-- The sections functor `𝓕 ↦ 𝓕(K)` over the final object `Spec K` of the small étale site of
`Spec K` is additive, being isomorphic to the global sections functor. -/
theorem additive_etaleSectionsFinal :
    ((sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).obj
      (op (SmallEtale.final B (Spec (.of K)) hK))).Additive :=
  Functor.additive_of_iso
    (Sheaf.ΓNatIsoSheafSections _ _ (SmallEtale.finalIsTerminal B (Spec (.of K)) hK))

attribute [local instance] additive_etaleSectionsFinal

/-- **Étale cohomology of a field is Galois cohomology, as an isomorphism of functors.** For
every `q`, the `q`-th right derived functor of the sections functor `𝓕 ↦ 𝓕(K)` on abelian
sheaves on the small étale site of `Spec K` is the stalk equivalence `𝓕 ↦ 𝓕(K̄)` followed by
the `q`-th Galois cohomology functor `H^q(G, -)`. -/
@[weil "lem_fk101_etale_cohomology_field_eq_galois_cohomology"]
def etaleSectionsRightDerivedIsoGaloisCohomologyFunctor (q : ℕ) :
    ((sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final B (Spec (.of K)) hK))).rightDerived q ≅
      (etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor ⋙
        continuousGroupCohomologyFunctor.{u, u + 1}
          (GeometricPoint.absoluteGaloisGroup sbar) q :=
  Functor.rightDerivedIsoOfNatIso
      (Sheaf.ΓNatIsoSheafSections _ _ (SmallEtale.finalIsTerminal B (Spec (.of K)) hK)).symm q ≪≫
    etaleRightDerivedGammaIsoContinuousGroupCohomologyFunctor B K hK sbar q

/-- **Étale cohomology of a field is Galois cohomology.** For an abelian sheaf `𝓕` on the small
étale site of `Spec K` and every `q`, `H^q(K, 𝓕) = R^qΓ_K(𝓕)` is isomorphic to the Galois
cohomology `H^q(G, 𝓕(K̄))` of the discrete `G`-module `𝓕(K̄)`. -/
def etaleCohomologyAddEquivGaloisCohomology
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) (q : ℕ) :
    (((sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final B (Spec (.of K)) hK))).rightDerived q).obj F ≃+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) q
        ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj F) :=
  ((etaleSectionsRightDerivedIsoGaloisCohomologyFunctor B K hK sbar q).app
    F).addCommGroupIsoToAddEquiv

/-- The isomorphism `H^q(K, 𝓕) ≃+ H^q(G, 𝓕(K̄))` is natural in `𝓕`. -/
theorem etaleCohomologyAddEquivGaloisCohomology_naturality
    {F F' : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}}
    (φ : F ⟶ F') (q : ℕ)
    (x : (((sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final B (Spec (.of K)) hK))).rightDerived q).obj F) :
    etaleCohomologyAddEquivGaloisCohomology B K hK sbar F' q
        ((((sheafSections (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}).obj
          (op (SmallEtale.final B (Spec (.of K)) hK))).rightDerived q).map φ x) =
      (continuousGroupCohomologyFunctor.{u, u + 1}
          (GeometricPoint.absoluteGaloisGroup sbar) q).map
        ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.map φ)
        (etaleCohomologyAddEquivGaloisCohomology B K hK sbar F q x) :=
  NatTrans.naturality_apply (etaleSectionsRightDerivedIsoGaloisCohomologyFunctor B K hK sbar q).hom
    φ x

end AlgebraicGeometry

end
