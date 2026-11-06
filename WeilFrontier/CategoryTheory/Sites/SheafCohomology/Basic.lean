module

public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.ConstantSheaf
public import WeilFrontier.Defs.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Global sections of the constant sheaf on the small étale site

Let `S` be a scheme and `F` an abelian group, and let `F_S` be the sheaf of abelian groups on the
small étale site of `S` sending `V` to the locally constant maps `|V| → F`. Since `S` is the
terminal object of its small étale site, `H⁰(S, F_S) ≅ F_S(S)`, the group of locally constant
maps `|S| → F`. If the underlying space of `S` is noetherian, it has finitely many connected
components `S_1, …, S_{n_S}`, each of them open, so a locally constant map on `S` is the same as
a map on the set of connected components, and `H⁰(S, F_S) ≅ F ^ n_S`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.hZeroLocallyConstantSheafAbAddEquiv` —
  `H⁰(S, F_S) ≃+ LocallyConstant |S| F`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.hZeroLocallyConstantSheafAbAddEquivFin` —
  `H⁰(S, F_S) ≃+ (Fin n_S → F)` for `S` with noetherian underlying space, `n_S` the number of
  connected components of `S`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.hZeroLocallyConstantSheafAbAddEquivFin_apply`
  — the component of a class at the connected component of a point `s` is the value at `s` of
  the corresponding locally constant map.

## Implementation notes

The statement is made on the small étale site `SmallEtale B S hS` of [Stacks, Tag 021B] rather
than on the category of noetherian separated étale `S`-schemes; for `S` locally noetherian the
two sites have equivalent categories of sheaves, matching the two forms of `F_S`
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquivFunctorObjLocallyConstantEtSheafAbIso`).
The noetherian hypothesis is only used through the noetherian property of the underlying
topological space of `S`. The `Ext`-groups defining `H⁰` are taken in an arbitrary universe `w`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **`H⁰(S, F_S) ≅ F_S(S)`.** The zeroth étale cohomology group of the constant sheaf `F_S` of
an abelian group `F` is the group of locally constant maps `|S| → F`, its sections over the
terminal object `S` of the small étale site. -/
@[weil "lem_fk102_constant_sheaf_global_sections"]
def hZeroLocallyConstantSheafAbAddEquiv (F : Type u) [AddCommGroup F]
    [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})] :
    (locallyConstantSheafAbSmallEtale B S hS F).H 0 ≃+ LocallyConstant S F :=
  Sheaf.H.equiv₀ _ (SmallEtale.finalIsTerminal B S hS)

/-- **`H⁰(S, F_S) ≅ F ^ n_S`.** For a scheme `S` whose underlying space is noetherian, with
`n_S` connected components, the zeroth étale cohomology group of the constant sheaf `F_S` of an
abelian group `F` is `F ^ n_S`, a class being sent to the values of the corresponding locally
constant map on the connected components. -/
@[weil "lem_fk102_constant_sheaf_global_sections"]
def hZeroLocallyConstantSheafAbAddEquivFin (F : Type u) [AddCommGroup F]
    [TopologicalSpace.NoetherianSpace S]
    [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})] :
    (locallyConstantSheafAbSmallEtale B S hS F).H 0 ≃+
      (Fin (Nat.card (_root_.ConnectedComponents S)) → F) :=
  (hZeroLocallyConstantSheafAbAddEquiv B S hS F).trans
    ((LocallyConstant.addEquivConnectedComponents (X := S) (Y := F)).trans
      (AddEquiv.arrowCongr (Finite.equivFin _) (AddEquiv.refl F)))

/-- The component of `hZeroLocallyConstantSheafAbAddEquivFin` at the connected component of a
point `s` is the value at `s` of the locally constant map given by
`hZeroLocallyConstantSheafAbAddEquiv`. -/
lemma hZeroLocallyConstantSheafAbAddEquivFin_apply (F : Type u) [AddCommGroup F]
    [TopologicalSpace.NoetherianSpace S]
    [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})]
    (x : (locallyConstantSheafAbSmallEtale B S hS F).H 0) (s : S) :
    hZeroLocallyConstantSheafAbAddEquivFin B S hS F x
        (Finite.equivFin _ (_root_.ConnectedComponents.mk s)) =
      hZeroLocallyConstantSheafAbAddEquiv B S hS F x s := by
  simp [hZeroLocallyConstantSheafAbAddEquivFin, AddEquiv.arrowCongr,
    LocallyConstant.addEquivConnectedComponents_apply_mk]

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
