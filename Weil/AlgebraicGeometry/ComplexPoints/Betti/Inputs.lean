module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.Finiteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import Weil.Definitions
public import Weil.Attr

/-!
# Artin's comparison theorem and finiteness of integral cohomology, as named inputs

Let `Y` be a smooth projective scheme over `ℂ` and `Y(ℂ)` its complex points with the analytic
topology (`AlgebraicGeometry.Scheme.ComplexPoints`). This file states two classical results as
named propositions, to be carried as hypotheses by the theorems that use them.

* **Artin's comparison theorem** (SGA 4, XVI 4.1; [FK] I.11.6): for every finite abelian group
  `M` and every `ν`, the étale cohomology `H^ν_et(Y, M)` is isomorphic to the sheaf cohomology
  `H^ν(Y(ℂ), M)` of the constant sheaf `M` on `Y(ℂ)`, naturally in `M`. The theorem holds for
  every scheme of finite type over `ℂ`; it is stated here for smooth projective ones.
* **Finiteness of integral cohomology**: for `Y` smooth projective, `Y(ℂ)` is a compact
  topological manifold, so each `H^ν(Y(ℂ), ℤ)` is a finitely generated abelian group: on a
  manifold sheaf cohomology with constant coefficients agrees with singular cohomology
  (Bredon, *Sheaf Theory*, III), and a compact manifold is homotopy equivalent to a finite CW
  complex (Hatcher, *Algebraic Topology*, Appendix).

## Main definitions

* `AlgebraicGeometry.Scheme.etaleCohomologyConstant`: `H^ν_et(Y, M)` for a constant sheaf `M`.
* `AlgebraicGeometry.Scheme.analyticCohomologyConstant`: `H^ν(Y(ℂ), M)` for a constant sheaf
  `M`.
* `AlgebraicGeometry.Scheme.ArtinComparisonAt`, `AlgebraicGeometry.Scheme.ArtinComparison`:
  Artin's comparison theorem for finite coefficients.
* `AlgebraicGeometry.Scheme.IntegralCohomologyFG`,
  `AlgebraicGeometry.Scheme.IntegralCohomologyFGOfProjective`: the integral cohomology of
  `Y(ℂ)` is finitely generated in each degree.

## Implementation notes

The étale cohomology is `Sheaf.H` on Mathlib's small étale site `Y.smallEtaleTopology` with
coefficients in `AddCommGrpCat.{1}` (the constant sheaf `ULift M`), with the Grothendieck
abelian structure `Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale` and `Ext`
from `CategoryTheory.IsGrothendieckAbelian.hasExt`, as in the étale cohomology of the Stacks
project formalization. The analytic cohomology is `Sheaf.H` on the site of opens of `Y(ℂ)`
with coefficients in `AddCommGrpCat.{0}`, with `Ext` from
`CategoryTheory.IsGrothendieckAbelian.hasExt`. The functoriality in `M` is postcomposition with
the image of `M ⟶ N` under the constant sheaf functor.

## References

* [SGA4] M. Artin, A. Grothendieck, J.-L. Verdier, *Théorie des topos et cohomologie étale des
  schémas*, Tome 3, Exposé XVI, Théorème 4.1.
* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, 11.6 and §12.
* [Bredon] G. Bredon, *Sheaf Theory*, Chapter III.
* [Hatcher] A. Hatcher, *Algebraic Topology*, Appendix.
-/

/- both propositions are proved in the library: `AlgebraicGeometry.Scheme.artinComparison`
(`Weil.AlgebraicGeometry.ComplexPoints.Betti.ArtinComparison`) and
`AlgebraicGeometry.Scheme.integralCohomologyFGOfProjective`
(`Weil.AlgebraicGeometry.ComplexPoints.Betti.IntegralCohomologyFG`). -/

@[expose] public section

open CategoryTheory TopologicalSpace Abelian

namespace AlgebraicGeometry.Scheme

/-- The étale cohomology `H^ν_et(Y, M)` of a scheme `Y` with coefficients in the constant sheaf
`M` (lifted to `ULift M` in `AddCommGrpCat.{1}`), on Mathlib's small étale site. -/
noncomputable def etaleCohomologyConstant (Y : Scheme.{0}) (M : AddCommGrpCat.{0}) (ν : ℕ) :
    Type 1 :=
  letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Y
  letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{1})
  Sheaf.H.{1}
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
      (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν

noncomputable instance (Y : Scheme.{0}) (M : AddCommGrpCat.{0}) (ν : ℕ) :
    AddCommGroup (etaleCohomologyConstant Y M ν) :=
  letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Y
  letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{1})
  inferInstanceAs (AddCommGroup (Sheaf.H.{1}
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj
      (AddCommGrpCat.uliftFunctor.{1, 0}.obj M)) ν))

/-- The map `H^ν_et(Y, M) → H^ν_et(Y, N)` induced by a homomorphism `g : M ⟶ N`. -/
noncomputable def etaleCohomologyConstantMap (Y : Scheme.{0}) {M N : AddCommGrpCat.{0}}
    (g : M ⟶ N) (ν : ℕ) : etaleCohomologyConstant Y M ν →+ etaleCohomologyConstant Y N ν :=
  letI := Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale.{0, 0} Y
  letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{1})
  (Ext.mk₀ ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).map
    (AddCommGrpCat.uliftFunctor.{1, 0}.map g))).postcomp _ (add_zero ν)

/-- The sheaf cohomology `H^ν(Y(ℂ), M)` of the constant sheaf `M` on the complex points `Y(ℂ)`
of a scheme over `ℂ`, with the analytic topology. -/
noncomputable def analyticCohomologyConstant {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ))
    (M : AddCommGrpCat.{0}) (ν : ℕ) : Type :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  Sheaf.H.{0}
    ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y)))
      AddCommGrpCat.{0}).obj M) ν

noncomputable instance {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) (M : AddCommGrpCat.{0}) (ν : ℕ) :
    AddCommGroup (analyticCohomologyConstant y M ν) :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  inferInstanceAs (AddCommGroup (Sheaf.H.{0}
    ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y)))
      AddCommGrpCat.{0}).obj M) ν))

/-- The map `H^ν(Y(ℂ), M) → H^ν(Y(ℂ), N)` induced by a homomorphism `g : M ⟶ N`. -/
noncomputable def analyticCohomologyConstantMap {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ))
    {M N : AddCommGrpCat.{0}} (g : M ⟶ N) (ν : ℕ) :
    analyticCohomologyConstant y M ν →+ analyticCohomologyConstant y N ν :=
  letI := IsGrothendieckAbelian.hasExt.{0}
    (Sheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y))) AddCommGrpCat.{0})
  (Ext.mk₀ ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoints y)))
    AddCommGrpCat.{0}).map g)).postcomp _ (add_zero ν)

/-- **Artin's comparison theorem** for `Y` over `ℂ` (SGA 4, XVI 4.1; [FK] I.11.6): in every
degree `ν` there are isomorphisms `H^ν_et(Y, M) ≃+ H^ν(Y(ℂ), M)` for all finite abelian groups
`M`, natural in `M`. -/
def ArtinComparisonAt {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) : Prop :=
  ∀ ν : ℕ, ∃ e : ∀ M : AddCommGrpCat.{0}, Finite M →
      etaleCohomologyConstant Y M ν ≃+ analyticCohomologyConstant y M ν,
    ∀ (M N : AddCommGrpCat.{0}) (hM : Finite M) (hN : Finite N) (g : M ⟶ N)
      (x : etaleCohomologyConstant Y M ν),
      e N hN (etaleCohomologyConstantMap Y g ν x) = analyticCohomologyConstantMap y g ν (e M hM x)

/-- **Artin's comparison theorem** for smooth projective schemes over `ℂ`: every smooth
projective `Y` over `ℂ` satisfies `ArtinComparisonAt`. -/
def ArtinComparison : Prop :=
  ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (.of ℂ)), Smooth y → IsProjective y → ArtinComparisonAt y

/-- The integral cohomology `H^ν(Y(ℂ), ℤ)` of the complex points of `Y` is a finitely generated
abelian group in every degree `ν`. -/
def IntegralCohomologyFG {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) : Prop :=
  ∀ ν : ℕ, AddGroup.FG (analyticCohomologyConstant y (AddCommGrpCat.of ℤ) ν)

/-- For every smooth projective `Y` over `ℂ`, the integral cohomology of `Y(ℂ)` is finitely
generated in every degree (`Y(ℂ)` is a compact topological manifold). -/
def IntegralCohomologyFGOfProjective : Prop :=
  ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (.of ℂ)), Smooth y → IsProjective y → IntegralCohomologyFG y

end AlgebraicGeometry.Scheme
