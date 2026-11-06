module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Attr

/-!
# Presheaves on the small étale site with open difference loci

Let `F` be a presheaf of sets on the small étale site of a scheme `X`. For an object `U` of the
site and sections `α β ∈ F(U)`, the coincidence set `C(α, β) ⊆ U` is the set of points of `U` at
which the germs of `α` and `β` agree (at every geometric point over the point). The presheaf
`F` *has open difference loci* if for every `U` and all `α β ∈ F(U)` the difference locus
`U \ C(α, β)`, the set of points at which the germs differ, is open in `U`; equivalently, every
coincidence set is closed.

## Main definitions

* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci`: the presheaf `F` has open difference
  loci.

## Main results

* `AlgebraicGeometry.SmallEtale.hasOpenDifferenceLoci_iff_isClosed`: `F` has open difference
  loci if and only if every coincidence set `C(α, β)` is closed.
* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.isOpen_compl`,
  `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.isClosed`: the two forms of the property
  for given sections.

## Implementation notes

The property is stated for presheaves `(SmallEtale B X hX)ᵒᵖ ⥤ Type v`, which contains the case
of an étale sheaf `F` through its underlying presheaf `F.val`; nothing in the definition uses
the sheaf condition. It is a plain predicate rather than a class, as it is passed as a
hypothesis and transferred to subsheaves, pullbacks and restrictions.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3.15
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- A presheaf of sets `F` on the small étale site of `X` has open difference loci if for every
object `U` and all sections `α β ∈ F(U)`, the set `U \ C(α, β)` of points of `U` at which the
germs of `α` and `β` differ is open in `U`. -/
@[weil "def_fk103_sheaf_open_difference_loci"]
def HasOpenDifferenceLoci (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}] : Prop :=
  ∀ (U : SmallEtale B X hX) (α β : F.obj (op U)), IsOpen (germCoincidenceSet F α β)ᶜ

variable {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v} {hv : UnivLE.{u, v}}

lemma hasOpenDifferenceLoci_iff :
    HasOpenDifferenceLoci F ↔
      ∀ (U : SmallEtale B X hX) (α β : F.obj (op U)), IsOpen (germCoincidenceSet F α β)ᶜ :=
  Iff.rfl

/-- `F` has open difference loci if and only if every coincidence set is closed. -/
lemma hasOpenDifferenceLoci_iff_isClosed :
    HasOpenDifferenceLoci F ↔
      ∀ (U : SmallEtale B X hX) (α β : F.obj (op U)), IsClosed (germCoincidenceSet F α β) := by
  simp only [hasOpenDifferenceLoci_iff, isOpen_compl_iff]

namespace HasOpenDifferenceLoci

/-- The difference locus `U \ C(α, β)` of two sections is open. -/
lemma isOpen_compl (hF : HasOpenDifferenceLoci F) {U : SmallEtale B X hX}
    (α β : F.obj (op U)) : IsOpen (germCoincidenceSet F α β)ᶜ :=
  hF U α β

/-- The coincidence set `C(α, β)` of two sections is closed. -/
lemma isClosed (hF : HasOpenDifferenceLoci F) {U : SmallEtale B X hX}
    (α β : F.obj (op U)) : IsClosed (germCoincidenceSet F α β) :=
  isOpen_compl_iff.mp (hF U α β)

end HasOpenDifferenceLoci

/-- A presheaf all of whose coincidence sets are closed has open difference loci. -/
lemma HasOpenDifferenceLoci.of_isClosed
    (h : ∀ (U : SmallEtale B X hX) (α β : F.obj (op U)), IsClosed (germCoincidenceSet F α β)) :
    HasOpenDifferenceLoci F :=
  hasOpenDifferenceLoci_iff_isClosed.mpr h

end AlgebraicGeometry.SmallEtale

end
