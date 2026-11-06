module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleQuasiCompact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable

/-!
# A constructible sheaf is a quotient of a representable sheaf

Let `X` be a quasi-compact and quasi-separated scheme and `F` a constructible sheaf of sets on
the small étale site of `X`. Then there is an object `Y` of the small étale site of `X` and an
epimorphism `h_Y ⟶ F` from the sheaf represented by `Y`.

The proof combines the epimorphism onto `F` from a finite coproduct `∐ₖ h_{U_k}` of
representable sheaves (Stacks, Tag 09Y9) with the identification of that coproduct with the
sheaf represented by the disjoint union `Y = ⊔ₖ U_k`.

## Main results

* `AlgebraicGeometry.exists_representable_epi_of_isConstructibleSetSheaf`: a constructible sheaf
  of sets on a quasi-compact quasi-separated scheme is the target of an epimorphism from the sheaf
  represented by a quasi-compact quasi-separated object of the small étale site.

## Implementation notes

[FK] work over a Noetherian scheme; the statement here only asks that `X` be quasi-compact and
quasi-separated, which every Noetherian scheme is. The object `Y` is moreover quasi-compact and
quasi-separated, being a finite disjoint union of such objects.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A constructible sheaf of sets is a quotient of a representable sheaf.** On a quasi-compact
and quasi-separated scheme `X`, every constructible sheaf of sets `F` on the small étale site of
`X` receives an epimorphism `h_Y ⟶ F` from the sheaf represented by some object `Y` of the
site. -/
@[weil "lem_fk104_constructible_implies_quotient_of_representable"]
theorem exists_representable_epi_of_isConstructibleSetSheaf
    (B : BigEtaleSite.{u}) (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B X F) :
    ∃ (Y : SmallEtale B X.obj X.property)
      (p : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y ⟶ F),
      Epi p := by
  obtain ⟨n, U, -, p, hp⟩ := exists_finite_representable_epi_of_isConstructibleSetSheaf B X F hF
  let _ : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
    CategoryTheory.Sheaf.instHasFiniteColimits
  let _ : HasColimitsOfShape (Discrete (Fin n))
      (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
    HasFiniteColimits.out _
  refine ⟨Stacks.EtaleCohomology.disjointUnionObj B X.property U,
    (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B X.property U).inv ≫ p,
    epi_comp _ _⟩

end AlgebraicGeometry
