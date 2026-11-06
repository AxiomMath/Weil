module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable

/-!
# Constructible sheaves are the quotients of representable sheaves

Let `X` be a Noetherian scheme. A sheaf of sets `F` on the small étale site of `X` is
constructible if and only if there are a Noetherian scheme `Y` étale over `X` and an epimorphism
`h_Y ⟶ F` from the sheaf represented by `Y`.

For "only if", a constructible sheaf receives an epimorphism from a finite coproduct
`∐ₖ h_{U_k}` of sheaves represented by quasi-compact quasi-separated étale `X`-schemes
(Stacks, Tag 09Y9); that coproduct is the sheaf represented by the disjoint union
`Y = ⊔ₖ U_k`, which is quasi-compact, and locally Noetherian since it is étale over `X`.
For "if", the sheaf `h_Y` of a Noetherian étale `X`-scheme is constructible (Stacks, Tag 03S8),
and a quotient of a constructible sheaf of sets is constructible (Stacks, Tag 09BH).

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_iff_exists_epi_sheafifiedYoneda`: on a Noetherian
  scheme, a sheaf of sets on the small étale site is constructible if and only if it is the
  target of an epimorphism from the sheaf represented by a Noetherian étale `X`-scheme.
* `AlgebraicGeometry.isNoetherian_disjointUnionObj`: a finite disjoint union of quasi-compact
  objects of the small étale site of a Noetherian scheme is Noetherian.

## Implementation notes

The objects of [FK]'s category `Et(X)` are the étale morphisms `Y ⟶ X` with `Y` Noetherian; the
objects of the small étale site are all étale `X`-schemes in the big étale site, so the
Noetherian condition on `Y` is stated explicitly. The "if" direction is deduced directly from
the stability of constructible sheaves of sets under quotients rather than through the
presentation of `F` as the cokernel of an étale equivalence relation, which [FK] use.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl1988]
* [Stacks Project, Tag 09Y9](https://stacks.math.columbia.edu/tag/09Y9)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A finite disjoint union of quasi-compact objects of the small étale site of a Noetherian
scheme is a Noetherian scheme. -/
theorem isNoetherian_disjointUnionObj (B : BigEtaleSite.{u}) (X : B.Scheme)
    [IsNoetherian X.obj] {n : ℕ} (U : Fin n → SmallEtale B X.obj X.property)
    (hU : ∀ i, CompactSpace ((SmallEtale.toScheme B X.obj X.property).obj (U i))) :
    IsNoetherian
      ((SmallEtale.toScheme B X.obj X.property).obj
        (Stacks.EtaleCohomology.disjointUnionObj B X.property U)) := by
  let g := fun k => (SmallEtale.toScheme B X.obj X.property).obj (U k)
  have : Finite (sigmaOpenCover g).I₀ := inferInstanceAs (Finite (Fin n))
  have hc : CompactSpace ((∐ g : Scheme.{u}) :) :=
    @Scheme.OpenCover.compactSpace _ (sigmaOpenCover g) _ fun i => hU i
  let f := B.inclusion.map (Stacks.EtaleCohomology.disjointUnionObj B X.property U).obj.hom
  have : Etale f := Stacks.EtaleCohomology.etale_hom B X.property
      (Stacks.EtaleCohomology.disjointUnionObj B X.property U)
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj X.obj X.property)) :=
    inferInstanceAs (IsLocallyNoetherian X.obj)
  have hY := LocallyOfFiniteType.isLocallyNoetherian f
  exact @IsNoetherian.mk _ hY hc

/-- **A constructible sheaf is a quotient of a representable sheaf, and conversely.** On a
Noetherian scheme `X`, a sheaf of sets `F` on the small étale site of `X` is constructible if and
only if there are a Noetherian scheme `Y` étale over `X` and an epimorphism `h_Y ⟶ F` from the
sheaf represented by `Y`. -/
@[weil "prop_fk104_constructible_iff_quotient_of_representable"]
theorem isConstructibleSetSheaf_iff_exists_epi_sheafifiedYoneda (B : BigEtaleSite.{u})
    (X : B.Scheme) [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsConstructibleSetSheaf B X F ↔
      ∃ (Y : SmallEtale B X.obj X.property)
        (_ : IsNoetherian ((SmallEtale.toScheme B X.obj X.property).obj Y))
        (p : (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj Y ⟶ F),
        Epi p := by
  have : QuasiSeparatedSpace X.obj := IsLocallyNoetherian.quasiSeparatedSpace
  constructor
  · intro hF
    obtain ⟨n, U, hU, p, hp⟩ := exists_finite_representable_epi_of_isConstructibleSetSheaf B X F hF
    let _ : HasFiniteColimits (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
      CategoryTheory.Sheaf.instHasFiniteColimits
    let _ : HasColimitsOfShape (Discrete (Fin n))
        (Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :=
      HasFiniteColimits.out _
    exact ⟨Stacks.EtaleCohomology.disjointUnionObj B X.property U,
      isNoetherian_disjointUnionObj B X U fun i => (hU i).1,
      (Stacks.EtaleCohomology.sigmaSheafifiedYonedaIsoDisjointUnion B X.property U).inv ≫ p,
      epi_comp _ _⟩
  · rintro ⟨Y, hY, p, hp⟩
    have : CompactSpace Y.obj.left.obj := hY.toCompactSpace
    have : QuasiSeparatedSpace Y.obj.left.obj :=
      @IsLocallyNoetherian.quasiSeparatedSpace _ hY.toIsLocallyNoetherian
    exact isConstructibleSetSheaf_of_epi B X (representableIsConstructibleSetSheaf B X)
      (hasFiniteRepresentableCover B X) p (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X Y)

end AlgebraicGeometry
