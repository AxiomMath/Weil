module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import Weil.Attr

/-!
# The cokernel of a pair of representable étale sheaves is constructible

Let `X` be a quasi-compact and quasi-separated scheme and `u, v : R ⇉ Y` a pair of morphisms of
quasi-compact and quasi-separated étale `X`-schemes. The cokernel (coequalizer)
`Coker(h_u, h_v)` of the induced pair of representable sheaves of sets on the small étale site
of `X` is a constructible sheaf of sets.

The representable sheaves `h_R` and `h_Y` are constructible (Stacks 03S8 (1)), and constructible
sheaves of sets are closed under finite colimits (Stacks 03RZ), so their coequalizer is
constructible.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_smallEtaleUliftYoneda`: the sheaf of sets
  represented by a quasi-compact quasi-separated étale `X`-scheme is constructible.
* `AlgebraicGeometry.isConstructibleSetSheaf_coequalizer_smallEtaleUliftYoneda`: the cokernel of a
  pair of morphisms of such representable sheaves is constructible.

## Implementation notes

Freitag–Kiehl state the result for an equivalence relation `R ⇉ Y` in the category `Et(X)` of
étale `X`-schemes of finite type over a noetherian scheme `X`, and prove it by noetherian
induction, reducing on a dense open to an equivalence relation with finite source and target
whose quotient is representable. The statement here holds for any pair of morphisms: the
equivalence relation hypothesis is not needed. The quasi-compactness and quasi-separatedness
hypotheses hold for every object of `Et(X)`, which is of finite type over a noetherian scheme.
The representable sheaves are taken with values in `Type (u + 1)`, the universe of the
constructible sheaves of sets on the small étale site.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **Representable sheaves of sets are constructible.** For a quasi-compact quasi-separated
scheme `X` and a quasi-compact quasi-separated étale `X`-scheme `U`, the sheaf of sets
`V ↦ Hom_X(V, U)` on the small étale site of `X`, with values in `Type (u + 1)`, is
constructible. -/
theorem isConstructibleSetSheaf_smallEtaleUliftYoneda
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleSetSheaf B X ((smallEtaleUliftYoneda.{u, u + 1} B X.obj X.property).obj U) :=
  isConstructibleSetSheaf_congr B X
    ((Sheaf.sheafifiedYonedaIsoUliftYoneda' (SmallEtale.topology B X.obj X.property)).app U)
    (isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X U)

/-- **The cokernel of a pair of representable sheaves is constructible** (FK I.4). Let `X` be a
quasi-compact quasi-separated scheme and `u, v : R ⟶ Y` morphisms of quasi-compact
quasi-separated étale `X`-schemes, for instance an equivalence relation in the étale category
of `X`. Then `Coker(h_u, h_v)`, the coequalizer of the induced maps of representable sheaves of
sets on the small étale site of `X`, is a constructible sheaf of sets. -/
@[weil "lem_fk104_cokernel_equivalence_relation_constructible"]
theorem isConstructibleSetSheaf_coequalizer_smallEtaleUliftYoneda
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] {R Y : SmallEtale B X.obj X.property}
    [CompactSpace R.obj.left.obj] [QuasiSeparatedSpace R.obj.left.obj]
    [CompactSpace Y.obj.left.obj] [QuasiSeparatedSpace Y.obj.left.obj] (u v : R ⟶ Y) :
    IsConstructibleSetSheaf B X
      (coequalizer ((smallEtaleUliftYoneda.{u, u + 1} B X.obj X.property).map u)
        ((smallEtaleUliftYoneda.{u, u + 1} B X.obj X.property).map v)) := by
  refine isConstructibleSetSheaf_colimit B X _ ?_
  rintro (_ | _)
  · exact isConstructibleSetSheaf_smallEtaleUliftYoneda B X R
  · exact isConstructibleSetSheaf_smallEtaleUliftYoneda B X Y

end AlgebraicGeometry

end
