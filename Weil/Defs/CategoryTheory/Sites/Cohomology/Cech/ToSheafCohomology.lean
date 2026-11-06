module

public import Weil.Attr
public import Mathlib.Algebra.Homology.TotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ToSheafCohomology
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyOfAnObject
public import Weil.Defs.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Canonical Čech-to-derived maps

Let `S` be a noetherian separated scheme, `F` an abelian sheaf on the small étale site of `S`
and `F → I^•` an injective resolution, so that `H^i(S, F) = H^i(Γ(S, I^•))`. For an étale
covering `𝔘 = (U_ν → S)_ν` in `Cov(S)` let `T_𝔘` be the total complex of the double complex
`K^{p,q} = Č^p(𝔘, I^q)`, with differential `D = d_Č + (-1)^p d_I`. There are two maps into
`T_𝔘`: `α_𝔘 : Č^n(𝔘, F) → K^{n,0} ⊆ T^n_𝔘`, induced by `F → I^0`, and
`β_𝔘 : I^n(S) → K^{0,n} ⊆ T^n_𝔘`, `y ↦ (y|_{U_ν})_ν`. A homomorphism
`c : Ȟ^i(S, F) → H^i(S, F)` is a *canonical Čech-to-derived map* if for every covering `𝔘`,
every cocycle `z ∈ Z^i(𝔘, F)` and every cocycle `y ∈ I^i(S)` with
`β_𝔘(y) - α_𝔘(z) ∈ D(T^{i-1}_𝔘)`, the image `c([z]_𝔘)` is the class of `y`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.restrictSheaf`: the restriction to `Et(S)`
  of an abelian sheaf on the small étale site.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechAugmentation`: the restriction map
  `G(U) → Č^0(𝔘, G)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechResolutionBicomplex`: the double complex
  `K^{p,q} = Č^p(𝔘, I^q)`, Čech degree first.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechResolutionTotal`: its total complex
  `T_𝔘`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechToTotalComplex`: the map `α_𝔘`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.globalSectionsToTotalComplex`: the map
  `β_𝔘`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.IsCanonicalCechToDerivedMap`: the property
  of a homomorphism `Ȟ^i(S, F) → H^i(S, F)` of being a canonical Čech-to-derived map.

## Implementation notes

The Čech side is that of `Et(S)`: the coverings are
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.CechCovering`, the group `Ȟ^i(S, F)` is
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.cechCohomologyOfObject` of the restriction of
`F` to `Et(S)`, and the Čech complexes of the terms of the resolution are those of their
restrictions to `Et(S)`. The derived side is that of the small étale site: `H^i(S, F)` is
`CategoryTheory.Sheaf.H`, identified with `H^i(Γ(S, I^•))` by
`AlgebraicGeometry.SmallEtale.hAddEquivHomologySections`. The two sheaf categories are
equivalent when `S` is locally noetherian, the restriction being the inverse equivalence.

The double complex is indexed by `ℤ × ℤ`, the Čech complexes and the resolution being extended
by zero to negative degrees; this encodes `T^{-1}_𝔘 = 0`. The first index is the Čech degree,
so that the sign convention of `HomologicalComplex₂.total` is `D = d_Č + (-1)^p d_I`. The
double complex `Stacks.CechSite.cechBicomplex` of Stacks 03AX has the resolution degree first,
and its total complex differs from this one by the sign `(-1)^{pq}` on `K^{p,q}`, which is `1`
on the terms `K^{n,0}` and `K^{0,n}` met by `α_𝔘` and `β_𝔘`; it requires coefficients in
the universe of the objects of the site, which the abelian sheaves `AddCommGrpCat.{u}` on the
small étale site of a `u`-scheme are not, so it is not used here.

A cocycle `y` of `Γ(S, I^•)` is given as an element of the cycles of that complex.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The final object `(S, id)` of `Et(S)` is the final object of the small étale site. -/
@[simp]
lemma inclusion_obj_final [IsNoetherian S] [S.IsSeparated] :
    (inclusion B S hS).obj (final B S hS) = SmallEtale.final B S hS :=
  rfl

variable {B S hS}

/-- The restriction to `Et(S)` of an abelian sheaf on the small étale site of `S`. -/
abbrev restrictSheaf (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}) :
    EtalePresheaf B S hS AddCommGrpCat.{u} :=
  (inclusion B S hS).op ⋙ F.obj

/-- **The augmentation** `G(U) → Č^0(𝔘, G)` of a family `𝔘 = (U_ν → U)_ν` of `Et(S)`:
`s ↦ (s|_{U_ν})_ν`. -/
def cechAugmentation {U : SmallNoetherianSeparatedEtale B S hS} (E : PreZeroHypercover.{0} U)
    (G : EtalePresheaf B S hS AddCommGrpCat.{u}) : G.obj (op U) ⟶ (cechComplex E G).X 0 :=
  Pi.lift fun ν : Fin 1 → E.I₀ ↦ G.map (∏ᶜ fun j ↦ Over.mk (E.f (ν j)) : Over U).hom.op

@[reassoc (attr := simp)]
lemma cechAugmentation_π {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) (G : EtalePresheaf B S hS AddCommGrpCat.{u})
    (ν : Fin 1 → E.I₀) :
    cechAugmentation E G ≫ Pi.π (Stacks.CechSite.cochainFactor E G 0) ν =
      G.map (∏ᶜ fun j ↦ Over.mk (E.f (ν j)) : Over U).hom.op :=
  Pi.lift_π _ _

/-- The Čech complex along a family of `Et(S)` of the restriction of an abelian sheaf on the
small étale site, extended by zero to an integer-graded complex. -/
abbrev cechCochainFunctor {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u} ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (inclusion B S hS).op ⋙
    Stacks.CechSite.cechComplexFunctor E ⋙
      ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}

instance cechCochainFunctor_preservesZeroMorphisms {U : SmallNoetherianSeparatedEtale B S hS}
    (E : PreZeroHypercover.{0} U) :
    (cechCochainFunctor (B := B) (S := S) (hS := hS) E).PreservesZeroMorphisms := by
  dsimp only [cechCochainFunctor]
  infer_instance

variable [IsNoetherian S] [S.IsSeparated]
  {F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u}} (I : InjectiveResolution F)

/-- **The double complex** `K^{p,q} = Č^p(𝔘, I^q)` of a covering `𝔘 ∈ Cov(S)` and an
injective resolution `F → I^•`, with the Čech degree `p` first. -/
abbrev cechResolutionBicomplex (𝔘 : CechCovering (final B S hS)) :
    HomologicalComplex₂ AddCommGrpCat.{u} (.up ℤ) (.up ℤ) :=
  HomologicalComplex₂.flip
    (((cechCochainFunctor 𝔘.toPreZeroHypercover).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex)

/-- **The total complex** `T_𝔘` of `K^{p,q} = Č^p(𝔘, I^q)`, with `T^n_𝔘 = ⨁_{p+q=n} K^{p,q}`
and differential `D = d_Č + (-1)^p d_I`. -/
abbrev cechResolutionTotal (𝔘 : CechCovering (final B S hS)) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  (cechResolutionBicomplex I 𝔘).total (.up ℤ)

/-- **The map** `α_𝔘 : Č^n(𝔘, F) → K^{n,0} ⊆ T^n_𝔘` induced by `F → I^0`. -/
def cechToTotalComplex (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    (cechComplex 𝔘.toPreZeroHypercover (restrictSheaf F)).X n ⟶
      (cechResolutionTotal I 𝔘).X n :=
  ((sheafToPresheaf _ _ ⋙ (Functor.whiskeringLeft _ _ _).obj (inclusion B S hS).op ⋙
      Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).map I.inclusionZero).f n ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X 0))).extendXIso ComplexShape.embeddingUpNat rfl).inv ≫
    (cechResolutionBicomplex I 𝔘).ιTotal (.up ℤ) n 0 n (by simp)

/-- **The map** `β_𝔘 : I^n(S) → K^{0,n} ⊆ T^n_𝔘`, `y ↦ (y|_{U_ν})_ν`. -/
def globalSectionsToTotalComplex (𝔘 : CechCovering (final B S hS)) (n : ℕ) :
    ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).obj (I.cocomplex.X n) ⟶ (cechResolutionTotal I 𝔘).X n :=
  ((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).map (I.cochainComplexXIso n n rfl).inv ≫
    cechAugmentation 𝔘.toPreZeroHypercover (restrictSheaf (I.cochainComplex.X n)) ≫
    (((Stacks.CechSite.cechComplexFunctor 𝔘.toPreZeroHypercover).obj
      (restrictSheaf (I.cochainComplex.X n))).extendXIso ComplexShape.embeddingUpNat rfl).inv ≫
    (cechResolutionBicomplex I 𝔘).ιTotal (.up ℤ) 0 n n (by simp)

/-- The complex `Γ(S, I^•)` of global sections of an injective resolution. -/
abbrev globalSectionsComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  (((sheafSections (SmallEtale.topology B S hS) AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B S hS))).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

variable [HasExt.{w} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u})]

/-- **Canonical Čech-to-derived maps.** A homomorphism `c : Ȟ^i(S, F) → H^i(S, F)` is a
canonical Čech-to-derived map, for the injective resolution `F → I^•`, if for every covering
`𝔘 ∈ Cov(S)`, every cocycle `z ∈ Z^i(𝔘, F)` and every cocycle `y` of `Γ(S, I^•)` in degree `i`
with `β_𝔘(y) - α_𝔘(z) ∈ D(T^{i-1}_𝔘)`, the image `c([z]_𝔘)` is the class of `y` in
`H^i(Γ(S, I^•)) = H^i(S, F)`. -/
@[weil "def_fk102_cech_to_derived_map"]
def IsCanonicalCechToDerivedMap (i : ℕ)
    (c : cechCohomologyOfObject (final B S hS) (restrictSheaf F) i →+ F.H i) : Prop :=
  ∀ (𝔘 : CechCovering (final B S hS))
    (z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i)
    (y : (globalSectionsComplex I).cycles i),
    (globalSectionsToTotalComplex I 𝔘 i).hom (((globalSectionsComplex I).iCycles i).hom y) -
        (cechToTotalComplex I 𝔘 i).hom z ∈
      ((cechResolutionTotal I 𝔘).d ((i : ℤ) - 1) i).hom.range →
      c (cechClass (restrictSheaf F) i 𝔘 z) =
        (SmallEtale.hAddEquivHomologySections B S hS F I i).symm
          (((globalSectionsComplex I).homologyπ i).hom y)

variable {I}

/-- The defining property of a canonical Čech-to-derived map, applied to a covering, a Čech
cocycle and a cocycle of `Γ(S, I^•)` matching it in the total complex. -/
lemma IsCanonicalCechToDerivedMap.apply_cechClass {i : ℕ}
    {c : cechCohomologyOfObject (final B S hS) (restrictSheaf F) i →+ F.H i}
    (hc : IsCanonicalCechToDerivedMap I i c) (𝔘 : CechCovering (final B S hS))
    (z : cechCycles 𝔘.toPreZeroHypercover (restrictSheaf F) i)
    (y : (globalSectionsComplex I).cycles i)
    (h : (globalSectionsToTotalComplex I 𝔘 i).hom (((globalSectionsComplex I).iCycles i).hom y) -
        (cechToTotalComplex I 𝔘 i).hom z ∈
      ((cechResolutionTotal I 𝔘).d ((i : ℤ) - 1) i).hom.range) :
    c (cechClass (restrictSheaf F) i 𝔘 z) =
      (SmallEtale.hAddEquivHomologySections B S hS F I i).symm
        (((globalSectionsComplex I).homologyπ i).hom y) :=
  hc 𝔘 z y h

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
