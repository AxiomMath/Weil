module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Attr

/-!
# Étale cohomology as the derived functors of global sections

Let `X` be a scheme and `F` an abelian sheaf on the small étale site of `X`. The étale
cohomology groups `H^i(X, F)` are the right derived functors of the global sections functor
`Γ(X, -)`: for any injective resolution `F → I^•`,
`H^i(X, F) = H^i(Γ(X, I^•)) = ker(I^i(X) → I^{i+1}(X)) / im(I^{i-1}(X) → I^i(X))`.

In this library the cohomology of an abelian sheaf on a site is Mathlib's `CategoryTheory.Sheaf.H`,
the `Ext`-groups out of the constant sheaf `ℤ`. This file proves that on a site with a terminal
object `T` these are the right derived functors of sections over `T`, hence are computed by any
injective resolution, and specialises the statement to the small étale site
`AlgebraicGeometry.SmallEtale` of a scheme, whose terminal object is the scheme itself.

## Main definitions

* `CategoryTheory.Sheaf.extZeroIsoSectionsOfIsTerminal`: degree-zero `Ext` out of the constant
  sheaf `ℤ` is the functor of sections over a terminal object.
* `CategoryTheory.Sheaf.functorHIsoRightDerivedSections`: `H^n(-) ≅ R^nΓ(T, -)`, as functors.
* `CategoryTheory.Sheaf.hAddEquivHomologySections`: `H^n(F) ≃+ H^n(Γ(T, I^•))` for an injective
  resolution `I` of `F`.
* `AlgebraicGeometry.SmallEtale.functorHIsoRightDerivedSections`,
  `AlgebraicGeometry.SmallEtale.hAddEquivHomologySections`: the same on the small étale site of a
  scheme `S`, with `Γ(S, -)` the sections over `SmallEtale.final`.

## Implementation notes

The identification `H^n ≅ R^nΓ(T, -)` comes from the universality of the two `δ`-functors
(`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso`), which only
asserts existence, so `functorHIsoRightDerivedSections` is a chosen isomorphism; it is the
identity on degree zero only up to that choice. The `Ext`-groups defining `Sheaf.H` may live in any
universe `w`; the comparison is made in the morphism universe of the site and transported along
`CategoryTheory.Abelian.Ext.chgUniv`, which is additive.

The source works on the site `Et(X)` of noetherian separated étale `X`-schemes; its sheaf
category is equivalent to that of `AlgebraicGeometry.SmallEtale`
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`), and the statement here is on the
latter, the convention of this library.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] {T : C} (hT : IsTerminal T)

section Pinned

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- Degree-zero `Ext` out of the constant sheaf `ℤ` is the functor of sections over a terminal
object `T`; on objects this is `CategoryTheory.Sheaf.H.equiv₀`. -/
def extZeroIsoSectionsOfIsTerminal :
    extFunctorObj.{v} ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ))) 0 ≅
      (sheafSections J AddCommGrpCat.{v}).obj (op T) :=
  NatIso.ofComponents (fun F ↦ (H.equiv₀ F hT).toAddCommGrpIso) (by
    intro F G f
    ext x
    exact (H.equiv₀_naturality hT f x).symm)

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]

/-- **Sheaf cohomology is the right derived functor of sections over a terminal object.** For a
site with a terminal object `T`, the cohomology functor `H^n(-)` on abelian sheaves is
`R^nΓ(T, -)`. This is a choice of isomorphism (see the implementation notes). -/
def functorHIsoRightDerivedSections (n : ℕ) :
    Sheaf.functorH J n ≅ ((sheafSections J AddCommGrpCat.{v}).obj (op T)).rightDerived n :=
  (ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso
    ((sheafSections J AddCommGrpCat.{v}).obj (op T)) _
    (extZeroIsoSectionsOfIsTerminal J hT) n).some

end Pinned

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- **Sheaf cohomology is computed by an injective resolution.** On a site with a terminal object
`T`, for an injective resolution `F → I^•` of an abelian sheaf `F`, `H^n(F)` is the `n`-th
cohomology of the complex of sections `Γ(T, I^•)`. -/
def hAddEquivHomologySections (F : Sheaf J AddCommGrpCat.{v}) (I : InjectiveResolution F)
    (n : ℕ) :
    F.H n ≃+ ((((sheafSections J AddCommGrpCat.{v}).obj (op T)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  AddEquiv.trans
    { toEquiv := Ext.chgUniv.{v}
      map_add' a b := by
        let := HasDerivedCategory.standard (Sheaf J AddCommGrpCat.{v})
        apply Ext.homEquiv.{max u (v + 1), v}.injective
        change Ext.homEquiv (Ext.chgUniv.{v} (a + b)) =
          Ext.homEquiv (Ext.chgUniv.{v} a + Ext.chgUniv.{v} b)
        rw [Ext.homEquiv_chgUniv]
        change (a + b).hom = (Ext.chgUniv.{v} a + Ext.chgUniv.{v} b).hom
        rw [Ext.add_hom, Ext.add_hom]
        change Ext.homEquiv a + Ext.homEquiv b = Ext.homEquiv (Ext.chgUniv.{v} a) +
          Ext.homEquiv (Ext.chgUniv.{v} b)
        rw [Ext.homEquiv_chgUniv, Ext.homEquiv_chgUniv] }
    ((((functorHIsoRightDerivedSections J hT n).app F) ≪≫
      I.isoRightDerivedObj ((sheafSections J AddCommGrpCat.{v}).obj (op T)) n)
        |>.addCommGroupIsoToAddEquiv)

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian sheaves on the small étale site have `Ext`-groups in the morphism universe of the
site. Not an instance, following Mathlib's policy for `CategoryTheory.HasExt`. -/
theorem hasExt_sheaf : HasExt.{u} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives _

/-- **Étale cohomology is the derived functor of global sections.** For a scheme `S`, the
étale cohomology functor `H^n(S, -)` on abelian sheaves on the small étale site of `S` is the
`n`-th right derived functor of the global sections functor `Γ(S, -)`, the sections over the
terminal object `SmallEtale.final B S hS`. -/
@[weil "def_fk102_etale_cohomology"]
def functorHIsoRightDerivedSections (n : ℕ) :
    letI := hasExt_sheaf B S hS
    Sheaf.functorH (topology B S hS) n ≅
      ((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj
        (op (final B S hS))).rightDerived n :=
  letI := hasExt_sheaf B S hS
  Sheaf.functorHIsoRightDerivedSections (topology B S hS) (finalIsTerminal B S hS) n

/-- **Étale cohomology is computed by an injective resolution.** For an abelian sheaf `F` on the
small étale site of a scheme `S` and an injective resolution `F → I^•`,
`H^n(S, F) = H^n(Γ(S, I^•)) = ker(I^n(S) → I^{n+1}(S)) / im(I^{n-1}(S) → I^n(S))`. -/
@[weil "def_fk102_etale_cohomology"]
def hAddEquivHomologySections [HasExt.{w} (Sheaf (topology B S hS) AddCommGrpCat.{u})]
    (F : Sheaf (topology B S hS) AddCommGrpCat.{u}) (I : InjectiveResolution F) (n : ℕ) :
    F.H n ≃+ ((((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj
      (op (final B S hS))).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  letI := hasExt_sheaf B S hS
  Sheaf.hAddEquivHomologySections.{w} (topology B S hS) (finalIsTerminal B S hS) F I n

end AlgebraicGeometry.SmallEtale
