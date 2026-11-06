module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeTorsionColimit
public import Weil.Attr

/-!
# Base change morphisms for a structure morphism and a base change morphism

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes, `X_T := X ×_S T`, and
`f' : X_T ⟶ T`, `g' : X_T ⟶ X` the two projections. In the cartesian square
```
X_T --g'--> X
 |f'        |f
 v          v
 T  --g---> S
```
`f` is called the *structure morphism* and `g` the *base change morphism*. For a complex `I` of
abelian sheaves on the small étale site of `X` and a morphism of complexes `q : g'^* I ⟶ J`, the
*base change morphism for `(f, g)`* is the morphism of complexes
`γ_{(ι,q)} : g^* f_* I ⟶ f'_* J` of `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`
for this square, and the *base change homomorphism for `(f, g)`* in degree `i` is
`β^i_{(ι,q)} = H^i(γ_{(ι,q)})`, the map of
`Stacks.EtaleCohomology.etaleAbelianResolutionHigherBaseChange` for this square.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianPullbackResolutionBaseChange` — the base change morphism
  `γ : g^* f_* I ⟶ pr₂_* J` for `(f, g)`.
* `Stacks.EtaleCohomology.etaleAbelianPullbackResolutionHigherBaseChange` — the base change
  homomorphism `β^i : H^i(g^* f_* I) ⟶ H^i(pr₂_* J)` for `(f, g)`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_pullback_app_eq` — for a choice of
  resolutions `(ι, q)` by K-injective complexes, the canonical base change map
  `g^*(Rf_* F) ⟶ R pr₂_*(pr₁^* F)` at `F` is the image of the base change morphism for `(f, g)`.
* `Stacks.EtaleCohomology.etaleAbelianPullbackResolutionHigherBaseChange_eq` — the base change
  homomorphism for `(f, g)` in degree `p` is the canonical base change map
  `g^*(R^p f_* F) ⟶ R^p pr₂_*(pr₁^* F)`.

## Implementation notes

The fibre product is Mathlib's `CategoryTheory.Limits.pullback f g`, with projections
`pullback.fst f g : X ×_S T ⟶ X` (the morphism `g'`) and `pullback.snd f g : X ×_S T ⟶ T` (the
morphism `f'`), and the square commutes by `pullback.condition`. A general cartesian square is a
`CategoryTheory.IsPullback g' f' f g`. Sheaves are abelian sheaves on Mathlib's small étale site
`X.smallEtaleTopology`, the setting of `Stacks.EtaleCohomology.etaleAbelianResolutionBaseChange`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6, p. 61][FreitagKiehl1988]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v

namespace Stacks.EtaleCohomology

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)

/-- **The base change morphism for `(f, g)`.** For the structure morphism `f : X ⟶ S`, the base
change morphism `g : T ⟶ S`, a complex `I` of abelian sheaves on `X` and a morphism of complexes
`q : pr₁^* I ⟶ J` on `X ×_S T`, the morphism of complexes
`γ = pr₂_*(q) ∘ β_I : g^* f_* I ⟶ pr₂_* J` of the cartesian square of `X ×_S T`. -/
@[weil "def_fk106_structure_and_base_change_mapping"]
abbrev etaleAbelianPullbackResolutionBaseChange {ι : Type*} {c : ComplexShape ι}
    (I : HomologicalComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c)
    {J : HomologicalComplex
      (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) c}
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex c).obj I ⟶
      J) :
    ((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
        c).obj I ⟶
      ((etaleAbelianDirectImage.{u, v} (pullback.snd f g)).mapHomologicalComplex c).obj J :=
  etaleAbelianResolutionBaseChange.{u, v} f g (pullback.fst f g) (pullback.snd f g)
    pullback.condition I q

/-- **The base change homomorphism for `(f, g)`.** For a complex `I` of abelian sheaves on `X`, a
morphism of complexes `q : pr₁^* I ⟶ J` on `X ×_S T` and `i : ℤ`, the map
`β^i = H^i(γ) : H^i(g^* f_* I) ⟶ H^i(pr₂_* J)`, where `γ` is the base change morphism for
`(f, g)`. -/
@[weil "def_fk106_structure_and_base_change_mapping"]
abbrev etaleAbelianPullbackResolutionHigherBaseChange
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (i : ℤ) :
    (((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i ⟶
      (((etaleAbelianDirectImage.{u, v} (pullback.snd f g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).homology i :=
  etaleAbelianResolutionHigherBaseChange.{u, v} f g (pullback.fst f g) (pullback.snd f g)
    pullback.condition I q i

/-- The base change homomorphism for `(f, g)` is the homology of the base change morphism for
`(f, g)`. -/
theorem etaleAbelianPullbackResolutionHigherBaseChange_eq_homologyMap
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    (i : ℤ) :
    etaleAbelianPullbackResolutionHigherBaseChange.{u, v} f g I q i =
      HomologicalComplex.homologyMap (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q) i :=
  rfl

section Resolutions

variable {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
  {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}

/-- **The base change map for `(f, g)` is computed by any choice of resolutions.** For
quasi-isomorphisms `ι : F ⟶ I` and `q : pr₁^* I ⟶ J` with `I` and `J` K-injective, the canonical
base change map `g^*(Rf_* F) ⟶ R pr₂_*(pr₁^* F)` at `F` is the image of the base change morphism
for `(f, g)`, read through `Q(g^* f_* I) ≅ g^*(Rf_* F)` and `Q(pr₂_* J) ≅ R pr₂_*(pr₁^* F)`. -/
theorem etaleAbelianDerivedBaseChange_pullback_app_eq
    {F' : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (ι : F' ⟶ I) [QuasiIso ι]
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso q]
    (hI : CochainComplex.IsKInjective I) (hJ : CochainComplex.IsKInjective J) :
    (etaleAbelianDerivedBaseChange.{u, v} f g (pullback.fst f g) (pullback.snd f g)
        pullback.condition).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F')) =
      (etaleAbelianResolutionBaseChangeSourceIso.{u, v} f g ι hI).inv ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q)) ≫
        (etaleAbelianResolutionBaseChangeTargetIso.{u, v} (pullback.fst f g) (pullback.snd f g)
          ι q hJ).hom :=
  etaleAbelianDerivedBaseChange_app_eq.{u, v} f g _ _ pullback.condition ι q hI hJ

/-- **The base change homomorphism for `(f, g)` is the canonical one.** For `p : ℕ` and
quasi-isomorphisms `ι : F[0] ⟶ I`, `q : pr₁^* I ⟶ J` with `I` and `J` K-injective, the base
change homomorphism `β^p` for `(f, g)`, read through `H^p(g^* f_* I) ≅ g^*(R^p f_* F)` and
`H^p(pr₂_* J) ≅ R^p pr₂_*(pr₁^* F)`, is the canonical base change map
`g^*(R^p f_* F) ⟶ R^p pr₂_*(pr₁^* F)` at `F`. -/
theorem etaleAbelianPullbackResolutionHigherBaseChange_eq
    (ι : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F ⟶ I) [QuasiIso ι]
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso q]
    (hI : CochainComplex.IsKInjective I) (hJ : CochainComplex.IsKInjective J) (p : ℕ) :
    (etaleAbelianResolutionHigherBaseChangeRightDerivedSourceIso.{u, v} f g ι hI p).inv ≫
        etaleAbelianPullbackResolutionHigherBaseChange.{u, v} f g I q p ≫
        (etaleAbelianResolutionHigherBaseChangeRightDerivedTargetIso.{u, v} (pullback.fst f g)
          (pullback.snd f g) ι q hJ p).hom =
      (etaleAbelianHigherBaseChangeSourceIso.{u, v} f g p).inv.app F ≫
        (etaleAbelianHigherBaseChange.{u, v} f g (pullback.fst f g) (pullback.snd f g)
          pullback.condition p).app F ≫
        (etaleAbelianHigherBaseChangeTargetIso.{u, v} (pullback.fst f g) (pullback.snd f g)
          p).hom.app F :=
  etaleAbelianResolutionHigherBaseChange_eq.{u, v} f g _ _ pullback.condition ι q hI hJ p

end Resolutions

end Stacks.EtaleCohomology

end
