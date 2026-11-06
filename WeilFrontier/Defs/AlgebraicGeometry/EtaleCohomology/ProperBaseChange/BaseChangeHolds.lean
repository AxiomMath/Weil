module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StructureAndBaseChangeMapping
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDerivedDirectImage
public import Weil.Attr

/-!
# Base change holds for a structure morphism, a base change morphism and a complex

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes, with the cartesian square
```
X ×_S T --g'--> X
   |f'          |f
   v            v
   T  ---g----> S
```
and let `F` be a bounded below complex of abelian sheaves on the small étale site of `X`. For a
*choice of resolutions* `(ι, q)` of `F` — injective resolutions `ι : F ⟶ I` of `F` and
`q : g'^* I ⟶ J` of `g'^* I` — the base change morphism of complexes
`γ_{(ι,q)} : g^* f_* I ⟶ f'_* J` is defined
(`Stacks.EtaleCohomology.etaleAbelianPullbackResolutionBaseChange`). *Base change holds for
`(f, g, F)`* if `γ_{(ι,q)}` is a quasi-isomorphism for every choice of resolutions.

The morphism `γ_{(ι,q)}` represents, in the derived category of `T`, the canonical base change map
`g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` (`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`), read
through isomorphisms. So base change holds for `(f, g, F)` exactly when the canonical base change
map is an isomorphism at `F`; this is the definition adopted here, and its agreement with the
formulation by resolutions is
`Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_iff_forall_injectiveResolution`. For a sheaf
`F`, base change holds for `(f, g, F)` when it holds for `F[0]`, that is, when every base change
homomorphism `β^i_{(ι,q)} = H^i(γ_{(ι,q)})` is an isomorphism; for `i < 0` both sides vanish.

## Main definitions

* `Stacks.EtaleCohomology.EtaleAbelianBaseChangeHolds` — base change holds for `(f, g, F)`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_iff_quasiIso` — for one choice of
  resolutions by K-injective complexes, base change holds if and only if `γ_{(ι,q)}` is a
  quasi-isomorphism.
* `Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_iff_forall_injectiveResolution` — for a
  bounded below complex, base change holds if and only if `γ_{(ι,q)}` is a quasi-isomorphism for
  every choice of injective resolutions.
* `Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_single_iff` — for a sheaf, base change holds
  for `F[0]` if and only if the base change map `g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` is an isomorphism.
* `Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_single_iff_forall_isIso` — for a sheaf, base
  change holds if and only if every base change homomorphism `β^i_{(ι,q)}` is an isomorphism, for
  every choice of injective resolutions.
* `Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_single_iff_forall_higherBaseChange` — for a
  sheaf, base change holds if and only if the base change maps
  `g^*(R^p f_* F) ⟶ R^p f'_*(g'^* F)` are isomorphisms for all `p ≥ 0`.
* `CochainComplex.InjectiveResolution.isKInjective_cocomplex` — the resolving complex of an
  injective resolution is K-injective.

## Implementation notes

The definition is stated for an arbitrary complex `F`, the resolution-free formulation needing no
boundedness; boundedness below of `F` is used only to know that injective resolutions of `F` (and
of `g'^* I`) exist, in
`Stacks.EtaleCohomology.etaleAbelianBaseChangeHolds_iff_forall_injectiveResolution`. Injective
resolutions are `CochainComplex.InjectiveResolution`: bounded below complexes of injective sheaves
with a quasi-isomorphism from the resolved complex. Sheaves are abelian sheaves on Mathlib's small
étale site `X.smallEtaleTopology`, the setting of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`.

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

/-- **Base change holds for `(f, g, F)`.** For the structure morphism `f : X ⟶ S`, the base change
morphism `g : T ⟶ S` and a complex `F` of abelian sheaves on the small étale site of `X`, the
canonical base change map `g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` of the cartesian square of `X ×_S T` is an
isomorphism of the derived category of `T`. -/
@[weil "def_fk106_base_change_holds"]
def EtaleAbelianBaseChangeHolds
    (F : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ) : Prop :=
  IsIso ((etaleAbelianDerivedBaseChange.{u, v} f g (pullback.fst f g) (pullback.snd f g)
    pullback.condition).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj F)))

/-- **Base change is computed by one choice of resolutions.** For quasi-isomorphisms
`ι : F ⟶ I` and `q : g'^* I ⟶ J` with `I` and `J` K-injective, base change holds for `(f, g, F)`
if and only if the base change morphism `γ_{(ι,q)} : g^* f_* I ⟶ f'_* J` is a
quasi-isomorphism. -/
theorem etaleAbelianBaseChangeHolds_iff_quasiIso
    {F I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
    (ι : F ⟶ I) [QuasiIso ι]
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso q]
    (hI : CochainComplex.IsKInjective I) (hJ : CochainComplex.IsKInjective J) :
    EtaleAbelianBaseChangeHolds.{u, v} f g F ↔
      QuasiIso (etaleAbelianPullbackResolutionBaseChange.{u, v} f g I q) := by
  rw [EtaleAbelianBaseChangeHolds,
    etaleAbelianDerivedBaseChange_pullback_app_eq.{u, v} f g ι q hI hJ,
    isIso_comp_left_iff, isIso_comp_right_iff]
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
  rfl

/-- The resolving complex of an injective resolution is K-injective. -/
theorem _root_.CochainComplex.InjectiveResolution.isKInjective_cocomplex {C : Type*} [Category* C]
    [Abelian C] {K : CochainComplex C ℤ} (R : K.InjectiveResolution) :
    R.cocomplex.IsKInjective := by
  obtain ⟨a, ha⟩ := R.boundedBelow
  exact CochainComplex.isKInjective_of_injective _ a

/-- **Base change holds, by resolutions.** For a bounded below complex `F` of abelian sheaves on
`X`, base change holds for `(f, g, F)` if and only if, for every choice of resolutions — an
injective resolution `ι : F ⟶ I` of `F` and an injective resolution `q : g'^* I ⟶ J` of `g'^* I`
— the base change morphism `γ_{(ι,q)} : g^* f_* I ⟶ f'_* J` is a quasi-isomorphism. -/
@[weil "def_fk106_base_change_holds"]
theorem etaleAbelianBaseChangeHolds_iff_forall_injectiveResolution
    (F : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ)
    (hF : CochainComplex.plus _ F) :
    EtaleAbelianBaseChangeHolds.{u, v} f g F ↔
      ∀ (R : F.InjectiveResolution)
        (R' : CochainComplex.InjectiveResolution
          (((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj R.cocomplex)),
        QuasiIso (etaleAbelianPullbackResolutionBaseChange.{u, v} f g R.cocomplex R'.ι) := by
  refine ⟨fun h R R' ↦ (etaleAbelianBaseChangeHolds_iff_quasiIso.{u, v} f g R.ι R'.ι
    R.isKInjective_cocomplex R'.isKInjective_cocomplex).1 h, fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := hF
  obtain ⟨R, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a F
  obtain ⟨R', -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a
    (((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R.cocomplex)
  exact (etaleAbelianBaseChangeHolds_iff_quasiIso.{u, v} f g R.ι R'.ι
    R.isKInjective_cocomplex R'.isKInjective_cocomplex).2 (h R R')

section Sheaf

variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})

/-- **Base change for a sheaf.** Base change holds for `(f, g, F[0])` if and only if the base
change map `g^*(Rf_* F) ⟶ Rf'_*(g'^* F)` of the cartesian square of `X ×_S T` is an isomorphism. -/
@[weil "def_fk106_base_change_holds"]
theorem etaleAbelianBaseChangeHolds_single_iff :
    EtaleAbelianBaseChangeHolds.{u, v} f g
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) ↔
      IsIso (etaleAbelianSheafDerivedBaseChange.{u, v} f g (pullback.fst f g) (pullback.snd f g)
        pullback.condition F) :=
  (NatTrans.isIso_app_iff_of_iso _ (etaleAbelianSingleObjIsoQhObj.{u, v} F)).symm

/-- **Base change for a sheaf, by base change homomorphisms.** Base change holds for
`(f, g, F[0])` if and only if, for every choice of injective resolutions `ι : F[0] ⟶ I` and
`q : g'^* I ⟶ J`, every base change homomorphism `β^i_{(ι,q)} : H^i(g^* f_* I) ⟶ H^i(f'_* J)`
is an isomorphism. -/
@[weil "def_fk106_base_change_holds"]
theorem etaleAbelianBaseChangeHolds_single_iff_forall_isIso :
    EtaleAbelianBaseChangeHolds.{u, v} f g
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) ↔
      ∀ (R : CochainComplex.InjectiveResolution
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))
        (R' : CochainComplex.InjectiveResolution
          (((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj R.cocomplex)) (i : ℤ),
        IsIso (etaleAbelianPullbackResolutionHigherBaseChange.{u, v} f g R.cocomplex R'.ι i) := by
  rw [etaleAbelianBaseChangeHolds_iff_forall_injectiveResolution.{u, v} f g _ ⟨0, inferInstance⟩]
  exact forall₂_congr fun R R' ↦ (quasiIso_iff _).trans
    (forall_congr' fun i ↦ quasiIsoAt_iff_isIso_homologyMap _ i)

/-- **Base change for a sheaf, in degrees `p ≥ 0`.** Base change holds for `(f, g, F[0])` if and
only if the base change map `g^*(R^p f_* F) ⟶ R^p f'_*(g'^* F)` on cohomology sheaves is an
isomorphism for every `p ≥ 0`: in negative degrees both sides vanish. -/
@[weil "def_fk106_base_change_holds"]
theorem etaleAbelianBaseChangeHolds_single_iff_forall_higherBaseChange :
    EtaleAbelianBaseChangeHolds.{u, v} f g
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) ↔
      ∀ p : ℕ, IsIso ((etaleAbelianHigherBaseChange.{u, v} f g (pullback.fst f g)
        (pullback.snd f g) pullback.condition p).app F) := by
  rw [etaleAbelianBaseChangeHolds_single_iff, etaleAbelianSheafDerivedBaseChange,
    DerivedCategory.isIso_iff]
  refine ⟨fun h p ↦ h p, fun h n ↦ ?_⟩
  rcases n with p | p
  · exact h p
  have hn : Int.negSucc p < 0 := Int.negSucc_lt_zero p
  have hsrc : ((etaleAbelianDerivedDirectImage.{u, v} f).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsGE 0 :=
    isGE_etaleAbelianDerivedDirectImage_obj f _ 0 inferInstance
  have htgt₀ : ((etaleAbelianDerivedInverseImage.{u, v} (pullback.fst f g)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsGE 0 :=
    have : DerivedCategory.TStructure.t.IsGE
        ((etaleAbelianInverseImage.{u, v} (pullback.fst f g) ⋙
          DerivedCategory.singleFunctor _ 0).obj F) 0 :=
      (inferInstance : ((DerivedCategory.singleFunctor _ 0).obj
        ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).obj F)).IsGE 0)
    DerivedCategory.TStructure.t.isGE_of_iso
      (((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapDerivedCategorySingleFunctor
        0).app F).symm 0
  have htgt : ((etaleAbelianDerivedDirectImage.{u, v} (pullback.snd f g)).obj
      ((etaleAbelianDerivedInverseImage.{u, v} (pullback.fst f g)).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))).IsGE 0 :=
    isGE_etaleAbelianDerivedDirectImage_obj _ _ 0 htgt₀
  have hX : IsZero ((DerivedCategory.homologyFunctor _ (Int.negSucc p)).obj
      ((etaleAbelianDerivedInverseImage.{u, v} g).obj ((etaleAbelianDerivedDirectImage.{u, v} f).obj
        ((DerivedCategory.singleFunctor _ 0).obj F)))) :=
    (Functor.map_isZero (etaleAbelianInverseImage.{u, v} g)
      (DerivedCategory.isZero_of_isGE _ 0 _ hn (hX := hsrc))).of_iso
      (((Stacks.DerivedFunctor.derivedHomologyIso (etaleAbelianInverseImage.{u, v} g)
        (Int.negSucc p)).app _))
  have hY := DerivedCategory.isZero_of_isGE _ 0 _ hn (hX := htgt)
  exact ⟨⟨0, hX.eq_of_src _ _, hY.eq_of_src _ _⟩⟩

end Sheaf

end Stacks.EtaleCohomology

end
