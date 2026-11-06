module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.PlusToUnboundedBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import Weil.Algebra.Homology.DerivedCategory.Plus
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMap
public import Weil.Attr

/-!
# Base change for bounded below complexes from base change for sheaves

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes, `X_T` a fibre product with projections
`f' : X_T ⟶ T` and `g' : X_T ⟶ X`, and suppose base change holds for `(f, g)`: the base change
homomorphisms `g⁻¹ R^i f_* F ⟶ R^i f'_* (g'⁻¹ F)` are isomorphisms for every abelian sheaf `F`
on the small étale site of `X` which is torsion prime to the residue characteristics of `S`.
Then for every bounded below complex `K` of abelian sheaves on `X` whose cohomology sheaves are
torsion prime to the residue characteristics of `S`, the derived base change morphism
$$ g^{-1} Rf_* K ⟶ Rf'_* (g'^{-1} K) $$
is an isomorphism.

The proof is the way-out argument `DerivedCategory.Plus.isIso_app_of_prop_homology`, applied to
the two functors `g⁻¹ ∘ Rf_*` and `Rf'_* ∘ g'⁻¹` on bounded below derived categories, the base
change morphism between them, and the class of sheaves torsion prime to the residue
characteristics of `S`. Both functors are triangulated, hence carry admissible triangles to
admissible triangles, and right derived functors do not lower the degree in which cohomology
starts. The base change morphism commutes with the shift, so it suffices to show it is invertible
at `F[0]` for such a sheaf `F`; there its degree `q` cohomology is the base change homomorphism
in degree `q` for `q ≥ 0`, and both sides vanish for `q < 0`.

## Main results

* `AlgebraicGeometry.SmallEtale.SatisfiesBaseChange.isIso_smallEtaleDerivedBaseChangeAb_app`:
  under `BC(f, g)`, the base change morphism of the bounded below derived categories is an
  isomorphism at every object whose cohomology sheaves are torsion prime to the residue
  characteristics of `S`.
* `AlgebraicGeometry.SmallEtale.SatisfiesBaseChange.isIso_etaleAbelianDerivedBaseChange_app`:
  the same for the base change morphism `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`
  of the unbounded derived categories, at bounded below objects.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_app_of_isIso_higherBaseChangeMapAb`,
  `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_of_isIso_higherBaseChangeMapAb`:
  the two statements for an arbitrary commutative square, with the hypothesis on the base change
  homomorphisms stated on Mathlib's small étale sites.

## Implementation notes

The derived categories are those of abelian sheaves on Mathlib's small étale sites
`X.smallEtaleTopology`, the setting of the base change morphisms; the condition `BC(f, g)` is
`AlgebraicGeometry.SmallEtale.SatisfiesBaseChange`, which is read on these sites through
`AlgebraicGeometry.SmallEtale.isIso_higherBaseChangeMapAb_app_of_satisfiesBaseChange`, and
"torsion prime to the residue characteristics of `S`" is
`Stacks.EtaleCohomology.HasTorsionOrdersInvertibleOn S`. A bounded below object of the unbounded
derived category is represented by a bounded below complex of injective sheaves, at which the
unbounded base change morphism is invertible as soon as the bounded below one is
(`isIso_etaleAbelianDerivedBaseChange_app_of_isIso_smallEtaleDerivedBaseChangeAb`, in the
namespace `Stacks.EtaleCohomology`).
Only the commutativity of the square is used in the general statements.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.7][FreitagKiehl1988]
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

universe u

namespace DerivedCategory.Plus

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- A triangulated functor `D⁺(C) ⥤ D⁺(D)` carries admissible triangles to admissible
triangles. -/
private theorem map_admissibleTriangles (Φ : Plus C ⥤ Plus D) [Φ.CommShift ℤ]
    [Φ.IsTriangulated] (T : Triangle (Plus C))
    (hT : ι.mapTriangle.obj T ∈ admissibleTriangles C) :
    ι.mapTriangle.obj (Φ.mapTriangle.obj T) ∈ admissibleTriangles D := by
  rw [mem_admissibleTriangles_ι_mapTriangle_iff] at hT ⊢
  refine isomorphic_distinguished _ (Φ.map_distinguished _ hT) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [Functor.mapTriangle])
      (by simp [Functor.mapTriangle]) (by simp [Functor.mapTriangle]; rfl))

end DerivedCategory.Plus

namespace Stacks.EtaleCohomology

variable {X S T XT : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (f' : XT ⟶ T) (g' : XT ⟶ X)
  (w : f' ≫ g = g' ≫ f)

/-- The right derived functor on bounded below derived categories does not lower the degree
in which cohomology starts. -/
private theorem isZero_homology_rightDerivedFunctorPlus_obj {A B : Type*} [Category* A]
    [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] (m : ℤ) (K : DerivedCategory.Plus A)
    (hK : ∀ ν < m, IsZero ((DerivedCategory.Plus.homologyFunctor A ν).obj K)) :
    ∀ ν < m, IsZero ((DerivedCategory.Plus.homologyFunctor B ν).obj
      (F.rightDerivedFunctorPlus.obj K)) := by
  have : K.IsGE m := (DerivedCategory.Plus.isGE_iff K m).2 hK
  exact (DerivedCategory.Plus.isGE_iff _ m).1 (F.isGE_rightDerivedFunctorPlus_obj K m)

/-- **Base change for bounded below complexes.** For a commutative square `f' ≫ g = g' ≫ f`,
if the base change homomorphisms `g⁻¹ R^i f_* G ⟶ R^i f'_* (g'⁻¹ G)` are isomorphisms at every
abelian sheaf `G` with torsion of orders invertible on `S`, then the base change morphism
`g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` of the bounded below derived categories is an isomorphism at every
object whose cohomology sheaves have torsion of orders invertible on `S`. -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_of_isIso_higherBaseChangeMapAb
    (hbc : ∀ G : Sheaf X.smallEtaleTopology Ab.{u + 1}, HasTorsionOrdersInvertibleOn S G →
      ∀ i : ℕ, IsIso ((higherBaseChangeMapAb g f f' g' w i).app G))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : ∀ ν : ℤ, HasTorsionOrdersInvertibleOn S
      ((DerivedCategory.Plus.homologyFunctor _ ν).obj K)) :
    IsIso ((smallEtaleDerivedBaseChangeAb g f f' g' w).app K) := by
  have := commShift_smallEtaleDerivedBaseChangeAb g f f' g' w
  refine DerivedCategory.Plus.isIso_app_of_prop_homology
    (DerivedCategory.Plus.map_admissibleTriangles _)
    (DerivedCategory.Plus.map_admissibleTriangles _) ?_ ?_ _
    (fun G => HasTorsionOrdersInvertibleOn S G) ?_ K hK
  · intro m K hK
    exact isZero_homology_rightDerivedFunctorPlus_obj _ m _
      (isZero_homology_rightDerivedFunctorPlus_obj _ m K hK)
  · intro m K hK
    exact isZero_homology_rightDerivedFunctorPlus_obj _ m _
      (isZero_homology_rightDerivedFunctorPlus_obj _ m K hK)
  · intro G hG j
    rw [NatTrans.app_shift]
    suffices IsIso ((smallEtaleDerivedBaseChangeAb g f f' g' w).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) by infer_instance
    rw [DerivedCategory.Plus.isIso_iff]
    intro q
    rcases lt_or_ge q 0 with hq | hq
    · have h0 : ∀ ν < (0 : ℤ), IsZero ((DerivedCategory.Plus.homologyFunctor _ ν).obj
          ((DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj G)) :=
        (DerivedCategory.Plus.isGE_iff _ 0).1 inferInstance
      refine ⟨⟨0, ?_, ?_⟩⟩
      · exact (isZero_homology_rightDerivedFunctorPlus_obj _ 0 _
          (isZero_homology_rightDerivedFunctorPlus_obj _ 0 _ h0) q hq).eq_of_src _ _
      · exact (isZero_homology_rightDerivedFunctorPlus_obj _ 0 _
          (isZero_homology_rightDerivedFunctorPlus_obj _ 0 _ h0) q hq).eq_of_src _ _
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact (isIso_higherBaseChangeMapAb_app_iff g f f' g' w n G).1 (hbc G hG n)

/-- **Base change for bounded below complexes, unbounded form.** Under the hypothesis of
`isIso_smallEtaleDerivedBaseChangeAb_app_of_isIso_higherBaseChangeMapAb`, the base change
morphism `g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` of the unbounded derived categories is an isomorphism at every
bounded below object whose cohomology sheaves have torsion of orders invertible on `S`. -/
theorem isIso_etaleAbelianDerivedBaseChange_app_of_isIso_higherBaseChangeMapAb
    (hbc : ∀ G : Sheaf X.smallEtaleTopology Ab.{u + 1}, HasTorsionOrdersInvertibleOn S G →
      ∀ i : ℕ, IsIso ((higherBaseChangeMapAb g f f' g' w i).app G))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ)
    [K.IsGE n]
    (hK : ∀ ν : ℤ, HasTorsionOrdersInvertibleOn S ((DerivedCategory.homologyFunctor _ ν).obj K)) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' w.symm).app K) := by
  let Kp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}) := ⟨K, n, inferInstance⟩
  have : Kp.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff Kp n).1 (inferInstanceAs (K.IsGE n))
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Kp n
  have hp := isIso_smallEtaleDerivedBaseChangeAb_app_of_isIso_higherBaseChangeMapAb
    f g f' g' w hbc Kp hK
  let N := (InjectiveObject.ι (Sheaf X.smallEtaleTopology Ab.{u + 1})).mapCochainComplexPlus.obj L
  let e' : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj N) ≅ Kp :=
    DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj N)
      ((DerivedCategory.Plus.QhCompιIsoιCompQh _).app _ ≪≫
        DerivedCategory.Qh.mapIso ((HomotopyCategory.Plus.quotientCompιIso _).app N) ≪≫
        (DerivedCategory.quotientCompQhIso _).app N.obj) ≪≫ e
  have hp' := (NatTrans.isIso_app_iff_of_iso (smallEtaleDerivedBaseChangeAb g f f' g' w) e').2 hp
  have hu := isIso_etaleAbelianDerivedBaseChange_app_of_isIso_smallEtaleDerivedBaseChangeAb
    f g g' f' w.symm N
    (fun m => by
      have : Injective (N.obj.X m) :=
        (L.obj.X m).property
      exact Functor.rightAcyclic_of_injective _ _) hp'
  exact (NatTrans.isIso_app_iff_of_iso _
    (((DerivedCategory.Plus.QhCompιIsoιCompQh _).app _ ≪≫
        DerivedCategory.Qh.mapIso ((HomotopyCategory.Plus.quotientCompιIso _).app N)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso e')).1 hu

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.SmallEtale

open Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X S T XT : Scheme.{u}} {hX : B.Contains X} {hT : B.Contains T}
  {f : X ⟶ S} {g : T ⟶ S} {f' : XT ⟶ T} {g' : XT ⟶ X}

/-- **Base change for complexes from base change for sheaves.** If base change holds for
`(f, g)` and `X_T` is a fibre product, then for every object `K` of the bounded below derived
category of abelian sheaves on `X` whose cohomology sheaves are torsion prime to the residue
characteristics of `S`, the base change morphism `g⁻¹ Rf_* K ⟶ Rf'_* (g'⁻¹ K)` is an
isomorphism in the bounded below derived category of `T`. -/
@[weil "lem_fk107_sbc_complexes_from_sheaves"]
theorem SatisfiesBaseChange.isIso_smallEtaleDerivedBaseChangeAb_app
    (h : SatisfiesBaseChange B hX hT f g) (sq : IsPullback f' g' g f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : ∀ ν : ℤ, HasTorsionOrdersInvertibleOn S
      ((DerivedCategory.Plus.homologyFunctor _ ν).obj K)) :
    IsIso ((smallEtaleDerivedBaseChangeAb g f f' g' sq.w).app K) :=
  isIso_smallEtaleDerivedBaseChangeAb_app_of_isIso_higherBaseChangeMapAb f g f' g' sq.w
    (fun _ hG i => isIso_higherBaseChangeMapAb_app_of_satisfiesBaseChange h sq hG i) K hK

/-- **Base change for complexes from base change for sheaves, unbounded form.** If base change
holds for `(f, g)` and `X_T` is a fibre product, the base change morphism
`g⁻¹ Rf_* K ⟶ Rf'_* (g'⁻¹ K)` of `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` is an
isomorphism at every bounded below complex `K` of abelian sheaves on `X` whose cohomology
sheaves are torsion prime to the residue characteristics of `S`. -/
@[weil "lem_fk107_sbc_complexes_from_sheaves"]
theorem SatisfiesBaseChange.isIso_etaleAbelianDerivedBaseChange_app
    (h : SatisfiesBaseChange B hX hT f g) (sq : IsPullback f' g' g f)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ) [K.IsGE n]
    (hK : ∀ ν : ℤ, HasTorsionOrdersInvertibleOn S ((DerivedCategory.homologyFunctor _ ν).obj K)) :
    IsIso ((etaleAbelianDerivedBaseChange.{u, 0} f g g' f' sq.w.symm).app K) :=
  isIso_etaleAbelianDerivedBaseChange_app_of_isIso_higherBaseChangeMapAb f g f' g' sq.w
    (fun _ hG i => isIso_higherBaseChangeMapAb_app_of_satisfiesBaseChange h sq hG i) K n hK

end AlgebraicGeometry.SmallEtale

end
