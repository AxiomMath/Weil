module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSmallEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteEtaleCompactification
public import Weil.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Main
public import Weil.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import Weil.AlgebraicGeometry.Sites.EtaleComparison
public import Weil.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericDirectImageCohomologyVanishGe3
public import Weil.Attr

/-!
# Higher direct images from the generic point of a curve are acyclic

Let `k` be a separably closed field, `X` a curve over `k` with function field `K`,
`η : Spec K ⟶ X` the canonical morphism onto the generic point and `𝒢` an abelian sheaf on
`(Spec K)_ét`. Then `H^p(X, R^q η_* 𝒢) = 0` for all `p > 0` and `q > 0`.

For `q > 0` the stalk of `R^q η_* 𝒢` at the generic geometric point `η̄` vanishes. By the
computation of the stalks of higher direct images (Stacks 03Q9) this stalk is the cohomology of
the base change `Spec K ×_X Spec(𝒪^{sh}_{X,η̄})` of `η` to the strict henselization at `η̄`. The
strict henselization maps onto the generic point, so it factors through the monomorphism `η`
and the base change is the strict henselization itself, a strictly henselian local scheme, whose
positive-degree étale cohomology vanishes (Stacks 03QO). A sheaf on a curve whose generic
geometric stalk vanishes has no higher cohomology.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_higherDirectImage_genericPointHom`:
  `H^p(X, R^q η_* 𝒢) = 0` for `p, q > 0`.
* `AlgebraicGeometry.isZero_etaleStalk_higherDirectImage_genericPointHom`: the stalk of
  `R^q η_* 𝒢` at the generic geometric point vanishes for `q > 0`.
* `Stacks.EtaleCohomology.isZero_smallEtaleStalkAb_rightDerived_genericPointInclusion`: the
  same on the small étale sites `AlgebraicGeometry.Scheme.Etale`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isIso_spec`: étale cohomology in positive
  degrees vanishes on any scheme isomorphic to the spectrum of a strictly henselian local ring.

## Implementation notes

Sheaves live on the small étale sites `AlgebraicGeometry.SmallEtale` of a big étale site, with
coefficients `AddCommGrpCat.{u + 1}`, and the stalk computation is carried out on the small
étale sites `AlgebraicGeometry.Scheme.Etale`, through the equivalences
`AlgebraicGeometry.SmallEtale.sheafEquiv`. The source assumes `k` algebraically closed and `𝒢` a
torsion sheaf; neither the torsion hypothesis nor more than separable closedness of `k` is used,
since the generic stalk of `R^q η_* 𝒢` vanishes for every abelian sheaf.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK88], I.5
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section IsoInvariance

/-- The abelian group `ℤ` is a projective object of `AddCommGrpCat` in every universe. -/
private theorem projective_addCommGrpCat_ulift_int :
    Projective (AddCommGrpCat.of (ULift.{u + 1, 0} ℤ)) := by
  constructor
  intro E X f e he
  obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective e).mp he (f.hom (ULift.up 1))
  refine ⟨AddCommGrpCat.ofHom (uliftZMultiplesHom E y), ?_⟩
  apply AddCommGrpCat.hom_ext
  ext z
  change e.hom ((uliftZMultiplesHom E y) z) = f.hom z
  rw [uliftZMultiplesHom_apply_apply]
  have hz : z = z.down • (ULift.up (1 : ℤ)) := by
    apply ULift.ext
    simp
  calc
    e.hom (z.down • y) = z.down • e.hom y := map_zsmul _ _ _
    _ = z.down • f.hom (ULift.up 1) := by rw [hy]
    _ = f.hom (z.down • ULift.up 1) := (map_zsmul _ _ _).symm
    _ = f.hom z := (congrArg f.hom hz).symm

/-- The direct image of abelian étale sheaves along an isomorphism of schemes is an equivalence,
with inverse the direct image along the inverse isomorphism. -/
def smallEtalePushforwardAbEquivOfIsIso {W V : Scheme.{u}} (e : W ⟶ V) [IsIso e] :
    Sheaf W.smallEtaleTopology Ab.{u + 1} ≌ Sheaf V.smallEtaleTopology Ab.{u + 1} :=
  CategoryTheory.Equivalence.mk (smallEtalePushforwardAb e) (smallEtalePushforwardAb (inv e))
    ((smallEtalePushforwardAbCompIso e (inv e) ≪≫
      eqToIso (congrArg smallEtalePushforwardAb (IsIso.hom_inv_id e)) ≪≫
        etaleAbelianDirectImageIdIso W).symm)
    (smallEtalePushforwardAbCompIso (inv e) e ≪≫
      eqToIso (congrArg smallEtalePushforwardAb (IsIso.inv_hom_id e)) ≪≫
        etaleAbelianDirectImageIdIso V)

/-- Global sections of abelian étale sheaves preserve epimorphisms as soon as the constant sheaf
`ℤ` is projective: a section of the target is a morphism from `ℤ`, which lifts. -/
theorem preservesEpimorphisms_sheafSections_of_projective (X : Scheme.{u})
    (h : Projective ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)))) :
    ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 X)))).PreservesEpimorphisms := by
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal (@Etale) X)
  refine ⟨fun {F G} φ hφ => ?_⟩
  rw [AddCommGrpCat.epi_iff_surjective]
  intro y
  let a : AddCommGrpCat.of (ULift ℤ) ⟶
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 X)))).obj G :=
    AddCommGrpCat.ofHom ((zmultiplesHom _ y).comp AddEquiv.ulift.toAddMonoidHom)
  let c := Projective.factorThru ((adj.homEquiv _ _).symm a) φ
  refine ⟨adj.homEquiv _ _ c (ULift.up 1), ?_⟩
  have hc : adj.homEquiv _ _ c ≫
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op (Scheme.Etale.mk (𝟙 X)))).map φ = a := by
    rw [← Adjunction.homEquiv_naturality_right, Projective.factorThru_comp,
      Equiv.apply_symm_apply]
  have := ConcreteCategory.congr_hom hc (ULift.up 1)
  rw [ConcreteCategory.comp_apply] at this
  rw [this]
  exact one_zsmul y

/-- The constant abelian sheaf `ℤ` on the small étale site is projective on a scheme as soon as
it is projective on an isomorphic one. -/
theorem projective_constantSheaf_of_isIso {W V : Scheme.{u}} (e : W ⟶ V) [IsIso e]
    (h : Projective ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)))) :
    Projective ((constantSheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) := by
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  have := preservesEpimorphisms_sheafSections_of_projective V h
  have : (smallEtalePushforwardAb e).PreservesEpimorphisms :=
    inferInstanceAs (smallEtalePushforwardAbEquivOfIsIso e).functor.PreservesEpimorphisms
  have : ((sheafSections W.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 W)))).PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso (smallEtalePushforwardAbΓIso e)
  exact (constantSheafAdj W.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal (@Etale) W)).map_projective _
      projective_addCommGrpCat_ulift_int

/-- Étale cohomology in positive degrees vanishes on a scheme isomorphic to the spectrum of a
strictly henselian local ring. -/
theorem subsingleton_sheafH_of_isIso_spec {W : Scheme.{u}} (R : Type u) [CommRing R]
    [StrictlyHenselianLocalRing R] (e : W ⟶ Spec (.of R)) [IsIso e]
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : p ≠ 0)
  have := projective_constantSheaf_of_isIso e
    (Stacks.StrictlyHenselian.projective_constantSheaf_smallEtaleTopology R)
  exact CategoryTheory.Abelian.Ext.subsingleton_of_projective _ _ n

end IsoInvariance

section GenericPoint

variable (X : Scheme.{u}) [IsIntegral X]

/-- Over the generic geometric point, the base change of `η : Spec K ⟶ X` to the strict
henselization `Spec(𝒪^{sh}_{X,η̄}) ⟶ X` is an isomorphism onto the strict henselization: the
strict henselization maps onto the generic point, so it factors through the monomorphism `η`. -/
instance isIso_strictHenselizationBaseChangeToStrictHenselization_genericPointInclusion
    (B : BigEtaleSite.{u}) (hX : B.Contains X) :
    IsIso (strictHenselizationBaseChangeToStrictHenselization B hX (genericPointInclusion X)
      (Scheme.genericGeometricPoint X)) := by
  have key : ∀ (x : X) (_ : x = genericPoint X) {T : Scheme.{u}}
      (ψ : T ⟶ Spec (X.presheaf.stalk x)),
      IsIso (pullback.snd (X.fromSpecStalk (genericPoint X)) (ψ ≫ X.fromSpecStalk x)) := by
    rintro x rfl T ψ
    infer_instance
  have hx : (Scheme.genericGeometricPoint X).hom
      (IsLocalRing.closedPoint (Scheme.genericGeometricPoint X).residueField) = genericPoint X := by
    rw [← Scheme.genericGeometricPoint_liesOver X]
    exact congrArg _ (Subsingleton.elim _ _)
  exact key _ hx _

/-- **The stalk at the generic geometric point of a higher direct image along the generic
point.** For an integral scheme `X` with function field `K` and `η : Spec K ⟶ X` quasi-compact,
the stalk of `R^q η_* F` at the generic geometric point vanishes for every abelian sheaf `F` on
`(Spec K)_ét` and every `q > 0`: by Stacks 03Q9 it is the cohomology of the base change of `η`
to the strict henselization at the generic geometric point, which is that strict henselization,
a strictly henselian local scheme. -/
theorem isZero_smallEtaleStalkAb_rightDerived_genericPointInclusion
    [QuasiCompact (genericPointInclusion X)]
    (F : Sheaf (Spec X.functionField).smallEtaleTopology Ab.{u + 1}) (q : ℕ) (hq : 0 < q) :
    IsZero ((smallEtaleStalkAb (Scheme.genericGeometricPoint X).hom).obj
      (((smallEtalePushforwardAb (genericPointInclusion X)).rightDerived q).obj F)) := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  have : QuasiSeparated (genericPointInclusion X) :=
    AlgebraicGeometry.instQuasiSeparatedOfMonoScheme _
  have hW := subsingleton_sheafH_of_isIso_spec
    (etaleLocalRing B X hX (Scheme.genericGeometricPoint X))
    (strictHenselizationBaseChangeToStrictHenselization B hX (genericPointInclusion X)
      (Scheme.genericGeometricPoint X))
    ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX (genericPointInclusion X)
      (Scheme.genericGeometricPoint X))).obj F) q hq
  exact IsZero.of_iso (AddCommGrpCat.isZero_of_subsingleton _)
    (higherDirectImageStalkIso B hX (genericPointInclusion X) (Scheme.genericGeometricPoint X) q F)

end GenericPoint

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

section

variable {X : Scheme.{u}} [IsIntegral X]
  (B : BigEtaleSite.{u}) (hX : B.Contains X) (hK : B.Contains (Spec X.functionField))

/-- On the small étale sites of a big étale site: for an integral scheme `X` with function field
`K` and `η : Spec K ⟶ X` quasi-compact, the stalk of `R^q η_* 𝒢` at the generic geometric point
vanishes for every abelian sheaf `𝒢` on `(Spec K)_ét` and every `q > 0`. -/
theorem isZero_etaleStalk_higherDirectImage_genericPointHom
    [QuasiCompact (genericPointInclusion X)]
    (G : SmallEtaleAbelianSheaf B (B.obj (Spec X.functionField) hK)) (q : ℕ) (hq : 0 < q) :
    IsZero (etaleStalk B X hX (Scheme.genericGeometricPoint X)
      ((BigEtaleSite.higherDirectImage.{u + 1} B (B.genericPointHom X hX hK) q).obj G).obj) := by
  let EK := SmallEtale.sheafEquiv B (Spec X.functionField) hK AddCommGrpCat.{u + 1}
  let EX := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  let s := Scheme.genericGeometricPoint X
  have h0 := isZero_smallEtaleStalkAb_rightDerived_genericPointInclusion X (EK.functor.obj G) q hq
  let e₁ := ((BigEtaleSite.etaleAbelianHigherDirectImageIso.{u, 0} B
    (B.genericPointHom X hX hK) q).app (EK.functor.obj G))
  let e₂ := EX.functor.mapIso
    ((BigEtaleSite.higherDirectImage.{u + 1} B (B.genericPointHom X hX hK) q).mapIso
    (EK.unitIso.app G).symm)
  have h1 := h0.of_iso ((Scheme.pointSmallEtale s.hom).sheafFiber.mapIso (e₁ ≪≫ e₂)).symm
  rw [etaleStalk_eq_presheafFiber]
  exact h1.of_iso (SmallEtale.sheafFiber_sheafEquiv_functor_obj_iso B X hX _ s _).symm

end

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] (B : BigEtaleSite.{u}) (hX : B.Contains X)
  (hK : B.Contains (Spec X.functionField))

include f in
/-- **Freitag–Kiehl I.5.** Let `k` be a separably closed field (for instance an algebraically
closed one), `X` a curve over `k` with function field `K`, `η : Spec K ⟶ X` the canonical
morphism onto the generic point, and `𝒢` an abelian sheaf on `(Spec K)_ét`. Then
`H^p(X, R^q η_* 𝒢) = 0` for all `p > 0` and `q > 0`. -/
@[weil "lem_fk105_generic_direct_image_higher_cohomology"]
theorem subsingleton_sheafH_higherDirectImage_genericPointHom
    (G : SmallEtaleAbelianSheaf B (B.obj (Spec X.functionField) hK)) (p q : ℕ) (hp : 0 < p)
    (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1, u + 1}
      ((BigEtaleSite.higherDirectImage.{u + 1} B (B.genericPointHom X hX hK) q).obj G) p) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact IsCurve.subsingleton_sheafH_of_isZero_etaleStalk_genericGeometricPoint B k (B.obj X hX) f
    _ (isZero_etaleStalk_higherDirectImage_genericPointHom B hX hK G q hq) p hp

end AlgebraicGeometry
