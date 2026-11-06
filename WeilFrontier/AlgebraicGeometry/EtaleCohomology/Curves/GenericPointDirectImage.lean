module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationStalkIdentifications
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsTransitivityOverBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import WeilFrontier.AlgebraicGeometry.FunctionField
public import Weil.Attr

/-!
# The unit of `η^* ⊣ η_*` at the generic geometric point

Let `X` be an integral scheme with function field `K`, let `η : Spec K ⟶ X` be the canonical
morphism onto the generic point and let `η̄` be a generic geometric point. For every abelian sheaf
`F` on the small étale site of `X`, the unit `F ⟶ η_* η^* F` of the adjunction `η^* ⊣ η_*`
induces an isomorphism of stalks `F_η̄ ≅ (η_* η^* F)_η̄`.

The proof is a special case of a general statement. Let `f : Y ⟶ X` be a quasi-compact and
quasi-separated morphism and `s` a geometric point of `X` such that the projection
`Y ×_X Spec 𝒪^{sh}_{X,s} ⟶ Spec 𝒪^{sh}_{X,s}` is an isomorphism. The stalk of a direct image is
`(f_* G)_s = Γ(Y ×_X Spec 𝒪^{sh}_{X,s}, p⁻¹ G)` (Stacks 03Q9 in degree zero), and the composite
of the unit with this identification is, by the triangle identity of the adjunction, the
canonical map `F_s ⟶ Γ(Y ×_X Spec 𝒪^{sh}_{X,s}, F)`; since the base change is the strict
henselization itself, that map is an isomorphism (Stacks 03Q9 for the identity). For the
generic point, `η` is a monomorphism and the strict henselization at `η̄` maps to `X` through
`Spec K`, so the projection is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_smallEtaleStalkAb_map_unit_of_isIso`: the general statement.
* `AlgebraicGeometry.isIso_smallEtaleStalkAb_map_genericPointInclusion_unit`: the unit of
  `η^* ⊣ η_*` is an isomorphism on stalks at the generic geometric point.
* `AlgebraicGeometry.isIso_sheafFiber_map_genericPointInclusion_unit_genericSepClosedPoint`:
  the same at the generic geometric point `Spec K^sep ⟶ X` over a separable closure.

## Implementation notes

The small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale` with abelian sheaves valued
in `AddCommGrpCat.{u + 1}`, the site on which the stalk of a direct image is computed by the
strict henselization. The source assumes `X` noetherian and separated and `F` torsion; the
statement holds for every integral scheme and every abelian sheaf, since `η = Spec 𝒪_{X,η} ⟶ X`
is always quasi-compact and quasi-separated.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl], I.5
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.EtaleCohomology

universe u

namespace CategoryTheory.Adjunction

/-- For an adjunction `L ⊣ R`, a natural transformation `E : S ⟶ Pq ⋙ Γ` and an isomorphism
`C : L ⋙ Pp ≅ Pq`, the map `S F ⟶ S (R L F) ⟶ Γ (Pp L F)` built from the unit, `E`, `C` and the
counit is `E` followed by `C⁻¹`. -/
theorem map_unit_comp_comp_inv_comp_map_counit {𝒞 𝒟 ℰ 𝒜 : Type*} [Category 𝒞] [Category 𝒟]
    [Category ℰ] [Category 𝒜] {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R) {Pp : 𝒟 ⥤ ℰ}
    {Pq : 𝒞 ⥤ ℰ} (C : L ⋙ Pp ≅ Pq) (Γ : ℰ ⥤ 𝒜) {S : 𝒞 ⥤ 𝒜} (E : S ⟶ Pq ⋙ Γ) (F : 𝒞) :
    S.map (adj.unit.app F) ≫ E.app (R.obj (L.obj F)) ≫ Γ.map (C.inv.app (R.obj (L.obj F))) ≫
        Γ.map (Pp.map (adj.counit.app (L.obj F))) =
      E.app F ≫ Γ.map (C.inv.app F) := by
  have h1 := E.naturality (adj.unit.app F)
  have h2 := C.inv.naturality (adj.unit.app F)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h1 h2
  rw [reassoc_of% h1, ← Functor.map_comp_assoc, h2, ← Functor.map_comp, Category.assoc,
    ← Functor.map_comp, adj.left_triangle_components, Functor.map_id, Category.comp_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

section General

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : Y ⟶ X)
  (s : GeometricPoint X)

/-- The map `(f_* G)_s ⟶ Γ(Y ×_X Spec 𝒪^{sh}_{X,s}, p⁻¹ G)` written out: the map
`H_s ⟶ Γ(Y ×_X Spec 𝒪^{sh}_{X,s}, H)` for `H = f_* G`, the identification of the two inverse
images of `f_* G` to the base change, and the counit `f^* f_* G ⟶ G`. -/
theorem pushforwardStalkToStrictHenselizationSectionsAb_app_eq
    (G : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (pushforwardStalkToStrictHenselizationSectionsAb B hX f s).app G =
      (etaleStalkToSectionsAb B X hX s
          (strictHenselizationBaseChangeToStrictHenselization B hX f s)).app
          ((smallEtalePushforwardAb f).obj G) ≫
        (Sheaf.Γ (strictHenselizationBaseChange B hX f s).smallEtaleTopology Ab.{u + 1}).map
          ((strictHenselizationBaseChangePullbackAbCompIso B hX f s).inv.app
            ((smallEtalePushforwardAb f).obj G)) ≫
          (Sheaf.Γ (strictHenselizationBaseChange B hX f s).smallEtaleTopology Ab.{u + 1}).map
            ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX f s)).map
              ((smallEtaleAdjunctionAb f).counit.app G)) := by
  simp only [pushforwardStalkToStrictHenselizationSectionsAb, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]

/-- The unit `F ⟶ f_* f^* F` on stalks at `s`, followed by the identification
`(f_* f^* F)_s = Γ(Y ×_X Spec 𝒪^{sh}_{X,s}, p⁻¹ f^* F)`, is the canonical map
`F_s ⟶ Γ(Y ×_X Spec 𝒪^{sh}_{X,s}, F)` followed by the identification of the inverse images. -/
theorem smallEtaleStalkAb_map_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    (smallEtaleStalkAb s.hom).map ((smallEtaleAdjunctionAb f).unit.app F) ≫
        (pushforwardStalkToStrictHenselizationSectionsAb B hX f s).app
          ((smallEtalePullbackAb f).obj F) =
      (etaleStalkToSectionsAb B X hX s
          (strictHenselizationBaseChangeToStrictHenselization B hX f s)).app F ≫
        (Sheaf.Γ (strictHenselizationBaseChange B hX f s).smallEtaleTopology Ab.{u + 1}).map
          ((strictHenselizationBaseChangePullbackAbCompIso B hX f s).inv.app F) := by
  rw [pushforwardStalkToStrictHenselizationSectionsAb_app_eq]
  -- The implicit arguments are given so that the kernel compares the functors syntactically.
  exact CategoryTheory.Adjunction.map_unit_comp_comp_inv_comp_map_counit
    (L := smallEtalePullbackAb f) (R := smallEtalePushforwardAb f)
    (Pp := smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hX f s))
    (Pq := smallEtalePullbackAb (strictHenselizationBaseChangeToStrictHenselization B hX f s ≫
          strictHenselizationToBase B X hX s))
    (S := smallEtaleStalkAb s.hom) (smallEtaleAdjunctionAb f)
    (strictHenselizationBaseChangePullbackAbCompIso B hX f s) _
    (etaleStalkToSectionsAb B X hX s
        (strictHenselizationBaseChangeToStrictHenselization B hX f s)) F

/-- The canonical map `F_s ⟶ Γ(T, F)` for a scheme `T` isomorphic to the strict henselization
at `s` is an isomorphism. -/
theorem isIso_etaleStalkToSectionsAb_of_isIso {T : Scheme.{u}}
    (q : T ⟶ strictHenselization B X hX s) [IsIso q] :
    IsIso (etaleStalkToSectionsAb B X hX s q) := by
  have := isIso_etaleStalkToSectionsAb_id B X hX s
  have h := etaleStalkToSectionsAb_comp B X hX s (𝟙 _) q
  have h' : IsIso (etaleStalkToSectionsAb B X hX s (q ≫ 𝟙 _)) := by
    rw [h]; infer_instance
  rwa [Category.comp_id] at h'

/-- **The unit of `f^* ⊣ f_*` on stalks.** Let `f : Y ⟶ X` be quasi-compact and
quasi-separated and `s` a geometric point of `X` such that the projection
`Y ×_X Spec 𝒪^{sh}_{X,s} ⟶ Spec 𝒪^{sh}_{X,s}` is an isomorphism. Then for every abelian sheaf
`F` on the small étale site of `X` the unit `F ⟶ f_* f^* F` is an isomorphism on stalks at
`s`. -/
theorem isIso_smallEtaleStalkAb_map_unit_of_isIso [QuasiCompact f] [QuasiSeparated f]
    [IsIso (strictHenselizationBaseChangeToStrictHenselization B hX f s)]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsIso ((smallEtaleStalkAb s.hom).map ((smallEtaleAdjunctionAb f).unit.app F)) := by
  have hP := isIso_pushforwardStalkToStrictHenselizationSectionsAb_app B hX f s
    ((smallEtalePullbackAb f).obj F)
  have hE := isIso_etaleStalkToSectionsAb_of_isIso B hX s
    (strictHenselizationBaseChangeToStrictHenselization B hX f s)
  have h := smallEtaleStalkAb_map_unit_comp_pushforwardStalkToStrictHenselizationSectionsAb
    B hX f s F
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

end General

section GenericPoint

/-- The base change of `Spec 𝒪_{X,x} ⟶ X` to the strict henselization at a geometric point over
`x` is an isomorphism onto the strict henselization: `Spec 𝒪_{X,x} ⟶ X` is a monomorphism
through which the strict henselization maps to `X`. -/
theorem isIso_strictHenselizationBaseChangeToStrictHenselization_fromSpecStalk
    (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (x : X) (s : GeometricPoint X)
    (hs : s.hom (IsLocalRing.closedPoint s.residueField) = x) :
    IsIso (strictHenselizationBaseChangeToStrictHenselization B hX (X.fromSpecStalk x) s) := by
  have key : ∀ {y : X} (h : y = x), ∃ e : Spec (X.presheaf.stalk y) ⟶ Spec (X.presheaf.stalk x),
      X.fromSpecStalk y = e ≫ X.fromSpecStalk x := by
    rintro y rfl
    exact ⟨𝟙 _, (Category.id_comp _).symm⟩
  obtain ⟨e, he⟩ := key hs
  have hbase : strictHenselizationToBase B X hX s =
      (Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B X hX s)) ≫ e) ≫
        X.fromSpecStalk x := by
    rw [Category.assoc, ← he]; rfl
  have : ∀ (g : strictHenselization B X hX s ⟶ X) (e' : strictHenselization B X hX s ⟶
      Spec (X.presheaf.stalk x)), g = e' ≫ X.fromSpecStalk x →
      IsIso (pullback.snd (X.fromSpecStalk x) g) := by
    rintro g e' rfl
    infer_instance
  exact this _ _ hbase

variable (X : Scheme.{u}) [IsIntegral X]

/-- **The unit of `η^* ⊣ η_*` at the generic geometric point.** Let `X` be an integral
scheme, `η : Spec K ⟶ X` the canonical morphism onto the generic point and `η̄`
the generic geometric point. For every abelian sheaf `F` on the small étale site of `X`, the
unit `F ⟶ η_* η^* F` induces an isomorphism `F_η̄ ≅ (η_* η^* F)_η̄`. -/
@[weil "lem_fk105_generic_adjunction_iso_at_generic_point"]
theorem isIso_smallEtaleStalkAb_map_genericPointInclusion_unit
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsIso ((smallEtaleStalkAb (Scheme.genericGeometricPoint X).hom).map
      ((smallEtaleAdjunctionAb (genericPointInclusion X)).unit.app F)) := by
  obtain ⟨B, hX⟩ := BigEtaleSite.exists_contains X
  have : IsIso (strictHenselizationBaseChangeToStrictHenselization B hX (genericPointInclusion X)
      (Scheme.genericGeometricPoint X)) :=
    isIso_strictHenselizationBaseChangeToStrictHenselization_fromSpecStalk B hX
      (genericPoint X) (Scheme.genericGeometricPoint X) (Scheme.genericPointInclusion_apply X _)
  exact isIso_smallEtaleStalkAb_map_unit_of_isIso B hX (genericPointInclusion X)
    (Scheme.genericGeometricPoint X) F

/-- **The unit of `η^* ⊣ η_*` at the separably closed generic geometric point**
`η̄ : Spec K^sep ⟶ X`: the unit `F ⟶ η_* η^* F` induces an isomorphism `F_η̄ ≅ (η_* η^* F)_η̄`. -/
@[weil "lem_fk105_generic_adjunction_iso_at_generic_point"]
theorem isIso_sheafFiber_map_genericPointInclusion_unit_genericSepClosedPoint
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    IsIso ((Scheme.pointSmallEtale (Scheme.genericSepClosedPoint X)).sheafFiber.map
      ((smallEtaleAdjunctionAb (genericPointInclusion X)).unit.app F)) := by
  let e := Scheme.pointSmallEtaleGenericIso X
  let i : (Scheme.pointSmallEtale (Scheme.genericSepClosedPoint X)).sheafFiber (A := Ab.{u + 1}) ≅
      (Scheme.pointSmallEtale (Scheme.genericGeometricPoint X).hom).sheafFiber :=
    { hom := e.hom.sheafFiber
      inv := e.inv.sheafFiber
      hom_inv_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.inv_hom_id,
          GrothendieckTopology.Point.Hom.sheafFiber_id]
      inv_hom_id := by
        rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.hom_inv_id,
          GrothendieckTopology.Point.Hom.sheafFiber_id] }
  exact (NatIso.isIso_map_iff i _).2 (isIso_smallEtaleStalkAb_map_genericPointInclusion_unit X F)

end GenericPoint

end AlgebraicGeometry
