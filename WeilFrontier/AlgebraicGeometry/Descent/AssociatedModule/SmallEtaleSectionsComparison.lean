module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSectionsComparison
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtaleSheaf
public import WeilFrontier.Defs.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.Modules.LocallyTrivialSections
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local

/-!
# The étale presheaf of a quasi-coherent module is a sheaf

Let `S` be a locally noetherian scheme and `M` a quasi-coherent `𝒪_S`-module. The presheaf
`M_et : (u : U ⟶ S) ↦ Γ(U, u^* M)` on the étale category `Et(S)` of noetherian separated étale
`S`-schemes is an étale sheaf: it is a sheaf for the étale topology of `Et(S)`, equivalently its
underlying presheaf of sets satisfies the conditions a) (finite disjoint unions) and b) (descent
along surjective morphisms) of an étale sheaf.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isSheaf_quasicoherentPresheaf`: `M_et` is a
  sheaf for `AlgebraicGeometry.SmallNoetherianSeparatedEtale.topology`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isEtaleSheaf_quasicoherentPresheaf`: the
  underlying presheaf of sets of `M_et` satisfies the conditions a) and b).
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.quasicoherentEtaleSheaf`: `M_et` as an object
  of the category `AlgebraicGeometry.EtaleSheaf B S hS AddCommGrpCat` of étale sheaves.

## Implementation notes

The descent argument (faithfully flat descent for modules along an étale surjection, first for
affine schemes, then by Zariski gluing) is the sheaf property of `M_et` on the small étale site,
`AlgebraicGeometry.SmallEtale.isSheaf_quasicoherentPresheaf` ([Stacks, Tag 03DT]). Since `S` is
locally noetherian, `Et(S)` is a dense subsite of the small étale site, so the inclusion is
continuous and the restriction of a sheaf to `Et(S)` is a sheaf. The hypothesis that `S` is
locally noetherian is the standing assumption that all schemes are noetherian.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.5][FreitagKiehl]
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent] [IsLocallyNoetherian S]

/-- **The étale presheaf of a quasi-coherent module is a sheaf** for the étale topology of
`Et(S)`, `S` locally noetherian. -/
@[weil "prop_fk102_quasicoherent_etale_is_sheaf"]
theorem isSheaf_quasicoherentPresheaf :
    Presheaf.IsSheaf (topology B S hS) (quasicoherentPresheaf B S hS F) :=
  (inclusion B S hS).op_comp_isSheaf (topology B S hS) (SmallEtale.topology B S hS)
    ⟨_, SmallEtale.isSheaf_quasicoherentPresheaf B S hS F⟩

/-- **The étale presheaf of a quasi-coherent module is an étale sheaf**: its underlying presheaf
of sets satisfies the conditions a) (finite disjoint unions) and b) (descent along surjective
morphisms) of an étale sheaf on `Et(S)`, `S` locally noetherian. -/
@[weil "prop_fk102_quasicoherent_etale_is_sheaf"]
theorem isEtaleSheaf_quasicoherentPresheaf :
    EtalePresheaf.IsEtaleSheaf (quasicoherentPresheaf B S hS F ⋙ forget AddCommGrpCat) :=
  (EtalePresheaf.isSheaf_topology_iff_isEtaleSheaf_forget _).mp
    (isSheaf_quasicoherentPresheaf B S hS F)

/-- The étale sheaf `M_et` of a quasi-coherent module `M`, as an object of the category of
étale sheaves of abelian groups on `Et(S)`. -/
abbrev quasicoherentEtaleSheaf : EtaleSheaf B S hS AddCommGrpCat.{u} :=
  ⟨quasicoherentPresheaf B S hS F, isSheaf_quasicoherentPresheaf B S hS F⟩

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

end

/-! ### The étale module of a Zariski line bundle -/

/-!
# The étale module of a Zariski line bundle

Let `S` be a scheme and `L` a quasi-coherent `𝒪_S`-module. Its étale module `L_et` is the
`𝒪_{S,et}`-module `(u : V ⟶ S) ↦ Γ(V, u^* L)` on the small étale site of `S`. If `U` is an open
of `S` and `e ∈ L(U)` corresponds to `1` under a trivialization `L|_U ≅ 𝒪_U`, then the pull-back
of `e` to the open subscheme `U` is a generator of `L_et` over `U`: for every étale `g : V ⟶ U`
the map `Γ(V, 𝒪_V) → L_et(V)`, `a ↦ a • e|_V`, is bijective, because `g^*(L|_U) ≅ g^* 𝒪_U ≅ 𝒪_V`
carries `e|_V` to `1`.

Consequently a Zariski covering `(X k)ₖ` of `S` with generators `e k ∈ L(X k)` of
`L|_{X k} ≅ 𝒪_{X k}` is a trivialization of `L_et`, and its transition family is the Zariski
transition family of `L`: if `e k = g • e l` on `X k ⊓ X l`, then the same relation holds for
the restrictions of the étale generators to `X k ⊓ X l` (which is the fibre product of `X k` and
`X l` over `S`). In particular `L_et` is an étale line bundle whenever `L` is invertible.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionOfOpen`: the section of `L_et` over an open `U` given by
  a section of `L` over `U`.
* `AlgebraicGeometry.SmallEtale.zariskiTrivialization`: the trivialization of `L_et` given by a
  Zariski covering of `S` with generators of `L` over its members.

## Main results

* `AlgebraicGeometry.bijective_smul_pullbackSectionHom_of_iso`: the pull-back of a generator of
  a trivial module along any morphism of schemes generates the global sections of the pull-back.
* `AlgebraicGeometry.SmallEtale.isGenerator_sectionOfOpen`: a Zariski generator of `L` over `U`
  is a generator of `L_et` over `U`.
* `AlgebraicGeometry.SmallEtale.zariskiTrivialization_transition`: the transition family of the
  trivialization `zariskiTrivialization` is the Zariski transition family of `L`.
* `AlgebraicGeometry.SmallEtale.isEtaleLineBundle_sectionsSheafOfModules`: the étale module of
  an invertible `𝒪_S`-module is an étale line bundle.

## Implementation notes

`L_et` is `AlgebraicGeometry.SmallEtale.sectionsSheafOfModules`, the pull-back-sections presheaf
of modules of [Stacks, Tag 03DS] with its sheaf condition [Stacks, Tag 03DT]; its underlying
abelian presheaf is `AlgebraicGeometry.SmallEtale.quasicoherentPresheaf` by definition
(`AlgebraicGeometry.SmallEtale.sectionsSheafOfModules_val_presheaf`). A generator `e ∈ L(U)` of
`L|_U ≅ 𝒪_U` is recorded as a trivialization `t : L.restrict U.ι ≅ 𝒪_U` together with a section
`e` of `L` over `U` whose restriction to `U.ι ''ᵁ ⊤ = U` is `t⁻¹(1)`, i.e. `e` is the image of `1`.
"Invertible" is invertibility for the tensor product ([Stacks, Tag 01CR]); on a scheme it gives
local trivializations by [Stacks, Tag 0B8M].

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The pull-back of a generator is a generator on global sections.** If `s` is the section
of `M` corresponding to `1` under a trivialization `M ≅ 𝒪_T`, then for every morphism of schemes
`g : V ⟶ T` the map `Γ(V, 𝒪_V) → Γ(V, g^* M)`, `a ↦ a • g^* s`, is bijective. -/
theorem bijective_smul_pullbackSectionHom_of_iso {T V : Scheme.{u}} (g : V ⟶ T) (M : T.Modules)
    (e : M ≅ SheafOfModules.unit T.ringCatSheaf) :
    Function.Bijective (fun a : Γ(V, ⊤) =>
      a • pullbackSectionHom g M ⊤ ⊤ le_top (e.inv.app ⊤ (1 : Γ(T, ⊤)))) := by
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have : (Opens.map g.base).Final := Stacks.AlgebraicGeometry.AffineQcohEquivalence.final_opensMap _
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal g.toRingCatSheafHom
  set s := e.inv.app ⊤ (1 : Γ(T, ⊤)) with hs
  let ψ : Γ((Scheme.Modules.pullback g).obj M, ⊤) → Γ(V, ⊤) := fun x =>
    (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom).val.app (op (g ⁻¹ᵁ ⊤))
      (((Scheme.Modules.pullback g).map e.hom).app (g ⁻¹ᵁ ⊤) x)
  have hψinj : Function.Injective ψ := by
    let P := SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom
    have : IsIso P.val := Functor.map_isIso (SheafOfModules.forget _) P
    have : IsIso (P.val.app (op (g ⁻¹ᵁ ⊤))) :=
      Functor.map_isIso (PresheafOfModules.evaluation _ (op (g ⁻¹ᵁ ⊤))) P.val
    have := e.isIso_hom
    have : IsIso ((Scheme.Modules.pullback g).map e.hom) :=
      Functor.map_isIso (Scheme.Modules.pullback g) e.hom
    exact (ConcreteCategory.bijective_of_isIso (P.val.app (op (g ⁻¹ᵁ ⊤)))).injective.comp
      (ConcreteCategory.bijective_of_isIso
        (((Scheme.Modules.pullback g).map e.hom).app (g ⁻¹ᵁ ⊤))).injective
  have hψs : ψ (pullbackSectionHom g M ⊤ ⊤ le_top s) = 1 := by
    have h := Stacks.Divisors.pullbackGlobalSections_frame_appTop g M e s
    refine h.trans ?_
    have h1 : (e.hom.app ⊤) ((e.inv.app ⊤) (1 : Γ(T, ⊤))) = (1 : Γ(T, ⊤)) := by
      exact congrArg (fun φ : (SheafOfModules.unit T.ringCatSheaf : T.Modules) ⟶
          (SheafOfModules.unit T.ringCatSheaf : T.Modules) =>
        Scheme.Modules.Hom.app φ ⊤ (1 : Γ(T, ⊤))) e.inv_hom_id
    rw [hs, h1]
    exact (Scheme.Hom.app g ⊤).hom.map_one
  have hψsmul : ∀ (a : Γ(V, ⊤)) x, ψ (a • x) = a * ψ x := by
    intro a x
    have h1 := Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullback g).map e.hom)
      (U := g ⁻¹ᵁ ⊤) a x
    have h2 := ((SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom).val.app
      (op (g ⁻¹ᵁ ⊤))).hom.map_smul a
      (((Scheme.Modules.pullback g).map e.hom).app (g ⁻¹ᵁ ⊤) x)
    exact (congrArg _ h1).trans h2
  refine ⟨fun a b hab => ?_, fun n => ⟨ψ n, hψinj ?_⟩⟩
  · have := congrArg ψ hab
    simp only [hψsmul, hψs, mul_one] at this
    exact this
  · simp only [hψsmul, hψs, mul_one]

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- Under `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, the restriction of a
section `e` of `L` over `U` to `U.ι ''ᵁ ⊤` is the pull-back of `e` to the open subscheme `U`. -/
lemma restrictFunctorIsoPullback_hom_app_app_top (L : X.Modules) (U : X.Opens)
    (e : Γ(L, U)) :
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app L).app ⊤
        (L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op e) =
      pullbackSectionHom U.ι L U ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) e := by
  have h := CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.restrictAdjunction U.ι) (Scheme.Modules.pullbackPushforwardAdjunction U.ι) L
  have h' := congrArg (fun ψ => (Scheme.Modules.Hom.app ψ U) e) h
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at h'
  let θ := (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app L
  have hn := ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf θ).naturality
    (homOfLE (Scheme.Opens.top_le_ι_preimage (V := U) (U := U) le_rfl)).op)
    (L.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op e)
  have h3 : ((Scheme.Modules.restrictFunctor U.ι).obj L).presheaf.map
      (homOfLE (Scheme.Opens.top_le_ι_preimage (V := U) (U := U) le_rfl)).op
        (L.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op e) =
      L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op e := by
    exact (PresheafOfModules.map_comp_apply L.val
      (homOfLE (U.ι.image_preimage_le U)).op
      (homOfLE (U.ι.image_mono (Scheme.Opens.top_le_ι_preimage (V := U) (U := U) le_rfl))).op
      e).symm.trans (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _)
  refine (congrArg (fun z => θ.app ⊤ z) h3).symm.trans ?_
  refine hn.trans ?_
  exact congrArg (fun z => ((Scheme.Modules.pullback U.ι).obj L).presheaf.map
    (homOfLE (Scheme.Opens.top_le_ι_preimage (V := U) (U := U) le_rfl)).op z) h'

end Scheme.Modules

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (L : S.Modules) [L.IsQuasicoherent]

/-- The underlying abelian presheaf of `L_et` is the étale presheaf `M_et` of `L`. -/
lemma sectionsSheafOfModules_val_presheaf :
    (sectionsSheafOfModules B S hS L).val.presheaf = quasicoherentPresheaf B S hS L :=
  rfl

/-- The section of `L_et` over an open `U` of `S` given by a section `e ∈ L(U)`: its pull-back
to the open subscheme `U`. -/
def sectionOfOpen (U : S.Opens) (e : Γ(L, U)) :
    (sectionsSheafOfModules B S hS L).val.obj (op ((opensToSmallEtale B S hS).obj U)) :=
  pullbackSectionHom U.ι L U ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) e

/-- The module structure of `L_et` over `V` is that of the global sections of the pull-back of
`L` to `V`. -/
lemma smul_sectionsSheafOfModules (V : SmallEtale B S hS)
    (r : (structureSheaf B S hS).obj.obj (op V))
    (m : (sectionsSheafOfModules B S hS L).val.obj (op V)) :
    r • m = (show (sectionsSheafOfModules B S hS L).val.obj (op V) from
      ((show Γ(((toOver B S hS).obj V).left, ⊤) from r) •
        (show Γ((Scheme.Modules.pullback ((toOver B S hS).obj V).hom).obj L, ⊤) from m))) :=
  rfl

/-- **A Zariski generator is an étale generator.** If `e ∈ L(U)` corresponds to `1` under a
trivialization `t : L|_U ≅ 𝒪_U`, then its pull-back `sectionOfOpen L U e` generates `L_et` over
`U`: for every arrow `V ⟶ U` of the small étale site, `a ↦ a • e|_V` is a bijection
`Γ(V, 𝒪_V) → L_et(V)`. -/
theorem isGenerator_sectionOfOpen (U : S.Opens) (e : Γ(L, U))
    (t : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (ht : t.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)) =
      L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op e) :
    IsGenerator (sectionsSheafOfModules B S hS L) ((opensToSmallEtale B S hS).obj U)
      (sectionOfOpen L U e) := by
  intro V f
  let F := (toOver B S hS).map f
  let g := F.left
  let θ := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L
  let M := (Scheme.Modules.pullback U.ι).obj L
  let e' : M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf := θ.symm ≪≫ t
  have he' : e'.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)) =
      pullbackSectionHom U.ι L U ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) e := by
    change θ.hom.app ⊤ (t.inv.app ⊤ (1 : Γ(U.toScheme, ⊤))) = _
    rw [ht]
    exact Scheme.Modules.restrictFunctorIsoPullback_hom_app_app_top L U e
  have hB := bijective_smul_pullbackSectionHom_of_iso g M e'
  let Θ₁ := ((Scheme.Modules.pullbackComp g U.ι).hom.app L).app ⊤
  let Θ₂ := ((Scheme.Modules.pullbackCongr (Over.w F)).hom.app L).app ⊤
  have hmap : (sectionsSheafOfModules B S hS L).val.map f.op (sectionOfOpen L U e) =
      Θ₂ (Θ₁ (pullbackSectionHom g M ⊤ ⊤ le_top
        (e'.inv.app ⊤ (1 : Γ(U.toScheme, ⊤))))) := by
    refine (pullbackSectionsMap_eq_comp L F le_top _).trans ?_
    rw [he']
    rfl
  have hΘ₁ : Function.Bijective Θ₁ := ConcreteCategory.bijective_of_isIso _
  have hΘ₂ : Function.Bijective Θ₂ := ConcreteCategory.bijective_of_isIso _
  rw [hmap]
  set x := pullbackSectionHom g M ⊤ ⊤ le_top (e'.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)))
  have key : ∀ a : (structureSheaf B S hS).obj.obj (op V),
      a • @id ((sectionsSheafOfModules B S hS L).val.obj (op V)) (Θ₂ (Θ₁ x)) =
        (Θ₂ ∘ Θ₁) ((show Γ(((toOver B S hS).obj V).left, ⊤) from a) • x) := by
    intro a
    have h1 : Θ₁ ((show Γ(((toOver B S hS).obj V).left, ⊤) from a) • x) =
        (show Γ(((toOver B S hS).obj V).left, ⊤) from a) • Θ₁ x :=
      Scheme.Modules.Hom.app_smul _ _ x
    have h2 : Θ₂ ((show Γ(((toOver B S hS).obj V).left, ⊤) from a) • Θ₁ x) =
        (show Γ(((toOver B S hS).obj V).left, ⊤) from a) • Θ₂ (Θ₁ x) :=
      Scheme.Modules.Hom.app_smul _ _ _
    exact (smul_sectionsSheafOfModules L V a _).trans (h2.symm.trans (congrArg Θ₂ h1.symm))
  have hb := (hΘ₂.comp hΘ₁).comp hB
  refine ⟨fun a b hab => hb.1 ((key a).symm.trans (hab.trans (key b))), fun y => ?_⟩
  obtain ⟨a, ha⟩ := hb.2 y
  exact ⟨a, (key a).trans ha⟩

variable {K : Type u} (X : K → S.Opens) (hX : ⨆ k, X k = ⊤)
  (t : ∀ k, L.restrict (X k).ι ≅ SheafOfModules.unit (X k).toScheme.ringCatSheaf)
  (e : ∀ k, Γ(L, X k))
  (ht : ∀ k, (t k).inv.app ⊤ (1 : Γ((X k).toScheme, ⊤)) =
    L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (X k)).le).op (e k))

/-- **The trivialization of `L_et` given by a Zariski trivialization of `L`.** For an open
covering `(X k)ₖ` of `S` and generators `e k ∈ L(X k)` of `L|_{X k} ≅ 𝒪_{X k}` (the images of
`1` under trivializations `t k`), the open immersions `X k ⟶ S` form a covering of `S` in its
small étale site, and the pull-backs of the `e k` are generators of `L_et` over its members. -/
@[weil "lem_fk102_zariski_line_bundle_etale"]
def zariskiTrivialization : LineBundleTrivialization (sectionsSheafOfModules B S hS L) where
  ι := ULift.{u + 1} K
  obj k := (opensToSmallEtale B S hS).obj (X k.down)
  hom k := (finalIsTerminal B S hS).from _
  ofArrows_mem_topology := by
    have h := coversTop_opensToSmallEtale_ulift B S hS X
      ((Opens.coversTop_iff (T := S) X).mpr hX) (final B S hS)
    refine (topology B S hS).superset_covering ?_ h
    rintro Z f ⟨i, ⟨a⟩⟩
    rw [(finalIsTerminal B S hS).hom_ext f (a ≫ (finalIsTerminal B S hS).from _)]
    exact Sieve.downward_closed _
      (Sieve.ofArrows_mk (fun k : ULift.{u + 1} K => (opensToSmallEtale B S hS).obj (X k.down))
        (fun k => (finalIsTerminal B S hS).from _) i) a
  generator k := sectionOfOpen L (X k.down) (e k.down)
  isGenerator k := isGenerator_sectionOfOpen L _ _ (t k.down) (ht k.down)

/-- The generator of `zariskiTrivialization` over `X k` is the pull-back of `e k`. -/
@[simp]
lemma zariskiTrivialization_generator (k : K) :
    (zariskiTrivialization (B := B) (hS := hS) L X hX t e ht).generator ⟨k⟩ =
      sectionOfOpen L (X k) (e k) :=
  rfl

/-- The restriction of `sectionOfOpen L U e` to a smaller open `W ≤ U` is the pull-back of
`e|_W`. -/
lemma map_sectionOfOpen {U W : S.Opens} (h : W ≤ U) (e : Γ(L, U)) :
    (sectionsSheafOfModules B S hS L).val.map ((opensToSmallEtale B S hS).map (homOfLE h)).op
        (sectionOfOpen L U e) =
      sectionOfOpen L W (L.presheaf.map (homOfLE h).op e) := by
  refine (pullbackSectionsMap_pullbackSectionHom L
    ((toOver B S hS).map ((opensToSmallEtale B S hS).map (homOfLE h))) U
    (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage h) e).trans ?_
  exact (pullbackSectionHom_map W.ι L U W h ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl)
    (Scheme.Opens.top_le_ι_preimage h) e).symm

/-- If `e = g • e'` on `U ⊓ U'` in `L`, then the same relation holds in `L_et` between the
restrictions of the pull-backs of `e` and `e'` to the open `U ⊓ U'`, with `g` read as a function
on the open subscheme `U ⊓ U'`. -/
theorem map_sectionOfOpen_inf_left_eq_smul {U U' : S.Opens} (e : Γ(L, U)) (e' : Γ(L, U'))
    (g : Γ(S, U ⊓ U'))
    (hg : L.presheaf.map (homOfLE inf_le_left).op e =
      g • L.presheaf.map (homOfLE inf_le_right).op e') :
    (sectionsSheafOfModules B S hS L).val.map
        ((opensToSmallEtale B S hS).map (homOfLE (inf_le_left : U ⊓ U' ≤ U))).op
        (sectionOfOpen L U e) =
      (show (structureSheaf B S hS).obj.obj (op ((opensToSmallEtale B S hS).obj (U ⊓ U'))) from
        (U ⊓ U').ι.appLE (U ⊓ U') ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) g) •
      (sectionsSheafOfModules B S hS L).val.map
        ((opensToSmallEtale B S hS).map (homOfLE (inf_le_right : U ⊓ U' ≤ U'))).op
        (sectionOfOpen L U' e') := by
  rw [map_sectionOfOpen, map_sectionOfOpen]
  refine Eq.trans ?_ (smul_sectionsSheafOfModules L _ _ _).symm
  refine (congrArg (pullbackSectionHom (U ⊓ U').ι L (U ⊓ U') ⊤
    (Scheme.Opens.top_le_ι_preimage le_rfl)) hg).trans ?_
  exact pullbackSectionHom_smul _ L _ ⊤ _ g _

/-- **The transition family of `zariskiTrivialization` is the Zariski one.** If `g` is the
Zariski transition function of `L` on `X k ⊓ X l`, i.e. `e k = g • e l` there, then on the
fibre product `X k ⊓ X l` of `X k` and `X l` over `S` the generators of `L_et` satisfy
`e k = g • e l` as well. -/
@[weil "lem_fk102_zariski_line_bundle_etale"]
theorem zariskiTrivialization_transition (k l : K) (g : Γ(S, X k ⊓ X l))
    (hg : L.presheaf.map (homOfLE inf_le_left).op (e k) =
      g • L.presheaf.map (homOfLE inf_le_right).op (e l)) :
    (sectionsSheafOfModules B S hS L).val.map
        ((opensToSmallEtale B S hS).map (homOfLE (inf_le_left : X k ⊓ X l ≤ X k))).op
        ((zariskiTrivialization (B := B) (hS := hS) L X hX t e ht).generator ⟨k⟩) =
      (show (structureSheaf B S hS).obj.obj
          (op ((opensToSmallEtale B S hS).obj (X k ⊓ X l))) from
        (X k ⊓ X l).ι.appLE (X k ⊓ X l) ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) g) •
      (sectionsSheafOfModules B S hS L).val.map
        ((opensToSmallEtale B S hS).map (homOfLE (inf_le_right : X k ⊓ X l ≤ X l))).op
        ((zariskiTrivialization (B := B) (hS := hS) L X hX t e ht).generator ⟨l⟩) :=
  map_sectionOfOpen_inf_left_eq_smul L (e k) (e l) g hg

end SmallEtale

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A locally trivial `𝒪_S`-module has, near every point, an open `U`, a trivialization
`L|_U ≅ 𝒪_U` and a section `e ∈ L(U)` which it sends to `1`. -/
lemma exists_trivialization_of_onSpace_isInvertible (L : S.Modules)
    [h : AlgebraicGeometry.SheafOfModules.OnSpace.IsInvertible L] (x : S) :
    ∃ (U : S.Opens) (_ : x ∈ U)
      (t : L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (e : Γ(L, U)),
      t.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)) =
        L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op e := by
  obtain ⟨U₀, hxU, ⟨t⟩⟩ := h.locally_iso x
  let U : S.Opens := U₀
  let t' := Stacks.AlgebraicGeometry.TwistMapsInvertible.restrictIsoUnitOfOverIsoUnit L U t
  have : IsIso (L.presheaf.map (homOfLE ((Scheme.Opens.ι_image_top U).le)).op) :=
    Scheme.Modules.isIso_presheaf_map_of_eq L ((Scheme.Opens.ι_image_top U).le) (by simp)
  have hb := ConcreteCategory.bijective_of_isIso
    (L.presheaf.map (homOfLE ((Scheme.Opens.ι_image_top U).le)).op)
  obtain ⟨e, he⟩ := hb.2 (t'.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)))
  exact ⟨U, hxU, t', e, he.symm⟩

/-- **The étale module of an invertible `𝒪_S`-module is an étale line bundle.** -/
@[weil "lem_fk102_zariski_line_bundle_etale"]
theorem isEtaleLineBundle_sectionsSheafOfModules (L : S.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L] :
    IsEtaleLineBundle B S hS (sectionsSheafOfModules B S hS L) := by
  have := Stacks.LocallyTrivial.onSpace_isInvertible_of_isInvertible L
  choose U hU t e ht using exists_trivialization_of_onSpace_isInvertible L
  have hX : ⨆ x, U x = ⊤ := eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact (isEtaleLineBundle_iff_nonempty_trivialization _).mpr
    ⟨zariskiTrivialization L U hX t e ht⟩

end SmallEtale

end AlgebraicGeometry
