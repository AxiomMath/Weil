module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.OpenProperExchangeMapDerived
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import WeilFrontier.Defs.AlgebraicGeometry.Flatness.Flattening.CompactificationDominates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.DerivedCoefficientUniverse
public import Weil.Attr

/-!
# Extension by zero along a dominating compactification

Let `f : X ⟶ S` be a morphism of schemes and let `c₂ = (X̄, j, f̄)` and `c₁ = (X̄', i, f̄ ∘ g)`
be compactifications of `f`, the second dominating the first through `g : X̄' ⟶ X̄`, so that
`g ∘ i = j`. Then `g` is proper, and for a bounded below complex `F` of sheaves of `Λ`-modules
on the small étale site of `X` with torsion cohomology sheaves, the morphism
`(*) : j_! F ⟶ Rg_*(i_! F)` of the square `g ∘ i = j ∘ 𝟙_X` is an isomorphism in `D⁺(X̄)`.

The proof has two steps.

* For every sheaf `G` on `X` the exchange morphism `α_G : j_! G ⟶ g_* i_! G` is an
  isomorphism. Its adjoint `G ⟶ (g_* i_! G)|_X` sends a section `s` over `V` to the section
  `t(s)` of `i_! G` over `A_V = V ×_B A` which is `ι(s)` on the open and closed part `X_V` and
  zero on its complement `R_V`; the complement lies over the complement of `i(X)`, where `i_! G`
  vanishes, and `ι` is bijective since the unit `G ⟶ (i_! G)|_X` is invertible. Moreover
  `g_* i_! G` vanishes away from `j(X)` ([Stacks, Tag 0A3U]), so it is the extension by zero of
  its restriction to `X`.
* If `u : i_! F ⟶ J` is an injective resolution, `(*)` is represented by the exchange chain map
  `θ_J : j_! (J|_X) ⟶ g_* J`. By naturality of `θ`, `θ_J ∘ j_!(u|_X) = g_*(u) ∘ θ_{i_! F}`; the
  map `θ_{i_! F}` is termwise `α` followed by the invertible counit `i_! ((i_! F)|_X) ⟶ i_! F`,
  and `g_*(u)` is a quasi-isomorphism because `i_! F` is acyclic for `Rg_*`: the composition
  comparison `R(g_* ∘ i_!) ⟶ Rg_* ∘ Ri_!` is invertible on `D⁺_tors` ([Stacks, Tag 0F7G]).

## Main results

* `AlgebraicGeometry.isIso_openProperExchangeMap_of_refinement`: `α_G` is an isomorphism.
* `AlgebraicGeometry.isIso_openProperExchangeDerivedMap_of_refinement`: `(*)` is an isomorphism
  for open immersions `i`, `j` and a proper `g` with `i ≫ g = j`.
* `AlgebraicGeometry.Scheme.Hom.Compactification.isProper_map`: the morphism of a domination
  of compactifications is proper.
* `AlgebraicGeometry.isIso_openProperExchangeDerivedMap_of_hom`: the case of a domination of
  compactifications.

## Implementation notes

The sheaves are sheaves of `Λ`-modules on Mathlib's small étale sites, for a ring `Λ` in any
universe, as for `AlgebraicGeometry.openProperExchangeDerivedMap`; the source's abelian sheaves
are the case `Λ = ℤ`. The objects of `D⁺_tors(X)` are presented as bounded below complexes `F`
whose image in `D⁺(X)` satisfies `Stacks.EtaleCohomology.isTorsionPlus`, and the morphism `(*)`
is computed with an arbitrary injective resolution of `i_! F`, of which it does not depend
(`AlgebraicGeometry.openProperExchangeDerivedMap_eq_of_resolution`).

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.6.
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale Stacks.EtaleCohomology AlgebraicGeometry.ExchangeSquare

universe r u

namespace AlgebraicGeometry

section Exchange

variable (Λ : Type r) [Ring Λ] {X A B : Scheme.{u}} (i : X ⟶ A) [IsOpenImmersion i]
  (j : X ⟶ B) [IsOpenImmersion j] {g : A ⟶ B} (h : i ≫ g = 𝟙 X ≫ j)

/-- Sections of `i_! G` over an object whose image misses that of `i` vanish. -/
private lemma subsingleton_extensionByZero_obj_of_disjoint (G : EtaleModules.{u, r} Λ X)
    (W : A.Etale) (hW : Disjoint (Set.range W.hom.base) (Set.range i.base)) :
    Subsingleton (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.obj (op W)) := by
  have : Etale W.hom := W.prop
  set S := (etaleModuleExtensionByZero.{u, r} Λ i).obj G
  have h0 := isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ W.hom i hW G
  have h1 : IsZero ((etaleModuleRestriction.{u, r} Λ W.hom).obj S) :=
    h0.of_iso ((etaleModuleInverseImageRestrictionIso.{u, r} Λ W.hom).symm.app _)
  have h2 : IsZero (((etaleModuleRestriction.{u, r} Λ W.hom).obj S).obj.obj
      (op (Scheme.Etale.mk (𝟙 W.left)))) :=
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 W.left)))).map_isZero h1
  have h3 : IsZero (S.obj.obj (op W)) :=
    h2.of_iso (S.obj.mapIso (smallEtaleComposeIdIso W).op)
  exact ModuleCat.subsingleton_of_isZero h3

variable [IsProper g]

/-- The complement `R_V` of the image of `X_V` in `A_V` lies over the complement of `X` in `A`. -/
private lemma disjoint_range_complementObj_hom {V : B.Etale} (φ : V ⟶ smallEtaleSource j) :
    Disjoint (Set.range (complementObj i j h φ).hom.base) (Set.range i.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨y, rfl⟩ hy
  have hy' : (complementOpens i j h φ).ι y ∈
      Set.range (pullback.fst (pullback.snd V.hom g) i) := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact hy
  obtain ⟨w, hw⟩ := hy'
  have hc : (pullback.fst (pullback.snd V.hom g) i ≫ pullback.fst V.hom g) ≫ φ.left =
      pullback.snd (pullback.snd V.hom g) i ≫ 𝟙 X := by
    apply (cancel_mono j).1
    have e1 := left_comp_eq_hom j φ
    have e2 := pullback.condition (f := V.hom) (g := g)
    have e3 := pullback.condition (f := pullback.snd V.hom g) (g := i)
    calc ((pullback.fst (pullback.snd V.hom g) i ≫ pullback.fst V.hom g) ≫ φ.left) ≫ j
        = pullback.fst (pullback.snd V.hom g) i ≫ pullback.fst V.hom g ≫ V.hom := by
          rw [← e1]; rfl
      _ = (pullback.fst (pullback.snd V.hom g) i ≫ pullback.snd V.hom g) ≫ g := by
          rw [e2, Category.assoc]
      _ = (pullback.snd (pullback.snd V.hom g) i ≫ 𝟙 X) ≫ j := by
          rw [e3, Category.assoc, h]; simp
  let m := pullback.lift _ _ hc
  have hm : m ≫ inclusionLeft i j h φ = pullback.fst (pullback.snd V.hom g) i := by
    apply pullback.hom_ext
    · rw [Category.assoc, inclusionLeft_fst]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, inclusionLeft_snd, ← Category.assoc]
      exact (congrArg (· ≫ i) (pullback.lift_snd _ _ hc)).trans pullback.condition.symm
  have hx : (complementOpens i j h φ).ι y ∈ Set.range (inclusionLeft i j h φ).base := by
    refine ⟨m w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hm, hw]
  have hy2 : (complementOpens i j h φ).ι y ∈ (complementOpens i j h φ : Set _) := by
    rw [← Scheme.Opens.range_ι]; exact ⟨y, rfl⟩
  exact hy2 hx

omit [IsProper g] in
/-- The section map `s ↦ ι(s)`, `G(U) ⟶ (i_! G)(U)`, is bijective for an open immersion `i`. -/
private lemma bijective_extensionByZeroSectionLinearMap (G : EtaleModules.{u, r} Λ X)
    (U : X.Etale) : Function.Bijective (extensionByZeroSectionLinearMap Λ i G U) := by
  have e := ι_comp_extensionByZeroPresheafToSheaf_app Λ i G ((smallEtaleCompose i).obj U)
    (structureHomToSource i U)
  have : IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app G) := inferInstance
  have : IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app G).hom :=
    (sheafToPresheaf _ _).map_isIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app G)
  have : IsIso (((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app G).hom.app
      (op (sourceDescend i (structureHomToSource i U))) ≫
        ((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map
          (sourceDescendIso i (structureHomToSource i U)).inv.op) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _) (Functor.map_isIso _ _)
  have hb := (ConcreteCategory.isIso_iff_bijective _).1 this
  rw [← e] at hb
  exact hb

/-- The glued section map `s ↦ t(s)` is bijective: the sections of `i_! G` over `A_V` are those
over `X_V`, where `ι` is bijective, together with those over the complement, which vanish. -/
private lemma bijective_exchangeGlue (G : EtaleModules.{u, r} Λ X) {V : B.Etale}
    (φ : V ⟶ smallEtaleSource j) : Function.Bijective (exchangeGlue Λ i j h G φ) := by
  have hι := bijective_extensionByZeroSectionLinearMap Λ i G (sourceObj j (𝟙 X) φ)
  have hsub := subsingleton_extensionByZero_obj_of_disjoint Λ i G (complementObj i j h φ)
    (disjoint_range_complementObj_hom i j h φ)
  unfold exchangeGlue
  rw [LinearMap.coe_comp]
  refine (LinearEquiv.bijective _).comp ⟨fun a b hab => hι.1 (congrArg Prod.fst hab), fun p => ?_⟩
  obtain ⟨s, hs⟩ := hι.2 p.1
  exact ⟨s, Prod.ext hs (@Subsingleton.elim _ hsub _ _)⟩

/-- **The exchange morphism of a refinement is an isomorphism.** For open immersions `i : X ⟶ A`,
`j : X ⟶ B` and a proper `g : A ⟶ B` with `i ≫ g = j`, the exchange morphism
`α_G : j_! G ⟶ g_* i_! G` of the square `i ≫ g = 𝟙 ≫ j` is invertible: its adjoint
`G ⟶ (g_* i_! G)|_X` is `s ↦ t(s)`, which is bijective, and `g_* i_! G` vanishes away from `X`,
so it is the extension by zero of its restriction to `X`. -/
theorem isIso_openProperExchangeMap_of_refinement (G : EtaleModules.{u, r} Λ X) :
    IsIso (openProperExchangeMap Λ i j h G) := by
  set M := (etaleModuleDirectImage.{u, r} Λ (𝟙 X)).obj G
  set N := (etaleModuleDirectImage.{u, r} Λ g).obj
    ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)
  set adj := etaleModuleExtensionByZeroAdj.{u, r} Λ j
  set β := (adj.homEquiv M N) (openProperExchangeMap Λ i j h G) with hβdef
  have hα : openProperExchangeMap Λ i j h G =
      (etaleModuleExtensionByZero.{u, r} Λ j).map β ≫ adj.counit.app N := by
    calc openProperExchangeMap Λ i j h G = (adj.homEquiv M N).symm β := by
          rw [hβdef, Equiv.symm_apply_apply]
      _ = _ := adj.homEquiv_counit _ _ _
  have hij : i ≫ g = j := h.trans (Category.id_comp j)
  have hik : Set.range j.base = (Set.range (openImmersionComplementι j).base)ᶜ := by
    rw [range_openImmersionComplementι, compl_compl]
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ
    (openImmersionComplementι j) j hik N
  have h₃ : IsIso (adj.counit.app N) :=
    hS.isIso_f_iff.2 ((etaleModuleDirectImage.{u, r} Λ (openImmersionComplementι j)).map_isZero
      (isZero_etaleModuleInverseImage_directImage_extensionByZero_univ Λ hij G))
  have hβ : ∀ U : X.Etale, Function.Bijective (β.hom.app (op U)) := by
    intro U
    have hinv : (sourceDescendIso j (structureHomToSource j U)).inv = 𝟙 _ := by
      ext1; rfl
    have e := ι_comp_extensionByZeroPresheafToSheaf_app Λ j M ((smallEtaleCompose j).obj U)
      (structureHomToSource j U)
    rw [hinv] at e
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at e
    have hβU : β.hom.app (op U) = (adj.unit.app M).hom.app (op U) ≫
        (openProperExchangeMap Λ i j h G).hom.app (op ((smallEtaleCompose j).obj U)) := by
      rw [hβdef, Adjunction.homEquiv_unit]; rfl
    have key : ∀ s, (β.hom.app (op U)) s =
        exchangeGlue Λ i j h G (structureHomToSource j U) s := by
      intro s
      rw [hβU]
      erw [← e]
      exact exchangeSection_openProperExchangeMap Λ i j h G (structureHomToSource j U) s
    have : ⇑(β.hom.app (op U)) = ⇑(exchangeGlue Λ i j h G (structureHomToSource j U)) :=
      funext key
    rw [this]
    exact bijective_exchangeGlue Λ i j h G _
  have : IsIso ((sheafToPresheaf _ _).map β) := by
    change IsIso β.hom
    have : ∀ U, IsIso (β.hom.app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2 (hβ U.unop)
    exact NatIso.isIso_of_isIso_app _
  have : IsIso β := isIso_of_reflects_iso β (sheafToPresheaf _ _)
  rw [hα]
  infer_instance

end Exchange

section Derived

attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

section Compactification

variable (Λ : Type r) [Ring Λ] {X S : Scheme.{u}} {f : X ⟶ S} {c₁ c₂ : f.Compactification}
  (φ : c₁ ⟶ c₂)

/-- The unit `g_*(i_! K) ⟶ Rg_*(i_! K)` of the derived direct image along a morphism of
compactifications is invertible on bounded below complexes with torsion cohomology: since
`i_!` and `j_! ≅ g_* ∘ i_!` are exact, this is the invertibility of the composition comparison
`R(g_* ∘ i_!) ⟶ Rg_* ∘ Ri_!` of [Stacks, Tag 0F7G]. -/
private lemma isIso_rightDerivedFunctorPlusUnit_app_extensionByZero_of_hom
    (K : HomotopyCategory.Plus (EtaleModules.{u, r} Λ X))
    (hK : isTorsionPlus.{u, r} Λ X (DerivedCategory.Plus.Qh.obj K)) :
    IsIso ((etaleModuleDirectImage.{u, r} Λ
        (CompactificationOf.Hom.map φ)).rightDerivedFunctorPlusUnit.app
      ((etaleModuleExtensionByZero.{u, r} Λ c₁.immersion).mapHomotopyCategoryPlus.obj K)) := by
  let F := etaleModuleExtensionByZero.{u, r} Λ c₁.immersion
  let H := etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map φ)
  have hF : IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
    have := Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology F
    exact NatIso.isIso_app_of_isIso _ K
  have hk : IsIso ((etaleModuleExtensionByZero.{u, r} Λ
      c₂.immersion).rightDerivedFunctorPlusUnit.app K) := by
    have := Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
      (etaleModuleExtensionByZero.{u, r} Λ c₂.immersion)
    exact NatIso.isIso_app_of_isIso _ K
  have hFH : IsIso ((F ⋙ H).rightDerivedFunctorPlusUnit.app K) := by
    have w := Functor.rightDerivedFunctorPlusNatIso_hom_fac_app (refinementIsoUniv Λ φ) K
    exact IsIso.of_isIso_fac_left w.symm
  have hc : IsIso ((Functor.rightDerivedFunctorPlusComp F H).app
      (DerivedCategory.Plus.Qh.obj K)) := by
    have := isIso_derivedRefinementComparisonUniv_app Λ φ _ hK
    rw [derivedRefinementComparisonUniv, NatTrans.comp_app] at this
    have : IsIso ((Functor.rightDerivedFunctorPlusNatIso (refinementIsoUniv Λ φ)).hom.app
        (DerivedCategory.Plus.Qh.obj K)) := inferInstance
    exact IsIso.of_isIso_comp_left
      ((Functor.rightDerivedFunctorPlusNatIso (refinementIsoUniv Λ φ)).hom.app
        (DerivedCategory.Plus.Qh.obj K)) _
  have w := Functor.unit_comp_rightDerivedFunctorPlusComp_app F H K
  have : IsIso (H.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K) ≫
      H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K)) := by
    rw [← w]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hFH hc
  exact IsIso.of_isIso_comp_right _
    (H.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K))

end Compactification

section Refinement

variable (Λ : Type r) [Ring Λ] {X A B : Scheme.{u}} (i : X ⟶ A) [IsOpenImmersion i]
  (j : X ⟶ B) [IsOpenImmersion j] {g : A ⟶ B} [IsProper g] (h : i ≫ g = 𝟙 X ≫ j)

include h in
/-- The unit `g_*(i_! K) ⟶ Rg_*(i_! K)` is invertible on bounded below complexes with torsion
cohomology, for open immersions `i`, `j` and a proper `g` with `i ≫ g = j`: the case of the
morphism of compactifications `(A, i, g) ⟶ (B, j, 𝟙)` of `j`. -/
private lemma isIso_rightDerivedFunctorPlusUnit_app_extensionByZero
    (K : HomotopyCategory.Plus (EtaleModules.{u, r} Λ X))
    (hK : isTorsionPlus.{u, r} Λ X (DerivedCategory.Plus.Qh.obj K)) :
    IsIso ((etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlusUnit.app
      ((etaleModuleExtensionByZero.{u, r} Λ i).mapHomotopyCategoryPlus.obj K)) := by
  have hij : i ≫ g = j := h.trans (Category.id_comp j)
  let c₂ : j.Compactification := Scheme.Hom.Compactification.mk B j (𝟙 B) (Category.comp_id j)
  let c₁ : j.Compactification := Scheme.Hom.Compactification.mk A i g hij
  let φ : c₁ ⟶ c₂ := Scheme.Hom.Compactification.homMk (c₁ := c₁) (c₂ := c₂) g hij
    (Category.comp_id g)
  exact isIso_rightDerivedFunctorPlusUnit_app_extensionByZero_of_hom Λ φ K hK

/-- **The morphism `(*)` of a refinement is an isomorphism on `D⁺_tors`.** For open immersions
`i : X ⟶ A`, `j : X ⟶ B` and a proper `g : A ⟶ B` with `i ≫ g = j`, a bounded below complex
`F` of sheaves of `Λ`-modules on `X` with torsion cohomology sheaves and an injective resolution
`u : i_! F ⟶ J`, the morphism `(*) : j_! F ⟶ Rg_*(i_! F)` of the square `i ≫ g = 𝟙 ≫ j`
(`AlgebraicGeometry.openProperExchangeDerivedMap` for the exchange morphisms) is an
isomorphism. -/
theorem isIso_openProperExchangeDerivedMap_of_refinement
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    (hF : isTorsionPlus.{u, r} Λ X
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj F)))
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ A)}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    IsIso (openProperExchangeDerivedMap Λ i j (openProperExchangeNatTrans Λ i j h) u) := by
  have hcounit : ∀ M : EtaleModules.{u, r} Λ X, IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ
      i).counit.app ((etaleModuleExtensionByZero.{u, r} Λ i).obj M)) := by
    intro M
    have ht := (etaleModuleExtensionByZeroAdj.{u, r} Λ i).left_triangle_components M
    have : IsIso ((etaleModuleExtensionByZero.{u, r} Λ i).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app M)) := inferInstance
    have : IsIso ((etaleModuleExtensionByZero.{u, r} Λ i).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app M) ≫
          (etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app
            ((etaleModuleExtensionByZero.{u, r} Λ i).obj M)) := by
      rw [ht]; exact IsIso.id _
    exact IsIso.of_isIso_comp_left ((etaleModuleExtensionByZero.{u, r} Λ i).map
        ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).unit.app M)) _
  have key : ∀ {P Q Q' Z : DerivedCategory.Plus (EtaleModules.{u, r} Λ B)}
      (a : P ⟶ Q) (b : Q ⟶ Z) (c : P ⟶ Q') (d : Q' ⟶ Z), a ≫ b = c ≫ d → IsIso a → IsIso b →
        IsIso c → IsIso d := by
    intro P Q Q' Z a b c d e ha hb hc
    have : IsIso (c ≫ d) := by rw [← e]; infer_instance
    exact IsIso.of_isIso_comp_left c d
  rw [openProperExchangeDerivedMap_eq]
  suffices hΘ : IsIso (DerivedCategory.Plus.Qh.map (Adjunction.exchangeHomotopyCategoryPlusMap
      (etaleModuleDirectImage.{u, r} Λ (𝟙 X)) (etaleModuleExtensionByZero.{u, r} Λ j)
      (etaleModuleDirectImage.{u, r} Λ g) (exchangeCounitTransformation Λ i j
        (openProperExchangeNatTrans Λ i j h)) J)) by
    infer_instance
  have hn := congrArg DerivedCategory.Plus.Qh.map
    (Adjunction.exchangeHomotopyCategoryPlusMap_naturality (etaleModuleDirectImage.{u, r} Λ (𝟙 X))
      (etaleModuleExtensionByZero.{u, r} Λ j) (etaleModuleDirectImage.{u, r} Λ g)
      (exchangeCounitTransformation Λ i j (openProperExchangeNatTrans Λ i j h)) u)
  rw [Functor.map_comp, Functor.map_comp] at hn
  refine key _ _ _ _ hn ?_ ?_ ?_
  · have hθ : ∀ M : EtaleModules.{u, r} Λ X, IsIso ((exchangeCounitTransformation Λ i j
        (openProperExchangeNatTrans Λ i j h)).app
          ((etaleModuleExtensionByZero.{u, r} Λ i).obj M)) := by
      intro M
      rw [exchangeCounitTransformation_app, openProperExchangeNatTrans_app]
      have := isIso_openProperExchangeMap_of_refinement Λ i j h
        ((etaleModuleRestriction.{u, r} Λ i).obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj M))
      have := hcounit M
      infer_instance
    have hc : IsIso (exchangeChainMap Λ i j (openProperExchangeNatTrans Λ i j h)
        ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F).obj) := by
      have : ∀ n, IsIso ((exchangeChainMap Λ i j (openProperExchangeNatTrans Λ i j h)
          ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F).obj).f n) :=
        fun n => hθ (F.obj.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (Adjunction.exchangeHomotopyCategoryPlusMap
        (etaleModuleDirectImage.{u, r} Λ (𝟙 X)) (etaleModuleExtensionByZero.{u, r} Λ j)
        (etaleModuleDirectImage.{u, r} Λ g) (exchangeCounitTransformation Λ i j
          (openProperExchangeNatTrans Λ i j h))
        ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F)).hom := by
      rw [exchangeHomotopyCategoryPlusMap_hom]
      exact Functor.map_isIso _ _
    have : IsIso (Adjunction.exchangeHomotopyCategoryPlusMap
        (etaleModuleDirectImage.{u, r} Λ (𝟙 X)) (etaleModuleExtensionByZero.{u, r} Λ j)
        (etaleModuleDirectImage.{u, r} Λ g) (exchangeCounitTransformation Λ i j
          (openProperExchangeNatTrans Λ i j h))
        ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F)) :=
      have : IsIso ((ObjectProperty.ι _).map (Adjunction.exchangeHomotopyCategoryPlusMap
          (etaleModuleDirectImage.{u, r} Λ (𝟙 X)) (etaleModuleExtensionByZero.{u, r} Λ j)
          (etaleModuleDirectImage.{u, r} Λ g) (exchangeCounitTransformation Λ i j
            (openProperExchangeNatTrans Λ i j h))
          ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F))) := this
      isIso_of_reflects_iso _ (ObjectProperty.ι _)
    exact Functor.map_isIso _ _
  · have hu := Functor.isIso_plusQh_map_quotient_map u
    have hU := isIso_rightDerivedFunctorPlusUnit_app_extensionByZero Λ i j h
      ((HomotopyCategory.Plus.quotient _).obj F) hF
    have hn2 := (etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlusUnit.naturality
      ((HomotopyCategory.Plus.quotient _).map u)
    have : IsIso ((etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj J)) := inferInstance
    have hn2' : DerivedCategory.Plus.Qh.map ((etaleModuleDirectImage.{u, r} Λ
        g).mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient _).map u)) ≫
          (etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj J) =
        (etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlusUnit.app
            ((etaleModuleExtensionByZero.{u, r} Λ i).mapHomotopyCategoryPlus.obj
              ((HomotopyCategory.Plus.quotient _).obj F)) ≫
          (etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map u)) := hn2
    have : IsIso (DerivedCategory.Plus.Qh.map ((etaleModuleDirectImage.{u, r} Λ
        g).mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient _).map u)) ≫
          (etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj J)) := by
      rw [hn2']
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hU (Functor.map_isIso
        (etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlus
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient _).map u)))
    exact IsIso.of_isIso_comp_right _
      ((etaleModuleDirectImage.{u, r} Λ g).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient _).obj J))
  · have q1 : QuasiIso (((etaleModuleRestriction.{u, r} Λ i).mapHomologicalComplex _).map u.hom) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology u.hom _
    have q2 : QuasiIso (((etaleModuleDirectImage.{u, r} Λ (𝟙 X)).mapHomologicalComplex _).map
        (((etaleModuleRestriction.{u, r} Λ i).mapHomologicalComplex _).map u.hom)) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology _ _
    have q3 : QuasiIso (((etaleModuleExtensionByZero.{u, r} Λ j).mapHomologicalComplex _).map
        (((etaleModuleDirectImage.{u, r} Λ (𝟙 X)).mapHomologicalComplex _).map
          (((etaleModuleRestriction.{u, r} Λ i).mapHomologicalComplex _).map u.hom))) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology _ _
    have : QuasiIso ((etaleModuleExtensionByZero.{u, r} Λ j).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, r} Λ (𝟙 X)).mapCochainComplexPlus.map
          ((etaleModuleRestriction.{u, r} Λ i).mapCochainComplexPlus.map u))).hom := q3
    exact Functor.isIso_plusQh_map_quotient_map ((etaleModuleExtensionByZero.{u, r} Λ
      j).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, r} Λ (𝟙 X)).mapCochainComplexPlus.map
          ((etaleModuleRestriction.{u, r} Λ i).mapCochainComplexPlus.map u)))

end Refinement

section Compactification

variable (Λ : Type r) [Ring Λ] {X S : Scheme.{u}} {f : X ⟶ S} {c₁ c₂ : f.Compactification}
  (φ : c₁ ⟶ c₂)

omit [Ring Λ] in
/-- The square `i ≫ g = 𝟙 ≫ j` attached to a morphism of compactifications. -/
lemma Scheme.Hom.Compactification.immersion_comp_map_eq_id_comp :
    c₁.immersion ≫ CompactificationOf.Hom.map φ = 𝟙 X ≫ c₂.immersion := by
  rw [Category.id_comp]
  exact CompactificationOf.immersion_comp_map φ

/-- **[FK, I.8.6]** If the compactification `c₁ = (X̄', i, f̄ ∘ g)` of `f : X ⟶ S` dominates
`c₂ = (X̄, j, f̄)` through `g : X̄' ⟶ X̄`, then `g` is proper. -/
@[weil "lem_fk108_compactification_extension_acyclic"]
theorem Scheme.Hom.Compactification.isProper_map : IsProper (CompactificationOf.Hom.map φ) :=
  inferInstance

/-- **[FK, I.8.6]** Let `c₂ = (X̄, j, f̄)` and `c₁ = (X̄', i, f̄ ∘ g)` be compactifications of
`f : X ⟶ S`, the second dominating the first through `g : X̄' ⟶ X̄`. For a bounded below
complex `F` of sheaves of `Λ`-modules on `X` with torsion cohomology sheaves and an injective
resolution `u : i_! F ⟶ J`, the morphism `(*) : j_! F ⟶ Rg_*(i_! F)` of the square
`g ∘ i = j ∘ 𝟙` is an isomorphism. -/
@[weil "lem_fk108_compactification_extension_acyclic"]
theorem isIso_openProperExchangeDerivedMap_of_hom
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    (hF : isTorsionPlus.{u, r} Λ X
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj F)))
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ c₁.space)}
    (u : (etaleModuleExtensionByZero.{u, r} Λ c₁.immersion).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    IsIso (openProperExchangeDerivedMap Λ c₁.immersion c₂.immersion
      (@openProperExchangeNatTrans Λ _ X c₁.space X c₂.space c₁.immersion _ c₂.immersion _
        (𝟙 X) (CompactificationOf.Hom.map φ) (by infer_instance) (by infer_instance)
        (Scheme.Hom.Compactification.immersion_comp_map_eq_id_comp φ)) u) :=
  isIso_openProperExchangeDerivedMap_of_refinement Λ c₁.immersion c₂.immersion
    (Scheme.Hom.Compactification.immersion_comp_map_eq_id_comp φ) hF u

end Compactification

end Derived

end AlgebraicGeometry
