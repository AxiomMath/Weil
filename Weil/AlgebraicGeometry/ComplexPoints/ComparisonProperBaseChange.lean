module

public import Weil.AlgebraicGeometry.ComplexPoints.ComparisonFinite
public import Weil.AlgebraicGeometry.ComplexPoints.FiberProduct
public import Weil.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreStalk
public import Weil.Topology.Sheaves.Cohomology.ProperBaseChangeAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsPullbackComposition
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointFiberStalk

/-!
# Proper base change and the comparison map

Let `p : X ⟶ S` be a proper morphism of schemes over `ℂ`, with `S` proper over `ℂ` and `X(ℂ)`
compact, and suppose that the geometric fibre `X_t = X ×_S Spec ℂ` over every complex point `t` of
`S` satisfies `PC`: the comparison map `c^ν(X_t, F)` is bijective for every torsion sheaf `F` and
every `ν`. For a torsion sheaf `G` on `X_et` this file proves:

* the base change map `β : ε^* p_* G ⟶ p_an,* ε^* G` is an isomorphism;
* if `R^q p_* G = 0`, then `R^q p_an,* (ε^* G) = 0`.

Both are checked on stalks at a complex point `t` of `S`. The fibre `p_an⁻¹(t)` of
`p_an : X(ℂ) → S(ℂ)` is homeomorphic to `X_t(ℂ)`. For the vanishing, topological proper base
change identifies the stalk of `R^q p_an,* ε^* G` with `H^q(X_t(ℂ), ε^* G|)`, `PC(X_t)` identifies
it with `H^q_et(X_t, G|)`, and étale proper base change identifies the latter with the stalk of
`R^q p_* G`; only abstract isomorphisms are needed.

For the isomorphism, the base change map is compatible with composition, so along
`i ≫ p = q ≫ t` (with `i : X_t ⟶ X` and `q : X_t ⟶ Spec ℂ`) the base change map of `p` at
`i_* i^* G` is invertible: the base change maps of the finite morphisms `i` and `t` are invertible,
and that of `q` is invertible because `c^0(X_t, i^* G)` is bijective and `ε^*` is an equivalence
over `Spec ℂ`. The unit `G ⟶ i_* i^* G` becomes invertible on stalks at `t` after `p_*`
(étale proper base change in degree zero) and after `p_an,* ε^*` (topological proper base change in
degree zero, `X_t(ℂ)` being the fibre), so the naturality square of `β` gives the stalk of `β` at
`t`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.isIso_pushforwardBaseChange_of_pc_fibres`: `β` is an
  isomorphism on torsion sheaves.
* `AlgebraicGeometry.Scheme.ComplexPoints.isZero_rightDerived_analytic_of_isZero`: vanishing of
  `R^q p_*` transfers to `R^q p_an,* ε^*`.
* `AlgebraicGeometry.Scheme.ComplexPoints.pushforwardBaseChange_comp_app`: the base change map
  of a composite is the composite of the base change maps.
* `AlgebraicGeometry.Scheme.ComplexPoints.isIso_pushforwardBaseChange_spec_of_bijective`: the
  base change map of `X' ⟶ Spec ℂ` at `G` is invertible when `c^0(X', G)` is bijective.
* `AlgebraicGeometry.Scheme.ComplexPoints.fibreHomeomorph`: `X_t(ℂ) ≃ₜ p_an⁻¹(t)`.

## Implementation notes

The topological properness of `p_an` is taken from the compactness of `X(ℂ)` (and the Hausdorff
property of `S(ℂ)`), not from the properness of `p`, hence the hypothesis
`[CompactSpace (ComplexPoints x)]`.

## References

* [Freitag–Kiehl, *Étale cohomology and the Weil conjecture*, I.11]
* [Stacks Project, Tag 0A3T](https://stacks.math.columbia.edu/tag/0A3T)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
-/

@[expose] public noncomputable section

attribute [-instance] TopCat.hasSheafify_opens_addCommGrpCat
  TopCat.wEqualsLocallyBijective_opens_addCommGrpCat
  TopCat.isGrothendieckAbelian_sheaf_opens_addCommGrpCat TopCat.hasSheafify_opens_of_addCommGrpCat
  TopCat.wEqualsLocallyBijective_opens_of_addCommGrpCat
  TopCat.isGrothendieckAbelian_sheaf_opens_of_addCommGrpCat
  Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

open CategoryTheory Limits Opposite TopologicalSpace Abelian Topology

-- This instance answers `HasSheafify` at a coefficient universe `max _ ?w` with `?w` left
-- undetermined, and elaboration then stops at `1 =?= max 1 ?w`.
attribute [-instance] Stacks.LargeModuleUniverse.hasSheafify

namespace AlgebraicGeometry.Scheme.ComplexPoints

section HomeomorphTransport

variable {A B : TopCat.{1}} (e : A ≅ B)

/-- Direct image along a homeomorphism is an equivalence of categories of abelian sheaves. -/
theorem isEquivalence_pushforward_of_iso :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} e.hom).IsEquivalence := by
  have : (TopologicalSpace.Opens.map e.hom).IsContinuous
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology _
  have : (TopologicalSpace.Opens.map e.inv).IsContinuous
      (Opens.grothendieckTopology A) (Opens.grothendieckTopology B) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology _
  have : (TopologicalSpace.Opens.map e.inv ⋙ TopologicalSpace.Opens.map e.hom).IsContinuous
      (Opens.grothendieckTopology A) (Opens.grothendieckTopology A) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology B) _
  have : (TopologicalSpace.Opens.map e.hom ⋙ TopologicalSpace.Opens.map e.inv).IsContinuous
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology B) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology A) _
  have e₁ : TopologicalSpace.Opens.map e.inv ⋙ TopologicalSpace.Opens.map e.hom ≅ 𝟭 _ :=
    NatIso.ofComponents (fun U => eqToIso (TopologicalSpace.Opens.ext (by
      ext a
      change e.inv (e.hom a) ∈ U ↔ a ∈ U
      rw [← ConcreteCategory.comp_apply, e.hom_inv_id, TopCat.id_app]))) (fun _ => rfl)
  have e₂ : TopologicalSpace.Opens.map e.hom ⋙ TopologicalSpace.Opens.map e.inv ≅ 𝟭 _ :=
    NatIso.ofComponents (fun U => eqToIso (TopologicalSpace.Opens.ext (by
      ext b
      change e.hom (e.inv b) ∈ U ↔ b ∈ U
      rw [← ConcreteCategory.comp_apply, e.inv_hom_id, TopCat.id_app]))) (fun _ => rfl)
  exact (CategoryTheory.Equivalence.mk
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} e.hom)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{1} e.inv)
    ((Functor.sheafPushforwardContinuousId' e₁ _ _).symm ≪≫
      (Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _).symm)
    (Functor.sheafPushforwardContinuousComp' (Iso.refl _) _ _ _ _ ≪≫
      Functor.sheafPushforwardContinuousId' e₂ _ _)).isEquivalence_functor

/-- Inverse image of abelian sheaves, in the site spelling. -/
noncomputable abbrev pullbackSh (f : A ⟶ B) :
    Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1} ⥤
      Sheaf (Opens.grothendieckTopology A) AddCommGrpCat.{1} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{1} f

/-- Direct image of abelian sheaves, in the site spelling. -/
noncomputable abbrev pushforwardSh (f : A ⟶ B) :
    Sheaf (Opens.grothendieckTopology A) AddCommGrpCat.{1} ⥤
      Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{1} f

instance additive_pushforwardSh (f : A ⟶ B) : (pushforwardSh f).Additive where
  map_add := rfl

/-- `f^* ⊣ f_*`, in the site spelling. -/
noncomputable abbrev pullbackAdjSh (f : A ⟶ B) : pullbackSh f ⊣ pushforwardSh f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{1} f

instance additive_pullbackSh (f : A ⟶ B) : (pullbackSh f).Additive :=
  (pullbackAdjSh f).left_adjoint_additive

instance preservesFiniteLimits_pullbackSh (f : A ⟶ B) : PreservesFiniteLimits (pullbackSh f) := by
  have : (TopologicalSpace.Opens.map f).IsContinuous
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology _
  have : RepresentablyFlat (TopologicalSpace.Opens.map f) :=
    instRepresentablyFlatOpensCarrierMap _
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    _ _ _ _

instance preservesFiniteColimits_pullbackSh (f : A ⟶ B) :
    PreservesFiniteColimits (pullbackSh f) := by
  have := (pullbackAdjSh f).leftAdjoint_preservesColimits.{0, 0}
  infer_instance

/-- Inverse image along a homeomorphism is an equivalence of categories of abelian sheaves. -/
theorem isEquivalence_pullback_of_iso : (pullbackSh e.hom).IsEquivalence :=
  have := isEquivalence_pushforward_of_iso e
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{1}
    e.hom).isEquivalence_left_of_isEquivalence_right

/-- The constant sheaf is preserved by inverse images: `M_A ≅ f^* M_B`. -/
noncomputable def constantSheafIsoPullback (f : A ⟶ B) :
    constantSheaf (Opens.grothendieckTopology A) AddCommGrpCat.{1} ≅
      constantSheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1} ⋙ pullbackSh f :=
  (constantSheafAdj _ _ isTerminalTop).leftAdjointUniq
    ((constantSheafAdj _ _ isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{1} f))

/-- **Cohomology is invariant under homeomorphisms**: `H^n(B, K) ≃ H^n(A, e^* K)`. -/
noncomputable def sheafHAddEquivPullbackOfIso
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology A) AddCommGrpCat.{1})]
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1})]
    (K : Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1}) (n : ℕ) :
    Sheaf.H.{1} K n ≃+ Sheaf.H.{1} ((pullbackSh e.hom).obj K) n :=
  have := isEquivalence_pullback_of_iso e
  have : EnoughInjectives (Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1}) :=
    IsGrothendieckAbelian.enoughInjectives.{1}
  AddEquiv.ofBijective ((pullbackSh e.hom).mapExtOfIso
    ((constantSheafIsoPullback e.hom).app (AddCommGrpCat.of (ULift ℤ))).symm K n) (by
      rw [Functor.mapExtOfIso_bijective_iff]
      exact Functor.mapExt_bijective_of_preservesInjectiveObjects _ _ _ _)

/-- The inverse image along a composite is the composite of the inverse images. -/
noncomputable def pullbackShCompIso {C : TopCat.{1}} (g : C ⟶ A) (f : A ⟶ B) :
    pullbackSh (g ≫ f) ≅ pullbackSh f ⋙ pullbackSh g :=
  (pullbackAdjSh (g ≫ f)).leftAdjointUniq ((pullbackAdjSh f).comp (pullbackAdjSh g))

/-- Evaluation at the generator: morphisms out of `ℤ` are elements. -/
theorem bijective_eval_uliftInt (M : AddCommGrpCat.{1}) :
    Function.Bijective (fun φ : AddCommGrpCat.of (ULift.{1} ℤ) ⟶ M => φ (ULift.up 1)) := by
  constructor
  · intro φ ψ h
    ext ⟨n⟩
    have : φ.hom.comp AddEquiv.ulift.symm.toAddMonoidHom =
        ψ.hom.comp AddEquiv.ulift.symm.toAddMonoidHom := AddMonoidHom.ext_int h
    exact DFunLike.congr_fun this n
  · intro m
    refine ⟨AddCommGrpCat.ofHom ((zmultiplesHom M m).comp AddEquiv.ulift.toAddMonoidHom), ?_⟩
    change (1 : ℤ) • m = m
    exact one_zsmul m

/-- **On a space with at most one point, `ℤ` detects isomorphisms of abelian sheaves.** -/
theorem isIso_of_bijective_comp_constantSheaf [Subsingleton A]
    {F G : Sheaf (Opens.grothendieckTopology A) AddCommGrpCat.{1}} (β : F ⟶ G)
    (h : Function.Bijective (fun ψ : (constantSheaf (Opens.grothendieckTopology A)
      AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F => ψ ≫ β)) : IsIso β := by
  let adj := constantSheafAdj (Opens.grothendieckTopology A) AddCommGrpCat.{1} isTerminalTop
  have h1 : Function.Bijective (fun φ : AddCommGrpCat.of (ULift ℤ) ⟶ F.obj.obj (op ⊤) =>
      φ ≫ β.hom.app (op ⊤)) := by
    have hc : (fun φ : AddCommGrpCat.of (ULift ℤ) ⟶ F.obj.obj (op ⊤) =>
        φ ≫ β.hom.app (op ⊤)) = adj.homEquiv _ _ ∘ (fun ψ => ψ ≫ β) ∘ (adj.homEquiv _ _).symm := by
      funext φ
      simp only [Function.comp_apply, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
      rfl
    rw [hc]
    exact (adj.homEquiv _ _).bijective.comp (h.comp (adj.homEquiv _ _).symm.bijective)
  have htop : IsIso (β.hom.app (op ⊤)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have hc : (fun φ : AddCommGrpCat.of (ULift ℤ) ⟶ G.obj.obj (op ⊤) => φ (ULift.up 1)) ∘
        (fun φ : AddCommGrpCat.of (ULift ℤ) ⟶ F.obj.obj (op ⊤) => φ ≫ β.hom.app (op ⊤)) =
        β.hom.app (op ⊤) ∘ (fun φ : AddCommGrpCat.of (ULift ℤ) ⟶ F.obj.obj (op ⊤) =>
          φ (ULift.up 1)) := by
      funext φ
      rfl
    have := (bijective_eval_uliftInt _).comp h1
    rw [hc] at this
    exact (Function.Bijective.of_comp_iff _ (bijective_eval_uliftInt _)).1 this
  have hV : ∀ V : (TopologicalSpace.Opens A)ᵒᵖ, IsIso (β.hom.app V) := by
    intro V
    induction V using Opposite.rec with | op V => ?_
    by_cases hne : (V : Set A).Nonempty
    · obtain ⟨a, ha⟩ := hne
      have : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun b =>
        (Subsingleton.elim b a) ▸ ha)
      subst this
      exact htop
    · have : V = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 hne)
      subst this
      exact isIso_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty (F : TopCat.Sheaf _ A))
        (TopCat.Sheaf.isTerminalOfEmpty (G : TopCat.Sheaf _ A)) _
  have : IsIso ((sheafToPresheaf _ _).map β) := NatIso.isIso_of_isIso_app β.hom
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- A morphism of abelian sheaves is an isomorphism if and only if it is bijective on every open. -/
theorem isIso_iff_bijective_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{1}} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ W, Function.Bijective (φ.hom.app W) := by
  constructor
  · intro h W
    have : IsIso ((sheafToPresheaf J AddCommGrpCat.{1}).map φ) := inferInstance
    have : IsIso (φ.hom.app W) :=
      NatIso.isIso_app_of_isIso ((sheafToPresheaf J AddCommGrpCat.{1}).map φ) W
    exact (ConcreteCategory.isIso_iff_bijective _).1 this
  · intro h
    have : ∀ W, IsIso (φ.hom.app W) := fun W => (ConcreteCategory.isIso_iff_bijective _).2 (h W)
    have : IsIso ((sheafToPresheaf J AddCommGrpCat.{1}).map φ) := NatIso.isIso_of_isIso_app φ.hom
    exact isIso_of_reflects_iso _ (sheafToPresheaf J AddCommGrpCat.{1})

section Embedding

variable {φ : A ⟶ B} (hφ : IsInducing φ)

include hφ in
/-- For an inducing map, every open set of the source is a preimage. -/
theorem opensMap_surjective : Function.Surjective (TopologicalSpace.Opens.map φ).obj := by
  intro V
  obtain ⟨U, hU, hVU⟩ := hφ.isOpen_iff.1 V.2
  exact ⟨⟨U, hU⟩, TopologicalSpace.Opens.ext hVU⟩

include hφ in
/-- Preimage of opens along an inducing map is cover dense. -/
theorem isCoverDense_opensMap :
    (TopologicalSpace.Opens.map φ).IsCoverDense (Opens.grothendieckTopology A) := by
  constructor
  intro V x hx
  obtain ⟨W, hW⟩ := opensMap_surjective hφ V
  refine ⟨V, 𝟙 V, ?_, hx⟩
  change Presieve.coverByImage (TopologicalSpace.Opens.map φ) V (𝟙 V)
  exact ⟨⟨W, eqToHom hW.symm, eqToHom hW, by simp⟩⟩

/-- Preimage of opens is locally full. -/
theorem isLocallyFull_opensMap :
    (TopologicalSpace.Opens.map φ).IsLocallyFull (Opens.grothendieckTopology A) := by
  constructor
  intro U V f x hx
  let G := TopologicalSpace.Opens.map φ
  refine ⟨G.obj (U ⊓ V), G.map (homOfLE inf_le_left), ?_, ?_⟩
  · change
      ∃ (Z' : _) (g : Z' ⟶ U) (_ : G.obj (U ⊓ V) ⟶ G.obj Z'),
        (G.imageSieve f).arrows g ∧ G.map (homOfLE inf_le_left) = _ ≫ G.map g
    exact ⟨U ⊓ V, homOfLE inf_le_left, 𝟙 _, ⟨homOfLE inf_le_right, Subsingleton.elim _ _⟩,
      by simp⟩
  · exact ⟨hx, leOfHom f hx⟩

include hφ in
/-- **The direct image along an embedding is fully faithful.** -/
theorem fullyFaithful_pushforwardSh :
    (pushforwardSh φ).Full ∧ (pushforwardSh φ).Faithful := by
  have := isCoverDense_opensMap hφ
  have := isLocallyFull_opensMap (φ := φ)
  have : (TopologicalSpace.Opens.map φ).IsContinuous
      (Opens.grothendieckTopology B) (Opens.grothendieckTopology A) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology _
  exact ⟨Functor.IsCoverDense.full_sheafPushforwardContinuous _ _ _,
    Functor.IsCoverDense.faithful_sheafPushforwardContinuous _ _ _⟩

include hφ in
/-- **Inverse image after direct image along an embedding**: `φ^*` of the unit of
`φ^* ⊣ φ_*` is an isomorphism. -/
theorem isIso_pullbackSh_map_unit (H : Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1}) :
    IsIso ((pullbackSh φ).map ((pullbackAdjSh φ).unit.app H)) := by
  obtain ⟨h₁, h₂⟩ := fullyFaithful_pushforwardSh hφ
  have : IsIso ((pullbackSh φ).map ((pullbackAdjSh φ).unit.app H) ≫
      (pullbackAdjSh φ).counit.app ((pullbackSh φ).obj H)) := by
    erw [(pullbackAdjSh φ).left_triangle_components]
    exact IsIso.id _
  have : IsIso ((pullbackAdjSh φ).counit.app ((pullbackSh φ).obj H)) :=
    @Adjunction.instIsIsoAppCounitOfFullOfFaithful _ _ _ _ _ _ (pullbackAdjSh φ) h₁ h₂ _
  exact IsIso.of_isIso_comp_right _ ((pullbackAdjSh φ).counit.app ((pullbackSh φ).obj H))

end Embedding

/-- An isomorphism `h` composed with `ι`: if `(h ≫ ι)^* χ` is invertible, so is `ι^* χ`. -/
theorem isIso_pullbackSh_map_of_comp {Z : TopCat.{1}} (h : A ≅ Z) (ι : Z ⟶ B)
    {F F' : Sheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1}} (χ : F ⟶ F')
    (hχ : IsIso ((pullbackSh (h.hom ≫ ι)).map χ)) : IsIso ((pullbackSh ι).map χ) := by
  have : IsIso ((pullbackSh h.hom).map ((pullbackSh ι).map χ)) :=
    (NatIso.isIso_map_iff (pullbackShCompIso h.hom ι) χ).1 hχ
  have := isEquivalence_pullback_of_iso h
  exact isIso_of_reflects_iso _ (pullbackSh h.hom)

/-- **Stalks of a proper direct image only see the fibre**: if the restriction of `χ` to the
fibre `f⁻¹(y)` is invertible, so is the stalk at `y` of `f_* χ`. -/
theorem isIso_sheafFiber_pushforwardSh_map {f : A ⟶ B} (y : B)
    (hclosed : IsClosedMap f) (hcompact : IsCompact (ProperBaseChange.fiber f y))
    (hsep : IsSeparatedMap f) {F F' : Sheaf (Opens.grothendieckTopology A) AddCommGrpCat.{1}}
    (χ : F ⟶ F')
    (hχ : IsIso ((Stacks.Topology.restrictionFunctor A (ProperBaseChange.fiber f y)).map χ)) :
    IsIso ((_root_.Opens.pointGrothendieckTopology y).sheafFiber.map
      ((pushforwardSh f).map χ)) := by
  have h1 : IsIso ((Stacks.Topology.sheafStalkFunctor y).map
      ((Stacks.Topology.pushforwardSheafFunctor f).map χ)) :=
    (NatIso.isIso_map_iff (ProperBaseChange.stalkIsoFiberSections y hclosed hcompact hsep) χ).2
      (Functor.map_isIso (Stacks.Topology.sectionsFunctor (TopCat.of (ProperBaseChange.fiber f y)))
        ((Stacks.Topology.restrictionFunctor A (ProperBaseChange.fiber f y)).map χ))
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerLeft
    (sheafToPresheaf (Opens.grothendieckTopology B) AddCommGrpCat.{1})
    (_root_.Opens.pointFiberStalkFunctorIso (C := AddCommGrpCat.{1}) y)) _).2 h1

end HomeomorphTransport

section Fibre

variable {X S : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (s : S ⟶ Spec (.of ℂ)) (p : X ⟶ S)
  (hp : p ≫ s = x)

/-- The geometric fibre over a complex point, as a `ℂ`-scheme. -/
noncomputable abbrev fibreOver (t : ComplexPoints s) : pullback p t.hom ⟶ Spec (.of ℂ) :=
  pullback.snd p t.hom

include hp in
/-- The inclusion of the fibre is a morphism over `ℂ`. -/
theorem fibreInclusion_comp (t : ComplexPoints s) :
    pullback.fst p t.hom ≫ x = fibreOver s p t := by
  rw [← hp, pullback.condition_assoc, t.hom_comp, Category.comp_id]

/-- The map of complex points of the inclusion of the fibre `X_t ⟶ X`. -/
noncomputable abbrev fibreAnalyticMap (t : ComplexPoints s) :
    analyticSpace (fibreOver s p t) ⟶ analyticSpace x :=
  analyticMap x (fibreOver s p t) (pullback.fst p t.hom) (fibreInclusion_comp x s p hp t)

/-- `Spec ℂ` has exactly one complex point. -/
instance unique_complexPoints_id : Unique (ComplexPoints (𝟙 (Spec (.of ℂ)))) :=
  uniqueOfSubsingleton ⟨𝟙 _, Category.comp_id _⟩

/-- The complex points of the fibre embed into those of `X`. -/
theorem isEmbedding_map_fibreInclusion (t : ComplexPoints s) :
    IsEmbedding (map (pullback.fst p t.hom) (fibreInclusion_comp x s p hp t)) :=
  (Homeomorph.prodUnique (ComplexPoints x) (ComplexPoints (𝟙 (Spec (.of ℂ))))).isEmbedding.comp
    (isEmbedding_pullbackPair hp t.hom_comp (fibreInclusion_comp x s p hp t))

/-- The complex points of `X` coming from the fibre over `t` are those over `t`. -/
theorem range_map_fibreInclusion (t : ComplexPoints s) :
    Set.range (map (pullback.fst p t.hom) (fibreInclusion_comp x s p hp t)) =
      {a | map p hp a = t} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    refine ext ?_
    change (b.hom ≫ pullback.fst p t.hom) ≫ p = t.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, b.hom_comp, Category.id_comp]
  · intro ha
    refine ⟨pullbackPoint hp t.hom_comp (fibreInclusion_comp x s p hp t) a default ?_, ?_⟩
    · refine ha.trans (ext ?_)
      change t.hom = (default : ComplexPoints (𝟙 (Spec (.of ℂ)))).hom ≫ t.hom
      rw [show (default : ComplexPoints (𝟙 (Spec (.of ℂ)))).hom = 𝟙 _ from
        congrArg ComplexPoints.hom (Subsingleton.elim _ ⟨𝟙 _, Category.comp_id _⟩)]
      exact (Category.id_comp _).symm
    · exact congrArg Prod.fst
        (pullbackPair_pullbackPoint hp t.hom_comp (fibreInclusion_comp x s p hp t) a default _)

/-- `X_t(ℂ) → X(ℂ)` is an embedding. -/
theorem isEmbedding_fibreAnalyticMap (t : ComplexPoints s) :
    IsEmbedding (fibreAnalyticMap x s p hp t) :=
  Homeomorph.ulift.symm.isEmbedding.comp
    ((isEmbedding_map_fibreInclusion x s p hp t).comp Homeomorph.ulift.isEmbedding)

/-- The image of `X_t(ℂ) → X(ℂ)` is the fibre `p_an⁻¹(t)`. -/
theorem range_fibreAnalyticMap (t : ComplexPoints s) :
    Set.range (fibreAnalyticMap x s p hp t) =
      ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t) := by
  ext w
  constructor
  · rintro ⟨b, rfl⟩
    have : map (pullback.fst p t.hom) (fibreInclusion_comp x s p hp t) b.down ∈
        {a | map p hp a = t} := by
      rw [← range_map_fibreInclusion x s p hp t]
      exact ⟨_, rfl⟩
    exact congrArg ULift.up this
  · intro hw
    have hw' : w.down ∈ {a | map p hp a = t} := congrArg ULift.down hw
    rw [← range_map_fibreInclusion x s p hp t] at hw'
    obtain ⟨b, hb⟩ := hw'
    exact ⟨ULift.up b, congrArg ULift.up hb⟩

/-- The complex points of the fibre are the fibre of the map of complex points. -/
noncomputable def fibreHomeomorph (t : ComplexPoints s) :
    analyticSpace (fibreOver s p t) ≃ₜ ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t) :=
  (isEmbedding_fibreAnalyticMap x s p hp t).toHomeomorph.trans
    (Homeomorph.setCongr (range_fibreAnalyticMap x s p hp t))

/-- `fibreHomeomorph` as an isomorphism in `TopCat`. -/
noncomputable def fibreIso (t : ComplexPoints s) :
    analyticSpace (fibreOver s p t) ≅
      TopCat.of (ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t)) :=
  TopCat.isoOfHomeo (fibreHomeomorph x s p hp t)

/-- `X_t(ℂ) ≅ p_an⁻¹(t)` followed by the inclusion of the fibre is `X_t(ℂ) → X(ℂ)`. -/
theorem fibreIso_hom_comp_subsetInclusion (t : ComplexPoints s) :
    (fibreIso x s p hp t).hom ≫ Stacks.subsetInclusion (analyticSpace x)
        (ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t)) =
      fibreAnalyticMap x s p hp t := by
  ext w
  rfl

end Fibre

section Vanishing

open Stacks.EtaleCohomology

variable {X S : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (s : S ⟶ Spec (.of ℂ)) (p : X ⟶ S)
  (hp : p ≫ s = x) [IsProper p] [IsProper s] [LocallyOfFiniteType x]

omit [LocallyOfFiniteType x] in
include hp in
/-- `X` is separated over `ℂ`. -/
theorem isSeparated_of_comp : IsSeparated x := hp ▸ inferInstance

omit [IsProper p] [LocallyOfFiniteType x] in
/-- `p_an : X(ℂ) → S(ℂ)` is proper when `X(ℂ)` is compact and `S(ℂ)` Hausdorff. -/
theorem isProperMap_analyticMap [CompactSpace (ComplexPoints x)] :
    IsProperMap (analyticMap s x p hp) :=
  (analyticMap s x p hp).hom.continuous.isProperMap

omit [LocallyOfFiniteType x] in
/-- `p_an : X(ℂ) → S(ℂ)` is separated. -/
theorem isSeparatedMap_analyticMap : IsSeparatedMap (analyticMap s x p hp) :=
  have := isSeparated_of_comp x s p hp
  T2Space.isSeparatedMap _

omit [IsProper s] in
/-- **The analytic fibre cohomology vanishes with the étale stalk of `R^q p_*`.** If the fibre
over `t` satisfies `PC`, `G` is torsion, and the stalk at `t` of `R^q p_* G` vanishes, then
`H^q(p_an⁻¹(t), ε^* G) = 0`. -/
theorem subsingleton_sheafH_fiber_of_isZero (t : ComplexPoints s) (hfib : PC (fibreOver s p t))
    (G : EtSheaf X) (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) (q : ℕ)
    (h : IsZero ((smallEtaleStalkAb t.hom).obj
      (((smallEtalePushforwardAb p).rightDerived q).obj G))) :
    letI := IsGrothendieckAbelian.hasExt.{1} (Sheaf (Opens.grothendieckTopology
      (TopCat.of (ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t)))) AddCommGrpCat.{1})
    Subsingleton (Sheaf.H.{1} ((Stacks.Topology.restrictionFunctor (analyticSpace x)
      (ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t))).obj
        ((analyticInverseImage x).obj G)) q) := by
  let i := pullback.fst p t.hom
  have hi := fibreInclusion_comp x s p hp t
  -- étale side: `H^q(X_t, i^* G) = 0`
  have h1 : Subsingleton (Sheaf.H.{1} ((etaleAbelianInverseImage.{0, 0} i).obj G) q) := by
    have e := (stalkRightDerivedPushforwardNatIsoFibreCohomology p t.hom q).app ⟨G, hG⟩
    exact AddCommGrpCat.subsingleton_of_isZero (h.of_iso e.symm)
  -- the comparison map of the fibre
  have h2 : Subsingleton (Sheaf.H.{1} ((analyticInverseImage (fibreOver s p t)).obj
      ((etaleAbelianInverseImage.{0, 0} i).obj G)) q) :=
    (hfib _ (torsionSheafProperty_etaleAbelianInverseImage _ G hG) q).surjective.subsingleton
  -- `ε_t^* i^* ≅ i_an^* ε^*`
  have h3 : Subsingleton (Sheaf.H.{1} ((pullbackSh (fibreAnalyticMap x s p hp t)).obj
      ((analyticInverseImage x).obj G)) q) :=
    @Function.Surjective.subsingleton _ _ _ h2 (Sheaf.H.map_bijective_of_isIso
      ((inverseImageIso x (fibreOver s p t) i hi).hom.app G) q).surjective
  rw [← fibreIso_hom_comp_subsetInclusion x s p hp t] at h3
  have h4 : Subsingleton (Sheaf.H.{1} ((pullbackSh (fibreIso x s p hp t).hom).obj
      ((pullbackSh (Stacks.subsetInclusion (analyticSpace x)
        (ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t)))).obj
          ((analyticInverseImage x).obj G))) q) :=
    @Function.Surjective.subsingleton _ _ _ h3
      (Sheaf.H.map_bijective_of_isIso ((pullbackShCompIso _ _).hom.app _) q).surjective
  exact (sheafHAddEquivPullbackOfIso (fibreIso x s p hp t) _ q).injective.subsingleton

omit [IsProper s] in
/-- **Vanishing of higher direct images transfers to the analytic side.** Let `p : X ⟶ S` be a
proper morphism over `ℂ` with compact `X(ℂ)` whose fibres over the complex points of `S`
satisfy `PC`, and `G` a torsion sheaf on `X_et`. If `R^q p_* G = 0`, then
`R^q p_an,* (ε^* G) = 0`. -/
theorem isZero_rightDerived_analytic_of_isZero [IsProper s] [CompactSpace (ComplexPoints x)]
    (hfib : ∀ t, PC (fibreOver s p t))
    (G : EtSheaf X) (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G)
    (q : ℕ)
    (h : IsZero (((smallEtalePushforwardAb p).rightDerived q).obj G)) :
    IsZero (((Stacks.Topology.pushforwardSheafFunctor
      (analyticMap s x p hp)).rightDerived q).obj ((analyticInverseImage x).obj G)) := by
  have := (isSeparated_of_comp x s p hp)
  refine (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (F := (((Stacks.Topology.pushforwardSheafFunctor (analyticMap s x p hp)).rightDerived q).obj
      ((analyticInverseImage x).obj G) : TopCat.Sheaf AddCommGrpCat.{1} (analyticSpace s)))).2
    fun y => ?_
  have := IsGrothendieckAbelian.hasExt.{1} (Sheaf (Opens.grothendieckTopology
    (TopCat.of (ProperBaseChange.fiber (analyticMap s x p hp) y))) AddCommGrpCat.{1})
  have hs := subsingleton_sheafH_fiber_of_isZero x s p hp y.down (hfib y.down) G hG q
    (Functor.map_isZero _ h)
  exact (AddCommGrpCat.isZero_of_subsingleton _).of_iso
    (ProperBaseChange.higherDirectImageStalkIsoSheafH (isProperMap_analyticMap x s p hp)
      (isSeparatedMap_analyticMap x s p hp) y q _)

end Vanishing

section Composition

open Stacks.EtaleCohomology

local notation "𝔅" => Stacks.EtaleCohomology.smallEtaleBaseChange

/-- The direct images of sheaves along two equal continuous maps are isomorphic. -/
noncomputable def pushforwardEqIso (C : Type*) [Category C] {A B : TopCat.{1}} {φ₁ φ₂ : A ⟶ B}
    (h : φ₁ = φ₂) : TopCat.Sheaf.pushforward C φ₁ ≅ TopCat.Sheaf.pushforward C φ₂ :=
  eqToIso (congrArg (TopCat.Sheaf.pushforward C) h)

/-- `pushforwardEqIso` on sections is restriction along the equality of preimages. -/
theorem pushforwardEqIso_hom_app_hom_app (C : Type*) [Category C] {A B : TopCat.{1}}
    {φ₁ φ₂ : A ⟶ B} (h : φ₁ = φ₂) (F : TopCat.Sheaf C A) (W : (TopologicalSpace.Opens B)ᵒᵖ) :
    ((pushforwardEqIso C h).hom.app F).hom.app W =
      F.obj.map (eqToHom (by subst h; rfl) :
        op ((TopologicalSpace.Opens.map φ₁).obj W.unop) ⟶
          op ((TopologicalSpace.Opens.map φ₂).obj W.unop)) := by
  subst h
  simp [pushforwardEqIso]
  rfl

variable {X X' X'' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  (x'' : X'' ⟶ Spec (.of ℂ)) (f : X' ⟶ X) (hf : f ≫ x = x') (g : X'' ⟶ X') (hg : g ≫ x' = x'')

include hf hg in
/-- A composite of morphisms over `ℂ` is a morphism over `ℂ`. -/
theorem comp_comp_eq : (g ≫ f) ≫ x = x'' := by rw [Category.assoc, hf, hg]

/-- The map of complex points of a composite. -/
theorem analyticMap_comp :
    analyticMap x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg) =
      analyticMap x' x'' g hg ≫ analyticMap x x' f hf := by
  ext w
  exact (Category.assoc _ _ _).symm

variable [LocallyOfFiniteType x] [LocallyOfFiniteType x'] [LocallyOfFiniteType x'']

/-- **The base change of sections along a composite**, on sheaves of sets. -/
theorem baseChangeSections_comp (U : X.Etale) :
    baseChangeSections x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg) U ≫
        (pushforwardEqIso (Type 1) (analyticMap_comp x x' x'' f hf g hg)).hom.app _ =
      baseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward (Type 1)
        (analyticMap x x' f hf)).map (baseChangeSections x' x'' g hg ((𝔅 f).obj U) ≫
          (TopCat.Sheaf.pushforward (Type 1) (analyticMap x' x'' g hg)).map
            ((sectionsFunctor x'').map ((smallEtaleBaseChangeComp g f).inv.app U))) := by
  ext W σ
  refine Subtype.ext (funext fun w => ULift.ext _ _ (ext ?_))
  have e1 := congrArg (fun τ => (τ.1 w).down.hom) (ConcreteCategory.congr_hom
    (pushforwardEqIso_hom_app_hom_app (Type 1) (analyticMap_comp x x' x'' f hf g hg)
      ((sectionsFunctor x'').obj ((𝔅 (g ≫ f)).obj U)) W)
    ((baseChangeSections x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg) U).hom.app W σ))
  refine e1.trans ?_
  change (pullback.lift _ _ _ : Spec (.of ℂ) ⟶ _) =
    (pullback.lift (pullback.lift _ _ _) _ _) ≫ ((smallEtaleBaseChangeComp g f).inv.app U).left
  have hw : analyticMap x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg) w.1 =
      analyticMap x x' f hf (analyticMap x' x'' g hg w.1) :=
    congrArg (fun φ : analyticSpace x'' ⟶ analyticSpace x => φ w.1)
      (analyticMap_comp x x' x'' f hf g hg)
  apply pullback.hom_ext
  · refine (pullback.lift_fst _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg _ (smallEtaleBaseChangeComp_inv_app_left_fst g f U)).symm
    refine Eq.trans ?_ (pullback.lift_fst_assoc _ _ _ _).symm
    refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
    exact congrArg (fun z => (σ.1 z).down.hom) (Subtype.ext hw)
  · refine (pullback.lift_snd _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg _ (MorphismProperty.Over.w
      ((smallEtaleBaseChangeComp g f).inv.app U))).symm
    exact (pullback.lift_snd _ _ _).symm

/-- `pushforwardEqIso` commutes with the forgetful functor. -/
theorem sheafCompose_forget_map_pushforwardEqIso {A B : TopCat.{1}} {φ₁ φ₂ : A ⟶ B}
    (h : φ₁ = φ₂) (F : Sheaf (_root_.Opens.grothendieckTopology A) AddCommGrpCat.{1}) :
    (sheafCompose (_root_.Opens.grothendieckTopology B)
      (CategoryTheory.forget AddCommGrpCat.{1})).map
        ((pushforwardEqIso AddCommGrpCat.{1} h).hom.app F) =
      (pushforwardEqIso (Type 1) h).hom.app
        ((sheafCompose (_root_.Opens.grothendieckTopology A)
          (CategoryTheory.forget AddCommGrpCat.{1})).obj F) := by
  subst h
  simp [pushforwardEqIso]
  rfl

/-- **The base change of free sections along a composite.** -/
theorem freeBaseChangeSections_comp (U : X.Etale) :
    freeBaseChangeSections x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg) U ≫
        (pushforwardEqIso AddCommGrpCat.{1} (analyticMap_comp x x' x'' f hf g hg)).hom.app _ =
      freeBaseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{1}
        (analyticMap x x' f hf)).map (freeBaseChangeSections x' x'' g hg ((𝔅 f).obj U) ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x' x'' g hg)).map
            ((freeSectionsFunctor x'').map ((smallEtaleBaseChangeComp g f).inv.app U))) := by
  apply ((freeAdj x).homEquiv _ _).injective
  let m := (smallEtaleBaseChangeComp g f).inv.app U
  have hz : (freeAdj x'').homEquiv _ _ ((freeSectionsFunctor x'').map m) =
      (sectionsFunctor x'').map m ≫ (freeAdj x'').unit.app _ :=
    ((freeAdj x'').homEquiv_unit _ _ _).trans ((freeAdj x'').unit.naturality _).symm
  have hin := homEquiv_freeBaseChangeSections_comp x' x'' g hg ((𝔅 f).obj U)
    ((freeSectionsFunctor x'').map m)
  have hout := homEquiv_freeBaseChangeSections_comp x x' f hf U
    (freeBaseChangeSections x' x'' g hg ((𝔅 f).obj U) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x' x'' g hg)).map
        ((freeSectionsFunctor x'').map m))
  have hh : (freeAdj x).homEquiv _ _
      (freeBaseChangeSections x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg) U) =
      baseChangeSections x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg) U ≫
        (TopCat.Sheaf.pushforward (Type 1) (analyticMap x x'' (g ≫ f)
          (comp_comp_eq x x' x'' f hf g hg))).map ((freeAdj x'').unit.app _) := by
    unfold freeBaseChangeSections
    exact Equiv.apply_symm_apply _ _
  have hS := baseChangeSections_comp x x' x'' f hf g hg U
  have hT := (pushforwardEqIso (Type 1) (analyticMap_comp x x' x'' f hf g hg)).hom.naturality
    ((freeAdj x'').unit.app ((sectionsFunctor x'').obj ((𝔅 (g ≫ f)).obj U)))
  refine ((freeAdj x).homEquiv_naturality_right _ _).trans ?_
  refine Eq.trans ?_ hout.symm
  rw [hh, sheafCompose_forget_map_pushforwardEqIso]
  erw [Category.assoc, hT]
  erw [← Category.assoc, hS, hin, hz]
  erw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]

/-- **The direct images commute with base change compatibly with composition.** -/
theorem directImageBaseChangeIso_comp (K : AnSheaf x'') :
    (directImageBaseChangeIso x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg)).hom.app K ≫
        (analyticDirectImage x).map
          ((pushforwardEqIso AddCommGrpCat.{1} (analyticMap_comp x x' x'' f hf g hg)).hom.app K) =
      (smallEtalePushforwardAbCompIso g f).inv.app ((analyticDirectImage x'').obj K) ≫
        (smallEtalePushforwardAb f).map ((directImageBaseChangeIso x' x'' g hg).hom.app K) ≫
          (directImageBaseChangeIso x x' f hf).hom.app
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x' x'' g hg)).obj K) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  induction U using Opposite.rec with | op U => ?_
  ext φ
  change (freeBaseChangeSections x x'' (g ≫ f) _ U ≫ _) ≫ _ =
    freeBaseChangeSections x x' f hf U ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{1}
      (analyticMap x x' f hf)).map (freeBaseChangeSections x' x'' g hg ((𝔅 f).obj U) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x' x'' g hg)).map
          ((((smallEtalePushforwardAbCompIso g f).inv.app ((analyticDirectImage x'').obj K)).hom.app
            (op U)) φ))
  rw [smallEtalePushforwardAbCompIso_inv_app_hom_app]
  have hT := (pushforwardEqIso AddCommGrpCat.{1}
    (analyticMap_comp x x' x'' f hf g hg)).hom.naturality φ
  have hF := freeBaseChangeSections_comp x x' x'' f hf g hg U
  erw [Category.assoc, hT, ← Category.assoc, hF]
  erw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, Functor.map_comp,
    Functor.map_comp]

omit [LocallyOfFiniteType x''] in
/-- The transpose of the base change map along `ε^* ⊣ ε_*`. -/
theorem homEquiv_pushforwardBaseChange_app (G : EtSheaf X') :
    (analyticAdjunction x).homEquiv _ _ ((pushforwardBaseChange x x' f hf).app G) =
      (smallEtalePushforwardAb f).map ((analyticAdjunction x').unit.app G) ≫
        (directImageBaseChangeIso x x' f hf).hom.app ((analyticInverseImage x').obj G) := by
  have h := homEquiv_pushforwardBaseChange_app_comp x x' f hf G (𝟙 _)
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at h
  exact h

/-- **The base change map along a composite** is the composite of the base change maps. -/
theorem pushforwardBaseChange_comp_app (G : EtSheaf X'') :
    (pushforwardBaseChange x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg)).app G ≫
        (pushforwardEqIso AddCommGrpCat.{1} (analyticMap_comp x x' x'' f hf g hg)).hom.app
          ((analyticInverseImage x'').obj G) =
      (analyticInverseImage x).map ((smallEtalePushforwardAbCompIso g f).inv.app G) ≫
        (pushforwardBaseChange x x' f hf).app ((smallEtalePushforwardAb g).obj G) ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)).map
            ((pushforwardBaseChange x' x'' g hg).app G) := by
  apply ((analyticAdjunction x).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_right, homEquiv_pushforwardBaseChange_app,
    Adjunction.homEquiv_naturality_left, homEquiv_pushforwardBaseChange_app_comp,
    homEquiv_pushforwardBaseChange_app]
  have hD := directImageBaseChangeIso_comp x x' x'' f hf g hg ((analyticInverseImage x'').obj G)
  have hc := (smallEtalePushforwardAbCompIso g f).inv.naturality
    ((analyticAdjunction x'').unit.app G)
  erw [Category.assoc, hD, ← Category.assoc, hc]
  erw [CategoryTheory.Functor.map_comp, Category.assoc, Category.assoc]

/-- For `g` with invertible base change map at `G`, the base change map of `g ≫ f` at `G` is
invertible if and only if that of `f` at `g_* G` is. -/
theorem isIso_pushforwardBaseChange_comp_iff (G : EtSheaf X'')
    (hg' : IsIso ((pushforwardBaseChange x' x'' g hg).app G)) :
    IsIso ((pushforwardBaseChange x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg)).app G) ↔
      IsIso ((pushforwardBaseChange x x' f hf).app ((smallEtalePushforwardAb g).obj G)) := by
  have e := pushforwardBaseChange_comp_app x x' x'' f hf g hg G
  rw [isIso_iff_bijective_app, isIso_iff_bijective_app]
  have hβg := (isIso_iff_bijective_app _).1 hg'
  have hT := (isIso_iff_bijective_app _).1 (Iso.isIso_hom ((pushforwardEqIso AddCommGrpCat.{1}
    (analyticMap_comp x x' x'' f hf g hg)).app ((analyticInverseImage x'').obj G)))
  have hc := (isIso_iff_bijective_app _).1 (Iso.isIso_hom ((analyticInverseImage x).mapIso
    ((smallEtalePushforwardAbCompIso g f).app G).symm))
  refine forall_congr' fun W => ?_
  have eW : ((pushforwardEqIso AddCommGrpCat.{1} (analyticMap_comp x x' x'' f hf g hg)).hom.app
        ((analyticInverseImage x'').obj G)).hom.app W ∘
      ((pushforwardBaseChange x x'' (g ≫ f) (comp_comp_eq x x' x'' f hf g hg)).app G).hom.app W =
      ((pushforwardBaseChange x' x'' g hg).app G).hom.app
        (op ((TopologicalSpace.Opens.map (analyticMap x x' f hf)).obj W.unop)) ∘
      (((pushforwardBaseChange x x' f hf).app ((smallEtalePushforwardAb g).obj G)).hom.app W ∘
        ((analyticInverseImage x).map
          ((smallEtalePushforwardAbCompIso g f).inv.app G)).hom.app W) :=
    funext fun z => congrArg (fun φ => (φ.hom.app W) z) e
  constructor
  · intro h
    have := (congrArg Function.Bijective eW).mp ((hT W).comp h)
    exact (Function.Bijective.of_comp_iff _ (hc W)).1
      ((Function.Bijective.of_comp_iff' (hβg _) _).1 this)
  · intro h
    have := (congrArg Function.Bijective eW).mpr ((hβg _).comp (h.comp (hc W)))
    exact (Function.Bijective.of_comp_iff' (hT W) _).1 this

end Composition

section DegreeZero

open Stacks.EtaleCohomology

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

/-- The constant sheaf `ℤ` on `Y_et`. -/
noncomputable abbrev etaleUnit : EtSheaf Y :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- **`c^0` on morphisms.** In degree zero the comparison map is `φ ↦ e⁻¹ ≫ ε^* φ` on
`Hom(ℤ, F)`. -/
theorem comparisonMap_zero_mk₀ (F : EtSheaf Y) (φ : etaleUnit ⟶ F) :
    comparisonMap y F 0 (Ext.mk₀ φ) =
      Ext.mk₀ (((constantSheafIso y).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
        (analyticInverseImage y).map φ) := by
  rw [comparisonMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- If `c^0(Y, F)` is bijective, then `ε^*` is bijective on `Hom(ℤ, F)`. -/
theorem bijective_map_of_bijective_comparisonMap_zero (F : EtSheaf Y)
    (h : Function.Bijective (comparisonMap y F 0)) :
    Function.Bijective (fun φ : etaleUnit ⟶ F => (analyticInverseImage y).map φ) := by
  let e := (constantSheafIso y).app (AddCommGrpCat.of (ULift ℤ))
  have h1 : Function.Bijective
      (fun φ : etaleUnit ⟶ F => e.inv ≫ (analyticInverseImage y).map φ) := by
    have hc : (Ext.mk₀ ∘ fun φ : etaleUnit ⟶ F => e.inv ≫ (analyticInverseImage y).map φ) =
        comparisonMap y F 0 ∘ Ext.mk₀ := funext fun φ => (comparisonMap_zero_mk₀ y F φ).symm
    have := h.comp (Ext.mk₀_bijective _ _)
    rw [← hc] at this
    exact (Function.Bijective.of_comp_iff' (Ext.mk₀_bijective _ _) _).1 this
  have h2 : Function.Bijective (fun ψ : (analyticInverseImage y).obj etaleUnit ⟶
      (analyticInverseImage y).obj F => e.inv ≫ ψ) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => e.hom ≫ ψ, fun ψ => by simp, fun ψ => by simp⟩
  exact (Function.Bijective.of_comp_iff' h2 _).1 h1

end DegreeZero

section PushforwardHom

open Stacks.EtaleCohomology

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType x'] (f : X' ⟶ X) (hf : f ≫ x = x')

/-- **The base change map on morphisms**: for `φ : f^* A ⟶ G`, the composite of `ε^*` of its
transpose with the base change map is the transpose of `ε'^* φ`. -/
theorem map_homEquiv_comp_pushforwardBaseChange_app (A : EtSheaf X) (G : EtSheaf X')
    (φ : (etaleAbelianInverseImage.{0, 0} f).obj A ⟶ G) :
    (analyticInverseImage x).map ((etaleInverseImageAdjunction f).homEquiv _ _ φ) ≫
        (pushforwardBaseChange x x' f hf).app G =
      (analyticPullbackAdjunction x x' f hf).homEquiv _ _
        ((inverseImageIso x x' f hf).inv.app A ≫ (analyticInverseImage x').map φ) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp,
    Category.assoc]
  erw [(pushforwardBaseChange x x' f hf).naturality φ]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (map_unit_comp_pushforwardBaseChange_app x x' f hf A)).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg _ (CategoryTheory.Functor.map_comp _ _ _).symm)

end PushforwardHom

section SpecBaseChange

open Stacks.EtaleCohomology

variable {X' : Scheme.{0}} (x' : X' ⟶ Spec (.of ℂ)) [LocallyOfFiniteType x']

/-- **The base change map to `Spec ℂ` is an isomorphism when `c^0` is bijective.** -/
theorem isIso_pushforwardBaseChange_spec_of_bijective (G : EtSheaf X')
    (h : Function.Bijective (comparisonMap x' G 0)) :
    IsIso ((pushforwardBaseChange (𝟙 (Spec (.of ℂ))) x' x' (Category.comp_id x')).app G) := by
  let hx := Category.comp_id x'
  let A : EtSheaf (Spec (.of ℂ)) := etaleUnit
  let a := etaleInverseImageAdjunction x'
  let b := analyticPullbackAdjunction (𝟙 (Spec (.of ℂ))) x' x' hx
  let γ := inverseImageIso (𝟙 (Spec (.of ℂ))) x' x' hx
  let κ := (etaleAbelianInverseImageConstantIso.{0, 0} x').app (AddCommGrpCat.of (ULift ℤ))
  let β := pushforwardBaseChange (𝟙 (Spec (.of ℂ))) x' x' hx
  -- `ε'^*` is bijective on `Hom(x'^* ℤ, G)`
  have hE : Function.Bijective (fun φ : (etaleAbelianInverseImage.{0, 0} x').obj A ⟶ G =>
      (analyticInverseImage x').map φ) := by
    have h0 := bijective_map_of_bijective_comparisonMap_zero x' G h
    have hκ : Function.Bijective (fun φ : (etaleAbelianInverseImage.{0, 0} x').obj A ⟶ G =>
        κ.inv ≫ φ) :=
      Function.bijective_iff_has_inverse.2 ⟨fun φ => κ.hom ≫ φ, fun φ => by simp, fun φ => by simp⟩
    have hκ' : Function.Bijective (fun ψ : (analyticInverseImage x').obj
        ((etaleAbelianInverseImage.{0, 0} x').obj A) ⟶ (analyticInverseImage x').obj G =>
          (analyticInverseImage x').map κ.inv ≫ ψ) :=
      Function.bijective_iff_has_inverse.2 ⟨fun ψ => (analyticInverseImage x').map κ.hom ≫ ψ,
        fun ψ => by simp [← CategoryTheory.Functor.map_comp_assoc],
        fun ψ => by simp [← CategoryTheory.Functor.map_comp_assoc]⟩
    have hc : (fun ψ => (analyticInverseImage x').map κ.inv ≫ ψ) ∘
        (fun φ : (etaleAbelianInverseImage.{0, 0} x').obj A ⟶ G =>
          (analyticInverseImage x').map φ) =
        (fun φ : etaleUnit ⟶ G => (analyticInverseImage x').map φ) ∘ (fun φ => κ.inv ≫ φ) := by
      funext φ
      simp
    have := (congrArg Function.Bijective hc).mpr (h0.comp hκ)
    exact (Function.Bijective.of_comp_iff' hκ' _).1 this
  -- the transpose of `ε'^*` along both adjunctions
  have hR1 : Function.Bijective (fun φ : (etaleAbelianInverseImage.{0, 0} x').obj A ⟶ G =>
      b.homEquiv _ _ (γ.inv.app A ≫ (analyticInverseImage x').map φ)) := by
    have hγ : Function.Bijective (fun ψ : (analyticInverseImage x').obj
        ((etaleAbelianInverseImage.{0, 0} x').obj A) ⟶ (analyticInverseImage x').obj G =>
          γ.inv.app A ≫ ψ) :=
      Function.bijective_iff_has_inverse.2 ⟨fun ψ => γ.hom.app A ≫ ψ, fun ψ => by simp,
        fun ψ => by simp⟩
    exact (b.homEquiv _ _).bijective.comp (hγ.comp hE)
  have hQ : Function.Bijective (fun ψ : A ⟶ (smallEtalePushforwardAb x').obj G =>
      (analyticInverseImage (𝟙 (Spec (.of ℂ)))).map ψ ≫ β.app G) := by
    have hc : (fun ψ : A ⟶ (smallEtalePushforwardAb x').obj G =>
        (analyticInverseImage (𝟙 (Spec (.of ℂ)))).map ψ ≫ β.app G) ∘ (a.homEquiv _ _) =
        (fun φ : (etaleAbelianInverseImage.{0, 0} x').obj A ⟶ G =>
          b.homEquiv _ _ (γ.inv.app A ≫ (analyticInverseImage x').map φ)) :=
      funext fun φ => map_homEquiv_comp_pushforwardBaseChange_app _ x' x' hx A G φ
    exact (Function.Bijective.of_comp_iff _ (a.homEquiv _ _).bijective).1
      ((congrArg Function.Bijective hc).mpr hR1)
  have hε : Function.Bijective (fun ψ : A ⟶ (smallEtalePushforwardAb x').obj G =>
      (analyticInverseImage (𝟙 (Spec (.of ℂ)))).map ψ) := by
    have := isEquivalence_analyticInverseImage_spec
    exact ⟨(analyticInverseImage (𝟙 (Spec (.of ℂ)))).map_injective,
      (analyticInverseImage (𝟙 (Spec (.of ℂ)))).map_surjective⟩
  have hpost : Function.Bijective (fun χ : (analyticInverseImage (𝟙 (Spec (.of ℂ)))).obj A ⟶
      (analyticInverseImage (𝟙 (Spec (.of ℂ)))).obj ((smallEtalePushforwardAb x').obj G) =>
        χ ≫ β.app G) :=
    (Function.Bijective.of_comp_iff _ hε).1 hQ
  let e := (constantSheafIso (𝟙 (Spec (.of ℂ)))).app (AddCommGrpCat.of (ULift ℤ))
  refine isIso_of_bijective_comp_constantSheaf (β.app G) ?_
  have h1 : Function.Bijective (fun ψ : (constantSheaf (Opens.grothendieckTopology
      (analyticSpace (𝟙 (Spec (.of ℂ))))) AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
        (analyticInverseImage (𝟙 (Spec (.of ℂ)))).obj ((smallEtalePushforwardAb x').obj G) =>
          e.hom ≫ ψ) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => e.inv ≫ ψ, fun ψ => by simp, fun ψ => by simp⟩
  have h2 : Function.Bijective (fun ψ : (constantSheaf (Opens.grothendieckTopology
      (analyticSpace (𝟙 (Spec (.of ℂ))))) AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶
        (analyticPushforward (𝟙 (Spec (.of ℂ))) x' x' hx).obj ((analyticInverseImage x').obj G) =>
          e.hom ≫ ψ) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => e.inv ≫ ψ, fun ψ => by simp, fun ψ => by simp⟩
  have hc : (fun ψ => e.hom ≫ ψ) ∘ (fun ψ => ψ ≫ β.app G) =
      (fun χ => χ ≫ β.app G) ∘ (fun ψ => e.hom ≫ ψ) := funext fun ψ => (Category.assoc _ _ _).symm
  exact (Function.Bijective.of_comp_iff' h2 _).1 ((congrArg Function.Bijective hc).mpr
    (hpost.comp h1))

end SpecBaseChange

section ProperBaseChange

open Stacks.EtaleCohomology

/-- A commutative square, after a functor to abelian groups, as an identity of functions. -/
theorem map_comp_map_eq_of_comp_eq {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{1})
    {P Q R T : C} {a : P ⟶ Q} {b : Q ⟶ T} {c : P ⟶ R} {d : R ⟶ T} (h : a ≫ b = c ≫ d) :
    F.map b ∘ F.map a = F.map d ∘ F.map c := by
  funext z
  change (F.map a ≫ F.map b) z = (F.map c ≫ F.map d) z
  rw [← F.map_comp, h, F.map_comp]

/-- The base change maps of two equal morphisms are invertible together. -/
theorem isIso_pushforwardBaseChange_congr {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ))
    (x' : X' ⟶ Spec (.of ℂ)) [LocallyOfFiniteType x] [LocallyOfFiniteType x'] {f₁ f₂ : X' ⟶ X}
    (h : f₁ = f₂) (hf₁ : f₁ ≫ x = x') (hf₂ : f₂ ≫ x = x') (G : EtSheaf X') :
    IsIso ((pushforwardBaseChange x x' f₁ hf₁).app G) ↔
      IsIso ((pushforwardBaseChange x x' f₂ hf₂).app G) := by
  subst h
  rfl

variable {X S : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (s : S ⟶ Spec (.of ℂ)) (p : X ⟶ S)
  (hp : p ≫ s = x) [IsProper p] [IsProper s] [LocallyOfFiniteType x]

/-- **The étale stalk of `p_*` of the unit of the fibre inclusion is invertible** (proper base
change in degree zero). -/
theorem bijective_sheafFiber_map_pushforward_unit (t : ComplexPoints s) (G : EtSheaf X) :
    Function.Bijective ((etPoint s t).sheafFiber.map ((smallEtalePushforwardAb p).map
      ((etaleInverseImageAdjunction (pullback.fst p t.hom)).unit.app G))) := by
  have := isClosedImmersion_hom s t
  let i := pullback.fst p t.hom
  let q := pullback.snd p t.hom
  let η := (etaleInverseImageAdjunction i).unit.app G
  let BC := etaleAbelianBaseChange.{0, 0} p t.hom i q pullback.condition
  have hBC : IsIso BC :=
    isIso_etaleAbelianBaseChange_of_isProper.{0} p t.hom i q (IsPullback.of_hasPullback p t.hom)
  have hη : IsIso ((etaleAbelianInverseImage.{0, 0} i).map η) :=
    isIso_etaleAbelianInverseImage_map_unit.{0, 0} i G
  have hQ : IsIso ((etaleAbelianInverseImage.{0, 0} i ⋙ etaleAbelianDirectImage.{0, 0} q).map η) :=
    Functor.map_isIso (etaleAbelianDirectImage.{0, 0} q) ((etaleAbelianInverseImage.{0, 0} i).map η)
  have h2 : IsIso ((etaleAbelianDirectImage.{0, 0} p ⋙
      etaleAbelianInverseImage.{0, 0} t.hom).map η) :=
    (NatIso.isIso_map_iff (asIso BC) η).2 hQ
  have h2' : IsIso ((etaleAbelianInverseImage.{0, 0} t.hom).map
      ((etaleAbelianDirectImage.{0, 0} p).map η)) := h2
  have h3 : IsIso ((smallEtaleStalkAb t.hom).map ((etaleAbelianDirectImage.{0, 0} p).map η)) :=
    (NatIso.isIso_map_iff (smallEtaleStalkAbIsoInverseImageGamma t.hom) _).2
      (Functor.map_isIso (Sheaf.Γ (Spec (.of ℂ)).smallEtaleTopology AddCommGrpCat.{1})
        ((etaleAbelianInverseImage.{0, 0} t.hom).map ((etaleAbelianDirectImage.{0, 0} p).map η)))
  exact (ConcreteCategory.isIso_iff_bijective _).1 h3

omit [IsProper s] [LocallyOfFiniteType x] in
/-- **The analytic stalk of `p_an,*` of the unit of the fibre inclusion is invertible**
(topological proper base change in degree zero). -/
theorem bijective_sheafFiber_map_pushforward_analyticUnit [IsProper s]
    [CompactSpace (ComplexPoints x)] (t : ComplexPoints s) (H : AnSheaf x) :
    Function.Bijective ((anPoint s t).sheafFiber.map ((analyticPushforward s x p hp).map
      ((analyticPullbackAdjunction x (fibreOver s p t) (pullback.fst p t.hom)
        (fibreInclusion_comp x s p hp t)).unit.app H))) := by
  have := isSeparated_of_comp x s p hp
  have hemb : IsInducing ((fibreIso x s p hp t).hom ≫ Stacks.subsetInclusion (analyticSpace x)
      (ProperBaseChange.fiber (analyticMap s x p hp) (ULift.up t))) := by
    rw [fibreIso_hom_comp_subsetInclusion]
    exact (isEmbedding_fibreAnalyticMap x s p hp t).isInducing
  have h1 := isIso_pullbackSh_map_of_comp (fibreIso x s p hp t) _ _
    (isIso_pullbackSh_map_unit hemb H)
  rw [fibreIso_hom_comp_subsetInclusion] at h1
  have hP := isProperMap_analyticMap x s p hp
  have h2 := isIso_sheafFiber_pushforwardSh_map (f := analyticMap s x p hp) (ULift.up t)
    hP.isClosedMap (hP.isCompact_preimage isCompact_singleton)
    (isSeparatedMap_analyticMap x s p hp)
    ((analyticPullbackAdjunction x (fibreOver s p t) (pullback.fst p t.hom)
        (fibreInclusion_comp x s p hp t)).unit.app H) h1
  exact (ConcreteCategory.isIso_iff_bijective _).1 h2

omit [IsProper s] in
/-- **Proper base change for the comparison in degree zero.** Let `p : X ⟶ S` be a proper
morphism over `ℂ`, with `S` proper over `ℂ` and `X(ℂ)` compact, whose fibres over the complex
points of `S` satisfy `PC`. Then for every torsion sheaf `G` on `X_et` the base change map
`ε^* p_* G ⟶ p_an,* ε^* G` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_of_pc_fibres [IsProper s] [CompactSpace (ComplexPoints x)]
    (hfib : ∀ t, PC (fibreOver s p t))
    (G : EtSheaf X) (hG : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G) :
    IsIso ((pushforwardBaseChange s x p hp).app G) := by
  have := isSeparated_of_comp x s p hp
  have hpt : ∀ t : ComplexPoints s, Function.Bijective
      ((anPoint s t).sheafFiber.map ((pushforwardBaseChange s x p hp).app G)) := by
    intro t
    have := isClosedImmersion_hom s t
    let i := pullback.fst p t.hom
    let q := pullback.snd p t.hom
    have hi := fibreInclusion_comp x s p hp t
    let G' := (etaleAbelianInverseImage.{0, 0} i).obj G
    have hG' := torsionSheafProperty_etaleAbelianInverseImage.{0, 0} i G hG
    -- the base change map is invertible on `i_* G'`
    have hq := isIso_pushforwardBaseChange_spec_of_bijective (fibreOver s p t) G' (hfib t G' hG' 0)
    have ht := isIso_pushforwardBaseChange_of_isFinite s (𝟙 _) t.hom t.hom_comp
      ((smallEtalePushforwardAb q).obj G')
    have h3 := (isIso_pushforwardBaseChange_comp_iff s (𝟙 _) (fibreOver s p t) t.hom t.hom_comp q
      (Category.comp_id _) G' hq).2 ht
    have h4 := (isIso_pushforwardBaseChange_congr s (fibreOver s p t) pullback.condition.symm _
      (comp_comp_eq s x (fibreOver s p t) p hp i hi) G').1 h3
    have hβi := isIso_pushforwardBaseChange_of_isFinite x (fibreOver s p t) i hi G'
    have h6 := (isIso_pushforwardBaseChange_comp_iff s x (fibreOver s p t) p hp i hi G' hβi).1 h4
    -- stalks at `t`
    let F := (anPoint s t).sheafFiber (A := AddCommGrpCat.{1})
    let β := pushforwardBaseChange s x p hp
    let η := (etaleInverseImageAdjunction i).unit.app G
    have hA : Function.Bijective (F.map (β.app ((smallEtalePushforwardAb i).obj G'))) :=
      (ConcreteCategory.isIso_iff_bijective _).1
        (Iso.isIso_hom (F.mapIso (@asIso _ _ _ _ _ h6)))
    have hB : Function.Bijective (F.map ((analyticInverseImage s).map
        ((smallEtalePushforwardAb p).map η))) := by
      have hn := (stalkIso s t).hom.naturality ((smallEtalePushforwardAb p).map η)
      have hS : ∀ A : EtSheaf S, Function.Bijective ((stalkIso s t).hom.app A) := fun A =>
        (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
      have e : (stalkIso s t).hom.app _ ∘ F.map ((analyticInverseImage s).map
          ((smallEtalePushforwardAb p).map η)) =
          (etPoint s t).sheafFiber.map ((smallEtalePushforwardAb p).map η) ∘
            (stalkIso s t).hom.app _ :=
        funext fun z => ConcreteCategory.congr_hom hn z
      exact (Function.Bijective.of_comp_iff' (hS _) _).1 ((congrArg Function.Bijective e).mpr
        ((bijective_sheafFiber_map_pushforward_unit s p t G).comp (hS _)))
    let P := analyticPushforward s x p hp
    have hC : Function.Bijective (F.map (P.map ((analyticInverseImage x).map η))) := by
      have E := map_unit_comp_pushforwardBaseChange_app x (fibreOver s p t) i hi G
      have e2 := map_comp_map_eq_of_comp_eq (P ⋙ F) E
      have h1 : Function.Bijective (F.map (P.map
          ((pushforwardBaseChange x (fibreOver s p t) i hi).app G'))) :=
        (ConcreteCategory.isIso_iff_bijective _).1
          (Iso.isIso_hom ((P ⋙ F).mapIso (@asIso _ _ _ _ _ hβi)))
      have h2 : Function.Bijective (F.map (P.map ((analyticPushforward x (fibreOver s p t) i hi).map
          ((inverseImageIso x (fibreOver s p t) i hi).inv.app G)))) :=
        (ConcreteCategory.isIso_iff_bijective _).1
          (Iso.isIso_hom ((P ⋙ F).mapIso ((analyticPushforward x (fibreOver s p t) i hi).mapIso
            ((inverseImageIso x (fibreOver s p t) i hi).app G).symm)))
      have h3 := bijective_sheafFiber_map_pushforward_analyticUnit x s p hp t
        ((analyticInverseImage x).obj G)
      exact (Function.Bijective.of_comp_iff' h1 _).1 ((congrArg Function.Bijective e2).mpr
        (h2.comp h3))
    have nat := β.naturality η
    have e3 := map_comp_map_eq_of_comp_eq F nat
    exact (Function.Bijective.of_comp_iff' hC _).1 ((congrArg Function.Bijective e3).mp
      (hA.comp hB))
  have : ∀ Φ : (_root_.Opens.pointsGrothendieckTopology (analyticSpace s)).FullSubcategory,
      IsIso (Φ.obj.sheafFiber.map ((pushforwardBaseChange s x p hp).app G)) := by
    intro Φ
    obtain ⟨w, hw⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
    rw [← hw]
    exact (ConcreteCategory.isIso_iff_bijective _).2 (hpt w.down)
  exact ((_root_.Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
    (analyticSpace s)).jointlyReflectIsomorphisms AddCommGrpCat.{1}).isIso _

end ProperBaseChange

end AlgebraicGeometry.Scheme.ComplexPoints
