module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.OpenProperExchangeMapDerived
public import WeilFrontier.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.CategoryTheory.Sites.DisjointCoverSections
public import Weil.Attr

/-!
# The exchange morphism `j_! Rf_* ⟶ Rf'_* i_!` is an isomorphism over `Y`

Consider a commutative square of schemes
```
  X --i--> X'
  |        |
  f        f'
  v        v
  Y --j--> Y'
```
with `i` and `j` open immersions, `f` proper and `f'` separated, and the morphism
`(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` of bounded below derived categories represented by the exchange
chain map `θ_J : j_! f_* (J|_X) ⟶ f'_* J`, for an injective resolution `i_! F ⟶ J`
(`AlgebraicGeometry.openProperExchangeDerivedMap`). Then for every `v` the restriction to `Y` of
`H^v(*) : j_! R^v f_* F ⟶ R^v f'_* (i_! F)` is an isomorphism.

Put `X₁ = X' ×_{Y'} Y`. The morphism `X ⟶ X₁` induced by `i` is an open immersion with closed
image, so `X₁` is the disjoint union of `X` and of the open subscheme `X'' = X₁ ∖ X`, with
`f'' : X'' ⟶ Y`. For `V` étale over `Y` the scheme `X' ×_{Y'} V` is accordingly the disjoint union
of `X ×_Y V` and `X'' ×_Y V`, and for every sheaf `G` of `Λ`-modules on `X'` the sequence
```
0 ⟶ f_* (G|_X) ⟶ j^{-1} f'_* G ⟶ f''_* (G|_{X''}) ⟶ 0
```
is short exact, the first map being the unit of `j_! ⊣ j^{-1}` followed by the restriction of
`θ_G`: an exchange morphism sends a section `s` over `X ×_Y V` to the section which is `s` on
`X ×_Y V` and zero on `X'' ×_Y V`, and the sheaf condition for the disjoint cover gives the
exactness. Applied to `J` termwise it gives a short exact sequence of complexes whose third term
`f''_* (J|_{X''})` is acyclic: `J|_{X''}` is a bounded below complex of injectives
quasi-isomorphic to `(i_! F)|_{X''} = 0`, hence homotopic to zero. So `j^{-1} θ_J` is a
quasi-isomorphism, and restriction to `Y`, being exact, commutes with cohomology sheaves.

## Main results

* `AlgebraicGeometry.isIso_restriction_homology_openProperExchangeDerivedMap`: the restriction
  to `Y` of `H^v(*)` is an isomorphism.

## Implementation notes

The sheaves live on Mathlib's small étale sites, as for
`AlgebraicGeometry.openProperExchangeDerivedMap`; restriction to `Y` is
`Stacks.EtaleCohomology.etaleModuleRestriction`, and `H^v` is the cohomology functor of the
bounded below derived category. The source's abelian sheaves are the case `Λ = ℤ`. The
exchange morphisms enter as a natural transformation `α` all of whose components are exchange
morphisms (`AlgebraicGeometry.IsOpenProperExchangeMorphism`); an object of `D⁺` is presented by
a bounded below complex `F` together with an injective resolution of `i_! F`, the morphism `(*)`
not depending on the resolution (`AlgebraicGeometry.openProperExchangeDerivedMap_eq_of_resolution`).
The source takes `F` with torsion cohomology sheaves; the argument does not use it, and the
result is stated for every bounded below `F`. The source assumes all schemes separated; only the
separatedness of `f'` is used, to make the image of `X` in `X₁` closed.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.8.5, p. 88.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale Stacks.EtaleCohomology

universe r u

namespace AlgebraicGeometry

section Topology

variable {X' Y Y' Z : Scheme.{u}} (j : Y ⟶ Y') (f' : X' ⟶ Y')

/-- The morphism `Z ×_Y V ⟶ X' ×_{Y'} V` induced by a commutative square `a ≫ f' = g ≫ j`. -/
private def baseChangeLift {a : Z ⟶ X'} {g : Z ⟶ Y} (hag : a ≫ f' = g ≫ j) {V : Scheme.{u}}
    (v : V ⟶ Y) : pullback v g ⟶ pullback (v ≫ j) f' :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) (by
    rw [Category.assoc, hag, pullback.condition_assoc])

private theorem isPullback_baseChangeLift [Mono j] {a : Z ⟶ X'} {g : Z ⟶ Y}
    (hag : a ≫ f' = g ≫ j) {V : Scheme.{u}} (v : V ⟶ Y) :
    IsPullback (baseChangeLift j f' hag v) (pullback.snd v g) (pullback.snd (v ≫ j) f') a := by
  have hR := IsPullback.of_hasPullback (v ≫ j) f'
  have h2 : IsPullback g (𝟙 Z) j (g ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have hbig := (IsPullback.of_hasPullback v g).paste_vert h2
  rw [Category.comp_id, ← hag] at hbig
  refine IsPullback.of_right ?_ ?_ hR
  · rw [baseChangeLift, pullback.lift_fst]; exact hbig
  · exact pullback.lift_snd _ _ _

private theorem range_baseChangeLift [Mono j] {a : Z ⟶ X'} {g : Z ⟶ Y}
    (hag : a ≫ f' = g ≫ j) {V : Scheme.{u}} (v : V ⟶ Y) :
    Set.range (baseChangeLift j f' hag v).base =
      (pullback.snd (v ≫ j) f').base ⁻¹' Set.range a.base := by
  have hpb := isPullback_baseChangeLift j f' hag v
  rw [← Scheme.Pullback.range_fst, ← hpb.isoPullback_hom_fst]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨hpb.isoPullback.hom y, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨hpb.isoPullback.inv y, by
      rw [← Scheme.Hom.comp_apply (hpb.isoPullback.inv), Iso.inv_hom_id_assoc]⟩

end Topology

section Clopen

variable {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
  (h : i ≫ f' = f ≫ j) [IsOpenImmersion i] [IsOpenImmersion j] [IsProper f] [IsSeparated f']

/-- The complement `X₁ ∖ X` of the open and closed subscheme `X` of `X₁ = X' ×_{Y'} Y`. -/
private def complementOpen : (pullback f' j).Opens :=
  ⟨(Set.range (pullback.lift i f h).base)ᶜ,
    (isOpenImmersion_and_isClosed_range_pullbackLift i j f f' h).2.isOpen_compl⟩

/-- The open immersion `X₁ ∖ X ⟶ X'`. -/
private def complementι : (complementOpen i j h : Scheme.{u}) ⟶ X' :=
  (complementOpen i j h).ι ≫ pullback.fst f' j

/-- The morphism `X₁ ∖ X ⟶ Y`. -/
private def complementBase : (complementOpen i j h : Scheme.{u}) ⟶ Y :=
  (complementOpen i j h).ι ≫ pullback.snd f' j

private theorem complementι_comp : complementι i j h ≫ f' = complementBase i j h ≫ j := by
  simp [complementι, complementBase, pullback.condition]

private instance isOpenImmersion_complementι : IsOpenImmersion (complementι i j h) := by
  unfold complementι; infer_instance

private theorem disjoint_range_complementι :
    Disjoint (Set.range i.base) (Set.range (complementι i j h).base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨z, hz⟩
  have hinj := (pullback.fst f' j).isOpenEmbedding.injective
  have h1 : (pullback.fst f' j).base ((pullback.lift i f h).base x) = i.base x := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [complementι, Scheme.Hom.comp_apply, ← h1] at hz
  exact z.2 ⟨x, (hinj hz).symm⟩

private theorem mem_range_or_mem_range_complementι (x : X') (hx : f'.base x ∈ Set.range j.base) :
    x ∈ Set.range i.base ∨ x ∈ Set.range (complementι i j h).base := by
  rw [← Set.mem_preimage, ← Scheme.Pullback.range_fst] at hx
  obtain ⟨z, rfl⟩ := hx
  by_cases hz : z ∈ Set.range (pullback.lift i f h).base
  · obtain ⟨w, rfl⟩ := hz
    left
    exact ⟨w, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩
  · right
    have hz' : z ∈ complementOpen i j h := hz
    refine ⟨⟨z, hz'⟩, ?_⟩
    simp [complementι]
    rfl

end Clopen

section Pieces

variable {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
  (h : i ≫ f' = f ≫ j) [IsOpenImmersion i] [IsOpenImmersion j] [IsProper f] [IsSeparated f']

private theorem disjoint_range_baseChangeLift {V : Scheme.{u}} (v : V ⟶ Y) :
    Disjoint (Set.range (baseChangeLift j f' h v).base)
      (Set.range (baseChangeLift j f' (complementι_comp i j h) v).base) := by
  rw [range_baseChangeLift, range_baseChangeLift]
  exact (disjoint_range_complementι i j h).preimage _

private theorem mem_range_baseChangeLift_or {V : Scheme.{u}} (v : V ⟶ Y)
    (x : ↥(pullback (v ≫ j) f')) :
    x ∈ Set.range (baseChangeLift j f' h v).base ∨
      x ∈ Set.range (baseChangeLift j f' (complementι_comp i j h) v).base := by
  rw [range_baseChangeLift, range_baseChangeLift]
  refine mem_range_or_mem_range_complementι i j h _ ⟨v.base ((pullback.fst (v ≫ j) f').base x), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ← pullback.condition]

private instance isOpenImmersion_baseChangeLift {Z : Scheme.{u}} {a : Z ⟶ X'} [IsOpenImmersion a]
    {g : Z ⟶ Y} (hag : a ≫ f' = g ≫ j) {V : Scheme.{u}} (v : V ⟶ Y) :
    IsOpenImmersion (baseChangeLift j f' hag v) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_baseChangeLift j f' hag v).flip
    ‹_›

end Pieces

section RestrictionBaseChange

variable (Λ : Type r) [Ring Λ] {X' Y Y' Z : Scheme.{u}} (j : Y ⟶ Y') [Etale j] (f' : X' ⟶ Y')
  {a : Z ⟶ X'} [Etale a] {g : Z ⟶ Y} (hag : a ≫ f' = g ≫ j)

/-- For `V` étale over `Y`, the morphism `Z ×_Y V ⟶ X' ×_{Y'} V` of the small étale site of `X'`
induced by the square `a ≫ f' = g ≫ j`. -/
private def baseChangeInclusion (V : Y.Etale) :
    (smallEtaleCompose a).obj ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange f').obj ((smallEtaleCompose j).obj V) :=
  MorphismProperty.Over.homMk (baseChangeLift j f' hag V.hom) (pullback.lift_snd _ _ _) trivial

private theorem baseChangeInclusion_left (V : Y.Etale) :
    (baseChangeInclusion j f' hag V).left = baseChangeLift j f' hag V.hom := rfl

private theorem baseChangeInclusion_naturality {V₁ V₂ : Y.Etale} (m : V₁ ⟶ V₂) :
    (smallEtaleCompose a).map ((Stacks.EtaleCohomology.smallEtaleBaseChange g).map m) ≫
        baseChangeInclusion j f' hag V₂ =
      baseChangeInclusion j f' hag V₁ ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChange f').map ((smallEtaleCompose j).map m) := by
  ext : 1
  have hm : m.left ≫ V₂.hom = V₁.hom := MorphismProperty.Over.w m
  change pullback.lift (pullback.fst V₁.hom g ≫ m.left) (pullback.snd V₁.hom g)
      (by rw [Category.assoc, hm, pullback.condition]) ≫ baseChangeLift j f' hag V₂.hom =
    baseChangeLift j f' hag V₁.hom ≫ pullback.lift (pullback.fst (V₁.hom ≫ j) f' ≫ m.left)
      (pullback.snd (V₁.hom ≫ j) f') (by rw [Category.assoc, reassoc_of% hm, pullback.condition])
  apply pullback.hom_ext
  · simp only [baseChangeLift, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [baseChangeLift, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

/-- The transformation `j^{-1} f'_* ⟶ g_* a^{-1}` of a commutative square `a ≫ f' = g ≫ j` with `a`,
`j` étale: over `V` étale over `Y`, the restriction of sections along `Z ×_Y V ⟶ X' ×_{Y'} V`. -/
private def restrictionBaseChange :
    etaleModuleDirectImage.{u, r} Λ f' ⋙ etaleModuleRestriction.{u, r} Λ j ⟶
      etaleModuleRestriction.{u, r} Λ a ⋙ etaleModuleDirectImage.{u, r} Λ g where
  app G := ⟨{
    app := fun V => G.obj.map (baseChangeInclusion j f' hag V.unop).op
    naturality := fun V₁ V₂ m => by
      change G.obj.map _ ≫ G.obj.map _ = G.obj.map _ ≫ G.obj.map _
      rw [← G.obj.map_comp, ← G.obj.map_comp]
      exact (congrArg (fun q => G.obj.map q.op)
        (baseChangeInclusion_naturality j f' hag m.unop)).symm }⟩
  naturality G₁ G₂ φ := by
    ext V : 3
    exact (φ.hom.naturality _).symm

private theorem restrictionBaseChange_app_hom_app (G : EtaleModules.{u, r} Λ X') (V : Y.Etale) :
    ((restrictionBaseChange Λ j f' hag).app G).hom.app (op V) =
      G.obj.map (baseChangeInclusion j f' hag V).op := rfl

end RestrictionBaseChange

/-- A short complex of sheaves whose complexes of sections are all short exact is short exact. -/
private theorem shortExact_of_forall_sections_shortExact {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A : Type*} [Category* A] [Abelian A] [HasSheafify J A]
    (S : ShortComplex (Sheaf J A))
    (h : ∀ U : Cᵒᵖ, (S.map ((sheafSections J A).obj U)).ShortExact) : S.ShortExact := by
  have hmono : Mono S.f := by
    have : ∀ U : Cᵒᵖ, Mono (((sheafToPresheaf J A).map S.f).app U) := fun U => (h U).mono_f
    exact (sheafToPresheaf J A).mono_of_mono_map (NatTrans.mono_of_mono_app _)
  have hepi : Epi S.g := by
    constructor
    intro Z β γ hβγ
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    have : Epi (((sheafSections J A).obj U).map S.g) := (h U).epi_g
    have h2 : ((sheafSections J A).obj U).map S.g ≫ ((sheafSections J A).obj U).map β =
        ((sheafSections J A).obj U).map S.g ≫ ((sheafSections J A).obj U).map γ := by
      rw [← Functor.map_comp, ← Functor.map_comp, hβγ]
    exact (cancel_epi _).mp h2
  refine ShortComplex.ShortExact.mk' (S.exact_iff_epi_kernel_lift.mpr ?_) hmono hepi
  constructor
  intro Z β γ hβγ
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  set E := (sheafSections J A).obj U with hE
  have hpl : PreservesFiniteLimits E := by
    rw [hE]
    exact comp_preservesFiniteLimits (sheafToPresheaf J A) ((evaluation _ _).obj U)
  have hek : Epi (kernel.lift (E.map S.g) (E.map S.f) (S.map E).zero) :=
    (h U).exact.epi_kernelLift
  have hcomp : Epi (E.map (kernel.lift S.g S.f S.zero) ≫ kernelComparison S.g E) := by
    rw [map_lift_kernelComparison]
    infer_instance
  have hfin : Epi (E.map (kernel.lift S.g S.f S.zero)) :=
    (epi_comp_iff_of_isIso (E.map (kernel.lift S.g S.f S.zero)) (kernelComparison S.g E)).mp hcomp
  have h2 : E.map (kernel.lift S.g S.f S.zero) ≫ E.map β =
      E.map (kernel.lift S.g S.f S.zero) ≫ E.map γ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hβγ]
  exact (cancel_epi _).mp h2

section Glue

variable (Λ : Type r) [Ring Λ] {X' : Scheme.{u}}

/-- The sections of a sheaf of `Λ`-modules over an object `T` of the small étale site that is the
disjoint union of two open subschemes `P` and `R` are the pairs of sections over `P` and `R`. -/
private theorem existsUnique_glue (G : EtaleModules.{u, r} Λ X') {T P R : X'.Etale}
    (p : P ⟶ T) (w : R ⟶ T) [IsOpenImmersion p.left] [IsOpenImmersion w.left]
    (hd : Disjoint (Set.range p.left.base) (Set.range w.left.base))
    (hc : ∀ x, x ∈ Set.range p.left.base ∨ x ∈ Set.range w.left.base)
    (s : G.obj.obj (op P)) (t : G.obj.obj (op R)) :
    ∃! b : G.obj.obj (op T), (G.obj.map p.op).hom b = s ∧ (G.obj.map w.op).hom b = t := by
  have hG : Presieve.IsSheaf X'.smallEtaleTopology
      (G.obj ⋙ CategoryTheory.forget (ModuleCat.{max (u + 1) r} Λ)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf X'.smallEtaleTopology
      G.obj (CategoryTheory.forget (ModuleCat.{max (u + 1) r} Λ)) G.property)
  let V : Bool → X'.Etale := fun b => cond b P R
  let π : ∀ b, V b ⟶ T := fun b => Bool.rec (motive := fun b => V b ⟶ T) w p b
  have hmono : ∀ b, Mono (π b) := by
    intro b
    refine ⟨fun g₁ g₂ e => ?_⟩
    have : Mono (π b).left := by cases b <;> (dsimp [π]; infer_instance)
    ext : 1
    exact (cancel_mono (π b).left).1 (congrArg (fun q => q.left) e)
  have hrange : ∀ x, ∃ b, x ∈ Set.range (π b).left.base := by
    intro x
    rcases hc x with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  have hcov : Sieve.ofArrows V π ∈ X'.smallEtaleTopology T := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hrange x)
  have hdisj : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ {Z : X'.Etale} (g₁ : Z ⟶ V b₁) (g₂ : Z ⟶ V b₂),
      g₁ ≫ π b₁ = g₂ ≫ π b₂ → (⊥ : Sieve Z) ∈ X'.smallEtaleTopology Z := by
    intro b₁ b₂ hb Z g₁ g₂ e
    refine bot_mem_smallEtaleTopology_of_isEmpty Z ⟨fun z => ?_⟩
    have e' : (π b₁).left.base (g₁.left.base z) = (π b₂).left.base (g₂.left.base z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun q => q.left.base z) e
    cases b₁ <;> cases b₂
    · exact hb rfl
    · exact Set.disjoint_left.1 hd ⟨_, e'.symm⟩ ⟨_, rfl⟩
    · exact Set.disjoint_left.1 hd ⟨_, e'⟩ ⟨_, rfl⟩
    · exact hb rfl
  obtain ⟨b, hb, hu⟩ := hG.existsUnique_section_of_disjoint_arrows π hcov hmono hdisj
    (fun k => Bool.rec (motive := fun k =>
      (G.obj ⋙ CategoryTheory.forget (ModuleCat.{max (u + 1) r} Λ)).obj (op (V k))) t s k)
  refine ⟨b, ⟨hb true, hb false⟩, fun b' hb' => hu b' ?_⟩
  intro k
  cases k
  · exact hb'.2
  · exact hb'.1

end Glue

private theorem sourceDescendIso_structureHomToSource_inv {Y Y' : Scheme.{u}} (j : Y ⟶ Y')
    [Etale j] (V : Y.Etale) : (sourceDescendIso j (structureHomToSource j V)).inv = 𝟙 _ := by
  ext : 1; rfl

section Exchange

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') {f : X ⟶ Y}
  {f' : X' ⟶ Y'} [Etale i] [Etale j]
  (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
    etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')


/-- The transformation `f_* (G|_X) ⟶ j^{-1} f'_* G`: the unit of `j_! ⊣ j^{-1}` followed by the
restriction to `Y` of the exchange transformation `j_! f_* (G|_X) ⟶ f'_* G`. -/
private def restrictedExchange :
    etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f ⟶
      etaleModuleDirectImage.{u, r} Λ f' ⋙ etaleModuleRestriction.{u, r} Λ j :=
  Functor.whiskerLeft (etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f)
      (etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit ≫
    Functor.whiskerRight (exchangeCounitTransformation Λ i j α) (etaleModuleRestriction.{u, r} Λ j)

/-- Over `V` étale over `Y`, the transformation `f_* (G|_X) ⟶ j^{-1} f'_* G` sends `s` to the
image under the counit `ε : i_! (G|_X) ⟶ G` of the exchange section `α(c [φ, s])`, `φ` being the
structure morphism `V ⟶ Y`. -/
private theorem restrictedExchange_app_apply (G : EtaleModules.{u, r} Λ X') (V : Y.Etale)
    (s : ((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f).obj G).obj.obj
      (op V)) :
    (((restrictedExchange Λ i j α).app G).hom.app (op V)).hom s =
      (((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.app
        (op (ExchangeSquare.targetObj f' ((smallEtaleCompose j).obj V)))).hom
        (exchangeSection Λ i j ((etaleModuleRestriction.{u, r} Λ i).obj G)
          (α.app ((etaleModuleRestriction.{u, r} Λ i).obj G)) (structureHomToSource j V) s) := by
  have hu := ι_comp_extensionByZeroPresheafToSheaf_app Λ j
    ((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f).obj G)
    ((smallEtaleCompose j).obj V) (structureHomToSource j V)
  rw [sourceDescendIso_structureHomToSource_inv] at hu
  have e1 := ((etaleModuleExtensionByZero.{u, r} Λ j).obj
    ((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f).obj G)).obj.map_id
      (op ((smallEtaleCompose j).obj V))
  have key := hu.trans ((congrArg (fun q => _ ≫ q) e1).trans (Category.comp_id _))
  refine (congrArg (fun q => (((exchangeCounitTransformation Λ i j α).app G).hom.app
    (op ((smallEtaleCompose j).obj V))).hom (q.hom s)) key.symm).trans ?_
  rw [exchangeCounitTransformation_app]
  rfl

end Exchange

section Formulas

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') {f : X ⟶ Y}
  {f' : X' ⟶ Y'} (h : i ≫ f' = f ≫ j) [IsOpenImmersion i] [IsOpenImmersion j] [IsProper f]
  [IsSeparated f']
  (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
    etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
  (hα : ∀ G, IsOpenProperExchangeMorphism Λ i j h G (α.app G))

omit [IsProper f] [IsSeparated f'] in
include hα in
/-- The section `θ(s)` restricts to `s` on `X ×_Y V`. -/
private theorem restrictedExchange_restrict_source (G : EtaleModules.{u, r} Λ X') (V : Y.Etale)
    (s : ((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f).obj G).obj.obj
      (op V)) :
    (G.obj.map (baseChangeInclusion j f' h V).op).hom
      ((((restrictedExchange Λ i j α).app G).hom.app (op V)).hom s) = s := by
  rw [restrictedExchange_app_apply]
  have hn := ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.naturality
    (baseChangeInclusion j f' h V).op
  have e1 := ((etaleModuleRestriction.{u, r} Λ i).obj G).obj.map_id
    (op ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V))
  refine (congrArg (fun q => ModuleCat.Hom.hom q (exchangeSection Λ i j
    ((etaleModuleRestriction.{u, r} Λ i).obj G) (α.app ((etaleModuleRestriction.{u, r} Λ i).obj G))
    (structureHomToSource j V) s)) hn).symm.trans ?_
  refine (congrArg (fun q => (((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.app
    _).hom q) ((hα ((etaleModuleRestriction.{u, r} Λ i).obj G)).map_inclusion
      (structureHomToSource j V) s)).trans ?_
  refine (etaleModuleExtensionByZeroAdj_counit_app_apply Λ i G
    ((smallEtaleCompose i).obj ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V))
    (structureHomToSource i ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)) s).trans ?_
  rw [sourceDescendIso_structureHomToSource_inv]
  exact congrArg (fun q => q.hom s) e1

include hα in
/-- The section `θ(s)` restricts to zero on the complement `(X₁ ∖ X) ×_Y V`. -/
private theorem restrictedExchange_restrict_complement (G : EtaleModules.{u, r} Λ X')
    (V : Y.Etale)
    (s : ((etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f).obj G).obj.obj
      (op V)) :
    (G.obj.map (baseChangeInclusion j f' (complementι_comp i j h) V).op).hom
      ((((restrictedExchange Λ i j α).app G).hom.app (op V)).hom s) = 0 := by
  rw [restrictedExchange_app_apply]
  have hn := ((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.naturality
    (baseChangeInclusion j f' (complementι_comp i j h) V).op
  refine (congrArg (fun q => ModuleCat.Hom.hom q (exchangeSection Λ i j
    ((etaleModuleRestriction.{u, r} Λ i).obj G) (α.app ((etaleModuleRestriction.{u, r} Λ i).obj G))
    (structureHomToSource j V) s)) hn).symm.trans ?_
  refine (congrArg (fun q => (((etaleModuleExtensionByZeroAdj.{u, r} Λ i).counit.app G).hom.app
    _).hom q) ((hα ((etaleModuleRestriction.{u, r} Λ i).obj G)).map_eq_zero_of_disjoint
      (structureHomToSource j V) s (baseChangeInclusion j f' (complementι_comp i j h) V)
      (disjoint_range_baseChangeLift i j h V.hom).symm)).trans ?_
  exact map_zero _

include hα in
private theorem restrictedExchange_comp_restrictionBaseChange (G : EtaleModules.{u, r} Λ X') :
    (restrictedExchange Λ i j α).app G ≫
      (restrictionBaseChange Λ j f' (complementι_comp i j h)).app G = 0 := by
  apply Sheaf.hom_ext; apply NatTrans.ext; funext V
  ext s
  exact restrictedExchange_restrict_complement Λ i j h α hα G V.unop s

include hα in
/-- For every sheaf `G` on `X'`, the sequence
`0 ⟶ f_* (G|_X) ⟶ j^{-1} f'_* G ⟶ f''_* (G|_{X₁ ∖ X}) ⟶ 0` is short exact. -/
private theorem restrictedExchange_shortExact (G : EtaleModules.{u, r} Λ X') :
    (ShortComplex.mk ((restrictedExchange Λ i j α).app G)
      ((restrictionBaseChange Λ j f' (complementι_comp i j h)).app G)
      (restrictedExchange_comp_restrictionBaseChange Λ i j h α hα G)).ShortExact := by
  refine shortExact_of_forall_sections_shortExact _ fun V => ?_
  obtain ⟨V⟩ := V
  have : IsOpenImmersion (baseChangeInclusion j f' h V).left :=
    isOpenImmersion_baseChangeLift j h V.hom
  have : IsOpenImmersion (baseChangeInclusion j f' (complementι_comp i j h) V).left :=
    isOpenImmersion_baseChangeLift j (complementι_comp i j h) V.hom
  have hglue := existsUnique_glue Λ G (baseChangeInclusion j f' h V)
    (baseChangeInclusion j f' (complementι_comp i j h) V)
    (disjoint_range_baseChangeLift i j h V.hom) (mem_range_baseChangeLift_or i j h V.hom)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro b hb
    refine ⟨(G.obj.map (baseChangeInclusion j f' h V).op).hom b, ?_⟩
    obtain ⟨c, -, hc⟩ := hglue ((G.obj.map (baseChangeInclusion j f' h V).op).hom b) 0
    refine (hc _ ⟨restrictedExchange_restrict_source Λ i j h α hα G V _,
      restrictedExchange_restrict_complement Λ i j h α hα G V _⟩).trans
      (hc _ ⟨rfl, hb⟩).symm
  · rw [ModuleCat.mono_iff_injective]
    intro s₁ s₂ e
    exact (restrictedExchange_restrict_source Λ i j h α hα G V s₁).symm.trans
      ((congrArg (G.obj.map (baseChangeInclusion j f' h V).op).hom e).trans
        (restrictedExchange_restrict_source Λ i j h α hα G V s₂))
  · rw [ModuleCat.epi_iff_surjective]
    intro c
    obtain ⟨b, ⟨-, hb⟩, -⟩ := hglue 0 c
    exact ⟨b, hb⟩

end Formulas

/-- A functor preserving homology carries a morphism of complexes inducing an isomorphism on
`v`-th homology after applying the functor termwise to an isomorphism after applying it to the
`v`-th homology. -/
private theorem isIso_map_homologyMap_of_quasiIsoAt {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive] [G.PreservesHomology]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (v : ℤ)
    [QuasiIsoAt ((G.mapHomologicalComplex _).map φ) v] :
    IsIso (G.map (HomologicalComplex.homologyMap φ v)) := by
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) v).map φ) G
  have h1 : IsIso (ShortComplex.homologyMap
      (G.mapShortComplex.map ((HomologicalComplex.shortComplexFunctor C _ v).map φ))) :=
    (quasiIsoAt_iff_isIso_homologyMap ((G.mapHomologicalComplex _).map φ) v).1 inferInstance
  have h2 : IsIso ((((HomologicalComplex.shortComplexFunctor C _ v).obj K).mapHomologyIso G).hom ≫
      G.map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor C _ v).map φ))) := by
    rw [← hn]; infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    (((HomologicalComplex.shortComplexFunctor C _ v).obj K).mapHomologyIso G).hom
    (G.map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor C _ v).map φ))) _ h2

section Complexes

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') {f : X ⟶ Y}
  {f' : X' ⟶ Y'} (h : i ≫ f' = f ≫ j) [IsOpenImmersion i] [IsOpenImmersion j] [IsProper f]
  [IsSeparated f']

private theorem isZero_restriction_complementι_extensionByZero (M : EtaleModules.{u, r} Λ X) :
    IsZero ((etaleModuleRestriction.{u, r} Λ (complementι i j h)).obj
      ((etaleModuleExtensionByZero.{u, r} Λ i).obj M)) :=
  (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ (complementι i j h) i
    (disjoint_range_complementι i j h).symm M).of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (complementι i j h)).app _).symm

/-- For an injective resolution `u : i_! F ⟶ J`, the complex `f''_* (J|_{X₁ ∖ X})` is acyclic:
`J|_{X₁ ∖ X}` is a bounded below complex of injectives quasi-isomorphic to
`(i_! F)|_{X₁ ∖ X} = 0`, hence homotopic to zero. -/
private theorem acyclic_directImage_restriction_complementι
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    (((etaleModuleRestriction.{u, r} Λ (complementι i j h) ⋙
      etaleModuleDirectImage.{u, r} Λ (complementBase i j h)).mapHomologicalComplex _).obj
        J.obj).Acyclic := by
  let r := etaleModuleRestriction.{u, r} Λ (complementι i j h)
  let K := r.mapCochainComplexPlus.obj J
  obtain ⟨d, hd⟩ := K.property
  have hzero : IsZero ((r.mapHomologicalComplex _).obj
      ((etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F).obj) := by
    rw [IsZero.iff_id_eq_zero]
    ext n : 1
    exact (isZero_restriction_complementι_extensionByZero Λ i j h _).eq_of_src _ _
  have hinj := (CochainComplex.bijective_precomp_quotient_map_of_quasiIso_of_injective
    ((r.mapHomologicalComplex _).map u.hom) K.obj d).1
  have h1 : 𝟙 ((HomotopyCategory.quotient _ _).obj K.obj) = 0 :=
    hinj (((HomotopyCategory.quotient _ _).map_isZero hzero).eq_of_src _ _)
  let H := HomotopyCategory.homotopyOfEq (𝟙 K.obj) 0 (by
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]; exact h1)
  let H' := (etaleModuleDirectImage.{u, r} Λ (complementBase i j h)).mapHomotopy H
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have := H'.homologyMap_eq n
  rw [CategoryTheory.Functor.map_id, Functor.map_zero, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at this
  exact this

variable (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
    etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
  (hα : ∀ G, IsOpenProperExchangeMorphism Λ i j h G (α.app G))

include hα in
/-- For an injective resolution `u : i_! F ⟶ J`, the chain map `f_* (J|_X) ⟶ j^{-1} f'_* J` is a
quasi-isomorphism. -/
private theorem quasiIso_restrictedExchange
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    QuasiIso ((NatTrans.mapHomologicalComplex (restrictedExchange Λ i j α) _).app J.obj) := by
  let S := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (restrictedExchange Λ i j α) _).app J.obj)
    ((NatTrans.mapHomologicalComplex (restrictionBaseChange Λ j f' (complementι_comp i j h))
      _).app J.obj) (by
        ext n : 1
        rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
        exact restrictedExchange_comp_restrictionBaseChange Λ i j h α hα (J.obj.X n))
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    restrictedExchange_shortExact Λ i j h α hα (J.obj.X n)
  have hac := acyclic_directImage_restriction_complementι Λ i j h u
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have e2 := hS.homology_exact₂ n
  have e1 := hS.homology_exact₁ (n - 1) n (by simp)
  have : Epi (HomologicalComplex.homologyMap S.f n) :=
    e2.epi_f (((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hac n)).eq_of_tgt _ _)
  have : Mono (HomologicalComplex.homologyMap S.f n) :=
    e1.mono_g (((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hac (n - 1))).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end Complexes

section Main

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') {f : X ⟶ Y}
  {f' : X' ⟶ Y'} (h : i ≫ f' = f ≫ j) [IsOpenImmersion i] [IsOpenImmersion j] [IsProper f]
  [IsSeparated f']

/-- **The exchange morphism becomes an isomorphism over `Y`.** Consider a commutative square
`i ≫ f' = f ≫ j` of schemes with `i : X ⟶ X'`, `j : Y ⟶ Y'` open immersions, `f` proper and
`f'` separated, and let `α : j_! f_* ⟶ f'_* i_!` be the exchange morphisms
(`AlgebraicGeometry.IsOpenProperExchangeMorphism`). For a bounded below complex `F` of sheaves of
`Λ`-modules on `X` and an injective resolution `u : i_! F ⟶ J`, let
`(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` be the morphism represented by the exchange chain map
(`AlgebraicGeometry.openProperExchangeDerivedMap`). Then for every `v : ℤ` the restriction to `Y`
of `H^v(*) : j_! R^v f_* F ⟶ R^v f'_* (i_! F)` is an isomorphism. -/
@[weil "lem_fk108_open_proper_exchange_map_restriction_iso"]
theorem isIso_restriction_homology_openProperExchangeDerivedMap
    (α : etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f')
    (hα : ∀ G, IsOpenProperExchangeMorphism Λ i j h G (α.app G))
    {F : CochainComplex.Plus (EtaleModules.{u, r} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, r} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, r} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] (v : ℤ) :
    IsIso ((etaleModuleRestriction.{u, r} Λ j).map
      ((DerivedCategory.Plus.homologyFunctor _ v).map
        (openProperExchangeDerivedMap Λ i j α u))) := by
  set θ := exchangeChainMap Λ i j α J.obj
  let unitC := (NatTrans.mapHomologicalComplex (Functor.whiskerLeft
    (etaleModuleRestriction.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f)
      (etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit) (ComplexShape.up ℤ)).app J.obj
  have hunit : IsIso unitC := by
    have : ∀ n, IsIso (unitC.f n) := fun n => by
      change IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app _); infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have hfac : (NatTrans.mapHomologicalComplex (restrictedExchange Λ i j α) _).app J.obj =
      unitC ≫ ((etaleModuleRestriction.{u, r} Λ j).mapHomologicalComplex _).map θ := by
    ext n : 1
    rfl
  have hq := quasiIso_restrictedExchange Λ i j h α hα u
  rw [hfac, quasiIso_iff_comp_left] at hq
  have : QuasiIsoAt (((etaleModuleRestriction.{u, r} Λ j).mapHomologicalComplex _).map θ) v :=
    inferInstance
  have h4 : IsIso ((etaleModuleRestriction.{u, r} Λ j).map (HomologicalComplex.homologyMap θ v)) :=
    isIso_map_homologyMap_of_quasiIsoAt _ θ v
  let E : HomotopyCategory.quotient (EtaleModules.{u, r} Λ Y') (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor _ v ≅
      HomologicalComplex.homologyFunctor _ _ v :=
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactorsh _ v) ≪≫
      HomotopyCategory.homologyFunctorFactors _ _ v
  have h5 := (NatIso.isIso_map_iff (Functor.isoWhiskerRight E
    (etaleModuleRestriction.{u, r} Λ j)) θ).2 h4
  have h6 : IsIso ((etaleModuleRestriction.{u, r} Λ j).map
      ((DerivedCategory.Plus.homologyFunctor _ v).map (DerivedCategory.Plus.Qh.map
        (Adjunction.exchangeHomotopyCategoryPlusMap (etaleModuleDirectImage.{u, r} Λ f)
          (etaleModuleExtensionByZero.{u, r} Λ j) (etaleModuleDirectImage.{u, r} Λ f')
          (exchangeCounitTransformation Λ i j α) J)))) := h5
  rw [openProperExchangeDerivedMap_eq]
  simp only [Functor.map_comp]
  infer_instance

end Main

end AlgebraicGeometry
