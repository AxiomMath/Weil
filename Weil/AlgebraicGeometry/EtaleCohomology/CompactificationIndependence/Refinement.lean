module

public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import Weil.AlgebraicGeometry.Morphisms.Proper
public import Weil.Attr

/-!
# Existence, uniqueness and naturality of the exchange morphism `j_! f_* ⟶ f'_* i_!`

Consider a commutative square of schemes
```
  X --i--> X'
  |        |
  f        f'
  v        v
  Y --j--> Y'
```
with `i` and `j` open immersions, `f` proper and `f'` separated. For a sheaf `G` of `Λ`-modules
on the small étale site of `X` there is exactly one exchange morphism
`α_G : j_! f_* G ⟶ f'_* i_! G` (in the sense of `AlgebraicGeometry.IsOpenProperExchangeMorphism`),
and `α_G` is natural in `G`.

For `V` étale over `Y'` with a factorisation `φ : V ⟶ Y` through `j`, the morphism
`i_V : X_V ⟶ X'_V` induced by the square is an open immersion with closed image, so `X'_V` is the
disjoint union of the image of `i_V` and of its open and closed complement `R_V`. Hence a section
of a sheaf over `X'_V` is the same as a pair of sections over `X_V` and over `R_V`; in particular
for every `s ∈ G(X_V)` there is a unique section `t(s)` of `i_! G` over `X'_V` restricting to
`ι(s)` on `X_V` and to `0` on `R_V`. The assignment `[φ, s] ↦ t(s)` is a morphism of presheaves
`β : P_j (f_* G) ⟶ f'_* i_! G`, and `α_G` is the morphism it induces on the sheafification
`j_! f_* G` of `P_j (f_* G)`. An exchange morphism `α` is determined by the sections
`α(c [φ, s])`, which are forced to be `t(s)`; this gives uniqueness, and naturality follows in the
same way.

## Main definitions

* `AlgebraicGeometry.openProperExchangeMap`: the exchange morphism `α_G : j_! f_* G ⟶ f'_* i_! G`.
* `AlgebraicGeometry.openProperExchangeNatTrans`: the exchange morphisms as a natural
  transformation `j_! ∘ f_* ⟶ f'_* ∘ i_!`.

## Main results

* `AlgebraicGeometry.existsUnique_isOpenProperExchangeMorphism`: there is exactly one exchange
  morphism `j_! f_* G ⟶ f'_* i_! G`.
* `AlgebraicGeometry.isOpenProperExchangeMorphism_openProperExchangeMap`: `α_G` is one.
* `AlgebraicGeometry.openProperExchangeMap_naturality`: `α_G` is natural in `G`.
* `AlgebraicGeometry.Scheme.Etale.existsUnique_map_eq_of_disjoint`: for monomorphisms `A ⟶ T` and
  `B ⟶ T` of the small étale site with disjoint images covering `T`, the sections of a sheaf over
  `T` are the pairs of sections over `A` and `B`.
* `AlgebraicGeometry.extensionByZero_hom_ext`: a morphism out of `j_! F` is determined by its
  values on the sections `c [φ, s]`.

## Implementation notes

The objects live on Mathlib's small étale site `X.Etale`, where the Stacks Project's extension by
zero and direct image are defined; the source's abelian sheaves are the case `Λ = ℤ`. The source
assumes all schemes separated; only the separatedness of `f'` is used (it makes `i_V` proper, so
that its image is closed).

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.5, pp. 87–88.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale Stacks.EtaleCohomology

universe w r u

namespace AlgebraicGeometry

section Sheaf

variable {X : Scheme.{u}}

/-- A morphism of the small étale site whose underlying morphism of schemes is a monomorphism
is a monomorphism. -/
private lemma Scheme.Etale.mono_of_mono_left {A B : X.Etale} (g : A ⟶ B) [Mono g.left] :
    Mono g := by
  constructor
  intro Z u v huv
  ext : 1
  exact (cancel_mono g.left).1 (congrArg (fun k => k.left) huv)

variable {F : (X.Etale)ᵒᵖ ⥤ Type w} (hF : Presieve.IsSheaf X.smallEtaleTopology F)
include hF

lemma Scheme.Etale.subsingleton_obj_of_isEmpty (U : X.Etale) [IsEmpty U.left] :
    Subsingleton (F.obj (op U)) := by
  have hmem : Sieve.ofArrows (fun i : PEmpty.{1} => U) (fun i => i.elim) ∈
      X.smallEtaleTopology U := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    exact isEmptyElim x
  constructor
  intro a b
  refine (hF _ hmem).isSeparatedFor.ext fun V g hg => ?_
  obtain ⟨_, _, _, ⟨i⟩, _⟩ := hg
  exact i.elim

lemma Scheme.Etale.existsUnique_map_eq_of_disjoint {T A B : X.Etale} (a : A ⟶ T) (b : B ⟶ T)
    [Mono a] [Mono b] (hcov : Set.range a.left ∪ Set.range b.left = Set.univ)
    (hdisj : Disjoint (Set.range a.left) (Set.range b.left)) (x : F.obj (op A))
    (y : F.obj (op B)) : ∃! z : F.obj (op T), F.map a.op z = x ∧ F.map b.op z = y := by
  let Z : Bool → X.Etale := fun i => Bool.rec B A i
  let π : ∀ i, Z i ⟶ T := fun i => Bool.rec (motive := fun i => Z i ⟶ T) b a i
  have hmem : Sieve.ofArrows Z π ∈ X.smallEtaleTopology T := by
    rw [ofArrows_mem_smallEtaleTopology_iff, ← hcov]
    ext t
    simp only [Set.mem_iUnion, Set.mem_union, Bool.exists_bool]
    exact Or.comm
  have hS := (Presieve.isSheafFor_iff_generate _).2 (hF _ hmem)
  rw [Presieve.isSheafFor_arrows_iff] at hS
  let s : ∀ i, F.obj (op (Z i)) := fun i => Bool.rec (motive := fun i => F.obj (op (Z i))) y x i
  have hempty : ∀ (W : X.Etale) (ga : W ⟶ A) (gb : W ⟶ B), ga ≫ a = gb ≫ b →
      IsEmpty W.left := by
    intro W ga gb he
    refine ⟨fun w => Set.disjoint_left.1 hdisj ⟨ga.left w, rfl⟩ ⟨gb.left w, ?_⟩⟩
    have : (ga ≫ a).left = (gb ≫ b).left := congrArg (fun k => k.left) he
    have h2 : ga.left ≫ a.left = gb.left ≫ b.left := this
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h2]
  have hc : Presieve.Arrows.Compatible F π s := by
    intro i k W gi gk he
    cases i <;> cases k
    · have : gi = gk := (cancel_mono b).1 he
      rw [this]
    · have := hempty W gk gi he.symm
      exact (subsingleton_obj_of_isEmpty hF W).elim _ _
    · have := hempty W gi gk he
      exact (subsingleton_obj_of_isEmpty hF W).elim _ _
    · have : gi = gk := (cancel_mono a).1 he
      rw [this]
  obtain ⟨z, hz, hu⟩ := hS s hc
  refine ⟨z, ⟨hz true, hz false⟩, fun z' hz' => hu z' ?_⟩
  intro i
  cases i
  · exact hz'.2
  · exact hz'.1

end Sheaf

section ExtensionByZero


variable (Λ : Type r) [Ring Λ] {Y Y' : Scheme.{u}} (j : Y ⟶ Y') [Etale j]

theorem extensionByZeroPresheafToSheaf_app_mk (F : EtaleModules.{u, r} Λ Y) {V W : Y'.Etale}
    (g : W ⟶ V) (φ : V ⟶ smallEtaleSource j) (s : F.obj.obj (op (sourceDescend j φ))) :
    (((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj.map g.op).hom
      (((extensionByZeroPresheafToSheaf Λ j F).app (op V)).hom
        ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ))) φ).hom
          s)) =
      ((extensionByZeroPresheafToSheaf Λ j F).app (op W)).hom
        ((Sigma.ι (fun ψ : W ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ)))
          (g ≫ φ)).hom ((F.obj.map (sourceDescendMap j g φ).op).hom s)) := by
  have h2 := congrArg (fun k => k.hom s) (ι_comp_etaleExtensionByZeroPresheaf_map j F g φ)
  have h1 := congrArg (fun k => k.hom
    ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ))) φ).hom s))
    ((extensionByZeroPresheafToSheaf Λ j F).naturality g.op)
  exact h1.symm.trans
    (congrArg (fun y => ((extensionByZeroPresheafToSheaf Λ j F).app (op W)).hom y) h2)

theorem extensionByZeroPresheafToSheaf_naturality {F F' : EtaleModules.{u, r} Λ Y}
    (u : F ⟶ F') :
    (extensionByZeroDirectSum j).map u.hom ≫ extensionByZeroPresheafToSheaf Λ j F' =
      extensionByZeroPresheafToSheaf Λ j F ≫
        ((etaleModuleExtensionByZero.{u, r} Λ j).map u).hom := by
  have h := congrArg (fun k => k.hom) (etaleModuleExtensionByZeroObjIso_hom_naturality Λ j u)
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h
  have h' : (etaleModuleExtensionByZeroObjIso Λ j F).inv.hom ≫
      ((etaleModuleExtensionByZero.{u, r} Λ j).map u).hom =
      sheafifyMap Y'.smallEtaleTopology ((extensionByZeroDirectSum j).map u.hom) ≫
        (etaleModuleExtensionByZeroObjIso Λ j F').inv.hom := by
    have e1 : (etaleModuleExtensionByZeroObjIso Λ j F).inv.hom ≫
        (etaleModuleExtensionByZeroObjIso Λ j F).hom.hom = 𝟙 _ := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]; rfl
    have e2 : (etaleModuleExtensionByZeroObjIso Λ j F').hom.hom ≫
        (etaleModuleExtensionByZeroObjIso Λ j F').inv.hom = 𝟙 _ := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id]; rfl
    calc _ = (etaleModuleExtensionByZeroObjIso Λ j F).inv.hom ≫
          (((etaleModuleExtensionByZero.{u, r} Λ j).map u).hom ≫
            (etaleModuleExtensionByZeroObjIso Λ j F').hom.hom) ≫
          (etaleModuleExtensionByZeroObjIso Λ j F').inv.hom := by
            simp only [Category.assoc, e2, Category.comp_id]
      _ = _ := by
            rw [h]
            have e3 := (reassoc_of% e1) (((presheafToSheaf Y'.smallEtaleTopology
              (ModuleCat.{max (u + 1) r} Λ)).map ((extensionByZeroDirectSum j).map u.hom)).hom ≫
                (etaleModuleExtensionByZeroObjIso Λ j F').inv.hom)
            exact (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans e3
  unfold extensionByZeroPresheafToSheaf
  rw [Category.assoc, h']
  have e := toSheafify_naturality Y'.smallEtaleTopology ((extensionByZeroDirectSum j).map u.hom)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (etaleModuleExtensionByZeroObjIso Λ j F').inv.hom) e).trans
      (Category.assoc _ _ _))

/-- The map `c : P_k F ⟶ k_! F` is natural in `F`, on the section `[φ, s]`. -/
theorem extensionByZeroPresheafToSheaf_naturality_apply {F F' : EtaleModules.{u, r} Λ Y}
    (v : F ⟶ F') {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) (s : F.obj.obj (op (sourceDescend j φ))) :
    (((etaleModuleExtensionByZero.{u, r} Λ j).map v).hom.app (op V)).hom
        (((extensionByZeroPresheafToSheaf Λ j F).app (op V)).hom
          ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ)))
            φ).hom s)) =
      ((extensionByZeroPresheafToSheaf Λ j F').app (op V)).hom
        ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F'.obj.obj (op (sourceDescend j ψ)))
          φ).hom ((v.hom.app (op (sourceDescend j φ))).hom s)) := by
  have h := congrArg (fun m => (m.app (op V)).hom
    ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ))) φ).hom s))
    (extensionByZeroPresheafToSheaf_naturality Λ j v)
  have h2 := congrArg (fun m => m.hom s) (ι_comp_extensionByZeroDirectSum_map_app j v.hom φ)
  exact h.symm.trans (congrArg (fun y => ((extensionByZeroPresheafToSheaf Λ j F').app
    (op V)).hom y) h2)

theorem extensionByZero_hom_ext {F : EtaleModules.{u, r} Λ Y} {S : EtaleModules.{u, r} Λ Y'}
    {γ γ' : (etaleModuleExtensionByZero.{u, r} Λ j).obj F ⟶ S}
    (H : ∀ (V : Y'.Etale) (φ : V ⟶ smallEtaleSource j) (s : F.obj.obj (op (sourceDescend j φ))),
      (γ.hom.app (op V)).hom (((extensionByZeroPresheafToSheaf Λ j F).app (op V)).hom
        ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ))) φ).hom
          s)) =
      (γ'.hom.app (op V)).hom (((extensionByZeroPresheafToSheaf Λ j F).app (op V)).hom
        ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ))) φ).hom
          s))) : γ = γ' := by
  have h1 : extensionByZeroPresheafToSheaf Λ j F ≫ γ.hom =
      extensionByZeroPresheafToSheaf Λ j F ≫ γ'.hom := by
    refine NatTrans.ext (funext fun V => ?_)
    obtain ⟨V⟩ := V
    exact Sigma.hom_ext _ _ fun φ => ModuleCat.hom_ext (LinearMap.ext fun s => H V φ s)
  have h2 : (etaleModuleExtensionByZeroObjIso Λ j F).inv ≫ γ =
      (etaleModuleExtensionByZeroObjIso Λ j F).inv ≫ γ' := by
    ext1
    apply sheafify_hom_ext _ _ _ S.property
    simpa [extensionByZeroPresheafToSheaf] using h1
  simpa using congrArg (fun k => (etaleModuleExtensionByZeroObjIso Λ j F).hom ≫ k) h2


theorem sigma_ι_hom_eq_of_eq_sourceDescend (F : EtaleModules.{u, r} Λ Y) {V : Y'.Etale}
    {ψ₁ ψ₂ : V ⟶ smallEtaleSource j} (e : ψ₁ = ψ₂) (x : F.obj.obj (op (sourceDescend j ψ₁))) :
    (Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ))) ψ₁).hom x =
      (Sigma.ι (fun ψ : V ⟶ smallEtaleSource j => F.obj.obj (op (sourceDescend j ψ))) ψ₂).hom
        ((F.obj.map (eqToHom (congrArg (sourceDescend j) e.symm)).op).hom x) := by
  subst e
  simp

variable {X X' : Scheme.{u}} (i : X ⟶ X') [Etale i]

theorem extensionByZeroSection_map (G : EtaleModules.{u, r} Λ X) {U U' : X.Etale} (a : U' ⟶ U)
    (s : G.obj.obj (op U)) :
    (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map
        ((smallEtaleCompose i).map a).op).hom (extensionByZeroSection Λ i G U s) =
      extensionByZeroSection Λ i G U' ((G.obj.map a.op).hom s) := by
  have e : (smallEtaleCompose i).map a ≫ structureHomToSource i U = structureHomToSource i U' := by
    ext : 1
    exact MorphismProperty.Over.w a
  refine (extensionByZeroPresheafToSheaf_app_mk Λ i G _ (structureHomToSource i U) s).trans ?_
  refine congrArg (fun y => ((extensionByZeroPresheafToSheaf Λ i G).app
    (op ((smallEtaleCompose i).obj U'))).hom y) ?_
  refine (sigma_ι_hom_eq_of_eq_sourceDescend Λ i G e _).trans ?_
  refine congrArg (fun y => (Sigma.ι (fun ψ : (smallEtaleCompose i).obj U' ⟶ smallEtaleSource i =>
    G.obj.obj (op (sourceDescend i ψ))) (structureHomToSource i U')).hom y) ?_
  have hk : eqToHom (congrArg (sourceDescend i) e.symm) ≫
      sourceDescendMap i ((smallEtaleCompose i).map a) (structureHomToSource i U) =
      (a : sourceDescend i (structureHomToSource i U') ⟶
        sourceDescend i (structureHomToSource i U)) := by
    ext : 1
    exact (congrArg (· ≫ a.left) (sourceDescend_eqToHom_left i e.symm)).trans
      (Category.id_comp _)
  have h3 := congrArg (fun k => (G.obj.map k.op).hom s) hk
  have h4 : G.obj.map (eqToHom (congrArg (sourceDescend i) e.symm) ≫
      sourceDescendMap i ((smallEtaleCompose i).map a) (structureHomToSource i U)).op =
      G.obj.map (sourceDescendMap i ((smallEtaleCompose i).map a) (structureHomToSource i U)).op ≫
        G.obj.map (eqToHom (congrArg (sourceDescend i) e.symm)).op := by
    rw [op_comp, Functor.map_comp]
  exact (congrArg (fun k => k.hom s) h4).symm.trans h3

theorem extensionByZeroSection_naturality {G G' : EtaleModules.{u, r} Λ X} (v : G ⟶ G')
    (U : X.Etale) (s : G.obj.obj (op U)) :
    (((etaleModuleExtensionByZero.{u, r} Λ i).map v).hom.app
        (op ((smallEtaleCompose i).obj U))).hom (extensionByZeroSection Λ i G U s) =
      extensionByZeroSection Λ i G' U ((v.hom.app (op U)).hom s) := by
  have h := congrArg (fun k => (k.app (op ((smallEtaleCompose i).obj U))).hom
    ((Sigma.ι (fun ψ : (smallEtaleCompose i).obj U ⟶ smallEtaleSource i =>
      G.obj.obj (op (sourceDescend i ψ))) (structureHomToSource i U)).hom s))
    (extensionByZeroPresheafToSheaf_naturality Λ i v)
  have h2 := congrArg (fun k => k.hom s)
    (ι_comp_extensionByZeroDirectSum_map_app i v.hom (structureHomToSource i U))
  exact h.symm.trans (congrArg (fun y =>
    ((extensionByZeroPresheafToSheaf Λ i G').app (op ((smallEtaleCompose i).obj U))).hom y) h2)

end ExtensionByZero




namespace ExchangeSquare

section Generic

/-- Restriction along a composite, applied to a section. -/
theorem map_comp_op_apply {C : Type*} [Category C] {Λ : Type r} [Ring Λ]
    (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ)
    {A B D : C} (a : A ⟶ B) (b : B ⟶ D) (z : P.obj (op D)) :
    (P.map (a ≫ b).op).hom z = (P.map a.op).hom ((P.map b.op).hom z) := by
  rw [op_comp, P.map_comp]
  rfl


variable {X X' Y Y' : Scheme.{u}} {A B S T : Scheme.{u}}

theorem isPullback_lift_fst (q : T ⟶ S) {a : A ⟶ S} {b : B ⟶ S} (k : A ⟶ B)
    (hk : k ≫ b = a) :
    IsPullback (pullback.lift (pullback.fst a q ≫ k) (pullback.snd a q)
        (by rw [Category.assoc, hk, pullback.condition]))
      (pullback.fst a q) (pullback.fst b q) k := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback b q).flip
  rw [pullback.lift_snd, hk]
  exact (IsPullback.of_hasPullback a q).flip

variable (i : X ⟶ X') (j : Y ⟶ Y') {f : X ⟶ Y} {f' : X' ⟶ Y'} (h : i ≫ f' = f ≫ j)
  {a : A ⟶ Y'} {b : B ⟶ Y'} (k : A ⟶ B) (hk : k ≫ b = a) (φ : B ⟶ Y) (hφ : φ ≫ j = b)

/-- The generic form of `i_V`. -/
abbrev liftInclusion {B : Scheme.{u}} {b : B ⟶ Y'} (φ : B ⟶ Y) (hφ : φ ≫ j = b) :
    pullback φ f ⟶ pullback b f' :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i) (by
    rw [Category.assoc, h, ← hφ]
    exact pullback.condition_assoc j)

theorem lift_comp_lift_eq (hφ' : (k ≫ φ) ≫ j = a) :
    liftInclusion i j h (k ≫ φ) hφ' ≫
        pullback.lift (pullback.fst a f' ≫ k) (pullback.snd a f')
          (by rw [Category.assoc, hk, pullback.condition]) =
      pullback.lift (pullback.fst (k ≫ φ) f ≫ k) (pullback.snd (k ≫ φ) f)
          (by rw [Category.assoc, pullback.condition]) ≫ liftInclusion i j h φ hφ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
    erw [pullback.lift_snd, pullback.lift_snd_assoc]

theorem isPullback_lift_lift (hφ' : (k ≫ φ) ≫ j = a) :
    IsPullback (pullback.lift (pullback.fst (k ≫ φ) f ≫ k) (pullback.snd (k ≫ φ) f)
          (by rw [Category.assoc, pullback.condition]))
      (liftInclusion i j h (k ≫ φ) hφ') (liftInclusion i j h φ hφ)
      (pullback.lift (pullback.fst a f' ≫ k) (pullback.snd a f')
          (by rw [Category.assoc, hk, pullback.condition])) := by
  refine IsPullback.of_bot ?_ (lift_comp_lift_eq i j h k hk φ hφ hφ').symm
    (isPullback_lift_fst f' k hk)
  rw [pullback.lift_fst, pullback.lift_fst]
  exact isPullback_lift_fst f k rfl

end Generic

variable {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') [Etale j]
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (h : i ≫ f' = f ≫ j)

instance mono_inclusionLeft [Mono i] {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    Mono (inclusionLeft i j h φ) := by
  constructor
  intro Z a b hab
  apply pullback.hom_ext
  · have := congrArg (· ≫ pullback.fst _ _) hab
    simpa only [Category.assoc, inclusionLeft_fst] using this
  · apply (cancel_mono i).1
    have := congrArg (· ≫ pullback.snd _ _) hab
    simpa only [Category.assoc, inclusionLeft_snd] using this

instance isProper_inclusionLeft [IsProper f] [IsSeparated f'] {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) : IsProper (inclusionLeft i j h φ) := by
  have : IsProper (inclusionLeft i j h φ ≫ pullback.fst V.hom f') := by
    have key : ∀ {T : Scheme.{u}} (ψ : T ⟶ Y), IsProper (pullback.fst ψ f) :=
      fun _ => inferInstance
    rw [inclusionLeft_fst]
    exact key φ.left
  have : IsSeparated (pullback.fst (V.hom : V.left ⟶ Y') f') := inferInstance
  exact IsProper.of_comp _ (pullback.fst V.hom f')

theorem isClosed_range_inclusionLeft [IsProper f] [IsSeparated f'] {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) : IsClosed (Set.range (inclusionLeft i j h φ).base) :=
  (inclusionLeft i j h φ).isClosedMap.isClosed_range

variable [IsProper f] [IsSeparated f']

/-- The open complement `R_V` of the image of `i_V : X_V ⟶ X'_V`. -/
def complementOpens {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) : (pullback V.hom f').Opens :=
  ⟨(Set.range (inclusionLeft i j h φ).base)ᶜ, (isClosed_range_inclusionLeft i j h φ).isOpen_compl⟩

/-- The open complement `R_V` of the image of `i_V`, as an object of the small étale site of
`X'`. -/
def complementObj {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) : X'.Etale :=
  MorphismProperty.Over.mk ⊤
    ((complementOpens i j h φ).ι ≫ (pullback.snd V.hom f' : pullback V.hom f' ⟶ X')) (by
      have : Etale V.hom := V.prop
      infer_instance)

/-- The inclusion `R_V ⟶ X'_V` in the small étale site of `X'`. -/
def complementInclusion {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    complementObj i j h φ ⟶ targetObj f' V :=
  MorphismProperty.Over.homMk (complementOpens i j h φ).ι rfl trivial

theorem range_complementInclusion_left {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    Set.range (complementInclusion i j h φ).left.base =
      (Set.range (inclusionLeft i j h φ).base)ᶜ :=
  Scheme.Opens.range_ι _

instance mono_complementInclusion {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    Mono (complementInclusion i j h φ) := by
  have : Mono (complementInclusion i j h φ).left := by
    change Mono (complementOpens i j h φ).ι
    infer_instance
  exact Scheme.Etale.mono_of_mono_left _

theorem exists_eq_comp_complementInclusion {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    {W : X'.Etale} (w : W ⟶ targetObj f' V)
    (hw : Disjoint (Set.range w.left.base) (Set.range (inclusionLeft i j h φ).base)) :
    ∃ w' : W ⟶ complementObj i j h φ, w' ≫ complementInclusion i j h φ = w := by
  have hsub : Set.range w.left.base ⊆ Set.range (complementOpens i j h φ).ι.base := by
    intro x hx
    exact (Scheme.Opens.range_ι (complementOpens i j h φ)).ge (hw.subset_compl_right hx)
  let l := IsOpenImmersion.lift (complementOpens i j h φ).ι w.left hsub
  have hl : l ≫ (complementOpens i j h φ).ι = w.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨MorphismProperty.Over.homMk l ?_ trivial, ?_⟩
  · change l ≫ (complementOpens i j h φ).ι ≫ pullback.snd V.hom f' = W.hom
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.snd V.hom f') hl)).trans
      (MorphismProperty.Over.w w)
  · ext : 1
    exact hl


section Functoriality

omit [IsProper f] [IsSeparated f'] in
theorem left_comp_eq_hom {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) : φ.left ≫ j = V.hom := by
  simpa using MorphismProperty.Over.w φ

variable {V V' : Y'.Etale} (g : V' ⟶ V) (φ : V ⟶ smallEtaleSource j)

omit [IsProper f] [IsSeparated f'] in
theorem smallEtaleBaseChange_map_left {T S : Scheme.{u}} (q : T ⟶ S) {A B : S.Etale}
    (k : A ⟶ B) :
    ((smallEtaleBaseChange q).map k).left =
      pullback.lift (pullback.fst A.hom q ≫ k.left) (pullback.snd A.hom q)
        (by rw [Category.assoc, MorphismProperty.Over.w k, pullback.condition]) :=
  rfl

variable (f) in
/-- The morphism `X_{V'} ⟶ X_V` of the small étale site of `X` induced by `g : V' ⟶ V`. -/
abbrev sourceMap : sourceObj j f (g ≫ φ) ⟶ sourceObj j f φ :=
  (smallEtaleBaseChange f).map (sourceDescendMap j g φ)

variable (f') in
/-- The morphism `X'_{V'} ⟶ X'_V` of the small étale site of `X'` induced by `g : V' ⟶ V`. -/
abbrev targetMap : targetObj f' V' ⟶ targetObj f' V :=
  (smallEtaleBaseChange f').map g

omit [IsProper f] [IsSeparated f'] in
theorem inclusionLeft_comp_targetMap_left :
    inclusionLeft i j h (g ≫ φ) ≫ (targetMap f' g).left =
      (sourceMap j f g φ).left ≫ inclusionLeft i j h φ :=
  lift_comp_lift_eq i j h g.left (MorphismProperty.Over.w g) φ.left
    (left_comp_eq_hom j φ) ((Category.assoc _ _ _).trans
      ((congrArg (g.left ≫ ·) (left_comp_eq_hom j φ)).trans (MorphismProperty.Over.w g)))

omit [IsProper f] [IsSeparated f'] in
theorem isPullback_targetMap_left :
    IsPullback (targetMap f' g).left (pullback.fst V'.hom f') (pullback.fst V.hom f') g.left :=
  isPullback_lift_fst f' g.left (MorphismProperty.Over.w g)

omit [IsProper f] [IsSeparated f'] in
theorem isPullback_inclusionLeft :
    IsPullback (sourceMap j f g φ).left (inclusionLeft i j h (g ≫ φ)) (inclusionLeft i j h φ)
      (targetMap f' g).left :=
  isPullback_lift_lift i j h g.left (MorphismProperty.Over.w g) φ.left
    (left_comp_eq_hom j φ) ((Category.assoc _ _ _).trans
      ((congrArg (g.left ≫ ·) (left_comp_eq_hom j φ)).trans (MorphismProperty.Over.w g)))

omit [IsProper f] [IsSeparated f'] in
theorem mem_range_inclusionLeft_of_targetMap {x : (targetObj f' V').left}
    (hx : (targetMap f' g).left x ∈ Set.range (inclusionLeft i j h φ)) :
    x ∈ Set.range (inclusionLeft i j h (g ≫ φ)) := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
  have e := (isPullback_inclusionLeft i j h g φ).isoPullback_inv_snd
  refine ⟨(isPullback_inclusionLeft i j h g φ).isoPullback.inv z,
    (Scheme.Hom.comp_apply _ _ _).symm.trans ?_⟩
  exact (congrArg (fun m => m z) e).trans hz

theorem disjoint_range_complementInclusion_comp_targetMap :
    Disjoint (Set.range (complementInclusion i j h (g ≫ φ) ≫ targetMap f' g).left)
      (Set.range (inclusionLeft i j h φ)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ hx
  have hx' : (complementInclusion i j h (g ≫ φ)).left x ∈
      (Set.range (inclusionLeft i j h (g ≫ φ)).base)ᶜ := by
    rw [← range_complementInclusion_left]
    exact ⟨x, rfl⟩
  exact hx' (mem_range_inclusionLeft_of_targetMap i j h g φ hx)

end Functoriality

end ExchangeSquare


section Exchange

open ExchangeSquare

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') [IsOpenImmersion i]
  (j : Y ⟶ Y') [IsOpenImmersion j] {f : X ⟶ Y} {f' : X' ⟶ Y'} [IsProper f] [IsSeparated f']
  (h : i ≫ f' = f ≫ j)

/-- A section of a sheaf over `X'_V` is determined by its restrictions to `X_V` and to the
complement `R_V`, and any pair of sections over these glues. -/
theorem existsUnique_map_inclusion_and_map_complementInclusion (S : EtaleModules.{u, r} Λ X')
    {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (x : S.obj.obj (op ((smallEtaleCompose i).obj (sourceObj j f φ))))
    (y : S.obj.obj (op (complementObj i j h φ))) :
    ∃! z : S.obj.obj (op (targetObj f' V)),
      (S.obj.map (inclusion i j h φ).op).hom z = x ∧
        (S.obj.map (complementInclusion i j h φ).op).hom z = y := by
  have hS : Presieve.IsSheaf X'.smallEtaleTopology (S.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose X'.smallEtaleTopology (forget (ModuleCat.{max (u + 1) r} Λ))).obj S).property
  have : Mono (inclusion i j h φ).left := mono_inclusionLeft i j h φ
  have : Mono (inclusion i j h φ) := Scheme.Etale.mono_of_mono_left _
  have hcov : Set.range (inclusion i j h φ).left ∪ Set.range (complementInclusion i j h φ).left =
      Set.univ := by
    rw [range_complementInclusion_left]
    exact Set.union_compl_self _
  have hdisj : Disjoint (Set.range (inclusion i j h φ).left)
      (Set.range (complementInclusion i j h φ).left) := by
    rw [range_complementInclusion_left]
    exact disjoint_compl_right
  exact Scheme.Etale.existsUnique_map_eq_of_disjoint hS _ _ hcov hdisj x y

/-- The restriction maps to `X_V` and `R_V` identify the sections of a sheaf over `X'_V` with
pairs of sections over `X_V` and `R_V`. -/
def restrictionLinearEquiv (S : EtaleModules.{u, r} Λ X') {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) :
    S.obj.obj (op (targetObj f' V)) ≃ₗ[Λ]
      S.obj.obj (op ((smallEtaleCompose i).obj (sourceObj j f φ))) ×
        S.obj.obj (op (complementObj i j h φ)) :=
  LinearEquiv.ofBijective
    (LinearMap.prod (S.obj.map (inclusion i j h φ).op).hom
      (S.obj.map (complementInclusion i j h φ).op).hom)
    ⟨fun z z' hz => (existsUnique_map_inclusion_and_map_complementInclusion Λ i j h S φ
        ((S.obj.map (inclusion i j h φ).op).hom z')
        ((S.obj.map (complementInclusion i j h φ).op).hom z')).unique
        ⟨(Prod.ext_iff.1 hz).1, (Prod.ext_iff.1 hz).2⟩ ⟨rfl, rfl⟩,
      fun p => by
        obtain ⟨z, hz, -⟩ :=
          existsUnique_map_inclusion_and_map_complementInclusion Λ i j h S φ p.1 p.2
        exact ⟨z, Prod.ext hz.1 hz.2⟩⟩

omit [IsProper f] [IsSeparated f'] in
/-- The section `ι(s)` of `i_! G` as a linear function of `s`. -/
def extensionByZeroSectionLinearMap (G : EtaleModules.{u, r} Λ X) (U : X.Etale) :
    G.obj.obj (op U) →ₗ[Λ]
      ((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.obj (op ((smallEtaleCompose i).obj U)) :=
  ((extensionByZeroPresheafToSheaf Λ i G).app (op ((smallEtaleCompose i).obj U))).hom ∘ₗ
    (Sigma.ι (fun ψ : (smallEtaleCompose i).obj U ⟶ smallEtaleSource i =>
      G.obj.obj (op (sourceDescend i ψ))) (structureHomToSource i U)).hom

omit [IsProper f] [IsSeparated f'] in
@[simp]
theorem extensionByZeroSectionLinearMap_apply (G : EtaleModules.{u, r} Λ X) (U : X.Etale)
    (s : G.obj.obj (op U)) :
    extensionByZeroSectionLinearMap Λ i G U s = extensionByZeroSection Λ i G U s :=
  rfl

variable (G : EtaleModules.{u, r} Λ X)

/-- The section `t(s)` of `i_! G` over `X'_V` which is `ι(s)` on `X_V` and `0` on the open and
closed complement `R_V`. -/
def exchangeGlue {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    G.obj.obj (op (sourceObj j f φ)) →ₗ[Λ]
      ((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.obj (op (targetObj f' V)) :=
  (restrictionLinearEquiv Λ i j h ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)
      φ).symm.toLinearMap
    ∘ₗ LinearMap.prod (extensionByZeroSectionLinearMap Λ i G _) 0

theorem exchangeGlue_spec {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (sourceObj j f φ))) :
    (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map (inclusion i j h φ).op).hom
        (exchangeGlue Λ i j h G φ s) = extensionByZeroSection Λ i G _ s ∧
      (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map
        (complementInclusion i j h φ).op).hom (exchangeGlue Λ i j h G φ s) = 0 := by
  have := (restrictionLinearEquiv Λ i j h ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)
    φ).apply_symm_apply (extensionByZeroSection Λ i G _ s, 0)
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem eq_exchangeGlue {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (sourceObj j f φ)))
    {z : ((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.obj (op (targetObj f' V))}
    (h₁ : (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map (inclusion i j h φ).op).hom z =
      extensionByZeroSection Λ i G _ s)
    (h₂ : (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map
      (complementInclusion i j h φ).op).hom z = 0) :
    z = exchangeGlue Λ i j h G φ s :=
  (existsUnique_map_inclusion_and_map_complementInclusion Λ i j h _ φ _ _).unique ⟨h₁, h₂⟩
    (exchangeGlue_spec Λ i j h G φ s)

omit [IsOpenImmersion i] in
theorem map_eq_zero_of_disjoint_of_map_complementInclusion {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) (S : EtaleModules.{u, r} Λ X')
    {z : S.obj.obj (op (targetObj f' V))}
    (hz : (S.obj.map (complementInclusion i j h φ).op).hom z = 0)
    {W : X'.Etale} (w : W ⟶ targetObj f' V)
    (hw : Disjoint (Set.range w.left.base) (Set.range (inclusionLeft i j h φ).base)) :
    (S.obj.map w.op).hom z = 0 := by
  obtain ⟨w', rfl⟩ := exists_eq_comp_complementInclusion i j h φ w hw
  rw [ExchangeSquare.map_comp_op_apply, hz, map_zero]

theorem exchangeGlue_naturality {V V' : Y'.Etale} (g : V' ⟶ V) (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (sourceObj j f φ))) :
    exchangeGlue Λ i j h G (g ≫ φ) ((G.obj.map (sourceMap j f g φ).op).hom s) =
      (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map (targetMap f' g).op).hom
        (exchangeGlue Λ i j h G φ s) := by
  set Gi := (etaleModuleExtensionByZero.{u, r} Λ i).obj G
  obtain ⟨hs₁, hs₂⟩ := exchangeGlue_spec Λ i j h G φ s
  symm
  apply eq_exchangeGlue
  · have e : inclusion i j h (g ≫ φ) ≫ targetMap f' g =
        (smallEtaleCompose i).map (sourceMap j f g φ) ≫ inclusion i j h φ := by
      ext : 1
      exact inclusionLeft_comp_targetMap_left i j h g φ
    refine (ExchangeSquare.map_comp_op_apply Gi.obj _ _ _).symm.trans ?_
    rw [e, ExchangeSquare.map_comp_op_apply, hs₁]
    exact extensionByZeroSection_map Λ i G _ s
  · refine (ExchangeSquare.map_comp_op_apply Gi.obj _ _ _).symm.trans ?_
    exact map_eq_zero_of_disjoint_of_map_complementInclusion Λ i j h φ Gi hs₂ _
      (disjoint_range_complementInclusion_comp_targetMap i j h g φ)

/-- The morphism of presheaves `β : P_j (f_* G) ⟶ f'_* i_! G` sending `[φ, s]` to `t(s)`. -/
def exchangePresheafHom :
    etaleExtensionByZeroPresheaf j ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
      ((etaleModuleDirectImage.{u, r} Λ f').obj
        ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)).obj where
  app V := Sigma.desc fun φ => ModuleCat.ofHom (exchangeGlue Λ i j h G φ)
  naturality V V' g := by
    refine Sigma.hom_ext _ _ fun φ => ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    have h1 := congrArg (fun k => k.hom s) (ι_comp_etaleExtensionByZeroPresheaf_map j
      ((etaleModuleDirectImage.{u, r} Λ f).obj G) g.unop φ)
    have h2 := congrArg (fun k => k.hom ((G.obj.map (sourceMap j f g.unop φ).op).hom s))
      (Sigma.ι_desc (fun ψ : V'.unop ⟶ smallEtaleSource j =>
        ModuleCat.ofHom (exchangeGlue Λ i j h G ψ)) (g.unop ≫ φ))
    have h3 := congrArg (fun k => k.hom s)
      (Sigma.ι_desc (fun ψ : V.unop ⟶ smallEtaleSource j =>
        ModuleCat.ofHom (exchangeGlue Λ i j h G ψ)) φ)
    refine (congrArg (fun y => (Sigma.desc fun ψ : V'.unop ⟶ smallEtaleSource j =>
      ModuleCat.ofHom (exchangeGlue Λ i j h G ψ)).hom y) h1).trans (h2.trans ?_)
    refine (exchangeGlue_naturality Λ i j h G g.unop φ s).trans ?_
    exact (congrArg (fun y => (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map
      (targetMap f' g.unop).op).hom y) h3).symm

theorem exchangePresheafHom_app_ι {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (sourceObj j f φ))) :
    ((exchangePresheafHom Λ i j h G).app (op V)).hom
      ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j =>
        ((etaleModuleDirectImage.{u, r} Λ f).obj G).obj.obj (op (sourceDescend j ψ))) φ).hom s) =
      exchangeGlue Λ i j h G φ s :=
  congrArg (fun k => k.hom s) (Sigma.ι_desc (fun ψ : V ⟶ smallEtaleSource j =>
    ModuleCat.ofHom (exchangeGlue Λ i j h G ψ)) φ)

/-- **The exchange morphism** `α_G : j_! f_* G ⟶ f'_* i_! G` of the square `i ≫ f' = f ≫ j`
(`i`, `j` open immersions, `f` proper, `f'` separated): the morphism induced by `β` on the
sheafification `j_! f_* G` of `P_j (f_* G)`. -/
def openProperExchangeMap :
    (etaleModuleExtensionByZero.{u, r} Λ j).obj ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
      (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj G) :=
  (etaleModuleExtensionByZeroObjIso Λ j ((etaleModuleDirectImage.{u, r} Λ f).obj G)).hom ≫
    Sheaf.homEquiv.symm (sheafifyLift Y'.smallEtaleTopology (exchangePresheafHom Λ i j h G)
      ((etaleModuleDirectImage.{u, r} Λ f').obj
        ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)).property)

theorem extensionByZeroPresheafToSheaf_comp_openProperExchangeMap_hom :
    extensionByZeroPresheafToSheaf Λ j ((etaleModuleDirectImage.{u, r} Λ f).obj G) ≫
        (openProperExchangeMap Λ i j h G).hom = exchangePresheafHom Λ i j h G := by
  have e : (etaleModuleExtensionByZeroObjIso Λ j
      ((etaleModuleDirectImage.{u, r} Λ f).obj G)).inv.hom ≫
      (etaleModuleExtensionByZeroObjIso Λ j ((etaleModuleDirectImage.{u, r} Λ f).obj G)).hom.hom =
      𝟙 _ := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id]
    rfl
  unfold extensionByZeroPresheafToSheaf openProperExchangeMap
  rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, reassoc_of% e]
  exact toSheafify_sheafifyLift _ _ _

theorem exchangeSection_openProperExchangeMap {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (sourceObj j f φ))) :
    exchangeSection Λ i j G (openProperExchangeMap Λ i j h G) φ s =
      exchangeGlue Λ i j h G φ s :=
  (congrArg (fun k => (k.app (op V)).hom
      ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j =>
        ((etaleModuleDirectImage.{u, r} Λ f).obj G).obj.obj (op (sourceDescend j ψ))) φ).hom s))
    (extensionByZeroPresheafToSheaf_comp_openProperExchangeMap_hom Λ i j h G)).trans
    (exchangePresheafHom_app_ι Λ i j h G φ s)

/-- The morphism `α_G` is an exchange morphism. -/
@[weil "lem_fk108_open_proper_exchange_map_exists_unique"]
theorem isOpenProperExchangeMorphism_openProperExchangeMap :
    IsOpenProperExchangeMorphism Λ i j h G (openProperExchangeMap Λ i j h G) := by
  intro V φ s
  rw [exchangeSection_openProperExchangeMap]
  obtain ⟨h₁, h₂⟩ := exchangeGlue_spec Λ i j h G φ s
  exact ⟨h₁, fun W w hw => map_eq_zero_of_disjoint_of_map_complementInclusion Λ i j h φ _ h₂ w hw⟩

theorem exchangeSection_eq_exchangeGlue_of_isOpenProperExchangeMorphism
    {α : (etaleModuleExtensionByZero.{u, r} Λ j).obj ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
      (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)}
    (hα : IsOpenProperExchangeMorphism Λ i j h G α) {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) (s : G.obj.obj (op (sourceObj j f φ))) :
    exchangeSection Λ i j G α φ s = exchangeGlue Λ i j h G φ s :=
  eq_exchangeGlue Λ i j h G φ s (hα.map_inclusion φ s)
    (hα.map_eq_zero_of_disjoint φ s _
      (by rw [range_complementInclusion_left]; exact disjoint_compl_left))

theorem eq_openProperExchangeMap_of_isOpenProperExchangeMorphism
    {α : (etaleModuleExtensionByZero.{u, r} Λ j).obj ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
      (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)}
    (hα : IsOpenProperExchangeMorphism Λ i j h G α) : α = openProperExchangeMap Λ i j h G :=
  extensionByZero_hom_ext Λ j fun _ φ s =>
    (exchangeSection_eq_exchangeGlue_of_isOpenProperExchangeMorphism Λ i j h G hα φ s).trans
      (exchangeSection_openProperExchangeMap Λ i j h G φ s).symm

/-- **[FK, I.8.5]** In a commutative square `i ≫ f' = f ≫ j` of schemes with `i`, `j` open
immersions, `f` proper and `f'` separated, for every sheaf `G` of `Λ`-modules on the small étale
site of `X` there is exactly one exchange morphism `α_G : j_! f_* G ⟶ f'_* i_! G`. -/
@[weil "lem_fk108_open_proper_exchange_map_exists_unique"]
theorem existsUnique_isOpenProperExchangeMorphism :
    ∃! α : (etaleModuleExtensionByZero.{u, r} Λ j).obj
        ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
      (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj G),
      IsOpenProperExchangeMorphism Λ i j h G α :=
  ⟨openProperExchangeMap Λ i j h G, isOpenProperExchangeMorphism_openProperExchangeMap Λ i j h G,
    fun _ hα => eq_openProperExchangeMap_of_isOpenProperExchangeMorphism Λ i j h G hα⟩

/-- **[FK, I.8.5]** The exchange morphisms `α_G : j_! f_* G ⟶ f'_* i_! G` are natural in `G`. -/
@[weil "lem_fk108_open_proper_exchange_map_exists_unique"]
theorem openProperExchangeMap_naturality {G G' : EtaleModules.{u, r} Λ X} (v : G ⟶ G') :
    (etaleModuleExtensionByZero.{u, r} Λ j).map ((etaleModuleDirectImage.{u, r} Λ f).map v) ≫
        openProperExchangeMap Λ i j h G' =
      openProperExchangeMap Λ i j h G ≫
        (etaleModuleDirectImage.{u, r} Λ f').map
          ((etaleModuleExtensionByZero.{u, r} Λ i).map v) := by
  refine extensionByZero_hom_ext Λ j fun V φ s => ?_
  have hL := extensionByZeroPresheafToSheaf_naturality_apply Λ j
    ((etaleModuleDirectImage.{u, r} Λ f).map v) φ s
  refine (congrArg (fun y => ((openProperExchangeMap Λ i j h G').hom.app (op V)).hom y) hL).trans ?_
  refine (exchangeSection_openProperExchangeMap Λ i j h G' φ _).trans ?_
  change _ = (((etaleModuleExtensionByZero.{u, r} Λ i).map v).hom.app
    (op (targetObj f' V))).hom (exchangeSection Λ i j G (openProperExchangeMap Λ i j h G) φ s)
  refine Eq.trans ?_ (congrArg (fun y => (((etaleModuleExtensionByZero.{u, r} Λ i).map v).hom.app
    (op (targetObj f' V))).hom y) (exchangeSection_openProperExchangeMap Λ i j h G φ s)).symm
  obtain ⟨h₁, h₂⟩ := exchangeGlue_spec Λ i j h G φ s
  symm
  apply eq_exchangeGlue
  · have n := congrArg (fun m => m.hom (exchangeGlue Λ i j h G φ s))
      (((etaleModuleExtensionByZero.{u, r} Λ i).map v).hom.naturality (inclusion i j h φ).op)
    refine n.symm.trans ?_
    refine (congrArg (fun y => (((etaleModuleExtensionByZero.{u, r} Λ i).map v).hom.app
      (op ((smallEtaleCompose i).obj (sourceObj j f φ)))).hom y) h₁).trans ?_
    exact extensionByZeroSection_naturality Λ i v _ s
  · have n := congrArg (fun m => m.hom (exchangeGlue Λ i j h G φ s))
      (((etaleModuleExtensionByZero.{u, r} Λ i).map v).hom.naturality
        (complementInclusion i j h φ).op)
    refine n.symm.trans ?_
    refine (congrArg (fun y => (((etaleModuleExtensionByZero.{u, r} Λ i).map v).hom.app
      (op (complementObj i j h φ))).hom y) h₂).trans ?_
    exact map_zero _

/-- The exchange morphisms `α_G` as a natural transformation `j_! ∘ f_* ⟶ f'_* ∘ i_!`. -/
def openProperExchangeNatTrans :
    etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ i ⋙ etaleModuleDirectImage.{u, r} Λ f' where
  app G := openProperExchangeMap Λ i j h G
  naturality _ _ v := openProperExchangeMap_naturality Λ i j h v

theorem openProperExchangeNatTrans_app :
    (openProperExchangeNatTrans Λ i j h).app G = openProperExchangeMap Λ i j h G :=
  rfl

end Exchange

end AlgebraicGeometry
