module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.OpenProperExchangeMapDerived
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTraceShortExact
public import Weil.Attr

/-!
# The exchange of `j_!` with proper direct images is an isomorphism

Consider a commutative square of schemes
```
  X --i--> X'
  |        |
  f        f'
  v        v
  Y --j--> Y'
```
with `i` and `j` open immersions and `f`, `f'` proper, and let `F` be a bounded below complex of
sheaves of `Λ`-modules on the small étale site of `X` whose cohomology sheaves are torsion. Then
the morphism `(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` of bounded below derived categories induced by
the exchange morphisms `j_! f_* ⟶ f'_* i_!` is an isomorphism.

The proof is the source's. Restrictions to the open `Y` and to its closed complement jointly
reflect isomorphisms of `D⁺(Y'_ét, Λ)`.

* Over the closed complement both sides vanish: the source because it is an extension by zero
  from `Y`, the target by proper base change, the inverse image of `i_! F` to the part of `X'`
  lying over the complement being zero.
* Over `Y`, let `u : i_! F ⟶ J` be an injective resolution. Put `X_1 = X' ×_{Y'} Y`; then `X` is
  open and closed in `X_1`, with complement `X''`, an open subscheme of `X'`. For `V` étale over
  `Y` the sections of `J` over `X'_V = X_1 ×_Y V` split as sections over `X_V` and over
  `X'_V ×_{X'} X''`. Accordingly, with `ψ : f_* (J|_X) ⟶ j^{-1} f'_* J` the restriction of the
  exchange chain map (composed with the unit of `j_! ⊣ j^{-1}`), restriction of sections
  `ρ : j^{-1} f'_* J ⟶ f_* (J|_X)`, restriction `η` to `X''` and extension by zero `ζ` from `X''`,
  one has `ρ ∘ ψ = 1` and `ψ ∘ ρ + ζ ∘ η = 1`. The complex `j^{-1} f'_* o_* (J|_{X''})` through
  which `ζ ∘ η` factors (`o : X'' ⟶ X'`) is acyclic: `J|_{X''}` is an injective resolution of
  `(i_! F)|_{X''} = 0`, so this complex computes a derived functor at `0`. Hence `ψ` is a
  quasi-isomorphism.

## Main results

* `AlgebraicGeometry.isIso_openProperExchangeDerivedMap`: the morphism `(*)` is an isomorphism.

## Implementation notes

The sheaves are sheaves of `Λ`-modules, `Λ` an arbitrary ring, on Mathlib's small étale sites
`X.Etale`, the setting of `AlgebraicGeometry.openProperExchangeDerivedMap`; the source's abelian
sheaves are the case `Λ = ℤ`. The coefficient ring lives in `Type`, the universe of the proper
base change theorem `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper` used
over the closed complement. An object of `D_{+,tor}(X)` is presented by a bounded below complex
`F` whose image in `D⁺` has torsion cohomology sheaves (`Stacks.EtaleCohomology.isTorsionPlus`),
and the morphism `(*)` is computed through an arbitrary injective resolution of `i_! F`, on which
it does not depend (`AlgebraicGeometry.openProperExchangeDerivedMap_eq_of_resolution`).

The square is only assumed commutative, as in the source; when it is cartesian, `X''` is empty.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.5, pp. 87–88.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

open ExchangeSquare

section Complement

variable {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') [IsOpenImmersion i]
  (j : Y ⟶ Y') [IsOpenImmersion j] {f : X ⟶ Y} {f' : X' ⟶ Y'} [IsProper f] [IsSeparated f']
  (h : i ≫ f' = f ≫ j)

/-- The complement `X'' = X_1 \ X` of `X` in `X_1 = X' ×_{Y'} Y`, as an object of the small
étale site of `X'`. -/
private abbrev cplObj : X'.Etale := complementObj i j h (𝟙 (smallEtaleSource j))

/-- The open immersion `X'' ⟶ X'`. -/
private abbrev cplHom : (cplObj i j h).left ⟶ X' := (cplObj i j h).hom

omit [IsOpenImmersion i] in
private theorem isOpenImmersion_cplHom : IsOpenImmersion (cplHom i j h) := by
  have : IsOpenImmersion (Limits.pullback.snd j f') :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (IsPullback.of_hasPullback j f')
      ‹IsOpenImmersion j›
  exact @IsOpenImmersion.comp _ _ _ (complementOpens i j h (𝟙 (smallEtaleSource j))).ι _
    inferInstance this

omit [IsOpenImmersion i] in
/-- The images of `X'' ⟶ X'` and of `i` are disjoint. -/
private lemma disjoint_range_cplHom :
    Disjoint (Set.range (cplHom i j h).base) (Set.range i.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨c, rfl⟩ ⟨x, hx⟩
  set s : pullback j f' ⟶ X' := pullback.snd j f'
  have hs : Function.Injective s := s.isOpenEmbedding.injective
  have hp : x ∈ Set.range (pullback.snd
      (𝟙 (smallEtaleSource j) : smallEtaleSource j ⟶ smallEtaleSource j).left f) := by
    let l : X ⟶ pullback (𝟙 (smallEtaleSource j) : smallEtaleSource j ⟶ smallEtaleSource j).left f
        :=
      pullback.lift f (𝟙 X) ((Category.comp_id f).trans (Category.id_comp f).symm)
    refine ⟨l.base x, ?_⟩
    have := congrArg (fun k => k.base x) (pullback.lift_snd f (𝟙 X) ((Category.comp_id f).trans
        (Category.id_comp f).symm) :
      l ≫ pullback.snd _ _ = 𝟙 X)
    exact this
  obtain ⟨p, rfl⟩ := hp
  have hc : (complementOpens i j h (𝟙 (smallEtaleSource j))).ι c ∈
      (Set.range (inclusionLeft i j h (𝟙 (smallEtaleSource j))).base)ᶜ := by
    rw [← range_complementInclusion_left]
    exact ⟨c, rfl⟩
  apply hc
  refine ⟨p, hs ?_⟩
  have e1 := congrArg (fun k => k.base p) (inclusionLeft_snd i j h (𝟙 (smallEtaleSource j)))
  exact e1.trans hx

/-- The morphism `W ×_{X'} X'' ⟶ W` of the small étale site of `X'`. -/
private def cplCounit (W : X'.Etale) :
    (smallEtaleCompose (cplHom i j h)).obj ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i
        j h)).obj W) ⟶ W :=
  MorphismProperty.Over.homMk (pullback.fst W.hom (cplHom i j h)) pullback.condition trivial

private lemma mono_of_mono_left' {T : Scheme.{u}} {A B : T.Etale} (g : A ⟶ B) [Mono g.left] :
    Mono g := by
  constructor
  intro Z a b hab
  ext : 1
  exact (cancel_mono g.left).1 (congrArg (fun k => k.left) hab)

omit [IsOpenImmersion i] in
private lemma mono_cplCounit (W : X'.Etale) : Mono (cplCounit i j h W) := by
  have : Mono (cplCounit i j h W).left := by
    have := isOpenImmersion_cplHom i j h
    change Mono (pullback.fst W.hom (cplHom i j h))
    infer_instance
  exact mono_of_mono_left' _

omit [IsProper f] [IsSeparated f'] in
private lemma mono_inclusion {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    Mono (ExchangeSquare.inclusion i j h φ) := by
  have : Mono (ExchangeSquare.inclusion i j h φ).left := mono_inclusionLeft i j h φ
  exact mono_of_mono_left' _

attribute [local instance] mono_cplCounit mono_inclusion

omit [IsOpenImmersion i] in
/-- A point of `X'_V`, for `V` factoring through `j`, lies in the image of `X_V` if and only if it
does not lie over `X''`. -/
private lemma mem_range_inclusionLeft_iff {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (x : (targetObj f' V).left) :
    x ∈ Set.range (inclusionLeft i j h φ) ↔
      x ∉ Set.range (cplCounit i j h (targetObj f' V)).left := by
  have hT := inclusionLeft_comp_targetMap_left i j h φ (𝟙 (smallEtaleSource j))
  have hm := mem_range_inclusionLeft_of_targetMap i j h φ (𝟙 (smallEtaleSource j)) (x := x)
  set T := (ExchangeSquare.targetMap f' φ).left
  have key₁ : x ∈ Set.range (inclusionLeft i j h (φ ≫ 𝟙 (smallEtaleSource j))) ↔
      T x ∈ Set.range (inclusionLeft i j h (𝟙 (smallEtaleSource j))) :=
    ⟨fun ⟨y, hy⟩ => ⟨(ExchangeSquare.sourceMap j f φ (𝟙 (smallEtaleSource j))).left y, by
      have := congrArg (fun k => k.base y) hT
      rw [← hy]
      exact this.symm⟩, hm⟩
  rw [Category.comp_id] at key₁
  rw [key₁]
  set s : pullback j f' ⟶ X' := pullback.snd j f'
  have hs : Function.Injective s := s.isOpenEmbedding.injective
  have hTs : T ≫ s = (targetObj f' V).hom := by
    simp only [T, s, ExchangeSquare.smallEtaleBaseChange_map_left]
    exact pullback.lift_snd _ _ _
  change _ ↔ x ∉ Set.range (pullback.fst (targetObj f' V).hom (cplHom i j h))
  rw [Scheme.Pullback.range_fst]
  change _ ↔ ¬ (targetObj f' V).hom x ∈
    Set.range ((complementOpens i j h (𝟙 (smallEtaleSource j))).ι ≫ s)
  rw [← hTs]
  change _ ↔ ¬ s (T x) ∈ _
  constructor
  · rintro hx ⟨y, hy⟩
    have := hs hy
    have hy' : (complementOpens i j h (𝟙 (smallEtaleSource j))).ι y ∈
        (Set.range (inclusionLeft i j h (𝟙 (smallEtaleSource j))).base)ᶜ := by
      rw [← range_complementInclusion_left]
      exact ⟨y, rfl⟩
    have hy'' : T x ∈ (Set.range (inclusionLeft i j h (𝟙 (smallEtaleSource j))).base)ᶜ := by
      rw [← this]
      exact hy'
    exact hy'' hx
  · intro hx
    by_contra hx'
    have : T x ∈ Set.range (complementInclusion i j h (𝟙 (smallEtaleSource j))).left.base := by
      rw [range_complementInclusion_left]
      exact hx'
    obtain ⟨y, hy⟩ := this
    exact hx ⟨y, congrArg s hy⟩


variable (Λ : Type) [Ring Λ]

/-- A section of a sheaf over `X'_V` is determined by its restrictions to `X_V` and to
`X'_V ×_{X'} X''`, and any pair of sections over these glues. -/
private lemma existsUnique_map_inclusion_and_map_cplCounit (S : EtaleModules.{u, 0} Λ X')
    {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (x : S.obj.obj (op ((smallEtaleCompose i).obj (sourceObj j f φ))))
    (y : S.obj.obj (op ((smallEtaleCompose (cplHom i j h)).obj
      ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).obj (targetObj f' V))))) :
    ∃! z : S.obj.obj (op (targetObj f' V)),
      (S.obj.map (ExchangeSquare.inclusion i j h φ).op).hom z = x ∧
        (S.obj.map (cplCounit i j h (targetObj f' V)).op).hom z = y := by
  have hS : Presieve.IsSheaf X'.smallEtaleTopology (S.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose X'.smallEtaleTopology (forget (ModuleCat.{u + 1} Λ))).obj S).property
  have hcov : Set.range (ExchangeSquare.inclusion i j h φ).left ∪
      Set.range (cplCounit i j h (targetObj f' V)).left = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx : x ∈ Set.range (cplCounit i j h (targetObj f' V)).left
    · exact Or.inr hx
    · exact Or.inl ((mem_range_inclusionLeft_iff i j h φ x).2 hx)
  have hdisj : Disjoint (Set.range (ExchangeSquare.inclusion i j h φ).left)
      (Set.range (cplCounit i j h (targetObj f' V)).left) :=
    Set.disjoint_left.2 fun x hx => (mem_range_inclusionLeft_iff i j h φ x).1 hx
  exact Scheme.Etale.existsUnique_map_eq_of_disjoint hS _ _ hcov hdisj x y

/-- The restriction maps to `X_V` and to `X'_V ×_{X'} X''` identify the sections over `X'_V`
with pairs. -/
private def cplRestrictionLinearEquiv (S : EtaleModules.{u, 0} Λ X') {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) :
    S.obj.obj (op (targetObj f' V)) ≃ₗ[Λ]
      S.obj.obj (op ((smallEtaleCompose i).obj (sourceObj j f φ))) ×
        S.obj.obj (op ((smallEtaleCompose (cplHom i j h)).obj
          ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).obj (targetObj f' V)))) :=
  LinearEquiv.ofBijective
    (LinearMap.prod (S.obj.map (ExchangeSquare.inclusion i j h φ).op).hom
      (S.obj.map (cplCounit i j h (targetObj f' V)).op).hom)
    ⟨fun z z' hz => (existsUnique_map_inclusion_and_map_cplCounit i j h Λ S φ
        ((S.obj.map (ExchangeSquare.inclusion i j h φ).op).hom z')
        ((S.obj.map (cplCounit i j h (targetObj f' V)).op).hom z')).unique
        ⟨(Prod.ext_iff.1 hz).1, (Prod.ext_iff.1 hz).2⟩ ⟨rfl, rfl⟩,
      fun p => by
        obtain ⟨z, hz, -⟩ := existsUnique_map_inclusion_and_map_cplCounit i j h Λ S φ p.1 p.2
        exact ⟨z, Prod.ext hz.1 hz.2⟩⟩

private lemma eq_of_map_inclusion_of_map_cplCounit (S : EtaleModules.{u, 0} Λ X')
    {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) {z z' : S.obj.obj (op (targetObj f' V))}
    (h₁ : (S.obj.map (ExchangeSquare.inclusion i j h φ).op).hom z =
      (S.obj.map (ExchangeSquare.inclusion i j h φ).op).hom z')
    (h₂ : (S.obj.map (cplCounit i j h (targetObj f' V)).op).hom z =
      (S.obj.map (cplCounit i j h (targetObj f' V)).op).hom z') : z = z' :=
  (cplRestrictionLinearEquiv i j h Λ S φ).injective (Prod.ext h₁ h₂)

omit [IsOpenImmersion i] in
private lemma cplCounit_naturality {W W' : X'.Etale} (g : W' ⟶ W) :
    (smallEtaleCompose (cplHom i j h)).map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).map g) ≫
      cplCounit i j h W = cplCounit i j h W' ≫ g := by
  ext : 1
  exact pullback.lift_fst _ _ _

omit [IsProper f] [IsSeparated f'] in
private lemma inclusion_comp_targetMap {U U' : Y.Etale} (g : U' ⟶ U) :
    ExchangeSquare.inclusion i j h (structureHomToSource j U') ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChange f').map ((smallEtaleCompose j).map g) =
      (smallEtaleCompose i).map ((Stacks.EtaleCohomology.smallEtaleBaseChange f).map g) ≫
        ExchangeSquare.inclusion i j h (structureHomToSource j U) := by
  ext : 1
  apply pullback.hom_ext
  · change inclusionLeft i j h _ ≫ pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫
      inclusionLeft i j h _ ≫ _
    simp only [inclusionLeft_fst]
    erw [pullback.lift_fst, inclusionLeft_fst_assoc, pullback.lift_fst]
    rfl
  · change inclusionLeft i j h _ ≫ pullback.lift _ _ _ ≫ _ = pullback.lift _ _ _ ≫
      inclusionLeft i j h _ ≫ _
    simp only [inclusionLeft_snd]
    erw [pullback.lift_snd, inclusionLeft_snd, pullback.lift_snd_assoc]
    rfl

/-- The morphism `G ⟶ o_* o^{-1} G` restricting sections to `W ×_{X'} X''`. -/
private def cplUnit (G : EtaleModules.{u, 0} Λ X') :
    G ⟶ (etaleModuleDirectImage.{u, 0} Λ (cplHom i j h)).obj
      ((etaleModuleRestriction.{u, 0} Λ (cplHom i j h)).obj G) :=
  Sheaf.homEquiv.symm
    { app := fun W => G.obj.map (cplCounit i j h W.unop).op
      naturality := fun W W' g => by
        change G.obj.map g ≫ G.obj.map (cplCounit i j h W'.unop).op =
          G.obj.map (cplCounit i j h W.unop).op ≫ G.obj.map ((smallEtaleCompose (cplHom i j h)).map
            ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).map g.unop)).op
        rw [← G.obj.map_comp, ← G.obj.map_comp, ← op_comp, cplCounit_naturality]
        rfl }

/-- The restriction `ρ_G : j^{-1} f'_* G ⟶ f_* i^{-1} G` of sections over `X'_V` to `X_V`. -/
private def cplRestrict (G : EtaleModules.{u, 0} Λ X') :
    (etaleModuleRestriction.{u, 0} Λ j).obj ((etaleModuleDirectImage.{u, 0} Λ f').obj G) ⟶
      (etaleModuleDirectImage.{u, 0} Λ f).obj ((etaleModuleRestriction.{u, 0} Λ i).obj G) :=
  Sheaf.homEquiv.symm
    { app := fun U => G.obj.map (ExchangeSquare.inclusion i j h (structureHomToSource j U.unop)).op
      naturality := fun U U' g => by
        change G.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChange f').map
            ((smallEtaleCompose j).map g.unop)).op ≫
            G.obj.map (ExchangeSquare.inclusion i j h (structureHomToSource j U'.unop)).op =
          G.obj.map (ExchangeSquare.inclusion i j h (structureHomToSource j U.unop)).op ≫
            G.obj.map ((smallEtaleCompose i).map
              ((Stacks.EtaleCohomology.smallEtaleBaseChange f).map g.unop)).op
        erw [← G.obj.map_comp, ← G.obj.map_comp]
        congr 1
        exact op_comp.symm.trans ((congrArg Quiver.Hom.op
          (inclusion_comp_targetMap i j h g.unop)).trans op_comp) }

/-- The section of `S` over `X'_V` which is `0` on `X_V` and `y` on `X'_V ×_{X'} X''`. -/
private def cplGlueLinearMap (S : EtaleModules.{u, 0} Λ X') {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) :
    S.obj.obj (op ((smallEtaleCompose (cplHom i j h)).obj
        ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).obj (targetObj f' V)))) →ₗ[Λ]
      S.obj.obj (op (targetObj f' V)) :=
  (cplRestrictionLinearEquiv i j h Λ S φ).symm.toLinearMap ∘ₗ LinearMap.inr Λ _ _

private lemma cplGlueLinearMap_spec (S : EtaleModules.{u, 0} Λ X') {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) (y) :
    (S.obj.map (ExchangeSquare.inclusion i j h φ).op).hom (cplGlueLinearMap i j h Λ S φ y) = 0 ∧
      (S.obj.map (cplCounit i j h (targetObj f' V)).op).hom (cplGlueLinearMap i j h Λ S φ y) =
        y := by
  have := (cplRestrictionLinearEquiv i j h Λ S φ).apply_symm_apply (0, y)
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- The gluing `ζ_G : j^{-1} f'_* o_* o^{-1} G ⟶ j^{-1} f'_* G`, extension by zero from
`X'_V ×_{X'} X''` to `X'_V`. -/
private def cplGlue (G : EtaleModules.{u, 0} Λ X') :
    (etaleModuleRestriction.{u, 0} Λ j).obj ((etaleModuleDirectImage.{u, 0} Λ f').obj
        ((etaleModuleDirectImage.{u, 0} Λ (cplHom i j h)).obj
          ((etaleModuleRestriction.{u, 0} Λ (cplHom i j h)).obj G))) ⟶
      (etaleModuleRestriction.{u, 0} Λ j).obj ((etaleModuleDirectImage.{u, 0} Λ f').obj G) :=
  Sheaf.homEquiv.symm
    { app := fun U => ModuleCat.ofHom (cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop))
      naturality := fun U U' g => by
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        set T := (Stacks.EtaleCohomology.smallEtaleBaseChange f').map ((smallEtaleCompose j).map
            g.unop)
        change cplGlueLinearMap i j h Λ G (structureHomToSource j U'.unop)
            ((G.obj.map ((smallEtaleCompose (cplHom i j h)).map
              ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).map T)).op).hom y) =
          (G.obj.map T.op).hom (cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop) y)
        obtain ⟨h₁, h₂⟩ := cplGlueLinearMap_spec i j h Λ G (structureHomToSource j U.unop) y
        obtain ⟨h₁', h₂'⟩ := cplGlueLinearMap_spec i j h Λ G (structureHomToSource j U'.unop)
          ((G.obj.map ((smallEtaleCompose (cplHom i j h)).map
              ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).map T)).op).hom y)
        apply eq_of_map_inclusion_of_map_cplCounit i j h Λ G (structureHomToSource j U'.unop)
        · set z := cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop) y
          have e1 := ExchangeSquare.map_comp_op_apply G.obj
            (ExchangeSquare.inclusion i j h (structureHomToSource j U'.unop)) T z
          have e2 := ExchangeSquare.map_comp_op_apply G.obj
            ((smallEtaleCompose i).map ((Stacks.EtaleCohomology.smallEtaleBaseChange f).map g.unop))
            (ExchangeSquare.inclusion i j h (structureHomToSource j U.unop)) z
          rw [inclusion_comp_targetMap] at e1
          rw [h₁', ← e1]
          erw [e2, h₁, map_zero]
          rfl
        · set z := cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop) y
          have e1 := ExchangeSquare.map_comp_op_apply G.obj
            (cplCounit i j h (targetObj f' ((smallEtaleCompose j).obj U'.unop))) T z
          have e2 := ExchangeSquare.map_comp_op_apply G.obj
            ((smallEtaleCompose (cplHom i j h)).map
              ((Stacks.EtaleCohomology.smallEtaleBaseChange (cplHom i j h)).map T))
            (cplCounit i j h (targetObj f' ((smallEtaleCompose j).obj U.unop))) z
          rw [cplCounit_naturality] at e2
          rw [h₂', ← e1]
          erw [e2, h₂] }

omit [IsOpenImmersion j] in
private lemma sourceDescendIso_structureHomToSource_inv {T S : Scheme.{u}} (e : T ⟶ S) [Etale e]
    (U : T.Etale) : (sourceDescendIso e (structureHomToSource e U)).inv = 𝟙 _ := by
  ext : 1
  rfl

/-- The composite `ψ_G : f_* i^{-1} G ⟶ j^{-1} j_! f_* i^{-1} G ⟶ j^{-1} f'_* G` of the unit of
`j_! ⊣ j^{-1}` and the restriction to `Y` of the exchange morphism `θ_G`. -/
private def cplExchange (G : EtaleModules.{u, 0} Λ X') :
    (etaleModuleDirectImage.{u, 0} Λ f).obj ((etaleModuleRestriction.{u, 0} Λ i).obj G) ⟶
      (etaleModuleRestriction.{u, 0} Λ j).obj ((etaleModuleDirectImage.{u, 0} Λ f').obj G) :=
  (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app _ ≫
    (etaleModuleRestriction.{u, 0} Λ j).map
      ((exchangeCounitTransformation Λ i j (openProperExchangeNatTrans Λ i j h)).app G)

private lemma cplExchange_apply (G : EtaleModules.{u, 0} Λ X') (U : Y.Etale)
    (s : ((etaleModuleRestriction.{u, 0} Λ i).obj G).obj.obj
      (op (sourceObj j f (structureHomToSource j U)))) :
    ((cplExchange i j h Λ G).hom.app (op U)).hom s =
      (((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).counit.app G).hom.app
        (op (targetObj f' ((smallEtaleCompose j).obj U)))).hom
        (exchangeGlue Λ i j h ((etaleModuleRestriction.{u, 0} Λ i).obj G)
          (structureHomToSource j U) s) := by
  have hu : (((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app ((etaleModuleDirectImage.{u, 0}
      Λ f).obj ((etaleModuleRestriction.{u, 0} Λ i).obj G))).hom.app
        (op U)).hom s =
      ((extensionByZeroPresheafToSheaf Λ j ((etaleModuleDirectImage.{u, 0} Λ f).obj
          ((etaleModuleRestriction.{u, 0} Λ i).obj G))).app (op ((smallEtaleCompose j).obj U))).hom
        ((Sigma.ι (fun ψ : (smallEtaleCompose j).obj U ⟶ smallEtaleSource j =>
          ((etaleModuleDirectImage.{u, 0} Λ f).obj ((etaleModuleRestriction.{u, 0} Λ i).obj
              G)).obj.obj (op (sourceDescend j ψ))) (structureHomToSource j U)).hom s) := by
    have e := congrArg (fun k => k.hom s)
      (ι_comp_extensionByZeroPresheafToSheaf_app Λ j ((etaleModuleDirectImage.{u, 0} Λ f).obj
          ((etaleModuleRestriction.{u, 0} Λ i).obj G)) ((smallEtaleCompose j).obj U)
        (structureHomToSource j U))
    refine Eq.trans ?_ e.symm
    change _ = ((((etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleDirectImage.{u, 0} Λ
        f).obj ((etaleModuleRestriction.{u, 0} Λ i).obj G))).obj.map
      (sourceDescendIso j (structureHomToSource j U)).inv.op).hom _)
    erw [sourceDescendIso_structureHomToSource_inv, op_id, CategoryTheory.Functor.map_id]
    rfl
  change (((exchangeCounitTransformation Λ i j (openProperExchangeNatTrans Λ i j h)).app G).hom.app
      (op ((smallEtaleCompose j).obj U))).hom
    ((((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app ((etaleModuleDirectImage.{u, 0} Λ
        f).obj ((etaleModuleRestriction.{u, 0} Λ i).obj G))).hom.app (op U)).hom s) = _
  erw [hu]
  refine Eq.trans ?_ (congrArg (((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).counit.app G).hom.app
    (op (targetObj f' ((smallEtaleCompose j).obj U)))).hom
      (exchangeSection_openProperExchangeMap Λ i j h ((etaleModuleRestriction.{u, 0} Λ i).obj G)
        (structureHomToSource j U) s))
  rfl

private lemma map_inclusion_cplExchange_apply (G : EtaleModules.{u, 0} Λ X') (U : Y.Etale)
    (s : ((etaleModuleRestriction.{u, 0} Λ i).obj G).obj.obj
      (op (sourceObj j f (structureHomToSource j U)))) :
    (G.obj.map (ExchangeSquare.inclusion i j h (structureHomToSource j U)).op).hom
      (((cplExchange i j h Λ G).hom.app (op U)).hom s) = s := by
  rw [cplExchange_apply]
  have h2 := congr_arg (fun g => g.hom (exchangeGlue Λ i j h ((etaleModuleRestriction.{u, 0} Λ
      i).obj G) (structureHomToSource j U) s))
    (((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).counit.app G).hom.naturality
        (ExchangeSquare.inclusion i j h (structureHomToSource j U)).op)
  refine h2.symm.trans ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [(exchangeGlue_spec Λ i j h ((etaleModuleRestriction.{u, 0} Λ i).obj G)
      (structureHomToSource j U) s).1]
  refine (etaleModuleExtensionByZeroAdj_counit_app_apply Λ i G _
    (structureHomToSource i (sourceObj j f (structureHomToSource j U))) s).trans ?_
  rw [sourceDescendIso_structureHomToSource_inv]
  exact congrArg (fun k => k.hom s) (G.obj.map_id _)

private lemma map_cplCounit_cplExchange_apply (G : EtaleModules.{u, 0} Λ X') (U : Y.Etale)
    (s : ((etaleModuleRestriction.{u, 0} Λ i).obj G).obj.obj
      (op (sourceObj j f (structureHomToSource j U)))) :
    (G.obj.map (cplCounit i j h (targetObj f' ((smallEtaleCompose j).obj U))).op).hom
      (((cplExchange i j h Λ G).hom.app (op U)).hom s) = 0 := by
  rw [cplExchange_apply]
  have h2 := congr_arg (fun g => g.hom (exchangeGlue Λ i j h ((etaleModuleRestriction.{u, 0} Λ
      i).obj G) (structureHomToSource j U) s))
    (((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).counit.app G).hom.naturality (cplCounit i j h
        (targetObj f' ((smallEtaleCompose j).obj U))).op)
  refine h2.symm.trans ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [map_eq_zero_of_disjoint_of_map_complementInclusion Λ i j h (structureHomToSource j U) _
    (exchangeGlue_spec Λ i j h ((etaleModuleRestriction.{u, 0} Λ i).obj G) (structureHomToSource j
        U) s).2 _ (Set.disjoint_right.2 fun x hx =>
      (mem_range_inclusionLeft_iff i j h (structureHomToSource j U) x).1 hx)]
  exact map_zero _

private lemma cplExchange_comp_cplRestrict (G : EtaleModules.{u, 0} Λ X') :
    cplExchange i j h Λ G ≫ cplRestrict i j h Λ G = 𝟙 _ := by
  apply Sheaf.homEquiv.injective
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  exact map_inclusion_cplExchange_apply i j h Λ G U.unop s

private lemma cplRestrict_comp_cplExchange_add (G : EtaleModules.{u, 0} Λ X') :
    cplRestrict i j h Λ G ≫ cplExchange i j h Λ G +
      (etaleModuleRestriction.{u, 0} Λ j).map ((etaleModuleDirectImage.{u, 0} Λ f').map
        (cplUnit i j h Λ G)) ≫ cplGlue i j h Λ G = 𝟙 _ := by
  apply Sheaf.homEquiv.injective
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun t => ?_))
  obtain ⟨h₁, h₂⟩ := cplGlueLinearMap_spec i j h Λ G (structureHomToSource j U.unop)
    ((G.obj.map (cplCounit i j h (targetObj f' ((smallEtaleCompose j).obj U.unop))).op).hom t)
  change (show G.obj.obj (op (targetObj f' ((smallEtaleCompose j).obj U.unop))) from
      ((cplExchange i j h Λ G).hom.app U).hom
      ((G.obj.map (ExchangeSquare.inclusion i j h (structureHomToSource j U.unop)).op).hom t)) +
    cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop)
      ((G.obj.map (cplCounit i j h (targetObj f' ((smallEtaleCompose j).obj U.unop))).op).hom t) =
    t
  apply eq_of_map_inclusion_of_map_cplCounit i j h Λ G (structureHomToSource j U.unop)
  · rw [map_add, h₁, add_zero]
    exact map_inclusion_cplExchange_apply i j h Λ G U.unop _
  · rw [map_add, h₂]
    erw [map_cplCounit_cplExchange_apply]
    rw [zero_add]

/-- `ψ` as a natural transformation `f_* i^{-1} ⟶ j^{-1} f'_*`. -/
private def cplExchangeNatTrans : (etaleModuleRestriction.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u,
    0} Λ f) ⟶ (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleRestriction.{u, 0} Λ j) where
  app G := cplExchange i j h Λ G
  naturality G G' v := by
    have h1 := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.naturality
      ((etaleModuleDirectImage.{u, 0} Λ f).map ((etaleModuleRestriction.{u, 0} Λ i).map v))
    have h2 := (exchangeCounitTransformation Λ i j (openProperExchangeNatTrans Λ i j
        h)).naturality v
    dsimp only [cplExchange]
    erw [← Category.assoc, h1, Category.assoc, Functor.comp_map, ← Functor.map_comp, h2,
      Functor.map_comp]
    rfl

/-- `ρ` as a natural transformation `j^{-1} f'_* ⟶ f_* i^{-1}`. -/
private def cplRestrictNatTrans : (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleRestriction.{u,
    0} Λ j) ⟶ (etaleModuleRestriction.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u, 0} Λ f) where
  app G := cplRestrict i j h Λ G
  naturality G G' v := by
    apply Sheaf.homEquiv.injective
    refine NatTrans.ext (funext fun U => ?_)
    exact (v.hom.naturality _).symm

/-- The unit `G ⟶ o_* o^{-1} G` as a natural transformation. -/
private def cplUnitNatTrans : 𝟭 (EtaleModules.{u, 0} Λ X') ⟶ (etaleModuleRestriction.{u, 0} Λ
    (cplHom i j h) ⋙ etaleModuleDirectImage.{u, 0} Λ (cplHom i j h)) where
  app G := cplUnit i j h Λ G
  naturality G G' v := by
    apply Sheaf.homEquiv.injective
    refine NatTrans.ext (funext fun W => ?_)
    exact (v.hom.naturality _).symm

/-- `ζ` as a natural transformation `j^{-1} f'_* o_* o^{-1} ⟶ j^{-1} f'_*`. -/
private def cplGlueNatTrans : (etaleModuleRestriction.{u, 0} Λ (cplHom i j h) ⋙
    etaleModuleDirectImage.{u, 0} Λ (cplHom i j h)) ⋙ (etaleModuleDirectImage.{u, 0} Λ f' ⋙
    etaleModuleRestriction.{u, 0} Λ j) ⟶ (etaleModuleDirectImage.{u, 0} Λ f' ⋙
    etaleModuleRestriction.{u, 0} Λ j) where
  app G := cplGlue i j h Λ G
  naturality G G' v := by
    apply Sheaf.homEquiv.injective
    refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
    obtain ⟨h₁, h₂⟩ := cplGlueLinearMap_spec i j h Λ G (structureHomToSource j U.unop) y
    change cplGlueLinearMap i j h Λ G' (structureHomToSource j U.unop) ((v.hom.app _).hom y) =
      (v.hom.app _).hom (cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop) y)
    obtain ⟨h₁', h₂'⟩ := cplGlueLinearMap_spec i j h Λ G' (structureHomToSource j U.unop)
      ((v.hom.app _).hom y)
    apply eq_of_map_inclusion_of_map_cplCounit i j h Λ G' (structureHomToSource j U.unop)
    · rw [h₁']
      have := congrArg (fun k => k.hom (cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop)
          y))
        (v.hom.naturality (ExchangeSquare.inclusion i j h (structureHomToSource j U.unop)).op)
      erw [← this]
      erw [ModuleCat.hom_comp, LinearMap.comp_apply, h₁, map_zero]
    · rw [h₂']
      have := congrArg (fun k => k.hom (cplGlueLinearMap i j h Λ G (structureHomToSource j U.unop)
          y))
        (v.hom.naturality (cplCounit i j h (targetObj f' ((smallEtaleCompose j).obj U.unop))).op)
      erw [← this]
      erw [ModuleCat.hom_comp, LinearMap.comp_apply, h₂]

end Complement

section Main

variable (Λ : Type) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') [IsOpenImmersion i]
  (j : Y ⟶ Y') [IsOpenImmersion j] {f : X ⟶ Y} {f' : X' ⟶ Y'} [IsProper f] [IsProper f']

omit [IsProper f'] in
/-- The restriction to `Y` of the exchange chain map `θ_J` is a quasi-isomorphism. -/
private lemma quasiIso_restriction_map_exchangeChainMap (h : i ≫ f' = f ≫ j) [IsSeparated f']
    {F : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, 0} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    QuasiIso (((etaleModuleRestriction.{u, 0} Λ j).mapHomologicalComplex _).map
      (exchangeChainMap Λ i j (openProperExchangeNatTrans Λ i j h) J.obj)) := by
  -- the complement part `C = j^{-1} f'_* o_* o^{-1} J` is acyclic
  have hC : ∀ n, IsZero (((((etaleModuleRestriction.{u, 0} Λ (cplHom i j h) ⋙
      etaleModuleDirectImage.{u, 0} Λ (cplHom i j h)) ⋙ (etaleModuleDirectImage.{u, 0} Λ f' ⋙
      etaleModuleRestriction.{u, 0} Λ j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      J.obj).homology n) := by
    intro n
    have : IsOpenImmersion (cplHom i j h) := isOpenImmersion_cplHom i j h
    let Gc := etaleModuleDirectImage.{u, 0} Λ (cplHom i j h) ⋙ (etaleModuleDirectImage.{u, 0} Λ f'
        ⋙ etaleModuleRestriction.{u, 0} Λ j)
    let K' := (etaleModuleRestriction.{u, 0} Λ (cplHom i j h)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj F)
    let J' := (etaleModuleRestriction.{u, 0} Λ (cplHom i j h)).mapCochainComplexPlus.obj J
    let u' := (etaleModuleRestriction.{u, 0} Λ (cplHom i j h)).mapCochainComplexPlus.map u
    have : QuasiIso u'.hom := by
      change QuasiIso (((etaleModuleRestriction.{u, 0} Λ (cplHom i j h)).mapHomologicalComplex
        _).map u.hom)
      infer_instance
    have : ∀ n, Injective (J'.obj.X n) := fun n => by
      change Injective ((etaleModuleRestriction.{u, 0} Λ (cplHom i j h)).obj (J.obj.X n))
      infer_instance
    have hK'X : ∀ m, IsZero (K'.obj.X m) := fun m =>
      (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ (cplHom i j h) i
        (disjoint_range_cplHom i j h) (F.obj.X m)).of_iso
          ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ (cplHom i j h)).app _).symm
    have hK'0 : IsZero K'.obj := by
      rw [IsZero.iff_id_eq_zero]
      ext m : 1
      exact (hK'X m).eq_of_src _ _
    have hQK : IsZero (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj K')) :=
        by
      refine isZero_of_forall_isZero_homology_plus _ fun q => ?_
      refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ q).mapIso
        ((DerivedCategory.quotientCompQhIso _).app K'.obj) ≪≫
          (DerivedCategory.homologyFunctorFactors _ q).app K'.obj)
      exact (HomologicalComplex.homologyFunctor _ _ q).map_isZero hK'0
    have h1 : IsZero (Gc.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient _).obj K'))) :=
      Functor.isZero_rightDerivedFunctorPlus_obj Gc hQK
    have h2 := h1.of_iso (Gc.rightDerivedFunctorPlusObjIsoOfInjective u').symm
    have h3 : IsZero (DerivedCategory.Q.obj ((Gc.mapHomologicalComplex _).obj J'.obj)) :=
      (DerivedCategory.Plus.ι.map_isZero h2).of_iso
        ((DerivedCategory.quotientCompQhIso _).app _).symm
    exact ((DerivedCategory.homologyFunctor _ n).map_isZero h3).of_iso
      ((DerivedCategory.homologyFunctorFactors _ n).app _).symm
  let ψJ := (NatTrans.mapHomologicalComplex (cplExchangeNatTrans i j h Λ)
    (ComplexShape.up ℤ)).app J.obj
  let ρJ := (NatTrans.mapHomologicalComplex (cplRestrictNatTrans i j h Λ)
    (ComplexShape.up ℤ)).app J.obj
  let ηJ : ((etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleRestriction.{u, 0} Λ
      j).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.obj ⟶
      (((etaleModuleRestriction.{u, 0} Λ (cplHom i j h) ⋙ etaleModuleDirectImage.{u, 0} Λ (cplHom
          i j h)) ⋙ (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleRestriction.{u, 0} Λ
          j)).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.obj :=
    (NatTrans.mapHomologicalComplex (Functor.whiskerRight (cplUnitNatTrans i j h Λ)
        (etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleRestriction.{u, 0} Λ j))
    (ComplexShape.up ℤ)).app J.obj
  let ζJ := (NatTrans.mapHomologicalComplex (cplGlueNatTrans i j h Λ)
    (ComplexShape.up ℤ)).app J.obj
  have I1 : ψJ ≫ ρJ = 𝟙 _ := by
    ext n : 1
    exact cplExchange_comp_cplRestrict i j h Λ (J.obj.X n)
  have I2 : ρJ ≫ ψJ + ηJ ≫ ζJ = 𝟙 _ := by
    ext n : 1
    exact cplRestrict_comp_cplExchange_add i j h Λ (J.obj.X n)
  have hψ : QuasiIso ψJ := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine ⟨⟨HomologicalComplex.homologyMap ρJ n, ?_, ?_⟩⟩
    · rw [← HomologicalComplex.homologyMap_comp, I1, HomologicalComplex.homologyMap_id]
    · have := congrArg (fun φ => HomologicalComplex.homologyMap φ n) I2
      simp only [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
        HomologicalComplex.homologyMap_id] at this
      rw [(hC n).eq_zero_of_tgt (HomologicalComplex.homologyMap ηJ n), zero_comp,
        add_zero] at this
      exact this
  let υJ := (NatTrans.mapHomologicalComplex (Functor.whiskerLeft (etaleModuleRestriction.{u, 0} Λ
      i ⋙ etaleModuleDirectImage.{u, 0} Λ f)
    (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit) (ComplexShape.up ℤ)).app J.obj
  have hυ : IsIso υJ := by
    have : ∀ n, IsIso (υJ.f n) := fun n => by
      change IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app _)
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have e : ψJ = υJ ≫ ((etaleModuleRestriction.{u, 0} Λ j).mapHomologicalComplex _).map
      (exchangeChainMap Λ i j (openProperExchangeNatTrans Λ i j h) J.obj) := by
    ext n : 1
    rfl
  rw [e] at hψ
  exact (quasiIso_iff_comp_left _ _).1 hψ

private lemma isIso_derivedRestriction_map_exchangeHomotopyCategoryPlusMap
    (h : i ≫ f' = f ≫ j) {F : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)}
    {J : CochainComplex.Plus (EtaleModules.{u, 0} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    IsIso ((etaleModuleDerivedRestriction.{u, 0} Λ j).map (DerivedCategory.Plus.Qh.map
      (Adjunction.exchangeHomotopyCategoryPlusMap (etaleModuleDirectImage.{u, 0} Λ f)
        (etaleModuleExtensionByZero.{u, 0} Λ j) (etaleModuleDirectImage.{u, 0} Λ f')
        (exchangeCounitTransformation Λ i j (openProperExchangeNatTrans Λ i j h)) J))) := by
  set G := etaleModuleRestriction.{u, 0} Λ j
  set φ := Adjunction.exchangeHomotopyCategoryPlusMap (etaleModuleDirectImage.{u, 0} Λ f)
    (etaleModuleExtensionByZero.{u, 0} Λ j) (etaleModuleDirectImage.{u, 0} Λ f')
    (exchangeCounitTransformation Λ i j (openProperExchangeNatTrans Λ i j h)) J
  have hu := Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology G
  have hu' : ∀ K, IsIso (G.rightDerivedFunctorPlusUnit.app K) := fun K =>
    NatIso.isIso_app_of_isIso _ K
  have hθ := quasiIso_restriction_map_exchangeChainMap Λ i j h u
  have hθ' : QuasiIso (ObjectProperty.homMk (P := CochainComplex.plus _)
      (X := G.mapCochainComplexPlus.obj ((etaleModuleExtensionByZero.{u, 0} Λ
          j).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.obj
          ((etaleModuleRestriction.{u, 0} Λ i).mapCochainComplexPlus.obj J))))
      (Y := G.mapCochainComplexPlus.obj ((etaleModuleDirectImage.{u, 0} Λ
          f').mapCochainComplexPlus.obj J))
      ((G.mapHomologicalComplex _).map
        (exchangeChainMap Λ i j (openProperExchangeNatTrans Λ i j h) J.obj))).hom := hθ
  have hφ : IsIso (DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map φ)) :=
    Functor.isIso_plusQh_map_quotient_map
      (K := G.mapCochainComplexPlus.obj ((etaleModuleExtensionByZero.{u, 0} Λ
          j).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ f).mapCochainComplexPlus.obj
          ((etaleModuleRestriction.{u, 0} Λ i).mapCochainComplexPlus.obj J))))
      (L := G.mapCochainComplexPlus.obj ((etaleModuleDirectImage.{u, 0} Λ
          f').mapCochainComplexPlus.obj J))
      (ObjectProperty.homMk ((G.mapHomologicalComplex _).map
        (exchangeChainMap Λ i j (openProperExchangeNatTrans Λ i j h) J.obj)))
  have hn := G.rightDerivedFunctorPlusUnit.naturality φ
  have e : (DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus).map φ =
      inv (G.rightDerivedFunctorPlusUnit.app _) ≫
        (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map φ ≫
          G.rightDerivedFunctorPlusUnit.app _ := by
    have := hu' ((etaleModuleExtensionByZero.{u, 0} Λ j).mapHomotopyCategoryPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient _).obj
            ((etaleModuleRestriction.{u, 0} Λ i).mapCochainComplexPlus.obj J))))
    rw [hn, IsIso.inv_hom_id_assoc]
  change IsIso ((DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus).map φ)
  rw [e]
  have : IsIso ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map φ) := hφ
  have h1 := hu' ((etaleModuleExtensionByZero.{u, 0} Λ j).mapHomotopyCategoryPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategoryPlus.obj
          ((HomotopyCategory.Plus.quotient _).obj
            ((etaleModuleRestriction.{u, 0} Λ i).mapCochainComplexPlus.obj J))))
  exact IsIso.comp_isIso' (IsIso.inv_isIso (f := _)) (IsIso.comp_isIso' this (hu' _))

/-- **[FK, I.8.5]** In a commutative square `i ≫ f' = f ≫ j` of schemes with `i`, `j` open
immersions and `f`, `f'` proper, for a bounded below complex `F` of sheaves of `Λ`-modules on
the small étale site of `X` with torsion cohomology sheaves, the morphism
`(*) : j_! Rf_* F ⟶ Rf'_* (i_! F)` induced by the exchange morphisms is an isomorphism in
`D⁺(Y'_ét, Λ)`. -/
@[weil "thm_fk108_open_proper_exchange_quasi_isomorphism"]
theorem isIso_openProperExchangeDerivedMap (h : i ≫ f' = f ≫ j)
    {F : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)}
    (hF : isTorsionPlus.{u, 0} Λ X
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj F)))
    {J : CochainComplex.Plus (EtaleModules.{u, 0} Λ X')}
    (u : (etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj F ⟶ J)
    [QuasiIso u.hom] [∀ n, Injective (J.obj.X n)] :
    IsIso (openProperExchangeDerivedMap Λ i j (openProperExchangeNatTrans Λ i j h) u) := by
  let Zc : Y'.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let c := Zc.subschemeι
  have hic : Set.range j.base = (Set.range c.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl _).symm
  refine isIso_of_isIso_etaleModuleDerivedInverseImagePlus Λ c j hic _ ?_ ?_
  · set K := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj F)
    have h₁ : IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K))) :=
      isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint Λ c j
        (by rw [hic]; exact disjoint_compl_right) _
    have h₂ : IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f').obj
          (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj F))))) := by
      have hu := Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
        (etaleModuleExtensionByZero.{u, 0} Λ i)
      have hu' := NatIso.isIso_app_of_isIso
        (etaleModuleExtensionByZero.{u, 0} Λ i).rightDerivedFunctorPlusUnit
        ((HomotopyCategory.Plus.quotient _).obj F)
      let eK : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
            ((etaleModuleExtensionByZero.{u, 0} Λ i).mapCochainComplexPlus.obj F)) ≅
          (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj K :=
        @asIso _ _ _ _ ((etaleModuleExtensionByZero.{u, 0} Λ i).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient _).obj F)) hu'
      refine IsZero.of_iso ?_ ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).mapIso
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f').mapIso eK))
      have sqc := IsPullback.of_hasPullback f' c
      have hT := isIso_etaleModuleDerivedBaseChange_of_isProper Λ f' sqc
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj K)
        (isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ i K hF)
      refine IsZero.of_iso ?_ (asIso ((etaleModuleDerivedBaseChange.{u, 0} Λ f'
        (pullback.snd f' c) c (pullback.fst f' c) sqc.w.symm).app _))
      refine (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd f' c)).map_isZero ?_
      refine isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint Λ _ i ?_ _
      rw [Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
      have h₁ : f'.base ((pullback.fst f' c).base z) ∈ Set.range c.base :=
        ⟨(pullback.snd f' c).base z, by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
      have h₂ : f'.base ((pullback.fst f' c).base z) ∈ Set.range j.base :=
        ⟨f.base x, by
          rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]⟩
      rw [hic] at h₂
      exact h₂ h₁
    exact ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩
  · rw [← NatIso.isIso_map_iff (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ j),
      openProperExchangeDerivedMap_eq]
    have := isIso_derivedRestriction_map_exchangeHomotopyCategoryPlusMap Λ i j h u
    simp only [Functor.map_comp]
    infer_instance

end Main

end AlgebraicGeometry
