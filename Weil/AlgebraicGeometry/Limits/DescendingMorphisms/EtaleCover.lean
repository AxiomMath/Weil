module

public import Weil.Attr
public import Weil.CategoryTheory.Sites.LocallySurjective
public import Weil.CategoryTheory.Sites.CokernelOfPairIsCoequalizer
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleObject
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections

/-!
# Sections locally in the image of an epimorphism descend to a finite stage

Let `X = lim Xᵢ` be the limit of a cofiltered diagram of quasi-compact quasi-separated schemes
with affine transition morphisms, let `U₀` be a quasi-compact quasi-separated scheme étale over
a stage `X_{i₀}`, with base change `U = U₀ ×_{X_{i₀}} X`, and let `φ : F ⟶ G` be an epimorphism
of sheaves of sets on the small étale site of `X`. For every section `s ∈ G(U)` there are a
later stage `i₁ → i₀` and a surjective morphism `V₁ ⟶ U₀ ×_{X_{i₀}} X_{i₁}` of schemes étale over
`X_{i₁}` such that, with `V = V₁ ×_{X_{i₁}} X`, the restriction of `s` along the base-changed
morphism `V ⟶ U` lies in the image of `φ_V : F(V) ⟶ G(V)`.

Since `φ` is an epimorphism, `s` lies in the image of `φ` after restriction along a surjective
étale morphism `V ⟶ U`. Replacing `V` by the disjoint union of finitely many affine opens of `V`
whose images cover the quasi-compact scheme `U`, one may take `V` affine. Then `V` descends to a
scheme étale over a finite stage, the morphism `V ⟶ U` descends to a morphism over a later stage,
and its surjectivity descends to a still later stage.

The case of Freitag–Kiehl is the inverse image along `X ⟶ X_{i₀}` of the canonical morphism
`π₀ : H₀ ⟶ Coker(r₁, r₂)` onto the cokernel of a pair of morphisms of sheaves on `X_{i₀}`: the
cokernel of a pair is a coequalizer, hence `π₀` is an epimorphism, and the inverse image, being
a left adjoint, preserves epimorphisms. The image of `φ_V` is the value at `V` of the presheaf
image of `φ`.

## Main results

* `AlgebraicGeometry.exists_surjective_etale_stage_map_mem_range_of_epi`: the descent statement
  for an arbitrary epimorphism of sheaves of sets on the small étale site of the limit.
* `AlgebraicGeometry.exists_surjective_etale_stage_map_mem_range_inverseImage_pairCokernelπ`: the
  case of the inverse image of the projection onto the cokernel of a pair.

## Implementation notes

The projective system is a limit cone `c` of a cofiltered diagram `D : I ⥤ Scheme`, a later stage
`i₁ ≥ i₀` is a morphism `i₁ ⟶ i₀`, and base change of schemes étale over `Xᵢ` is
`Stacks.EtaleCohomology.smallEtaleBaseChange`. Freitag–Kiehl's noetherian separated schemes of
finite type over the stages are replaced by quasi-compact quasi-separated ones, and the
morphism `V ⟶ U` along which `s` is restricted is pinned down by its first projection: a morphism
into `U = U₀ ×_{X_{i₀}} X` over `X` is determined by its composite with the projection to `U₀`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, proof of I.4.17.
* [Stacks] Stacks Project, Tags 01ZM, 07RR.
-/

/- FK's statement is in its "presentation setting" with
noetherian separated schemes and Et(X); here it is stated on Mathlib's small étale site
`X.smallEtaleTopology` (where the epimorphism criterion
`AlgebraicGeometry.Scheme.epi_iff_forall_exists_surjective` lives), for qcqs schemes, and for an
arbitrary epimorphism; the presentation case is the second theorem. -/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Stacks.EtaleCohomology

namespace AlgebraicGeometry

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition morphisms, `U₀` a quasi-compact quasi-separated scheme étale over `X_{i₀}`, and
`φ : F ⟶ G` an epimorphism of sheaves of sets on the small étale site of `X`. For every section
`s` of `G` over `U = U₀ ×_{X_{i₀}} X` there are a stage `e : i₁ ⟶ i₀`, a scheme `V₁` étale over
`X_{i₁}` with a surjective morphism `g : V₁ ⟶ U₀ ×_{X_{i₀}} X_{i₁}` over `X_{i₁}`, and, with
`V = V₁ ×_{X_{i₁}} X` and `h : V ⟶ U` the base change of `g`, a section `t ∈ F(V)` with
`φ_V(t) = s|_V`. -/
@[weil "lem_fk104_section_locally_in_presheaf_image_descends"]
theorem exists_surjective_etale_stage_map_mem_range_of_epi
    [HasSheafify c.pt.smallEtaleTopology (Type w)]
    {F G : Sheaf c.pt.smallEtaleTopology (Type w)} (φ : F ⟶ G) [Epi φ]
    {i₀ : I} (U₀ : (D.obj i₀).Etale) [CompactSpace U₀.left] [QuasiSeparatedSpace U₀.left]
    (s : G.obj.obj (op ((smallEtaleBaseChange (c.π.app i₀)).obj U₀))) :
    ∃ (i₁ : I) (e : i₁ ⟶ i₀) (V₁ : (D.obj i₁).Etale)
      (g : V₁ ⟶ (smallEtaleBaseChange (D.map e)).obj U₀), Surjective g.left ∧
      ∃ h : (smallEtaleBaseChange (c.π.app i₁)).obj V₁ ⟶
          (smallEtaleBaseChange (c.π.app i₀)).obj U₀,
        h.left ≫ pullback.fst U₀.hom (c.π.app i₀) =
          pullback.fst V₁.hom (c.π.app i₁) ≫ g.left ≫ pullback.fst U₀.hom (D.map e) ∧
        ∃ t : F.obj.obj (op ((smallEtaleBaseChange (c.π.app i₁)).obj V₁)),
          φ.hom.app _ t = G.obj.map h.op s := by
  classical
  let U := (smallEtaleBaseChange (c.π.app i₀)).obj U₀
  -- `s` lies in the image of `φ` after restriction along a surjective étale `V ⟶ U`.
  obtain ⟨V, f, hf, t, ht⟩ := (Scheme.epi_iff_forall_exists_surjective φ).1 inferInstance U s
  -- `U` is quasi-compact.
  have : IsAffineHom (c.π.app i₀) := isAffineHom_π_app D c hc i₀
  have : QuasiCompact (c.π.app i₀) := inferInstance
  have : QuasiCompact (pullback.fst U₀.hom (c.π.app i₀)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip this
  have : CompactSpace ((𝟭 Scheme.{u}).obj U₀.left) := ‹CompactSpace U₀.left›
  have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj U₀.left) := ‹QuasiSeparatedSpace U₀.left›
  have hUc := QuasiCompact.compactSpace_of_compactSpace (pullback.fst U₀.hom (c.π.app i₀))
  have : CompactSpace U.left := hUc
  -- Finitely many affine opens of `V` whose images cover `U`.
  have h₁ : ∀ x : U.left, ∃ W : V.left.affineOpens,
      x ∈ Set.range ((W : V.left.Opens).ι ≫ f.left) := by
    intro x
    obtain ⟨y, rfl⟩ := hf.surj x
    obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ (⊤ : V.left.Opens) from trivial)
    obtain ⟨z, hz⟩ : y ∈ Set.range (W.ι) := by rw [Scheme.Opens.range_ι]; exact hyW
    exact ⟨⟨W, hW⟩, z, by rw [Scheme.Hom.comp_apply, hz]⟩
  choose W hW using h₁
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ Set.range ((W x : V.left.Opens).ι ≫ f.left))
    (fun x ↦ ((W x : V.left.Opens).ι ≫ f.left).isOpenMap.isOpen_range)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hW x⟩)
  let Wk (k : T) : c.pt.Etale := Scheme.Etale.mk ((W k.1 : V.left.Opens).ι ≫ V.hom)
  let incl (k : T) : Wk k ⟶ V := MorphismProperty.Over.homMk (W k.1 : V.left.Opens).ι rfl trivial
  let V' := Scheme.Etale.sigmaObj Wk
  let ρ : V' ⟶ V := Scheme.Etale.sigmaDesc incl
  have : ∀ k : T, IsAffine (Wk k).left := fun k ↦ (W k.1).2
  have : IsAffine V'.left := by
    rw [Scheme.Etale.sigmaObj_left]; infer_instance
  let f' : V' ⟶ U := ρ ≫ f
  have hf' : Surjective f'.left := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨k, hk, z, hz⟩ : ∃ k ∈ T, x ∈ Set.range ((W k : V.left.Opens).ι ≫ f.left) := by
      simpa using hT (Set.mem_univ x)
    refine ⟨Sigma.ι (fun k ↦ (Wk k).left) ⟨k, hk⟩ z, ?_⟩
    have hι : Sigma.ι (fun k ↦ (Wk k).left) ⟨k, hk⟩ ≫ f'.left =
        (W k : V.left.Opens).ι ≫ f.left := by
      change Sigma.ι (fun k ↦ (Wk k).left) ⟨k, hk⟩ ≫ (Sigma.desc fun k ↦ (incl k).left) ≫
        f.left = _
      rw [Sigma.ι_desc_assoc]
      rfl
    rw [← hz, ← hι]
    rfl
  let t' : F.obj.obj (op V') := F.obj.map ρ.op t
  have ht' : φ.hom.app _ t' = G.obj.map f'.op s := by
    simp only [t', f', op_comp, Functor.map_comp, types_comp_apply, ← ht]
    exact NatTrans.naturality_apply φ.hom ρ.op t
  -- Descend `V'` to a scheme `Y` étale over a stage `X_j`.
  let w : V'.left ⟶ U₀.left := f'.left ≫ pullback.fst U₀.hom (c.π.app i₀)
  have hw : w ≫ U₀.hom = V'.hom ≫ c.π.app i₀ := by
    have h1 : f'.left ≫ U.hom = V'.hom := MorphismProperty.Over.w f'
    change (f'.left ≫ pullback.fst U₀.hom (c.π.app i₀)) ≫ U₀.hom = V'.hom ≫ c.π.app i₀
    exact (Category.assoc _ _ _).trans ((congrArg (f'.left ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ c.π.app i₀) h1)))
  have : IsAffine ((𝟭 Scheme.{u}).obj V'.left) := ‹IsAffine V'.left›
  obtain ⟨j, ej, Y, p, θ, hp, hYc, hYq, hθ⟩ :=
    exists_isPullback_etale_of_isLimit_of_hom D c hc U₀.hom V'.hom w hw
  -- Descend the morphism `V' ⟶ U` to a stage `X_l`.
  obtain ⟨l, b, g, hg₁, hg₂⟩ :=
    exists_hom_of_isPullback_of_isLimit' D c hc ej hθ U₀.hom w hw
  have hl := isPullback_lift_of_isPullback D c hθ b
  have : Etale p := hp
  have : CompactSpace Y := hYc
  have : QuasiSeparatedSpace Y := hYq
  let E : l ⟶ i₀ := b ≫ ej
  let q : pullback p (D.map b) ⟶ D.obj l := pullback.snd p (D.map b)
  have hgE : g ≫ U₀.hom = q ≫ D.map E := by
    rw [hg₂, Functor.map_comp, ← Category.assoc, pullback.condition, Category.assoc]
  let γ : pullback p (D.map b) ⟶ pullback U₀.hom (D.map E) := pullback.lift g q hgE
  -- `γ` becomes surjective at a later stage.
  let X₀ : Over (D.obj l) := Over.mk q
  let Y₀ : Over (D.obj l) := Over.mk (pullback.snd U₀.hom (D.map E))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk γ (pullback.lift_snd _ _ _)
  have : QuasiCompact (pullback.fst p (D.map b)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : QuasiSeparated (pullback.fst p (D.map b)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : QuasiCompact (pullback.fst U₀.hom (D.map E)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : QuasiSeparated (pullback.fst U₀.hom (D.map E)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : CompactSpace X₀.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (D.map b))
  have : QuasiSeparatedSpace X₀.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (D.map b))
  have : CompactSpace Y₀.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst U₀.hom (D.map E))
  have : QuasiSeparatedSpace Y₀.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst U₀.hom (D.map E))
  have : Etale (γ ≫ pullback.snd U₀.hom (D.map E)) := by
    rw [pullback.lift_snd]; infer_instance
  have : Etale γ := Etale.of_comp γ (pullback.snd U₀.hom (D.map E))
  have : LocallyOfFinitePresentation f₀.left := inferInstanceAs (LocallyOfFinitePresentation γ)
  have hπl : c.π.app l ≫ D.map E = c.π.app i₀ := c.w E
  let eU : pullback (pullback.snd U₀.hom (D.map E)) (c.π.app l) ≅
      pullback U₀.hom (c.π.app i₀) :=
    pullbackLeftPullbackSndIso U₀.hom (D.map E) (c.π.app l) ≪≫ pullback.congrHom rfl hπl
  let Q := ((Over.pullback (c.π.app l)).map f₀).left
  have hQf : Q ≫ pullback.fst (pullback.snd U₀.hom (D.map E)) (c.π.app l) =
      pullback.fst q (c.π.app l) ≫ γ := overPullback_map_left_fst _ f₀
  have hQs : Q ≫ pullback.snd (pullback.snd U₀.hom (D.map E)) (c.π.app l) =
      pullback.snd q (c.π.app l) := overPullback_map_left_snd _ f₀
  have key : hl.isoPullback.hom ≫ Q ≫ eU.hom = f'.left := by
    apply pullback.hom_ext
    · simp only [eU, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
        Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
      rw [reassoc_of% hQf, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc, hg₁]
      rfl
    · simp only [eU, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
        Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
      rw [hQs, IsPullback.isoPullback_hom_snd]
      exact (MorphismProperty.Over.w f').symm
  have : Surjective f'.left := hf'
  have : Surjective Q := by
    have hQ : Q = hl.isoPullback.inv ≫ f'.left ≫ eU.inv := by
      exact (Iso.eq_inv_comp _).2 ((Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans key))
    rw [hQ]
    exact ⟨(eU.inv.surjective.comp f'.left.surjective).comp hl.isoPullback.inv.surjective⟩
  have : Surjective ((Over.pullback (c.π.app l)).map f₀).left := ‹Surjective Q›
  obtain ⟨m, g', hm⟩ :=
    exists_surjective_baseChange_of_surjective_limitBaseChange D c hc l X₀ Y₀ f₀
  -- The stage `X_m`, the scheme `V₁` étale over it and the morphism `V₁ ⟶ U₀ ×_{X_{i₀}} X_m`.
  let q₁ : pullback q (D.map g') ⟶ D.obj m := pullback.snd q (D.map g')
  have : Etale q := inferInstanceAs (Etale (pullback.snd p (D.map b)))
  let V₁ : (D.obj m).Etale := Scheme.Etale.mk q₁
  have hcond : (pullback.fst q (D.map g') ≫ g) ≫ U₀.hom = q₁ ≫ D.map (g' ≫ E) := by
    rw [Category.assoc, hgE, ← Category.assoc, pullback.condition, Category.assoc,
      ← Functor.map_comp]
  let gfin : V₁ ⟶ (smallEtaleBaseChange (D.map (g' ≫ E))).obj U₀ :=
    MorphismProperty.Over.homMk (pullback.lift (pullback.fst q (D.map g') ≫ g) q₁ hcond)
      (pullback.lift_snd _ _ _) trivial
  let M := ((Over.pullback (D.map g')).map f₀).left
  have hMf : M ≫ pullback.fst (pullback.snd U₀.hom (D.map E)) (D.map g') =
      pullback.fst q (D.map g') ≫ γ := overPullback_map_left_fst _ f₀
  have hMs : M ≫ pullback.snd (pullback.snd U₀.hom (D.map E)) (D.map g') =
      pullback.snd q (D.map g') := overPullback_map_left_snd _ f₀
  let eU' : pullback (pullback.snd U₀.hom (D.map E)) (D.map g') ≅
      pullback U₀.hom (D.map (g' ≫ E)) :=
    pullbackLeftPullbackSndIso U₀.hom (D.map E) (D.map g') ≪≫
      pullback.congrHom rfl (D.map_comp g' E).symm
  have hgfin : pullback.lift (pullback.fst q (D.map g') ≫ g) q₁ hcond = M ≫ eU'.hom := by
    apply pullback.hom_ext
    · simp only [eU', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_fst,
        Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
      rw [reassoc_of% hMf, pullback.lift_fst]
    · simp only [eU', Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.lift_snd,
        Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
      rw [hMs]
  have : Surjective M := hm
  have hsurj : Surjective gfin.left := by
    change Surjective (pullback.lift (pullback.fst q (D.map g') ≫ g) q₁ hcond)
    rw [hgfin]
    exact ⟨eU'.hom.surjective.comp M.surjective⟩
  -- The morphism `V₁ ×_{X_m} X ⟶ V'` and the restriction of `t'`.
  have hrc : (pullback.fst q₁ (c.π.app m) ≫ pullback.fst q (D.map g')) ≫ q =
      pullback.snd q₁ (c.π.app m) ≫ c.π.app l := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, c.w g']
  let r : (smallEtaleBaseChange (c.π.app m)).obj V₁ ⟶ V' :=
    MorphismProperty.Over.homMk (hl.lift _ _ hrc) (hl.lift_snd _ _ _) trivial
  refine ⟨m, g' ≫ E, V₁, gfin, hsurj, r ≫ f', ?_, F.obj.map r.op t', ?_⟩
  · change hl.lift _ _ hrc ≫ f'.left ≫ pullback.fst U₀.hom (c.π.app i₀) =
      pullback.fst q₁ (c.π.app m) ≫ gfin.left ≫ pullback.fst U₀.hom (D.map (g' ≫ E))
    change hl.lift _ _ hrc ≫ w = _
    rw [← hg₁, hl.lift_fst_assoc]
    erw [pullback.lift_fst]
    rw [Category.assoc]
    rfl
  · rw [NatTrans.naturality_apply φ.hom r.op t', ht']
    simp only [f', op_comp, Functor.map_comp]
    rfl

include hc in
/-- The presentation case: let `r₁, r₂ : R ⟶ H` be morphisms of sheaves of sets on the small
étale site of `X_{i₀}`, `π₀ : H ⟶ Coker(r₁, r₂)` the projection onto their cokernel, and `π` its
inverse image along `X ⟶ X_{i₀}`. For every section `s` of the inverse image of the cokernel over
`U = U₀ ×_{X_{i₀}} X` there are a stage `e : i₁ ⟶ i₀`, a surjective morphism
`g : V₁ ⟶ U₀ ×_{X_{i₀}} X_{i₁}` of schemes étale over `X_{i₁}` and, with `V = V₁ ×_{X_{i₁}} X`
and `h : V ⟶ U` the base change of `g`, the restriction `s|_V` lies in the image of `π_V`. -/
@[weil "lem_fk104_section_locally_in_presheaf_image_descends"]
theorem exists_surjective_etale_stage_map_mem_range_inverseImage_pairCokernelπ {i₀ : I}
    {R H : Sheaf (D.obj i₀).smallEtaleTopology (Type (max (u + 1) v))} (r₁ r₂ : R ⟶ H)
    (U₀ : (D.obj i₀).Etale) [CompactSpace U₀.left] [QuasiSeparatedSpace U₀.left]
    (s : ((smallEtaleInverseImage.{u, v} (c.π.app i₀)).obj (Sheaf.pairCokernel r₁ r₂)).obj.obj
      (op ((smallEtaleBaseChange (c.π.app i₀)).obj U₀))) :
    ∃ (i₁ : I) (e : i₁ ⟶ i₀) (V₁ : (D.obj i₁).Etale)
      (g : V₁ ⟶ (smallEtaleBaseChange (D.map e)).obj U₀), Surjective g.left ∧
      ∃ h : (smallEtaleBaseChange (c.π.app i₁)).obj V₁ ⟶
          (smallEtaleBaseChange (c.π.app i₀)).obj U₀,
        h.left ≫ pullback.fst U₀.hom (c.π.app i₀) =
          pullback.fst V₁.hom (c.π.app i₁) ≫ g.left ≫ pullback.fst U₀.hom (D.map e) ∧
        ∃ t : ((smallEtaleInverseImage.{u, v} (c.π.app i₀)).obj H).obj.obj
            (op ((smallEtaleBaseChange (c.π.app i₁)).obj V₁)),
          ((smallEtaleInverseImage.{u, v} (c.π.app i₀)).map
            (Sheaf.pairCokernelπ r₁ r₂)).hom.app _ t =
            ((smallEtaleInverseImage.{u, v} (c.π.app i₀)).obj
              (Sheaf.pairCokernel r₁ r₂)).obj.map h.op s := by
  have : Epi (Sheaf.pairCokernelπ r₁ r₂) :=
    epi_of_isColimit_cofork (Sheaf.isColimitPairCokernelCofork r₁ r₂)
  have := (smallEtaleInverseImageAdjunction.{u, v} (c.π.app i₀)).isLeftAdjoint
  exact exists_surjective_etale_stage_map_mem_range_of_epi D c hc _ U₀ s

end AlgebraicGeometry
