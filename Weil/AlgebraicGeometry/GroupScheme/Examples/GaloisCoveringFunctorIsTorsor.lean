module

public import Weil.Attr
public import Weil.AlgebraicGeometry.GroupScheme.Examples.GaloisCoveringSpace
public import Weil.AlgebraicGeometry.Sites.Bridges.EtaleSheafCondition

/-!
# The functor of points of a Galois covering space is a torsor

Let `X` be a scheme, `F` a group and `X'` an `F`-Galois covering space of `X`, with action
`τ ↦ a_τ`: the morphism `X' → X` is étale and surjective and
`γ : ∐_{τ ∈ F} X' → X' ×_X X'`, `x' ↦ (a_τ x', x')` on the copy indexed by `τ`, is an
isomorphism. Then the presheaf `h_{X'} : U ↦ Hom_X(U, X')` on the étale category `Et(X)`, with
the right action `t ↦ t ^ σ` of the constant sheaf of groups `F_X` induced by the action on `X'`,
is an `F_X`-torsor:

* it is formally principal: for sections `s, t` of `h_{X'}` over `U` there is a unique locally
  constant `σ : |U| → F` with `t ^ σ = s`. The section `σ` is read off from the morphism
  `γ⁻¹ ∘ (s, t) : U → ∐_{τ ∈ F} X'`: its value at `u` is the inverse of the index of the copy
  containing the image of `u`;
* it has sections locally: every object `U` of `Et(X)` is covered by the affine opens of
  `U ×_X X'`, over which `h_{X'}` has the second projection as a section.

If moreover `F` is finite and `X` is noetherian and separated, then `X'` is an object of `Et(X)`:
it is noetherian, because `X'` is the union of the finitely many quasi-compact subsets `a_τ(W)`
for `W` in a finite family of affine opens whose images cover `X`; and it is separated, because
the diagonal of `X' → X` is `γ` composed with the inclusion of the copy indexed by `1`, which is
open and closed.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.representableRightAction` — the sheaf `h_{X'}`
  on `Et(X)` with the right action of `F_X` induced by an action of `F` on the `X`-scheme `X'`.
* `AlgebraicGeometry.IsGaloisCovering.toEt` — a Galois covering space with finite group of a
  noetherian separated scheme `X`, as an object of `Et(X)`.

## Main results

* `AlgebraicGeometry.IsGaloisCovering.isNoetherian_left`,
  `AlgebraicGeometry.IsGaloisCovering.isSeparated_hom` — the source of a Galois covering space
  with finite group of a noetherian scheme is noetherian, and the covering map is separated.
* `AlgebraicGeometry.IsGaloisCovering.isFormallyPrincipal_representableRightAction` — `h_{X'}`
  with the induced right action is formally principal.
* `AlgebraicGeometry.IsGaloisCovering.isTorsor_representableRightAction` — it is an
  `F_X`-torsor.

## Implementation notes

The torsor is stated for an arbitrary `X`-scheme `X'`, not only for objects of `Et(X)`: the
presheaf `h_{X'}` is defined on `Et(X)` for every `X`-scheme. The torsor statements need
neither `F` finite nor `X` noetherian beyond the local noetherianity under which `Et(X)` carries
its topology; finiteness of `F` and `X` noetherian and separated are used only to place `X'` in
`Et(X)`. The torsor condition is that of `PseudoTorsor.IsTorsor`, a covering of every object of
`Et(X)` on whose members `h_{X'}` has sections.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

namespace IsGaloisCovering

variable {X : Scheme.{u}} {F : Type u} [Group F] {Y : Over X} {ρ : F →* Aut Y}

omit [Group F] in
/-- The index of the copy of `∐_{τ ∈ F} Y` containing a point. -/
def sigmaIndex (z : (∐ fun _ : F ↦ Y.left : Scheme.{u})) : F :=
  ((sigmaMk fun _ : F ↦ Y.left).symm z).1

omit [Group F] in
lemma sigmaIndex_ι (τ : F) (y : Y.left) :
    sigmaIndex (Y := Y) (Sigma.ι (fun _ : F ↦ Y.left) τ y) = τ := by
  rw [sigmaIndex, ← sigmaMk_mk, Homeomorph.symm_apply_apply]

omit [Group F] in
lemma ι_sigmaIndex (z : (∐ fun _ : F ↦ Y.left : Scheme.{u})) :
    Sigma.ι (fun _ : F ↦ Y.left) (sigmaIndex z) ((sigmaMk fun _ : F ↦ Y.left).symm z).2 = z := by
  rw [sigmaIndex, ← sigmaMk_mk, Sigma.eta, Homeomorph.apply_symm_apply]

/-- Two points of `X'` with the same image in `X` differ by the action of an element of `F`. -/
lemma exists_smul_eq (h : IsGaloisCovering Y ρ) {x y : Y.left} (hxy : Y.hom x = Y.hom y) :
    ∃ σ : F, (ρ σ).hom.left y = x := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  have := h.isIso_galoisCoveringMap
  obtain ⟨w, rfl⟩ : ∃ w, (galoisCoveringMap Y ρ) w = z :=
    ⟨(inv (galoisCoveringMap Y ρ)) z, by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rw [← ι_sigmaIndex w] at hz1 hz2
  refine ⟨sigmaIndex w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ι_galoisCoveringMap_snd] at hz2
  change ((sigmaMk fun _ : F ↦ Y.left).symm w).snd = y at hz2
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ι_galoisCoveringMap_fst] at hz1
  rw [← hz2]
  exact hz1

/-- **The source of a Galois covering space with finite group is quasi-compact** when the base
is: it is the union of the translates `a_τ(W)` of finitely many affine opens `W` whose images
cover the base. -/
lemma compactSpace_left [Finite F] [CompactSpace X] (h : IsGaloisCovering Y ρ) :
    CompactSpace Y.left := by
  have := h.etale
  have hopen : IsOpenMap Y.hom := Y.hom.isOpenMap
  choose W hW hxW using fun x : Y.left ↦
    exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) (by simp)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : Y.left ↦ Y.hom '' (W x))
    (fun x ↦ hopen _ (W x).isOpen) fun x _ ↦ by
      obtain ⟨y, rfl⟩ := h.surjective.surj x
      exact Set.mem_iUnion.mpr ⟨y, y, hxW y |>.1, rfl⟩
  refine isCompact_univ_iff.mp ?_
  have hcover : (Set.univ : Set Y.left) =
      ⋃ σ : F, ⋃ x ∈ t, (ρ σ).hom.left '' (W x) := by
    refine (Set.eq_univ_of_forall fun y ↦ ?_).symm
    obtain ⟨x, hx, w, hw, he⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (Y.hom y)))
    obtain ⟨σ, hσ⟩ := h.exists_smul_eq he.symm
    exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion₂.mpr ⟨x, hx, w, hw, hσ⟩⟩
  rw [hcover]
  exact isCompact_iUnion fun σ ↦ t.isCompact_biUnion fun x _ ↦
    ((hW x).isCompact).image (ρ σ).hom.left.continuous

/-- The source of a Galois covering space with finite group of a noetherian scheme is
noetherian. -/
lemma isNoetherian_left [Finite F] [IsNoetherian X] (h : IsGaloisCovering Y ρ) :
    IsNoetherian Y.left :=
  have := h.etale
  have := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have := h.compactSpace_left
  {}

/-- The diagonal of a Galois covering space `X' → X` is `γ` composed with the inclusion of the
copy indexed by `1`. -/
lemma diagonal_eq (ρ : F →* Aut Y) :
    pullback.diagonal Y.hom = Sigma.ι (fun _ : F ↦ Y.left) 1 ≫ galoisCoveringMap Y ρ := by
  apply pullback.hom_ext
  · simp [map_one]
    rfl
  · simp

/-- The structure morphism of a Galois covering space is separated. -/
lemma isSeparated_hom (h : IsGaloisCovering Y ρ) : IsSeparated Y.hom := by
  have := h.isIso_galoisCoveringMap
  have hcl : IsClosed (Set.range (Sigma.ι (fun _ : F ↦ Y.left) 1)) := by
    have : Set.range (Sigma.ι (fun _ : F ↦ Y.left) 1) =
        (sigmaMk fun _ : F ↦ Y.left) '' Set.range (Sigma.mk 1) := by
      ext z
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and, sigmaMk_mk]
    rw [this]
    exact (sigmaMk fun _ : F ↦ Y.left).isClosedMap _ isClosed_range_sigmaMk
  have : IsClosedImmersion (Sigma.ι (fun _ : F ↦ Y.left) 1) := .of_isPreimmersion _ hcl
  refine ⟨?_⟩
  rw [diagonal_eq ρ]
  infer_instance

/-- The source of a Galois covering space of a separated scheme is separated. -/
lemma isSeparated_left [X.IsSeparated] (h : IsGaloisCovering Y ρ) : Y.left.IsSeparated := by
  have := h.isSeparated_hom
  exact ⟨by rw [← terminal.comp_from Y.hom]; infer_instance⟩

end IsGaloisCovering

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) [IsLocallyNoetherian X]
  {F : Type u} [Group F]

/-- **The sheaf `h_{X'}` with the induced right action of `F_X`.** For an action `ρ` of a group
`F` on an `X`-scheme `X'` by `X`-automorphisms, the sheaf `U ↦ Hom_X(U, X')` on `Et(X)` with the
right action `t ↦ t ^ σ` of the sections of the constant sheaf of groups `F_X`
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale.inducedMulAction`). -/
@[weil "lem_fk102_galois_covering_functor_is_torsor"]
def representableRightAction (X' : Over X) (ρ : F →* Aut X') :
    SheafOfGroups.RightAction (locallyConstantSheafOfGroups B X hX F) where
  presheaf := representablePresheaf B X hX X'
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).mpr (representablePresheaf.isSheaf_topology X')
  act U t σ := Over.locallyConstantSMul (U := (toOver B X hX).obj U.unop) ρ σ t
  act_one U t := (Over.locallyConstantMulAction (U := (toOver B X hX).obj U.unop) ρ).one_smul t
  act_mul U t σ τ := (Over.locallyConstantMulAction (U := (toOver B X hX).obj U.unop) ρ).mul_smul
    (MulOpposite.op τ) (MulOpposite.op σ) t
  naturality f t σ := inducedMulAction_map ρ f.unop σ t

variable {B hX}

lemma representableRightAction_act (X' : Over X) (ρ : F →* Aut X')
    (U : (SmallNoetherianSeparatedEtale B X hX)ᵒᵖ)
    (t : (representableRightAction B hX X' ρ).presheaf.obj U)
    (σ : (locallyConstantSheafOfGroups B X hX F).presheaf.obj U) :
    (representableRightAction B hX X' ρ).act U t σ =
      Over.locallyConstantSMul (U := (toOver B X hX).obj U.unop) ρ σ t :=
  rfl

end SmallNoetherianSeparatedEtale

namespace IsGaloisCovering

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {F : Type u} [Group F]
  {Y : Over X} {ρ : F →* Aut Y}

/-- The morphism `U → X' ×_X X'` given by two `X`-morphisms `s, t : U → X'`. -/
abbrev pairHom {U : Over X} (s t : U ⟶ Y) : U.left ⟶ pullback Y.hom Y.hom :=
  pullback.lift s.left t.left (by rw [Over.w s, Over.w t])

/-- The inverse `γ⁻¹ : X' ×_X X' → ∐_{τ ∈ F} X'` of the defining isomorphism of a Galois
covering space. -/
def galoisCoveringInv (h : IsGaloisCovering Y ρ) :
    pullback Y.hom Y.hom ⟶ ∐ fun _ : F ↦ Y.left :=
  haveI := h.isIso_galoisCoveringMap
  inv (galoisCoveringMap Y ρ)

@[reassoc (attr := simp)]
lemma galoisCoveringMap_galoisCoveringInv (h : IsGaloisCovering Y ρ) :
    galoisCoveringMap Y ρ ≫ h.galoisCoveringInv = 𝟙 _ := by
  have := h.isIso_galoisCoveringMap
  exact IsIso.hom_inv_id _

@[reassoc (attr := simp)]
lemma galoisCoveringInv_galoisCoveringMap (h : IsGaloisCovering Y ρ) :
    h.galoisCoveringInv ≫ galoisCoveringMap Y ρ = 𝟙 _ := by
  have := h.isIso_galoisCoveringMap
  exact IsIso.inv_hom_id _

/-- If `s = t ≫ a_{τ⁻¹}` on an open subset `W` of `U`, then `(s, t) = γ ∘ ι_{τ⁻¹} ∘ t` on `W`. -/
lemma ι_pairHom_eq {U : Over X} (s t : U ⟶ Y) (W : U.left.Opens) (τ : F)
    (hW : W.ι ≫ s.left = W.ι ≫ t.left ≫ (ρ τ⁻¹).hom.left) :
    W.ι ≫ pairHom s t =
      W.ι ≫ t.left ≫ Sigma.ι (fun _ : F ↦ Y.left) τ⁻¹ ≫ galoisCoveringMap Y ρ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pairHom, pullback.lift_fst, ι_galoisCoveringMap_fst, hW]
  · simp only [Category.assoc, pairHom, pullback.lift_snd, ι_galoisCoveringMap_snd,
      Category.comp_id]

/-- **The index read off from `γ⁻¹ ∘ (s, t)`.** If `t ^ σ = s`, then at every point `u` of `U`
the image of `u` under `γ⁻¹ ∘ (s, t)` lies in the copy indexed by `σ(u)⁻¹`. -/
lemma sigmaIndex_galoisCoveringInv_pairHom (h : IsGaloisCovering Y ρ) {U : Over X}
    (s t : U ⟶ Y) (σ : LocallyConstant U.left F) (hσ : Over.locallyConstantSMul ρ σ t = s)
    (u : U.left) :
    sigmaIndex (Y := Y) (h.galoisCoveringInv (pairHom s t u)) = (σ u)⁻¹ := by
  let W := fiberOpen F σ (σ u)
  have hW : W.ι ≫ s.left = W.ι ≫ t.left ≫ (ρ (σ u)⁻¹).hom.left := by
    rw [← hσ]
    exact Scheme.ι_fiberOpen_twistByLocallyConstant _ σ t.left (σ u)
  have hu : u ∈ W := rfl
  have e := congrArg (fun φ ↦ (φ ≫ h.galoisCoveringInv) (⟨u, hu⟩ : W))
    (ι_pairHom_eq (ρ := ρ) s t W (σ u) hW)
  simp only [Category.assoc, galoisCoveringMap_galoisCoveringInv, Category.comp_id] at e
  change h.galoisCoveringInv (pairHom s t u) = Sigma.ι (fun _ : F ↦ Y.left) (σ u)⁻¹ (t.left u)
    at e
  rw [e, sigmaIndex_ι]

/-- The points of `U` over which `γ⁻¹ ∘ (s, t)` lands in the copy indexed by `τ⁻¹`. -/
lemma setOf_sigmaIndex_inv_eq (h : IsGaloisCovering Y ρ) {U : Over X} (s t : U ⟶ Y) (τ : F) :
    {u : U.left | (sigmaIndex (Y := Y) (h.galoisCoveringInv (pairHom s t u)))⁻¹ = τ} =
      (pairHom s t ≫ h.galoisCoveringInv) ⁻¹' Set.range (Sigma.ι (fun _ : F ↦ Y.left) τ⁻¹) := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Scheme.Hom.comp_apply, Set.mem_range]
  constructor
  · intro hu
    refine ⟨((sigmaMk _).symm (h.galoisCoveringInv (pairHom s t u))).2, ?_⟩
    rw [← hu, inv_inv]
    exact ι_sigmaIndex _
  · rintro ⟨y, hy⟩
    rw [← hy, sigmaIndex_ι, inv_inv]

/-- The locally constant map `|U| → F`, `u ↦ (index of γ⁻¹(s(u), t(u)))⁻¹`: the unique `σ` with
`t ^ σ = s`. -/
def quotientSection (h : IsGaloisCovering Y ρ) {U : Over X} (s t : U ⟶ Y) :
    LocallyConstant U.left F where
  toFun u := (sigmaIndex (Y := Y) (h.galoisCoveringInv (pairHom s t u)))⁻¹
  isLocallyConstant := by
    refine IsLocallyConstant.iff_isOpen_fiber.mpr fun τ ↦ ?_
    change IsOpen {u : U.left |
      (sigmaIndex (Y := Y) (h.galoisCoveringInv (pairHom s t u)))⁻¹ = τ}
    rw [setOf_sigmaIndex_inv_eq]
    exact (Sigma.ι (fun _ : F ↦ Y.left) τ⁻¹).isOpenEmbedding.isOpen_range.preimage
      (pairHom s t ≫ h.galoisCoveringInv).continuous

lemma quotientSection_apply (h : IsGaloisCovering Y ρ) {U : Over X} (s t : U ⟶ Y)
    (u : U.left) :
    h.quotientSection s t u = (sigmaIndex (Y := Y) (h.galoisCoveringInv (pairHom s t u)))⁻¹ :=
  rfl

lemma locallyConstantSMul_quotientSection (h : IsGaloisCovering Y ρ) {U : Over X}
    (s t : U ⟶ Y) : Over.locallyConstantSMul ρ (h.quotientSection s t) t = s := by
  ext1
  refine Scheme.hom_ext_of_forall _ _ fun x ↦
    ⟨fiberOpen F (h.quotientSection s t) (h.quotientSection s t x), rfl, ?_⟩
  set τ := h.quotientSection s t x
  set W := fiberOpen F (h.quotientSection s t) τ
  rw [Over.locallyConstantSMul_left, Scheme.ι_fiberOpen_twistByLocallyConstant]
  have hrange : Set.range (W.ι ≫ pairHom s t ≫ h.galoisCoveringInv) ⊆
      Set.range (Sigma.ι (fun _ : F ↦ Y.left) τ⁻¹) := by
    rintro _ ⟨w, rfl⟩
    have hw : W.ι w ∈ {u : U.left |
        (sigmaIndex (Y := Y) (h.galoisCoveringInv (pairHom s t u)))⁻¹ = τ} := w.2
    rw [setOf_sigmaIndex_inv_eq, Set.mem_preimage, Scheme.Hom.comp_apply] at hw
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact hw
  set q := IsOpenImmersion.lift (Sigma.ι (fun _ : F ↦ Y.left) τ⁻¹) _ hrange
  have hq : W.ι ≫ pairHom s t = q ≫ Sigma.ι (fun _ : F ↦ Y.left) τ⁻¹ ≫
      galoisCoveringMap Y ρ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    simp
  have h1 := congrArg (· ≫ pullback.fst Y.hom Y.hom) hq
  have h2 := congrArg (· ≫ pullback.snd Y.hom Y.hom) hq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, ι_galoisCoveringMap_fst,
    ι_galoisCoveringMap_snd, Category.comp_id] at h1 h2
  rw [h1, ← Category.assoc, h2]

/-- **`h_{X'}` is formally principal.** For an `F`-Galois covering space `X'` of `X`, the sheaf
`h_{X'}` on `Et(X)` with the right action of `F_X` induced by the action of `F` on `X'` is
formally principal. -/
@[weil "lem_fk102_galois_covering_functor_is_torsor"]
theorem isFormallyPrincipal_representableRightAction [IsLocallyNoetherian X]
    (h : IsGaloisCovering Y ρ) :
    (representableRightAction B hX Y ρ).IsFormallyPrincipal := by
  rw [SheafOfGroups.RightAction.isFormallyPrincipal_iff]
  intro U (s : (toOver B X hX).obj U.unop ⟶ Y) (t : (toOver B X hX).obj U.unop ⟶ Y)
  refine ⟨h.quotientSection (U := (toOver B X hX).obj U.unop) s t,
    h.locallyConstantSMul_quotientSection _ _, fun σ hσ ↦ ?_⟩
  obtain ⟨σ', rfl⟩ : ∃ σ' : LocallyConstant ((toOver B X hX).obj U.unop).left F, σ' = σ :=
    ⟨σ, rfl⟩
  refine LocallyConstant.ext fun u ↦ ?_
  rw [quotientSection_apply,
    h.sigmaIndex_galoisCoveringInv_pairHom (U := (toOver B X hX).obj U.unop) s t σ' hσ u,
    inv_inv]

/-- **The functor of points of a Galois covering space is a torsor.** For an `F`-Galois covering
space `X'` of `X`, the sheaf `h_{X'}` on `Et(X)` with the right action of `F_X` induced by the
action of `F` on `X'` is an `F_X`-torsor. -/
@[weil "lem_fk102_galois_covering_functor_is_torsor"]
theorem isTorsor_representableRightAction [IsLocallyNoetherian X]
    (h : IsGaloisCovering Y ρ) :
    ((representableRightAction B hX Y ρ).toPseudoTorsor
      h.isFormallyPrincipal_representableRightAction).IsTorsor := by
  intro U
  refine ⟨⟨fun V _ ↦ Nonempty ((toOver B X hX).obj V ⟶ Y),
    fun {V W} f ⟨t⟩ g ↦ ⟨(toOver B X hX).map g ≫ t⟩⟩, ?_, fun V f hf ↦ hf⟩
  rw [mem_topology_iff]
  intro x
  have := h.etale
  obtain ⟨y, hy⟩ := h.surjective.surj (structureMorphism U x)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := structureMorphism U)
    (g := Y.hom) x y hy.symm
  obtain ⟨R, j, _, ⟨w, rfl⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := z) (U := ⊤) (by simp)
  let v := j ≫ pullback.fst (structureMorphism U) Y.hom ≫ structureMorphism U
  have hR : B.Contains (Spec R) := (Scheme.size_le_of_locallyOfFiniteType v).trans_lt hX
  have : IsLocallyNoetherian (Spec R) := LocallyOfFiniteType.isLocallyNoetherian v
  have : IsNoetherian (Spec R) := {}
  let V : SmallNoetherianSeparatedEtale B X hX := SmallNoetherianSeparatedEtale.mk (Spec R) hR v
  let f : V ⟶ U := (homEquiv V U).symm ⟨j ≫ pullback.fst _ _,
    (Category.assoc _ _ _).trans rfl⟩
  refine ⟨V, f, ⟨Over.homMk (U := (toOver B X hX).obj V) (j ≫ pullback.snd _ _) ?_⟩, w, ?_⟩
  · change (j ≫ pullback.snd _ _) ≫ Y.hom = v
    simp [v, pullback.condition]
  · change (j ≫ pullback.fst _ _) w = x
    rw [Scheme.Hom.comp_apply, hz]

variable (B hX) in
/-- **A Galois covering space with finite group is an object of `Et(X)`.** For `X` noetherian
and separated and `F` finite, an `F`-Galois covering space `X'` of `X` is an object of the étale
category `Et(X)`. -/
@[weil "lem_fk102_galois_covering_functor_is_torsor"]
def toEt [Finite F] [IsNoetherian X] [X.IsSeparated] (h : IsGaloisCovering Y ρ) :
    SmallNoetherianSeparatedEtale B X hX :=
  have := h.etale
  have := h.isNoetherian_left
  have := h.isSeparated_left
  SmallNoetherianSeparatedEtale.mk Y.left
    ((Scheme.size_le_of_locallyOfFiniteType Y.hom).trans_lt hX) Y.hom

@[simp]
lemma toOver_obj_toEt [Finite F] [IsNoetherian X] [X.IsSeparated] (h : IsGaloisCovering Y ρ) :
    (toOver B X hX).obj (h.toEt B hX) = Y :=
  rfl

end IsGaloisCovering

end AlgebraicGeometry

end
