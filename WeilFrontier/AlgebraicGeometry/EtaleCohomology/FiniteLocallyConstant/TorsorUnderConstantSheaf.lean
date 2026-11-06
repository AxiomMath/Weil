module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RepresentabilityDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SliceConstantSheaf
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafIsSheafification
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.InducedActionOnPoints
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtaleFibreProductInEt
public import Weil.Attr

/-!
# Torsors under a finite constant sheaf of groups are representable

Let `X` be a noetherian separated scheme, `F` a finite group and `F_X` the constant sheaf of
groups on the étale category `Et(X)` (locally constant maps `|U| → F`). Let `𝒢` be an
`F_X`-torsor: a sheaf of sets with a right action `(t, σ) ↦ t ^ σ` of `F_X` which is formally
principal (`F_X × 𝒢 → 𝒢 × 𝒢`, `(σ, t) ↦ (t ^ σ, t)` is an isomorphism), and which has a section
over every member of some étale covering `(V_i → X)`. Then there are an object `X'` of `Et(X)`,
whose structure morphism `X' → X` is étale and finite (in particular affine), an action
`τ ↦ a_τ` of `F` on `X'` by `X`-automorphisms, and an isomorphism of sheaves of sets
`θ : h_{X'} ≅ 𝒢` with `θ(t ^ σ) = θ(t) ^ σ` for the induced right action of `F_X` on `h_{X'}`.

The proof has three steps.

1. *Local triviality.* Over an object `V` of `Et(X)` carrying a section `s` of `𝒢`, the map
   `σ ↦ s|_W ^ σ` identifies the sheaf `F_X` of locally constant maps with `𝒢` on `Et(X)/V`;
   since `F_X` is the sheafification of the constant presheaf `F`, `𝒢|_V` is the constant sheaf
   with value `F`. The objects `U ×_X V_i` cover any `U`, so `𝒢` is finite locally constant.
2. *Representability.* Restriction along the dense subsite `Et(X) ⊆ SmallEtale X` preserves and
   reflects finite local constancy, and a finite locally constant sheaf of sets on the small étale
   site is represented by a scheme finite étale over `X` (Stacks 03RV). A scheme finite over the
   noetherian separated `X` is noetherian and separated, hence an object `X'` of `Et(X)`.
3. *The action.* The automorphism `g ↦ g ^ τ⁻¹` of `𝒢` (for the constant section `τ`) becomes,
   through `θ`, an automorphism of `h_{X'}`, which by the Yoneda lemma is postcomposition with an
   `X`-automorphism `a_τ` of `X'`. Then `θ(t ^ σ)` and `θ(t) ^ σ` agree on each member of a
   covering on which `σ` is constant, hence agree.

## Main results

In the namespace `AlgebraicGeometry.SmallNoetherianSeparatedEtale`:

* `exists_iso_representablePresheaf_of_isFormallyPrincipal`: an `F_X`-torsor is represented,
  equivariantly, by an object of `Et(X)` finite over `X`.
* `TorsorRepresentable.isFiniteLocallyConstant_uliftSheaf`: an `F_X`-torsor is a finite locally
  constant sheaf.

## Implementation notes

Freitag–Kiehl prove the statement by étale descent of the scheme `F_X × T` along the étale
surjection `T = ⨆ V_i → X`. Here the descent is the one already carried out in Stacks 03RV
(`Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable`), applied to the
sheaf of sets underlying `𝒢`; it gives a representing scheme finite over `X`, which is stronger
than the affineness asked for. That result is stated for sheaves with values in `Type (u + 1)` on
the small étale site, so `𝒢` is lifted along `uliftFunctor` and transported along
`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`; the resulting isomorphism descends
to `θ` because `uliftFunctor` is fully faithful.

The covering in the hypothesis is FK's étale covering of `X` by objects of `Et(X)`
(`AlgebraicGeometry.Scheme.IsEtaleCovering` of the structure morphisms).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2, proof of
  2.11][FreitagKiehl]
* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {F : Type u} [Group F]

namespace TorsorRepresentable

/-- For an object `X'` of `Et(X)`, the presheaf represented by `X'` in the small étale site,
restricted to `Et(X)`, is the presheaf represented by `X'` in `Et(X)`. -/
noncomputable def inclusionOpCompYonedaIso (X' : SmallNoetherianSeparatedEtale B X hX) :
    (inclusion B X hX).op ⋙ yoneda.obj ((inclusion B X hX).obj X') ≅ yoneda.obj X' :=
  have : ∀ W, IsIso ((yonedaMap (inclusion B X hX) X').app W) := fun _ ↦
    (isIso_iff_bijective _).mpr ((ObjectProperty.fullyFaithfulι _).map_bijective _ _)
  have : IsIso (yonedaMap (inclusion B X hX) X') := NatIso.isIso_of_isIso_app _
  (asIso (yonedaMap (inclusion B X hX) X')).symm

/-- An object of the small étale site finite over a noetherian separated scheme is noetherian and
separated, i.e. lies in `Et(X)`. -/
lemma isNoetherianSeparated_of_isFinite [IsNoetherian X] [X.IsSeparated] (U : SmallEtale B X hX)
    [IsFinite (B.inclusion.map U.obj.hom)] : SmallEtale.IsNoetherianSeparated B X hX U := by
  let p : (SmallEtale.toScheme B X hX).obj U ⟶ X := B.inclusion.map U.obj.hom
  have : IsFinite p := ‹_›
  have : IsLocallyNoetherian ((SmallEtale.toScheme B X hX).obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace ((SmallEtale.toScheme B X hX).obj U) :=
    QuasiCompact.compactSpace_of_compactSpace p
  refine ⟨{}, ⟨?_⟩⟩
  rw [← terminal.comp_from p]
  infer_instance

section LocallyNoetherian

variable [IsLocallyNoetherian X]
  (𝒢 : SheafOfGroups.RightAction (locallyConstantSheafOfGroups B X hX F))

/-- The sheaf `𝒢` with values lifted to `Type (u + 1)`. -/
noncomputable def uliftSheaf : Sheaf (topology B X hX) (Type (u + 1)) :=
  ⟨𝒢.presheaf ⋙ uliftFunctor.{u + 1}, (isSheaf_iff_isSheaf_of_type _ _).mpr
    (Presieve.isSheaf_comp_uliftFunctor _ ((isSheaf_iff_isSheaf_of_type _ _).mp 𝒢.isSheaf))⟩

variable {𝒢}

/-- The orbit map `σ ↦ s ^ σ` of a section `s` of a formally principal sheaf is bijective. -/
lemma bijective_act (h𝒢 : 𝒢.IsFormallyPrincipal) {U : (SmallNoetherianSeparatedEtale B X hX)ᵒᵖ}
    (s : 𝒢.presheaf.obj U) : Function.Bijective (𝒢.act U s) := by
  rw [SheafOfGroups.RightAction.isFormallyPrincipal_iff] at h𝒢
  refine ⟨fun σ τ hστ ↦ ?_, fun g ↦ (h𝒢 U g s).exists⟩
  obtain ⟨ρ, -, hρ⟩ := h𝒢 U (𝒢.act U s σ) s
  exact (hρ σ rfl).trans (hρ τ hστ.symm).symm

/-- Restricting `s|_W ^ σ` along a morphism `g : W' ⟶ W` over `V` gives `s|_{W'} ^ σ|_{W'}`. -/
lemma map_act_map_hom {V : SmallNoetherianSeparatedEtale B X hX} (s : 𝒢.presheaf.obj (op V))
    {W W' : Over V} (g : W' ⟶ W)
    (σ : (locallyConstantSheafOfGroups B X hX F).presheaf.obj (op W.left)) :
    𝒢.presheaf.map g.left.op (𝒢.act _ (𝒢.presheaf.map W.hom.op s) σ) =
      𝒢.act _ (𝒢.presheaf.map W'.hom.op s)
        ((locallyConstantSheafOfGroups B X hX F).presheaf.map g.left.op σ) := by
  rw [𝒢.naturality, ← Functor.map_comp_apply, ← op_comp, Over.w g]

variable (𝒢) in
/-- For a section `s` of a formally principal sheaf `𝒢` over `V`, the isomorphism of presheaves
on `Et(X)/V` from the locally constant `F`-valued maps to `𝒢`, `σ ↦ s|_W ^ σ` (values lifted to
`Type (u + 1)`). -/
noncomputable def orbitIso (h𝒢 : 𝒢.IsFormallyPrincipal) (V : SmallNoetherianSeparatedEtale B X hX)
    (s : 𝒢.presheaf.obj (op V)) :
    (Over.forget V).op ⋙ locallyConstantPresheaf.{u + 1, u} B X hX (ULift.{u + 1} F) ≅
      (Over.forget V).op ⋙ (uliftSheaf 𝒢).obj :=
  NatIso.ofComponents
    (fun W ↦ Equiv.toIso ((LocallyConstant.congrRight Equiv.ulift).trans
      ((Equiv.ofBijective _ (bijective_act h𝒢 (𝒢.presheaf.map W.unop.hom.op s))).trans
        Equiv.ulift.symm)))
    (fun {W W'} g ↦ by
      ext k
      apply ULift.ext
      exact (map_act_map_hom s g.unop (LocallyConstant.congrRight Equiv.ulift k)).symm)

/-- **Local triviality.** Over an object `V` of `Et(X)` on which a formally principal sheaf `𝒢`
has a section, `𝒢` is the constant sheaf with value `F`. -/
lemma nonempty_constantSheaf_obj_iso_overPullback (h𝒢 : 𝒢.IsFormallyPrincipal)
    (V : SmallNoetherianSeparatedEtale B X hX) (s : 𝒢.presheaf.obj (op V)) :
    Nonempty ((constantSheaf ((topology B X hX).over V) (Type (u + 1))).obj (ULift.{u + 1} F) ≅
      ((topology B X hX).overPullback (Type (u + 1)) V).obj (uliftSheaf 𝒢)) := by
  have := isLocallyInjective_constToLocallyConstantPresheaf.{u + 1, u} (B := B) (S := X) (hS := hX)
    (ULift.{u + 1} F)
  have := isLocallySurjective_constToLocallyConstantPresheaf.{u + 1, u} (B := B) (S := X) (hS := hX)
    (ULift.{u + 1} F)
  let ψ : (Functor.const (Over V)ᵒᵖ).obj (ULift.{u + 1} F) ⟶
      (((topology B X hX).overPullback (Type (u + 1)) V).obj (uliftSheaf 𝒢)).obj :=
    Functor.whiskerLeft (Over.forget V).op
      (constToLocallyConstantPresheaf.{u + 1, u} B X hX (ULift.{u + 1} F)) ≫ (orbitIso 𝒢 h𝒢 V s).hom
  have hi : Presheaf.IsLocallyInjective ((topology B X hX).over V) (orbitIso 𝒢 h𝒢 V s).hom :=
    Presheaf.isLocallyInjective_of_injective _ _ fun W ↦
      ((orbitIso 𝒢 h𝒢 V s).app W).toEquiv.injective
  have hs : Presheaf.IsLocallySurjective ((topology B X hX).over V) (orbitIso 𝒢 h𝒢 V s).hom :=
    Presheaf.isLocallySurjective_of_surjective _ _ fun W ↦
      ((orbitIso 𝒢 h𝒢 V s).app W).toEquiv.surjective
  exact ⟨Stacks.ConstantSheaf.presheafToSheafObjIso _ ψ
    (@Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ inferInstance hi)
    (@Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ inferInstance hs)⟩

variable (B X hX) in
/-- The constant section `τ` of `F_X` over `U`. -/
abbrev constSection (U : (SmallNoetherianSeparatedEtale B X hX)ᵒᵖ) (τ : F) :
    (locallyConstantSheafOfGroups B X hX F).presheaf.obj U :=
  LocallyConstant.const _ τ

variable (𝒢) in
/-- The endomorphism `g ↦ g ^ τ` of `𝒢`, for `τ ∈ F` the constant section. -/
noncomputable def actConst (τ : F) : 𝒢.presheaf ⟶ 𝒢.presheaf where
  app U := TypeCat.ofHom fun g ↦ 𝒢.act U g (constSection B X hX U τ)
  naturality U V f := by
    ext g
    exact (𝒢.naturality f g (constSection B X hX U τ)).symm

@[simp]
lemma actConst_app_apply (τ : F) (U : (SmallNoetherianSeparatedEtale B X hX)ᵒᵖ)
    (g : 𝒢.presheaf.obj U) : (actConst 𝒢 τ).app U g = 𝒢.act U g (constSection B X hX U τ) :=
  rfl

omit [IsLocallyNoetherian X] in
/-- **Yoneda for `h_Y` on `Et(X)`.** An endomorphism `Φ` of the presheaf `h_Y` represented by an
object `Y` of `Et(X)` is postcomposition with `Φ(id_Y)`. -/
lemma app_eq_comp_app_id {Y : SmallNoetherianSeparatedEtale B X hX}
    (Φ : representablePresheaf B X hX ((toOver B X hX).obj Y) ⟶
      representablePresheaf B X hX ((toOver B X hX).obj Y))
    (U : SmallNoetherianSeparatedEtale B X hX) (t : (toOver B X hX).obj U ⟶ (toOver B X hX).obj Y) :
    Φ.app (op U) t = t ≫ Φ.app (op Y) (𝟙 _) := by
  obtain ⟨t', rfl⟩ := (toOver B X hX).map_surjective t
  have := NatTrans.naturality_apply Φ t'.op (𝟙 ((toOver B X hX).obj Y))
  simp only [representablePresheaf.map_apply] at this
  exact this

variable {Y : SmallNoetherianSeparatedEtale B X hX}
  (θ : representablePresheaf B X hX ((toOver B X hX).obj Y) ≅ 𝒢.presheaf)

/-- The endomorphism `t ↦ θ⁻¹(θ(t) ^ τ⁻¹)` of `h_Y`, for an isomorphism `θ : h_Y ≅ 𝒢`. -/
noncomputable def transportedAct (τ : F) :
    representablePresheaf B X hX ((toOver B X hX).obj Y) ⟶
      representablePresheaf B X hX ((toOver B X hX).obj Y) :=
  θ.hom ≫ actConst 𝒢 τ⁻¹ ≫ θ.inv

variable (Y) in
/-- The identity of `Y`, as a section of `h_Y` over `Y`. -/
def idSection : (representablePresheaf B X hX ((toOver B X hX).obj Y)).obj (op Y) :=
  𝟙 ((toOver B X hX).obj Y)

/-- The `X`-endomorphism `a_τ` of `Y` with `θ(t ≫ a_τ) = θ(t) ^ τ⁻¹`. -/
noncomputable def actionHom (τ : F) : (toOver B X hX).obj Y ⟶ (toOver B X hX).obj Y :=
  (transportedAct θ τ).app (op Y) (idSection Y)

lemma transportedAct_app (τ : F) (U : SmallNoetherianSeparatedEtale B X hX)
    (t : (toOver B X hX).obj U ⟶ (toOver B X hX).obj Y) :
    (transportedAct θ τ).app (op U) t = t ≫ actionHom θ τ :=
  app_eq_comp_app_id _ U t

lemma hom_app_comp_actionHom (τ : F) (U : SmallNoetherianSeparatedEtale B X hX)
    (t : (toOver B X hX).obj U ⟶ (toOver B X hX).obj Y) :
    θ.hom.app (op U) (t ≫ actionHom θ τ) =
      𝒢.act (op U) (θ.hom.app (op U) t) (constSection B X hX (op U) τ⁻¹) := by
  rw [← transportedAct_app]
  change θ.hom.app _ (θ.inv.app _ ((actConst 𝒢 τ⁻¹).app _ (θ.hom.app _ t))) = _
  rw [Iso.inv_hom_id_app_apply]
  rfl

lemma transportedAct_comp (τ τ' : F) :
    transportedAct θ τ' ≫ transportedAct θ τ = transportedAct θ (τ * τ') := by
  ext U t
  change θ.inv.app U ((actConst 𝒢 τ⁻¹).app U (θ.hom.app U (θ.inv.app U
    ((actConst 𝒢 τ'⁻¹).app U (θ.hom.app U t))))) =
      θ.inv.app U ((actConst 𝒢 (τ * τ')⁻¹).app U (θ.hom.app U t))
  rw [Iso.inv_hom_id_app_apply]
  congr 1
  rw [actConst_app_apply, actConst_app_apply, actConst_app_apply, ← 𝒢.act_mul, mul_inv_rev]
  rfl

lemma actionHom_mul (τ τ' : F) :
    actionHom θ (τ * τ') = actionHom θ τ' ≫ actionHom θ τ := by
  rw [actionHom, ← transportedAct_comp]
  change (transportedAct θ τ).app (op Y) ((transportedAct θ τ').app (op Y) (idSection Y)) = _
  exact transportedAct_app θ τ Y (actionHom θ τ')

lemma actionHom_one : actionHom θ 1 = 𝟙 _ := by
  have h : constSection B X hX (op Y) (1 : F)⁻¹ = 1 := by
    rw [inv_one]; rfl
  change θ.inv.app _ ((actConst 𝒢 1⁻¹).app _ (θ.hom.app _ (idSection Y))) = 𝟙 _
  rw [actConst_app_apply, h, 𝒢.act_one]
  exact Iso.hom_inv_id_app_apply θ (op Y) _

/-- The action `τ ↦ a_τ` of `F` on `Y` by `X`-automorphisms transported from `𝒢` along `θ`. -/
noncomputable def actionAut : F →* Aut ((toOver B X hX).obj Y) where
  toFun τ := ⟨actionHom θ τ, actionHom θ τ⁻¹,
    by rw [← actionHom_mul, inv_mul_cancel, actionHom_one],
    by rw [← actionHom_mul, mul_inv_cancel, actionHom_one]⟩
  map_one' := Iso.ext (actionHom_one θ)
  map_mul' τ τ' := Iso.ext (actionHom_mul θ τ τ')

@[simp]
lemma actionAut_apply_hom (τ : F) : (actionAut θ τ).hom = actionHom θ τ :=
  rfl

/-- **Equivariance of `θ`.** For the action `τ ↦ a_τ` transported along `θ`, and the induced
right action of `F_X` on `h_Y`, `θ(t ^ σ) = θ(t) ^ σ`. The two sides agree after restriction to
every member of a covering of `U` on which `σ` is constant, by the definition of `a_τ`, hence
agree by the sheaf property of `𝒢`. -/
lemma hom_app_smul (U : SmallNoetherianSeparatedEtale B X hX)
    (σ : (locallyConstantPresheafGrp B X hX F).obj (op U))
    (t : (representablePresheaf B X hX ((toOver B X hX).obj Y)).obj (op U)) :
    θ.hom.app (op U) (letI := inducedMulAction (actionAut θ) U; MulOpposite.op σ • t) =
      𝒢.act (op U) (θ.hom.app (op U) t) σ := by
  let := inducedMulAction (actionAut θ) U
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).mp 𝒢.isSheaf).isSeparated _
    ((isLocallySurjective_constToLocallyConstantPresheaf.{u, u} (B := B) (S := X) (hS := hX)
      F).imageSieve_mem (U := U) σ)
  refine hsep.ext fun W f hf ↦ ?_
  obtain ⟨(τ : F), hτ⟩ := hf
  have hτ' : constSection B X hX (op W) τ =
      (locallyConstantSheafOfGroups B X hX F).presheaf.map f.op σ := hτ
  have hx : ∀ x, (show LocallyConstant ((toScheme B X hX).obj U) F from σ)
      ((toScheme B X hX).map f x) = τ := fun x ↦
    (congrArg (fun k : LocallyConstant ((toScheme B X hX).obj W) F ↦ k x) hτ').symm
  have key : (toOver B X hX).map f ≫ (MulOpposite.op σ • t) =
      ((toOver B X hX).map f ≫ t) ≫ actionHom θ τ⁻¹ := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    exact comp_inducedMulAction_smul_left_of_forall (actionAut θ) _ σ t τ hx
  calc 𝒢.presheaf.map f.op (θ.hom.app (op U) (MulOpposite.op σ • t))
      = θ.hom.app (op W) ((toOver B X hX).map f ≫ (MulOpposite.op σ • t)) :=
        (NatTrans.naturality_apply θ.hom f.op _).symm
    _ = θ.hom.app (op W) (((toOver B X hX).map f ≫ t) ≫ actionHom θ τ⁻¹) := by rw [key]
    _ = 𝒢.act (op W) (θ.hom.app (op W) ((toOver B X hX).map f ≫ t))
          (constSection B X hX (op W) τ) := by rw [hom_app_comp_actionHom, inv_inv]
    _ = 𝒢.act (op W) (𝒢.presheaf.map f.op (θ.hom.app (op U) t))
          ((locallyConstantSheafOfGroups B X hX F).presheaf.map f.op σ) := by
        rw [← hτ']
        congr 1
        exact NatTrans.naturality_apply θ.hom f.op t
    _ = 𝒢.presheaf.map f.op (𝒢.act (op U) (θ.hom.app (op U) t) σ) :=
        (𝒢.naturality f.op _ _).symm

end LocallyNoetherian

end TorsorRepresentable

section Noetherian

variable [IsNoetherian X] [X.IsSeparated]

namespace TorsorRepresentable

variable {𝒢 : SheafOfGroups.RightAction (locallyConstantSheafOfGroups B X hX F)}

/-- **A torsor under `F_X` is finite locally constant**, for a finite group `F`: on every member
of the covering of `U` by the objects of `Et(X)` over `U` on which `𝒢` has a section, `𝒢` is the
constant sheaf with value `F`. -/
theorem isFiniteLocallyConstant_uliftSheaf [Finite F]
    (h𝒢 : 𝒢.IsFormallyPrincipal) {ι : Type*} (V : ι → SmallNoetherianSeparatedEtale B X hX)
    (hV : Scheme.IsEtaleCovering fun i ↦ structureMorphism (V i))
    (hne : ∀ i, Nonempty (𝒢.presheaf.obj (op (V i)))) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (topology B X hX) (uliftSheaf 𝒢) where
  exists_finite_cover U := by
    refine ⟨Σ W : SmallNoetherianSeparatedEtale B X hX,
      {f : W ⟶ U // Nonempty (𝒢.presheaf.obj (op W))}, fun a ↦ a.1, fun a ↦ a.2.1, ?_,
      fun a ↦ ?_⟩
    · rw [mem_topology_iff]
      intro x
      obtain ⟨i, y, hy⟩ := hV.exists_mem_range (structureMorphism U x)
      let tU : U ⟶ final B X hX :=
        (homEquiv _ _).symm ⟨structureMorphism U, Category.comp_id _⟩
      let tV : V i ⟶ final B X hX :=
        (homEquiv _ _).symm ⟨structureMorphism (V i), Category.comp_id _⟩
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := (toScheme B X hX).map tU) (g := (toScheme B X hX).map tV) x y hy.symm
      refine ⟨pullbackObj tU tV, pullbackFst tU tV, ?_, z, hz⟩
      exact Sieve.ofArrows_mk _ (fun a : Σ W : SmallNoetherianSeparatedEtale B X hX,
          {f : W ⟶ U // Nonempty (𝒢.presheaf.obj (op W))} ↦ a.2.1)
        ⟨pullbackObj tU tV, pullbackFst tU tV,
          (hne i).map (𝒢.presheaf.map (pullbackSnd tU tV).op)⟩
    · obtain ⟨s⟩ := a.2.2
      exact ⟨ULift.{u + 1} F, inferInstance, nonempty_constantSheaf_obj_iso_overPullback h𝒢 a.1 s⟩

/-- **Representability of the lifted sheaf.** A formally principal sheaf `𝒢` with an étale
covering of `X` on whose members it has sections is, after lifting its values to
`Type (u + 1)`, represented by an object `X'` of `Et(X)` finite over `X`. This is Stacks 03RV
applied to the finite locally constant sheaf `𝒢`, transported along the dense subsite
`Et(X) ⊆ SmallEtale X`. -/
theorem exists_isFinite_nonempty_iso [Finite F]
    (h𝒢 : 𝒢.IsFormallyPrincipal) {ι : Type*} (V : ι → SmallNoetherianSeparatedEtale B X hX)
    (hV : Scheme.IsEtaleCovering fun i ↦ structureMorphism (V i))
    (hne : ∀ i, Nonempty (𝒢.presheaf.obj (op (V i)))) :
    ∃ X' : SmallNoetherianSeparatedEtale B X hX, IsFinite (structureMorphism X') ∧
      Nonempty (yoneda.obj X' ⋙ uliftFunctor.{u + 1} ≅ 𝒢.presheaf ⋙ uliftFunctor.{u + 1}) := by
  let E := sheafEquiv B X hX (Type (u + 1))
  have h₁ := isFiniteLocallyConstant_uliftSheaf h𝒢 V hV hne
  have h₂ : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X hX)
      (E.functor.obj (uliftSheaf 𝒢)) := by
    rw [Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_sheafPushforwardContinuous.{0, u, u + 1}
      (J := topology B X hX) (inclusion B X hX)]
    exact Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso _ (E.unitIso.app (uliftSheaf 𝒢)) h₁
  obtain ⟨U, hUfin, ⟨e⟩⟩ :=
    (Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable B ⟨X, hX⟩
      _).mp h₂
  let X' : SmallNoetherianSeparatedEtale B X hX := ⟨U, isNoetherianSeparated_of_isFinite U⟩
  refine ⟨X', hUfin, ⟨?_⟩⟩
  let e₁ : uliftSheaf 𝒢 ≅ E.inverse.obj ((SmallEtale.topology B X hX).uliftYoneda.{u + 1}.obj U) :=
    E.unitIso.app _ ≪≫ E.inverse.mapIso (e ≪≫
      Stacks.EtaleCohomology.sheafifiedYonedaIsoUliftYoneda _ U)
  exact (Functor.isoWhiskerRight (inclusionOpCompYonedaIso X') uliftFunctor.{u + 1}).symm ≪≫
    (sheafToPresheaf _ _).mapIso e₁.symm

end TorsorRepresentable

open TorsorRepresentable in
/-- **Torsors under a finite constant sheaf of groups are representable.** Let `X` be a
noetherian separated scheme, `F` a finite group and `𝒢` an `F_X`-torsor on `Et(X)`: a formally
principal sheaf with right `F_X`-action having a section over every member of an étale covering
`(V_i → X)`. Then there are an object `X'` of `Et(X)` whose structure morphism `X' → X` is étale
and affine (indeed finite), an action `τ ↦ a_τ = ρ τ` of `F` on `X'` by `X`-automorphisms, and an
isomorphism of sheaves of sets `θ : h_{X'} ≅ 𝒢` with `θ(t ^ σ) = θ(t) ^ σ` for all `U` in `Et(X)`,
`σ ∈ F_X(U)` and `t ∈ h_{X'}(U)`, where `h_{X'}` carries the right action of `F_X` induced by
`ρ` (`AlgebraicGeometry.SmallNoetherianSeparatedEtale.inducedMulAction`). -/
@[weil "lem_fk102_torsor_representable"]
theorem exists_iso_representablePresheaf_of_isFormallyPrincipal [Finite F]
    (𝒢 : SheafOfGroups.RightAction (locallyConstantSheafOfGroups B X hX F))
    (h𝒢 : 𝒢.IsFormallyPrincipal) {ι : Type*} (V : ι → SmallNoetherianSeparatedEtale B X hX)
    (hV : Scheme.IsEtaleCovering fun i ↦ structureMorphism (V i))
    (hne : ∀ i, Nonempty (𝒢.presheaf.obj (op (V i)))) :
    ∃ (X' : SmallNoetherianSeparatedEtale B X hX) (ρ : F →* Aut ((toOver B X hX).obj X'))
      (θ : representablePresheaf B X hX ((toOver B X hX).obj X') ≅ 𝒢.presheaf),
      IsAffineHom (structureMorphism X') ∧ IsFinite (structureMorphism X') ∧
      ∀ (U : SmallNoetherianSeparatedEtale B X hX)
        (σ : (locallyConstantPresheafGrp B X hX F).obj (op U))
        (t : (representablePresheaf B X hX ((toOver B X hX).obj X')).obj (op U)),
        θ.hom.app (op U) (letI := inducedMulAction ρ U; MulOpposite.op σ • t) =
          𝒢.act (op U) (θ.hom.app (op U) t) σ := by
  obtain ⟨X', hfin, ⟨e⟩⟩ := exists_isFinite_nonempty_iso h𝒢 V hV hne
  let θ : representablePresheaf B X hX ((toOver B X hX).obj X') ≅ 𝒢.presheaf :=
    representablePresheaf.toOverIso X' ≪≫
      ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight
        _).preimageIso e
  exact ⟨X', actionAut θ, θ, inferInstance, hfin, hom_app_smul θ⟩

end Noetherian

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
