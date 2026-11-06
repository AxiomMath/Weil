module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.EtaleLocalHomeomorph
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.Points
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Sheaves of sections of étale schemes on complex points

Let `Y` be a scheme locally of finite type over `ℂ`. Every `U` étale over `Y` gives a local
homeomorphism `U(ℂ) → Y(ℂ)` of complex points, and so a sheaf of sets `Φ U` on `Y(ℂ)`: its
sections over an open `V` are the continuous maps `σ : V → U(ℂ)` lifting the inclusion. This is
functorial in `U`, and the functor `Φ` from the small étale site of `Y` to sheaves of sets on
`Y(ℂ)` turns étale coverings into jointly locally surjective families. Consequently, for every
abelian sheaf `G` on `Y(ℂ)`, the presheaf `U ↦ Hom(ℤ[Φ U], G)` on the small étale site is a sheaf:
it is the direct image of `G` along the morphism of sites `Y(ℂ) → Y_et`. Its stalk at a complex
point `p` is the fibre of `U(ℂ) → Y(ℂ)` over `p`, that is the fibre at `p` of the étale geometric
point given by `p`.

## Main definitions

* `AlgebraicGeometry.Scheme.ComplexPoints.etaleMap`: the map `U(ℂ) → Y(ℂ)` of `U` étale over `Y`.
* `AlgebraicGeometry.Scheme.ComplexPoints.etalePullback`: the fibre product of étale `Y`-schemes,
  with `etalePullbackPoint` the complex point given by two points over the same point.
* `AlgebraicGeometry.Scheme.ComplexPoints.sectionsPresheaf`: the presheaf of continuous sections
  of `U(ℂ) → Y(ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.sectionsFunctor`: the functor `Φ` from étale `Y`-schemes
  to sheaves of sets on `Y(ℂ)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.freeSectionsFunctor`: its composite with the free
  abelian sheaf functor.
* `AlgebraicGeometry.Scheme.ComplexPoints.analyticDirectImagePresheaf`: `U ↦ Hom(ℤ[Φ U], G)`.
* `AlgebraicGeometry.Scheme.ComplexPoints.sectionsFiberEquiv`: the stalk of `Φ U` at `p` is the
  fibre of the étale point given by `p`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.isSheaf_sectionsPresheaf`: `Φ U` is a sheaf.
* `AlgebraicGeometry.Scheme.ComplexPoints.continuous_etalePullbackPoint`: two continuous lifts
  over the same section of `U(ℂ)` give a continuous lift to the fibre product.
* `AlgebraicGeometry.Scheme.ComplexPoints.exists_sectionsPresheaf_lift`: sections of `Φ U` lift
  locally to members of every étale covering sieve of `U`.
* `AlgebraicGeometry.Scheme.ComplexPoints.isSheaf_sectionsFunctor_op_comp_yoneda`: for every sheaf
  of sets `H` on `Y(ℂ)`, `U ↦ Hom(Φ U, H)` is an étale sheaf.
* `AlgebraicGeometry.Scheme.ComplexPoints.isSheaf_analyticDirectImagePresheaf`: for every abelian
  sheaf `G` on `Y(ℂ)`, `U ↦ Hom(ℤ[Φ U], G)` is a sheaf for the étale topology.
* `AlgebraicGeometry.Scheme.ComplexPoints.sectionsFiberEquiv_naturality`: the identification of
  stalks is natural in `U`.

## Implementation notes

The complex points are lifted to `Type 1` (`ULift`), so that sheaves of abelian groups in
`AddCommGrpCat.{1}` on them and sheaves on the small étale site of a scheme in universe `0`
take values in the same category. The sheaf condition on the étale side is proved by reducing to
sheaves of sets through the free–forgetful adjunction and gluing along local lifts: a complex
point of `U` lifts to a member of an étale covering, local homeomorphisms lift sections locally,
and a pair of lifts to two members of a covering is a section of their fibre product.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### Two facts about local homeomorphisms -/

section Topology

variable {E B V : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace V]

/-- Two lifts through a local homeomorphism, continuous at a point where they agree and with
the same image near it, agree near it. -/
theorem eventuallyEq_of_isLocalHomeomorph {q : E → B} (hq : IsLocalHomeomorph q)
    {σ₁ σ₂ : V → E} {v : V} (h₁ : ContinuousAt σ₁ v) (h₂ : ContinuousAt σ₂ v)
    (h : ∀ᶠ w in nhds v, q (σ₁ w) = q (σ₂ w)) (hv : σ₁ v = σ₂ v) : σ₁ =ᶠ[nhds v] σ₂ := by
  obtain ⟨O, hO, hvO, hinj⟩ := hq.isLocallyInjective (σ₁ v)
  have e₁ : ∀ᶠ w in nhds v, σ₁ w ∈ O := h₁.preimage_mem_nhds (hO.mem_nhds hvO)
  have e₂ : ∀ᶠ w in nhds v, σ₂ w ∈ O := h₂.preimage_mem_nhds (hO.mem_nhds (hv ▸ hvO))
  filter_upwards [e₁, e₂, h] with w hw₁ hw₂ hw
  exact hinj hw₁ hw₂ hw

/-- A continuous map into the base of a local homeomorphism lifts near every point, through any
prescribed point of the fibre. -/
theorem exists_local_lift_of_isLocalHomeomorph {q : E → B} (hq : IsLocalHomeomorph q)
    {σ : V → B} (hσ : Continuous σ) {v : V} {e : E} (he : q e = σ v) :
    ∃ (W : Set V) (τ : V → E), IsOpen W ∧ v ∈ W ∧ τ v = e ∧ ContinuousOn τ W ∧
      ∀ w ∈ W, q (τ w) = σ w := by
  obtain ⟨φ, heφ, rfl⟩ := hq e
  have hvt : σ v ∈ φ.target := he ▸ φ.map_source heφ
  refine ⟨σ ⁻¹' φ.target, φ.symm ∘ σ, φ.open_target.preimage hσ, hvt, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, ← he]
    exact φ.left_inv heφ
  · exact φ.continuousOn_symm.comp hσ.continuousOn fun w hw => hw
  · intro w hw
    exact φ.right_inv hw

end Topology

/-! ### The map on complex points of an étale `Y`-scheme -/

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ))

set_option hygiene false in
/-- The complex points of `Y`, lifted to `TopCat.{1}`. -/
local notation "𝔛" => TopCat.of (ULift.{1} (ComplexPoints y))

set_option hygiene false in
/-- The site of open subsets of `Y(ℂ)`. -/
local notation "𝔍" => _root_.Opens.grothendieckTopology 𝔛

/-- `U(ℂ) → Y(ℂ)` for `U` étale over `Y`. -/
noncomputable def etaleMap (U : Y.Etale) : ComplexPoints (U.hom ≫ y) → ComplexPoints y :=
  map U.hom rfl

@[simp]
theorem etaleMap_hom (U : Y.Etale) (q : ComplexPoints (U.hom ≫ y)) :
    (etaleMap y U q).hom = q.hom ≫ U.hom := rfl

theorem continuous_etaleMap (U : Y.Etale) : Continuous (etaleMap y U) :=
  continuous_map _ _

theorem isLocalHomeomorph_etaleMap [LocallyOfFiniteType y] (U : Y.Etale) :
    IsLocalHomeomorph (etaleMap y U) :=
  isLocalHomeomorph_map_of_etale _ _

/-- `U(ℂ) → V(ℂ)` for a morphism `f : U ⟶ V` of étale `Y`-schemes. -/
noncomputable def etaleHomMap {U V : Y.Etale} (f : U ⟶ V) :
    ComplexPoints (U.hom ≫ y) → ComplexPoints (V.hom ≫ y) :=
  map f.left (by rw [← Category.assoc, MorphismProperty.Over.w f])

@[simp]
theorem etaleHomMap_hom {U V : Y.Etale} (f : U ⟶ V) (q : ComplexPoints (U.hom ≫ y)) :
    (etaleHomMap y f q).hom = q.hom ≫ f.left := rfl

@[simp]
theorem etaleMap_etaleHomMap {U V : Y.Etale} (f : U ⟶ V) (q : ComplexPoints (U.hom ≫ y)) :
    etaleMap y V (etaleHomMap y f q) = etaleMap y U q :=
  ext (by simp [MorphismProperty.Over.w f])

@[simp]
theorem etaleHomMap_id (U : Y.Etale) (q : ComplexPoints (U.hom ≫ y)) :
    etaleHomMap y (𝟙 U) q = q :=
  ext (Category.comp_id _)

@[simp]
theorem etaleHomMap_comp {U V W : Y.Etale} (f : U ⟶ V) (g : V ⟶ W)
    (q : ComplexPoints (U.hom ≫ y)) :
    etaleHomMap y (f ≫ g) q = etaleHomMap y g (etaleHomMap y f q) :=
  ext (Category.assoc _ _ _).symm

theorem continuous_etaleHomMap {U V : Y.Etale} (f : U ⟶ V) : Continuous (etaleHomMap y f) :=
  continuous_map _ _

theorem isLocalHomeomorph_etaleHomMap [LocallyOfFiniteType y] {U V : Y.Etale} (f : U ⟶ V) :
    IsLocalHomeomorph (etaleHomMap y f) :=
  isLocalHomeomorph_map_of_etale _ _

/-! ### The sheaf of sections -/

/-- Being a continuous section of `U(ℂ) → Y(ℂ)` is a local condition. -/
def sectionsLocalPredicate (U : Y.Etale) :
    TopCat.LocalPredicate fun _ : 𝔛 => ULift.{1} (ComplexPoints (U.hom ≫ y)) where
  pred {V} σ := Continuous σ ∧ ∀ v : V, etaleMap y U (σ v).down = v.1.down
  res {V W} i σ h := ⟨h.1.comp (Opens.isOpenEmbedding_of_le i.le).continuous, fun w => h.2 _⟩
  locality {V} σ w := by
    refine ⟨(TopCat.continuousLocal 𝔛 (ULift.{1} (ComplexPoints (U.hom ≫ y)))).locality σ
      fun v => ?_, fun v => ?_⟩
    · obtain ⟨W, hvW, i, h⟩ := w v
      exact ⟨W, hvW, i, h.1⟩
    · obtain ⟨W, hvW, i, h⟩ := w v
      exact h.2 ⟨v.1, hvW⟩

/-- The sheaf of continuous sections of `U(ℂ) → Y(ℂ)`: its value on `V` is the set of continuous
`σ : V → U(ℂ)` with `etaleMap ∘ σ = incl`. -/
def sectionsPresheaf (U : Y.Etale) : (TopologicalSpace.Opens 𝔛)ᵒᵖ ⥤ Type 1 :=
  TopCat.subpresheafToTypes (sectionsLocalPredicate y U).toPrelocalPredicate

theorem sectionsPresheaf_obj (U : Y.Etale) (V : (TopologicalSpace.Opens 𝔛)ᵒᵖ) :
    (sectionsPresheaf y U).obj V = {σ : V.unop → ULift.{1} (ComplexPoints (U.hom ≫ y)) //
      Continuous σ ∧ ∀ v, etaleMap y U (σ v).down = v.1.down} := rfl

theorem isSheaf_sectionsPresheaf (U : Y.Etale) :
    Presheaf.IsSheaf (𝔍) (sectionsPresheaf y U) :=
  TopCat.subpresheafToTypes.isSheaf _

/-- Composing sections with `U(ℂ) → V(ℂ)` for a morphism `f : U ⟶ V`. -/
noncomputable def sectionsPresheafMap {U V : Y.Etale} (f : U ⟶ V) :
    sectionsPresheaf y U ⟶ sectionsPresheaf y V where
  app W := ↾fun σ => ⟨fun w => ULift.up (etaleHomMap y f (σ.1 w).down),
    continuous_uliftUp.comp ((continuous_etaleHomMap y f).comp
      (continuous_uliftDown.comp σ.2.1)), fun w => by simpa using σ.2.2 w⟩

@[simp]
theorem sectionsPresheafMap_app_apply {U V : Y.Etale} (f : U ⟶ V)
    (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : (sectionsPresheaf y U).obj W) (w : W.unop) :
    ((sectionsPresheafMap y f).app W σ).1 w = ULift.up (etaleHomMap y f (σ.1 w).down) := rfl

@[simp]
theorem sectionsPresheaf_map_apply (U : Y.Etale) {W W' : (TopologicalSpace.Opens 𝔛)ᵒᵖ}
    (i : W ⟶ W') (σ : (sectionsPresheaf y U).obj W) (w : W'.unop) :
    ((sectionsPresheaf y U).map i σ).1 w = σ.1 ⟨w.1, i.unop.le w.2⟩ := rfl

/-- The functor `Φ` from étale `Y`-schemes to sheaves of sets on `Y(ℂ)`: `U` goes to the sheaf of
continuous sections of `U(ℂ) → Y(ℂ)`. -/
noncomputable def sectionsFunctor : Y.Etale ⥤ Sheaf (𝔍) (Type 1) where
  obj U := ⟨sectionsPresheaf y U, isSheaf_sectionsPresheaf y U⟩
  map f := ObjectProperty.homMk (sectionsPresheafMap y f)
  map_id U := by
    ext W σ
    apply Subtype.ext
    funext w
    simp
  map_comp f g := by
    ext W σ
    apply Subtype.ext
    funext w
    simp

/-! ### Fibre products of étale `Y`-schemes -/

section FiberProduct

set_option backward.isDefEq.respectTransparency false

variable {U W₁ W₂ : Y.Etale} (f₁ : W₁ ⟶ U) (f₂ : W₂ ⟶ U)

/-- The fibre product `W₁ ×_U W₂` of étale `Y`-schemes, as an étale `Y`-scheme. -/
noncomputable def etalePullback : Y.Etale :=
  Etale.mk (pullback.fst f₁.left f₂.left ≫ W₁.hom)

@[simp]
theorem etalePullback_left : (etalePullback f₁ f₂).left = pullback f₁.left f₂.left := rfl

@[simp]
theorem etalePullback_hom :
    (etalePullback f₁ f₂).hom = pullback.fst f₁.left f₂.left ≫ W₁.hom := rfl

/-- The first projection of `W₁ ×_U W₂`. -/
noncomputable def etalePullbackFst : etalePullback f₁ f₂ ⟶ W₁ :=
  MorphismProperty.Over.homMk (pullback.fst f₁.left f₂.left) rfl trivial

/-- The second projection of `W₁ ×_U W₂`. -/
noncomputable def etalePullbackSnd : etalePullback f₁ f₂ ⟶ W₂ :=
  MorphismProperty.Over.homMk (pullback.snd f₁.left f₂.left) (by
    rw [etalePullback_hom, ← MorphismProperty.Over.w f₂, ← MorphismProperty.Over.w f₁,
      pullback.condition_assoc]) trivial

@[simp]
theorem etalePullbackFst_left :
    (etalePullbackFst f₁ f₂).left = pullback.fst f₁.left f₂.left := rfl

@[simp]
theorem etalePullbackSnd_left :
    (etalePullbackSnd f₁ f₂).left = pullback.snd f₁.left f₂.left := rfl

theorem etalePullback_condition :
    etalePullbackFst f₁ f₂ ≫ f₁ = etalePullbackSnd f₁ f₂ ≫ f₂ :=
  MorphismProperty.Over.Hom.ext (pullback.condition (f := f₁.left) (g := f₂.left))

/-- A pair of complex points of `W₁` and `W₂` over the same point of `U` is a complex point of
`W₁ ×_U W₂`. -/
noncomputable def etalePullbackPoint (a₁ : ComplexPoints (W₁.hom ≫ y))
    (a₂ : ComplexPoints (W₂.hom ≫ y)) (h : etaleHomMap y f₁ a₁ = etaleHomMap y f₂ a₂) :
    ComplexPoints ((etalePullback f₁ f₂).hom ≫ y) :=
  ⟨pullback.lift a₁.hom a₂.hom (congrArg ComplexPoints.hom h), by
    rw [etalePullback_hom, Category.assoc, pullback.lift_fst_assoc]
    exact a₁.hom_comp⟩

@[simp]
theorem etalePullbackPoint_hom (a₁ : ComplexPoints (W₁.hom ≫ y))
    (a₂ : ComplexPoints (W₂.hom ≫ y)) (h : etaleHomMap y f₁ a₁ = etaleHomMap y f₂ a₂) :
    (etalePullbackPoint y f₁ f₂ a₁ a₂ h).hom =
      pullback.lift a₁.hom a₂.hom (congrArg ComplexPoints.hom h) := rfl

@[simp]
theorem etaleHomMap_fst_etalePullbackPoint (a₁ : ComplexPoints (W₁.hom ≫ y))
    (a₂ : ComplexPoints (W₂.hom ≫ y)) (h : etaleHomMap y f₁ a₁ = etaleHomMap y f₂ a₂) :
    etaleHomMap y (etalePullbackFst f₁ f₂) (etalePullbackPoint y f₁ f₂ a₁ a₂ h) = a₁ :=
  ext (by simp)

@[simp]
theorem etaleHomMap_snd_etalePullbackPoint (a₁ : ComplexPoints (W₁.hom ≫ y))
    (a₂ : ComplexPoints (W₂.hom ≫ y)) (h : etaleHomMap y f₁ a₁ = etaleHomMap y f₂ a₂) :
    etaleHomMap y (etalePullbackSnd f₁ f₂) (etalePullbackPoint y f₁ f₂ a₁ a₂ h) = a₂ :=
  ext (by simp)

/-- Complex points of `W₁ ×_U W₂` are determined by their two projections. -/
theorem etalePullback_ext {z z' : ComplexPoints ((etalePullback f₁ f₂).hom ≫ y)}
    (h₁ : etaleHomMap y (etalePullbackFst f₁ f₂) z = etaleHomMap y (etalePullbackFst f₁ f₂) z')
    (h₂ : etaleHomMap y (etalePullbackSnd f₁ f₂) z = etaleHomMap y (etalePullbackSnd f₁ f₂) z') :
    z = z' :=
  ext (pullback.hom_ext (by simpa using congrArg ComplexPoints.hom h₁)
    (by simpa using congrArg ComplexPoints.hom h₂))

/-- **The pair of two continuous lifts is continuous.** Near a point it is the local inverse
of the first projection composed with the first lift. -/
theorem continuous_etalePullbackPoint [LocallyOfFiniteType y] {V : Type*} [TopologicalSpace V]
    {τ₁ : V → ComplexPoints (W₁.hom ≫ y)} {τ₂ : V → ComplexPoints (W₂.hom ≫ y)}
    (hτ₁ : Continuous τ₁) (hτ₂ : Continuous τ₂)
    (h : ∀ v, etaleHomMap y f₁ (τ₁ v) = etaleHomMap y f₂ (τ₂ v)) :
    Continuous fun v => etalePullbackPoint y f₁ f₂ (τ₁ v) (τ₂ v) (h v) := by
  rw [continuous_iff_continuousAt]
  intro v₀
  obtain ⟨O, τ, hO, hv₀O, hτv₀, hτO, hτ⟩ := exists_local_lift_of_isLocalHomeomorph
    (isLocalHomeomorph_etaleHomMap y (etalePullbackFst f₁ f₂)) hτ₁
    (etaleHomMap_fst_etalePullbackPoint y f₁ f₂ _ _ (h v₀))
  have hOn : O ∈ nhds v₀ := hO.mem_nhds hv₀O
  have hτc : ContinuousAt τ v₀ := hτO.continuousAt hOn
  have e₂ : (fun v => etaleHomMap y (etalePullbackSnd f₁ f₂) (τ v)) =ᶠ[nhds v₀] τ₂ := by
    refine eventuallyEq_of_isLocalHomeomorph (isLocalHomeomorph_etaleHomMap y f₂)
      ((continuous_etaleHomMap y _).continuousAt.comp hτc) hτ₂.continuousAt ?_ ?_
    · filter_upwards [hOn] with w hw
      rw [← h w, ← hτ w hw, ← etaleHomMap_comp, ← etaleHomMap_comp, etalePullback_condition]
    · rw [hτv₀, etaleHomMap_snd_etalePullbackPoint]
  have e : (fun v => etalePullbackPoint y f₁ f₂ (τ₁ v) (τ₂ v) (h v)) =ᶠ[nhds v₀] τ := by
    filter_upwards [hOn, e₂] with w hw hw₂
    exact etalePullback_ext y f₁ f₂ (by simp [hτ w hw]) (by simp [hw₂])
  exact hτc.congr e.symm

end FiberProduct

/-! ### Local lifts along étale coverings -/

section Lifts

set_option backward.isDefEq.respectTransparency false

variable [LocallyOfFiniteType y]

omit [LocallyOfFiniteType y] in
/-- A complex point of `U` lifts to a member of every étale covering sieve of `U`. -/
theorem exists_etaleHomMap_eq_of_mem {U : Y.Etale} {S : Sieve U}
    (hS : S ∈ Y.smallEtaleTopology U) (a : ComplexPoints (U.hom ≫ y)) :
    ∃ (W : Y.Etale) (f : W ⟶ U) (_ : S f) (q : ComplexPoints (W.hom ≫ y)),
      etaleHomMap y f q = a := by
  obtain ⟨W, f, hf, t, ht⟩ := (pointSmallEtale (a.hom ≫ U.hom)).jointly_surjective S hS
    (Over.homMk a.hom rfl : Over.mk (a.hom ≫ U.hom) ⟶ Over.mk U.hom)
  have ht' : t.left ≫ f.left = a.hom := congrArg CommaMorphism.left ht
  refine ⟨W, f, hf, ⟨t.left, ?_⟩, ext ht'⟩
  rw [← Category.assoc, show t.left ≫ W.hom = a.hom ≫ U.hom from Over.w t, Category.assoc]
  exact a.hom_comp

/-- **Local lifts.** A section of `U(ℂ) → Y(ℂ)` lifts, near every point, to a section of a member
of any étale covering sieve of `U`. -/
theorem exists_sectionsPresheaf_lift {U : Y.Etale} {S : Sieve U}
    (hS : S ∈ Y.smallEtaleTopology U) {V : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op V)) (v : 𝔛) (hv : v ∈ V) :
    ∃ (W : Y.Etale) (f : W ⟶ U) (_ : S f) (V' : TopologicalSpace.Opens 𝔛) (_ : v ∈ V')
      (hV' : V' ≤ V) (τ : (sectionsPresheaf y W).obj (op V')),
      ∀ w : V', etaleHomMap y f (τ.1 w).down = (σ.1 ⟨w.1, hV' w.2⟩).down := by
  obtain ⟨W, f, hf, q, hq⟩ := exists_etaleHomMap_eq_of_mem y hS (σ.1 ⟨v, hv⟩).down
  obtain ⟨O, τ, hO, hvO, -, hτO, hτ⟩ := exists_local_lift_of_isLocalHomeomorph
    (isLocalHomeomorph_etaleHomMap y f) (continuous_uliftDown.comp σ.2.1) hq
  let V' : TopologicalSpace.Opens 𝔛 := ⟨Subtype.val '' O, V.2.isOpenMap_subtype_val O hO⟩
  have hV' : V' ≤ V := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hmem (w : V') : (⟨w.1, hV' w.2⟩ : V) ∈ O := by
    obtain ⟨x, hx, hxw⟩ := w.2
    have : (⟨w.1, hV' w.2⟩ : V) = x := Subtype.ext hxw.symm
    rw [this]
    exact hx
  refine ⟨W, f, hf, V', ⟨⟨v, hv⟩, hvO, rfl⟩, hV',
    ⟨fun w => ULift.up (τ ⟨w.1, hV' w.2⟩), ?_, fun w => ?_⟩, fun w => hτ _ (hmem w)⟩
  · refine continuous_uliftUp.comp (hτO.comp_continuous ?_ hmem)
    exact (continuous_subtype_val.subtype_mk _)
  · rw [← etaleMap_etaleHomMap y f, hτ _ (hmem w)]
    exact σ.2.2 _

end Lifts

/-! ### The sheaf condition for `U ↦ Hom(Φ U, H)` -/

section SheafCondition

variable [LocallyOfFiniteType y] (H : Sheaf (𝔍) (Type 1))
  {U : Y.Etale} {S : Sieve U}
  {x : Presieve.FamilyOfElements ((sectionsFunctor y).op ⋙ yoneda.obj H) S.arrows}

omit [LocallyOfFiniteType y] in
theorem sectionsFunctor_map_hom_app_apply {U V : Y.Etale} (f : U ⟶ V)
    (W : (TopologicalSpace.Opens 𝔛)ᵒᵖ) (σ : (sectionsPresheaf y U).obj W) :
    ((sectionsFunctor y).map f).hom.app W σ = (sectionsPresheafMap y f).app W σ := rfl

include x in
/-- Two compatible sections of members of a covering over the same section of `U` have the same
image. -/
theorem family_apply_eq_of_compatible (hx : x.Compatible) {W₁ W₂ : Y.Etale} {f₁ : W₁ ⟶ U}
    {f₂ : W₂ ⟶ U} (h₁ : S f₁) (h₂ : S f₂) {V : TopologicalSpace.Opens 𝔛}
    (τ₁ : (sectionsPresheaf y W₁).obj (op V)) (τ₂ : (sectionsPresheaf y W₂).obj (op V))
    (h : ∀ w, etaleHomMap y f₁ (τ₁.1 w).down = etaleHomMap y f₂ (τ₂.1 w).down) :
    (x f₁ h₁).hom.app (op V) τ₁ = (x f₂ h₂).hom.app (op V) τ₂ := by
  let π : (sectionsPresheaf y (etalePullback f₁ f₂)).obj (op V) :=
    ⟨fun w => ULift.up (etalePullbackPoint y f₁ f₂ (τ₁.1 w).down (τ₂.1 w).down (h w)),
      continuous_uliftUp.comp (continuous_etalePullbackPoint y f₁ f₂
        (continuous_uliftDown.comp τ₁.2.1) (continuous_uliftDown.comp τ₂.2.1) h),
      fun w => by
        rw [← etaleMap_etaleHomMap y (etalePullbackFst f₁ f₂),
          etaleHomMap_fst_etalePullbackPoint]
        exact τ₁.2.2 w⟩
  have e₁ : (sectionsPresheafMap y (etalePullbackFst f₁ f₂)).app _ π = τ₁ :=
    Subtype.ext (funext fun w =>
      congrArg ULift.up (etaleHomMap_fst_etalePullbackPoint y f₁ f₂ _ _ (h w)))
  have e₂ : (sectionsPresheafMap y (etalePullbackSnd f₁ f₂)).app _ π = τ₂ :=
    Subtype.ext (funext fun w =>
      congrArg ULift.up (etaleHomMap_snd_etalePullbackPoint y f₁ f₂ _ _ (h w)))
  have := congrArg (fun α : (sectionsFunctor y).obj (etalePullback f₁ f₂) ⟶ H =>
    α.hom.app (op V) π) (hx (etalePullbackFst f₁ f₂) (etalePullbackSnd f₁ f₂) h₁ h₂
      (etalePullback_condition f₁ f₂))
  rw [← e₁, ← e₂]
  exact this

omit [LocallyOfFiniteType y] in
/-- Naturality of a morphism of sheaves out of `Φ W`, applied to a section. -/
theorem sectionsFunctor_hom_app_map {W : Y.Etale} (α : (sectionsFunctor y).obj W ⟶ H)
    {V₁ V₂ : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (i : V₁ ⟶ V₂) (τ : (sectionsPresheaf y W).obj V₁) :
    H.obj.map i (α.hom.app V₁ τ) = α.hom.app V₂ ((sectionsPresheaf y W).map i τ) :=
  (ConcreteCategory.congr_hom (α.hom.naturality i) τ).symm

omit [LocallyOfFiniteType y] in
theorem presheaf_map_map_apply (F : (TopologicalSpace.Opens 𝔛)ᵒᵖ ⥤ Type 1)
    {A B C : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C) (s : F.obj A) :
    F.map j (F.map i s) = F.map k s := by
  rw [← Functor.map_comp_apply, Subsingleton.elim (i ≫ j) k]

/-- A local lift of a section `σ` of `U(ℂ) → Y(ℂ)` over `V` to a section, over an open
`V' ≤ V`, of a member `f : W ⟶ U` of a sieve `S`. -/
structure SectionLift (S : Sieve U) {V : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op V)) : Type 1 where
  /-- the source of the member of the sieve -/
  W : Y.Etale
  /-- the member of the sieve -/
  f : W ⟶ U
  mem : S f
  /-- the open on which the lift is defined -/
  V' : TopologicalSpace.Opens 𝔛
  le : V' ≤ V
  /-- the lift -/
  τ : (sectionsPresheaf y W).obj (op V')
  eq : ∀ w : V', etaleHomMap y f (τ.1 w).down = (σ.1 ⟨w.1, le w.2⟩).down

variable {H}

theorem le_iSup_sectionLift (hS : S ∈ Y.smallEtaleTopology U) {V : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op V)) : V ≤ ⨆ d : SectionLift y S σ, d.V' := by
  intro v hv
  obtain ⟨W, f, hf, V', hvV', hV', τ, hτ⟩ := exists_sectionsPresheaf_lift y hS σ v hv
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, f, hf, V', hV', τ, hτ⟩, hvV'⟩

theorem isCompatible_sectionLift (hx : x.Compatible) {V : TopologicalSpace.Opens 𝔛}
    (σ : (sectionsPresheaf y U).obj (op V)) :
    TopCat.Presheaf.IsCompatible H.obj (fun d : SectionLift y S σ => d.V')
      (fun d => (x d.f d.mem).hom.app (op d.V') d.τ) := by
  intro d₁ d₂
  rw [sectionsFunctor_hom_app_map, sectionsFunctor_hom_app_map]
  apply family_apply_eq_of_compatible y H hx
  intro w
  simp only [sectionsPresheaf_map_apply, d₁.eq, d₂.eq]

theorem existsUnique_sectionLift_gluing (hS : S ∈ Y.smallEtaleTopology U) (hx : x.Compatible)
    {V : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op V)) :
    ∃! s : H.obj.obj (op V), ∀ d : SectionLift y S σ,
      H.obj.map (homOfLE d.le).op s = (x d.f d.mem).hom.app (op d.V') d.τ :=
  TopCat.Sheaf.existsUnique_gluing' H (fun d : SectionLift y S σ => d.V') V
    (fun d => homOfLE d.le) (le_iSup_sectionLift y hS σ) _ (isCompatible_sectionLift y hx σ)

/-- The section of `H` glued from the images of the local lifts of `σ`. -/
noncomputable def sectionsAmalgamation (hS : S ∈ Y.smallEtaleTopology U) (hx : x.Compatible)
    {V : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op V)) : H.obj.obj (op V) :=
  (existsUnique_sectionLift_gluing y hS hx σ).exists.choose

theorem sectionsAmalgamation_spec (hS : S ∈ Y.smallEtaleTopology U) (hx : x.Compatible)
    {V : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op V))
    (d : SectionLift y S σ) :
    H.obj.map (homOfLE d.le).op (sectionsAmalgamation y hS hx σ) =
      (x d.f d.mem).hom.app (op d.V') d.τ :=
  (existsUnique_sectionLift_gluing y hS hx σ).exists.choose_spec d

theorem eq_sectionsAmalgamation (hS : S ∈ Y.smallEtaleTopology U) (hx : x.Compatible)
    {V : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op V)) (s : H.obj.obj (op V))
    (hs : ∀ d : SectionLift y S σ,
      H.obj.map (homOfLE d.le).op s = (x d.f d.mem).hom.app (op d.V') d.τ) :
    s = sectionsAmalgamation y hS hx σ :=
  (existsUnique_sectionLift_gluing y hS hx σ).unique hs (sectionsAmalgamation_spec y hS hx σ)

theorem sectionsAmalgamation_map (hS : S ∈ Y.smallEtaleTopology U) (hx : x.Compatible)
    {V₁ V₂ : (TopologicalSpace.Opens 𝔛)ᵒᵖ} (σ : (sectionsPresheaf y U).obj V₁) (i : V₁ ⟶ V₂) :
    sectionsAmalgamation y hS hx (V := V₂.unop) ((sectionsPresheaf y U).map i σ) =
      H.obj.map i (sectionsAmalgamation y hS hx (V := V₁.unop) σ) := by
  symm
  refine eq_sectionsAmalgamation y hS hx _ _ fun d => ?_
  exact (presheaf_map_map_apply y H.obj i (homOfLE d.le).op
    (homOfLE (d.le.trans i.unop.le)).op _).trans
    (sectionsAmalgamation_spec y hS hx (V := V₁.unop) σ
      ⟨d.W, d.f, d.mem, d.V', d.le.trans i.unop.le, d.τ, d.eq⟩)

/-- The amalgamation `Φ U ⟶ H` of a compatible family on a covering sieve. -/
noncomputable def sectionsAmalgamationHom (hS : S ∈ Y.smallEtaleTopology U)
    (hx : x.Compatible) : (sectionsFunctor y).obj U ⟶ H :=
  ObjectProperty.homMk
    { app V := ↾fun σ => sectionsAmalgamation y hS hx (V := V.unop) σ
      naturality V₁ V₂ i := by
        ext σ
        exact sectionsAmalgamation_map y hS hx σ i }

theorem sectionsAmalgamationHom_app (hS : S ∈ Y.smallEtaleTopology U) (hx : x.Compatible)
    {V : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op V)) :
    (sectionsAmalgamationHom y hS hx).hom.app (op V) σ = sectionsAmalgamation y hS hx σ := rfl

theorem sectionsAmalgamation_sectionsPresheafMap (hS : S ∈ Y.smallEtaleTopology U)
    (hx : x.Compatible) {W : Y.Etale} (f : W ⟶ U) (hf : S f) {V : TopologicalSpace.Opens 𝔛}
    (τ : (sectionsPresheaf y W).obj (op V)) :
    sectionsAmalgamation y hS hx ((sectionsPresheafMap y f).app (op V) τ) =
      (x f hf).hom.app (op V) τ := by
  symm
  refine eq_sectionsAmalgamation y hS hx _ _ fun d => ?_
  rw [sectionsFunctor_hom_app_map]
  apply family_apply_eq_of_compatible y H hx
  intro w
  rw [d.eq w]
  rfl

theorem isAmalgamation_sectionsAmalgamationHom (hS : S ∈ Y.smallEtaleTopology U)
    (hx : x.Compatible) : x.IsAmalgamation (sectionsAmalgamationHom y hS hx) := by
  intro W f hf
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro τ
  exact sectionsAmalgamation_sectionsPresheafMap y hS hx f hf (V := V.unop) τ

theorem sectionsAmalgamation_eq_of_isAmalgamation (hS : S ∈ Y.smallEtaleTopology U)
    (hx : x.Compatible) (t : (sectionsFunctor y).obj U ⟶ H) (ht : x.IsAmalgamation t)
    {V : TopologicalSpace.Opens 𝔛} (σ : (sectionsPresheaf y U).obj (op V)) :
    t.hom.app (op V) σ = sectionsAmalgamation y hS hx σ := by
  refine eq_sectionsAmalgamation y hS hx _ _ fun d => ?_
  rw [sectionsFunctor_hom_app_map]
  have hσ : (sectionsPresheaf y U).map (homOfLE d.le).op σ =
      (sectionsPresheafMap y d.f).app _ d.τ :=
    Subtype.ext (funext fun w => congrArg ULift.up (d.eq w).symm)
  rw [hσ, ← ht d.f d.mem]
  rfl

theorem eq_sectionsAmalgamationHom (hS : S ∈ Y.smallEtaleTopology U) (hx : x.Compatible)
    (t : (sectionsFunctor y).obj U ⟶ H) (ht : x.IsAmalgamation t) :
    t = sectionsAmalgamationHom y hS hx := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro σ
  exact sectionsAmalgamation_eq_of_isAmalgamation y hS hx t ht (V := V.unop) σ

/-- **The étale sheaf condition, for sheaves of sets.** For every sheaf of sets `H` on `Y(ℂ)`,
`U ↦ Hom(Φ U, H)` is a sheaf on the small étale site of `Y`. -/
theorem isSheaf_sectionsFunctor_op_comp_yoneda (H : Sheaf (𝔍) (Type 1)) :
    Presieve.IsSheaf Y.smallEtaleTopology ((sectionsFunctor y).op ⋙ yoneda.obj H) :=
  fun _ _ hS _ hx => ⟨sectionsAmalgamationHom y hS hx,
    isAmalgamation_sectionsAmalgamationHom y hS hx,
    fun t ht => eq_sectionsAmalgamationHom y hS hx t ht⟩

end SheafCondition

/-! ### The direct image presheaf -/

/-- `Ψ = ℤ[Φ]`: the free abelian sheaf on the sheaf of sections of `U(ℂ) → Y(ℂ)`. -/
noncomputable def freeSectionsFunctor :
    Y.Etale ⥤ Sheaf (𝔍) AddCommGrpCat.{1} :=
  sectionsFunctor y ⋙ Sheaf.composeAndSheafify _ AddCommGrpCat.free.{1}

/-- `ε_* G : U ↦ Hom(ℤ[Φ U], G)`, the sections of `G` pulled back to `U(ℂ)`. -/
noncomputable def analyticDirectImagePresheaf
    (G : Sheaf (𝔍) AddCommGrpCat.{1}) :
    Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{1} :=
  (freeSectionsFunctor y).op ⋙ preadditiveYoneda.obj G


/-- The underlying presheaf of sets of `U ↦ Hom(ℤ[Φ U], G)` is `U ↦ Hom(Φ U, G)`, by the
free–forgetful adjunction. -/
noncomputable def analyticDirectImagePresheafForgetIso
    (G : Sheaf (𝔍) AddCommGrpCat.{1}) :
    analyticDirectImagePresheaf y G ⋙ CategoryTheory.forget AddCommGrpCat.{1} ≅
      (sectionsFunctor y).op ⋙ yoneda.obj
        ((sheafCompose (𝔍) (CategoryTheory.forget AddCommGrpCat.{1})).obj G) :=
  Functor.isoWhiskerLeft (sectionsFunctor y).op
    ((Sheaf.adjunction (𝔍) AddCommGrpCat.adj.{1}).compYonedaIso.app
      G).symm

/-- **`U ↦ Hom(ℤ[Φ U], G)` is an étale sheaf**, for every abelian sheaf `G` on `Y(ℂ)`. -/
theorem isSheaf_analyticDirectImagePresheaf [LocallyOfFiniteType y]
    (G : Sheaf (𝔍) AddCommGrpCat.{1}) :
    Presheaf.IsSheaf Y.smallEtaleTopology (analyticDirectImagePresheaf y G) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat.{1}),
    Presheaf.isSheaf_of_iso_iff (analyticDirectImagePresheafForgetIso y G),
    isSheaf_iff_isSheaf_of_type]
  exact isSheaf_sectionsFunctor_op_comp_yoneda y
    ((sheafCompose (𝔍) (CategoryTheory.forget AddCommGrpCat.{1})).obj G)

/-! ### Stalks of the sheaf of sections -/

section Fiber

set_option backward.isDefEq.respectTransparency false

variable (p : ComplexPoints y)

set_option hygiene false in
/-- The point of the site of open subsets of `Y(ℂ)` given by `p`. -/
local notation "𝔓" => _root_.Opens.pointGrothendieckTopology (X := 𝔛) (ULift.up p)

/-- A complex point of `U` over `p` is a point of the fibre at `p` of the étale geometric point
given by `p`. -/
noncomputable def etalePointFiberEquiv (U : Y.Etale) :
    {q : ComplexPoints (U.hom ≫ y) // etaleMap y U q = p} ≃
      (Scheme.pointSmallEtale p.hom).fiber.obj U where
  toFun q := Over.homMk q.1.hom (by simpa using congrArg ComplexPoints.hom q.2)
  invFun t := ⟨⟨t.left, by
      rw [← Category.assoc, show t.left ≫ U.hom = p.hom from Over.w t]
      exact p.hom_comp⟩, ext (Over.w t)⟩
  left_inv q := rfl
  right_inv t := rfl

/-- Evaluation at `p` of sections of `U(ℂ) → Y(ℂ)` near `p`, on the stalk at `p`. -/
noncomputable def sectionsFiberToFiber (U : Y.Etale) :
    ((𝔓).sheafFiber
      (A := Type 1)).obj ((sectionsFunctor y).obj U) ⟶
      ULift.{1} ((Scheme.pointSmallEtale p.hom).fiber.obj U) :=
  (𝔓).presheafFiberDesc
    (P := sectionsPresheaf y U)
    (fun _ hV => ↾fun σ => ULift.up (etalePointFiberEquiv y p U
      ⟨(σ.1 ⟨ULift.up p, hV.down.down⟩).down, σ.2.2 _⟩))
    (fun _ _ _ _ => rfl)

theorem sectionsFiberToFiber_toPresheafFiber (U : Y.Etale) (V : TopologicalSpace.Opens 𝔛)
    (hV : ULift.up p ∈ V) (σ : (sectionsPresheaf y U).obj (op V)) :
    sectionsFiberToFiber y p U
      ((𝔓).toPresheafFiber V
        ⟨⟨hV⟩⟩ (sectionsPresheaf y U) σ) =
      ULift.up (etalePointFiberEquiv y p U ⟨(σ.1 ⟨ULift.up p, hV⟩).down, σ.2.2 _⟩) :=
  ConcreteCategory.congr_hom
    ((𝔓).toPresheafFiber_presheafFiberDesc
      (P := sectionsPresheaf y U) (fun _ hV => ↾fun σ => ULift.up (etalePointFiberEquiv y p U
      ⟨(σ.1 ⟨ULift.up p, hV.down.down⟩).down, σ.2.2 _⟩)) (fun _ _ _ _ => rfl) V ⟨⟨hV⟩⟩) σ

/-- A property holding near a point of an open `V` holds on an open of `Y(ℂ)` around it. -/
theorem exists_opens_of_eventually {V : TopologicalSpace.Opens 𝔛} {v : V} {P : V → Prop}
    (h : ∀ᶠ w in nhds v, P w) :
    ∃ (O : TopologicalSpace.Opens 𝔛) (_ : v.1 ∈ O) (hO : O ≤ V), ∀ w : O, P ⟨w.1, hO w.2⟩ := by
  obtain ⟨t, ht, hto, hvt⟩ := mem_nhds_iff.1 h
  refine ⟨⟨Subtype.val '' t, V.2.isOpenMap_subtype_val t hto⟩, ⟨v, hvt, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro ⟨_, x, hx, rfl⟩
    exact ht hx

variable [LocallyOfFiniteType y]

theorem sectionsFiberToFiber_surjective (U : Y.Etale) :
    Function.Surjective (sectionsFiberToFiber y p U) := by
  intro t
  obtain ⟨W, τ, hW, hpW, hτp, hτW, hτ⟩ := exists_local_lift_of_isLocalHomeomorph
    (V := 𝔛) (isLocalHomeomorph_etaleMap y U) continuous_uliftDown (v := ULift.up p)
    ((etalePointFiberEquiv y p U).symm t.down).2
  let V : TopologicalSpace.Opens 𝔛 := ⟨W, hW⟩
  let σ : (sectionsPresheaf y U).obj (op V) :=
    ⟨fun w => ULift.up (τ w.1), continuous_uliftUp.comp
      (hτW.comp_continuous continuous_subtype_val fun w => w.2), fun w => hτ w.1 w.2⟩
  refine ⟨(𝔓).toPresheafFiber V
    ⟨⟨hpW⟩⟩ (sectionsPresheaf y U) σ, ?_⟩
  rw [sectionsFiberToFiber_toPresheafFiber]
  apply ULift.ext
  change etalePointFiberEquiv y p U ⟨τ (ULift.up p), _⟩ = t.down
  rw [← (etalePointFiberEquiv y p U).apply_symm_apply t.down]
  congr 1
  apply Subtype.ext
  change τ (ULift.up p) = ((etalePointFiberEquiv y p U).symm t.down).1
  exact hτp

theorem sectionsFiberToFiber_injective (U : Y.Etale) :
    Function.Injective (sectionsFiberToFiber y p U) := by
  intro z₁ z₂ h
  obtain ⟨V, hV, a₁, a₂, rfl, rfl⟩ :=
    (𝔓).toPresheafFiber_jointly_surjective₂
      (P := sectionsPresheaf y U) z₁ z₂
  obtain ⟨⟨hV⟩⟩ := hV
  rw [sectionsFiberToFiber_toPresheafFiber, sectionsFiberToFiber_toPresheafFiber] at h
  have h' : (a₁.1 ⟨ULift.up p, hV⟩).down = (a₂.1 ⟨ULift.up p, hV⟩).down :=
    congrArg Subtype.val ((etalePointFiberEquiv y p U).injective (ULift.up_injective h))
  have hev := eventuallyEq_of_isLocalHomeomorph (isLocalHomeomorph_etaleMap y U)
    (continuous_uliftDown.comp a₁.2.1).continuousAt (continuous_uliftDown.comp a₂.2.1).continuousAt
    (Filter.Eventually.of_forall fun w => (a₁.2.2 w).trans (a₂.2.2 w).symm) h'
  obtain ⟨O, hpO, hOV, hO⟩ := exists_opens_of_eventually y hev
  rw [GrothendieckTopology.Point.toPresheafFiber_eq_iff']
  refine ⟨O, homOfLE hOV, ⟨⟨hpO⟩⟩, rfl, Subtype.ext (funext fun w => ULift.ext _ _ (hO w))⟩

/-- **The stalk of the sheaf of sections** of `U(ℂ) → Y(ℂ)` at `p` is the fibre of `U` at the
étale geometric point given by `p`. -/
noncomputable def sectionsFiberEquiv (U : Y.Etale) :
    ((𝔓).sheafFiber
      (A := Type 1)).obj ((sectionsFunctor y).obj U) ≃
      ULift.{1} ((Scheme.pointSmallEtale p.hom).fiber.obj U) :=
  Equiv.ofBijective _ ⟨sectionsFiberToFiber_injective y p U, sectionsFiberToFiber_surjective y p U⟩

theorem sectionsFiberEquiv_apply (U : Y.Etale) (z) :
    sectionsFiberEquiv y p U z = sectionsFiberToFiber y p U z := rfl

/-- `sectionsFiberEquiv` is natural in the étale `Y`-scheme. -/
theorem sectionsFiberEquiv_naturality {U V : Y.Etale} (f : U ⟶ V)
    (z : ((𝔓).sheafFiber
      (A := Type 1)).obj ((sectionsFunctor y).obj U)) :
    sectionsFiberEquiv y p V
        (((𝔓).sheafFiber
          (A := Type 1)).map ((sectionsFunctor y).map f) z) =
      ULift.up ((Scheme.pointSmallEtale p.hom).fiber.map f (sectionsFiberEquiv y p U z).down) := by
  obtain ⟨W, ⟨⟨hW⟩⟩, a, rfl⟩ :=
    (𝔓).toPresheafFiber_jointly_surjective
      (P := sectionsPresheaf y U) z
  rw [sectionsFiberEquiv_apply, sectionsFiberEquiv_apply, sectionsFiberToFiber_toPresheafFiber]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  exact (sectionsFiberToFiber_toPresheafFiber y p V W hW _).trans rfl

end Fiber

end AlgebraicGeometry.Scheme.ComplexPoints
