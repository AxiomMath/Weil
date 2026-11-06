module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Sign rules for products of extension classes

## Main results

* `Weil.extClass_comp_extClass_add_extClass_comp_extClass_eq_zero`: the `3 × 3` lemma for
  extension classes. For a morphism of short exact sequences `R₁ ⟶ R₂ ⟶ R₃` of short exact
  sequences whose three columns are short exact, the two composites of extension classes
  `Ext²(R₃.X₃, R₁.X₁)` around the diagram add up to zero.
* `Weil.mapExactFunctor_comp_extClass_eq_negOnePow_smul`: for an objectwise short exact
  sequence `F₁ ⟶ F₂ ⟶ F₃` of exact functors with connecting classes `δ_X ∈ Ext¹(F₃ X, F₁ X)`
  and `b ∈ Extᵠ(X, Y)`, one has `F₃(b) · δ_Y = (-1)ᵠ δ_X · F₁(b)`.

## Implementation notes

The `3 × 3` lemma is proved without derived tensor products: with `N` the kernel of the
diagonal `R₂.X₂ ⟶ R₃.X₃`, the short exact sequences
`0 → R₁.X₁ → R₂.X₁ ⊞ R₁.X₂ → N → 0` and `0 → N → R₂.X₂ → R₃.X₃ → 0` map to the first column
and the first row, resp. to the third row and the third column, and naturality of extension
classes identifies the Yoneda product of their classes with both composites, up to the sign
coming from the first map `(φ.τ₁, -R₁.f)`. The sign rule for exact functors follows by
dimension shifting through injective objects of the source category.

## References

* M. Suárez-Álvarez, the Hilton–Eckmann argument for the anti-commutativity of cup products,
  Proc. Amer. Math. Soc. 132 (2004).
-/

@[expose] public noncomputable section

universe w w' u u' v v'

open CategoryTheory Limits Abelian

namespace Weil

section ThreeByThree

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ThreeByThree

variable {R₁ R₂ R₃ : ShortComplex C} (φ : R₁ ⟶ R₂) (ψ : R₂ ⟶ R₃)

/-- The short complex `N ⟶ R₂.X₂ ⟶ R₃.X₃`, where `N` is the kernel of the diagonal. -/
abbrev W : ShortComplex C := ShortComplex.mk (kernel.ι (R₂.g ≫ ψ.τ₃)) (R₂.g ≫ ψ.τ₃) (by simp)

variable (w₂ : φ.τ₂ ≫ ψ.τ₂ = 0)

/-- The short complex `R₁.X₁ ⟶ R₂.X₁ ⊞ R₁.X₂ ⟶ N`. -/
abbrev V : ShortComplex C :=
  ShortComplex.mk (biprod.lift φ.τ₁ (-R₁.f))
    (kernel.lift (R₂.g ≫ ψ.τ₃) (biprod.desc R₂.f φ.τ₂) (by
      ext
      · simp
      · simp only [biprod.inr_desc_assoc, comp_zero]
        rw [← ψ.comm₂₃, reassoc_of% w₂, zero_comp]))
    (by
      ext
      simp [φ.comm₁₂])

@[reassoc (attr := simp)]
lemma V_g_ι : (V φ ψ w₂).g ≫ kernel.ι (R₂.g ≫ ψ.τ₃) = biprod.desc R₂.f φ.τ₂ := by
  simp

variable {φ ψ}

lemma W_shortExact (hR₂ : R₂.ShortExact) (hψ₃ : Epi ψ.τ₃) : (W ψ).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := inferInstance
  epi_g := by
    have := hR₂.epi_g
    exact epi_comp _ _

lemma V_shortExact (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact)
    {w₁ : φ.τ₁ ≫ ψ.τ₁ = 0} {w₃ : φ.τ₃ ≫ ψ.τ₃ = 0}
    (hc₁ : (ShortComplex.mk φ.τ₁ ψ.τ₁ w₁).ShortExact)
    (hc₂ : (ShortComplex.mk φ.τ₂ ψ.τ₂ w₂).ShortExact)
    (hc₃ : (ShortComplex.mk φ.τ₃ ψ.τ₃ w₃).ShortExact) :
    (V φ ψ w₂).ShortExact := by
  have := hR₁.mono_f
  have := hR₁.epi_g
  have := hR₃.mono_f
  have := hc₂.mono_f
  have := hc₃.mono_f
  refine
    { exact := ?_
      mono_f := ?_
      epi_g := ?_ }
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x hx
    have hx' : x ≫ biprod.fst ≫ R₂.f + x ≫ biprod.snd ≫ φ.τ₂ = 0 := by
      have := hx =≫ kernel.ι (R₂.g ≫ ψ.τ₃)
      simp only [Category.assoc, kernel.lift_ι, zero_comp] at this
      rw [← this, ← Preadditive.comp_add]
      congr 1
      ext <;> simp
    have ha : (x ≫ biprod.fst) ≫ ψ.τ₁ = 0 := by
      rw [← cancel_mono R₃.f, zero_comp, Category.assoc, Category.assoc, ψ.comm₁₂]
      have := hx' =≫ ψ.τ₂
      simpa [w₂] using this
    obtain ⟨A', π, hπ, c, hc⟩ := hc₁.exact.exact_up_to_refinements _ ha
    refine ⟨A', π, hπ, c, ?_⟩
    dsimp at hc ⊢
    ext
    · simpa using hc
    · rw [← cancel_mono φ.τ₂]
      have := π ≫= hx'
      simp only [Preadditive.comp_add, comp_zero, reassoc_of% hc, φ.comm₁₂] at this
      simp only [Category.assoc, biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg]
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact this
  · have : (V φ ψ w₂).f ≫ (-biprod.snd) = R₁.f := by simp
    exact mono_of_mono_fac this
  · rw [epi_iff_surjective_up_to_refinements]
    intro A n
    obtain ⟨A₁, π₁, hπ₁, m, hm⟩ := hc₃.exact.exact_up_to_refinements
      (n ≫ kernel.ι (R₂.g ≫ ψ.τ₃) ≫ R₂.g) (by simp)
    obtain ⟨A₂, π₂, hπ₂, b, hb⟩ := surjective_up_to_refinements_of_epi R₁.g m
    obtain ⟨A₃, π₃, hπ₃, a, ha⟩ := hR₂.exact.exact_up_to_refinements
      (π₂ ≫ π₁ ≫ n ≫ kernel.ι (R₂.g ≫ ψ.τ₃) - b ≫ φ.τ₂) (by
        dsimp at hm
        simp only [Preadditive.sub_comp, Category.assoc, φ.comm₂₃]
        rw [hm, ← reassoc_of% hb, sub_self])
    refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance, biprod.lift a (π₃ ≫ b), ?_⟩
    rw [← cancel_mono (kernel.ι (R₂.g ≫ ψ.τ₃))]
    simp only [Category.assoc, kernel.lift_ι, biprod.lift_desc]
    dsimp at ha
    rw [← ha]
    simp

/-- The morphism `N ⟶ R₃.X₁` lifting `N ⟶ R₂.X₂ ⟶ R₃.X₂`. -/
def t (hR₃ : R₃.ShortExact) : kernel (R₂.g ≫ ψ.τ₃) ⟶ R₃.X₁ :=
  have := hR₃.mono_f
  hR₃.exact.lift (kernel.ι _ ≫ ψ.τ₂) (by rw [Category.assoc, ψ.comm₂₃]; exact kernel.condition _)

@[reassoc (attr := simp)]
lemma t_f (hR₃ : R₃.ShortExact) : t (ψ := ψ) hR₃ ≫ R₃.f = kernel.ι _ ≫ ψ.τ₂ := by
  have := hR₃.mono_f
  exact hR₃.exact.lift_f _ _

/-- The morphism `N ⟶ R₁.X₃` lifting `N ⟶ R₂.X₂ ⟶ R₂.X₃`. -/
def m {w₃ : φ.τ₃ ≫ ψ.τ₃ = 0} (hc₃ : (ShortComplex.mk φ.τ₃ ψ.τ₃ w₃).ShortExact) :
    kernel (R₂.g ≫ ψ.τ₃) ⟶ R₁.X₃ :=
  have := hc₃.mono_f
  hc₃.exact.lift (kernel.ι _ ≫ R₂.g) (by simp)

@[reassoc (attr := simp)]
lemma m_f {w₃ : φ.τ₃ ≫ ψ.τ₃ = 0} (hc₃ : (ShortComplex.mk φ.τ₃ ψ.τ₃ w₃).ShortExact) :
    m hc₃ ≫ φ.τ₃ = kernel.ι _ ≫ R₂.g := by
  have := hc₃.mono_f
  exact hc₃.exact.lift_f (S := ShortComplex.mk φ.τ₃ ψ.τ₃ w₃) _ _

end ThreeByThree

open ThreeByThree in
/-- The `3 × 3` lemma for extension classes: for morphisms `φ : R₁ ⟶ R₂`, `ψ : R₂ ⟶ R₃` of
short exact sequences whose three columns `R₁.Xⱼ ⟶ R₂.Xⱼ ⟶ R₃.Xⱼ` are short exact, the
composite of the classes of the third column and the first row plus the composite of the
classes of the third row and the first column vanishes in `Ext²(R₃.X₃, R₁.X₁)`. -/
theorem extClass_comp_extClass_add_extClass_comp_extClass_eq_zero [HasExt.{w} C]
    {R₁ R₂ R₃ : ShortComplex C} (φ : R₁ ⟶ R₂) (ψ : R₂ ⟶ R₃)
    (hR₁ : R₁.ShortExact) (hR₂ : R₂.ShortExact) (hR₃ : R₃.ShortExact)
    {w₁ : φ.τ₁ ≫ ψ.τ₁ = 0} {w₂ : φ.τ₂ ≫ ψ.τ₂ = 0} {w₃ : φ.τ₃ ≫ ψ.τ₃ = 0}
    (hc₁ : (ShortComplex.mk φ.τ₁ ψ.τ₁ w₁).ShortExact)
    (hc₂ : (ShortComplex.mk φ.τ₂ ψ.τ₂ w₂).ShortExact)
    (hc₃ : (ShortComplex.mk φ.τ₃ ψ.τ₃ w₃).ShortExact) {n : ℕ} (h : 1 + 1 = n) :
    hc₃.extClass.comp hR₁.extClass h + hR₃.extClass.comp hc₁.extClass h = 0 := by
  have := hR₃.mono_f
  have := hc₃.mono_f
  have hψ₃ : Epi ψ.τ₃ := hc₃.epi_g
  have hV := V_shortExact w₂ hR₁ hR₂ hR₃ hc₁ hc₂ hc₃
  have hW := W_shortExact (ψ := ψ) hR₂ hψ₃
  let f₁ : V φ ψ w₂ ⟶ ShortComplex.mk φ.τ₁ ψ.τ₁ w₁ :=
    { τ₁ := 𝟙 _
      τ₂ := biprod.fst
      τ₃ := t (ψ := ψ) hR₃
      comm₂₃ := by
        rw [← cancel_mono R₃.f]
        dsimp
        ext <;> simp [w₂, ψ.comm₁₂] }
  let f₂ : V φ ψ w₂ ⟶ R₁ :=
    { τ₁ := 𝟙 _
      τ₂ := -biprod.snd
      τ₃ := -m hc₃
      comm₂₃ := by
        rw [← cancel_mono φ.τ₃]
        dsimp
        ext <;> simp [φ.comm₂₃] }
  let f₃ : W ψ ⟶ R₃ :=
    { τ₁ := t (ψ := ψ) hR₃
      τ₂ := ψ.τ₂
      τ₃ := 𝟙 _
      comm₁₂ := by simp
      comm₂₃ := by simp [ψ.comm₂₃] }
  let f₄ : W ψ ⟶ ShortComplex.mk φ.τ₃ ψ.τ₃ w₃ :=
    { τ₁ := m hc₃
      τ₂ := R₂.g
      τ₃ := 𝟙 _ }
  have e₁ := hV.extClass_naturality hc₁ f₁
  have e₂ := hV.extClass_naturality hR₁ f₂
  have e₃ := hW.extClass_naturality hR₃ f₃
  have e₄ := hW.extClass_naturality hc₃ f₄
  simp only [f₁, f₂, f₃, f₄, Ext.comp_mk₀_id, Ext.mk₀_id_comp, Ext.mk₀_neg, Ext.neg_comp]
    at e₁ e₂ e₃ e₄
  subst h
  rw [← e₃, ← e₄, Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_second_deg_zero, ← e₁,
    ← neg_neg ((Ext.mk₀ (m hc₃)).comp hR₁.extClass (zero_add 1)), ← e₂, Ext.comp_neg,
    neg_add_cancel]

end ThreeByThree

section SignNaturality

namespace ExtSign

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

lemma zsmul_comp {X Y Z : C} {a b c : ℕ} (k : ℤ) (x : Ext.{w} X Y a) (y : Ext.{w} Y Z b)
    (h : a + b = c) : (k • x).comp y h = k • x.comp y h :=
  (AddMonoidHom.mk' (fun x : Ext.{w} X Y a ↦ x.comp y h)
    (fun _ _ ↦ Ext.add_comp _ _ _ _)).map_zsmul k x

lemma comp_zsmul {X Y Z : C} {a b c : ℕ} (k : ℤ) (x : Ext.{w} X Y a) (y : Ext.{w} Y Z b)
    (h : a + b = c) : x.comp (k • y) h = k • x.comp y h :=
  (AddMonoidHom.mk' (fun y : Ext.{w} Y Z b ↦ x.comp y h)
    (fun _ _ ↦ Ext.comp_add _ _ _ _)).map_zsmul k y

end ExtSign

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  {F₁ F₂ F₃ : C ⥤ D} [F₁.Additive] [F₂.Additive] [F₃.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂] [PreservesFiniteLimits F₃]
  [PreservesFiniteColimits F₁] [PreservesFiniteColimits F₂] [PreservesFiniteColimits F₃]
  (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) (hw : ∀ X, α.app X ≫ β.app X = 0)
  (hS : ∀ X, (ShortComplex.mk (α.app X) (β.app X) (hw X)).ShortExact)

omit [Abelian C] [HasExt.{w} C] [F₁.Additive] [F₂.Additive] [F₃.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂] [PreservesFiniteLimits F₃]
  [PreservesFiniteColimits F₁] [PreservesFiniteColimits F₂] [PreservesFiniteColimits F₃] in
include hS in
/-- Degree zero of `Weil.mapExactFunctor_comp_extClass_eq_negOnePow_smul`: the connecting
classes of an objectwise short exact sequence of exact functors are natural. -/
lemma mk₀_map_comp_extClass_eq_extClass_comp_mk₀_map {X Y : C} (f : X ⟶ Y) :
    (Ext.mk₀ (F₃.map f)).comp (hS Y).extClass (zero_add 1) =
      (hS X).extClass.comp (Ext.mk₀ (F₁.map f)) (add_zero 1) := by
  let g : ShortComplex.mk (α.app X) (β.app X) (hw X) ⟶
      ShortComplex.mk (α.app Y) (β.app Y) (hw Y) :=
    { τ₁ := F₁.map f
      τ₂ := F₂.map f
      τ₃ := F₃.map f
      comm₁₂ := α.naturality f
      comm₂₃ := β.naturality f }
  exact ((hS X).extClass_naturality (hS Y) g).symm

include hS in
lemma mapExactFunctor_comp_extClass_eq_negOnePow_smul_aux [EnoughInjectives C] (q : ℕ) :
    ∀ {X Y : C} (b : Ext.{w} X Y q),
      (b.mapExactFunctor F₃).comp (hS Y).extClass rfl =
        ((-1 : ℤ) ^ q) • (hS X).extClass.comp (b.mapExactFunctor F₁) (add_comm 1 q) := by
  induction q with
  | zero =>
    intro X Y b
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).2 b
    rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, pow_zero, one_smul]
    exact mk₀_map_comp_extClass_eq_extClass_comp_mk₀_map α β hw hS f
  | succ q ih =>
    intro X Y b
    let T : ShortComplex C :=
      ShortComplex.mk (Injective.ι Y) (cokernel.π (Injective.ι Y)) (cokernel.condition _)
    have hT : T.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
    have hb : b.comp (Ext.mk₀ T.f) (add_zero _) = 0 := Ext.eq_zero_of_injective _
    obtain ⟨b', rfl⟩ := Ext.covariant_sequence_exact₁ (hS := hT) X b hb rfl
    have L : (hT.map_of_exact F₃).extClass.comp (hS T.X₁).extClass (rfl : 1 + 1 = 2) =
        -(hS T.X₃).extClass.comp (hT.map_of_exact F₁).extClass rfl := by
      refine eq_neg_of_add_eq_zero_right ?_
      exact extClass_comp_extClass_add_extClass_comp_extClass_eq_zero
        (T.mapNatTrans α) (T.mapNatTrans β)
        (hT.map_of_exact F₁) (hT.map_of_exact F₂) (hT.map_of_exact F₃)
        (hS T.X₁) (hS T.X₂) (hS T.X₃) rfl
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.mapExactFunctor_extClass,
      Ext.comp_assoc _ _ _ rfl (rfl : 1 + 1 = 2) (by lia), L, Ext.comp_neg,
      ← Ext.comp_assoc _ _ _ (rfl : q + 1 = q + 1) rfl (by lia), ih,
      ExtSign.zsmul_comp, Ext.comp_assoc _ _ _ (add_comm 1 q) rfl (by lia), pow_succ,
      mul_neg_one, neg_smul]

include hS in
/-- Sign naturality of connecting classes: for an objectwise short exact sequence of exact
functors `F₁ ⟶ F₂ ⟶ F₃` with connecting classes `δ_X ∈ Ext¹(F₃ X, F₁ X)` and any
`b ∈ Extᵠ(X, Y)`, one has `F₃(b) · δ_Y = (-1)ᵠ δ_X · F₁(b)`. -/
theorem mapExactFunctor_comp_extClass_eq_negOnePow_smul [EnoughInjectives C] {X Y : C} {q n : ℕ}
    (b : Ext.{w} X Y q) (h₁ : q + 1 = n) (h₂ : 1 + q = n) :
    (b.mapExactFunctor F₃).comp (hS Y).extClass h₁ =
      ((-1 : ℤ) ^ q) • (hS X).extClass.comp (b.mapExactFunctor F₁) h₂ := by
  subst h₁
  exact mapExactFunctor_comp_extClass_eq_negOnePow_smul_aux α β hw hS q b

end SignNaturality

end Weil
