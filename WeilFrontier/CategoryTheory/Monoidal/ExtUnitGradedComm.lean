module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import StacksFrontier.CategoryTheory.Abelian.ExtCupProduct
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.CategoryTheory.Abelian.ExtUnitAction
public import WeilFrontier.Algebra.Homology.DerivedCategory.Ext.ExtClassSignNaturality

/-!
# Graded commutativity of the Yoneda algebra `Ext^*(𝟙, 𝟙)`

Let `C` be an abelian monoidal category with enough injectives. A class `a ∈ Ext^p(𝟙, 𝟙)` acts
on every object `M` for which `- ⊗ M` is exact, by the class
`a · M = λ_M ∘ (a ⊗ M) ∘ λ_M⁻¹ ∈ Ext^p(M, M)` (`Stacks.ExtUnitAction.action`). On `M = 𝟙` this
action is `a` itself, and it is natural in `M` in degree zero.

Following Hilton–Eckmann (in the form of Suárez-Álvarez), the Yoneda product on `Ext^*(𝟙, 𝟙)`
is graded commutative, `a ∘ b = (-1)^{pq} b ∘ a`, as soon as there is a class `P` of objects
containing `𝟙`, made of objects with exact tensor, with enough embeddings into injective objects
of `P` with cokernel in `P`, and whose short exact sequences stay short exact after tensoring on
the left. The proof is dimension shifting in the second variable: for `c ∈ Ext^q(𝟙, M)` with
`P M`, one shows `a ∘ c = (-1)^{pq} c ∘ (a · M)` by induction on `q`. The inductive step is the
sign rule `(a · S.X₃) ∘ δ_S = (-1)^p δ_S ∘ (a · S.X₁)` for a short exact sequence `S` of objects
of `P`, which is the sign naturality of connecting classes
(`Weil.mapExactFunctor_comp_extClass_eq_negOnePow_smul`) for the objectwise short exact sequence
of exact functors `- ⊗ S.X₁ ⟶ - ⊗ S.X₂ ⟶ - ⊗ S.X₃`.

For the cup product attached to a pairing `μ : 𝟙 ⊗ 𝟙 ⟶ T`, the cup product of two classes of
`Ext^*(𝟙, 𝟙)` is their Yoneda product followed by `λ⁻¹ ≫ μ`; in particular it is
anticommutative on classes of the same odd degree.

## Main results

* `Weil.Ext.action_unit`: the action of `a` on `𝟙` is `a`.
* `Weil.Ext.action_comp_mk₀`: the action is natural in degree zero.
* `Weil.ShortComplex.shortExact_map_tensorLeft`: tensoring a short exact sequence on the left
  with `Z` keeps it short exact when `Z ⊗ -` is right exact and `Z ◁ S.f` is a monomorphism.
* `Weil.Ext.comp_eq_negOnePow_smul_comp_action`: `a ∘ c = (-1)^{pq} c ∘ (a · M)`, given the sign
  rule of the action on short exact sequences of `P`.
* `Weil.Ext.action_comp_extClass_eq_negOnePow_smul`: that sign rule.
* `Weil.Ext.comp_eq_negOnePow_smul_comp_of_unit`: graded commutativity of `Ext^*(𝟙, 𝟙)`.
* `Weil.Ext.cup_eq_comp_comp_mk₀`: the cup product on `Ext^*(𝟙, 𝟙)` is the Yoneda product.
* `Weil.Ext.cup_eq_neg_cup_of_odd`: the cup product is anticommutative in odd degree.

## Implementation notes

The action is StacksFrontier's `Stacks.ExtUnitAction.action`. No braiding and no additivity of the
tensor product in the second variable is assumed: the only hypotheses on `Z ⊗ -` are right
exactness and injectivity on the first map of the short exact sequences of `P`.
`Weil.Ext.comp_eq_negOnePow_smul_comp_of_unit_of_sign` and
`Weil.Ext.cup_eq_neg_cup_of_odd_of_sign` are the same statements with the sign rule of the action
as a hypothesis in place of the hypotheses on `Z ⊗ -`.

## References

* [P. J. Hilton, B. Eckmann, *Homotopy groups of maps and exact sequences*]
* [M. Suárez-Álvarez, *The Hilton–Heckmann argument for the anti-commutativity of cup
  products*, Proc. AMS 132 (2004)]
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory

namespace Weil

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]

namespace ShortComplex

/-- **Tensoring a short exact sequence on the left**: if `Z ⊗ -` is right exact and `Z ◁ S.f`
is a monomorphism, then `Z ⊗ S` is short exact. (When `Z ⊗ -` preserves finite colimits, the
instance `(tensorLeft Z).PreservesZeroMorphisms` is found by instance search.) -/
theorem shortExact_map_tensorLeft {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) (Z : C)
    [PreservesFiniteColimits (tensorLeft Z)] [(tensorLeft Z).PreservesZeroMorphisms]
    (hmono : Mono (Z ◁ S.f)) : (S.map (tensorLeft Z)).ShortExact := by
  have := hS.epi_g
  have : Epi (S.map (tensorLeft Z)).g := (tensorLeft Z).map_epi S.g
  have : Mono (S.map (tensorLeft Z)).f := hmono
  exact { exact := hS.exact.map_of_epi_of_preservesCokernel _ inferInstance inferInstance }

end ShortComplex

namespace Ext

variable [HasExt.{w} C]

omit [MonoidalCategory C] in
/-- The Yoneda product is `ℤ`-linear in the first variable. -/
theorem zsmul_comp {X Y Z : C} {a b c : ℕ} (r : ℤ) (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b)
    (h : a + b = c) : (r • α).comp β h = r • α.comp β h :=
  map_zsmul (Ext.postcomp β X h) r α

omit [MonoidalCategory C] in
/-- The Yoneda product is `ℤ`-linear in the second variable. -/
theorem comp_zsmul {X Y Z : C} {a b c : ℕ} (r : ℤ) (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b)
    (h : a + b = c) : α.comp (r • β) h = r • α.comp β h :=
  map_zsmul (Ext.precomp α Z h) r β

/-- **The action of `a ∈ Ext^p(𝟙, 𝟙)` on the unit is `a`**: the left and right unitors of `𝟙`
agree, and `- ⊗ 𝟙` is naturally isomorphic to the identity functor, which acts trivially. -/
theorem action_unit [EnoughInjectives C] {p : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p)
    [(tensorRight (𝟙_ C)).Additive] [PreservesFiniteLimits (tensorRight (𝟙_ C))]
    [PreservesFiniteColimits (tensorRight (𝟙_ C))] :
    Stacks.ExtUnitAction.action a (𝟙_ C) = a := by
  have key := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor (rightUnitorNatIso C).hom (𝟙_ C) p a
  rw [Stacks.ExtFunctorial.mapExactFunctor_id] at key
  have e : ((rightUnitorNatIso C).hom.app (𝟙_ C)) = (λ_ (𝟙_ C)).hom := by
    simp [unitors_equal]
  rw [e] at key
  rw [Stacks.ExtUnitAction.action, ← key, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Iso.inv_hom_id, Ext.mk₀_id_comp]

/-- **Naturality of the action in degree zero**: for `f : M ⟶ M'` between objects with exact
tensor, `(a · M) ∘ f = f ∘ (a · M')`, read as Yoneda products `(a · M).comp (mk₀ f)` and
`(mk₀ f).comp (a · M')`. -/
theorem action_comp_mk₀ [EnoughInjectives C] {p : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) {M M' : C}
    [(tensorRight M).Additive] [PreservesFiniteLimits (tensorRight M)]
    [PreservesFiniteColimits (tensorRight M)] [(tensorRight M').Additive]
    [PreservesFiniteLimits (tensorRight M')] [PreservesFiniteColimits (tensorRight M')]
    (f : M ⟶ M') :
    (Stacks.ExtUnitAction.action a M).comp (Ext.mk₀ f) (add_zero p) =
      (Ext.mk₀ f).comp (Stacks.ExtUnitAction.action a M') (zero_add p) :=
  (Stacks.ExtUnitAction.mk₀_comp_action a f).symm

section GradedComm

variable [EnoughInjectives C]

/-- **Dimension shifting for the action.** Let `P` be a class of objects with exact tensor, with
enough injective embeddings `M ↪ I ↠ K` with `P I`, `P K`, on whose short exact sequences the
action of every class of `Ext^*(𝟙, 𝟙)` commutes with the extension class up to the sign
`(-1)^p`. Then for `a ∈ Ext^p(𝟙, 𝟙)`, `M` in `P` and `c ∈ Ext^q(𝟙, M)`,
`a ∘ c = (-1)^{pq} c ∘ (a · M)`. -/
theorem comp_eq_negOnePow_smul_comp_action (P : C → Prop) (hunit : P (𝟙_ C))
    (hexact : ∀ X, P X → (tensorRight X).Additive ∧ PreservesFiniteLimits (tensorRight X) ∧
      PreservesFiniteColimits (tensorRight X))
    (hemb : ∀ X, P X → ∃ (S : CategoryTheory.ShortComplex C) (_ : S.ShortExact) (_ : S.X₁ ≅ X),
      Injective S.X₂ ∧ P S.X₂ ∧ P S.X₃)
    (hA : ∀ (S : CategoryTheory.ShortComplex C) (hS : S.ShortExact), P S.X₁ → P S.X₂ → P S.X₃ →
      ∀ (p : ℕ) (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) [(tensorRight S.X₁).Additive]
        [PreservesFiniteLimits (tensorRight S.X₁)] [PreservesFiniteColimits (tensorRight S.X₁)]
        [(tensorRight S.X₃).Additive] [PreservesFiniteLimits (tensorRight S.X₃)]
        [PreservesFiniteColimits (tensorRight S.X₃)],
        (Stacks.ExtUnitAction.action a S.X₃).comp hS.extClass rfl =
          ((-1 : ℤ) ^ p) • hS.extClass.comp (Stacks.ExtUnitAction.action a S.X₁) (add_comm 1 p))
    {p : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) (q : ℕ) :
    ∀ (M : C) (_ : P M) [(tensorRight M).Additive] [PreservesFiniteLimits (tensorRight M)]
      [PreservesFiniteColimits (tensorRight M)] (c : Ext.{w} (𝟙_ C) M q) {n : ℕ}
      (h : p + q = n) (h' : q + p = n),
      a.comp c h = ((-1 : ℤ) ^ (p * q)) • c.comp (Stacks.ExtUnitAction.action a M) h' := by
  induction q with
  | zero =>
    intro M hM _ _ _ c n h h'
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (𝟙_ C) M).surjective c
    obtain ⟨_, _, _⟩ := hexact _ hunit
    subst h
    rw [mul_zero, pow_zero, one_smul, ← action_comp_mk₀, action_unit]
  | succ q ih =>
    intro M hM _ _ _ c n h h'
    obtain ⟨S, hS, e, hI, h₂, h₃⟩ := hemb M hM
    let S' : CategoryTheory.ShortComplex C :=
      CategoryTheory.ShortComplex.mk (e.inv ≫ S.f) S.g (by simp)
    have hS' : S'.ShortExact :=
      CategoryTheory.ShortComplex.shortExact_of_iso
        (CategoryTheory.ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by simp [S'])
          (by simp [S'])) hS
    have : Injective S'.X₂ := hI
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ (𝟙_ C) hS' (S := S')
      (c : Ext.{w} (𝟙_ C) S'.X₁ (q + 1)) (Ext.eq_zero_of_injective _) rfl
    obtain ⟨_, _, _⟩ := hexact _ h₃
    have hA' := hA S' hS' hM h₂ h₃ p a
    have ih' := ih S'.X₃ h₃ x₃ (rfl : p + q = p + q) (add_comm q p)
    calc a.comp (x₃.comp hS'.extClass rfl) h
        = (a.comp x₃ rfl).comp hS'.extClass (by lia) := (Ext.comp_assoc _ _ _ _ _ (by lia)).symm
      _ = ((-1 : ℤ) ^ (p * q)) •
            (x₃.comp (Stacks.ExtUnitAction.action a S'.X₃) (add_comm q p)).comp
              hS'.extClass (by lia) := by rw [ih', zsmul_comp]
      _ = ((-1 : ℤ) ^ (p * q)) •
            x₃.comp ((Stacks.ExtUnitAction.action a S'.X₃).comp hS'.extClass rfl) (by lia) := by
            rw [Ext.comp_assoc _ _ _ _ _ (by lia)]
      _ = ((-1 : ℤ) ^ (p * q) * (-1) ^ p) •
            x₃.comp (hS'.extClass.comp (Stacks.ExtUnitAction.action a S'.X₁) (add_comm 1 p))
              (by lia) := by rw [hA', comp_zsmul, smul_smul]
      _ = ((-1 : ℤ) ^ (p * (q + 1))) •
            (x₃.comp hS'.extClass rfl).comp (Stacks.ExtUnitAction.action a M) h' := by
            rw [← pow_add, mul_add, mul_one, Ext.comp_assoc _ _ _ _ _ (by lia)]

/-- **Graded commutativity of `Ext^*(𝟙, 𝟙)`**, conditional on the sign naturality of the action:
under the hypotheses of `Weil.Ext.comp_eq_negOnePow_smul_comp_action`, for `a ∈ Ext^p(𝟙, 𝟙)` and
`b ∈ Ext^q(𝟙, 𝟙)`, `a ∘ b = (-1)^{pq} b ∘ a`. -/
theorem comp_eq_negOnePow_smul_comp_of_unit_of_sign (P : C → Prop) (hunit : P (𝟙_ C))
    (hexact : ∀ X, P X → (tensorRight X).Additive ∧ PreservesFiniteLimits (tensorRight X) ∧
      PreservesFiniteColimits (tensorRight X))
    (hemb : ∀ X, P X → ∃ (S : CategoryTheory.ShortComplex C) (_ : S.ShortExact) (_ : S.X₁ ≅ X),
      Injective S.X₂ ∧ P S.X₂ ∧ P S.X₃)
    (hA : ∀ (S : CategoryTheory.ShortComplex C) (hS : S.ShortExact), P S.X₁ → P S.X₂ → P S.X₃ →
      ∀ (p : ℕ) (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) [(tensorRight S.X₁).Additive]
        [PreservesFiniteLimits (tensorRight S.X₁)] [PreservesFiniteColimits (tensorRight S.X₁)]
        [(tensorRight S.X₃).Additive] [PreservesFiniteLimits (tensorRight S.X₃)]
        [PreservesFiniteColimits (tensorRight S.X₃)],
        (Stacks.ExtUnitAction.action a S.X₃).comp hS.extClass rfl =
          ((-1 : ℤ) ^ p) • hS.extClass.comp (Stacks.ExtUnitAction.action a S.X₁) (add_comm 1 p))
    {p q n : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) (b : Ext.{w} (𝟙_ C) (𝟙_ C) q) (h : p + q = n)
    (h' : q + p = n) :
    a.comp b h = ((-1 : ℤ) ^ (p * q)) • b.comp a h' := by
  obtain ⟨_, _, _⟩ := hexact _ hunit
  rw [comp_eq_negOnePow_smul_comp_action P hunit hexact hemb hA a q (𝟙_ C) hunit b h h',
    action_unit]

end GradedComm

section Cup

variable [EnoughInjectives C] [(tensorRight (𝟙_ C)).Additive]
  [PreservesFiniteLimits (tensorRight (𝟙_ C))] [PreservesFiniteColimits (tensorRight (𝟙_ C))]

/-- The image of `a ∈ Ext^p(𝟙, 𝟙)` under `- ⊗ 𝟙` is `a`, read through the left unitor of `𝟙`. -/
theorem mk₀_comp_mapExactFunctor_tensorRight_unit {p : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) :
    (Ext.mk₀ (λ_ (𝟙_ C)).inv).comp (a.mapExactFunctor (tensorRight (𝟙_ C))) (zero_add p) =
      a.comp (Ext.mk₀ (λ_ (𝟙_ C)).inv) (add_zero p) := by
  conv_rhs => rw [← action_unit a]
  rw [Stacks.ExtUnitAction.action, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.comp_mk₀_id]

/-- **The cup product on `Ext^*(𝟙, 𝟙)` is the Yoneda product**: for a pairing
`μ : 𝟙 ⊗ 𝟙 ⟶ T`, `a ∪_μ b = (b ∘ a) ∘ (λ⁻¹ ≫ μ)`. -/
theorem cup_eq_comp_comp_mk₀ {T : C} (μ : 𝟙_ C ⊗ 𝟙_ C ⟶ T) {i j n : ℕ}
    (a : Ext.{w} (𝟙_ C) (𝟙_ C) i) (b : Ext.{w} (𝟙_ C) (𝟙_ C) j) (h : j + i = n) :
    Stacks.ExtCup.cup μ a b h = (b.comp a h).comp (Ext.mk₀ ((λ_ (𝟙_ C)).inv ≫ μ)) (add_zero n) := by
  rw [Stacks.ExtCup.cup, Ext.comp_assoc_of_second_deg_zero,
    ← Ext.comp_assoc_of_third_deg_zero, mk₀_comp_mapExactFunctor_tensorRight_unit,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- **The cup product on `Ext^*(𝟙, 𝟙)` is anticommutative in odd degree**, under the
hypotheses of `Weil.Ext.comp_eq_negOnePow_smul_comp_of_unit_of_sign`: for
`a, b ∈ Ext^p(𝟙, 𝟙)` with `p` odd and any pairing `μ : 𝟙 ⊗ 𝟙 ⟶ T`, `a ∪_μ b = -(b ∪_μ a)`. -/
theorem cup_eq_neg_cup_of_odd_of_sign (P : C → Prop) (hunit : P (𝟙_ C))
    (hexact : ∀ X, P X → (tensorRight X).Additive ∧ PreservesFiniteLimits (tensorRight X) ∧
      PreservesFiniteColimits (tensorRight X))
    (hemb : ∀ X, P X → ∃ (S : CategoryTheory.ShortComplex C) (_ : S.ShortExact) (_ : S.X₁ ≅ X),
      Injective S.X₂ ∧ P S.X₂ ∧ P S.X₃)
    (hA : ∀ (S : CategoryTheory.ShortComplex C) (hS : S.ShortExact), P S.X₁ → P S.X₂ → P S.X₃ →
      ∀ (p : ℕ) (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) [(tensorRight S.X₁).Additive]
        [PreservesFiniteLimits (tensorRight S.X₁)] [PreservesFiniteColimits (tensorRight S.X₁)]
        [(tensorRight S.X₃).Additive] [PreservesFiniteLimits (tensorRight S.X₃)]
        [PreservesFiniteColimits (tensorRight S.X₃)],
        (Stacks.ExtUnitAction.action a S.X₃).comp hS.extClass rfl =
          ((-1 : ℤ) ^ p) • hS.extClass.comp (Stacks.ExtUnitAction.action a S.X₁) (add_comm 1 p))
    {T : C} (μ : 𝟙_ C ⊗ 𝟙_ C ⟶ T) {p n : ℕ} (hp : Odd p) (a b : Ext.{w} (𝟙_ C) (𝟙_ C) p)
    (h : p + p = n) :
    Stacks.ExtCup.cup μ a b h = -Stacks.ExtCup.cup μ b a h := by
  rw [cup_eq_comp_comp_mk₀, cup_eq_comp_comp_mk₀,
    comp_eq_negOnePow_smul_comp_of_unit_of_sign P hunit hexact hemb hA a b h h,
    (Nat.odd_mul.mpr ⟨hp, hp⟩).neg_one_pow, neg_one_zsmul, Ext.neg_comp, neg_neg]

end Cup

section SignNaturality

/-- The left unitor, as an isomorphism of short complexes `𝟙 ⊗ S ≅ S`. -/
@[simps]
def leftUnitorShortComplex (S : CategoryTheory.ShortComplex C)
    [(tensorLeft (𝟙_ C)).PreservesZeroMorphisms] : S.map (tensorLeft (𝟙_ C)) ≅ S where
  hom :=
    { τ₁ := (λ_ S.X₁).hom
      τ₂ := (λ_ S.X₂).hom
      τ₃ := (λ_ S.X₃).hom
      comm₁₂ := by simp
      comm₂₃ := by simp }
  inv :=
    { τ₁ := (λ_ S.X₁).inv
      τ₂ := (λ_ S.X₂).inv
      τ₃ := (λ_ S.X₃).inv
      comm₁₂ := by simp
      comm₂₃ := by simp }

/-- **From sign naturality of `- ⊗ S` to sign naturality of the action.** Let `S` be short
exact, with `- ⊗ S.X₁` and `- ⊗ S.X₃` exact, and `𝟙 ⊗ S` short exact. If the image of
`a ∈ Ext^p(𝟙, 𝟙)` under `- ⊗ S.X₃`, followed by the class of `𝟙 ⊗ S`, is `(-1)^p` times the class
of `𝟙 ⊗ S` followed by the image of `a` under `- ⊗ S.X₁`, then the same holds for the actions
`a · S.X₃`, `a · S.X₁` and the class of `S`: conjugate by the left unitor `𝟙 ⊗ S ≅ S`. -/
theorem action_comp_extClass_of_mapExactFunctor_comp_extClass
    {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact)
    [(tensorLeft (𝟙_ C)).PreservesZeroMorphisms] (hS₁ : (S.map (tensorLeft (𝟙_ C))).ShortExact)
    [(tensorRight S.X₁).Additive] [PreservesFiniteLimits (tensorRight S.X₁)]
    [PreservesFiniteColimits (tensorRight S.X₁)] [(tensorRight S.X₃).Additive]
    [PreservesFiniteLimits (tensorRight S.X₃)] [PreservesFiniteColimits (tensorRight S.X₃)]
    {p : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p)
    (hLA : (a.mapExactFunctor (tensorRight S.X₃)).comp hS₁.extClass rfl =
      ((-1 : ℤ) ^ p) • hS₁.extClass.comp (a.mapExactFunctor (tensorRight S.X₁)) (add_comm 1 p)) :
    (Stacks.ExtUnitAction.action a S.X₃).comp hS.extClass rfl =
      ((-1 : ℤ) ^ p) • hS.extClass.comp (Stacks.ExtUnitAction.action a S.X₁) (add_comm 1 p) := by
  have N₁ := hS₁.extClass_naturality hS (leftUnitorShortComplex S).hom
  have N₂ := hS.extClass_naturality hS₁ (leftUnitorShortComplex S).inv
  simp only [leftUnitorShortComplex_hom_τ₁, leftUnitorShortComplex_hom_τ₃,
    leftUnitorShortComplex_inv_τ₁, leftUnitorShortComplex_inv_τ₃] at N₁ N₂
  set A₁ := a.mapExactFunctor (tensorRight S.X₁)
  set A₃ := a.mapExactFunctor (tensorRight S.X₃)
  calc (Stacks.ExtUnitAction.action a S.X₃).comp hS.extClass rfl
      = (Ext.mk₀ (λ_ S.X₃).inv).comp
          (A₃.comp ((Ext.mk₀ (λ_ S.X₃).hom).comp hS.extClass (zero_add 1)) rfl)
            (zero_add (p + 1)) := by
        rw [Stacks.ExtUnitAction.action,
          Ext.comp_assoc (Ext.mk₀ _) _ _ (zero_add p) rfl (by lia : 0 + p + 1 = p + 1),
          Ext.comp_assoc A₃ _ _ (add_zero p) (zero_add 1) (by lia : p + 0 + 1 = p + 1)]
    _ = (Ext.mk₀ (λ_ S.X₃).inv).comp
          ((A₃.comp hS₁.extClass rfl).comp (Ext.mk₀ (λ_ S.X₁).hom) (add_zero (p + 1)))
            (zero_add (p + 1)) := by
        rw [← N₁, Ext.comp_assoc_of_third_deg_zero]
    _ = ((-1 : ℤ) ^ p) • (Ext.mk₀ (λ_ S.X₃).inv).comp
          ((hS₁.extClass.comp A₁ (add_comm 1 p)).comp (Ext.mk₀ (λ_ S.X₁).hom)
            (add_zero (p + 1))) (zero_add (p + 1)) := by
        rw [hLA, zsmul_comp, comp_zsmul]
    _ = ((-1 : ℤ) ^ p) • ((Ext.mk₀ (λ_ S.X₃).inv).comp hS₁.extClass (zero_add 1)).comp
          (A₁.comp (Ext.mk₀ (λ_ S.X₁).hom) (add_zero p)) (add_comm 1 p) := by
        rw [Ext.comp_assoc_of_third_deg_zero,
          Ext.comp_assoc (Ext.mk₀ _) _ _ (zero_add 1) (add_comm 1 p) (by lia : 0 + 1 + p = p + 1)]
    _ = ((-1 : ℤ) ^ p) • hS.extClass.comp (Stacks.ExtUnitAction.action a S.X₁) (add_comm 1 p) := by
        rw [← N₂, Ext.comp_assoc_of_second_deg_zero, Stacks.ExtUnitAction.action]

end SignNaturality

section GradedCommutativity

variable [EnoughInjectives C]

/-- **Sign naturality of the action.** Let `S` be a short exact sequence whose three objects
have exact tensor, such that `Z ⊗ -` is right exact and `Z ◁ S.f` is a monomorphism for every
`Z`. Then for `a ∈ Ext^p(𝟙, 𝟙)`, `(a · S.X₃) ∘ δ_S = (-1)^p δ_S ∘ (a · S.X₁)`: this is the sign
naturality of connecting classes (`Weil.mapExactFunctor_comp_extClass_eq_negOnePow_smul`) for the
objectwise short exact sequence of exact functors `- ⊗ S.X₁ ⟶ - ⊗ S.X₂ ⟶ - ⊗ S.X₃`, evaluated at
`𝟙` and conjugated by the left unitor. -/
theorem action_comp_extClass_eq_negOnePow_smul
    (hleft : ∀ Z : C, PreservesFiniteColimits (tensorLeft Z))
    {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact)
    [(tensorRight S.X₁).Additive] [PreservesFiniteLimits (tensorRight S.X₁)]
    [PreservesFiniteColimits (tensorRight S.X₁)] [(tensorRight S.X₂).Additive]
    [PreservesFiniteLimits (tensorRight S.X₂)] [PreservesFiniteColimits (tensorRight S.X₂)]
    [(tensorRight S.X₃).Additive] [PreservesFiniteLimits (tensorRight S.X₃)]
    [PreservesFiniteColimits (tensorRight S.X₃)]
    (hmono : ∀ Z : C, Mono (Z ◁ S.f)) {p : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) :
    (Stacks.ExtUnitAction.action a S.X₃).comp hS.extClass rfl =
      ((-1 : ℤ) ^ p) • hS.extClass.comp (Stacks.ExtUnitAction.action a S.X₁) (add_comm 1 p) := by
  have hw : ∀ Y, ((tensoringRight C).map S.f).app Y ≫ ((tensoringRight C).map S.g).app Y = 0 :=
    fun Y => by
      have := hleft Y
      change Y ◁ S.f ≫ Y ◁ S.g = 0
      rw [← whiskerLeft_comp, S.zero]
      exact (tensorLeft Y).map_zero _ _
  have hSY : ∀ Y, (CategoryTheory.ShortComplex.mk _ _ (hw Y)).ShortExact := fun Y => by
    have := hleft Y
    exact ShortComplex.shortExact_map_tensorLeft hS Y (hmono Y)
  have := hleft (𝟙_ C)
  exact action_comp_extClass_of_mapExactFunctor_comp_extClass hS (hSY (𝟙_ C)) a
    (mapExactFunctor_comp_extClass_eq_negOnePow_smul _ _ hw hSY a rfl (add_comm 1 p))

/-- **Graded commutativity of the Yoneda algebra `Ext^*(𝟙, 𝟙)`.** Let `P` be a class of objects
containing `𝟙`, whose objects have exact tensor and embed into injective objects of `P` with
cokernel in `P`, and on whose short exact sequences `Z ◁ -` stays injective on the first map,
`Z ⊗ -` being right exact for every `Z`. Then for `a ∈ Ext^p(𝟙, 𝟙)` and `b ∈ Ext^q(𝟙, 𝟙)`,
`a ∘ b = (-1)^{pq} b ∘ a`. -/
theorem comp_eq_negOnePow_smul_comp_of_unit (P : C → Prop) (hunit : P (𝟙_ C))
    (hexact : ∀ X, P X → (tensorRight X).Additive ∧ PreservesFiniteLimits (tensorRight X) ∧
      PreservesFiniteColimits (tensorRight X))
    (hemb : ∀ X, P X → ∃ (S : CategoryTheory.ShortComplex C) (_ : S.ShortExact) (_ : S.X₁ ≅ X),
      Injective S.X₂ ∧ P S.X₂ ∧ P S.X₃)
    (hleft : ∀ Z : C, PreservesFiniteColimits (tensorLeft Z))
    (hmono : ∀ S : CategoryTheory.ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      ∀ Z, Mono (Z ◁ S.f))
    {p q n : ℕ} (a : Ext.{w} (𝟙_ C) (𝟙_ C) p) (b : Ext.{w} (𝟙_ C) (𝟙_ C) q) (h : p + q = n)
    (h' : q + p = n) :
    a.comp b h = ((-1 : ℤ) ^ (p * q)) • b.comp a h' := by
  refine comp_eq_negOnePow_smul_comp_of_unit_of_sign P hunit hexact hemb
    (fun S hS h₁ h₂ h₃ p a _ _ _ _ _ _ => ?_) a b h h'
  obtain ⟨_, _, _⟩ := hexact _ h₂
  exact action_comp_extClass_eq_negOnePow_smul hleft hS (hmono S hS h₁ h₂ h₃) a

/-- **The cup product on `Ext^*(𝟙, 𝟙)` is anticommutative in odd degree**, under the hypotheses
of `Weil.Ext.comp_eq_negOnePow_smul_comp_of_unit`: for `a, b ∈ Ext^p(𝟙, 𝟙)` with `p` odd and
any pairing `μ : 𝟙 ⊗ 𝟙 ⟶ T`, `a ∪_μ b = -(b ∪_μ a)`. -/
theorem cup_eq_neg_cup_of_odd (P : C → Prop) (hunit : P (𝟙_ C))
    (hexact : ∀ X, P X → (tensorRight X).Additive ∧ PreservesFiniteLimits (tensorRight X) ∧
      PreservesFiniteColimits (tensorRight X))
    (hemb : ∀ X, P X → ∃ (S : CategoryTheory.ShortComplex C) (_ : S.ShortExact) (_ : S.X₁ ≅ X),
      Injective S.X₂ ∧ P S.X₂ ∧ P S.X₃)
    (hleft : ∀ Z : C, PreservesFiniteColimits (tensorLeft Z))
    (hmono : ∀ S : CategoryTheory.ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
      ∀ Z, Mono (Z ◁ S.f))
    [(tensorRight (𝟙_ C)).Additive] [PreservesFiniteLimits (tensorRight (𝟙_ C))]
    [PreservesFiniteColimits (tensorRight (𝟙_ C))]
    {T : C} (μ : 𝟙_ C ⊗ 𝟙_ C ⟶ T) {p n : ℕ} (hp : Odd p) (a b : Ext.{w} (𝟙_ C) (𝟙_ C) p)
    (h : p + p = n) :
    Stacks.ExtCup.cup μ a b h = -Stacks.ExtCup.cup μ b a h := by
  rw [cup_eq_comp_comp_mk₀, cup_eq_comp_comp_mk₀,
    comp_eq_negOnePow_smul_comp_of_unit P hunit hexact hemb hleft hmono a b h h,
    (Nat.odd_mul.mpr ⟨hp, hp⟩).neg_one_pow, neg_one_zsmul, Ext.neg_comp, neg_neg]

end GradedCommutativity

end Ext

end Weil
