module

public import Weil.Attr
public import WeilFrontier.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilFrontier.CategoryTheory.Sites.ConcreteSheafification
public import WeilFrontier.CategoryTheory.Sites.Plus
public import WeilFrontier.CategoryTheory.Sites.PlusFunctorialMap

/-!
# The plus construction is left exact

Let `A` be a commutative ring and `0 → F₁ → F₂ → F₃` (maps `α`, `β`) an exact sequence of
presheaves of abelian groups on the étale category `Et(A)`. Then the induced sequence
`0 → F̃₁ → F̃₂ → F̃₃` of plus presheaves is exact.

Exactness is checked objectwise. For a covering `𝔅` of `B` the sequence
`0 → F₁(𝔅) → F₂(𝔅) → F₃(𝔅)` of sections over `𝔅` is exact: injectivity is componentwise, and a
family `s ∈ F₂(𝔅)` killed by `β` is the image of the unique family `t` with `α(tᵢ) = sᵢ`, which
is compatible because the maps `α_D` are injective. The statement for `F̃(B)` follows from this,
since every element of `F̃(B)` is a single class `[𝔅, s]` and two classes are equal exactly when
they become equal on a common refinement.

## Main results

- `AlgebraicGeometry.EtaleCategory.coveringSectionsAddMonoidHom_injective`,
  `AlgebraicGeometry.EtaleCategory.coveringSectionsAddMonoidHom_exact`: left exactness of
  `𝔅 ↦ F(𝔅)`.
- `AlgebraicGeometry.EtaleCategory.addPlusConstruction.map_injective`,
  `AlgebraicGeometry.EtaleCategory.addPlusConstruction.map_exact`: left exactness of `F ↦ F̃(B)`.
- `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.mono_homOfHom`,
  `AlgebraicGeometry.EtaleCategory.AddPlusPresheaf.exact_homOfHom`: left exactness of `F ↦ F̃`,
  for exact sequences in the abelian category of presheaves.

## Implementation notes

Mathlib's `CategoryTheory.GrothendieckTopology.preserveFiniteLimits_plusFunctor` is the
analogous statement for the plus construction indexed by covering sieves; the plus construction
here is the colimit over the category of covering families, so the statement is proved directly.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w u v

open CategoryTheory

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}} {F₁ F₂ F₃ : Presheaf A AddCommGrpCat.{v}}

section Sections

variable {B : EtaleCategory A} {ι : Type w} {C : ι → EtaleCategory A}

/-- If the maps `α_U` are injective, so is `α_𝔅 : F₁(𝔅) → F₂(𝔅)`. -/
theorem coveringSectionsAddMonoidHom_injective {α : F₁ ⟶ F₂}
    (hα : ∀ U, Function.Injective (α.app U)) (g : ∀ i, B ⟶ C i) :
    Function.Injective (coveringSectionsAddMonoidHom α g) := fun _ _ h ↦
  Subtype.ext <| funext fun i ↦ hα (C i) (congrFun (congrArg Subtype.val h) i)

/-- If `0 → F₁(U) → F₂(U) → F₃(U)` is exact for every `U`, then
`F₁(𝔅) → F₂(𝔅) → F₃(𝔅)` is exact for every family `𝔅`. -/
theorem coveringSectionsAddMonoidHom_exact {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃}
    (hα : ∀ U, Function.Injective (α.app U)) (hαβ : ∀ U, Function.Exact (α.app U) (β.app U))
    (g : ∀ i, B ⟶ C i) :
    Function.Exact (coveringSectionsAddMonoidHom α g) (coveringSectionsAddMonoidHom β g) := by
  intro s
  constructor
  · intro hs
    have h : ∀ i, β.app (C i) (s.1 i) = 0 := fun i ↦ by
      simpa using congrFun (congrArg Subtype.val hs) i
    choose t ht using fun i ↦ ((hαβ (C i)) (s.1 i)).1 (h i)
    have hmem : t ∈ coveringSectionsAddSubgroup F₁ g := by
      rw [mem_coveringSectionsAddSubgroup_iff]
      intro i j D u v huv
      apply hα D
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ht, ht]
      exact map_eq_map_of_mem_coveringSections (F₂ ⋙ forget AddCommGrpCat) g s.2 u v huv
    exact ⟨⟨t, hmem⟩, Subtype.ext <| funext ht⟩
  · rintro ⟨t, rfl⟩
    refine Subtype.ext <| funext fun i ↦ ?_
    simp only [coveringSectionsAddMonoidHom_apply]
    exact (hαβ (C i) _).2 ⟨_, rfl⟩

end Sections

namespace addPlusConstruction

variable {B : EtaleCategory A}

private lemma map_mk_apply (α : F₁ ⟶ F₂) (𝔅 : Covering.{w} B)
    (s : coveringSectionsAddSubgroup F₁ 𝔅.map) :
    (map (B := B) α).hom (mk 𝔅 s) = mk 𝔅 (coveringSectionsAddMonoidHom α 𝔅.map s) :=
  map_mk α 𝔅 s

/-- If the maps `α_U` are injective, so is `α̃_B : F̃₁(B) → F̃₂(B)`. -/
theorem map_injective {α : F₁ ⟶ F₂} (hα : ∀ U, Function.Injective (α.app U)) :
    Function.Injective (map.{w} (B := B) α) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨𝔅, t, rfl⟩ := exists_mk x
  have hx' : mk 𝔅 (coveringSectionsAddMonoidHom α 𝔅.map t) = mk 𝔅 0 := by
    rw [map_zero, ← map_mk_apply]
    exact hx
  obtain ⟨𝔅₃, φ₁, φ₂, e⟩ := (mk_eq_mk_iff_exists F₂ _ _).1 hx'
  rw [map_zero] at e
  have e' : coveringSectionsAddMonoidHom α 𝔅₃.map (Covering.HomOver.sectionsAddMonoidHom F₁ φ₁ t)
      = 0 := by
    rw [← e]
    exact (DFunLike.congr_fun
      (Covering.HomOver.sectionsAddMonoidHom_comp_coveringSectionsAddMonoidHom φ₁ α) t).symm
  have h0 : Covering.HomOver.sectionsAddMonoidHom F₁ φ₁ t = 0 :=
    coveringSectionsAddMonoidHom_injective hα _ (e'.trans (map_zero _).symm)
  rw [← mk_sectionsAddMonoidHom φ₁, h0, map_zero]

/-- If `0 → F₁(U) → F₂(U) → F₃(U)` is exact for every `U`, then
`F̃₁(B) → F̃₂(B) → F̃₃(B)` is exact. -/
theorem map_exact {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃} (hα : ∀ U, Function.Injective (α.app U))
    (hαβ : ∀ U, Function.Exact (α.app U) (β.app U)) :
    Function.Exact (map.{w} (B := B) α) (map.{w} (B := B) β) := by
  intro y
  constructor
  · intro hy
    obtain ⟨𝔅, s, rfl⟩ := exists_mk y
    have hy' : mk 𝔅 (coveringSectionsAddMonoidHom β 𝔅.map s) = mk 𝔅 0 := by
      rw [map_zero, ← map_mk_apply]
      exact hy
    obtain ⟨𝔅₃, φ₁, φ₂, e⟩ := (mk_eq_mk_iff_exists F₃ _ _).1 hy'
    rw [map_zero] at e
    have e' : coveringSectionsAddMonoidHom β 𝔅₃.map
        (Covering.HomOver.sectionsAddMonoidHom F₂ φ₁ s) = 0 := by
      rw [← e]
      exact (DFunLike.congr_fun
        (Covering.HomOver.sectionsAddMonoidHom_comp_coveringSectionsAddMonoidHom φ₁ β) s).symm
    obtain ⟨t, ht⟩ := ((coveringSectionsAddMonoidHom_exact hα hαβ 𝔅₃.map) _).1 e'
    refine ⟨mk 𝔅₃ t, ?_⟩
    change (map α).hom (mk 𝔅₃ t) = _
    rw [map_mk_apply, ht, mk_sectionsAddMonoidHom]
  · rintro ⟨x, rfl⟩
    obtain ⟨𝔅, t, rfl⟩ := exists_mk x
    change (map β).hom ((map α).hom (mk 𝔅 t)) = 0
    rw [map_mk_apply, map_mk_apply,
      ((coveringSectionsAddMonoidHom_exact hα hαβ 𝔅.map) _).2 ⟨t, rfl⟩, map_zero]

end addPlusConstruction

namespace AddPlusPresheaf

/-- The morphism of plus presheaves induced by the zero morphism is zero. -/
lemma homOfHom_zero (P₁ : AddPlusPresheaf.{w} F₁) (P₂ : AddPlusPresheaf.{w} F₂) :
    homOfHom P₁ P₂ 0 = 0 := by
  refine NatTrans.ext (funext fun B ↦ AddCommGrpCat.hom_ext (addPlusConstruction.hom_ext
    (f := (addPlusConstruction.map (B := B) (0 : F₁ ⟶ F₂)).hom) (g := 0) fun 𝔅 t ↦ ?_))
  change (addPlusConstruction.map 0).hom (addPlusConstruction.mk 𝔅 t) = 0
  rw [addPlusConstruction.map_mk]
  convert map_zero (addPlusConstruction.mk (F := F₂) 𝔅)
  exact Subtype.ext <| funext fun i ↦ rfl

/-- If `α ≫ β = 0`, then `α̃ ≫ β̃ = 0`. -/
lemma homOfHom_comp_homOfHom_eq_zero (P₁ : AddPlusPresheaf.{w} F₁)
    (P₂ : AddPlusPresheaf.{w} F₂) (P₃ : AddPlusPresheaf.{w} F₃) {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃}
    (hαβ : α ≫ β = 0) : homOfHom P₁ P₂ α ≫ homOfHom P₂ P₃ β = 0 := by
  rw [← homOfHom_comp, hαβ, homOfHom_zero]

private lemma injective_app_of_mono {G₁ G₂ : Presheaf A AddCommGrpCat.{v}} (α : G₁ ⟶ G₂)
    [Mono α] (U : EtaleCategory A) : Function.Injective (α.app U) :=
  (AddCommGrpCat.mono_iff_injective (α.app U)).1 inferInstance

/-- **The plus construction preserves monomorphisms.** If `α : F₁ ⟶ F₂` is a monomorphism of
presheaves of abelian groups on `Et(A)`, so is `α̃ : F̃₁ ⟶ F̃₂`. -/
@[weil "lem_fk101_plus_left_exact"]
theorem mono_homOfHom (P₁ : AddPlusPresheaf.{w} F₁) (P₂ : AddPlusPresheaf.{w} F₂) (α : F₁ ⟶ F₂)
    [Mono α] : Mono (homOfHom P₁ P₂ α) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun B ↦ ?_
  exact (AddCommGrpCat.mono_iff_injective _).2
    (addPlusConstruction.map_injective (injective_app_of_mono α))

/-- **The plus construction is left exact.** If `0 → F₁ → F₂ → F₃` is an exact sequence of
presheaves of abelian groups on `Et(A)` (`α` a monomorphism and `F₁ → F₂ → F₃` exact), then
`F̃₁ → F̃₂ → F̃₃` is exact (and `α̃` is a monomorphism, `mono_homOfHom`). -/
@[weil "lem_fk101_plus_left_exact"]
theorem exact_homOfHom (P₁ : AddPlusPresheaf.{w} F₁) (P₂ : AddPlusPresheaf.{w} F₂)
    (P₃ : AddPlusPresheaf.{w} F₃) {α : F₁ ⟶ F₂} {β : F₂ ⟶ F₃} [Mono α] (hαβ : α ≫ β = 0)
    (h : (ShortComplex.mk α β hαβ).Exact) :
    (ShortComplex.mk (homOfHom P₁ P₂ α) (homOfHom P₂ P₃ β)
      (homOfHom_comp_homOfHom_eq_zero P₁ P₂ P₃ hαβ)).Exact := by
  rw [ShortComplex.exact_iff_forall_function_exact_app] at h ⊢
  exact fun B ↦ addPlusConstruction.map_exact (injective_app_of_mono α) h

end AddPlusPresheaf

end EtaleCategory

end AlgebraicGeometry
