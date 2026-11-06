module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteConstantRepresentable
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Constant
public import Weil.Attr

/-!
# The constant group scheme

Let `X` be a scheme and `F` a finite group. The *constant group scheme* `F̃_X` is the `X`-scheme
`∐_{σ ∈ F} X`, made of `|F|` copies of `X`, with its fold map to `X`. Since finite coproducts of
schemes are universal, the fibre product `F̃_X ×_X F̃_X` is the disjoint union of the copies of
`X` indexed by `F × F`, and the multiplication maps the copy indexed by `(σ, τ)` identically onto
the copy indexed by `σ τ`. This makes `F̃_X` a group object of the category of `X`-schemes.

The constant group scheme `AlgebraicGeometry.constantGroupScheme F X` of the Stacks project
(Tag 03YW) is the base change `(∐_{σ ∈ F} Spec ℤ) ×_{Spec ℤ} X` of the constant group scheme over
`Spec ℤ`; this file identifies it, as a group object over `X`, with `∐_{σ ∈ F} X` and the
multiplication above.

## Main definitions

* `AlgebraicGeometry.sigmaConstOver X F` — the `X`-scheme `∐_{σ ∈ F} X`, as an object of
  `Over X`.
* `AlgebraicGeometry.sigmaConstOver.ι σ` — the copy of `X` indexed by `σ`, as an `X`-point.
* `AlgebraicGeometry.sigmaConstOver.instGrpObj` — the group object structure on `∐_{σ ∈ F} X`.
* `AlgebraicGeometry.constantGroupScheme.isoGrpSigmaConstOver` — the isomorphism of group objects
  over `X` between `∐_{σ ∈ F} X` and the constant group scheme `constantGroupScheme F X`.

## Main results

* `AlgebraicGeometry.sigmaConstOver.isColimit_tensorCopy` — `T ×_X F̃_X` is the disjoint
  union of `|F|` copies of `T`.
* `AlgebraicGeometry.sigmaConstOver.isColimit_tensorSelfCopy` — `F̃_X ×_X F̃_X` is the
  disjoint union of the copies `X → F̃_X ×_X F̃_X` indexed by `F × F`.
* `AlgebraicGeometry.sigmaConstOver.tensorSelfCopy_mul_left`,
  `AlgebraicGeometry.sigmaConstOver.lift_ι_mul` — the multiplication maps the copy indexed
  by `(σ, τ)` identically onto the copy indexed by `σ τ`.
* `AlgebraicGeometry.sigmaConstOver.toScheme_obj_splitObj`,
  `AlgebraicGeometry.sigmaConstOver.inclusion_map_splitObj_hom` — the underlying `X`-scheme
  is the split cover `Stacks.EtaleCohomology.splitObj` of the small étale site of `X`.
* `AlgebraicGeometry.constantGroupScheme.ι_isoSigmaConstOver_hom` — the identification maps the
  copy of `X` indexed by `σ` onto the copy `constantGroupScheme.point σ` indexed by `σ`.

## Implementation notes

The scheme `∐_{σ ∈ F} X` is defined for any `F : Type u`; finiteness of `F` is used for the
fibre product. The group object structure is taken in `Over X` with its cartesian monoidal
structure given by fibre products over `X`, the setting of Mathlib's group schemes.

The group axioms are checked on copies: a morphism out of `T ×_X F̃_X` is determined by its
restrictions to the copies `T → T ×_X F̃_X` indexed by `F`, by universality of finite coproducts
of schemes (`FinitaryPreExtensive.isUniversal_finiteCoproducts`), and iterating this reduces every
axiom to the corresponding identity in `F`. The unit is not part of the characterisation of the
Stacks project's group law, which only prescribes the multiplication on copies; it is recovered as
the unique idempotent `X`-point of a group object (`constantGroupScheme.point_one`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2.
* [Stacks Project, Tag 03YW](https://stacks.math.columbia.edu/tag/03YW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (F : Type u)

/-- The `X`-scheme `∐_{σ ∈ F} X` of `|F|` copies of `X`, with its fold map: the underlying
`X`-scheme of the constant group scheme `F̃_X`. -/
@[weil "def_fk102_constant_group_scheme"]
abbrev sigmaConstOver : Over X :=
  Over.mk (Sigma.desc fun _ : F ↦ 𝟙 X)

namespace sigmaConstOver

variable {X F}

lemma left_eq : (sigmaConstOver X F).left = ∐ fun _ : F ↦ X := rfl

lemma hom_eq : (sigmaConstOver X F).hom = Sigma.desc fun _ : F ↦ 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma sigmaι_hom (σ : F) :
    Sigma.ι (fun _ : F ↦ X) σ ≫ (sigmaConstOver X F).hom = 𝟙 X := by
  simp

/-- The copy of `X` indexed by `σ`, as an `X`-point of `F̃_X`. -/
def ι (σ : F) : 𝟙_ (Over X) ⟶ sigmaConstOver X F :=
  Over.homMk (Sigma.ι (fun _ : F ↦ X) σ) (by simp)

@[simp]
lemma ι_left (σ : F) : (ι (X := X) σ).left = Sigma.ι (fun _ : F ↦ X) σ := rfl

/-- Morphisms out of `F̃_X` are determined by their restrictions to the copies of `X`. -/
lemma hom_ext {Y : Over X} {f g : sigmaConstOver X F ⟶ Y}
    (h : ∀ σ, ι σ ≫ f = ι σ ≫ g) : f = g := by
  ext1
  refine Sigma.hom_ext _ _ fun σ ↦ ?_
  have := congr_arg (fun k ↦ k.left) (h σ)
  simpa using this

/-- The copy of `T` indexed by `σ` in `T ×_X F̃_X`, as a morphism of schemes. -/
def tensorCopy (T : Over X) (σ : F) : T.left ⟶ (T ⊗ sigmaConstOver X F).left :=
  pullback.lift (𝟙 T.left) (T.hom ≫ Sigma.ι (fun _ : F ↦ X) σ) (by simp)

@[reassoc (attr := simp)]
lemma tensorCopy_fst (T : Over X) (σ : F) :
    tensorCopy T σ ≫ pullback.fst T.hom (Sigma.desc fun _ : F ↦ 𝟙 X) = 𝟙 T.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma tensorCopy_snd (T : Over X) (σ : F) :
    tensorCopy T σ ≫ pullback.snd T.hom (Sigma.desc fun _ : F ↦ 𝟙 X) =
      T.hom ≫ Sigma.ι (fun _ : F ↦ X) σ :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma tensorCopy_self_fst (σ : F) :
    tensorCopy (sigmaConstOver X F) σ ≫
      pullback.fst (Sigma.desc fun _ : F ↦ 𝟙 X) (Sigma.desc fun _ : F ↦ 𝟙 X) = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma tensorCopy_self_snd (σ : F) :
    tensorCopy (sigmaConstOver X F) σ ≫
      pullback.snd (Sigma.desc fun _ : F ↦ 𝟙 X) (Sigma.desc fun _ : F ↦ 𝟙 X) =
      (Sigma.desc fun _ : F ↦ 𝟙 X) ≫ Sigma.ι (fun _ : F ↦ X) σ :=
  pullback.lift_snd _ _ _

lemma tensorCopy_eq (T : Over X) (σ : F) :
    tensorCopy T σ = (lift (𝟙 T) (toUnit T ≫ ι σ)).left := by
  apply pullback.hom_ext <;> simp [tensorCopy]

variable [Finite F]

/-- `T ×_X F̃_X` is the disjoint union of the copies of `T` indexed by `F`. -/
lemma isColimit_tensorCopy (T : Over X) :
    Nonempty (IsColimit (Cofan.mk _ (tensorCopy (F := F) T))) := by
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct fun _ : F ↦ X)
  exact hau.nonempty_isColimit_of_isPullback_left (fun _ ↦ 𝟙 X) (sigmaConstOver X F).hom
    T.hom (fun _ ↦ 𝟙 T.left) (fun _ ↦ T.hom) (fun _ ↦ IsPullback.id_horiz T.hom)
    (IsPullback.of_hasPullback T.hom (sigmaConstOver X F).hom) _ (Iso.refl _)
    (fun σ ↦ sigmaι_hom σ) (fun σ ↦ by change tensorCopy T σ ≫ 𝟙 _ ≫ _ = _; simp)
    (fun σ ↦ by change tensorCopy T σ ≫ 𝟙 _ ≫ _ = _; simp)

/-- Morphisms out of `T ×_X F̃_X` are determined by their restrictions to the copies of `T`. -/
lemma tensor_hom_ext {T Y : Over X} {f g : T ⊗ sigmaConstOver X F ⟶ Y}
    (h : ∀ σ, lift (𝟙 T) (toUnit T ≫ ι σ) ≫ f = lift (𝟙 T) (toUnit T ≫ ι σ) ≫ g) :
    f = g := by
  obtain ⟨hc⟩ := isColimit_tensorCopy (F := F) T
  ext1
  refine Cofan.IsColimit.hom_ext hc _ _ fun σ ↦ ?_
  change tensorCopy T σ ≫ _ = tensorCopy T σ ≫ _
  have := congr_arg (fun k ↦ k.left) (h σ)
  simpa [tensorCopy_eq] using this

/-- The copy of `X` indexed by `(σ, τ)` in `F̃_X ×_X F̃_X`, as a morphism of schemes. -/
def tensorSelfCopy (p : F × F) : X ⟶ (sigmaConstOver X F ⊗ sigmaConstOver X F).left :=
  Sigma.ι (fun _ : F ↦ X) p.1 ≫ tensorCopy (sigmaConstOver X F) p.2

omit [Finite F] in
lemma tensorSelfCopy_eq (σ τ : F) :
    tensorSelfCopy (σ, τ) = (lift (ι (X := X) σ) (ι τ)).left := by
  apply pullback.hom_ext
  · simpa [tensorSelfCopy] using (pullback.lift_fst _ _ _).symm
  · simpa [tensorSelfCopy] using (pullback.lift_snd _ _ _).symm

/-- `F̃_X ×_X F̃_X` is the disjoint union of `|F|²` copies of `X`, the copy indexed by `(σ, τ)`
being the `X`-point `(σ, τ)`. -/
@[weil "def_fk102_constant_group_scheme"]
lemma isColimit_tensorSelfCopy :
    Nonempty (IsColimit (Cofan.mk _ (tensorSelfCopy (X := X) (F := F)))) := by
  obtain ⟨hc⟩ := isColimit_tensorCopy (F := F) (sigmaConstOver X F)
  have h := Cofan.IsColimit.prod (fun _ : F ↦ Cofan.mk _ (Sigma.ι fun _ : F ↦ X))
    (fun _ ↦ coproductIsCoproduct _) (Cofan.mk _ (tensorCopy (sigmaConstOver X F))) hc
  exact ⟨(Cofan.isColimitEquivOfEquiv (Equiv.prodComm F F) _ h)⟩

variable [Group F]

/-- The multiplication of `F̃_X`, as a morphism of schemes: on the copy of `F̃_X` indexed by `τ`
in `F̃_X ×_X F̃_X`, the copy indexed by `σ` is mapped identically onto the copy indexed by
`σ τ`. -/
def mulLeft : (sigmaConstOver X F ⊗ sigmaConstOver X F).left ⟶
    (sigmaConstOver X F).left :=
  Cofan.IsColimit.desc (isColimit_tensorCopy (F := F) (sigmaConstOver X F)).some
    fun τ ↦ Sigma.desc fun σ ↦ Sigma.ι (fun _ : F ↦ X) (σ * τ)

lemma tensorCopy_mulLeft (τ : F) :
    tensorCopy (sigmaConstOver X F) τ ≫ mulLeft =
      Sigma.desc fun σ ↦ Sigma.ι (fun _ : F ↦ X) (σ * τ) :=
  Cofan.IsColimit.fac
    (isColimit_tensorCopy (F := F) (sigmaConstOver X F)).some
    (fun τ ↦ Sigma.desc fun σ ↦ Sigma.ι (fun _ : F ↦ X) (σ * τ)) τ

/-- The multiplication `F̃_X ×_X F̃_X → F̃_X`. -/
def mul : sigmaConstOver X F ⊗ sigmaConstOver X F ⟶ sigmaConstOver X F :=
  Over.homMk mulLeft <| by
    obtain ⟨hc⟩ := isColimit_tensorCopy (F := F) (sigmaConstOver X F)
    refine Cofan.IsColimit.hom_ext hc _ _ fun τ ↦ ?_
    change tensorCopy _ τ ≫ _ = tensorCopy _ τ ≫ _
    rw [← Category.assoc, tensorCopy_mulLeft]
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    simp [Over.tensorObj_hom]

/-- The inverse `F̃_X → F̃_X`, mapping the copy indexed by `σ` identically onto the copy indexed
by `σ⁻¹`. -/
def inv : sigmaConstOver X F ⟶ sigmaConstOver X F :=
  Over.homMk (Sigma.desc fun σ ↦ Sigma.ι (fun _ : F ↦ X) σ⁻¹) <| by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    simp

/-- The multiplication maps the copy indexed by `(σ, τ)` identically onto the copy indexed by
`σ τ`. -/
@[reassoc]
lemma lift_ι_mul (σ τ : F) : lift (ι σ) (ι τ) ≫ mul = ι (X := X) (σ * τ) := by
  ext1
  have : (lift (ι (X := X) σ) (ι τ)).left =
      Sigma.ι (fun _ : F ↦ X) σ ≫ tensorCopy (sigmaConstOver X F) τ := by
    apply pullback.hom_ext
    · simpa using pullback.lift_fst _ _ _
    · simpa using pullback.lift_snd _ _ _
  rw [Over.comp_left, this, Category.assoc]
  change _ ≫ tensorCopy _ τ ≫ mulLeft = _
  rw [tensorCopy_mulLeft]
  simp

/-- The multiplication, on `F̃_X ×_X F̃_X = ∐_{(σ, τ) ∈ F × F} X`
(`sigmaConstOver.isColimit_tensorSelfCopy`), maps the copy indexed by `(σ, τ)` identically
onto the copy indexed by `σ τ`. -/
@[weil "def_fk102_constant_group_scheme"]
lemma tensorSelfCopy_mul_left (σ τ : F) :
    tensorSelfCopy (σ, τ) ≫ (mul (X := X)).left = Sigma.ι (fun _ : F ↦ X) (σ * τ) := by
  rw [tensorSelfCopy_eq, ← Over.comp_left, lift_ι_mul, ι_left]

@[reassoc (attr := simp)]
lemma lift_comp_ι_mul {T : Over X} (t : T ⟶ 𝟙_ (Over X)) (σ τ : F) :
    lift (t ≫ ι σ) (t ≫ ι τ) ≫ mul = t ≫ ι (σ * τ) := by
  rw [← comp_lift, Category.assoc, lift_ι_mul]

omit [Finite F] in
@[reassoc (attr := simp)]
lemma ι_inv (σ : F) : ι σ ≫ inv = ι (X := X) σ⁻¹ := by
  ext1
  simp [inv]

/-- The constant group scheme is a group object of the category of `X`-schemes. -/
@[weil "def_fk102_constant_group_scheme"]
instance instGrpObj : GrpObj (sigmaConstOver X F) where
  one := ι 1
  mul := mul
  one_mul := by
    refine tensor_hom_ext fun σ ↦ ?_
    have := lift_comp_ι_mul (X := X) (𝟙 _) 1 σ
    simp only [Category.id_comp] at this
    simp [this]
  mul_one := by
    refine (cancel_epi (ρ_ _).inv).1 (hom_ext fun σ ↦ ?_)
    have e : ι σ ≫ (ρ_ (sigmaConstOver X F)).inv = lift (ι σ) (𝟙 _) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simp [comp_toUnit]
    have := lift_comp_ι_mul (X := X) (𝟙 _) σ 1
    simp only [Category.id_comp] at this
    rw [reassoc_of% e]
    simp [this]
  mul_assoc := by
    refine tensor_hom_ext fun ρ ↦ tensor_hom_ext fun τ ↦ hom_ext fun σ ↦ ?_
    have h₁ := lift_comp_ι_mul (X := X) (𝟙 _) σ τ
    have h₃ := lift_comp_ι_mul (X := X) (𝟙 _) (σ * τ) ρ
    have h₄ := lift_comp_ι_mul (X := X) (𝟙 _) σ (τ * ρ)
    simp only [Category.id_comp] at h₁ h₃ h₄
    simp [comp_lift_assoc, comp_toUnit_assoc, h₁, h₃, h₄, _root_.mul_assoc]
  inv := inv
  left_inv := hom_ext fun σ ↦ by
    have := lift_comp_ι_mul (X := X) (𝟙 _) σ⁻¹ σ
    simp only [Category.id_comp] at this
    simp [comp_lift_assoc, comp_toUnit_assoc, this]
  right_inv := hom_ext fun σ ↦ by
    have := lift_comp_ι_mul (X := X) (𝟙 _) σ σ⁻¹
    simp only [Category.id_comp] at this
    simp [comp_lift_assoc, comp_toUnit_assoc, this]



section SplitObj

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (hX : B.Contains X)

omit [Group F] in
/-- The underlying scheme of `sigmaConstOver X F` is the split cover `∐_{σ ∈ F} X` of the
small étale site of `X`. -/
lemma toScheme_obj_splitObj :
    (SmallEtale.toScheme B X hX).obj (splitObj B hX F) = (sigmaConstOver X F).left :=
  rfl

omit [Group F] in
/-- The structure morphism of the split cover is that of `sigmaConstOver X F`. -/
lemma inclusion_map_splitObj_hom :
    B.inclusion.map (splitObj B hX F).obj.hom = (sigmaConstOver X F).hom :=
  rfl

end SplitObj

end sigmaConstOver

/-! ### Comparison with the constant group scheme of the Stacks project -/

namespace constantGroupScheme

open Functor.LaxMonoidal MonObj

variable {X F} [Group F]

/-- The copy of `X` indexed by `σ` in the constant group scheme
`G_X = (∐_{σ ∈ F} Spec ℤ) ×_{Spec ℤ} X`, as an `X`-point. -/
def point (σ : F) : 𝟙_ (Over X) ⟶ (constantGroupScheme F X).X :=
  Over.homMk (pullback.lift (terminal.from X ≫ Sigma.ι (fun _ : F ↦ ⊤_ Scheme.{u}) σ) (𝟙 X)
    (terminal.hom_ext _ _)) (by exact (pullback.lift_snd _ _ _).trans (Category.id_comp _).symm)

lemma point_eq (σ : F) :
    point σ = ε (Over.pullback (terminal.from X)) ≫
      (Over.pullback (terminal.from X)).map (constantComponent F σ) := by
  ext1
  rw [Over.comp_left]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    erw [pullback.lift_fst, pullback.lift_fst]
    rw [← Category.assoc]
    congr 1
    exact terminal.hom_ext _ _
  · simp only [Category.assoc]
    erw [pullback.lift_snd, pullback.lift_snd]
    simp [Over.ε_pullback_left]

lemma lift_map_constantComponent_mul (σ τ : F) :
    lift (ε (Over.pullback (terminal.from X)) ≫
        (Over.pullback (terminal.from X)).map (constantComponent F σ))
      (ε (Over.pullback (terminal.from X)) ≫
        (Over.pullback (terminal.from X)).map (constantComponent F τ)) ≫
      Functor.LaxMonoidal.μ (Over.pullback (terminal.from X)) _ _ ≫
        (Over.pullback (terminal.from X)).map μ[constantSchemeOverIntegersObj F] =
    ε (Over.pullback (terminal.from X)) ≫
      (Over.pullback (terminal.from X)).map (constantComponent F (σ * τ)) := by
  let : (Over.pullback (terminal.from X)).Monoidal := Functor.Braided.toMonoidal
  rw [← comp_lift, Category.assoc, Functor.Monoidal.lift_μ_assoc, ← Functor.map_comp]
  congr 2
  exact (constantGroupSchemeStructure F).2 σ τ

/-- In the constant group scheme, the product of the copies indexed by `σ` and `τ` is the copy
indexed by `σ τ`. -/
lemma lift_point_mul (σ τ : F) :
    lift (point (X := X) σ) (point τ) ≫ μ[(constantGroupScheme F X).X] = point (σ * τ) := by
  have := lift_map_constantComponent_mul (X := X) σ τ
  simp only [← point_eq] at this
  change lift (point σ) (point τ) ≫ (Functor.LaxMonoidal.μ (Over.pullback (terminal.from X)) _ _ ≫
    (Over.pullback (terminal.from X)).map μ[constantSchemeOverIntegersObj F]) = _
  exact this

lemma point_one : point (X := X) (1 : F) = η[(constantGroupScheme F X).X] := by
  have h : point (X := X) (1 : F) * point 1 = point 1 := by
    rw [Hom.mul_def, lift_point_mul, _root_.mul_one]
  rw [mul_eq_left.mp h, Hom.one_def, toUnit_unit, Category.id_comp]

variable [Finite F]

/-- The constant group scheme `G_X` is the disjoint union of the copies of `X` indexed by `F`. -/
lemma isColimit_point :
    Nonempty (IsColimit (Cofan.mk _ fun σ : F ↦ (point (X := X) σ).left)) := by
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct fun _ : F ↦ ⊤_ Scheme.{u})
  exact hau.nonempty_isColimit_of_isPullback_right (fun _ ↦ 𝟙 _)
    (terminal.from (constantSchemeOverIntegers F)) (terminal.from X)
    (fun _ ↦ terminal.from X) (fun _ ↦ 𝟙 X) (fun _ ↦ IsPullback.id_vert (terminal.from X))
    (IsPullback.of_hasPullback _ _) _ (Iso.refl _) (fun _ ↦ terminal.hom_ext _ _)
    (fun σ ↦ by
      change pullback.lift _ _ _ ≫ 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      exact pullback.lift_fst _ _ _)
    (fun σ ↦ by
      change pullback.lift _ _ _ ≫ 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
      exact pullback.lift_snd _ _ _)

/-- The identification of the constant group scheme `G_X = (∐_{σ ∈ F} Spec ℤ) ×_{Spec ℤ} X`
with `∐_{σ ∈ F} X`, mapping copies to copies. -/
def isoSigmaConstOver : sigmaConstOver X F ≅ (constantGroupScheme F X).X :=
  Over.isoMk ((coproductIsCoproduct fun _ : F ↦ X).coconePointUniqueUpToIso
    (isColimit_point (X := X) (F := F)).some) <| by
    refine Sigma.hom_ext _ _ fun σ ↦ ?_
    have := (coproductIsCoproduct fun _ : F ↦ X).comp_coconePointUniqueUpToIso_hom
      (isColimit_point (X := X) (F := F)).some ⟨σ⟩
    simp only [Cofan.mk_pt, Cofan.mk_ι_app] at this
    rw [reassoc_of% this]
    exact (Over.w (point σ)).trans (by simp)

@[reassoc (attr := simp)]
lemma ι_isoSigmaConstOver_hom (σ : F) :
    sigmaConstOver.ι σ ≫ (isoSigmaConstOver (X := X) (F := F)).hom = point σ := by
  ext1
  have := (coproductIsCoproduct fun _ : F ↦ X).comp_coconePointUniqueUpToIso_hom
    (isColimit_point (X := X) (F := F)).some ⟨σ⟩
  simpa [isoSigmaConstOver] using this

instance : IsMonHom (isoSigmaConstOver (X := X) (F := F)).hom where
  one_hom := by
    change sigmaConstOver.ι 1 ≫ _ = _
    rw [ι_isoSigmaConstOver_hom, point_one]
  mul_hom := by
    refine sigmaConstOver.tensor_hom_ext fun τ ↦ sigmaConstOver.hom_ext fun σ ↦ ?_
    have h₁ : sigmaConstOver.ι σ ≫ lift (𝟙 _) (toUnit _ ≫ sigmaConstOver.ι τ) =
        lift (sigmaConstOver.ι (X := X) σ) (sigmaConstOver.ι τ) := by
      simp [comp_toUnit_assoc]
    rw [reassoc_of% h₁, reassoc_of% h₁]
    change lift _ _ ≫ sigmaConstOver.mul ≫ _ = _
    rw [sigmaConstOver.lift_ι_mul_assoc, ι_isoSigmaConstOver_hom, lift_map_assoc,
      ι_isoSigmaConstOver_hom, ι_isoSigmaConstOver_hom, lift_point_mul]

/-- **The constant group scheme is `∐_{σ ∈ F} X` with the multiplication mapping the copy
indexed by `(σ, τ)` identically onto the copy indexed by `σ τ`.** The constant group scheme
`G_X` of the Stacks project is isomorphic, as a group object over `X`, to `sigmaConstOver X F`
with its group law `sigmaConstOver.instGrpObj`. -/
@[weil "def_fk102_constant_group_scheme"]
def isoGrpSigmaConstOver : Grp.mk (sigmaConstOver X F) ≅ constantGroupScheme F X :=
  Grp.mkIso' isoSigmaConstOver

end constantGroupScheme

end AlgebraicGeometry
