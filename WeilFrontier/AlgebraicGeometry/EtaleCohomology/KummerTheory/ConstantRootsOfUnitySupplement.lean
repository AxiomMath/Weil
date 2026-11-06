module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.ConstantRootsOfUnitySupplement
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Attr

/-!
# `𝐙/n𝐙 ≅ μ_n` for a chosen primitive root of unity

Let `k` be an algebraically closed field, `n ≥ 1` an integer invertible in `k`, `ζ ∈ k` a
primitive `n`-th root of unity and `X` a `k`-scheme. On the small étale site of `X`, the
morphism of sheaves of abelian groups `(𝐙/n𝐙)_X → (μ_n)_X` sending the global section `1` to
(the image in `Γ(X, 𝒪_X)` of) `ζ` is an isomorphism.

There is exactly one morphism `(𝐙/n𝐙)_X → (μ_n)_X` sending `1` to `ζ`, since the constant sheaf
is the sheafification of the constant presheaf and a homomorphism out of `𝐙/n𝐙` is fixed by
the image of `1`. The isomorphism is obtained from the isomorphism
`AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheaf`, which is attached to some
identification `𝐙/n𝐙 ≅ μ_n(k)` sending `1` to a primitive root `ζ₀`, by precomposing with the
automorphism of `𝐙/n𝐙` given by multiplication by the class `j₀` with `ζ₀^{j₀} = ζ`
(a unit of `𝐙/n𝐙` since `ζ` is primitive).

## Main definitions

* `AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot`: the isomorphism
  `(𝐙/n𝐙)_X ≅ (μ_n)_X` attached to `ζ`.
* `AlgebraicGeometry.constantSheafOneSection`: the global section `1` of `(𝐙/n𝐙)_X`.

## Main results

* `AlgebraicGeometry.constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot_hom_one`: the
  isomorphism sends `1` to `ζ`.
* `AlgebraicGeometry.isIso_of_rootsOfUnity_app_one_eq`: every morphism
  `(𝐙/n𝐙)_X → (μ_n)_X` sending `1` to `ζ` is an isomorphism.

## Implementation notes

The site is the small étale site `SmallEtale B X hX` of `X` inside a big étale site `B`; the
constant sheaf is the sheafification of the constant presheaf with value `ULift (ZMod n)`, and
`μ_n` is the kernel of the `n`-th power map of the sheaf of units on that site. The hypothesis
that `n` is not divisible by the characteristic of `k` is written `IsUnit (n : k)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.5][FreitagKiehl]
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open ConstantRootsOfUnity

section

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}

/-- The root of unity `zeta` attached to `m • j` is the `m`-th power of the one attached to
`j`. -/
theorem ConstantRootsOfUnity.zeta_nsmul (hn : 0 < n) (hnk : IsUnit (n : k)) (m : ℕ)
    (j : ZMod n) :
    ((zeta k n hn hnk (m • j) : kˣ) : k) = ((zeta k n hn hnk j : kˣ) : k) ^ m := by
  unfold zeta
  rw [map_nsmul, toMul_nsmul]
  simp

/-- The residue class `j₀` with `zeta j₀ = ζ`, for a primitive `n`-th root of unity `ζ`, is
a unit of `𝐙/n𝐙`: there is `m` with `m * j₀ = 1`. -/
theorem ConstantRootsOfUnity.exists_mul_eq_one_of_isPrimitiveRoot (hn : 0 < n)
    (hnk : IsUnit (n : k)) {ζ : k} (hζ : IsPrimitiveRoot ζ n) {j₀ : ZMod n}
    (hj₀ : ((zeta k n hn hnk j₀ : kˣ) : k) = ζ) :
    ∃ m : ZMod n, m * j₀ = 1 ∧ j₀ * m = 1 := by
  have h1 : ((zeta k n hn hnk 1 : kˣ) : k) ^ n = 1 := by
    rw [← zeta_nsmul hn hnk, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    have : zeta k n hn hnk 0 = 1 := by
      unfold zeta
      simp
    rw [this, Units.val_one]
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hmul : (m : ZMod n) * j₀ = 1 := by
    apply zeta_injective k n hn hnk
    simp only
    rw [← nsmul_eq_mul, zeta_nsmul hn hnk, hj₀, hm]
  exact ⟨m, hmul, by rw [mul_comm]; exact hmul⟩

end

variable (B : BigEtaleSite.{u}) {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (hX : B.Contains X) {n : ℕ} (hn : 0 < n) (hnk : IsUnit (n : k))
  {ζ : k} (hζ : IsPrimitiveRoot ζ n)

/-- The residue class `j₀ ∈ 𝐙/n𝐙` with `zeta j₀ = ζ`. -/
def ConstantRootsOfUnity.zetaIndex : ZMod n :=
  (exists_zeta_eq k n hn hnk hζ.pow_eq_one).choose

theorem ConstantRootsOfUnity.zeta_zetaIndex :
    ((zeta k n hn hnk (zetaIndex hn hnk hζ) : kˣ) : k) = ζ :=
  (exists_zeta_eq k n hn hnk hζ.pow_eq_one).choose_spec

/-- Multiplication by `zetaIndex`, an automorphism of `𝐙/n𝐙`. -/
def ConstantRootsOfUnity.zetaIndexMulAddEquiv : ULift.{u} (ZMod n) ≃+ ULift.{u} (ZMod n) :=
  let h := exists_mul_eq_one_of_isPrimitiveRoot hn hnk hζ (zeta_zetaIndex hn hnk hζ)
  { toFun := fun x => ULift.up (zetaIndex hn hnk hζ * x.down)
    invFun := fun x => ULift.up (h.choose * x.down)
    left_inv := fun x => by
      apply ULift.ext
      simp only
      rw [← mul_assoc, h.choose_spec.1, one_mul]
    right_inv := fun x => by
      apply ULift.ext
      simp only
      rw [← mul_assoc, h.choose_spec.2, one_mul]
    map_add' := fun x y => by
      apply ULift.ext
      simp [mul_add] }

theorem ConstantRootsOfUnity.zetaIndexMulAddEquiv_apply_one :
    zetaIndexMulAddEquiv hn hnk hζ (ULift.up 1) = ULift.up (zetaIndex hn hnk hζ) := by
  apply ULift.ext
  change zetaIndex hn hnk hζ * 1 = zetaIndex hn hnk hζ
  rw [mul_one]

/-- The global section `1` of the constant sheaf `(𝐙/n𝐙)_X` on the small étale site. -/
def constantSheafOneSection :
    ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} (ZMod n)))).obj.obj (op (SmallEtale.final B X hX)) :=
  (toSheafify (SmallEtale.topology B X hX)
    ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n))))).app
      (op (SmallEtale.final B X hX)) (ULift.up 1)

/-- The value in `Γ(X, 𝒪_X)` of a global section of `μ_n`. -/
def rootsOfUnitySheafGlobalValue
    (s : (rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
      (unitsPresheaf_isSheaf_smallEtale B X hX) n).obj.obj (op (SmallEtale.final B X hX))) :
    Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX))) :=
  ((Additive.toMul ((kernel.ι (powerSheaf (SmallEtale.topology B X hX)
    (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom.app
      (op (SmallEtale.final B X hX)) s) : (Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj
        (SmallEtale.final B X hX))))ˣ) : Scheme.Γ.obj (op ((SmallEtale.toScheme B X hX).obj
          (SmallEtale.final B X hX))))

/-- **`(𝐙/n𝐙)_X ≅ (μ_n)_X`, `1 ↦ ζ`.** For a primitive `n`-th root of unity `ζ` of the
algebraically closed base field `k`, the isomorphism of étale sheaves of abelian groups on the
small étale site of the `k`-scheme `X` sending the global section `1` to `ζ`
(`constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot_hom_one`). -/
@[weil "lem_fk105_mu_n_isomorphic_constant_sheaf"]
def constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot :
    (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) ≅
      rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n :=
  (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).mapIso
      (zetaIndexMulAddEquiv hn hnk hζ).toAddCommGrpIso ≪≫
    constantZModSheafIsoRootsOfUnitySheaf B k f hX n hn hnk

/-- The isomorphism `constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot`, precomposed with
the unit of sheafification, is the automorphism `zetaIndexMulAddEquiv` followed by the
comparison `constToRoots`. -/
theorem toSheafify_comp_constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot_hom :
    toSheafify (SmallEtale.topology B X hX)
        ((Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n)))) ≫
      (constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot B f hX hn hnk hζ).hom.hom =
    (Functor.const (SmallEtale B X hX)ᵒᵖ).map
        (zetaIndexMulAddEquiv hn hnk hζ).toAddCommGrpIso.hom ≫
      constToRoots B k f hX n hn hnk := by
  have h1 : ∀ {A A' : AddCommGrpCat.{u}} (g : A ⟶ A'),
      ((constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map g).hom =
        sheafifyMap (D := AddCommGrpCat.{u}) _ ((Functor.const (SmallEtale B X hX)ᵒᵖ).map g) :=
    fun _ => rfl
  have h2 : ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
      (constToRoots B k f hX n hn hnk)).hom =
        sheafifyMap (D := AddCommGrpCat.{u}) _ (constToRoots B k f hX n hn hnk) := rfl
  simp only [constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot,
    constantZModSheafIsoRootsOfUnitySheaf, Iso.trans_hom, Functor.mapIso_hom,
    asIso_hom, ObjectProperty.FullSubcategory.comp_hom]
  have h3 : ∀ (hI : IsIso ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
      (constToRoots B k f hX n hn hnk))), (Iso.refl ((constantSheaf (SmallEtale.topology B X hX)
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} (ZMod n)))) ≪≫ @asIso _ _ _ _
        ((presheafToSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).map
          (constToRoots B k f hX n hn hnk)) hI).hom.hom =
      sheafifyMap (D := AddCommGrpCat.{u}) _ (constToRoots B k f hX n hn hnk) := fun _ => by
    rw [Iso.trans_hom, Iso.refl_hom, Category.id_comp]; exact h2
  rw [h1]
  erw [h3, ← toSheafify_naturality_assoc, ← toSheafify_naturality_assoc]
  rw [sheafificationAdjunction_counit_app_val, toSheafify_sheafifyLift, Category.comp_id]

/-- **`(𝐙/n𝐙)_X ≅ (μ_n)_X` sends `1` to `ζ`.** The isomorphism
`constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot` sends the global section `1` of
`(𝐙/n𝐙)_X` to the image of `ζ` in `Γ(X, 𝒪_X)`. -/
@[weil "lem_fk105_mu_n_isomorphic_constant_sheaf"]
theorem constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot_hom_one :
    rootsOfUnitySheafGlobalValue B hX
        ((constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot B f hX hn hnk hζ).hom.hom.app
          (op (SmallEtale.final B X hX)) (constantSheafOneSection B hX)) =
      structHom B k f hX (SmallEtale.final B X hX) ζ := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_comp_constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot_hom B f hX hn hnk hζ)
      (op (SmallEtale.final B X hX))) (ULift.up (1 : ZMod n))
  have h' := ConcreteCategory.congr_hom (NatTrans.congr_app (constToRoots_comp_ι B k f hX n hn hnk)
    (op (SmallEtale.final B X hX))) (ULift.up (zetaIndex hn hnk hζ))
  unfold rootsOfUnitySheafGlobalValue constantSheafOneSection
  erw [h]
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.const_map_app]
  erw [zetaIndexMulAddEquiv_apply_one]
  erw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h'
  erw [h', constToUnits_app_val, zeta_zetaIndex]

/-- A morphism of presheaves out of the constant presheaf with value `𝐙/n𝐙` on the small étale
site is determined by the image of `1` over `X` itself. -/
theorem constPresheaf_zmod_hom_ext {F : (SmallEtale B X hX)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {α β : (Functor.const (SmallEtale B X hX)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} (ZMod n))) ⟶ F}
    (h : α.app (op (SmallEtale.final B X hX)) (ULift.up 1) =
      β.app (op (SmallEtale.final B X hX)) (ULift.up 1)) :
    α = β := by
  have hfin : α.app (op (SmallEtale.final B X hX)) = β.app (op (SmallEtale.final B X hX)) := by
    ext x
    have hx : x = (x.down.cast : ℤ) • (ULift.up 1 : ULift.{u} (ZMod n)) := by
      apply ULift.ext
      change x.down = (x.down.cast : ℤ) • (1 : ZMod n)
      rw [zsmul_eq_mul, mul_one, ZMod.intCast_zmod_cast]
    rw [hx, map_zsmul, map_zsmul, h]
  ext T x
  have hα := ConcreteCategory.congr_hom
    (α.naturality ((SmallEtale.finalIsTerminal B X hX).from T.unop).op) x
  have hβ := ConcreteCategory.congr_hom
    (β.naturality ((SmallEtale.finalIsTerminal B X hX).from T.unop).op) x
  simp only [Functor.const_obj_map, ConcreteCategory.comp_apply, op_unop] at hα hβ
  rw [hfin] at hα
  exact hα.trans hβ.symm

/-- A morphism `(𝐙/n𝐙)_X ⟶ (μ_n)_X` is determined by the image of the global section `1`. -/
theorem constantSheaf_zmod_rootsOfUnitySheaf_hom_ext
    {φ ψ : (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) ⟶
      rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n}
    (h : rootsOfUnitySheafGlobalValue B hX
        (φ.hom.app (op (SmallEtale.final B X hX)) (constantSheafOneSection B hX)) =
      rootsOfUnitySheafGlobalValue B hX
        (ψ.hom.app (op (SmallEtale.final B X hX)) (constantSheafOneSection B hX))) :
    φ = ψ := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (rootsOfUnitySheaf (SmallEtale.topology B X hX)
    (SmallEtale.toScheme B X hX) (unitsPresheaf_isSheaf_smallEtale B X hX) n).property
  apply constPresheaf_zmod_hom_ext
  apply rootsSheaf_ι_app_injective B hX n
  apply Additive.toMul.injective
  apply Units.ext
  exact h

include hn hnk hζ in
/-- **`(𝐙/n𝐙)_X → (μ_n)_X`, `1 ↦ ζ`, is an isomorphism.** Let `k` be an algebraically closed
field, `n ≥ 1` invertible in `k`, `ζ ∈ k` a primitive `n`-th root of unity and `X` a
`k`-scheme. Every morphism of étale sheaves of abelian groups `(𝐙/n𝐙)_X ⟶ (μ_n)_X` sending the
global section `1` to `ζ` is an isomorphism; such a morphism exists
(`constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot`) and is unique
(`constantSheaf_zmod_rootsOfUnitySheaf_hom_ext`). -/
@[weil "lem_fk105_mu_n_isomorphic_constant_sheaf"]
theorem isIso_of_rootsOfUnitySheafGlobalValue_eq
    (φ : (constantSheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod n))) ⟶
      rootsOfUnitySheaf (SmallEtale.topology B X hX) (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n)
    (hφ : rootsOfUnitySheafGlobalValue B hX
        (φ.hom.app (op (SmallEtale.final B X hX)) (constantSheafOneSection B hX)) =
      structHom B k f hX (SmallEtale.final B X hX) ζ) :
    IsIso φ := by
  have : φ = (constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot B f hX hn hnk hζ).hom :=
    constantSheaf_zmod_rootsOfUnitySheaf_hom_ext B hX
      (hφ.trans
        (constantZModSheafIsoRootsOfUnitySheafOfIsPrimitiveRoot_hom_one B f hX hn hnk hζ).symm)
  rw [this]
  infer_instance

end AlgebraicGeometry
