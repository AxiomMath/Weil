module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantLAdicLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseKernelTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.ConstantSystem
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# The local factors of the constant ℓ-adic sheaf

Let `X` be a noetherian scheme, `ℓ` a prime and `ℤ_ℓ = (ℤ/ℓⁿ⁺¹ℤ)ₙ` the constant ℓ-adic sheaf on
the small étale site of `X`, whose level `n` is the extension by zero
`j_{X!}\underline{ℤ/ℓⁿ⁺¹ℤ}_X` of the constant sheaf from the final object. For a geometric point
`s` of `X` the stalk `(ℤ_ℓ)_s` is free of rank one over `ℤ_ℓ`, with basis the compatible family
of germs of the constant section `1`, and every endomorphism `a` of `s` acts on it as the
identity, since it carries the germ of a section at a neighbourhood `(U, u)` to its germ at
`(U, u ∘ a)` and the final neighbourhood has a unique lift of `s`. Hence
`det(1 - t^d · a | (ℤ_ℓ)_s) = 1 - t^d`, over `ℤ_ℓ` and over `ℚ_ℓ`. At a closed point `x` of a
scheme of finite type over a finite field, with `a` the geometric Frobenius and `d = deg x`, this
is the local factor `1 - T^{deg x}` of `L(X, ℚ_ℓ)`, so that `L(X, ℚ_ℓ)` is the Euler product
`∏_{x ∈ |X|} (1 - T^{deg x})⁻¹`.

## Main definitions

* `Weil.shriekFinalIsoConstant`: the extension by zero of the constant sheaf from the final
  object is the constant sheaf `R_X`, by an isomorphism carrying the generator to `1`.
* `Weil.shriekFinalStalkLinearEquiv`: the stalk of `j_{X!}\underline{R}_X` at a geometric point
  is `R`, the germ of the generator going to `1`.
* `Weil.constantSystemLevelTrivialization`: the finite-level stalks of the constant ℓ-adic sheaf
  are trivialised, compatibly with the transitions, by the germs of the generators.
* `Weil.constantSystemStalkBasis`, `Weil.constantSystemRationalStalkBasis`: bases of rank one of
  the ℓ-adic and rational stalks.

## Main results

* `Weil.stalkEnd_constantSystem`, `Weil.rationalStalkEnd_constantSystem`: an endomorphism of a
  geometric point acts as the identity on the stalk of the constant ℓ-adic sheaf.
* `Weil.charPowerSeries_stalkEnd_constantSystem`: `det(1 - t^d F) = 1 - t^d` over `ℤ_ℓ`.
* `Weil.charPowerSeries_rationalStalkFrobenius_constantSystem_residueDegree`: the local factor
  of the constant sheaf at a closed point `x` is `1 - T^{deg x}`.
* `Weil.rationalLFunction_constantSystem`: `L(X, ℚ_ℓ) = ∏_{x ∈ |X|} (1 - T^{deg x})⁻¹`.

## Implementation notes

The identification of `j_{X!}\underline{R}_X` with the constant sheaf is by corepresentability:
maps out of either are sections over the final object. The stalk of the constant sheaf is then
computed through Mathlib's identification of the fibre of a sheafification with that of the
presheaf, and the fibre of a constant presheaf with its value. The geometric point is algebraically
closed (the convention of the étale site used here); no connectedness and no rational point are
assumed.

## References

* [Freitag–Kiehl, *Étale Cohomology and the Weil Conjecture*, IV.1]
* [Stacks Project, Tag 03V7](https://stacks.math.columbia.edu/tag/03V7)
* [Stacks Project, Tag 03UX](https://stacks.math.columbia.edu/tag/03UX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Opposite

universe u

namespace Weil

section ConstantFinal

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type) [CommRing R]

/-- Sheafification of module presheaves on the small étale site, in the coefficient universe of
the constant ℓ-adic sheaf. -/
local instance smallEtaleHasSheafify :
    HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) :=
  SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X R

/-- Modules in the coefficient universe have `u`-small limits. -/
local instance moduleCatHasLimitsOfSize : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, 0, u + 1} R

/-- The constant sheaf `R_X` on the small étale site. -/
abbrev constantModuleSheafSmallEtale :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) :=
  (constantSheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)).obj
    (ModuleCat.of R (ULift.{u + 1} R))

/-- The section `1` of the constant sheaf over the final object. -/
def constantModuleSheafOne :
    (constantModuleSheafSmallEtale B X R).obj.obj (op (SmallEtale.final B X.1 X.property)) :=
  ((constantSheafAdj (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)
    (SmallEtale.finalIsTerminal B X.1 X.property)).unit.app
      (ModuleCat.of R (ULift.{u + 1} R))).hom (ULift.up 1)

theorem constantModuleSheafOne_eq :
    constantModuleSheafOne B X R =
      ((toSheafify (SmallEtale.topology B X.1 X.property)
        ((Functor.const _).obj (ModuleCat.of R (ULift.{u + 1} R)))).app
          (op (SmallEtale.final B X.1 X.property))).hom (ULift.up 1) := by
  rfl

/-- The level sheaf `j_{X!}\underline{R}_X` of the constant system: the extension by zero of the
constant sheaf from the final object. -/
abbrev shriekFinal : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) :=
  moduleShriekConstant.{u, 0, 0} B X R (SmallEtale.final B X.1 X.property)

/-- Two maps out of the constant sheaf agree if they agree on the section `1` over the final
object. -/
theorem constantModuleSheaf_hom_ext {F : Sheaf (SmallEtale.topology B X.1 X.property)
      (ModuleCat.{u + 1} R)} {φ₁ φ₂ : constantModuleSheafSmallEtale B X R ⟶ F}
    (h : (φ₁.hom.app (op (SmallEtale.final B X.1 X.property))).hom (constantModuleSheafOne B X R) =
      (φ₂.hom.app (op (SmallEtale.final B X.1 X.property))).hom (constantModuleSheafOne B X R)) :
    φ₁ = φ₂ := by
  apply ((constantSheafAdj (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)
    (SmallEtale.finalIsTerminal B X.1 X.property)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext x
  obtain ⟨r⟩ := x
  have hx : (ULift.up r : ULift.{u + 1} R) = r • ULift.up 1 := by
    ext; simp
  rw [hx]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, map_smul]
  exact congrArg (r • ·) h

/-- The map `R_X ⟶ j_{X!}\underline{R}_X` sending `1` to the generator. -/
def constantToShriekFinal : constantModuleSheafSmallEtale B X R ⟶ shriekFinal B X R :=
  ((constantSheafAdj (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)
    (SmallEtale.finalIsTerminal B X.1 X.property)).homEquiv _ _).symm
      (ModuleCat.ofHom ((LinearMap.toSpanSingleton R _
        (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property))).comp
          (ULift.moduleEquiv (R := R) (M := R)).toLinearMap))

theorem constantToShriekFinal_one :
    ((constantToShriekFinal B X R).hom.app (op (SmallEtale.final B X.1 X.property))).hom
        (constantModuleSheafOne B X R) =
      moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property) := by
  have h := ((constantSheafAdj (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)
    (SmallEtale.finalIsTerminal B X.1 X.property)).homEquiv _ _).apply_symm_apply
      (ModuleCat.ofHom ((LinearMap.toSpanSingleton R _
        (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property))).comp
          (ULift.moduleEquiv (R := R) (M := R)).toLinearMap))
  rw [Adjunction.homEquiv_unit] at h
  have h' := congrArg (fun φ => φ.hom (ULift.up (1 : R))) h
  simp only [Functor.flip_obj_obj, ObjectProperty.ι_obj, Functor.comp_obj, Functor.flip_obj_map,
    ObjectProperty.ι_map, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ConcreteCategory.hom_ofHom, LinearEquiv.coe_coe, ULift.moduleEquiv_apply,
    LinearMap.toSpanSingleton_apply, one_smul] at h'
  exact h'

/-- The map `j_{X!}\underline{R}_X ⟶ R_X` sending the generator to `1`. -/
def shriekFinalToConstant : shriekFinal B X R ⟶ constantModuleSheafSmallEtale B X R :=
  (moduleShriekConstantSectionEquiv.{u, 0, 0} B X R (SmallEtale.final B X.1 X.property) _).symm
    (constantModuleSheafOne B X R)

theorem shriekFinalToConstant_generator :
    ((shriekFinalToConstant B X R).hom.app (op (SmallEtale.final B X.1 X.property))).hom
        (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property)) =
      constantModuleSheafOne B X R := by
  rw [← moduleShriekConstantSectionEquiv_apply]
  exact Equiv.apply_symm_apply _ _

/-- **The extension by zero of the constant sheaf from the final object is the constant sheaf**
on the small étale site, by an isomorphism carrying the generator to the section `1`. -/
def shriekFinalIsoConstant : shriekFinal B X R ≅ constantModuleSheafSmallEtale B X R where
  hom := shriekFinalToConstant B X R
  inv := constantToShriekFinal B X R
  hom_inv_id := by
    apply (moduleShriekConstantSectionEquiv.{u, 0, 0} B X R
      (SmallEtale.final B X.1 X.property) _).injective
    rw [moduleShriekConstantSectionEquiv_apply, moduleShriekConstantSectionEquiv_apply]
    change ((constantToShriekFinal B X R).hom.app _).hom
      (((shriekFinalToConstant B X R).hom.app _).hom _) = _
    rw [shriekFinalToConstant_generator, constantToShriekFinal_one]
    rfl
  inv_hom_id := by
    apply constantModuleSheaf_hom_ext
    change ((shriekFinalToConstant B X R).hom.app _).hom
      (((constantToShriekFinal B X R).hom.app _).hom _) = _
    rw [constantToShriekFinal_one, shriekFinalToConstant_generator]
    rfl

variable (s : GeometricPoint X.1)

/-- The unique lift of a geometric point to the final object of the small étale site. -/
def geometricPointFinalLift :
    (geometricPointSitePoint B X.1 X.property s).fiber.obj (SmallEtale.final B X.1 X.property) :=
  ((geometricPointSitePoint B X.1 X.property s).uniqueFiberObj _
    (SmallEtale.finalIsTerminal B X.1 X.property)).default

theorem subsingleton_geometricPointFinalLift :
    Subsingleton
      ((geometricPointSitePoint B X.1 X.property s).fiber.obj
        (SmallEtale.final B X.1 X.property)) :=
  @Unique.instSubsingleton _ ((geometricPointSitePoint B X.1 X.property s).uniqueFiberObj _
    (SmallEtale.finalIsTerminal B X.1 X.property))

/-- The germ at a geometric point of the generator of `j_{X!}\underline{R}_X`, at the final
étale neighbourhood. -/
def shriekFinalGerm :
    ((geometricPointSitePoint B X.1 X.property s).presheafFiber
      (A := ModuleCat.{u + 1} R)).obj (shriekFinal B X R).obj :=
  ((geometricPointSitePoint B X.1 X.property s).toPresheafFiber _ (geometricPointFinalLift B X s)
    (shriekFinal B X R).obj).hom
      (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property))

/-- Sheafification does not change the stalk of the constant presheaf. -/
def constantModuleSheafStalkIso :
    (geometricPointSitePoint B X.1 X.property s).presheafFiber.obj
        (constantModuleSheafSmallEtale B X R).obj ≅
      (geometricPointSitePoint B X.1 X.property s).presheafFiber.obj
        ((Functor.const (SmallEtale B X.1 X.property)ᵒᵖ).obj
          (ModuleCat.of R (ULift.{u + 1} R))) :=
  ((geometricPointSitePoint B X.1 X.property s).presheafToSheafCompSheafFiberIso
    (ModuleCat.{u + 1} R)).app _

theorem constantModuleSheafStalkIso_inv :
    (constantModuleSheafStalkIso B X R s).inv =
      (geometricPointSitePoint B X.1 X.property s).presheafFiber.map
        (toSheafify _ ((Functor.const (SmallEtale B X.1 X.property)ᵒᵖ).obj
          (ModuleCat.of R (ULift.{u + 1} R)))) :=
  rfl

/-- The stalk of `j_{X!}\underline{R}_X` at a geometric point is `R`. -/
def shriekFinalStalkIso :
    (geometricPointSitePoint B X.1 X.property s).presheafFiber.obj (shriekFinal B X R).obj ≅
      ModuleCat.of R (ULift.{u + 1} R) :=
  (geometricPointSitePoint B X.1 X.property s).presheafFiber.mapIso
      ((sheafToPresheaf _ _).mapIso (shriekFinalIsoConstant B X R)) ≪≫
    constantModuleSheafStalkIso B X R s ≪≫
    CategoryTheory.Sites.constantPresheafFiberIso (geometricPointSitePoint B X.1 X.property s)
      (ModuleCat.of R (ULift.{u + 1} R))

theorem shriekFinalStalkIso_germ :
    (shriekFinalStalkIso B X R s).hom.hom (shriekFinalGerm B X R s) = ULift.up 1 := by
  set Φ := geometricPointSitePoint B X.1 X.property s
  set P := (Functor.const (SmallEtale B X.1 X.property)ᵒᵖ).obj
    (ModuleCat.of R (ULift.{u + 1} R))
  set i2 := constantModuleSheafStalkIso B X R s
  have hi2 : i2.inv = Φ.presheafFiber.map (toSheafify _ P) :=
    constantModuleSheafStalkIso_inv B X R s
  have hcomp : (shriekFinalStalkIso B X R s).hom =
      Φ.presheafFiber.map (shriekFinalToConstant B X R).hom ≫ i2.hom ≫
        (CategoryTheory.Sites.constantPresheafFiberIso Φ (ModuleCat.of R (ULift.{u + 1} R))).hom :=
    rfl
  have h1 : Φ.toPresheafFiber _ (geometricPointFinalLift B X s) (shriekFinal B X R).obj ≫
      Φ.presheafFiber.map (shriekFinalToConstant B X R).hom =
      (shriekFinalToConstant B X R).hom.app _ ≫
        Φ.toPresheafFiber _ (geometricPointFinalLift B X s)
          (constantModuleSheafSmallEtale B X R).obj :=
    (Φ.toPresheafFiber_naturality _ _ _)
  have h2 : Φ.toPresheafFiber _ (geometricPointFinalLift B X s) P ≫ i2.inv =
      (toSheafify _ P).app _ ≫
        Φ.toPresheafFiber _ (geometricPointFinalLift B X s)
          (constantModuleSheafSmallEtale B X R).obj := by
    rw [hi2]
    exact Φ.toPresheafFiber_naturality _ _ _
  have h3 := CategoryTheory.Sites.constantPresheafFiberIso_ι Φ (ModuleCat.of R (ULift.{u + 1} R))
    _ (geometricPointFinalLift B X s)
  have e1 := ConcreteCategory.congr_hom h1
    (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property))
  have e2 : i2.inv (Φ.toPresheafFiber _ (geometricPointFinalLift B X s) P (ULift.up 1)) =
      Φ.toPresheafFiber _ (geometricPointFinalLift B X s) (constantModuleSheafSmallEtale B X R).obj
        ((toSheafify _ P).app _ (ULift.up 1)) :=
    ConcreteCategory.congr_hom h2 (ULift.up 1)
  have e3 := ConcreteCategory.congr_hom h3 (ULift.up 1)
  simp only [ConcreteCategory.comp_apply] at e1 e3
  rw [shriekFinalToConstant_generator, constantModuleSheafOne_eq] at e1
  change (ConcreteCategory.hom (shriekFinalStalkIso B X R s).hom)
      ((ConcreteCategory.hom
        (Φ.toPresheafFiber _ (geometricPointFinalLift B X s) (shriekFinal B X R).obj))
        (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property))) = _
  rw [hcomp]
  simp only [ConcreteCategory.comp_apply]
  rw [e1]
  erw [← e2]
  rw [Iso.inv_hom_id_apply]
  exact e3

/-- The stalk of `j_{X!}\underline{R}_X` at a geometric point is free of rank one, with basis
the germ of the generator. -/
def shriekFinalStalkLinearEquiv :
    ((geometricPointSitePoint B X.1 X.property s).presheafFiber
      (A := ModuleCat.{u + 1} R)).obj (shriekFinal B X R).obj ≃ₗ[R] R :=
  (shriekFinalStalkIso B X R s).toLinearEquiv.trans ULift.moduleEquiv

theorem shriekFinalStalkLinearEquiv_germ :
    shriekFinalStalkLinearEquiv B X R s (shriekFinalGerm B X R s) = 1 := by
  change ((shriekFinalStalkIso B X R s).hom.hom (shriekFinalGerm B X R s)).down = 1
  rw [shriekFinalStalkIso_germ]

/-- Every element of the stalk of `j_{X!}\underline{R}_X` is a multiple of the germ of the
generator. -/
theorem eq_smul_shriekFinalGerm
    (y : ((geometricPointSitePoint B X.1 X.property s).presheafFiber
      (A := ModuleCat.{u + 1} R)).obj (shriekFinal B X R).obj) :
    y = shriekFinalStalkLinearEquiv B X R s y • shriekFinalGerm B X R s := by
  apply (shriekFinalStalkLinearEquiv B X R s).injective
  rw [map_smul, shriekFinalStalkLinearEquiv_germ, smul_eq_mul, mul_one]

/-- **An endomorphism of a geometric point acts as the identity on the stalk of
`j_{X!}\underline{R}_X`.** The germ of the generator at the final neighbourhood is carried to
the germ at the restricted neighbourhood, which is the same neighbourhood since the final
object has a unique lift of the point; and that germ is a basis of the stalk. -/
theorem geometricPointStalkMap_app_shriekFinal (a : GeometricPoint.Hom s s) :
    (geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} R)).app
      (shriekFinal B X R).obj = 𝟙 _ := by
  have hgerm : (geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} R)).app
      (shriekFinal B X R).obj (shriekFinalGerm B X R s) = shriekFinalGerm B X R s := by
    have h := colimit.ι_pre ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
      (shriekFinal B X R).obj) (neighborhoodFunctor B X.1 X.property a).op
      (op ⟨SmallEtale.final B X.1 X.property, geometricPointFinalLift B X s⟩)
    have e := ConcreteCategory.congr_hom h
      (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property))
    have hj : ∀ y z : (geometricPointSitePoint B X.1 X.property s).fiber.obj
        (SmallEtale.final B X.1 X.property),
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
          (shriekFinal B X R).obj) (op ⟨SmallEtale.final B X.1 X.property, y⟩)).hom
            (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property)) =
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
          (shriekFinal B X R).obj) (op ⟨SmallEtale.final B X.1 X.property, z⟩)).hom
            (moduleShriekConstantGenerator B X R (SmallEtale.final B X.1 X.property)) := by
      intro y z
      have := subsingleton_geometricPointFinalLift B X s
      obtain rfl : y = z := Subsingleton.elim _ _
      rfl
    exact e.trans (hj _ _)
  let V := ((geometricPointSitePoint B X.1 X.property s).presheafFiber
    (A := ModuleCat.{u + 1} R)).obj (shriekFinal B X R).obj
  let f : V →ₗ[R] V :=
    ((geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} R)).app
      (shriekFinal B X R).obj).hom
  have hf : f = LinearMap.id := by
    ext y
    change f y = y
    conv_lhs => rw [eq_smul_shriekFinalGerm B X R s y]
    rw [map_smul]
    change _ • (geometricPointStalkMap B X.1 X.property a (ModuleCat.{u + 1} R)).app
      (shriekFinal B X R).obj (shriekFinalGerm B X R s) = y
    rw [hgerm]
    exact (eq_smul_shriekFinalGerm B X R s y).symm
  ext y
  exact LinearMap.congr_fun hf y

end ConstantFinal

section ConstantSystem

open Stacks.EtaleCohomology Stacks.Frobenius

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime] [QuasiSeparatedSpace X.1]

/-- An endomorphism of a geometric point acts as the identity on every finite-level stalk of the
constant ℓ-adic sheaf. -/
theorem finiteLevelStalkEnd_constantSystem {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (n : ℕ) :
    finiteLevelStalkEnd B X ℓ (LAdicSheaf.constantSystem B X ℓ) a n = 𝟙 _ :=
  geometricPointStalkMap_app_shriekFinal B X (ZMod (ℓ ^ (n + 1))) s a

/-- **An endomorphism of a geometric point acts as the identity on the stalk `ℤ_ℓ` of the
constant ℓ-adic sheaf.** -/
theorem stalkEnd_constantSystem {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    LAdicSheaf.stalkEnd B X ℓ (LAdicSheaf.constantSystem B X ℓ) a = LinearMap.id := by
  ext v n
  change (finiteLevelStalkEnd B X ℓ (LAdicSheaf.constantSystem B X ℓ) a n).hom (v.1 n) = v.1 n
  rw [finiteLevelStalkEnd_constantSystem]
  rfl

/-- An endomorphism of a geometric point acts as the identity on the rational stalk of the
constant ℓ-adic sheaf. -/
theorem rationalStalkEnd_constantSystem {s : GeometricPoint X.1} (a : GeometricPoint.Hom s s) :
    LAdicSheaf.rationalStalkEnd B X ℓ (LAdicSheaf.constantSystem B X ℓ) a = LinearMap.id := by
  rw [LAdicSheaf.rationalStalkEnd, stalkEnd_constantSystem, LinearMap.baseChange_id]

/-- The transition between consecutive finite-level stalks of the constant ℓ-adic sheaf carries
the germ of the generator to the germ of the generator. -/
theorem stalkTransition_constantSystem_germ (s : GeometricPoint X.1) (n : ℕ) :
    LAdicSheaf.stalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n
        (shriekFinalGerm B X (ZMod (ℓ ^ (n + 1 + 1))) s) =
      shriekFinalGerm B X (ZMod (ℓ ^ (n + 1))) s := by
  let x : (geometricPointFiber B X.1 X.property s).obj (SmallEtale.final B X.1 X.property) :=
    geometricPointFinalLift B X s
  have h : colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
          ((LAdicSheaf.constantSystem B X ℓ).level (n + 1)).obj)
        (op ⟨SmallEtale.final B X.1 X.property, x⟩) ≫
      finiteLevelStalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n =
      ((LAdicSheaf.constantSystem B X ℓ).transition n).hom.app
          (op (SmallEtale.final B X.1 X.property)) ≫
        (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n)).map
          (colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
              ((LAdicSheaf.constantSystem B X ℓ).level n).obj)
            (op ⟨SmallEtale.final B X.1 X.property, x⟩)) := by
    rw [finiteLevelStalkTransition]
    erw [colimit.ι_map_assoc]
    congr 1
    exact ι_preservesColimitIso_inv (ModuleCat.restrictScalars (finiteLevelRingHom ℓ n))
      ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
        ((LAdicSheaf.constantSystem B X ℓ).level n).obj) _
  have e := ConcreteCategory.congr_hom h
    (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1))) (SmallEtale.final B X.1 X.property))
  have e' : (finiteLevelStalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n).hom
      (shriekFinalGerm B X (ZMod (ℓ ^ (n + 1 + 1))) s) =
      (colimit.ι ((CategoryOfElements.π (geometricPointFiber B X.1 X.property s)).op ⋙
          ((LAdicSheaf.constantSystem B X ℓ).level n).obj)
            (op ⟨SmallEtale.final B X.1 X.property, x⟩)).hom
        (((LAdicSheaf.shriekConstantTransition B X ℓ (SmallEtale.final B X.1 X.property) n).hom.app
          (op (SmallEtale.final B X.1 X.property))).hom
          (moduleShriekConstantGenerator B X (ZMod (ℓ ^ (n + 1 + 1)))
            (SmallEtale.final B X.1 X.property))) := e
  rw [LAdicSheaf.shriekConstantTransition_generator] at e'
  exact e'

/-- The transition of the constant ℓ-adic sheaf on finite-level stalks, read in the bases given
by the germs of the generators: it is the reduction `ℤ/ℓⁿ⁺²ℤ → ℤ/ℓⁿ⁺¹ℤ`. -/
theorem stalkTransition_constantSystem (s : GeometricPoint X.1) (n : ℕ)
    (y : finiteLevelStalk B X ℓ (LAdicSheaf.constantSystem B X ℓ) s (n + 1)) :
    LAdicSheaf.stalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n y =
      finiteLevelRingHom ℓ n (shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1 + 1))) s y) •
        shriekFinalGerm B X (ZMod (ℓ ^ (n + 1))) s := by
  set c := shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1 + 1))) s y
  have hy : y = c • shriekFinalGerm B X (ZMod (ℓ ^ (n + 1 + 1))) s :=
    eq_smul_shriekFinalGerm B X (ZMod (ℓ ^ (n + 1 + 1))) s y
  have h1 := congrArg
    (finiteLevelStalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n).hom hy
  have h2 := (finiteLevelStalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n).hom.map_smul
    c (shriekFinalGerm B X (ZMod (ℓ ^ (n + 1 + 1))) s)
  have h3 := stalkTransition_constantSystem_germ B X ℓ s n
  refine h1.trans (h2.trans ?_)
  change finiteLevelRingHom ℓ n c •
    (finiteLevelStalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n).hom
      (shriekFinalGerm B X (ZMod (ℓ ^ (n + 1 + 1))) s) = _
  exact congrArg (finiteLevelRingHom ℓ n c • ·) h3

/-- **The constant ℓ-adic sheaf has rank one at every geometric point**: the germs of the
generators trivialise its finite-level stalks compatibly with the transitions. -/
def constantSystemLevelTrivialization (s : GeometricPoint X.1) :
    LAdicSheaf.LevelTrivialization (LAdicSheaf.constantSystem B X ℓ) s 1 where
  equiv n := (shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1))) s).toAddEquiv.trans
    (LinearEquiv.funUnique (Fin 1) (ZMod (ℓ ^ (n + 1))) (ZMod (ℓ ^ (n + 1)))).symm.toAddEquiv
  transition n y := by
    funext i
    change shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1))) s
        (LAdicSheaf.stalkTransition B X ℓ (LAdicSheaf.constantSystem B X ℓ) s n y) =
      levelRingHom (n + 1) (shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1 + 1))) s y)
    have h1 := congrArg (shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1))) s)
      (stalkTransition_constantSystem B X ℓ s n y)
    have h2 := (shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1))) s).map_smul
      (finiteLevelRingHom ℓ n (shriekFinalStalkLinearEquiv B X (ZMod (ℓ ^ (n + 1 + 1))) s y))
      (shriekFinalGerm B X (ZMod (ℓ ^ (n + 1))) s)
    refine h1.trans (h2.trans ?_)
    rw [shriekFinalStalkLinearEquiv_germ, smul_eq_mul, mul_one]

/-- The basis of the stalk `ℤ_ℓ` of the constant ℓ-adic sheaf given by the compatible germs of
the generators. -/
def constantSystemStalkBasis (s : GeometricPoint X.1) :
    Module.Basis (Fin 1) ℤ_[ℓ] (LAdicSheaf.stalk B X ℓ (LAdicSheaf.constantSystem B X ℓ) s) :=
  (Pi.basisFun ℤ_[ℓ] (Fin 1)).map (constantSystemLevelTrivialization B X ℓ s).stalkEquiv.symm

/-- The basis of the rational stalk `ℚ_ℓ` of the constant ℓ-adic sheaf. -/
def constantSystemRationalStalkBasis (s : GeometricPoint X.1) :
    Module.Basis (Fin 1) ℚ_[ℓ]
      (LAdicSheaf.rationalStalkLeft B X ℓ (LAdicSheaf.constantSystem B X ℓ) s) :=
  (Pi.basisFun ℚ_[ℓ] (Fin 1)).map
    (constantSystemLevelTrivialization B X ℓ s).rationalStalkEquiv.symm

/-- **The transport of an endomorphism of a geometric point on the stalk of the constant ℓ-adic
sheaf has `det(1 - t^d F) = 1 - t^d` over `ℤ_ℓ`.** The stalk is free of rank one and the
transport is the identity. -/
@[weil "lem_fk401_constant_sheaf_frobenius_transport_trivial"]
theorem charPowerSeries_stalkEnd_constantSystem {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (d : ℕ) :
    charPowerSeries (LAdicSheaf.stalkEnd B X ℓ (LAdicSheaf.constantSystem B X ℓ) a) d =
      1 - (PowerSeries.X : PowerSeries ℤ_[ℓ]) ^ d :=
  charPowerSeries_eq_one_sub_X_pow_of_id (constantSystemStalkBasis B X ℓ s)
    (stalkEnd_constantSystem B X ℓ a) d

/-- The same on the rational stalk. -/
theorem charPowerSeries_rationalStalkEnd_constantSystem {s : GeometricPoint X.1}
    (a : GeometricPoint.Hom s s) (d : ℕ) :
    charPowerSeries (LAdicSheaf.rationalStalkEnd B X ℓ (LAdicSheaf.constantSystem B X ℓ) a) d =
      1 - (PowerSeries.X : PowerSeries ℚ_[ℓ]) ^ d :=
  charPowerSeries_eq_one_sub_X_pow_of_id (constantSystemRationalStalkBasis B X ℓ s)
    (rationalStalkEnd_constantSystem B X ℓ a) d

/-- The geometric Frobenius at a point with finite residue field acts on the rational stalk of
the constant ℓ-adic sheaf with characteristic series `1 - T^d`. -/
theorem charPowerSeries_rationalStalkFrobenius_constantSystem (x : X.1)
    (hx : Finite (X.1.residueField x)) (d : ℕ) :
    charPowerSeries (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.constantSystem B X ℓ) x hx)
        d = 1 - (PowerSeries.X : PowerSeries ℚ_[ℓ]) ^ d := by
  have := hx
  exact charPowerSeries_rationalStalkEnd_constantSystem B X ℓ _ d

variable {k : Type u} [Field k] [Finite k]

/-- **The local factor of the constant ℓ-adic sheaf at a closed point `x` is `1 - T^{deg x}`**:
this is the hypothesis of
`Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction_eq_constantLFunction` for the constant
sheaf. -/
@[weil "lem_fk401_constant_sheaf_frobenius_transport_trivial"]
theorem charPowerSeries_rationalStalkFrobenius_constantSystem_residueDegree
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : closedPoints X.1) :
    charPowerSeries
        (LAdicSheaf.rationalStalkFrobenius B X ℓ (LAdicSheaf.constantSystem B X ℓ) x.1
          (finite_residueField f x.1 x.2))
        (residueDegree f x.1) =
      1 - PowerSeries.X ^ (residueDegree f x.1) :=
  charPowerSeries_rationalStalkFrobenius_constantSystem B X ℓ x.1 _ _

/-- The L-function of the constant ℓ-adic sheaf is `∏_{x ∈ |X|} (1 - T^{deg x})⁻¹`. -/
theorem rationalLFunction_constantSystem (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] :
    LAdicSheaf.rationalLFunction B X ℓ (LAdicSheaf.constantSystem B X ℓ) f =
      constantLFunction f (Padic ℓ) :=
  LAdicSheaf.rationalLFunction_eq_constantLFunction B X ℓ _ f
    (charPowerSeries_rationalStalkFrobenius_constantSystem_residueDegree B X ℓ f)

end ConstantSystem

end Weil
