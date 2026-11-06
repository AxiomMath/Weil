module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.CechCohomologyOfAnObject
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import WeilFrontier.CategoryTheory.Sites.Cohomology.Cech.ToSheafCohomology
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.Cech
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleSiteFirstCohomology
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOneEssentiallySmall

/-!
# The étale Picard group is the first Čech cohomology of the units

Let `S` be a noetherian separated scheme, `Et(S)` its category of noetherian separated étale
`S`-schemes and `𝒪^*_{S,et}` the presheaf of units `U ↦ Γ(U, 𝒪_U)^*` on `Et(S)`. The étale
Picard group `Pic_et(S)` is the group of isomorphism classes of étale line bundles, that is of
invertible `𝒪_{S,et}`-modules, under the tensor product.

A trivialization of an étale line bundle `L` is a covering `𝔘 = (U_i ⟶ S)_i` of `S` in `Et(S)`
together with generators `e_i` of `L` over the `U_i`. On `U_i ×_S U_j` there are unique units
`g_{ij}` with `e_i = g_{ij} e_j`; the family `g = (g_{ij})` is a Čech `1`-cocycle of `𝒪^*`, and
changing the generators, refining the covering or replacing `L` by an isomorphic module changes
it by a coboundary. This gives a map `κ : Pic_et(S) → Ȟ¹(S, 𝒪^*_{S,et})`, `[L] ↦ [g]_𝔘`. It is
additive, because `e_i ⊗ f_i` generates `L ⊗ M` with transition family `g h`; injective, because
if `g` is a coboundary the rescaled generators glue to a global generator, which trivializes
`L`; and surjective, because a cocycle `g` on `𝔘` is the transition family of the line bundle
`V ↦ {(a_i)_i | a_i ∈ Γ(V ×_S U_i, 𝒪), a_j = g_{ij} a_i on V ×_S U_i ×_S U_j}`. Hence `κ` is an
isomorphism of abelian groups.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.CechTrivialization`: a trivialization of an
  `𝒪_{S,et}`-module on a covering of `S` in `Et(S)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.CechTrivialization.IsTransition`: a degree-one
  cochain `g` is the transition family of a trivialization, `e_i = g_{ij} e_j`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.EtalePicardGroup`: the étale Picard group.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.etalePicardGroupAddEquivCechH1`: the
  isomorphism `κ : Pic_et(S) ≃+ Ȟ¹(S, 𝒪^*_{S,et})`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.cocycleBundle`: the line bundle of a cocycle.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.CechTrivialization.cechDifferential_eq_zero`:
  a transition family is a cocycle.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.CechTrivialization.cechH1Class_eq_cechH1Class`:
  the class of the transition family does not depend on the trivialization.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.etalePicardGroupAddEquivCechH1_etalePicardClass`:
  for every trivialization of an étale line bundle `L` with transition family `g`, the family
  `g` is a cocycle and `κ [L] = [g]_𝔘`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.etalePicardClass_add_etalePicardClass`: the
  group law of `Pic_et(S)` is the tensor product.

## Implementation notes

The modules live on the small étale site `AlgebraicGeometry.SmallEtale B S hS` and the Čech
cohomology on its full subcategory `Et(S)` of noetherian separated objects; the members of a
covering are carried into the small étale site by the inclusion. The étale Picard group is the
Picard group `Stacks.SheafOfModules.Picard.PicardGroup` of the small étale ringed site, whose
elements are the classes of invertible modules; these are exactly the étale line bundles
(`isEtaleLineBundle_of_isInvertible`, `isInvertible_of_isEtaleLineBundle`).

The fibre products `U_{i_0} ×_S ⋯ ×_S U_{i_p}` of the Čech complex are products over the final
object of `Et(S)`; maps into them from objects of the small étale site are produced by
`CechCovering.qlift`, and the transition relation and the cocycle relation are used at such
generalized points (`CechTrivialization.isTransition_iff`, `gAt_mul_gAt`). The line bundle of a
cocycle is the sheafification of the presheaf of compatible families; over each `U_k` this
presheaf is already isomorphic to `𝒪`, which is what makes the image of `e_k = (g_{ki})_i` a
generator (`isGenerator_sheafifySection`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Generalized points of the iterated fibre products of a covering -/

section Final

variable [IsNoetherian S] [S.IsSeparated]

namespace CechCovering

variable (𝔘 : CechCovering (final B S hS))

/-- The iterated fibre product `U_{ν₀} ×_S ⋯ ×_S U_{ν_p}` of the members of a covering of `S`,
as an object of `Et(S)`. -/
abbrev prodObj {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) :
    SmallNoetherianSeparatedEtale B S hS :=
  (∏ᶜ fun a ↦ Over.mk (𝔘.toPreZeroHypercover.f (ν a)) : Over (final B S hS)).left

/-- The projection `U_{ν₀} ×_S ⋯ ×_S U_{ν_p} ⟶ U_{ν_a}`. -/
abbrev prodπ {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) (a : Fin (p + 1)) :
    𝔘.prodObj ν ⟶ 𝔘.toPreZeroHypercover.X (ν a) :=
  (Pi.π (fun a ↦ Over.mk (𝔘.toPreZeroHypercover.f (ν a))) a).left

/-- The image of the iterated fibre product in the small étale site is again a product over the
final object. -/
private def isLimitMapCone {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) :
    IsLimit ((Over.post (X := final B S hS) (inclusion B S hS)).mapCone
      (limit.cone (Discrete.functor fun a ↦ Over.mk (𝔘.toPreZeroHypercover.f (ν a))))) :=
  isLimitOfPreserves _ (limit.isLimit _)

/-- An object of the small étale site, as an object over the final object. -/
private abbrev overFinal (T : SmallEtale B S hS) : Over ((inclusion B S hS).obj (final B S hS)) :=
  Over.mk ((SmallEtale.finalIsTerminal B S hS).from T)

private lemma comp_eq_from {T V : SmallEtale B S hS} (x : T ⟶ V)
    (y : V ⟶ (inclusion B S hS).obj (final B S hS)) :
    x ≫ y = (SmallEtale.finalIsTerminal B S hS).from T :=
  (SmallEtale.finalIsTerminal B S hS).hom_ext _ _

/-- The cone over the image of the product diagram given by maps `h a : T ⟶ U_{ν_a}`. -/
private def liftCone {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) {T : SmallEtale B S hS}
    (h : ∀ a, T ⟶ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X (ν a))) :
    Cone (Discrete.functor (fun a ↦ Over.mk (𝔘.toPreZeroHypercover.f (ν a))) ⋙
      Over.post (X := final B S hS) (inclusion B S hS)) where
  pt := overFinal T
  π := Discrete.natTrans fun a ↦ Over.homMk (h a.as) (comp_eq_from _ _)

/-- **The map into an iterated fibre product** given by its components `h a : T ⟶ U_{ν_a}`. -/
private def qlift {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) {T : SmallEtale B S hS}
    (h : ∀ a, T ⟶ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X (ν a))) :
    T ⟶ (inclusion B S hS).obj (𝔘.prodObj ν) :=
  ((𝔘.isLimitMapCone ν).lift (𝔘.liftCone ν h)).left

@[reassoc (attr := simp)]
private lemma qlift_π {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) {T : SmallEtale B S hS}
    (h : ∀ a, T ⟶ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X (ν a))) (a : Fin (p + 1)) :
    𝔘.qlift ν h ≫ (inclusion B S hS).map (𝔘.prodπ ν a) = h a := by
  have := (𝔘.isLimitMapCone ν).fac (𝔘.liftCone ν h) ⟨a⟩
  exact congrArg CommaMorphism.left this

private lemma hom_ext' {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) {T : SmallEtale B S hS}
    {x y : T ⟶ (inclusion B S hS).obj (𝔘.prodObj ν)}
    (h : ∀ a, x ≫ (inclusion B S hS).map (𝔘.prodπ ν a) =
      y ≫ (inclusion B S hS).map (𝔘.prodπ ν a)) : x = y := by
  let x' : overFinal T ⟶ (Over.post (X := final B S hS) (inclusion B S hS)).obj
      (∏ᶜ fun a ↦ Over.mk (𝔘.toPreZeroHypercover.f (ν a))) :=
    Over.homMk x (comp_eq_from _ _)
  let y' : overFinal T ⟶ (Over.post (X := final B S hS) (inclusion B S hS)).obj
      (∏ᶜ fun a ↦ Over.mk (𝔘.toPreZeroHypercover.f (ν a))) :=
    Over.homMk y (comp_eq_from _ _)
  have : x' = y' := (𝔘.isLimitMapCone ν).hom_ext fun ⟨a⟩ ↦
    Over.OverMorphism.ext (h a)
  exact congrArg CommaMorphism.left this

private lemma eq_qlift {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) {T : SmallEtale B S hS}
    (x : T ⟶ (inclusion B S hS).obj (𝔘.prodObj ν)) :
    x = 𝔘.qlift ν (fun a ↦ x ≫ (inclusion B S hS).map (𝔘.prodπ ν a)) :=
  𝔘.hom_ext' ν fun a ↦
    (𝔘.qlift_π ν (fun a ↦ x ≫ (inclusion B S hS).map (𝔘.prodπ ν a)) a).symm

private lemma comp_qlift {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀)
    {T T' : SmallEtale B S hS}
    (m : T' ⟶ T)
    (h : ∀ a, T ⟶ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X (ν a))) :
    m ≫ 𝔘.qlift ν h = 𝔘.qlift ν (fun a ↦ m ≫ h a) :=
  𝔘.hom_ext' ν fun a ↦ by rw [Category.assoc, qlift_π, qlift_π]

private lemma qlift_prodπ {p : ℕ} (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) :
    𝔘.qlift ν (fun a ↦ (inclusion B S hS).map (𝔘.prodπ ν a)) = 𝟙 _ :=
  𝔘.hom_ext' ν fun a ↦ by rw [qlift_π, Category.id_comp]

end CechCovering

end Final

/-! ### Units pulled back to generalized points -/

/-- A section of `𝒪^*` over an object `Q` of `Et(S)`, as a unit of the sections of the
private structure sheaf of the small étale site over `Q`. -/
def toUnits {Q : SmallNoetherianSeparatedEtale B S hS} (x : (unitsPresheaf B S hS).obj (op Q)) :
    ((SmallEtale.structureSheaf B S hS).obj.obj (op ((inclusion B S hS).obj Q)))ˣ :=
  Additive.toMul x

private lemma toUnits_injective {Q : SmallNoetherianSeparatedEtale B S hS} :
    Function.Injective (toUnits (B := B) (S := S) (hS := hS) (Q := Q)) :=
  Additive.toMul.injective

/-- A unit of `Γ(Q, 𝒪_Q)` for an object `Q` of `Et(S)`, pulled back along a morphism
`t : T ⟶ Q` of the small étale site to a unit of `Γ(T, 𝒪_T)`. -/
private def pullUnit {Q : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (x : (unitsPresheaf B S hS).obj (op Q)) (t : T ⟶ (inclusion B S hS).obj Q) :
    ((SmallEtale.structureSheaf B S hS).obj.obj (op T))ˣ :=
  Units.map ((SmallEtale.structureSheaf B S hS).obj.map t.op).hom.toMonoidHom (toUnits x)

private lemma val_pullUnit {Q : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (x : (unitsPresheaf B S hS).obj (op Q)) (t : T ⟶ (inclusion B S hS).obj Q) :
    (pullUnit x t : (SmallEtale.structureSheaf B S hS).obj.obj (op T)) =
      (SmallEtale.structureSheaf B S hS).obj.map t.op (toUnits x : _) :=
  rfl

private lemma pullUnit_comp {Q : SmallNoetherianSeparatedEtale B S hS} {T T' : SmallEtale B S hS}
    (x : (unitsPresheaf B S hS).obj (op Q)) (m : T' ⟶ T) (t : T ⟶ (inclusion B S hS).obj Q) :
    pullUnit x (m ≫ t) =
      Units.map ((SmallEtale.structureSheaf B S hS).obj.map m.op).hom.toMonoidHom
        (pullUnit x t) := by
  ext
  simp only [val_pullUnit, Units.coe_map, op_comp, Functor.map_comp, RingCat.hom_comp,
    RingHom.coe_comp, Function.comp_apply]
  rfl

private lemma pullUnit_map {Q Q' : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (x : (unitsPresheaf B S hS).obj (op Q)) (h : Q' ⟶ Q) (t : T ⟶ (inclusion B S hS).obj Q') :
    pullUnit ((unitsPresheaf B S hS).map h.op x) t = pullUnit x (t ≫ (inclusion B S hS).map h) := by
  ext
  simp only [val_pullUnit, op_comp, Functor.map_comp, RingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  rfl

private lemma pullUnit_id {Q : SmallNoetherianSeparatedEtale B S hS}
    (x : (unitsPresheaf B S hS).obj (op Q)) :
    pullUnit x (𝟙 ((inclusion B S hS).obj Q)) = toUnits x := by
  ext
  rw [val_pullUnit, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma pullUnit_add {Q : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (x y : (unitsPresheaf B S hS).obj (op Q)) (t : T ⟶ (inclusion B S hS).obj Q) :
    pullUnit (x + y) t = pullUnit x t * pullUnit y t :=
  map_mul _ _ _

private lemma pullUnit_zero {Q : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (t : T ⟶ (inclusion B S hS).obj Q) :
    pullUnit (0 : (unitsPresheaf B S hS).obj (op Q)) t = 1 :=
  map_one _

private lemma pullUnit_neg {Q : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (x : (unitsPresheaf B S hS).obj (op Q)) (t : T ⟶ (inclusion B S hS).obj Q) :
    pullUnit (-x) t = (pullUnit x t)⁻¹ :=
  map_inv _ _

private lemma pullUnit_sub {Q : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (x y : (unitsPresheaf B S hS).obj (op Q)) (t : T ⟶ (inclusion B S hS).obj Q) :
    pullUnit (x - y) t = pullUnit x t * (pullUnit y t)⁻¹ := by
  rw [sub_eq_add_neg, pullUnit_add, pullUnit_neg]

/-- A section of `𝒪^*` over an object of `Et(S)` is determined by its pullback along the
identity. -/
private lemma eq_of_pullUnit_id_eq {Q : SmallNoetherianSeparatedEtale B S hS}
    {x y : (unitsPresheaf B S hS).obj (op Q)}
    (h : pullUnit x (𝟙 _) = pullUnit y (𝟙 _)) : x = y := by
  rw [pullUnit_id, pullUnit_id] at h
  exact toUnits_injective h


end AlgebraicGeometry.SmallNoetherianSeparatedEtale

/-! ### Generators -/

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The sections of the structure sheaf of the small étale site form a commutative ring. -/
private instance structureSheaf_obj_obj_commRing (V : (SmallEtale B S hS)ᵒᵖ) :
    CommRing ((structureSheaf B S hS).obj.obj V) :=
  inferInstanceAs (CommRing Γ((toScheme B S hS).obj V.unop, ⊤))

namespace IsGenerator


variable {L : SmallEtale.OxetModule B S hS} {V : SmallEtale B S hS} {e : L.val.obj (op V)}

lemma bijective (he : SmallEtale.IsGenerator L V e) :
    Function.Bijective (fun a : (SmallEtale.structureSheaf B S hS).obj.obj (op V) ↦ a • e) := by
  have h := he (𝟙 V)
  rwa [op_id, PresheafOfModules.map_id] at h

lemma smul_left_injective (he : SmallEtale.IsGenerator L V e)
    {a b : (SmallEtale.structureSheaf B S hS).obj.obj (op V)} (h : a • e = b • e) : a = b :=
  he.bijective.1 h

/-- Two generators over the same object differ by a unique unit. -/
lemma existsUnique_unit_smul (he : SmallEtale.IsGenerator L V e) {e' : L.val.obj (op V)}
    (he' : SmallEtale.IsGenerator L V e') :
    ∃! a : ((SmallEtale.structureSheaf B S hS).obj.obj (op V))ˣ,
      e = (a : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) • e' := by
  obtain ⟨r, hr⟩ := he'.bijective.2 e
  obtain ⟨q, hq⟩ := he.bijective.2 e'
  simp only at hr hq
  have hqr : q * r = 1 := by
    apply he'.smul_left_injective
    rw [mul_smul, hr, hq, one_smul]
  refine ⟨⟨r, q, by rw [mul_comm]; exact hqr, hqr⟩, hr.symm, fun b hb ↦ Units.ext ?_⟩
  exact he'.smul_left_injective (hb.symm.trans hr.symm)

/-- A generator multiplied by a unit is a generator. -/
private lemma unit_smul (he : SmallEtale.IsGenerator L V e)
    (a : ((SmallEtale.structureSheaf B S hS).obj.obj (op V))ˣ) :
    SmallEtale.IsGenerator L V
      ((a : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) • e) := by
  intro W f
  have h := he f
  rw [PresheafOfModules.map_smul]
  let a' : ((SmallEtale.structureSheaf B S hS).obj.obj (op W))ˣ :=
    Units.map ((SmallEtale.structureSheaf B S hS).obj.map f.op).hom.toMonoidHom a
  have : (fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op W) ↦
      r • ((SmallEtale.structureSheaf B S hS).obj.map f.op
        (a : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) • L.val.map f.op e)) =
      (fun r ↦ r • L.val.map f.op e) ∘
        (fun r ↦ r * (a' : (SmallEtale.structureSheaf B S hS).obj.obj (op W))) := by
    funext r
    simp only [Function.comp_apply, mul_smul]
    rfl
  rw [this]
  refine h.comp (Function.bijective_iff_has_inverse.mpr
    ⟨fun r ↦ r * ((a'⁻¹ : _) : (SmallEtale.structureSheaf B S hS).obj.obj (op W)),
      fun r ↦ Units.mul_inv_cancel_right r a', fun r ↦ Units.inv_mul_cancel_right r a'⟩)

end IsGenerator

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Restriction of sections of an `𝒪_{S,et}`-module, with its target typed as the sections
over the source of the arrow. -/
abbrev _root_.AlgebraicGeometry.SmallEtale.OxetModule.res (L : SmallEtale.OxetModule B S hS)
    {U V : SmallEtale B S hS} (f : V ⟶ U) (x : L.val.obj (op U)) : L.val.obj (op V) :=
  L.val.map f.op x

private lemma _root_.AlgebraicGeometry.SmallEtale.OxetModule.res_comp
    (L : SmallEtale.OxetModule B S hS) {U V W : SmallEtale B S hS} (f : W ⟶ V) (g : V ⟶ U)
    (x : L.val.obj (op U)) : L.res (f ≫ g) x = L.res f (L.res g x) := by
  simp only [SmallEtale.OxetModule.res, op_comp, PresheafOfModules.map_comp_apply]
  rfl

private lemma _root_.AlgebraicGeometry.SmallEtale.OxetModule.res_id
    (L : SmallEtale.OxetModule B S hS) {U : SmallEtale B S hS}
    (x : L.val.obj (op U)) : L.res (𝟙 U) x = x := by
  simp only [SmallEtale.OxetModule.res, op_id, PresheafOfModules.map_id]
  rfl

private lemma _root_.AlgebraicGeometry.SmallEtale.OxetModule.res_smul
    (L : SmallEtale.OxetModule B S hS) {U V : SmallEtale B S hS} (f : V ⟶ U)
    (a : (SmallEtale.structureSheaf B S hS).obj.obj (op U)) (x : L.val.obj (op U)) :
    L.res f (a • x) = (SmallEtale.structureSheaf B S hS).obj.map f.op a • L.res f x :=
  PresheafOfModules.map_smul _ _ _ _

/-- A unit of the sections of the structure sheaf over an object `Q` of `Et(S)`, as a section of
`𝒪^*` over `Q`. -/
def ofUnits {Q : SmallNoetherianSeparatedEtale B S hS}
    (a : ((SmallEtale.structureSheaf B S hS).obj.obj (op ((inclusion B S hS).obj Q)))ˣ) :
    (unitsPresheaf B S hS).obj (op Q) :=
  Additive.ofMul (a : (Γ((toScheme B S hS).obj Q, ⊤))ˣ)

@[simp]
lemma toUnits_ofUnits {Q : SmallNoetherianSeparatedEtale B S hS}
    (a : ((SmallEtale.structureSheaf B S hS).obj.obj (op ((inclusion B S hS).obj Q)))ˣ) :
    toUnits (ofUnits a) = a :=
  rfl


section Units

private lemma toUnits_add {Q : SmallNoetherianSeparatedEtale B S hS}
    (x y : (unitsPresheaf B S hS).obj (op Q)) : toUnits (x + y) = toUnits x * toUnits y :=
  rfl

private lemma toUnits_sub {Q : SmallNoetherianSeparatedEtale B S hS}
    (x y : (unitsPresheaf B S hS).obj (op Q)) : toUnits (x - y) = toUnits x * (toUnits y)⁻¹ :=
  rfl

private lemma toUnits_zero {Q : SmallNoetherianSeparatedEtale B S hS} :
    toUnits (0 : (unitsPresheaf B S hS).obj (op Q)) = 1 :=
  rfl

private lemma toUnits_map {Q Q' : SmallNoetherianSeparatedEtale B S hS} (h : Q' ⟶ Q)
    (x : (unitsPresheaf B S hS).obj (op Q)) :
    toUnits ((unitsPresheaf B S hS).map h.op x) = pullUnit x ((inclusion B S hS).map h) := by
  rw [← pullUnit_id, pullUnit_map, Category.id_comp]

private lemma pullUnit_ofUnits {Q : SmallNoetherianSeparatedEtale B S hS} {T : SmallEtale B S hS}
    (a : ((SmallEtale.structureSheaf B S hS).obj.obj (op ((inclusion B S hS).obj Q)))ˣ)
    (t : T ⟶ (inclusion B S hS).obj Q) :
    pullUnit (ofUnits a) t =
      Units.map ((SmallEtale.structureSheaf B S hS).obj.map t.op).hom.toMonoidHom a :=
  rfl

end Units

section Trivialization

variable [IsNoetherian S] [S.IsSeparated]

/-- **Čech trivializations of an `𝒪_{S,et}`-module.** A covering `(U_i ⟶ S)_{i}` of `S` in
`Et(S)` (finite, by noetherian separated étale `S`-schemes) together with a generator `e_i` of
the module over each `U_i`. -/
structure CechTrivialization (L : SmallEtale.OxetModule B S hS) where
  /-- The covering `(U_i ⟶ S)_i`. -/
  covering : CechCovering (final B S hS)
  /-- The generator `e_i ∈ L(U_i)`. -/
  generator : ∀ i : covering.toPreZeroHypercover.I₀,
    L.val.obj (op ((inclusion B S hS).obj (covering.toPreZeroHypercover.X i)))
  /-- Each `e_i` generates the module over `U_i`. -/
  isGenerator : ∀ i, SmallEtale.IsGenerator L _ (generator i)

namespace CechTrivialization

variable {L : SmallEtale.OxetModule B S hS} (T : CechTrivialization L)

/-- The degree-one Čech cochains of `𝒪^*` on the covering of a trivialization, as families. -/
abbrev Cochain (𝔘 : CechCovering (final B S hS)) (p : ℕ) :=
  Stacks.CechSite.cechCochain 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) p

/-- **Transition families.** A degree-one cochain `g = (g_{ij})` is the transition family of the
trivialization if `e_i = g_{ij} e_j` on `U_i ×_S U_j` for all `i, j`. -/
def IsTransition (g : Cochain T.covering 1) : Prop :=
  ∀ ν : Fin 2 → T.covering.toPreZeroHypercover.I₀,
    L.res ((inclusion B S hS).map (T.covering.prodπ ν 0)) (T.generator (ν 0)) =
      ((toUnits (g ν) : ((SmallEtale.structureSheaf B S hS).obj.obj
        (op ((inclusion B S hS).obj (T.covering.prodObj ν))))ˣ) :
          (SmallEtale.structureSheaf B S hS).obj.obj
            (op ((inclusion B S hS).obj (T.covering.prodObj ν)))) •
        L.res ((inclusion B S hS).map (T.covering.prodπ ν 1)) (T.generator (ν 1))

/-- The transition relation read at generalized points: for `h₀ : V ⟶ U_i`, `h₁ : V ⟶ U_j`,
`e_i|_V = g_{ij}(h₀, h₁) e_j|_V`. -/
private lemma isTransition_iff (g : Cochain T.covering 1) :
    T.IsTransition g ↔ ∀ (ν : Fin 2 → T.covering.toPreZeroHypercover.I₀) (V : SmallEtale B S hS)
      (h : ∀ a, V ⟶ (inclusion B S hS).obj (T.covering.toPreZeroHypercover.X (ν a))),
      L.res (h 0) (T.generator (ν 0)) =
        ((pullUnit (g ν) (T.covering.qlift ν h) : _) :
          (SmallEtale.structureSheaf B S hS).obj.obj (op V)) •
          L.res (h 1) (T.generator (ν 1)) := by
  constructor
  · intro hg ν V h
    have e0 : h 0 = T.covering.qlift ν h ≫ (inclusion B S hS).map (T.covering.prodπ ν 0) :=
      (T.covering.qlift_π ν h 0).symm
    have e1 : h 1 = T.covering.qlift ν h ≫ (inclusion B S hS).map (T.covering.prodπ ν 1) :=
      (T.covering.qlift_π ν h 1).symm
    rw [e0, e1, L.res_comp, L.res_comp, hg ν, L.res_smul]
    rfl
  · intro hg ν
    have := hg ν _ (fun a ↦ (inclusion B S hS).map (T.covering.prodπ ν a))
    rw [T.covering.qlift_prodπ, pullUnit_id] at this
    exact this

/-- The restriction of a generator of a trivialization along `h : V ⟶ U_i` is a generator. -/
lemma isGenerator_map {i : T.covering.toPreZeroHypercover.I₀} {V : SmallEtale B S hS}
    (h : V ⟶ (inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i)) :
    SmallEtale.IsGenerator L V (L.res h (T.generator i)) :=
  (T.isGenerator i).restrict h

/-- The transition family of a trivialization is unique. -/
lemma isTransition_unique {g g' : Cochain T.covering 1} (hg : T.IsTransition g)
    (hg' : T.IsTransition g') : g = g' := by
  funext ν
  apply toUnits_injective
  apply Units.ext
  apply (T.isGenerator_map ((inclusion B S hS).map (T.covering.prodπ ν 1))).smul_left_injective
  exact (hg ν).symm.trans (hg' ν)

/-- **The transition family** `g_{ij}` of a trivialization: the unique units with
`e_i = g_{ij} e_j` on `U_i ×_S U_j`. -/
def transition : Cochain T.covering 1 := fun ν ↦
  ofUnits (Classical.choose
    ((T.isGenerator_map ((inclusion B S hS).map (T.covering.prodπ ν 0))).existsUnique_unit_smul
      (T.isGenerator_map ((inclusion B S hS).map (T.covering.prodπ ν 1)))).exists)

lemma isTransition_transition : T.IsTransition T.transition := fun ν ↦
  Classical.choose_spec
    ((T.isGenerator_map ((inclusion B S hS).map (T.covering.prodπ ν 0))).existsUnique_unit_smul
      (T.isGenerator_map ((inclusion B S hS).map (T.covering.prodπ ν 1)))).exists

end CechTrivialization


/-- The face maps of the iterated fibre products, at generalized points. -/
private lemma CechCovering.map_faceProjection_left (𝔘 : CechCovering (final B S hS)) {p : ℕ}
    (k : Fin (p + 2) → 𝔘.toPreZeroHypercover.I₀) (j : Fin (p + 2)) :
    (inclusion B S hS).map (Stacks.CechSite.faceProjection 𝔘.toPreZeroHypercover k j).left =
      𝔘.qlift (fun b ↦ k (j.succAbove b))
        (fun b ↦ (inclusion B S hS).map (𝔘.prodπ k (j.succAbove b))) := by
  refine 𝔘.hom_ext' _ fun b ↦ ?_
  rw [CechCovering.qlift_π, ← Functor.map_comp]
  exact congrArg (fun f : _ ⟶ Over.mk (𝔘.toPreZeroHypercover.f (k (j.succAbove b))) ↦
    (inclusion B S hS).map f.left)
    (Pi.lift_π (fun b ↦ Pi.π (fun c ↦ Over.mk (𝔘.toPreZeroHypercover.f (k c))) (j.succAbove b)) b)

namespace CechTrivialization

variable {L : SmallEtale.OxetModule B S hS} (T : CechTrivialization L)

/-- **The transition family is a cocycle**: `g_{ij} g_{jk} = g_{ik}` on `U_i ×_S U_j ×_S U_k`,
that is `d g = 0`. -/
private lemma cechDifferential_eq_zero {g : Cochain T.covering 1} (hg : T.IsTransition g) :
    Stacks.CechSite.cechDifferential T.covering.toPreZeroHypercover (unitsPresheaf B S hS) 1 g =
      0 := by
  funext k
  rw [Stacks.CechSite.cechDifferential_one_apply]
  apply eq_of_pullUnit_id_eq
  rw [pullUnit_add, pullUnit_sub, pullUnit_map, pullUnit_map, pullUnit_map]
  simp only [Category.id_comp, T.covering.map_faceProjection_left]
  change _ = pullUnit 0 _
  rw [pullUnit_zero]
  set V := (inclusion B S hS).obj (T.covering.prodObj k)
  let P : ∀ a, V ⟶ (inclusion B S hS).obj (T.covering.toPreZeroHypercover.X (k a)) :=
    fun a ↦ (inclusion B S hS).map (T.covering.prodπ k a)
  have H (j : Fin 3) := (T.isTransition_iff g).1 hg (fun b ↦ k (j.succAbove b)) V
    (fun b ↦ P (j.succAbove b))
  set u0 := pullUnit (g fun b ↦ k ((0 : Fin 3).succAbove b))
    (T.covering.qlift (fun b ↦ k ((0 : Fin 3).succAbove b)) fun b ↦ P ((0 : Fin 3).succAbove b))
  set u1 := pullUnit (g fun b ↦ k ((1 : Fin 3).succAbove b))
    (T.covering.qlift (fun b ↦ k ((1 : Fin 3).succAbove b)) fun b ↦ P ((1 : Fin 3).succAbove b))
  set u2 := pullUnit (g fun b ↦ k ((2 : Fin 3).succAbove b))
    (T.covering.qlift (fun b ↦ k ((2 : Fin 3).succAbove b)) fun b ↦ P ((2 : Fin 3).succAbove b))
  have H0 : L.res (P 1) (T.generator (k 1)) =
      (u0 : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) •
        L.res (P 2) (T.generator (k 2)) := H 0
  have H1 : L.res (P 0) (T.generator (k 0)) =
      (u1 : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) •
        L.res (P 2) (T.generator (k 2)) := H 1
  have H2 : L.res (P 0) (T.generator (k 0)) =
      (u2 : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) •
        L.res (P 1) (T.generator (k 1)) := H 2
  have h12 : (u1 : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) = u2 * u0 := by
    apply (T.isGenerator_map (P 2)).smul_left_injective
    rw [← H1, H2, H0, mul_smul]
  have h12' : u1 = u2 * u0 := Units.ext h12
  rw [h12', mul_inv_rev, ← mul_assoc u0, mul_inv_cancel, one_mul, inv_mul_cancel]

end CechTrivialization

namespace CechTrivialization

variable {L : SmallEtale.OxetModule B S hS}

/-- A family of degree-`p` cochains, as an element of the degree-`p` term of the Čech complex. -/
abbrev toCochain {𝔘 : CechCovering (final B S hS)} {p : ℕ} (g : Cochain 𝔘 p) :
    (cechComplex 𝔘.toPreZeroHypercover (unitsPresheaf B S hS)).X p :=
  (Stacks.CechSite.productAddEquiv
    (Stacks.CechSite.cochainFactor 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) p)).symm g

lemma pi_π_toCochain {𝔘 : CechCovering (final B S hS)} {p : ℕ} (g : Cochain 𝔘 p)
    (ν : Fin (p + 1) → 𝔘.toPreZeroHypercover.I₀) :
    Pi.π (Stacks.CechSite.cochainFactor 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) p) ν
      (toCochain g) = g ν :=
  congrFun ((Stacks.CechSite.productAddEquiv _).apply_symm_apply g) ν

lemma toCochain_mem_cechCycles (T : CechTrivialization L) {g : Cochain T.covering 1}
    (hg : T.IsTransition g) :
    toCochain g ∈ cechCycles T.covering.toPreZeroHypercover (unitsPresheaf B S hS) 1 := by
  rw [mem_cechCycles_iff]
  have h := Stacks.CechSite.cechDifferential_productAddEquiv T.covering.toPreZeroHypercover
    (unitsPresheaf B S hS) 1 (toCochain g)
  rw [AddEquiv.apply_symm_apply, T.cechDifferential_eq_zero hg] at h
  exact (Stacks.CechSite.productAddEquiv
    (Stacks.CechSite.cochainFactor T.covering.toPreZeroHypercover (unitsPresheaf B S hS)
      (1 + 1))).injective (h.symm.trans (map_zero _).symm)

/-- The transition family of a trivialization, as a Čech `1`-cocycle. -/
def transitionCycle (T : CechTrivialization L) :
    cechCycles T.covering.toPreZeroHypercover (unitsPresheaf B S hS) 1 :=
  ⟨toCochain T.transition, T.toCochain_mem_cechCycles T.isTransition_transition⟩

/-- The class `[g]_𝔘 ∈ Ȟ¹(S, 𝒪^*)` of the transition family of a trivialization. -/
def cechH1Class (T : CechTrivialization L) :
    cechCohomologyOfObject (final B S hS) (unitsPresheaf B S hS) 1 :=
  cechClass (unitsPresheaf B S hS) 1 T.covering T.transitionCycle

lemma cechH1Class_eq (T : CechTrivialization L) {g : Cochain T.covering 1}
    (hg : T.IsTransition g) :
    T.cechH1Class = cechClass (unitsPresheaf B S hS) 1 T.covering
      ⟨toCochain g, T.toCochain_mem_cechCycles hg⟩ := by
  obtain rfl := T.isTransition_unique T.isTransition_transition hg
  rfl

/-! #### Refinement -/

/-- The restriction of a trivialization along a refinement `φ : 𝔚 ⟶ 𝔘` of its covering: the
generators `e_{σ(k)}|_{W_k}`. -/
private abbrev refine (T : CechTrivialization L) {𝔚 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ T.covering.toPreZeroHypercover) : CechTrivialization L where
  covering := 𝔚
  generator k := L.res ((inclusion B S hS).map (φ.h₀ k)) (T.generator (φ.s₀ k))
  isGenerator _ := T.isGenerator_map _

/-- The transition family of a restricted trivialization is the pullback `φ^* g`. -/
private lemma isTransition_refine (T : CechTrivialization L) {𝔚 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ T.covering.toPreZeroHypercover) {g : Cochain T.covering 1}
    (hg : T.IsTransition g) :
    (T.refine φ).IsTransition (fun ν ↦ (unitsPresheaf B S hS).map
      (refinementProductMap φ 1 ν).op (g (φ.s₀ ∘ ν))) := by
  intro ν
  have key := (T.isTransition_iff g).1 hg (φ.s₀ ∘ ν)
    ((inclusion B S hS).obj (𝔚.prodObj ν))
    (fun a ↦ (inclusion B S hS).map (𝔚.prodπ ν a) ≫ (inclusion B S hS).map (φ.h₀ (ν a)))
  have hq : T.covering.qlift (φ.s₀ ∘ ν)
      (fun a ↦ (inclusion B S hS).map (𝔚.prodπ ν a) ≫ (inclusion B S hS).map (φ.h₀ (ν a))) =
      (inclusion B S hS).map (refinementProductMap φ 1 ν) := by
    refine T.covering.hom_ext' _ fun a ↦ ?_
    rw [CechCovering.qlift_π, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (inclusion B S hS).map (refinementProductMap_π φ 1 ν a).symm
  rw [hq, L.res_comp, L.res_comp, ← toUnits_map] at key
  exact key

private lemma transitionCycle_refine (T : CechTrivialization L) {𝔚 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ T.covering.toPreZeroHypercover) :
    (T.refine φ).transitionCycle =
      cechCyclesMap (unitsPresheaf B S hS) 1 φ T.transitionCycle := by
  have hfam := (T.refine φ).isTransition_unique (T.refine φ).isTransition_transition
    (T.isTransition_refine φ T.isTransition_transition)
  apply Subtype.ext
  rw [coe_cechCyclesMap]
  apply (Stacks.CechSite.productAddEquiv
    (Stacks.CechSite.cochainFactor 𝔚.toPreZeroHypercover (unitsPresheaf B S hS) 1)).injective
  funext ν
  refine (pi_π_toCochain (𝔘 := 𝔚) _ ν).trans ?_
  refine (congrFun hfam ν).trans ?_
  refine Eq.trans ?_ (refinementCochainMap_f_apply φ (unitsPresheaf B S hS) 1 _ ν).symm
  exact congrArg _ (pi_π_toCochain T.transition (φ.s₀ ∘ ν)).symm

private lemma cechH1Class_refine (T : CechTrivialization L) {𝔚 : CechCovering (final B S hS)}
    (φ : 𝔚.toPreZeroHypercover ⟶ T.covering.toPreZeroHypercover) :
    (T.refine φ).cechH1Class = T.cechH1Class := by
  rw [cechH1Class, transitionCycle_refine]
  exact cechClass_cechCyclesMap _ _ φ _

end CechTrivialization

namespace CechTrivialization

variable {L : SmallEtale.OxetModule B S hS}

/-! #### Change of generators -/

/-- The degree-zero Čech cochain of `𝒪^*` given by a family of units `λ_i ∈ Γ(U_i, 𝒪)^*`. -/
private abbrev unitsCochain {𝔘 : CechCovering (final B S hS)}
    (lam : ∀ i : 𝔘.toPreZeroHypercover.I₀, ((SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (𝔘.toPreZeroHypercover.X i))))ˣ) :
    (cechComplex 𝔘.toPreZeroHypercover (unitsPresheaf B S hS)).X 0 :=
  Stacks.CechSite.familyToCochain 𝔘.toPreZeroHypercover (unitsPresheaf B S hS)
    (fun i ↦ ofUnits (lam i))

/-- The coboundary `(λ_j λ_i⁻¹)_{ij}` of a family of units, as a family of cochains. -/
private abbrev unitsCoboundary {𝔘 : CechCovering (final B S hS)}
    (lam : ∀ i : 𝔘.toPreZeroHypercover.I₀, ((SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (𝔘.toPreZeroHypercover.X i))))ˣ) : Cochain 𝔘 1 :=
  Stacks.CechSite.cechDifferential 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 0
    (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
      𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 0) (unitsCochain lam))

private lemma toUnits_unitsCoboundary {𝔘 : CechCovering (final B S hS)}
    (lam : ∀ i : 𝔘.toPreZeroHypercover.I₀, ((SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (𝔘.toPreZeroHypercover.X i))))ˣ)
    (ν : Fin 2 → 𝔘.toPreZeroHypercover.I₀) :
    toUnits (unitsCoboundary lam ν) =
      pullUnit (ofUnits (lam (ν 1))) ((inclusion B S hS).map (𝔘.prodπ ν 1)) *
        (pullUnit (ofUnits (lam (ν 0))) ((inclusion B S hS).map (𝔘.prodπ ν 0)))⁻¹ := by
  have hc (k : Fin 1 → 𝔘.toPreZeroHypercover.I₀) :
      Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
        𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 0) (unitsCochain lam) k =
      (unitsPresheaf B S hS).map (𝔘.prodπ k 0).op (ofUnits (lam (k 0))) :=
    Stacks.CechSite.familyToCochain_π 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) _ k
  rw [unitsCoboundary, Stacks.CechSite.cechDifferential_zero_apply, hc, hc, toUnits_sub,
    toUnits_map, toUnits_map,
    pullUnit_map, pullUnit_map, 𝔘.map_faceProjection_left,
    𝔘.map_faceProjection_left, CechCovering.qlift_π, CechCovering.qlift_π]
  rfl

private lemma toCochain_unitsCoboundary {𝔘 : CechCovering (final B S hS)}
    (lam : ∀ i : 𝔘.toPreZeroHypercover.I₀, ((SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (𝔘.toPreZeroHypercover.X i))))ˣ) :
    toCochain (unitsCoboundary lam) =
      (cechComplex 𝔘.toPreZeroHypercover (unitsPresheaf B S hS)).d 0 1 (unitsCochain lam) := by
  rw [unitsCoboundary, Stacks.CechSite.cechDifferential_productAddEquiv]
  exact AddEquiv.symm_apply_apply _ _

/-- The trivialization with generators `λ_i e_i`. -/
private abbrev smulUnits (T : CechTrivialization L)
    (lam : ∀ i : T.covering.toPreZeroHypercover.I₀, ((SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i))))ˣ) :
    CechTrivialization L where
  covering := T.covering
  generator i := (lam i : (SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i)))) • T.generator i
  isGenerator i := (T.isGenerator i).unit_smul (lam i)

/-- Multiplying the generators by units `λ_i` multiplies the transition family by
`λ_i λ_j⁻¹`. -/
private lemma isTransition_smulUnits (T : CechTrivialization L)
    (lam : ∀ i : T.covering.toPreZeroHypercover.I₀, ((SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i))))ˣ) :
    (T.smulUnits lam).IsTransition (fun ν ↦ T.transition ν - unitsCoboundary lam ν) := by
  intro ν
  dsimp only [smulUnits]
  rw [L.res_smul, L.res_smul, T.isTransition_transition ν, smul_smul,
    smul_smul, toUnits_sub, toUnits_unitsCoboundary]
  congr 1
  have h0 : (SmallEtale.structureSheaf B S hS).obj.map
      ((inclusion B S hS).map (T.covering.prodπ ν 0)).op (lam (ν 0) : _) =
      (pullUnit (ofUnits (lam (ν 0))) ((inclusion B S hS).map (T.covering.prodπ ν 0)) : _) :=
    rfl
  have h1 : (SmallEtale.structureSheaf B S hS).obj.map
      ((inclusion B S hS).map (T.covering.prodπ ν 1)).op (lam (ν 1) : _) =
      (pullUnit (ofUnits (lam (ν 1))) ((inclusion B S hS).map (T.covering.prodπ ν 1)) : _) :=
    rfl
  rw [h0, h1, ← Units.val_mul, ← Units.val_mul]
  congr 1
  rw [mul_comm (pullUnit (ofUnits (lam (ν 0))) _)]
  group

private lemma cechH1Class_smulUnits (T : CechTrivialization L)
    (lam : ∀ i : T.covering.toPreZeroHypercover.I₀, ((SmallEtale.structureSheaf B S hS).obj.obj
      (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i))))ˣ) :
    (T.smulUnits lam).cechH1Class = T.cechH1Class := by
  rw [CechTrivialization.cechH1Class_eq _ (T.isTransition_smulUnits lam)]
  refine cechClass_eq_of_sub_mem_range _ _ _ _ ⟨-(unitsCochain lam), ?_⟩
  have e1 : toCochain (fun ν ↦ T.transition ν - unitsCoboundary lam ν) - toCochain T.transition =
      toCochain (-unitsCoboundary lam) := by
    refine (map_sub (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
      T.covering.toPreZeroHypercover (unitsPresheaf B S hS) 1)).symm _ _).symm.trans ?_
    congr 1
    funext ν
    change T.transition ν - unitsCoboundary lam ν - T.transition ν = -unitsCoboundary lam ν
    abel
  change (cechComplex T.covering.toPreZeroHypercover (unitsPresheaf B S hS)).d 0 1
      (-(unitsCochain lam)) =
    toCochain (fun ν ↦ T.transition ν - unitsCoboundary lam ν) - toCochain T.transition
  refine (map_neg (ConcreteCategory.hom
    ((cechComplex T.covering.toPreZeroHypercover (unitsPresheaf B S hS)).d 0 1)) _).trans ?_
  refine Eq.trans ?_ e1.symm
  refine Eq.trans ?_ (map_neg (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
    T.covering.toPreZeroHypercover (unitsPresheaf B S hS) 1)).symm _).symm
  exact congrArg Neg.neg (toCochain_unitsCoboundary lam).symm

/-- **Changing the generators changes the transition family by a coboundary**, so the class
`[g]_𝔘` does not depend on the generators. -/
private lemma cechH1Class_mk_eq (T : CechTrivialization L)
    (e' : ∀ i : T.covering.toPreZeroHypercover.I₀,
      L.val.obj (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i))))
    (he' : ∀ i, SmallEtale.IsGenerator L _ (e' i)) :
    cechH1Class ⟨T.covering, e', he'⟩ = T.cechH1Class := by
  have hlam (i : T.covering.toPreZeroHypercover.I₀) :=
    (he' i).existsUnique_unit_smul (T.isGenerator i)
  choose lam hlame _ using hlam
  have : (⟨T.covering, e', he'⟩ : CechTrivialization L) = T.smulUnits lam := by
    simp only [CechTrivialization.mk.injEq, heq_eq_eq, true_and]
    funext i
    exact hlame i
  rw [this, cechH1Class_smulUnits]

/-! #### Isomorphisms -/

/-- The image of a trivialization under an isomorphism of `𝒪_{S,et}`-modules. -/
private abbrev map {L' : SmallEtale.OxetModule B S hS} (T : CechTrivialization L) (α : L ≅ L') :
    CechTrivialization L' where
  covering := T.covering
  generator i := α.hom.val.app _ (T.generator i)
  isGenerator i := by
    intro V f
    have h := T.isGenerator i f
    have e : (fun a : (SmallEtale.structureSheaf B S hS).obj.obj (op V) ↦
        a • L'.val.map f.op (α.hom.val.app _ (T.generator i))) =
        (α.hom.val.app (op V)) ∘ (fun a ↦ a • L.val.map f.op (T.generator i)) := by
      funext a
      refine Eq.trans ?_ ((α.hom.val.app (op V)).hom.map_smul a _).symm
      congr 1
      exact (PresheafOfModules.naturality_apply α.hom.val f.op (T.generator i)).symm
    rw [e]
    refine Function.Bijective.comp ?_ h
    exact (ConcreteCategory.isIso_iff_bijective _).mp (by
      have : IsIso α.hom.val := Functor.map_isIso (SheafOfModules.forget _) α.hom
      exact Functor.map_isIso (PresheafOfModules.evaluation _ (op V)) α.hom.val)

private lemma cechH1Class_map {L' : SmallEtale.OxetModule B S hS} (T : CechTrivialization L)
    (α : L ≅ L') : (T.map α).cechH1Class = T.cechH1Class := by
  have htr : (T.map α).IsTransition T.transition := by
    intro ν
    have h1 := congrArg (α.hom.val.app (op _)) (T.isTransition_transition ν)
    rw [(α.hom.val.app _).hom.map_smul] at h1
    simp only [SmallEtale.OxetModule.res] at h1 ⊢
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply] at h1
    exact h1
  exact (T.map α).cechH1Class_eq htr

/-- **The class of a trivialization depends only on the module**: any two trivializations of
`L` have the same class in `Ȟ¹(S, 𝒪^*)`. -/
lemma cechH1Class_eq_cechH1Class (T T' : CechTrivialization L) :
    T.cechH1Class = T'.cechH1Class := by
  let φ := CechCovering.infFst T.covering T'.covering
  let φ' := CechCovering.infSnd T.covering T'.covering
  rw [← T.cechH1Class_refine φ, ← T'.cechH1Class_refine φ']
  exact ((T.refine φ).cechH1Class_mk_eq (T'.refine φ').generator
    (T'.refine φ').isGenerator).symm

/-! #### Existence -/

omit [IsNoetherian S] [S.IsSeparated] in
/-- Over an empty scheme every section of an `𝒪_{S,et}`-module generates it. -/
private lemma isGenerator_of_isEmpty (L : SmallEtale.OxetModule B S hS) (U : SmallEtale B S hS)
    (hU : IsEmpty ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)))
    (e : L.val.obj (op U)) : SmallEtale.IsGenerator L U e := by
  intro V f
  have : IsEmpty ((SmallEtale.toScheme B S hS).obj V) :=
    Function.isEmpty ((SmallEtale.toScheme B S hS).map
      ((SmallEtale.finalIsTerminal B S hS).from V)).base
  have hO : Subsingleton ((SmallEtale.structureSheaf B S hS).obj.obj (op V)) :=
    inferInstanceAs (Subsingleton Γ((SmallEtale.toScheme B S hS).obj V, ⊤))
  have hL : Subsingleton (L.val.obj (op V)) := Module.subsingleton
    ((SmallEtale.structureSheaf B S hS).obj.obj (op V)) _
  exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun y ↦ ⟨0, hL.elim _ _⟩⟩

/-- **Étale line bundles have Čech trivializations**: over a noetherian scheme, a trivialization
of an étale line bundle on an arbitrary covering of the small étale site is refined by one on a
finite covering by noetherian separated étale `S`-schemes. -/
theorem nonempty_cechTrivialization (L : SmallEtale.OxetModule B S hS)
    (hL : SmallEtale.IsEtaleLineBundle B S hS L) : Nonempty (CechTrivialization L) := by
  obtain ⟨T0⟩ := (SmallEtale.isEtaleLineBundle_iff_nonempty_trivialization L).1 hL
  let R : Sieve (final B S hS) :=
    { arrows := fun Y _ ↦ ∃ i, Nonempty ((inclusion B S hS).obj Y ⟶ T0.obj i)
      downward_closed := by
        rintro Y Z f ⟨i, ⟨g⟩⟩ h
        exact ⟨i, ⟨(inclusion B S hS).map h ≫ g⟩⟩ }
  have hR : R ∈ topology B S hS (final B S hS) := by
    rw [mem_topology_iff]
    intro x
    obtain ⟨W, g, hg, w, hw⟩ :=
      SmallEtale.exists_mem_arrows_mem_range B S hS T0.ofArrows_mem_topology x
    obtain ⟨i, h, -⟩ := Sieve.ofArrows.exists hg
    obtain ⟨U, g', u, hu⟩ := exists_obj_mem_range B S hS W w
    let t : U ⟶ final B S hS :=
      ObjectProperty.homMk ((SmallEtale.finalIsTerminal B S hS).from _)
    have ht : (inclusion B S hS).map t = g' ≫ g := (SmallEtale.finalIsTerminal B S hS).hom_ext _ _
    refine ⟨U, t, ⟨i, ⟨g' ≫ h⟩⟩, u, ?_⟩
    change (SmallEtale.toScheme B S hS).map ((inclusion B S hS).map t) u = x
    rw [ht]
    change ((SmallEtale.toScheme B S hS).map g) ((SmallEtale.toScheme B S hS).map g' u) = x
    rw [hu, hw]
  obtain ⟨P, ⟨ι, hfin, V, φ, rfl, hcov⟩, hle⟩ := exists_finite_subfamily B S hS R hR
  have hmem (j : ι) : R (φ j) := by
    apply hle
    exact Presieve.ofArrows.mk j
  choose i g using hmem
  by_cases h0 : Nat.card ι = 0
  · have : IsEmpty ι := (Finite.card_eq_zero_iff).mp h0
    have hE : IsEmpty ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) := by
      refine ⟨fun x ↦ ?_⟩
      have hx : x ∈ ⋃ j, Set.range ((toScheme B S hS).map (φ j)) := by rw [hcov]; trivial
      obtain ⟨j, -⟩ := Set.mem_iUnion.mp hx
      exact isEmptyElim j
    exact ⟨⟨CechCovering.self _, fun _ ↦ 0, fun _ ↦ isGenerator_of_isEmpty L _ hE _⟩⟩
  · let e : ι ≃ Fin (Nat.card ι) := Finite.equivFin ι
    let 𝔘 : CechCovering (final B S hS) :=
      { n := Nat.card ι
        pos := Nat.pos_of_ne_zero h0
        X := fun p ↦ V (e.symm p)
        f := fun p ↦ φ (e.symm p)
        iUnion_range := by
          refine Set.eq_univ_of_forall fun x ↦ ?_
          have hx : x ∈ ⋃ j, Set.range ((toScheme B S hS).map (φ j)) := by rw [hcov]; trivial
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_iUnion.mpr ⟨e j, by rw [Equiv.symm_apply_apply]; exact hj⟩ }
    exact ⟨⟨𝔘, fun p ↦ L.res (g (e.symm p)).some (T0.generator (i (e.symm p))),
      fun p ↦ (T0.isGenerator _).restrict _⟩⟩

end CechTrivialization

end Trivialization


end AlgebraicGeometry.SmallNoetherianSeparatedEtale


namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The étale Picard group -/

/-- **The étale Picard group** `Pic_et(S)`: the group of isomorphism classes of invertible
`𝒪_{S,et}`-modules, with the tensor product as group law. -/
abbrev EtalePicardGroup (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  Stacks.SheafOfModules.Picard.PicardGroup (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2

/-- The abelian group structure on the étale Picard group, named because instance search does
not find it through the universe constraints of the small étale ringed site. -/
instance (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AddCommGroup (EtalePicardGroup B S hS) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2

/-- The class `[L] ∈ Pic_et(S)` of an invertible `𝒪_{S,et}`-module. -/
abbrev etalePicardClass (L : SmallEtale.OxetModule B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L) :
    EtalePicardGroup B S hS :=
  Stacks.SheafOfModules.Picard.classOf _ _ L hL

/-- An invertible `𝒪_{S,et}`-module is an étale line bundle. -/
lemma isEtaleLineBundle_of_isInvertible (L : SmallEtale.OxetModule B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L) :
    SmallEtale.IsEtaleLineBundle B S hS L :=
  @RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible' (smallEtaleRingedSite B S hS) _ _ L
    (smallEtaleRingedSite_isLocallyRinged B S hS) hL

/-- An étale line bundle is an invertible `𝒪_{S,et}`-module. -/
lemma isInvertible_of_isEtaleLineBundle (L : SmallEtale.OxetModule B S hS)
    (hL : SmallEtale.IsEtaleLineBundle B S hS L) :
    Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L :=
  have := smallEtaleRingedSite_essentiallySmall B S hS
  RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall
    (smallEtaleRingedSite B S hS) L hL

/-- The class of the structure sheaf is zero. -/
private lemma etalePicardClass_unit :
    etalePicardClass (SheafOfModules.unit (SmallEtale.structureSheaf B S hS))
      (Stacks.SheafOfModules.isInvertible_unit _ _) = 0 := by
  let X := smallEtaleRingedSite B S hS
  have hU : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.isInvertible_unit X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
  have := hU
  have hUU := Stacks.SheafOfModules.isInvertible_tensorSheaf X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  have he := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 _ _ hUU hU).2
    ⟨Stacks.SheafOfModules.tensorSheafLeftUnitor X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 _⟩
  have h := (Stacks.SheafOfModules.Picard.classOf_tensor X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 _ _ hU hU hUU).trans he
  exact add_eq_left.mp h

/-- The tensor product `L ⊗ N` of two `𝒪_{S,et}`-modules. -/
abbrev etaleTensor (L N : SmallEtale.OxetModule B S hS) : SmallEtale.OxetModule B S hS :=
  Stacks.Cohomology.Torsors.Generators.tensorSheafOfModules (smallEtaleRingedSite B S hS) L N

/-- The section `s ⊗ t` of `L ⊗ N`. -/
private abbrev etaleTensorSection (L N : SmallEtale.OxetModule B S hS) (U : SmallEtale B S hS)
    (s : L.val.obj (op U)) (t : N.val.obj (op U)) : (etaleTensor L N).val.obj (op U) :=
  Stacks.Cohomology.Torsors.Generators.tensorSection (smallEtaleRingedSite B S hS) L N U s t

private lemma etaleTensorSection_res (L N : SmallEtale.OxetModule B S hS) {U V : SmallEtale B S hS}
    (g : V ⟶ U) (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    (etaleTensor L N).res g (etaleTensorSection L N U s t) =
      etaleTensorSection L N V (L.res g s) (N.res g t) :=
  Stacks.Cohomology.Torsors.Generators.tensorSection_restrict (smallEtaleRingedSite B S hS) L N g
    s t

private lemma etaleTensorSection_smul (L N : SmallEtale.OxetModule B S hS) (U : SmallEtale B S hS)
    (a b : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
    (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    etaleTensorSection L N U (a • s) (b • t) = (a * b) • etaleTensorSection L N U s t :=
  Stacks.Cohomology.Torsors.Generators.tensorSection_smul' (smallEtaleRingedSite B S hS) L N U a b
    s t

private lemma isGenerator_etaleTensorSection {L N : SmallEtale.OxetModule B S hS}
    {U : SmallEtale B S hS}
    {s : L.val.obj (op U)} {t : N.val.obj (op U)} (hs : SmallEtale.IsGenerator L U s)
    (ht : SmallEtale.IsGenerator N U t) :
    SmallEtale.IsGenerator (etaleTensor L N) U (etaleTensorSection L N U s t) :=
  fun _ g ↦ (Stacks.Cohomology.Torsors.Generators.tensorGeneratorSections'
    (smallEtaleRingedSite B S hS) L N U ⟨s, fun _ g ↦ hs g⟩ ⟨t, fun _ g ↦ ht g⟩).property _ g


section Kappa

variable [IsNoetherian S] [S.IsSeparated]

/-- The class in `Ȟ¹(S, 𝒪^*)` of a Picard class: the class of the transition family of any
Čech trivialization of any invertible module in it. -/
def picardCechClass (p : EtalePicardGroup B S hS) :
    cechCohomologyOfObject (final B S hS) (unitsPresheaf B S hS) 1 :=
  (CechTrivialization.nonempty_cechTrivialization _ (isEtaleLineBundle_of_isInvertible _
    (Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ p).choose_spec.choose)).some.cechH1Class

lemma picardCechClass_etalePicardClass (L : SmallEtale.OxetModule B S hS)
    (hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L)
    (T : CechTrivialization L) :
    picardCechClass (etalePicardClass L hL) = T.cechH1Class := by
  have h := (Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ (etalePicardClass L hL))
  have hspec := h.choose_spec.choose_spec
  obtain ⟨α⟩ := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ _).1 hspec
  rw [picardCechClass, ← CechTrivialization.cechH1Class_map _ α]
  exact CechTrivialization.cechH1Class_eq_cechH1Class _ _

namespace CechTrivialization

variable {L N : SmallEtale.OxetModule B S hS}

/-- The tensor product of two trivializations on one covering: the generators
`e_i ⊗ f_i` of `L ⊗ N`. -/
private abbrev tensor (T : CechTrivialization L)
    (f : ∀ i : T.covering.toPreZeroHypercover.I₀,
      N.val.obj (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i))))
    (hf : ∀ i, SmallEtale.IsGenerator N _ (f i)) :
    CechTrivialization (etaleTensor L N) where
  covering := T.covering
  generator i := etaleTensorSection L N _ (T.generator i) (f i)
  isGenerator i := isGenerator_etaleTensorSection (T.isGenerator i) (hf i)

private lemma isTransition_tensor (T : CechTrivialization L)
    (f : ∀ i : T.covering.toPreZeroHypercover.I₀,
      N.val.obj (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i))))
    (hf : ∀ i, SmallEtale.IsGenerator N _ (f i)) :
    (T.tensor f hf).IsTransition (fun ν ↦ T.transition ν +
      (CechTrivialization.transition ⟨T.covering, f, hf⟩ ν)) := by
  intro ν
  have hL := T.isTransition_transition ν
  have hN := (CechTrivialization.isTransition_transition ⟨T.covering, f, hf⟩) ν
  change (etaleTensor L N).res _ (etaleTensorSection L N _ _ _) = _ •
    (etaleTensor L N).res _ (etaleTensorSection L N _ _ _)
  rw [etaleTensorSection_res, etaleTensorSection_res]
  erw [hL, hN]
  rw [etaleTensorSection_smul, toUnits_add]
  rfl

private lemma cechH1Class_tensor (T : CechTrivialization L)
    (f : ∀ i : T.covering.toPreZeroHypercover.I₀,
      N.val.obj (op ((inclusion B S hS).obj (T.covering.toPreZeroHypercover.X i))))
    (hf : ∀ i, SmallEtale.IsGenerator N _ (f i)) :
    (T.tensor f hf).cechH1Class =
      T.cechH1Class + (CechTrivialization.cechH1Class ⟨T.covering, f, hf⟩) := by
  rw [(T.tensor f hf).cechH1Class_eq (T.isTransition_tensor f hf), cechH1Class, cechH1Class,
    ← map_add]
  congr 1
  apply Subtype.ext
  exact map_add (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
    T.covering.toPreZeroHypercover (unitsPresheaf B S hS) 1)).symm _ _

end CechTrivialization

/-- **`κ` is additive**: the class of `L ⊗ N` is the sum of the classes. -/
lemma picardCechClass_add (p q : EtalePicardGroup B S hS) :
    picardCechClass (p + q) = picardCechClass p + picardCechClass q := by
  obtain ⟨L, hL, rfl⟩ : ∃ (L : SmallEtale.OxetModule B S hS) (hL : _),
      etalePicardClass L hL = p := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ p
  obtain ⟨N, hN, rfl⟩ : ∃ (N : SmallEtale.OxetModule B S hS) (hN : _),
      etalePicardClass N hN = q := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ q
  have := hL
  have := hN
  have hLN := Stacks.SheafOfModules.isInvertible_tensorSheaf (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L N
  have hsum : etalePicardClass L hL + etalePicardClass N hN =
      etalePicardClass (etaleTensor L N) hLN :=
    Stacks.SheafOfModules.Picard.classOf_tensor (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L N hL hN hLN
  obtain ⟨TL⟩ := CechTrivialization.nonempty_cechTrivialization L
    (isEtaleLineBundle_of_isInvertible L hL)
  obtain ⟨TN⟩ := CechTrivialization.nonempty_cechTrivialization N
    (isEtaleLineBundle_of_isInvertible N hN)
  let φ := CechCovering.infFst TL.covering TN.covering
  let φ' := CechCovering.infSnd TL.covering TN.covering
  let T := TL.refine φ
  let T' := TN.refine φ'
  rw [hsum,
    picardCechClass_etalePicardClass _ _ (T.tensor T'.generator T'.isGenerator),
    CechTrivialization.cechH1Class_tensor, picardCechClass_etalePicardClass _ _ T,
    picardCechClass_etalePicardClass _ _ T']

end Kappa


/-! ### Trivial classes -/

section Trivial

variable [IsNoetherian S] [S.IsSeparated] {L : SmallEtale.OxetModule B S hS}

/-- A section over the final object which generates on the members of a covering generates. -/
private lemma isGenerator_final_of_isGenerator_res (𝔘 : CechCovering (final B S hS))
    (s : L.val.obj (op ((inclusion B S hS).obj (final B S hS))))
    (hs : ∀ i, SmallEtale.IsGenerator L _
      (L.res ((inclusion B S hS).map (𝔘.toPreZeroHypercover.f i)) s)) :
    SmallEtale.IsGenerator L ((inclusion B S hS).obj (final B S hS)) s := by
  let R : Sieve ((inclusion B S hS).obj (final B S hS)) :=
    Sieve.ofArrows (fun i ↦ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X i))
      (fun i ↦ (inclusion B S hS).map (𝔘.toPreZeroHypercover.f i))
  have hR : R ∈ SmallEtale.topology B S hS _ := by
    apply SmallEtale.mem_topology_of_jointlySurjective
    intro x
    have hx : x ∈ ⋃ ν, Set.range ((toScheme B S hS).map (𝔘.f ν)) := by
      rw [𝔘.iUnion_range]; trivial
    obtain ⟨ν, hν⟩ := Set.mem_iUnion.1 hx
    exact ⟨_, _, Sieve.ofArrows_mk _ _ ν, hν⟩
  have := (Stacks.Cohomology.Torsors.Generators.generatorSections_of_locally_generator'
    (smallEtaleRingedSite B S hS) L _ s R hR (by
      intro V f hf W g
      obtain ⟨i, h, rfl⟩ := Sieve.ofArrows.exists hf
      have hb := hs i (g ≫ h)
      change Function.Bijective (fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op W) ↦
        r • L.res (g ≫ h ≫ (inclusion B S hS).map (𝔘.toPreZeroHypercover.f i)) s)
      rw [← Category.assoc, L.res_comp]
      exact hb)).property
  exact fun V f ↦ this V f

omit [IsNoetherian S] [S.IsSeparated] in
/-- **An `𝒪_{S,et}`-module with a global generator is trivial.** -/
private lemma nonempty_iso_unit_of_isGenerator (s : L.val.obj (op (SmallEtale.final B S hS)))
    (hs : SmallEtale.IsGenerator L (SmallEtale.final B S hS) s) :
    Nonempty (SheafOfModules.unit (SmallEtale.structureSheaf B S hS) ≅ L) := by
  let σ : L.val.sections := PresheafOfModules.sectionsMk
    (fun V ↦ L.res ((SmallEtale.finalIsTerminal B S hS).from V.unop) s) (by
      intro X Y f
      change L.res f.unop (L.res _ s) = L.res _ s
      rw [← L.res_comp]
      congr 1
      exact (SmallEtale.finalIsTerminal B S hS).hom_ext _ _)
  let φ := L.unitHomEquiv.symm σ
  have happ (V : (SmallEtale B S hS)ᵒᵖ) (a : (SmallEtale.structureSheaf B S hS).obj.obj V) :
      @id (L.val.obj V) (φ.val.app V a) =
        a • L.res ((SmallEtale.finalIsTerminal B S hS).from V.unop) s := by
    have h1 : @id (L.val.obj V) (φ.val.app V a) =
        a • @id (L.val.obj V)
          (φ.val.app V (1 : (SmallEtale.structureSheaf B S hS).obj.obj V)) := by
      have := (φ.val.app V).hom.map_smul a (1 : (SmallEtale.structureSheaf B S hS).obj.obj V)
      exact (congrArg (fun x ↦ (φ.val.app V).hom x) (mul_one a).symm).trans this
    rw [h1]
    congr 1
    change (L.unitHomEquiv φ).val V = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hφ (V : (SmallEtale B S hS)ᵒᵖ) : IsIso (φ.val.app V) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have hb := hs ((SmallEtale.finalIsTerminal B S hS).from V.unop)
    have heq : (fun a : (SmallEtale.structureSheaf B S hS).obj.obj V ↦ @id (L.val.obj V)
        (φ.val.app V a)) = fun a ↦
          a • L.res ((SmallEtale.finalIsTerminal B S hS).from V.unop) s :=
      funext (happ V)
    exact (heq ▸ hb : Function.Bijective _)
  let ψ : (SheafOfModules.unit (SmallEtale.structureSheaf B S hS)).val ≅ L.val :=
    PresheafOfModules.isoMk (fun V ↦ @asIso _ _ _ _ (φ.val.app V) (hφ V))
      (by intro V V' f; exact φ.val.naturality f)
  have : IsIso φ.val := by
    have hψ : ψ.hom = φ.val := by ext V; rfl
    rw [← hψ]
    infer_instance
  have : IsIso ((SheafOfModules.forget (SmallEtale.structureSheaf B S hS)).map φ) := this
  have := isIso_of_fully_faithful (SheafOfModules.forget _) φ
  exact ⟨asIso φ⟩

/-- **Gluing.** If the transition family of a trivialization vanishes, the generators glue to a
global generator. -/
private lemma CechTrivialization.exists_isGenerator_of_isTransition_zero (T : CechTrivialization L)
    (h : T.IsTransition 0) :
    ∃ s, SmallEtale.IsGenerator L ((inclusion B S hS).obj (final B S hS)) s := by
  let G := (SheafOfModules.toSheaf (SmallEtale.structureSheaf B S hS)).obj L
  have hG : Presheaf.IsSheaf (topology B S hS) (restrictSheaf G) :=
    ((sheafEquiv B S hS AddCommGrpCat.{u}).inverse.obj G).property
  have hbij := Stacks.CechSite.cechRestriction_bijective_of_isSheaf (topology B S hS)
    (restrictSheaf G) hG T.covering.toPreZeroHypercover (sieve₀_mem_topology T.covering)
  have hmatch : PreZeroHypercover.IsMatching (restrictSheaf G ⋙ forget AddCommGrpCat)
      T.covering.toPreZeroHypercover T.generator := by
    intro i j W p q _
    have := (T.isTransition_iff 0).1 h ![i, j] ((inclusion B S hS).obj W)
      (fun a ↦ match a with
        | 0 => (inclusion B S hS).map p
        | 1 => (inclusion B S hS).map q)
    rw [show (0 : Cochain T.covering 1) ![i, j] = 0 from rfl, pullUnit_zero, Units.val_one,
      one_smul] at this
    exact this
  obtain ⟨s, hs⟩ := hbij.2 ⟨T.generator, hmatch⟩
  refine ⟨s, isGenerator_final_of_isGenerator_res T.covering s fun i ↦ ?_⟩
  have h2 : L.res ((inclusion B S hS).map (T.covering.toPreZeroHypercover.f i)) s =
      T.generator i := congrFun (congrArg Subtype.val hs) i
  rw [h2]
  exact T.isGenerator i

/-- **`κ` has trivial kernel**: an invertible module whose Čech class vanishes is trivial. -/
private lemma etalePicardClass_eq_zero_of_cechH1Class_eq_zero
    (hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L)
    (T : CechTrivialization L) (h0 : T.cechH1Class = 0) : etalePicardClass L hL = 0 := by
  have h := h0
  rw [CechTrivialization.cechH1Class, ← map_zero (cechClass (unitsPresheaf B S hS) 1 T.covering),
    cechClass_eq_cechClass_iff] at h
  obtain ⟨𝔚, φ, φ', c, hc⟩ := h
  let T₁ := T.refine φ
  have hT₁ : CechTrivialization.toCochain T₁.transition =
      (cechComplex 𝔚.toPreZeroHypercover (unitsPresheaf B S hS)).d 0 1 c := by
    have h1 := congrArg Subtype.val (T.transitionCycle_refine φ)
    rw [coe_cechCyclesMap] at h1
    change CechTrivialization.toCochain T₁.transition = _ at h1
    rw [h1]
    change _ = (cechComplex 𝔚.toPreZeroHypercover (unitsPresheaf B S hS)).d (1 - 1) 1 c
    rw [hc, ZeroMemClass.coe_zero, map_zero, sub_zero]
  let lam (i : 𝔚.toPreZeroHypercover.I₀) :=
    toUnits (Stacks.CechSite.cochainToFamily 𝔚.toPreZeroHypercover (unitsPresheaf B S hS) c i)
  have hlam : CechTrivialization.unitsCochain lam = c :=
    Stacks.CechSite.familyToCochain_cochainToFamily _ _ c
  have hcob : CechTrivialization.unitsCoboundary lam = T₁.transition := by
    apply (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
      𝔚.toPreZeroHypercover (unitsPresheaf B S hS) 1)).symm.injective
    change CechTrivialization.toCochain _ = CechTrivialization.toCochain _
    rw [CechTrivialization.toCochain_unitsCoboundary, hlam, hT₁]
  have h2 : (T₁.smulUnits lam).IsTransition 0 := by
    have := T₁.isTransition_smulUnits lam
    rw [hcob] at this
    convert this using 1
    funext ν
    exact (sub_self _).symm
  obtain ⟨s, hs⟩ := (T₁.smulUnits lam).exists_isGenerator_of_isTransition_zero h2
  obtain ⟨α⟩ := nonempty_iso_unit_of_isGenerator s hs
  rw [← etalePicardClass_unit (B := B) (S := S) (hS := hS)]
  exact (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ _).2 ⟨α.symm⟩

end Trivial

/-! ### The line bundle of a cocycle -/

section Construction

variable [IsNoetherian S] [S.IsSeparated] (𝔘 : CechCovering (final B S hS))

/-- The member `U_i` of a covering, as an object of the small étale site. -/
private abbrev CechCovering.obj (i : 𝔘.toPreZeroHypercover.I₀) : SmallEtale B S hS :=
  (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X i)

/-- The pair of morphisms `h₀ : T ⟶ U_i`, `h₁ : T ⟶ U_j`, as a family indexed by `Fin 2`. -/
private def CechCovering.pair {T : SmallEtale B S hS} {i j : 𝔘.toPreZeroHypercover.I₀}
    (h₀ : T ⟶ 𝔘.obj i) (h₁ : T ⟶ 𝔘.obj j) :
    ∀ a : Fin 2, T ⟶ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X (![i, j] a))
  | 0 => h₀
  | 1 => h₁

/-- The triple of morphisms `h₀ : T ⟶ U_i`, `h₁ : T ⟶ U_j`, `h₂ : T ⟶ U_k`. -/
private def CechCovering.triple {T : SmallEtale B S hS} {i j k : 𝔘.toPreZeroHypercover.I₀}
    (h₀ : T ⟶ 𝔘.obj i) (h₁ : T ⟶ 𝔘.obj j) (h₂ : T ⟶ 𝔘.obj k) :
    ∀ a : Fin 3, T ⟶ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X (![i, j, k] a))
  | 0 => h₀
  | 1 => h₁
  | 2 => h₂

variable {𝔘} (g : CechTrivialization.Cochain 𝔘 1)

/-- The value `g_{ij}(h₀, h₁) ∈ Γ(T, 𝒪)^*` of a degree-one cochain at a generalized point
`(h₀, h₁) : T ⟶ U_i ×_S U_j`. -/
private def gAt {T : SmallEtale B S hS} {i j : 𝔘.toPreZeroHypercover.I₀}
    (h₀ : T ⟶ 𝔘.obj i) (h₁ : T ⟶ 𝔘.obj j) :
    ((SmallEtale.structureSheaf B S hS).obj.obj (op T))ˣ :=
  pullUnit (g ![i, j]) (𝔘.qlift ![i, j] (𝔘.pair h₀ h₁))

private lemma pullUnit_qlift_eq_gAt {T : SmallEtale B S hS} (ν : Fin 2 → 𝔘.toPreZeroHypercover.I₀)
    (h : ∀ a, T ⟶ (inclusion B S hS).obj (𝔘.toPreZeroHypercover.X (ν a))) :
    pullUnit (g ν) (𝔘.qlift ν h) = gAt g (h 0) (h 1) := by
  obtain ⟨i, j, rfl⟩ : ∃ i j, ν = ![i, j] :=
    ⟨ν 0, ν 1, by funext a; fin_cases a <;> rfl⟩
  have : h = 𝔘.pair (h 0) (h 1) := by
    funext a
    match a with
    | 0 => rfl
    | 1 => rfl
  rw [gAt, ← this]
  rfl

private lemma gAt_comp {T T' : SmallEtale B S hS} {i j : 𝔘.toPreZeroHypercover.I₀} (m : T' ⟶ T)
    (h₀ : T ⟶ 𝔘.obj i) (h₁ : T ⟶ 𝔘.obj j) :
    gAt g (m ≫ h₀) (m ≫ h₁) =
      Units.map ((SmallEtale.structureSheaf B S hS).obj.map m.op).hom.toMonoidHom
        (gAt g h₀ h₁) := by
  rw [gAt, gAt, ← pullUnit_comp, 𝔘.comp_qlift]
  congr 2
  funext a
  match a with
  | 0 => rfl
  | 1 => rfl

variable {g}

/-- **The cocycle relation at generalized points**: `g_{ij} g_{jk} = g_{ik}`. -/
private lemma gAt_mul_gAt
    (hg : Stacks.CechSite.cechDifferential 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 1 g = 0)
    {T : SmallEtale B S hS} {i j k : 𝔘.toPreZeroHypercover.I₀}
    (h₀ : T ⟶ 𝔘.obj i) (h₁ : T ⟶ 𝔘.obj j) (h₂ : T ⟶ 𝔘.obj k) :
    gAt g h₀ h₁ * gAt g h₁ h₂ = gAt g h₀ h₂ := by
  have h := congrArg (fun x ↦ pullUnit x (𝔘.qlift ![i, j, k] (𝔘.triple h₀ h₁ h₂)))
    (congrFun hg ![i, j, k])
  rw [Stacks.CechSite.cechDifferential_one_apply, pullUnit_add, pullUnit_sub, pullUnit_map,
    pullUnit_map, pullUnit_map, 𝔘.map_faceProjection_left, 𝔘.map_faceProjection_left,
    𝔘.map_faceProjection_left, 𝔘.comp_qlift, 𝔘.comp_qlift, 𝔘.comp_qlift,
    pullUnit_qlift_eq_gAt, pullUnit_qlift_eq_gAt, pullUnit_qlift_eq_gAt] at h
  change _ = pullUnit 0 _ at h
  rw [pullUnit_zero] at h
  simp only [CechCovering.qlift_π] at h
  change gAt g h₁ h₂ * (gAt g h₀ h₂)⁻¹ * gAt g h₀ h₁ = 1 at h
  rw [← mul_inv_eq_one]
  rw [show gAt g h₀ h₁ * gAt g h₁ h₂ * (gAt g h₀ h₂)⁻¹ =
    gAt g h₁ h₂ * (gAt g h₀ h₂)⁻¹ * gAt g h₀ h₁ by ac_rfl]
  exact h

private lemma gAt_self
    (hg : Stacks.CechSite.cechDifferential 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 1 g = 0)
    {T : SmallEtale B S hS} {i : 𝔘.toPreZeroHypercover.I₀} (h₀ : T ⟶ 𝔘.obj i) :
    gAt g h₀ h₀ = 1 := by
  have := gAt_mul_gAt hg h₀ h₀ h₀
  rwa [mul_eq_left] at this

end Construction

/-- Restriction of sections of the structure sheaf of the small étale site. -/
private abbrev ores {V W : SmallEtale B S hS} (f : V ⟶ W) :
    (SmallEtale.structureSheaf B S hS).obj.obj (op W) →+*
      (SmallEtale.structureSheaf B S hS).obj.obj (op V) :=
  ((SmallEtale.structureSheaf B S hS).obj.map f.op).hom

private lemma ores_comp {V W X : SmallEtale B S hS} (f : V ⟶ W) (f' : W ⟶ X)
    (x : (SmallEtale.structureSheaf B S hS).obj.obj (op X)) :
    ores (f ≫ f') x = ores f (ores f' x) := by
  simp only [ores, op_comp, Functor.map_comp, RingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]

private lemma ores_id {V : SmallEtale B S hS}
    (x : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) :
    ores (𝟙 V) x = x := by
  simp only [ores, op_id, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]


section CocycleModule

variable [IsNoetherian S] [S.IsSeparated] {𝔘 : CechCovering (final B S hS)}
  (g : CechTrivialization.Cochain 𝔘 1)

attribute [local instance] hasBinaryProducts_of_hasTerminal_and_pullbacks in
/-- Binary products in the small étale site: fibre products over the final object. -/
private instance hasBinaryProducts_smallEtale : HasBinaryProducts (SmallEtale B S hS) :=
  have : HasTerminal (SmallEtale B S hS) := (SmallEtale.finalIsTerminal B S hS).hasTerminal
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

private lemma val_gAt_comp {T T' : SmallEtale B S hS} {i j : 𝔘.toPreZeroHypercover.I₀} (m : T' ⟶ T)
    (h₀ : T ⟶ 𝔘.obj i) (h₁ : T ⟶ 𝔘.obj j) :
    ((gAt g (m ≫ h₀) (m ≫ h₁) : _) : (SmallEtale.structureSheaf B S hS).obj.obj (op T')) =
      ores m (gAt g h₀ h₁ : _) := by
  rw [gAt_comp]
  rfl

/-- The families `(a_i)_i`, `a_i ∈ Γ(V ×_S U_i, 𝒪)`. -/
private def CocycleFamily (V : SmallEtale B S hS) : Type u :=
  ∀ i : 𝔘.toPreZeroHypercover.I₀,
    (SmallEtale.structureSheaf B S hS).obj.obj (op (V ⨯ 𝔘.obj i))

private instance (V : SmallEtale B S hS) : AddCommGroup (CocycleFamily (𝔘 := 𝔘) V) :=
  inferInstanceAs (AddCommGroup (∀ i : 𝔘.toPreZeroHypercover.I₀,
    (SmallEtale.structureSheaf B S hS).obj.obj (op (V ⨯ 𝔘.obj i))))

private instance (V : SmallEtale B S hS) :
    Module ((SmallEtale.structureSheaf B S hS).obj.obj (op V)) (CocycleFamily (𝔘 := 𝔘) V) :=
  letI (i : 𝔘.toPreZeroHypercover.I₀) : Module ((SmallEtale.structureSheaf B S hS).obj.obj (op V))
      ((SmallEtale.structureSheaf B S hS).obj.obj (op (V ⨯ 𝔘.obj i))) :=
    (ores (prod.fst : V ⨯ 𝔘.obj i ⟶ V)).toModule
  inferInstanceAs (Module _ (∀ i : 𝔘.toPreZeroHypercover.I₀,
    (SmallEtale.structureSheaf B S hS).obj.obj (op (V ⨯ 𝔘.obj i))))

private lemma CocycleFamily.smul_apply {V : SmallEtale B S hS}
    (r : (SmallEtale.structureSheaf B S hS).obj.obj (op V)) (a : CocycleFamily (𝔘 := 𝔘) V)
    (i : 𝔘.toPreZeroHypercover.I₀) : (r • a) i = ores prod.fst r * a i :=
  rfl

/-- **The sections of the line bundle of a cocycle** over `V`: the families `(a_i)_i`,
`a_i ∈ Γ(V ×_S U_i, 𝒪)`, with `a_j = g_{ij} a_i` on `V ×_S U_i ×_S U_j`, read at generalized
points. -/
private def cocycleSubmodule (V : SmallEtale B S hS) :
    Submodule ((SmallEtale.structureSheaf B S hS).obj.obj (op V)) (CocycleFamily (𝔘 := 𝔘) V) where
  carrier := {a | ∀ (i j : 𝔘.toPreZeroHypercover.I₀) (T : SmallEtale B S hS) (t : T ⟶ V)
      (h₀ : T ⟶ 𝔘.obj i) (h₁ : T ⟶ 𝔘.obj j),
      ores (prod.lift t h₁) (a j) = (gAt g h₀ h₁ : _) * ores (prod.lift t h₀) (a i)}
  add_mem' {a b} ha hb i j T t h₀ h₁ := by
    change ores _ (a j + b j) = _ * ores _ (a i + b i)
    rw [map_add, map_add, ha i j T t h₀ h₁, hb i j T t h₀ h₁, mul_add]
  zero_mem' i j T t h₀ h₁ := by
    change ores _ 0 = _ * ores _ 0
    rw [map_zero, map_zero, mul_zero]
  smul_mem' r a ha i j T t h₀ h₁ := by
    change ores _ (ores prod.fst r * a j) = _ * ores _ (ores prod.fst r * a i)
    rw [map_mul, map_mul, ← ores_comp, ← ores_comp, prod.lift_fst, prod.lift_fst,
      ha i j T t h₀ h₁]
    ring

/-- Restriction of families along `f : V' ⟶ V`. -/
private def cocycleRestrict {V V' : SmallEtale B S hS} (f : V' ⟶ V) :
    cocycleSubmodule g V →+ cocycleSubmodule g V' where
  toFun a := ⟨fun i ↦ ores (prod.map f (𝟙 _)) (a.1 i), by
    intro i j T t h₀ h₁
    change ores _ (ores _ (a.1 j)) = _ * ores _ (ores _ (a.1 i))
    rw [← ores_comp, ← ores_comp, prod.lift_map, prod.lift_map, Category.comp_id,
      Category.comp_id]
    exact a.2 i j T (t ≫ f) h₀ h₁⟩
  map_zero' := Subtype.ext (funext fun i ↦ map_zero (ores (prod.map f (𝟙 (𝔘.obj i)))))
  map_add' a b := Subtype.ext (funext fun i ↦ map_add (ores (prod.map f (𝟙 (𝔘.obj i)))) _ _)

private lemma cocycleRestrict_apply {V V' : SmallEtale B S hS} (f : V' ⟶ V)
    (a : cocycleSubmodule g V)
    (i : 𝔘.toPreZeroHypercover.I₀) :
    (cocycleRestrict g f a).1 i = ores (prod.map f (𝟙 _)) (a.1 i) :=
  rfl

/-- The abelian presheaf `V ↦ {(a_i) | a_j = g_{ij} a_i}`. -/
private def cocyclePresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (cocycleSubmodule g V.unop)
  map f := AddCommGrpCat.ofHom (cocycleRestrict g f.unop)
  map_id V := by
    ext a
    funext i
    change ores (prod.map (𝟙 V).unop (𝟙 (𝔘.obj i))) (a.1 i) = a.1 i
    rw [unop_id, prod.map_id_id, ores_id]
  map_comp f f' := by
    ext a
    funext i
    change ores _ (a.1 i) = ores _ (ores _ (a.1 i))
    rw [← ores_comp, unop_comp, prod.map_map, Category.comp_id]

private instance (V : (SmallEtale B S hS)ᵒᵖ) :
    Module ((SmallEtale.structureSheaf B S hS).obj.obj V) ((cocyclePresheaf g).obj V) :=
  inferInstanceAs (Module _ (cocycleSubmodule g V.unop))

/-- **The presheaf of modules of a cocycle.** -/
private def cocyclePresheafOfModules :
    PresheafOfModules.{u} (SmallEtale.structureSheaf B S hS).obj :=
  PresheafOfModules.ofPresheaf (cocyclePresheaf g) (by
    intro V V' f r a
    apply Subtype.ext
    funext i
    change ores _ (ores prod.fst r * a.1 i) = ores prod.fst (ores f.unop r) * ores _ (a.1 i)
    rw [map_mul, ← ores_comp, ← ores_comp, prod.map_fst])

end CocycleModule

/-! ### Sheafification and generators -/

section Sheafify

/-- The sheafification of a presheaf of `𝒪_{S,et}`-modules. -/
private abbrev sheafifyEt (P : PresheafOfModules.{u} (SmallEtale.structureSheaf B S hS).obj) :
    SmallEtale.OxetModule B S hS :=
  (Stacks.SheafOfModules.TensorSheafification.sheafify (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2).obj P

/-- The image of a section of a presheaf of modules in its sheafification. -/
private abbrev sheafifySection (P : PresheafOfModules.{u} (SmallEtale.structureSheaf B S hS).obj)
    (U : SmallEtale B S hS) (p : P.obj (op U)) : (sheafifyEt P).val.obj (op U) :=
  ((Stacks.SheafOfModules.TensorSheafification.toSheafify (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 P).app
      (op U)).hom p

private lemma sheafifySection_res (P : PresheafOfModules.{u} (SmallEtale.structureSheaf B S hS).obj)
    {U V : SmallEtale B S hS} (f : V ⟶ U) (p : P.obj (op U)) :
    (sheafifyEt P).res f (sheafifySection P U p) = sheafifySection P V (P.restrictₛₗ f.op p) :=
  (PresheafOfModules.naturality_apply
    (Stacks.SheafOfModules.TensorSheafification.toSheafify (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 P) f.op p).symm

private lemma sheafifySection_smul
    (P : PresheafOfModules.{u} (SmallEtale.structureSheaf B S hS).obj)
    (U : SmallEtale B S hS) (r : (SmallEtale.structureSheaf B S hS).obj.obj (op U))
    (p : P.obj (op U)) :
    sheafifySection P U (r • p) = r • sheafifySection P U p :=
  ((Stacks.SheafOfModules.TensorSheafification.toSheafify (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 P).app
      (op U)).hom.map_smul r p

/-- If multiplication by a section of a presheaf of modules is bijective over every object over
`U`, multiplication by its image in the sheafification is bijective over `U`: on the slice over
`U` the presheaf is isomorphic to the structure sheaf, hence a sheaf, and agrees with its
sheafification. -/
private lemma bijective_smul_sheafifySection
    (P : PresheafOfModules.{u} (SmallEtale.structureSheaf B S hS).obj)
    (U : SmallEtale B S hS) (p : P.obj (op U))
    (hp : ∀ ⦃V : SmallEtale B S hS⦄ (f : V ⟶ U), Function.Bijective
      (fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op V) ↦ r • P.restrictₛₗ f.op p)) :
    Function.Bijective (fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op U) ↦
      r • sheafifySection P U p) := by
  let X := smallEtaleRingedSite B S hS
  let η := (PresheafOfModules.toPresheaf _).map
    (Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 P)
  let η' := Functor.whiskerRight η (forget AddCommGrpCat)
  have : Presheaf.IsLocallyInjective X.J η := by
    change Presheaf.IsLocallyInjective X.J (CategoryTheory.toSheafify X.J P.presheaf)
    infer_instance
  have : Presheaf.IsLocallySurjective X.J η := by
    change Presheaf.IsLocallySurjective X.J (CategoryTheory.toSheafify X.J P.presheaf)
    infer_instance
  let R := (X.O.over U).obj ⋙ forget CommRingCat
  let T := (Over.forget U).op ⋙ P.presheaf ⋙ forget AddCommGrpCat
  let kf (V : (Over U)ᵒᵖ) : R.obj V → T.obj V :=
    fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op V.unop.left) ↦
      r • P.restrictₛₗ V.unop.hom.op p
  have hres {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
      P.restrictₛₗ f.unop.left.op (P.restrictₛₗ V.unop.hom.op p) =
        P.restrictₛₗ W.unop.hom.op p := by
    change P.map f.unop.left.op (P.map V.unop.hom.op p) = P.map W.unop.hom.op p
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w f.unop]
  have hknat {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (r : R.obj V) :
      kf W (R.map f r) = T.map f (kf V r) := by
    have hsm := (P.restrictₛₗ f.unop.left.op).map_smulₛₗ
      (r : (SmallEtale.structureSheaf B S hS).obj.obj (op V.unop.left))
      (P.restrictₛₗ V.unop.hom.op p)
    have e1 : kf W (R.map f r) =
        ((SmallEtale.structureSheaf B S hS).obj.map f.unop.left.op) r •
          P.restrictₛₗ f.unop.left.op (P.restrictₛₗ V.unop.hom.op p) := by
      change ((SmallEtale.structureSheaf B S hS).obj.map f.unop.left.op) r •
        P.restrictₛₗ W.unop.hom.op p = _
      rw [hres]
    exact e1.trans hsm.symm
  let k : R ⟶ T :=
    { app := fun V ↦ ↾(kf V)
      naturality := by
        intro V W f
        ext r
        exact hknat f r }
  have hk (V : (Over U)ᵒᵖ) : Function.Bijective (k.app V) := hp V.unop.hom
  have : IsIso k := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun V ↦ (ConcreteCategory.isIso_iff_bijective _).2 (hk V)
  have hR : Presheaf.IsSheaf (X.J.over U) R :=
    Presheaf.isSheaf_comp_of_isSheaf (X.J.over U) (X.O.over U).obj
      (forget CommRingCat.{u}) (X.O.over U).property
  have hT : Presheaf.IsSheaf (X.J.over U) T := (Presheaf.isSheaf_of_iso_iff (asIso k)).1 hR
  let ψ := Functor.whiskerLeft (Over.forget U).op η'
  have : Presheaf.IsLocallyInjective (X.J.over U) ψ :=
    Presheaf.isLocallyInjective_whisker (X.J.over U) X.J (Over.forget U) η'
  have : Presheaf.IsLocallySurjective (X.J.over U) ψ :=
    Presheaf.isLocallySurjective_whisker (X.J.over U) X.J (Over.forget U) η'
  let q : (⟨T, hT⟩ : Sheaf (X.J.over U) (Type u)) ⟶
      (sheafCompose (X.J.over U) (forget AddCommGrpCat.{u})).obj
        ((SheafOfModules.toSheaf _).obj ((sheafifyEt P).over U)) := ⟨ψ⟩
  have hqi : Sheaf.IsLocallyInjective q :=
    inferInstanceAs (Presheaf.IsLocallyInjective (X.J.over U) ψ)
  have hqs : Sheaf.IsLocallySurjective q :=
    inferInstanceAs (Presheaf.IsLocallySurjective (X.J.over U) ψ)
  have : IsIso q := (Sheaf.isLocallyBijective_iff_isIso q).1 ⟨hqi, hqs⟩
  have : IsIso ψ := (sheafToPresheaf _ _).map_isIso q
  have hη : Function.Bijective (ψ.app (op (Over.mk (𝟙 U)))) :=
    ConcreteCategory.bijective_of_isIso _
  have h := hη.comp (hk (op (Over.mk (𝟙 U))))
  have hr (r : (SmallEtale.structureSheaf B S hS).obj.obj (op U)) :
      ψ.app (op (Over.mk (𝟙 U))) (k.app (op (Over.mk (𝟙 U))) r) =
        r • sheafifySection P U p := by
    have h0 : k.app (op (Over.mk (𝟙 U))) r = r • p := by
      change r • P.restrictₛₗ (𝟙 U).op p = r • p
      congr 1
      change P.map (𝟙 U).op p = p
      rw [op_id, PresheafOfModules.map_id]
      rfl
    rw [h0]
    exact sheafifySection_smul P U r p
  exact (funext hr) ▸ h

/-- A section of a presheaf of modules by which multiplication is bijective over every object
over `U` becomes a generator of the sheafification over `U`. -/
private lemma isGenerator_sheafifySection
    (P : PresheafOfModules.{u} (SmallEtale.structureSheaf B S hS).obj)
    (U : SmallEtale B S hS) (p : P.obj (op U))
    (hp : ∀ ⦃V : SmallEtale B S hS⦄ (f : V ⟶ U), Function.Bijective
      (fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op V) ↦ r • P.restrictₛₗ f.op p)) :
    SmallEtale.IsGenerator (sheafifyEt P) U (sheafifySection P U p) := by
  intro V f
  change Function.Bijective (fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op V) ↦
    r • (sheafifyEt P).res f (sheafifySection P U p))
  rw [sheafifySection_res]
  refine bijective_smul_sheafifySection P V _ fun W g ↦ ?_
  have := hp (g ≫ f)
  have e : P.restrictₛₗ (g ≫ f).op p = P.restrictₛₗ g.op (P.restrictₛₗ f.op p) := by
    change P.map (g ≫ f).op p = P.map g.op (P.map f.op p)
    rw [op_comp, PresheafOfModules.map_comp_apply]
  rw [e] at this
  exact this

end Sheafify

/-! ### Surjectivity -/

section CocycleBundle

variable [IsNoetherian S] [S.IsSeparated] {𝔘 : CechCovering (final B S hS)}
  {g : CechTrivialization.Cochain 𝔘 1}
  (hg : Stacks.CechSite.cechDifferential 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 1 g = 0)

variable (g) in
/-- The section `g_{ki}(pr₁, pr₂)` of `𝒪` over `U_k ×_S U_i`. -/
private abbrev gFS (k i : 𝔘.toPreZeroHypercover.I₀) :
    (SmallEtale.structureSheaf B S hS).obj.obj (op (𝔘.obj k ⨯ 𝔘.obj i)) :=
  (gAt g (prod.fst : 𝔘.obj k ⨯ 𝔘.obj i ⟶ 𝔘.obj k) prod.snd : _)

include hg in
private lemma gAt_fst_snd_mem (k : 𝔘.toPreZeroHypercover.I₀) :
    (fun i ↦ gFS g k i : CocycleFamily (𝔘 := 𝔘) (𝔘.obj k)) ∈ cocycleSubmodule g (𝔘.obj k) := by
  intro i j T t h₀ h₁
  change ores _ (gFS g k j) = _ * ores _ (gFS g k i)
  rw [← val_gAt_comp, ← val_gAt_comp, prod.lift_fst, prod.lift_snd, prod.lift_fst,
    prod.lift_snd, ← Units.val_mul, ← gAt_mul_gAt hg t h₀ h₁, mul_comm]

/-- The generator `e_k = (g_{ki})_i` of the line bundle of a cocycle over `U_k`. -/
private def cocycleGenerator (k : 𝔘.toPreZeroHypercover.I₀) :
    (cocyclePresheafOfModules g).obj (op (𝔘.obj k)) :=
  (⟨_, gAt_fst_snd_mem hg k⟩ : cocycleSubmodule g (𝔘.obj k))

private lemma cocycleGenerator_bijective (k : 𝔘.toPreZeroHypercover.I₀) ⦃V : SmallEtale B S hS⦄
    (f : V ⟶ 𝔘.obj k) :
    Function.Bijective (fun r : (SmallEtale.structureSheaf B S hS).obj.obj (op V) ↦
      r • (cocyclePresheafOfModules g).restrictₛₗ f.op (cocycleGenerator hg k)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun a ↦ ores (prod.lift (𝟙 V) f) ((a : cocycleSubmodule g V).1 k), fun r ↦ ?_, fun a ↦ ?_⟩
  · change ores (prod.lift (𝟙 V) f) (ores prod.fst r *
      ores (prod.map f (𝟙 _)) (gFS g k k)) = r
    rw [map_mul, ← ores_comp, prod.lift_fst, ores_id, ← ores_comp,
      ← val_gAt_comp, prod.lift_map, Category.id_comp, Category.comp_id, prod.lift_fst,
      prod.lift_snd, gAt_self hg, Units.val_one, mul_one]
  · apply Subtype.ext
    funext i
    have ha := (a : cocycleSubmodule g V).2 k i (V ⨯ 𝔘.obj i) prod.fst (prod.fst ≫ f) prod.snd
    rw [prod.lift_fst_snd, ores_id,
      show prod.lift (prod.fst : V ⨯ 𝔘.obj i ⟶ V) (prod.fst ≫ f) = prod.fst ≫ prod.lift (𝟙 V) f
        by ext <;> simp, ores_comp] at ha
    change ores prod.fst (ores (prod.lift (𝟙 V) f) ((a : cocycleSubmodule g V).1 k)) *
      ores (prod.map f (𝟙 _)) (gFS g k i) = (a : cocycleSubmodule g V).1 i
    rw [ha, ← val_gAt_comp, prod.map_fst, prod.map_snd, Category.comp_id, mul_comm]

/-- **The line bundle of a cocycle** `g` on a covering `(U_i)`: the sheafification of
`V ↦ {(a_i) | a_j = g_{ij} a_i}`. -/
private abbrev cocycleBundle : SmallEtale.OxetModule B S hS :=
  sheafifyEt (cocyclePresheafOfModules g)

/-- The trivialization of the line bundle of a cocycle by the generators `e_k = (g_{ki})_i`. -/
private abbrev cocycleTrivialization : CechTrivialization (cocycleBundle (g := g)) where
  covering := 𝔘
  generator k := sheafifySection _ _ (cocycleGenerator hg k)
  isGenerator k := isGenerator_sheafifySection _ _ _ (cocycleGenerator_bijective hg k)

/-- **The transition family of the trivialization of the line bundle of a cocycle is the
cocycle**: `e_k = g_{kl} e_l`. -/
private lemma isTransition_cocycleTrivialization : (cocycleTrivialization hg).IsTransition g := by
  intro ν
  change (cocycleBundle (g := g)).res _ (sheafifySection _ _ (cocycleGenerator hg (ν 0))) =
    _ • (cocycleBundle (g := g)).res _ (sheafifySection _ _ (cocycleGenerator hg (ν 1)))
  rw [sheafifySection_res, sheafifySection_res, ← sheafifySection_smul]
  congr 1
  apply Subtype.ext
  funext i
  change ores (prod.map ((inclusion B S hS).map (𝔘.prodπ ν 0)) (𝟙 _)) (gFS g (ν 0) i) =
    ores prod.fst (toUnits (g ν) : _) *
      ores (prod.map ((inclusion B S hS).map (𝔘.prodπ ν 1)) (𝟙 _)) (gFS g (ν 1) i)
  have hfst : (ores prod.fst (toUnits (g ν) : _) :
      (SmallEtale.structureSheaf B S hS).obj.obj (op ((inclusion B S hS).obj (𝔘.prodObj ν) ⨯
        𝔘.obj i))) =
      ((gAt g ((prod.fst : (inclusion B S hS).obj (𝔘.prodObj ν) ⨯ 𝔘.obj i ⟶ _) ≫
        (inclusion B S hS).map (𝔘.prodπ ν 0))
        (prod.fst ≫ (inclusion B S hS).map (𝔘.prodπ ν 1)) : _ˣ) :
          (SmallEtale.structureSheaf B S hS).obj.obj
            (op ((inclusion B S hS).obj (𝔘.prodObj ν) ⨯ 𝔘.obj i))) := by
    rw [← pullUnit_qlift_eq_gAt g ν (fun a ↦ prod.fst ≫ (inclusion B S hS).map (𝔘.prodπ ν a)),
      ← 𝔘.eq_qlift]
    rfl
  rw [hfst, ← val_gAt_comp, ← val_gAt_comp, prod.map_fst, prod.map_snd, prod.map_fst,
    prod.map_snd, Category.comp_id, ← Units.val_mul, gAt_mul_gAt hg]

end CocycleBundle

/-- A Čech trivialization makes a module an étale line bundle. -/
private lemma CechTrivialization.isEtaleLineBundle [IsNoetherian S] [S.IsSeparated]
    {L : SmallEtale.OxetModule B S hS} (T : CechTrivialization L) :
    SmallEtale.IsEtaleLineBundle B S hS L := by
  rw [SmallEtale.isEtaleLineBundle_iff_nonempty_trivialization]
  refine ⟨⟨ULift.{u + 1} T.covering.toPreZeroHypercover.I₀, fun i ↦ T.covering.obj i.down,
    fun i ↦ (inclusion B S hS).map (T.covering.toPreZeroHypercover.f i.down), ?_,
    fun i ↦ T.generator i.down, fun i ↦ T.isGenerator i.down⟩⟩
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  have hx : x ∈ ⋃ ν, Set.range ((toScheme B S hS).map (T.covering.f ν)) := by
    rw [T.covering.iUnion_range]; trivial
  obtain ⟨ν, hν⟩ := Set.mem_iUnion.1 hx
  exact ⟨_, _, Sieve.ofArrows_mk _ _ (ULift.up ν), hν⟩

/-! ### The isomorphism `Pic_et(S) ≅ Ȟ¹(S, 𝒪^*)` -/

section Main

variable [IsNoetherian S] [S.IsSeparated]

/-- **`κ` is surjective**: every Čech class `[g]_𝔘` is the class of the line bundle of the
cocycle `g`. -/
lemma picardCechClass_surjective :
    Function.Surjective (picardCechClass (B := B) (S := S) (hS := hS)) := by
  intro x
  obtain ⟨𝔘, z, rfl⟩ := exists_cechClass_eq (unitsPresheaf B S hS) 1 x
  let g : CechTrivialization.Cochain 𝔘 1 :=
    Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor 𝔘.toPreZeroHypercover
      (unitsPresheaf B S hS) 1) z.1
  have hg : Stacks.CechSite.cechDifferential 𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 1 g =
      0 := by
    have hz : (Stacks.CechSite.cechComplex 𝔘.toPreZeroHypercover (unitsPresheaf B S hS)).d 1
        (1 + 1) z.1 = 0 := z.2
    simp only [g]
    rw [Stacks.CechSite.cechDifferential_productAddEquiv, hz]
    exact map_zero (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
      𝔘.toPreZeroHypercover (unitsPresheaf B S hS) (1 + 1)))
  let T := cocycleTrivialization hg
  have hL := isInvertible_of_isEtaleLineBundle _ T.isEtaleLineBundle
  refine ⟨etalePicardClass _ hL, ?_⟩
  rw [picardCechClass_etalePicardClass _ hL T,
    CechTrivialization.cechH1Class_eq T (isTransition_cocycleTrivialization hg)]
  congr 1
  apply Subtype.ext
  exact AddEquiv.symm_apply_apply (Stacks.CechSite.productAddEquiv (Stacks.CechSite.cochainFactor
    𝔘.toPreZeroHypercover (unitsPresheaf B S hS) 1)) z.1

/-- `κ`, as a homomorphism of abelian groups. -/
def picardCechClassHom : EtalePicardGroup B S hS →+
    cechCohomologyOfObject (final B S hS) (unitsPresheaf B S hS) 1 :=
  AddMonoidHom.mk' picardCechClass picardCechClass_add

lemma picardCechClassHom_injective :
    Function.Injective (picardCechClassHom (B := B) (S := S) (hS := hS)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨L, hL, rfl⟩ : ∃ (L : SmallEtale.OxetModule B S hS) (hL : _),
      etalePicardClass L hL = p := Stacks.SheafOfModules.Picard.exists_classOf_eq _ _ p
  obtain ⟨T⟩ := CechTrivialization.nonempty_cechTrivialization L
    (isEtaleLineBundle_of_isInvertible L hL)
  have h0 : T.cechH1Class = 0 := by
    rw [← picardCechClass_etalePicardClass L hL T]
    exact hp
  exact etalePicardClass_eq_zero_of_cechH1Class_eq_zero hL T h0

/-- **The étale Picard group is the first Čech cohomology of the units**:
`κ : Pic_et(S) ≅ Ȟ¹(S, 𝒪^*_{S,et})`, sending the class of an étale line bundle to the class of
the transition family of any of its trivializations. -/
@[weil "lem_fk102_cech_h1_units_eq_etale_pic"]
def etalePicardGroupAddEquivCechH1 : EtalePicardGroup B S hS ≃+
    cechCohomologyOfObject (final B S hS) (unitsPresheaf B S hS) 1 :=
  AddEquiv.ofBijective picardCechClassHom ⟨picardCechClassHom_injective, picardCechClass_surjective⟩

omit [IsNoetherian S] [S.IsSeparated] in
/-- **The group law of `Pic_et(S)` is the tensor product**: `[L] + [M] = [L ⊗ M]`. -/
@[weil "lem_fk102_cech_h1_units_eq_etale_pic"]
theorem etalePicardClass_add_etalePicardClass (L M : SmallEtale.OxetModule B S hS)
    (hL : SmallEtale.IsEtaleLineBundle B S hS L) (hM : SmallEtale.IsEtaleLineBundle B S hS M) :
    ∃ hLM : SmallEtale.IsEtaleLineBundle B S hS (etaleTensor L M),
      etalePicardClass L (isInvertible_of_isEtaleLineBundle L hL) +
          etalePicardClass M (isInvertible_of_isEtaleLineBundle M hM) =
        etalePicardClass (etaleTensor L M) (isInvertible_of_isEtaleLineBundle _ hLM) := by
  have := isInvertible_of_isEtaleLineBundle L hL
  have := isInvertible_of_isEtaleLineBundle M hM
  have hLM := Stacks.SheafOfModules.isInvertible_tensorSheaf (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L M
  exact ⟨isEtaleLineBundle_of_isInvertible _ hLM,
    Stacks.SheafOfModules.Picard.classOf_tensor (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L M _ _ _⟩

/-- **FK, Lemma I.2.10 (the explicit description of `κ`).** For an étale line bundle `L`, a
trivialization `((U_i ⟶ S)_i, (e_i))` of `L` and a family `g = (g_{ij})`,
`g_{ij} ∈ Γ(U_i ×_S U_j, 𝒪)^*`, with `e_i = g_{ij} e_j` on `U_i ×_S U_j` for all `i, j`, the
family `g` is a `1`-cocycle and `κ [L] = [g]_𝔘`. -/
@[weil "lem_fk102_cech_h1_units_eq_etale_pic"]
theorem etalePicardGroupAddEquivCechH1_etalePicardClass (L : SmallEtale.OxetModule B S hS)
    (hL : SmallEtale.IsEtaleLineBundle B S hS L) (T : CechTrivialization L)
    (g : CechTrivialization.Cochain T.covering 1) (hg : T.IsTransition g) :
    ∃ hz : CechTrivialization.toCochain g ∈
        cechCycles T.covering.toPreZeroHypercover (unitsPresheaf B S hS) 1,
      etalePicardGroupAddEquivCechH1 (etalePicardClass L (isInvertible_of_isEtaleLineBundle L hL)) =
        cechClass (unitsPresheaf B S hS) 1 T.covering ⟨CechTrivialization.toCochain g, hz⟩ :=
  ⟨T.toCochain_mem_cechCycles hg, (picardCechClass_etalePicardClass L _ T).trans
    (T.cechH1Class_eq hg)⟩

end Main

end AlgebraicGeometry.SmallNoetherianSeparatedEtale

