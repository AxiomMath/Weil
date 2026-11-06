module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.FormulaAdjunction
public import Weil.Attr
public import Weil.AlgebraicGeometry.Sites.EtaleHomExt

/-!
# The direct-sum presheaf of extension by zero along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of schemes and `F` a sheaf on the small étale site of `X`.
The presheaf `P_f F` on the small étale site of `Y` has as sections over `V → Y` the direct sum
`⨁_φ F(V →^φ X)`, the sum over the `Y`-morphisms `φ : V ⟶ X` (which are automatically étale),
and the restriction map along a morphism `u : V' ⟶ V` over `Y` sends the summand `F(V, φ)` to
the summand `F(V', φ ∘ u)` by the map `F(u)`, `u` being regarded as a morphism
`(V', φ ∘ u) ⟶ (V, φ)` over `X`. For `s ∈ F(V, φ)` one writes `[φ, s]` for `s` placed in the
summand `φ`. Its sheafification is the extension by zero `f_! F`.

This presheaf is Stacks Tag 0F4K, formalized as
`Stacks.EtaleCohomology.extensionByZeroDirectSumPresheaf`; this file specializes it to sheaves
and records the description of its sections and restriction maps.

## Main definitions

* `AlgebraicGeometry.etaleExtensionByZeroPresheaf f F`: the presheaf `P_f F`.
* `AlgebraicGeometry.etaleExtensionByZeroPresheaf.mk f F φ s`: the section `[φ, s]` of `P_f F`,
  for a sheaf `F` of `Λ`-modules.
* `AlgebraicGeometry.Scheme.Etale.homSmallEtaleSourceEquiv`: morphisms `V ⟶ X` in the small étale
  site of `Y` are exactly the `Y`-morphisms of schemes `V ⟶ X`.

## Main results

* `AlgebraicGeometry.etaleExtensionByZeroPresheaf_obj`: the sections over `V` are the direct sum
  `⨁_φ F(V →^φ X)`.
* `AlgebraicGeometry.ι_comp_etaleExtensionByZeroPresheaf_map` and
  `AlgebraicGeometry.etaleExtensionByZeroPresheaf.map_mk`: the restriction map along `u` sends
  `[φ, s]` to `[φ ∘ u, F(u) s]`.
* `AlgebraicGeometry.etaleExtensionByZeroPresheaf.hom_ext`: a morphism out of the sections of
  `P_f F` over `V` is determined by its values on the elements `[φ, s]`.

## Implementation notes

The presheaf is stated on Mathlib's small étale site `Y.Etale`, where the construction of the
Stacks Project lives, with coefficients in an arbitrary category with coproducts; the source's
sheaves of `Λ`-modules are the case `A = ModuleCat Λ`. The index set of the direct sum is the set
of morphisms `V ⟶ X` of `Y.Etale`; `Scheme.Etale.homSmallEtaleSourceEquiv` identifies it with the
set of `Y`-morphisms of schemes, each of which is étale
(`Scheme.Etale.etale_left_of_hom_smallEtaleSource`).

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 0F4K](https://stacks.math.columbia.edu/tag/0F4K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale

universe w₂ w₁ w u

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]

/-- The morphisms `V ⟶ X` of the small étale site of `Y` are the `Y`-morphisms of schemes
`V ⟶ X`. -/
def homSmallEtaleSourceEquiv (V : Y.Etale) :
    (V ⟶ smallEtaleSource f) ≃ {φ : V.left ⟶ X // φ ≫ f = V.hom} where
  toFun φ := ⟨φ.left, by simpa using Over.w φ.toCommaMorphism⟩
  invFun φ := MorphismProperty.Over.homMk φ.1 φ.2
  left_inv φ := by ext; rfl
  right_inv φ := rfl

@[simp]
theorem homSmallEtaleSourceEquiv_apply_coe (V : Y.Etale) (φ : V ⟶ smallEtaleSource f) :
    (homSmallEtaleSourceEquiv f V φ : V.left ⟶ X) = φ.left :=
  rfl

end Scheme.Etale

section General

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
  {A : Type w₁} [Category.{w₂} A] [HasCoproducts.{u} A]
  [∀ F : (X.Etale)ᵒᵖ ⥤ A, (smallEtaleCompose f).op.HasPointwiseLeftKanExtension F]

/-- The presheaf `P_f F` on the small étale site of `Y` attached to an étale morphism
`f : X ⟶ Y` and a sheaf `F` on the small étale site of `X`: its sections over `V` are the direct
sum `⨁_φ F(V →^φ X)` over the morphisms `φ : V ⟶ X` over `Y`. Its sheafification is the extension
by zero `f_! F`. -/
@[weil "def_fk108_extension_by_zero_presheaf"]
abbrev etaleExtensionByZeroPresheaf (F : Sheaf X.smallEtaleTopology A) : (Y.Etale)ᵒᵖ ⥤ A :=
  Stacks.EtaleCohomology.extensionByZeroDirectSumPresheaf f F.obj

/-- The sections of `P_f F` over `V` are the direct sum `⨁_φ F(V →^φ X)`. -/
@[weil "def_fk108_extension_by_zero_presheaf"]
theorem etaleExtensionByZeroPresheaf_obj (F : Sheaf X.smallEtaleTopology A) (V : Y.Etale) :
    (etaleExtensionByZeroPresheaf f F).obj (op V) =
      ∐ fun φ : V ⟶ smallEtaleSource f => F.obj.obj (op (sourceDescend f φ)) :=
  rfl

/-- The restriction map of `P_f F` along `u : W ⟶ V` sends the summand indexed by `φ` to the
summand indexed by `u ≫ φ`, through the map `F` assigns to `u` regarded as a morphism over `X`. -/
@[weil "def_fk108_extension_by_zero_presheaf"]
theorem ι_comp_etaleExtensionByZeroPresheaf_map (F : Sheaf X.smallEtaleTopology A)
    {V W : Y.Etale} (u : W ⟶ V) (φ : V ⟶ smallEtaleSource f) :
    Sigma.ι (fun ψ : V ⟶ smallEtaleSource f => F.obj.obj (op (sourceDescend f ψ))) φ ≫
        (etaleExtensionByZeroPresheaf f F).map u.op =
      F.obj.map (sourceDescendMap f u φ).op ≫
        Sigma.ι (fun ψ : W ⟶ smallEtaleSource f => F.obj.obj (op (sourceDescend f ψ))) (u ≫ φ) :=
  Stacks.EtaleCohomology.ι_comp_extensionByZeroDirectSumPresheaf_map f F.obj u φ

end General

namespace etaleExtensionByZeroPresheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] {Λ : Type w} [Ring Λ]

/-- The section `[φ, s]` of `P_f F` over `V`: the section `s` of `F` over `V →^φ X`, placed in the
summand indexed by `φ`. -/
@[weil "def_fk108_extension_by_zero_presheaf"]
def mk (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : Y.Etale}
    (φ : V ⟶ smallEtaleSource f) (s : F.obj.obj (op (sourceDescend f φ))) :
    (etaleExtensionByZeroPresheaf f F).obj (op V) :=
  (Sigma.ι (fun ψ : V ⟶ smallEtaleSource f => F.obj.obj (op (sourceDescend f ψ))) φ).hom s

/-- The restriction map of `P_f F` along `u : W ⟶ V` sends `[φ, s]` to `[u ≫ φ, F(u) s]`. -/
@[weil "def_fk108_extension_by_zero_presheaf"]
theorem map_mk (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V W : Y.Etale}
    (u : W ⟶ V) (φ : V ⟶ smallEtaleSource f) (s : F.obj.obj (op (sourceDescend f φ))) :
    ((etaleExtensionByZeroPresheaf f F).map u.op).hom (mk f F φ s) =
      mk f F (u ≫ φ) ((F.obj.map (sourceDescendMap f u φ).op).hom s) := by
  change (Sigma.ι (fun ψ : V ⟶ smallEtaleSource f => F.obj.obj (op (sourceDescend f ψ))) φ ≫
      (etaleExtensionByZeroPresheaf f F).map u.op).hom s =
    (F.obj.map (sourceDescendMap f u φ).op ≫
      Sigma.ι (fun ψ : W ⟶ smallEtaleSource f => F.obj.obj (op (sourceDescend f ψ))) (u ≫ φ)).hom s
  rw [ι_comp_etaleExtensionByZeroPresheaf_map]
  rfl

/-- The map `s ↦ [φ, s]` is `Λ`-linear. -/
theorem mk_add (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : Y.Etale}
    (φ : V ⟶ smallEtaleSource f) (s t : F.obj.obj (op (sourceDescend f φ))) :
    mk f F φ (s + t) = mk f F φ s + mk f F φ t :=
  map_add _ s t

/-- The map `s ↦ [φ, s]` is `Λ`-linear. -/
theorem mk_smul (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : Y.Etale}
    (φ : V ⟶ smallEtaleSource f) (c : Λ) (s : F.obj.obj (op (sourceDescend f φ))) :
    mk f F φ (c • s) = c • mk f F φ s :=
  map_smul _ c s

/-- Two linear maps out of the sections of `P_f F` over `V` agree when they agree on every
section `[φ, s]`. -/
theorem hom_ext (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : Y.Etale}
    {M : ModuleCat.{u + 1} Λ} {g h : (etaleExtensionByZeroPresheaf f F).obj (op V) ⟶ M}
    (hgh : ∀ (φ : V ⟶ smallEtaleSource f) (s : F.obj.obj (op (sourceDescend f φ))),
      g.hom (mk f F φ s) = h.hom (mk f F φ s)) :
    g = h :=
  Sigma.hom_ext g h fun φ => ModuleCat.hom_ext (LinearMap.ext fun s => hgh φ s)

end etaleExtensionByZeroPresheaf

end AlgebraicGeometry
