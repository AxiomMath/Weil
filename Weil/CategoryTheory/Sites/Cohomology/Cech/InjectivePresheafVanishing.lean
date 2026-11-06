module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.Sites.Cohomology.Cech.FlabbySheaf
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import Weil.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverCofree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectiveSheafVanishing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Injective sheaves of `Λ`-modules on `Et(X)` are flabby

Let `Λ` be a ring and `I` an injective object of the category of sheaves of `Λ`-modules on the
étale category `Et(X)` of noetherian separated étale `X`-schemes. Then `I` is flabby: for every
object `U` of `Et(X)`, every étale covering `𝔘` of `U` and every `i > 0`, the Čech cohomology
`Ȟ^i(𝔘, I)` vanishes.

The proof has two steps. First, an injective sheaf is injective as a presheaf, since the
inclusion of sheaves into presheaves is right adjoint to sheafification, which preserves
monomorphisms. Second, for a presheaf `P` on a category `C` which is injective in the presheaf
category, the positive-degree Čech cohomology of `P` along any family `𝔘 = (Uᵢ ⟶ U)` vanishes.
For this, `P` is a retract of a *cofree* presheaf `W ↦ ∏_k ∏_{obj k ⟶ W} J_k`; restricted to the
slice `C/U`, that cofree presheaf receives a morphism from the cofree presheaf of `C/U` on the
objects `obj k ⟶ U` through which the restriction of `P` still splits, and the Čech complex of a
cofree presheaf on `C/U` has a contracting homotopy in positive degrees.

## Main results

* `Stacks.CechSite.isZero_cechCohomology_of_injective_presheaf`: the positive-degree Čech
  cohomology of a presheaf injective in the presheaf category vanishes, for any family of
  morphisms with fixed target and coefficients in any abelian category with enough products.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isFlabby_of_injective`: an injective sheaf of
  `Λ`-modules on `Et(X)` is flabby.

## Implementation notes

The source proves the second step by applying `Hom(-, I)` to the exact augmented Čech complex of
free `Λ`-module sheaves `K_•(𝔘, Λ)`. Here the dual argument by cofree presheaves is used: it
works in an arbitrary abelian coefficient category and needs no exactness statement about free
sheaves. The family `obj` indexing the cofree presheaf is only required to reach every object of
`C` up to isomorphism, so that, `Et(X)` being essentially small, the products involved are
indexed by small types.

Sheaves of `Λ`-modules are `CategoryTheory.Sheaf (topology B S hS) (ModuleCat.{u} Λ)`; flabbiness
is a condition on the underlying presheaf. The ring `Λ` need not be commutative.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory Stacks.CategoryTheory.CechComplex

universe t w v v' u₁ u' u

namespace Stacks.CechSite

variable {C : Type u₁} [Category.{v} C] {A : Type u'} [Category.{v'} A]

section Restrict

variable [HasProducts.{v} A] [HasProducts.{t} A] [HasProducts.{max t v} A]
  {κ : Type t} (obj : κ → C) (val : κ → A) (U : C)

/-- The objects of the slice `C/U` lying over the members of a family `obj : κ → C`: one for each
index `k` and each morphism `obj k ⟶ U`. -/
abbrev overFamily : (Σ k : κ, (obj k ⟶ U)) → Over U := fun p ↦ Over.mk p.2

omit [HasProducts.{t} A] in
/-- Projections of the cofree presheaf on the objects `obj k ⟶ U` of `C/U` only depend on the
underlying morphism of the index. -/
lemma cofreeπ_overFamily_congr {k : κ} {h h' : obj k ⟶ U} (e : h = h') {T : Over U}
    (g : overFamily obj U ⟨k, h⟩ ⟶ T) (g' : overFamily obj U ⟨k, h'⟩ ⟶ T) (hg : g.left = g'.left) :
    cofreeπ (overFamily obj U) (fun p ↦ val p.1) ⟨k, h⟩ g =
      cofreeπ (overFamily obj U) (fun p ↦ val p.1) ⟨k, h'⟩ g' := by
  subst e
  obtain rfl : g = g' := Over.OverMorphism.ext hg
  rfl

omit [HasProducts.{t} A] in
/-- The comparison from the cofree presheaf of the slice `C/U` on the objects `obj k ⟶ U` to the
restriction to `C/U` of the cofree presheaf of `C` on `obj`: the projection indexed by `k` and
`g : obj k ⟶ T` is the projection indexed by `obj k ⟶ U` and `g` as a morphism over `U`. -/
noncomputable def cofreeOverToRestrict :
    cofree (overFamily obj U) (fun p ↦ val p.1) ⟶ (Over.forget U).op ⋙ cofree obj val where
  app T := cofreeObjLift obj val fun k g ↦
    cofreeπ (overFamily obj U) (fun p ↦ val p.1) ⟨k, g ≫ T.unop.hom⟩ (Over.homMk g)
  naturality T T' f := by
    refine cofree_obj_hom_ext obj val fun k a ↦ ?_
    simp only [Functor.comp_map, Functor.op_map, Category.assoc, cofree_map_comp_cofreeπ,
      cofreeObjLift_comp_cofreeπ]
    exact cofreeπ_overFamily_congr obj val U (by simp [Over.w f.unop]) _ _ (by simp)

end Restrict

section Injective

variable [Abelian A] [HasProducts.{w} A] [HasProducts.{v} A] [HasProducts.{t} A]
  [HasProducts.{max t v} A]

/-- **Positive-degree Čech cohomology of an injective presheaf vanishes.** Let `P` be a presheaf
on `C` with values in an abelian category, injective in the presheaf category, and let
`E = (Uᵢ ⟶ U)` be a family of morphisms with fixed target whose finite fibre products exist. Then
`Ȟ^n(E, P) = 0` for `n > 0`.

The family `obj : κ → C` is only used to index a cofree presheaf into which `P` embeds; it must
reach every object of `C` up to isomorphism. -/
theorem isZero_cechCohomology_of_injective_presheaf {κ : Type t} (obj : κ → C)
    (hobj : ∀ W : C, ∃ k, Nonempty (obj k ≅ W)) {U : C} (E : PreZeroHypercover.{w} U)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (P : Cᵒᵖ ⥤ A) [Injective P] (n : ℕ) (hn : 0 < n) :
    IsZero (cechCohomology E P n) := by
  let val : κ → A := fun k ↦ P.obj (op (obj k))
  let s : P ⟶ cofree obj val := cofreeDesc obj val P fun _ ↦ 𝟙 _
  have : Mono s := by
    rw [NatTrans.mono_iff_mono_app]
    rintro ⟨W⟩
    obtain ⟨k, ⟨e⟩⟩ := hobj W
    have hfac : s.app (op W) ≫ cofreeπ obj val k e.hom = P.map e.hom.op := by
      simp [s]
    exact mono_of_mono_fac hfac
  let r : cofree obj val ⟶ P := Injective.factorThru (𝟙 P) s
  have hsr : s ≫ r = 𝟙 P := Injective.comp_factorThru _ _
  let obj' := overFamily obj U
  let val' : (Σ k : κ, (obj k ⟶ U)) → A := fun p ↦ val p.1
  let P' : (Over U)ᵒᵖ ⥤ A := (Over.forget U).op ⋙ P
  let s' : P' ⟶ cofree obj' val' := cofreeDesc obj' val' P' fun _ ↦ 𝟙 _
  let r' : cofree obj' val' ⟶ P' :=
    cofreeOverToRestrict obj val U ≫ Functor.whiskerLeft (Over.forget U).op r
  have hs : s' ≫ cofreeOverToRestrict obj val U = Functor.whiskerLeft (Over.forget U).op s := by
    ext ⟨T⟩ : 2
    refine cofree_obj_hom_ext obj val fun k a ↦ ?_
    simp only [s', s, cofreeOverToRestrict, P', obj', val', NatTrans.comp_app, Category.assoc,
      cofreeObjLift_comp_cofreeπ, Functor.whiskerLeft_app]
    erw [cofreeDesc_app_comp_cofreeπ, cofreeDesc_app_comp_cofreeπ]
    rfl
  have hsr' : s' ≫ r' = 𝟙 P' := by
    rw [← Category.assoc, hs, ← Functor.whiskerLeft_comp, hsr, Functor.whiskerLeft_id']
  exact FinalCover.isZero_homology_complexFunctor_of_retract_of_isZero
    (fun i ↦ Over.mk (E.f i)) n
    (FinalCover.isZero_homology_complexFunctor_cofree (fun i ↦ Over.mk (E.f i)) obj' val' n hn)
    s' r' hsr'

end Injective

end Stacks.CechSite

namespace AlgebraicGeometry.SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Injective sheaves of `Λ`-modules are flabby.** Let `Λ` be a ring and `I` an injective
object of the category of sheaves of `Λ`-modules on `Et(S)`. Then `Ȟ^i(𝔘, I) = 0` for every
`i > 0` and every étale covering `𝔘` of every object of `Et(S)`. -/
@[weil "lem_fk104_injective_lambda_sheaf_cech_acyclic"]
theorem isFlabby_of_injective {Λ : Type u} [Ring Λ]
    (I : Sheaf (topology B S hS) (ModuleCat.{u} Λ)) [Injective I] : IsFlabby I.obj := by
  have : HasSheafify (topology B S hS) (ModuleCat.{u} Λ) :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  have : Injective I.obj := I.injective_obj
  intro U E _ ν hν
  let e := equivSmallModel.{u} (SmallNoetherianSeparatedEtale B S hS)
  exact Stacks.CechSite.isZero_cechCohomology_of_injective_presheaf e.inverse.obj
    (fun W ↦ ⟨e.functor.obj W, ⟨(e.unitIso.app W).symm⟩⟩) E I.obj ν hν

end AlgebraicGeometry.SmallNoetherianSeparatedEtale
