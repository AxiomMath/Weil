module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.LeftAdjointPushforwardFiber
public import Weil.AlgebraicGeometry.Morphisms.Etale.OverField
public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness

/-!
# Stalks of the extension by zero along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of schemes and let `α : Spec Ω ⟶ Y` be a geometric point
with `Ω` separably closed. The geometric points of `X` over `α` are the morphisms
`β : Spec Ω ⟶ X` with `β ≫ f = α`. For every abelian sheaf `F` on the small étale site of `X`,
the stalk of the extension by zero `f_! F` at `α` is the direct sum of the stalks of `F` at the
geometric points over `α`,
```
  (f_! F)_α ≅ ∐_{β ≫ f = α} F_β,
```
naturally in `F`. When `f` is moreover quasi-compact there are only finitely many such `β`, and
the direct sum is the product `∏_{β ≫ f = α} F_β`.

The proof is by adjunction. The stalk functor at `α` is left adjoint to the skyscraper sheaf
functor, and `f_!` is left adjoint to restriction along `f`, so `F ↦ (f_! F)_α` is left adjoint
to `M ↦ (α_* M)|_X`. Over an étale `X`-scheme `U`, the sections of `(α_* M)|_X` are the product
of copies of `M` indexed by the lifts of `α` to `U → X → Y`, and such a lift is the same as a
geometric point `β` of `X` over `α` together with a lift of `β` to `U`. Hence `(α_* M)|_X` is the
product of the skyscraper sheaves `β_* M`, which is right adjoint to `F ↦ ∐_β F_β`.

Finiteness of the set of `β` comes from base change: the `β` are the sections of the projection
`X ×_Y Spec Ω ⟶ Spec Ω`, which is étale and quasi-compact, hence a finite coproduct of copies of
`Spec Ω`; a section of such a coproduct is the inclusion of one of the summands.

## Main definitions

* `AlgebraicGeometry.GeometricPointsOver`: the geometric points of `X` over a geometric point
  of `Y`.
* `AlgebraicGeometry.extensionByZeroSheafFiberIsoSigma`: the natural isomorphism
  `(f_! F)_α ≅ ∐_β F_β`.
* `AlgebraicGeometry.extensionByZeroSheafFiberIsoPi`: for `f` quasi-compact, the natural
  isomorphism `(f_! F)_α ≅ ∏_β F_β`.

## Main results

* `AlgebraicGeometry.finite_geometricPointsOver`: for `f` étale and quasi-compact there are only
  finitely many geometric points of `X` over `α`.

## Implementation notes

Extension by zero is `Stacks.EtaleCohomology.extensionByZero`, on Mathlib's small étale site
`X.Etale` with coefficients `AddCommGrpCat.{max (u + 1) v}`; the stalk at a geometric point is the
fibre functor of the point `AlgebraicGeometry.Scheme.pointSmallEtale` of that site. The adjunction
argument is the Stacks Project's
`CategoryTheory.GrothendieckTopology.Point.sheafFiberLeftAdjointIso`, applied to composition with
`f` and the decomposition of fibres `AlgebraicGeometry.pointSmallEtaleFiberSigmaEquiv`.

Étale morphisms in the sense of [FK] are of finite type, hence quasi-compact over a noetherian
base; Mathlib's `AlgebraicGeometry.Etale` only asks for local finite presentation, so the
finiteness statement carries the hypothesis `QuasiCompact f`. Without it the set of geometric
points over `α` can be infinite (take `X` an infinite disjoint union of copies of `Y`), and the
stalk formula is the coproduct form.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.2 (4).
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

/-- In a preadditive category with finite biproducts, the coproduct and the product of a
finite family are naturally isomorphic. -/
def sigmaFunctorIsoPiFunctor {C : Type*} [Category* C] [Preadditive C] [HasFiniteBiproducts C]
    (ι : Type*) [Finite ι] : Sigma.functor ι (C := C) ≅ Pi.functor ι :=
  NatIso.ofComponents
    (fun F => ((biproduct.isoCoproduct F).symm ≪≫ biproduct.isoProduct F : ∐ F ≅ ∏ᶜ F))
    (fun {F G} φ => by
      change Sigma.map φ ≫ _ = _ ≫ Pi.map φ
      refine Sigma.hom_ext _ _ fun i => Pi.hom_ext _ _ fun j => ?_
      simp only [biproduct.isoCoproduct_inv, biproduct.isoProduct_hom, Iso.trans_hom, Iso.symm_hom,
        Sigma.ι_map_assoc, Category.assoc, limit.lift_π, Fan.mk_π_app, Pi.map_π,
        colimit.ι_desc_assoc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as, limit.lift_π_assoc]
      by_cases h : i = j
      · subst h
        simp
      · rw [biproduct.ι_π_ne_assoc _ h, biproduct.ι_π_ne _ h, Limits.zero_comp,
          Limits.comp_zero])

end CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme Scheme.Etale Stacks.EtaleCohomology CategoryTheory.GrothendieckTopology

universe v u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (α : Spec (.of Ω) ⟶ Y)

/-- The geometric points of `X` lying over a geometric point `α` of `Y`, that is, the lifts of
`α` along `f`. -/
abbrev GeometricPointsOver : Type u := {β : Spec (.of Ω) ⟶ X // β ≫ f = α}

/-- A lift `t` of a geometric point `β` to an étale `X`-scheme `U` satisfies
`t ≫ U.hom = β`. -/
lemma pointSmallEtale_fiber_w {β : Spec (.of Ω) ⟶ X} {U : X.Etale}
    (t : (pointSmallEtale β).fiber.obj U) : t.left ≫ U.hom = β := by
  simpa using Over.w t

/-- A point of the fiber of `pointSmallEtale β` over `U` is a lift of `β` along `U → X`. -/
def pointSmallEtaleFiberEquivSubtype (β : Spec (.of Ω) ⟶ X) (U : X.Etale) :
    (pointSmallEtale β).fiber.obj U ≃ {t : Spec (.of Ω) ⟶ U.left // t ≫ U.hom = β} where
  toFun t := ⟨t.left, pointSmallEtale_fiber_w t⟩
  invFun t := Over.homMk t.1 (show t.1 ≫ U.hom = β from t.2)
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := rfl

/-- A lift of `α` to an étale `X`-scheme `U` is a lift, along `U → X`, of a geometric point of
`X` over `α`. -/
def pointSmallEtaleFiberSigmaEquiv (U : X.Etale) :
    (Σ β : GeometricPointsOver f α, (pointSmallEtale β.1).fiber.obj U) ≃
      (pointSmallEtale α).fiber.obj ((smallEtaleCompose f).obj U) :=
  (Equiv.sigmaCongrRight fun β : GeometricPointsOver f α =>
      pointSmallEtaleFiberEquivSubtype β.1 U).trans <|
    (({ toFun s := ⟨s.2.1, by rw [← Category.assoc, s.2.2, s.1.2]⟩
        invFun t := ⟨⟨t.1 ≫ U.hom, (Category.assoc _ _ _).trans t.2⟩, ⟨t.1, rfl⟩⟩
        left_inv := by
          rintro ⟨⟨β, hβ⟩, ⟨t, ht⟩⟩
          change t ≫ U.hom = β at ht
          subst ht
          rfl
        right_inv _ := rfl } :
      (Σ β : GeometricPointsOver f α, {t : Spec (.of Ω) ⟶ U.left // t ≫ U.hom = β.1}) ≃
        {t : Spec (.of Ω) ⟶ U.left // t ≫ U.hom ≫ f = α}).trans
      (pointSmallEtaleFiberEquivSubtype α ((smallEtaleCompose f).obj U)).symm)

/-- The decomposition `pointSmallEtaleFiberSigmaEquiv` does not change the underlying morphism of
schemes of a lift. -/
@[simp]
lemma pointSmallEtaleFiberSigmaEquiv_apply_left (U : X.Etale)
    (s : Σ β : GeometricPointsOver f α, (pointSmallEtale β.1).fiber.obj U) :
    (pointSmallEtaleFiberSigmaEquiv f α U s).left = s.2.left :=
  rfl

omit [IsSepClosed Ω] in
/-- A section of the codiagonal `∐ Spec Ω ⟶ Spec Ω` whose image lies in the `i`-th summand is
the inclusion of that summand. -/
lemma eq_sigmaι_of_comp_sigmaDesc_eq_id {r : ℕ}
    (t : Spec (.of Ω) ⟶ ∐ fun _ : Fin r => Spec (.of Ω))
    (ht : t ≫ Sigma.desc (fun _ => 𝟙 _) = 𝟙 _) (i : Fin r)
    (hi : t default ∈ Set.range (Sigma.ι (fun _ : Fin r => Spec (.of Ω)) i)) :
    t = Sigma.ι (fun _ : Fin r => Spec (.of Ω)) i := by
  have H : Set.range t ⊆ Set.range (Sigma.ι (fun _ : Fin r => Spec (.of Ω)) i) := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z default]
  have hg := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : Fin r => Spec (.of Ω)) i) t H
  set g := IsOpenImmersion.lift (Sigma.ι (fun _ : Fin r => Spec (.of Ω)) i) t H
  have h1 : g = 𝟙 _ := calc
    g = g ≫ Sigma.ι (fun _ : Fin r => Spec (.of Ω)) i ≫ Sigma.desc (fun _ => 𝟙 _) := by
      rw [Sigma.ι_desc, Category.comp_id]
    _ = t ≫ Sigma.desc (fun _ => 𝟙 _) := by rw [← Category.assoc, hg]
    _ = 𝟙 _ := ht
  rw [← hg, h1, Category.id_comp]

/-- **Finiteness of the geometric points over a geometric point.** For `f : X ⟶ Y` étale and
quasi-compact and a geometric point `α : Spec Ω ⟶ Y` with `Ω` separably closed, there are only
finitely many geometric points `β : Spec Ω ⟶ X` with `β ≫ f = α`. -/
@[weil "lem_fk108_extension_by_zero_stalk"]
theorem finite_geometricPointsOver [QuasiCompact f] : Finite (GeometricPointsOver f α) := by
  obtain ⟨r, E, hE⟩ :=
    exists_iso_sigma_fin_spec_of_etale_of_isSepClosed Ω (pullback.snd f α)
  let s : GeometricPointsOver f α → (Spec (.of Ω) ⟶ ∐ fun _ : Fin r => Spec (.of Ω)) := fun β =>
    pullback.lift β.1 (𝟙 _) (by rw [β.2, Category.id_comp]) ≫ E.inv
  have hs (β : GeometricPointsOver f α) : s β ≫ Sigma.desc (fun _ => 𝟙 _) = 𝟙 _ := by
    simp only [s, Category.assoc, ← hE, Iso.inv_hom_id_assoc, pullback.lift_snd]
  choose idx y hy using fun β : GeometricPointsOver f α =>
    (sigmaOpenCover (fun _ : Fin r => Spec (.of Ω))).exists_eq (s β default)
  let idx' : GeometricPointsOver f α → Fin r := idx
  refine Finite.of_injective idx' fun β₁ β₂ h => ?_
  have h₁ := eq_sigmaι_of_comp_sigmaDesc_eq_id (s β₁) (hs β₁) (idx β₁) ⟨_, hy β₁⟩
  have h₂ := eq_sigmaι_of_comp_sigmaDesc_eq_id (s β₂) (hs β₂) (idx β₂) ⟨_, hy β₂⟩
  have h₃ : s β₁ = s β₂ := h₁.trans ((congrArg (Sigma.ι (fun _ : Fin r => Spec (.of Ω))) h).trans
    h₂.symm)
  apply Subtype.ext
  have := congrArg (fun t => t ≫ E.hom ≫ pullback.fst f α) h₃
  simp only [s, Category.assoc, Iso.inv_hom_id_assoc] at this
  rwa [pullback.lift_fst, pullback.lift_fst] at this

/-- The decomposition `pointSmallEtaleFiberSigmaEquiv` is natural in the étale `X`-scheme. -/
lemma pointSmallEtaleFiberSigmaEquiv_naturality ⦃U V : X.Etale⦄ (g : U ⟶ V)
    (β : GeometricPointsOver f α) (x : (pointSmallEtale β.1).fiber.obj U) :
    (pointSmallEtale α).fiber.map ((smallEtaleCompose f).map g)
        (pointSmallEtaleFiberSigmaEquiv f α U ⟨β, x⟩) =
      pointSmallEtaleFiberSigmaEquiv f α V ⟨β, (pointSmallEtale β.1).fiber.map g x⟩ :=
  Over.OverMorphism.ext rfl

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- The stalk of the extension by zero `f_! F` at a geometric point `α` of `Y` is the direct sum
of the stalks of `F` at the geometric points of `X` over `α`, naturally in `F`. -/
def extensionByZeroSheafFiberIsoSigma :
    extensionByZero.{u, v} f ⋙ (pointSmallEtale α).sheafFiber ≅
      Point.sigmaSheafFiber (fun β : GeometricPointsOver f α => pointSmallEtale β.1) :=
  Point.sheafFiberLeftAdjointIso (smallEtaleCompose f) (pointSmallEtale α) _
    (pointSmallEtaleFiberSigmaEquiv f α) (pointSmallEtaleFiberSigmaEquiv_naturality f α)
    _ (extensionByZeroAdj.{u, v} f)

/-- **Stalks of the extension by zero** (FK I.8.2 (4)). For `f : X ⟶ Y` étale and quasi-compact
and a geometric point `α` of `Y`, the stalk at `α` of the extension by zero `f_! F` of an abelian
sheaf `F` on `X` is the product of the stalks of `F` at the finitely many geometric points of `X`
over `α`, naturally in `F`. -/
@[weil "lem_fk108_extension_by_zero_stalk"]
def extensionByZeroSheafFiberIsoPi [QuasiCompact f] :
    extensionByZero.{u, v} f ⋙ (pointSmallEtale α).sheafFiber ≅
      Functor.pi' (fun β : GeometricPointsOver f α => (pointSmallEtale β.1).sheafFiber) ⋙
        Pi.functor (GeometricPointsOver f α) :=
  haveI := finite_geometricPointsOver f α
  extensionByZeroSheafFiberIsoSigma f α ≪≫
    Functor.isoWhiskerLeft _ (sigmaFunctorIsoPiFunctor (GeometricPointsOver f α))

end AlgebraicGeometry

/-! ### Exactness of extension by zero along an étale morphism -/

/-!
# Exactness of extension by zero along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of schemes. Extension by zero `f_!` from abelian sheaves on
the small étale site of `X` to abelian sheaves on the small étale site of `Y` is an exact
functor: it carries an exact sequence `F₁ ⟶ F₂ ⟶ F₃` of abelian sheaves on `X` to an exact
sequence `f_! F₁ ⟶ f_! F₂ ⟶ f_! F₃` on `Y`.

The exactness of the functor is the Stacks Project's (Tag 03S5), on both presentations of the
small étale site; this file deduces from it the preservation of exact sequences, which is the
form in which the statement is used.

## Main results

* `AlgebraicGeometry.SmallEtale.exact_map_abelianExtensionByZero`: on the small étale site of
  Stacks Tag 021B, extension by zero along an object `U` of the small étale site of `X`
  carries exact sequences of abelian sheaves to exact sequences.
* `AlgebraicGeometry.exact_map_extensionByZero`: the same on Mathlib's small étale site, for an
  arbitrary étale morphism `f : X ⟶ Y`.

## Implementation notes

The proof is formal from the exactness of `f_!` as a functor
(`AlgebraicGeometry.abelianExtensionByZero_exact`, `Stacks.EtaleCohomology.extensionByZero_exact`):
a functor between abelian categories preserving finite limits and finite colimits preserves
homology, hence exactness of short complexes. [FK] argue instead through stalks: the stalk of
`f_! F` at a geometric point of `Y` is the finite product of the stalks of `F` at the geometric
points of `X` over it, and exactness of sheaves is checked stalkwise. The Stacks Project's proof
shows instead that `f_!` preserves monomorphisms, through the direct-sum formula for the presheaf
extension by zero and Grothendieck's axiom AB4 for abelian groups.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- **Extension by zero is exact**, on the small étale site of Stacks Tag 021B: for an object `U`
of the small étale site of `X`, with structure morphism `f : U ⟶ X`, extension by zero `f_!`
carries an exact sequence `F₁ ⟶ F₂ ⟶ F₃` of abelian sheaves on `U` to an exact sequence
`f_! F₁ ⟶ f_! F₂ ⟶ f_! F₃` on `X`. -/
@[weil "lem_fk108_extension_by_zero_exact"]
theorem SmallEtale.exact_map_abelianExtensionByZero (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (U : SmallEtale B X hX)
    {S : ShortComplex
      (Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1})}
    (hS : S.Exact) : (S.map (abelianExtensionByZero B X hX U)).Exact := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp (abelianExtensionByZero_exact B X hX U)
  exact hS.map _

/-- **Extension by zero is exact**, on Mathlib's small étale site: for an étale morphism
`f : X ⟶ Y`, extension by zero `f_!` carries an exact sequence `F₁ ⟶ F₂ ⟶ F₃` of abelian
sheaves on `X` to an exact sequence `f_! F₁ ⟶ f_! F₂ ⟶ f_! F₃` on `Y`. -/
@[weil "lem_fk108_extension_by_zero_exact"]
theorem exact_map_extensionByZero {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (hS : S.Exact) : (S.map (Stacks.EtaleCohomology.extensionByZero.{u, v} f)).Exact := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).mp (Stacks.EtaleCohomology.extensionByZero_exact f)
  exact hS.map _

end AlgebraicGeometry

end
