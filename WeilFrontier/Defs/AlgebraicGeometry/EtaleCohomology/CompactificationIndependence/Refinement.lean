module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ExtensionByZeroEtale
public import Weil.Attr

/-!
# Exchange morphisms `j_! f_* ⟶ f'_* i_!`

Consider a commutative square of schemes
```
  X --i--> X'
  |        |
  f        f'
  v        v
  Y --j--> Y'
```
with `i` and `j` open immersions (in the source, `f` is moreover proper). For a sheaf `G` of
`Λ`-modules on the small étale site of `X` we compare `j_! f_* G` and `f'_* i_! G` on the small
étale site of `Y'`.

For `V` étale over `Y'` together with a factorisation `φ : V ⟶ Y` of `V ⟶ Y'` through `j`, write
`V_Y` for `V` regarded as étale over `Y` through `φ`, `X_V := V_Y ×_Y X`, étale over `X`, and
`X'_V := V ×_{Y'} X'`, étale over `X'`. The square induces the morphism `i_V : X_V ⟶ X'_V` over
`X'` (`X_V` being étale over `X'` through `i`).

* A section `s ∈ G(X_V) = (f_* G)(V_Y)` gives the section `[φ, s]` of the direct-sum presheaf
  `P_j (f_* G)` over `V`, and hence the section `c [φ, s]` of its sheafification `j_! f_* G`.
* The same `s`, placed in the summand of `P_i G` over `X_V` indexed by the structure morphism
  `X_V ⟶ X`, gives after sheafification the section `ι(s) ∈ (i_! G)(X_V)`.

A morphism `α : j_! f_* G ⟶ f'_* i_! G` is an *exchange morphism* if for all such `V`, `φ` and `s`
the section `t := α(c [φ, s]) ∈ (f'_* i_! G)(V) = (i_! G)(X'_V)` restricts to `ι(s)` along `i_V`
and restricts to zero along every étale `w : W ⟶ X'_V` whose image is disjoint from that of
`i_V`.

## Main definitions

* `AlgebraicGeometry.ExchangeSquare.sourceObj`: the object `X_V` of the small étale site of `X`.
* `AlgebraicGeometry.ExchangeSquare.targetObj`: the object `X'_V` of the small étale site of
  `X'`.
* `AlgebraicGeometry.ExchangeSquare.inclusion`: the morphism `i_V : X_V ⟶ X'_V` over `X'`.
* `AlgebraicGeometry.extensionByZeroPresheafToSheaf`: the canonical map `c : P_j F ⟶ j_! F`.
* `AlgebraicGeometry.extensionByZeroSection`: the section `ι(s)` of `i_! G` over an object `U`
  of the small étale site of `X`, regarded as étale over `X'` through `i`.
* `AlgebraicGeometry.IsOpenProperExchangeMorphism`: the exchange condition on a morphism
  `α : j_! f_* G ⟶ f'_* i_! G`.

## Implementation notes

The objects live on Mathlib's small étale site `X.Etale`, where the Stacks Project's extension by
zero `Stacks.EtaleCohomology.etaleModuleExtensionByZero` and direct image
`Stacks.EtaleCohomology.etaleModuleDirectImage` are defined; the source's abelian sheaves are
the case `Λ = ℤ`. A factorisation of `V ⟶ Y'` through `j` is a morphism `φ : V ⟶ Y` of the small
étale site of `Y'` (it is unique when `j` is a monomorphism, so quantifying over it loses nothing).
The definition of the exchange condition uses neither that `i`, `j` are open immersions nor that
`f` is proper, so it is stated for étale `i`, `j` and arbitrary `f`, `f'`; these hypotheses enter
the existence and uniqueness of exchange morphisms.

## References

* [FK] Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.8.5, pp. 87–88.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Etale Stacks.EtaleCohomology

universe r u

namespace AlgebraicGeometry

namespace ExchangeSquare

variable {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') (j : Y ⟶ Y') [Etale j]
  (f : X ⟶ Y) (f' : X' ⟶ Y')

/-- For `V` étale over `Y'` and a factorisation `φ : V ⟶ Y` through `j`, the object
`X_V = V ×_Y X` of the small étale site of `X`. -/
abbrev sourceObj {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) : X.Etale :=
  (smallEtaleBaseChange f).obj (sourceDescend j φ)

/-- For `V` étale over `Y'`, the object `X'_V = V ×_{Y'} X'` of the small étale site of `X'`. -/
abbrev targetObj (V : Y'.Etale) : X'.Etale :=
  (smallEtaleBaseChange f').obj V

theorem sourceObj_left {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    (sourceObj j f φ).left = pullback φ.left f :=
  rfl

theorem sourceObj_hom {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    (sourceObj j f φ).hom = pullback.snd φ.left f :=
  rfl

theorem targetObj_left (V : Y'.Etale) : (targetObj f' V).left = pullback V.hom f' :=
  rfl

theorem targetObj_hom (V : Y'.Etale) : (targetObj f' V).hom = pullback.snd V.hom f' :=
  rfl

variable {f f'}

/-- The morphism of schemes `X_V ⟶ X'_V` induced by the commutative square
`i ≫ f' = f ≫ j`. -/
def inclusionLeft (h : i ≫ f' = f ≫ j) {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    pullback φ.left f ⟶ pullback V.hom f' :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i) (by
    have hφ : φ.left ≫ j = V.hom := by simpa using MorphismProperty.Over.w φ
    have hc := pullback.condition_assoc (f := φ.left) (g := f) j
    rw [Category.assoc, h, ← hφ]
    exact hc)

@[reassoc (attr := simp)]
theorem inclusionLeft_fst (h : i ≫ f' = f ≫ j) {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    inclusionLeft i j h φ ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem inclusionLeft_snd (h : i ≫ f' = f ≫ j) {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    inclusionLeft i j h φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ i :=
  pullback.lift_snd _ _ _

variable [Etale i]

/-- The morphism `i_V : X_V ⟶ X'_V` of the small étale site of `X'`, where `X_V` is regarded as
étale over `X'` through `i`. -/
def inclusion (h : i ≫ f' = f ≫ j) {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    (smallEtaleCompose i).obj (sourceObj j f φ) ⟶ targetObj f' V :=
  MorphismProperty.Over.homMk (inclusionLeft i j h φ) (inclusionLeft_snd i j h φ) trivial

@[simp]
theorem inclusion_left (h : i ≫ f' = f ≫ j) {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j) :
    (inclusion i j h φ).left = inclusionLeft i j h φ :=
  rfl

end ExchangeSquare

section Sections

variable (Λ : Type r) [Ring Λ]

/-- The canonical map `c : P_j F ⟶ j_! F` from the direct-sum presheaf to its sheafification, the
extension by zero, along an étale morphism `j`. -/
def extensionByZeroPresheafToSheaf {Y Y' : Scheme.{u}} (j : Y ⟶ Y') [Etale j]
    (F : EtaleModules.{u, r} Λ Y) :
    etaleExtensionByZeroPresheaf j F ⟶ ((etaleModuleExtensionByZero.{u, r} Λ j).obj F).obj :=
  toSheafify Y'.smallEtaleTopology _ ≫ (etaleModuleExtensionByZeroObjIso Λ j F).inv.hom

/-- The structure morphism `U ⟶ X` of an object `U` of the small étale site of `X`, as a morphism
from `U`, regarded as étale over `X'` through `i`, to `X` in the small étale site of `X'`. -/
def structureHomToSource {X X' : Scheme.{u}} (i : X ⟶ X') [Etale i] (U : X.Etale) :
    (smallEtaleCompose i).obj U ⟶ smallEtaleSource i :=
  MorphismProperty.Over.homMk U.hom rfl trivial

/-- For an étale morphism `i : X ⟶ X'`, a sheaf `G` on the small étale site of `X` and a section
`s ∈ G(U)` over an object `U` of that site, the section `ι(s)` of `i_! G` over `U`, regarded as
étale over `X'` through `i`: the image of `s` under the summand of the direct-sum presheaf `P_i G`
indexed by the structure morphism `U ⟶ X`, followed by sheafification. -/
def extensionByZeroSection {X X' : Scheme.{u}} (i : X ⟶ X') [Etale i]
    (G : EtaleModules.{u, r} Λ X) (U : X.Etale) (s : G.obj.obj (op U)) :
    ((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.obj (op ((smallEtaleCompose i).obj U)) :=
  ((extensionByZeroPresheafToSheaf Λ i G).app (op ((smallEtaleCompose i).obj U))).hom
    ((Sigma.ι (fun ψ : (smallEtaleCompose i).obj U ⟶ smallEtaleSource i =>
      G.obj.obj (op (sourceDescend i ψ))) (structureHomToSource i U)).hom s)

end Sections

variable (Λ : Type r) [Ring Λ] {X X' Y Y' : Scheme.{u}} (i : X ⟶ X') [Etale i]
  (j : Y ⟶ Y') [Etale j] {f : X ⟶ Y} {f' : X' ⟶ Y'} (h : i ≫ f' = f ≫ j)
  (G : EtaleModules.{u, r} Λ X)

/-- The section `t = α(c [φ, s])` of `f'_* i_! G` over `V`, that is of `i_! G` over `X'_V`,
attached to a morphism `α : j_! f_* G ⟶ f'_* i_! G`, a factorisation `φ : V ⟶ Y` of `V ⟶ Y'`
through `j` and a section `s ∈ G(X_V) = (f_* G)(V_Y)`. -/
def exchangeSection
    (α : (etaleModuleExtensionByZero.{u, r} Λ j).obj ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
      (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj G))
    {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (ExchangeSquare.sourceObj j f φ))) :
    ((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.obj (op (ExchangeSquare.targetObj f' V)) :=
  (α.hom.app (op V)).hom
    (((extensionByZeroPresheafToSheaf Λ j ((etaleModuleDirectImage.{u, r} Λ f).obj G)).app
      (op V)).hom ((Sigma.ι (fun ψ : V ⟶ smallEtaleSource j =>
        ((etaleModuleDirectImage.{u, r} Λ f).obj G).obj.obj (op (sourceDescend j ψ))) φ).hom s))

/-- A morphism `α : j_! f_* G ⟶ f'_* i_! G` is an *exchange morphism* for the square
`i ≫ f' = f ≫ j` if for every `V` étale over `Y'`, every factorisation `φ : V ⟶ Y` of `V ⟶ Y'`
through `j` and every `s ∈ G(X_V)`, the section `t = α(c [φ, s]) ∈ (i_! G)(X'_V)` satisfies
`i_V^* t = ι(s)` and `w^* t = 0` for every `w : W ⟶ X'_V` in the small étale site of `X'` whose
image is disjoint from the image of `i_V`. -/
@[weil "def_fk108_open_proper_exchange_map"]
def IsOpenProperExchangeMorphism
    (α : (etaleModuleExtensionByZero.{u, r} Λ j).obj ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
      (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)) :
    Prop :=
  ∀ (V : Y'.Etale) (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (ExchangeSquare.sourceObj j f φ))),
    (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map
        (ExchangeSquare.inclusion i j h φ).op).hom (exchangeSection Λ i j G α φ s) =
      extensionByZeroSection Λ i G _ s ∧
    ∀ (W : X'.Etale) (w : W ⟶ ExchangeSquare.targetObj f' V),
      Disjoint (Set.range w.left.base) (Set.range (ExchangeSquare.inclusionLeft i j h φ).base) →
      (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map w.op).hom
        (exchangeSection Λ i j G α φ s) = 0

namespace IsOpenProperExchangeMorphism

variable {Λ i j h G}
variable {α : (etaleModuleExtensionByZero.{u, r} Λ j).obj
      ((etaleModuleDirectImage.{u, r} Λ f).obj G) ⟶
    (etaleModuleDirectImage.{u, r} Λ f').obj ((etaleModuleExtensionByZero.{u, r} Λ i).obj G)}

/-- For an exchange morphism `α`, the section `α(c [φ, s])` restricts to `ι(s)` along `i_V`. -/
theorem map_inclusion (hα : IsOpenProperExchangeMorphism Λ i j h G α) {V : Y'.Etale}
    (φ : V ⟶ smallEtaleSource j) (s : G.obj.obj (op (ExchangeSquare.sourceObj j f φ))) :
    (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map
        (ExchangeSquare.inclusion i j h φ).op).hom (exchangeSection Λ i j G α φ s) =
      extensionByZeroSection Λ i G _ s :=
  (hα V φ s).1

/-- For an exchange morphism `α`, the section `α(c [φ, s])` restricts to zero along every
`w : W ⟶ X'_V` whose image is disjoint from that of `i_V`. -/
theorem map_eq_zero_of_disjoint (hα : IsOpenProperExchangeMorphism Λ i j h G α)
    {V : Y'.Etale} (φ : V ⟶ smallEtaleSource j)
    (s : G.obj.obj (op (ExchangeSquare.sourceObj j f φ))) {W : X'.Etale}
    (w : W ⟶ ExchangeSquare.targetObj f' V)
    (hw : Disjoint (Set.range w.left.base)
      (Set.range (ExchangeSquare.inclusionLeft i j h φ).base)) :
    (((etaleModuleExtensionByZero.{u, r} Λ i).obj G).obj.map w.op).hom
      (exchangeSection Λ i j G α φ s) = 0 :=
  (hα V φ s).2 W w hw

end IsOpenProperExchangeMorphism

end AlgebraicGeometry
