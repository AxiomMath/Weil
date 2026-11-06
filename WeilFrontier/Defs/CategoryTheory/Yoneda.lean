module

public import Mathlib.CategoryTheory.Yoneda
public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf

/-!
# The presheaf represented by an `S`-scheme on the étale category

Let `S` be a scheme and `X'` an `S`-scheme. The presheaf of sets `h_{X'}` on the étale
category `Et(S)` sends an object `(U, u)` to the set `Hom_S(U, X')` of morphisms of `S`-schemes
`U ⟶ X'`, and a morphism `g : (U, u) ⟶ (V, v)` of `Et(S)` to the map `Hom_S(V, X') ⟶ Hom_S(U, X')`
given by composition with `g`. It is the Yoneda presheaf of `X'` on the category of `S`-schemes,
restricted along the embedding of `Et(S)` into `S`-schemes.

## Main definitions

* `AlgebraicGeometry.representablePresheaf` — the presheaf `h_{X'}` on
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale B S hS`.
* `AlgebraicGeometry.representablePresheafFunctor` — `X' ↦ h_{X'}`, functorial in `X'`.
* `AlgebraicGeometry.representablePresheaf.sectionsEquiv` — the sections of `h_{X'}` over `(U, u)`
  are the morphisms of schemes `f : U ⟶ X'` with `f ≫ (X' ⟶ S) = u`.
* `AlgebraicGeometry.representablePresheaf.toOverIso` — for `X'` itself an object of `Et(S)`,
  `h_{X'}` is the Yoneda presheaf of that object of `Et(S)`.
* `AlgebraicGeometry.Scheme.representablePresheaf` — the same for a bare scheme `X`, on
  `AlgebraicGeometry.Scheme.noetherianSeparatedEtale X`.

## Main results

* `AlgebraicGeometry.representablePresheaf.map_apply` and
  `AlgebraicGeometry.representablePresheaf.sectionsEquiv_map_apply` — restriction is composition.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

open SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The presheaf represented by an `S`-scheme.** For an `S`-scheme `X'`, `h_{X'}` is the
presheaf of sets `U ↦ Hom_S(U, X')` on `Et(S)`, with restriction by composition: the Yoneda
presheaf of `X'` on `S`-schemes restricted along `Et(S) ⥤ Over S`. -/
@[weil "def_fk102_representable_presheaf"]
def representablePresheaf (X' : Over S) : EtalePresheaf B S hS (Type u) :=
  (toOver B S hS).op ⋙ yoneda.obj X'

/-- The functor `X' ↦ h_{X'}` from `S`-schemes to presheaves of sets on `Et(S)`. -/
def representablePresheafFunctor : Over S ⥤ EtalePresheaf B S hS (Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (toOver B S hS).op

@[simp]
lemma representablePresheafFunctor_obj (X' : Over S) :
    (representablePresheafFunctor B S hS).obj X' = representablePresheaf B S hS X' :=
  rfl

@[simp]
lemma representablePresheafFunctor_map_app_apply {X' Y' : Over S} (φ : X' ⟶ Y')
    (U : (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ)
    (f : (representablePresheaf B S hS X').obj U) :
    ((representablePresheafFunctor B S hS).map φ).app U f = f ≫ φ :=
  rfl

namespace representablePresheaf

variable {B S hS}

@[simp]
lemma obj_eq (X' : Over S) (U : (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ) :
    (representablePresheaf B S hS X').obj U = ((toOver B S hS).obj U.unop ⟶ X') :=
  rfl

/-- Restriction in `h_{X'}` along `g : U ⟶ V` is composition with `g`. -/
@[simp]
lemma map_apply (X' : Over S) {U V : SmallNoetherianSeparatedEtale B S hS} (g : U ⟶ V)
    (f : (representablePresheaf B S hS X').obj (op V)) :
    (representablePresheaf B S hS X').map g.op f = (toOver B S hS).map g ≫ f :=
  rfl

/-- **Sections of `h_{X'}`.** A section of `h_{X'}` over `(U, u)` is a morphism of schemes
`f : U ⟶ X'` with `f ≫ (X' ⟶ S) = u`. -/
def sectionsEquiv (X' : Over S) (U : SmallNoetherianSeparatedEtale B S hS) :
    (representablePresheaf B S hS X').obj (op U) ≃
      {f : (toScheme B S hS).obj U ⟶ X'.left // f ≫ X'.hom = structureMorphism U} where
  toFun f := ⟨f.left, Over.w f⟩
  invFun f := Over.homMk (U := (toOver B S hS).obj U) (V := X') f.1 f.2
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma sectionsEquiv_apply_coe (X' : Over S) (U : SmallNoetherianSeparatedEtale B S hS)
    (f : (representablePresheaf B S hS X').obj (op U)) :
    (sectionsEquiv X' U f : (toScheme B S hS).obj U ⟶ X'.left) =
      (f : (toOver B S hS).obj U ⟶ X').left :=
  rfl

/-- Under `sectionsEquiv`, restriction along `g : U ⟶ V` is composition with the underlying
morphism of schemes of `g`. -/
lemma sectionsEquiv_map_apply (X' : Over S) {U V : SmallNoetherianSeparatedEtale B S hS}
    (g : U ⟶ V) (f : (representablePresheaf B S hS X').obj (op V)) :
    (sectionsEquiv X' U ((representablePresheaf B S hS X').map g.op f) :
        (toScheme B S hS).obj U ⟶ X'.left) =
      (toScheme B S hS).map g ≫ (sectionsEquiv X' V f :
        (toScheme B S hS).obj V ⟶ X'.left) :=
  rfl

/-- For an object `U'` of `Et(S)`, the presheaf represented by the `S`-scheme underlying `U'`
is the Yoneda presheaf of `U'` on `Et(S)`, since `Et(S)` is a full subcategory of `S`-schemes. -/
def toOverIso (U' : SmallNoetherianSeparatedEtale B S hS) :
    representablePresheaf B S hS ((toOver B S hS).obj U') ≅ yoneda.obj U' :=
  NatIso.ofComponents
    (fun U ↦ ((fullyFaithfulToOver B S hS).homEquiv (X := U.unop) (Y := U')).symm.toIso)
    (fun {U V} g ↦ by
      ext (f : (toOver B S hS).obj U.unop ⟶ (toOver B S hS).obj U')
      change (fullyFaithfulToOver B S hS).preimage ((toOver B S hS).map g.unop ≫ f) =
        g.unop ≫ (fullyFaithfulToOver B S hS).preimage f
      exact (fullyFaithfulToOver B S hS).map_injective (by simp))

lemma isRepresentable_toOver (U' : SmallNoetherianSeparatedEtale B S hS) :
    (representablePresheaf B S hS ((toOver B S hS).obj U')).IsRepresentable :=
  Functor.IsRepresentable.mk' (toOverIso U').symm

end representablePresheaf

/-- The presheaf `h_{X'}` represented by an `X`-scheme `X'` on the étale category `Et(X)` of a
bare scheme `X`. -/
@[weil "def_fk102_representable_presheaf"]
noncomputable abbrev Scheme.representablePresheaf (X : Scheme.{u}) (X' : Over X) :
    X.EtalePresheaf (Type u) :=
  AlgebraicGeometry.representablePresheaf (BigEtaleSite.containing X) X
    (BigEtaleSite.contains_containing X) X'

end AlgebraicGeometry

end
