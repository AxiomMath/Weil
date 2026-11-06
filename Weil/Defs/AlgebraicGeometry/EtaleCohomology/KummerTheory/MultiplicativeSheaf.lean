module

public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Sites.EtalePresheafFk101
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf

/-!
# The multiplicative group as a presheaf on `Et(A)`

For a commutative ring `A`, the multiplicative group `𝐆_m` is the presheaf of abelian groups on
the étale category `Et(A)` with `𝐆_m(B) = Bˣ`, the group of units of `B`, a morphism
`f : B → C` of `Et(A)` acting by `u ↦ f(u)`.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.multiplicativeGroup A`: the presheaf `𝐆_m` on `Et(A)`.
- `AlgebraicGeometry.EtaleCategory.multiplicativeGroupSectionsEquiv`: the identification of the
  sections of `𝐆_m` over `B` with the units `Bˣ`, written additively.

## Main results

- `AlgebraicGeometry.EtaleCategory.multiplicativeGroupSectionsEquiv_map`: under this
  identification, restriction along a morphism `B → C` of `Et(A)` is `u ↦ f(u)`.

## Implementation notes

`𝐆_m` is not built from scratch: it is the restriction, along the inclusion
`Scheme.AffineEtale.Spec (Spec A)` of the affine étale site into the small étale site, of the
sheaf of invertible global functions `Stacks.Kummer.multiplicativePresheaf (Spec A)` of the small
étale site of `Spec A`. Its sections over `B` are therefore `Γ(Spec B, ⊤)ˣ`, which are identified
with `Bˣ` through `Scheme.ΓSpecIso`. The values are abelian groups in the universe
`max (u + 1) v` in which étale cohomology of `Spec A` is computed, the units being raised by
`ULift`; the group law is multiplication of units, written additively.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory Opposite

namespace AlgebraicGeometry

namespace EtaleCategory

/-- **The multiplicative group `𝐆_m` on `Et(A)`**: the presheaf of abelian groups
`B ↦ Bˣ` on the étale category of `A`. It is the restriction to affine étale `Spec A`-schemes of
the sheaf `Stacks.Kummer.multiplicativePresheaf (Spec A)` of invertible global functions. -/
@[weil "def_fk101_multiplicative_group_sheaf"]
def multiplicativeGroup (A : CommRingCat.{u}) : Presheaf A AddCommGrpCat.{max (u + 1) v} :=
  (Scheme.AffineEtale.Spec (Spec A)).op ⋙ Stacks.Kummer.multiplicativePresheaf.{u, v} (Spec A)

lemma multiplicativeGroup_eq (A : CommRingCat.{u}) :
    multiplicativeGroup.{v} A =
      (Scheme.AffineEtale.Spec (Spec A)).op ⋙
        Stacks.Kummer.multiplicativePresheaf.{u, v} (Spec A) := rfl

variable {A : CommRingCat.{u}}

/-- Sections of `𝐆_m` over `X` are, by definition, the invertible global functions on
`Spec B`, written additively and raised to the coefficient universe. -/
lemma multiplicativeGroup_obj (X : EtaleCategory A) :
    ToType ((multiplicativeGroup.{v} A).obj X) =
      ULift.{max (u + 1) v} (Additive (Γ(Spec X.unop.left.unop, ⊤))ˣ) := rfl

/-- **Sections of `𝐆_m` over `B` are the units of `B`.** For an object `X` of `Et(A)` with
underlying ring `B = X.unop.left.unop`, the sections of `𝐆_m` over `X` are `Bˣ`, written
additively. -/
@[weil "def_fk101_multiplicative_group_sheaf"]
def multiplicativeGroupSectionsEquiv (X : EtaleCategory A) :
    ToType ((multiplicativeGroup.{v} A).obj X) ≃+ Additive (X.unop.left.unop)ˣ :=
  (AddEquiv.ulift.{u, max (u + 1) v} (α := Additive (Γ(Spec X.unop.left.unop, ⊤))ˣ)).trans
    (MulEquiv.toAdditive (Units.mapEquiv
      (Scheme.ΓSpecIso X.unop.left.unop).commRingCatIsoToRingEquiv.toMulEquiv))

/-- **Restriction in `𝐆_m` is `u ↦ f(u)`.** For a morphism `g : X ⟶ Y` of `Et(A)`, with
underlying ring homomorphism `f = g.unop.left.unop : B → C`, the restriction map of `𝐆_m`
sends the section corresponding to a unit `u ∈ Bˣ` to the one corresponding to `f(u) ∈ Cˣ`. -/
@[weil "def_fk101_multiplicative_group_sheaf"]
lemma multiplicativeGroupSectionsEquiv_map {X Y : EtaleCategory A} (g : X ⟶ Y)
    (s : ToType ((multiplicativeGroup.{v} A).obj X)) :
    multiplicativeGroupSectionsEquiv Y ((multiplicativeGroup.{v} A).map g s) =
      Additive.ofMul (Units.map g.unop.left.unop.hom.toMonoidHom
        (multiplicativeGroupSectionsEquiv X s).toMul) := by
  obtain ⟨x⟩ := s
  change Additive (Γ(Spec X.unop.left.unop, ⊤))ˣ at x
  set y : (Γ(Spec X.unop.left.unop, ⊤))ˣ := Additive.toMul x
  apply Additive.toMul.injective
  ext
  change (Scheme.ΓSpecIso _).hom ((Spec.map g.unop.left.unop).appTop (y : _)) =
    g.unop.left.unop ((Scheme.ΓSpecIso _).hom (y : _))
  exact congr($(Scheme.ΓSpecIso_naturality g.unop.left.unop).hom (y : _))

end EtaleCategory

end AlgebraicGeometry
