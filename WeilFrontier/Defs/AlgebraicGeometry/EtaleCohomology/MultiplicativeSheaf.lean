module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtalePresheaf

/-!
# The étale presheaf of units

For a scheme `S`, the presheaf of units `𝒪^*_{S,et}` (also written `𝒪^*_S` or `𝐆_m`) on the
étale category `Et(S)` assigns to an object `U` the group `Γ(U, 𝒪_U)ˣ` of invertible global
functions on `U`, and to a morphism `h : U ⟶ V` the restriction `Γ(V, 𝒪_V)ˣ → Γ(U, 𝒪_U)ˣ`
induced by the ring map `h^# : Γ(V, 𝒪_V) → Γ(U, 𝒪_U)`. It is a presheaf of abelian groups,
the group law being written additively.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.unitsPresheaf`: the presheaf of units on
  `Et(S)`, as an `AlgebraicGeometry.EtalePresheaf` with values in `AddCommGrpCat`.
* `AlgebraicGeometry.Scheme.unitsEtalePresheaf`: the same for a bare scheme `X`, on
  `X.noetherianSeparatedEtale`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.unitsPresheaf_obj`: the sections over `U`
  are `Additive Γ(U, 𝒪_U)ˣ`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.unitsPresheaf_map_ofMul`: restriction along
  `h : U ⟶ V` sends a unit `x` to its image under `h^#`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.unitsPresheaf_eq_comp`: the presheaf is the
  restriction to `Et(S)` of the units presheaf on the small étale site of `S`.

## Implementation notes

The presheaf is the units presheaf `AlgebraicGeometry.unitsPresheaf` (global sections, then
units, written additively) of the functor `Et(S) ⥤ Scheme` sending `(U, u)` to `U`; nothing is
redefined. Its sheaf property on the small étale site is
`AlgebraicGeometry.unitsPresheaf_isSheaf_smallEtale`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The presheaf of units `𝒪^*_{S,et}` on `Et(S)`.** Its sections over `U` are the invertible
global functions `Γ(U, 𝒪_U)ˣ`, written additively, and restriction along `h : U ⟶ V` is induced
by `h^# : Γ(V, 𝒪_V) → Γ(U, 𝒪_U)`. -/
@[weil "def_fk102_units_sheaf"]
abbrev unitsPresheaf : EtalePresheaf B S hS AddCommGrpCat.{u} :=
  AlgebraicGeometry.unitsPresheaf (toScheme B S hS)

/-- The sections of `𝒪^*_{S,et}` over `U` are the units of `Γ(U, 𝒪_U)`, written additively. -/
lemma unitsPresheaf_obj (U : SmallNoetherianSeparatedEtale B S hS) :
    ToType ((unitsPresheaf B S hS).obj (op U)) = Additive (Γ((toScheme B S hS).obj U, ⊤))ˣ :=
  rfl

variable {B S hS}

/-- Restriction along `h : U ⟶ V` sends the unit `x` of `Γ(V, 𝒪_V)` to its image under
`h^# : Γ(V, 𝒪_V) → Γ(U, 𝒪_U)`. -/
@[simp]
lemma unitsPresheaf_map_ofMul {U V : SmallNoetherianSeparatedEtale B S hS} (h : U ⟶ V)
    (x : (Γ((toScheme B S hS).obj V, ⊤))ˣ) :
    (unitsPresheaf B S hS).map h.op (Additive.ofMul x : Additive (Γ((toScheme B S hS).obj V, ⊤))ˣ) =
      (Additive.ofMul (Units.map ((toScheme B S hS).map h).appTop.hom.toMonoidHom x) :
        Additive (Γ((toScheme B S hS).obj U, ⊤))ˣ) :=
  rfl

/-- The underlying function of a restriction: the value of the restricted unit is `h^#` of the
value of the unit. -/
lemma val_toMul_unitsPresheaf_map {U V : SmallNoetherianSeparatedEtale B S hS} (h : U ⟶ V)
    (x : Additive (Γ((toScheme B S hS).obj V, ⊤))ˣ) :
    ((Additive.toMul ((unitsPresheaf B S hS).map h.op x :
      Additive (Γ((toScheme B S hS).obj U, ⊤))ˣ) : (Γ((toScheme B S hS).obj U, ⊤))ˣ) :
        Γ((toScheme B S hS).obj U, ⊤)) =
      ((toScheme B S hS).map h).appTop.hom (Additive.toMul x : (Γ((toScheme B S hS).obj V, ⊤))ˣ) :=
  rfl

variable (B S hS)

/-- `𝒪^*_{S,et}` is the restriction to `Et(S)` of the units presheaf on the small étale site
of `S`. -/
lemma unitsPresheaf_eq_comp :
    unitsPresheaf B S hS =
      (inclusion B S hS).op ⋙ AlgebraicGeometry.unitsPresheaf (SmallEtale.toScheme B S hS) :=
  rfl

end SmallNoetherianSeparatedEtale

/-- **The presheaf of units `𝒪^*_{X,et}` on `Et(X)`** for a bare scheme `X`: sections over `U`
are `Γ(U, 𝒪_U)ˣ`, written additively, with restriction induced by `h^#`. -/
@[weil "def_fk102_units_sheaf"]
abbrev Scheme.unitsEtalePresheaf (X : Scheme.{u}) : X.EtalePresheaf AddCommGrpCat.{u} :=
  SmallNoetherianSeparatedEtale.unitsPresheaf (BigEtaleSite.containing X) X
    (BigEtaleSite.contains_containing X)

end AlgebraicGeometry

end
