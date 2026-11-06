module

public import Mathlib.CategoryTheory.Types.Basic
public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# Presheaves on the étale category

A presheaf (of sets, of abelian groups, ...) on the étale category `Et(S)` of a scheme `S` is a
contravariant functor from `Et(S)` to the category of sets (resp. of abelian groups, ...), and a
morphism of presheaves is a natural transformation. For a morphism `h : U ⟶ V` of `Et(S)` and a
section `s ∈ F(V)`, the restriction `h^* s ∈ F(U)` is `F.map h.op s`.

## Main definitions

* `AlgebraicGeometry.EtalePresheaf` — the category of presheaves with values in a category `C`
  on `AlgebraicGeometry.SmallNoetherianSeparatedEtale B S hS`, i.e. the functor category
  `(SmallNoetherianSeparatedEtale B S hS)ᵒᵖ ⥤ C`.
* `AlgebraicGeometry.Scheme.EtalePresheaf` — the same for a bare scheme `X`, over
  `AlgebraicGeometry.Scheme.noetherianSeparatedEtale X`.

## Main results

* `AlgebraicGeometry.EtalePresheaf.map_id_apply`, `AlgebraicGeometry.EtalePresheaf.map_comp_apply`
  — the restriction maps of a presheaf of sets are functorial: `id^* s = s` and
  `(g ≫ h)^* s = g^* (h^* s)`.
* `AlgebraicGeometry.EtalePresheaf.naturality_apply` — a morphism of presheaves of sets commutes
  with restriction.

## Implementation notes

No new structure is introduced: a presheaf is a functor out of the opposite category, morphisms
of presheaves are the morphisms of Mathlib's functor category (natural transformations), and the
restriction `h^* s` is written `F.map h.op s` throughout. Presheaves of sets take values in
`Type v`, presheaves of abelian groups in `AddCommGrpCat`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Presheaves on `Et(S)`.** A presheaf with values in a category `C` (sets, abelian groups,
...) on the étale category `Et(S)` is a contravariant functor `Et(S) ⥤ C`; morphisms of
presheaves are natural transformations. -/
@[weil "def_fk102_etale_presheaf"]
abbrev EtalePresheaf (C : Type v) [Category.{w} C] :=
  (SmallNoetherianSeparatedEtale B S hS)ᵒᵖ ⥤ C

/-- Presheaves with values in `C` on the étale category `Et(X)` of a bare scheme `X`. -/
@[weil "def_fk102_etale_presheaf"]
noncomputable abbrev Scheme.EtalePresheaf (X : Scheme.{u}) (C : Type v) [Category.{w} C] :=
  (X.noetherianSeparatedEtale)ᵒᵖ ⥤ C

namespace EtalePresheaf

variable {B S hS}

/-- Restriction along the identity is the identity: `id^* s = s`. -/
lemma map_id_apply (F : EtalePresheaf B S hS (Type v)) (U : SmallNoetherianSeparatedEtale B S hS)
    (s : F.obj (op U)) : F.map (𝟙 U).op s = s := by
  simp

/-- Restriction is functorial: `(g ≫ h)^* s = g^* (h^* s)`. -/
lemma map_comp_apply (F : EtalePresheaf B S hS (Type v))
    {U V W : SmallNoetherianSeparatedEtale B S hS} (g : U ⟶ V) (h : V ⟶ W) (s : F.obj (op W)) :
    F.map (g ≫ h).op s = F.map g.op (F.map h.op s) := by
  simp

/-- A morphism of presheaves of sets commutes with restriction: `φ (h^* s) = h^* (φ s)`. -/
lemma naturality_apply {F G : EtalePresheaf B S hS (Type v)} (φ : F ⟶ G)
    {U V : SmallNoetherianSeparatedEtale B S hS} (h : U ⟶ V) (s : F.obj (op V)) :
    φ.app (op U) (F.map h.op s) = G.map h.op (φ.app (op V) s) :=
  NatTrans.naturality_apply φ h.op s

end EtalePresheaf

end AlgebraicGeometry

end
