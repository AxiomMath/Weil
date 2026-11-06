module

public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Weil.Attr

/-!
# Sections avoiding a set of global sections on every connected component

Let `B` be a big étale site containing a scheme `X`, let `F` be a presheaf of sets on the small
étale site of `X` and let `E ⊆ F(X)` be a set of global sections. For an object `U` of the site,
`F°_E(U) ⊆ F(U)` is the set of sections `σ` such that `σ|_{U_c} ≠ e|_{U_c}` for every connected
component `U_c` of `U` that is open in `U` and every `e ∈ E`. When `U` is connected this is
`F(U) ∖ E|_U`.

In general `U ↦ F°_E(U)` is not stable under restriction (two sections may differ on `U` and
agree on an open of `U`); it is a subsheaf of `F` when `F` is a sheaf whose difference loci are
open, which is a separate result.

## Main definitions

* `AlgebraicGeometry.SmallEtale.globalRestrict`: the restriction `e|_U ∈ F(U)` of a global
  section `e ∈ F(X)`.
* `AlgebraicGeometry.SmallEtale.sectionsAvoiding`: the set `F°_E(U)`.

## Main results

* `AlgebraicGeometry.SmallEtale.mem_sectionsAvoiding_iff`: membership in `F°_E(U)`.
* `AlgebraicGeometry.SmallEtale.globalRestrict_map`: `(e|_U)|_V = e|_V`.
* `AlgebraicGeometry.SmallEtale.mem_sectionsAvoiding_iff_of_connectedSpace`: for connected `U`,
  `F°_E(U) = F(U) ∖ E|_U`.

## Implementation notes

A connected component of `U` is an object of the small étale site only when it is open in `U`,
which is always the case for the noetherian schemes of the source (they are locally connected).
The condition is imposed on the connected components that are open; the open subscheme is
viewed as an object of the site through `AlgebraicGeometry.SmallEtale.openObject`. The
definition only uses the presheaf structure, so it is stated for presheaves, and `E` is an
arbitrary set of global sections (the source takes a finite one).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The restriction `e|_U ∈ F(U)` of a global section `e ∈ F(X)` of a presheaf on the small
étale site, along the unique morphism from `U` to the final object. -/
def globalRestrict (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) (U : SmallEtale B X hX)
    (e : F.obj (op (SmallEtale.final B X hX))) : F.obj (op U) :=
  F.map ((SmallEtale.finalIsTerminal B X hX).from U).op e

/-- Restricting the restriction of a global section is its restriction: `(e|_U)|_V = e|_V`. -/
@[simp]
theorem globalRestrict_map (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) {U V : SmallEtale B X hX}
    (f : V ⟶ U) (e : F.obj (op (SmallEtale.final B X hX))) :
    F.map f.op (globalRestrict F U e) = globalRestrict F V e := by
  simp only [globalRestrict, ← Functor.map_comp_apply, ← op_comp,
    (SmallEtale.finalIsTerminal B X hX).hom_ext (f ≫ _)
      ((SmallEtale.finalIsTerminal B X hX).from V)]

/-- **The sections avoiding `E` on every connected component.** For a presheaf of sets `F` on
the small étale site of `X`, a set `E ⊆ F(X)` of global sections and an object `U`, the set
`F°_E(U)` of sections `σ ∈ F(U)` with `σ|_{U_c} ≠ e|_{U_c}` for every connected component
`U_c` of `U` that is open in `U` and every `e ∈ E`. -/
@[weil "def_fk103_sheaf_minus_sections"]
def sectionsAvoiding (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    (E : Set (F.obj (op (SmallEtale.final B X hX)))) (U : SmallEtale B X hX) :
    Set (F.obj (op U)) :=
  {σ | ∀ W : ((SmallEtale.toScheme B X hX).obj U).Opens,
    (∃ x, (W : Set ((SmallEtale.toScheme B X hX).obj U)) = connectedComponent x) →
    ∀ e ∈ E, F.map (openObjectι B X hX U W).op σ ≠ globalRestrict F (openObject B X hX U W) e}

theorem mem_sectionsAvoiding_iff (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    (E : Set (F.obj (op (SmallEtale.final B X hX)))) {U : SmallEtale B X hX}
    (σ : F.obj (op U)) :
    σ ∈ sectionsAvoiding F E U ↔ ∀ W : ((SmallEtale.toScheme B X hX).obj U).Opens,
      (∃ x, (W : Set ((SmallEtale.toScheme B X hX).obj U)) = connectedComponent x) →
      ∀ e ∈ E, F.map (openObjectι B X hX U W).op σ ≠
        globalRestrict F (openObject B X hX U W) e :=
  Iff.rfl

/-- The inclusion of the open `⊤` of an object of the small étale site is an isomorphism. -/
instance isIso_openObjectι_top (U : SmallEtale B X hX) :
    IsIso (openObjectι B X hX U ⊤) := by
  have : IsIso ((SmallEtale.toScheme B X hX).map (openObjectι B X hX U ⊤)) := by
    rw [openObjectι_map, ← Scheme.topIso_hom]
    infer_instance
  exact isIso_of_reflects_iso _ (SmallEtale.toScheme B X hX)

/-- For a connected object `U`, a section lies in `F°_E(U)` exactly when it is not the
restriction of an element of `E`: `F°_E(U) = F(U) ∖ E|_U`. -/
theorem mem_sectionsAvoiding_iff_of_connectedSpace (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v)
    (E : Set (F.obj (op (SmallEtale.final B X hX)))) {U : SmallEtale B X hX}
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] (σ : F.obj (op U)) :
    σ ∈ sectionsAvoiding F E U ↔ ∀ e ∈ E, σ ≠ globalRestrict F U e := by
  have hinj : Function.Injective (F.map (openObjectι B X hX U ⊤).op) :=
    ((isIso_iff_bijective _).mp (inferInstance : IsIso (F.map (openObjectι B X hX U ⊤).op))).1
  rw [mem_sectionsAvoiding_iff]
  constructor
  · intro h e he hσ
    obtain ⟨x⟩ := (inferInstance : Nonempty ((SmallEtale.toScheme B X hX).obj U))
    refine h ⊤ ⟨x, ?_⟩ e he ?_
    · exact (PreconnectedSpace.connectedComponent_eq_univ x).symm
    · rw [hσ, globalRestrict_map]
  · rintro h W ⟨x, hW⟩ e he hσ
    obtain rfl : W = ⊤ := by
      ext1
      rw [hW, PreconnectedSpace.connectedComponent_eq_univ]
      rfl
    exact h e he (hinj (by rw [hσ, globalRestrict_map]))

end AlgebraicGeometry.SmallEtale
