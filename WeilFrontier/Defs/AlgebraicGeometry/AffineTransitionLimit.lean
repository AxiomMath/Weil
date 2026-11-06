module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic

/-!
# Projective systems of schemes with limit

A *projective system of schemes with limit* consists of a cofiltered diagram `D : I ⥤ Scheme`
of noetherian separated schemes with affine transition morphisms, together with a cone
`c : Cone D` whose apex `X = c.pt` is a noetherian separated scheme and whose projections
`pᵢ : X ⟶ Dᵢ` are affine, such that for every index `i` and every affine open `U ⊆ Dᵢ` the
natural map
`colim_{j → i} Γ(Dⱼ, D(j → i)⁻¹ U) ⟶ Γ(X, pᵢ⁻¹ U)`
is an isomorphism. One writes `X = lim Dᵢ`.

The Γ-condition is phrased with Mathlib's restricted diagram `AlgebraicGeometry.opensDiagram`
(the diagram `{ D(j → i)⁻¹ U }` indexed by `Over i`) and its cone
`AlgebraicGeometry.opensCone`: it says that `Γ` sends `(opensCone D c i U).op` to a colimit
cocone.

## Main definitions

- `AlgebraicGeometry.IsProjectiveSystemWithLimit D c`: the cone `c` over `D` exhibits a
  projective system of schemes with limit.

## Main results

- `AlgebraicGeometry.IsProjectiveSystemWithLimit.of_isLimit`: a limit cone of a cofiltered
  diagram of noetherian separated schemes with affine transition maps, whose apex is noetherian
  and separated, is a projective system of schemes with limit.
- `AlgebraicGeometry.isColimit_Γ_opensCone_of_isLimit`: for a limit cone of a cofiltered
  diagram with affine transition maps, the sections over the preimage of an affine open are the
  colimit of the sections over the preimages at the finite levels.
- `AlgebraicGeometry.IsProjectiveSystemWithLimit.nonempty_isLimit`: conversely, the cone of a
  projective system of schemes with limit is a limit cone.
- `AlgebraicGeometry.isProjectiveSystemWithLimit_iff`: a projective system of schemes with limit
  is exactly a limit cone of a cofiltered diagram of noetherian separated schemes with affine
  transition maps, with noetherian separated apex.

## Implementation notes

The index category is an arbitrary (small) cofiltered category instead of a nonempty directed
set; a directed set `(I, ≤)` is the case of the opposite of the poset category, the morphisms
`α ⟶ β` being the relations `α ≥ β`. The identities `p_{αα} = id`, `p_{βγ} ∘ p_{αβ} = p_{αγ}`
and `p_{αβ} ∘ p_α = p_β` are the functoriality of `D` and the naturality of the cone `c`.

The bijectivity of `colim_{j → i} Γ(Dⱼ, D(j → i)⁻¹ U) ⟶ Γ(X, pᵢ⁻¹ U)` is stated as the
cocone of rings being a colimit cocone; since the forgetful functor from commutative rings to
types preserves and reflects filtered colimits, this is the same condition.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
* [Stacks] Stacks Project, Tag 01YT.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The cone `c` over the diagram `D : I ⥤ Scheme` is a *projective system of schemes with
limit*: `I` is cofiltered, all `Dᵢ` and the apex `c.pt` are noetherian and separated, the
transition morphisms and the projections are affine, and for every index `i` and every affine
open `U ⊆ Dᵢ` the sections `Γ(c.pt, pᵢ⁻¹ U)` are the colimit of the sections
`Γ(Dⱼ, D(j → i)⁻¹ U)`, `j → i`, along the maps induced by the projections. -/
@[weil "def_fk104_projective_system_of_schemes"]
structure IsProjectiveSystemWithLimit : Prop where
  /-- The index category is cofiltered (in particular nonempty). -/
  isCofiltered : IsCofiltered I
  /-- Every stage is noetherian. -/
  isNoetherian_obj (i : I) : IsNoetherian (D.obj i)
  /-- Every stage is separated. -/
  isSeparated_obj (i : I) : (D.obj i).IsSeparated
  /-- The transition morphisms are affine. -/
  isAffineHom_map {i j : I} (f : i ⟶ j) : IsAffineHom (D.map f)
  /-- The limit is noetherian. -/
  isNoetherian_pt : IsNoetherian c.pt
  /-- The limit is separated. -/
  isSeparated_pt : c.pt.IsSeparated
  /-- The projections are affine. -/
  isAffineHom_π (i : I) : IsAffineHom (c.π.app i)
  /-- Sections over the preimage of an affine open are the colimit of the sections at the
  finite levels. -/
  isColimit_Γ (i : I) (U : (D.obj i).Opens) (hU : IsAffineOpen U) :
    Nonempty (IsColimit (Scheme.Γ.mapCocone (opensCone D c i U).op))

section

variable {D c}

set_option backward.isDefEq.respectTransparency false in
/-- For a limit cone of a cofiltered diagram of schemes with affine transition maps, the
sections over the preimage `pᵢ⁻¹ U` of an affine open `U ⊆ Dᵢ` are the colimit of the
sections over the preimages `D(j → i)⁻¹ U`. -/
theorem isColimit_Γ_opensCone_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (hc : IsLimit c) (i : I)
    (U : (D.obj i).Opens) (hU : IsAffineOpen U) :
    Nonempty (IsColimit (Scheme.Γ.mapCocone (opensCone D c i U).op)) := by
  have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage _
  exact nonempty_isColimit_Γ_mapCocone (opensDiagram D i U) (opensCone D c i U)
    (isLimitOpensCone D c hc i U)

/-- A limit cone of a cofiltered diagram of noetherian separated schemes with affine transition
maps, whose apex is noetherian and separated, is a projective system of schemes with limit. -/
theorem IsProjectiveSystemWithLimit.of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsNoetherian (D.obj i)]
    [∀ i, (D.obj i).IsSeparated] [IsNoetherian c.pt] [c.pt.IsSeparated] (hc : IsLimit c) :
    IsProjectiveSystemWithLimit D c where
  isCofiltered := inferInstance
  isNoetherian_obj := inferInstance
  isSeparated_obj := inferInstance
  isAffineHom_map := inferInstance
  isNoetherian_pt := inferInstance
  isSeparated_pt := inferInstance
  isAffineHom_π := isAffineHom_π_app D c hc
  isColimit_Γ := isColimit_Γ_opensCone_of_isLimit hc

set_option backward.isDefEq.respectTransparency false in
/-- The cone of a projective system of schemes with limit is a limit cone: `X = lim Dᵢ`. -/
theorem IsProjectiveSystemWithLimit.nonempty_isLimit (h : IsProjectiveSystemWithLimit D c) :
    Nonempty (IsLimit c) := by
  have := h.isCofiltered
  have : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f) := fun f ↦ h.isAffineHom_map f
  have := h.isAffineHom_π
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨⟨L, hL⟩⟩ := HasLimit.exists_limit (F := D)
  let φ : c.pt ⟶ L.pt := hL.lift c
  have hφ (j : I) : φ ≫ L.π.app j = c.π.app j := hL.fac c j
  have := isAffineHom_π_app D L hL
  suffices IsIso φ from ⟨IsLimit.ofPointIso hL⟩
  let W : (D.obj i₀).affineOpens → L.pt.Opens := fun W ↦ L.π.app i₀ ⁻¹ᵁ W.1
  have hW : iSup W = ⊤ := by
    simp only [W]
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := .isomorphisms _) W hW fun U ↦ ?_
  have hle : c.π.app i₀ ⁻¹ᵁ U.1 ≤ φ ⁻¹ᵁ (L.π.app i₀ ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, hφ]
  let ψ := φ.resLE (L.π.app i₀ ⁻¹ᵁ U.1) (c.π.app i₀ ⁻¹ᵁ U.1) hle
  have hψ : IsIso ψ := by
    have : IsAffine (L.π.app i₀ ⁻¹ᵁ U.1).toScheme := U.2.preimage _
    have : IsAffine (c.π.app i₀ ⁻¹ᵁ U.1).toScheme := U.2.preimage _
    refine ((HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).mpr
      ⟨inferInstance, ?_⟩)
    obtain ⟨hA⟩ := h.isColimit_Γ i₀ U.1 U.2
    obtain ⟨hB⟩ := isColimit_Γ_opensCone_of_isLimit hL i₀ U.1 U.2
    let m : Scheme.Γ.mapCocone (opensCone D L i₀ U.1).op ⟶
        Scheme.Γ.mapCocone (opensCone D c i₀ U.1).op :=
      { hom := Scheme.Γ.map ψ.op
        w := fun j ↦ by
          change Scheme.Γ.map ((opensCone D L i₀ U.1).π.app j.unop).op ≫ Scheme.Γ.map ψ.op =
            Scheme.Γ.map ((opensCone D c i₀ U.1).π.app j.unop).op
          rw [← Functor.map_comp, ← op_comp]
          congr 2
          simp only [opensCone_π_app, ψ, Scheme.Hom.resLE_comp_resLE]
          congr 1
          exact hφ j.unop.left }
    have := IsColimit.hom_isIso hB hA m
    exact (Cocone.forget _).map_isIso m
  have := (Scheme.Hom.resLE_congr (f := φ) (e := hle) (e₁ := rfl) (e₂ := (le_antisymm hle (by
      rw [← Scheme.Hom.comp_preimage, hφ]))) (P := MorphismProperty.isomorphisms _)).mp hψ
  rwa [Scheme.Hom.resLE_eq_morphismRestrict] at this

variable (D c) in
/-- A projective system of schemes with limit is exactly a limit cone of a cofiltered diagram of
noetherian separated schemes with affine transition maps whose apex is noetherian and
separated. -/
theorem isProjectiveSystemWithLimit_iff :
    IsProjectiveSystemWithLimit D c ↔
      IsCofiltered I ∧ (∀ i, IsNoetherian (D.obj i)) ∧ (∀ i, (D.obj i).IsSeparated) ∧
        (∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)) ∧ IsNoetherian c.pt ∧
          c.pt.IsSeparated ∧ Nonempty (IsLimit c) := by
  refine ⟨fun h ↦ ⟨h.isCofiltered, h.isNoetherian_obj, h.isSeparated_obj, h.isAffineHom_map,
    h.isNoetherian_pt, h.isSeparated_pt, h.nonempty_isLimit⟩, ?_⟩
  rintro ⟨_, _, _, _, _, _, ⟨hc⟩⟩
  exact .of_isLimit hc

end

end AlgebraicGeometry
