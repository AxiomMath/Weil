module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import WeilFrontier.AlgebraicGeometry.Sites.EtalePoint

/-!
# The stalk of a constant sheaf at a geometric point

Let `V` be a scheme, `M` a set and `M_V` the presheaf on the small étale site `V.Etale` sending
an étale `V`-scheme `U` to the set of locally constant maps `|U| → M`. Let
`v : Spec Ω ⟶ V` be a point of `V` with values in a separably closed field `Ω`. Then the map
`M → (M_V)_v` sending `m` to the germ, at the étale neighbourhood `(V, v)`, of the constant map
with value `m` is bijective.

It is surjective because a section `s ∈ M_V(W)` over an étale neighbourhood `(W, w)` is constant
on the open subscheme of `W` where it takes the value `s(w)`, which is again an étale
neighbourhood of `v`, and the germ of a constant map does not depend on the neighbourhood. It is
injective because two constants with the same germ agree on some étale neighbourhood, which is
nonempty since it receives a point of `Spec Ω`.

## Main definitions

* `AlgebraicGeometry.Scheme.smallEtaleLocallyConstantMapsType`: the presheaf of sets `M_V` of
  locally constant `M`-valued maps on `V.Etale`.
* `AlgebraicGeometry.Scheme.constGerm`: the map `M → (M_V)_v`, `m ↦` germ of the constant `m`
  at `(V, v)`.
* `AlgebraicGeometry.Scheme.constGermEquiv`: the resulting bijection.

## Main results

* `AlgebraicGeometry.Scheme.toPresheafFiber_constSection`: the germ of a constant map at any étale
  neighbourhood of `v` is the germ of the same constant at `(V, v)`.
* `AlgebraicGeometry.Scheme.constGerm_bijective`: the map `M → (M_V)_v` is bijective.

## Implementation notes

Stalks are Mathlib's `CategoryTheory.GrothendieckTopology.Point.presheafFiber` at the point
`AlgebraicGeometry.Scheme.pointSmallEtale v` of the small étale site, which is defined for any
separably closed field `Ω`; a geometric point (with algebraically closed field) is the special
case `v = s.hom`. The result is proved directly from the description of the stalk as a filtered
colimit and needs no sheaf property of `M_V`; it applies verbatim to the sheafification of the
constant presheaf, which is `M_V`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
-/

/- Stated on
Mathlib's `V.Etale` with the point `pointSmallEtale v` for any separably closed `Ω` (FK: a
geometric point; stronger). Surjectivity uses the open fibre of the section instead of FK's
connected component (connected components need not be open on an arbitrary scheme). -/

@[expose] public noncomputable section

open CategoryTheory GrothendieckTopology Opposite

universe w u

namespace AlgebraicGeometry.Scheme

variable (V : Scheme.{u}) (M : Type w)

/-- The presheaf of sets `M_V` on the small étale site of `V`: an étale `V`-scheme `U` goes to
the set of locally constant maps `|U| → M`, with restriction by composition. -/
abbrev smallEtaleLocallyConstantMapsType : V.Etaleᵒᵖ ⥤ Type (max u w) :=
  (Etale.forget V ⋙ Over.forget V).op ⋙ locallyConstantMapsType.{w, u} M

variable {V} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (v : Spec (.of Ω) ⟶ V)

/-- The point `v` as an element of the fibre over `V` itself: `(V, v)` is an étale
neighbourhood of `v`. -/
def pointSmallEtaleFiberSelf : (pointSmallEtale v).fiber.obj (Etale.mk (𝟙 V)) :=
  Over.homMk v (by simp)

/-- The constant section with value `m` of `M_V` over an étale `V`-scheme `U`. -/
def constSection (U : V.Etale) (m : M) :
    ToType ((smallEtaleLocallyConstantMapsType V M).obj (op U)) :=
  LocallyConstant.const _ m

lemma constSection_apply (U : V.Etale) (m : M) (x : U.left) :
    (show LocallyConstant U.left M from constSection M U m) x = m :=
  rfl

/-- Constant sections restrict to constant sections. -/
@[simp]
lemma map_constSection {U U' : V.Etale} (f : U' ⟶ U) (m : M) :
    (smallEtaleLocallyConstantMapsType V M).map f.op (constSection M U m) =
      constSection M U' m :=
  rfl

/-- The map `M → (M_V)_v` sending `m` to the germ of the constant map with value `m` at the
étale neighbourhood `(V, v)`. -/
def constGerm (m : M) :
    ToType ((pointSmallEtale v).presheafFiber.obj (smallEtaleLocallyConstantMapsType V M)) :=
  (pointSmallEtale v).toPresheafFiber (Etale.mk (𝟙 V)) (pointSmallEtaleFiberSelf v)
    (smallEtaleLocallyConstantMapsType V M) (constSection M _ m)

/-- The germ of a constant map at any étale neighbourhood of `v` is the germ of the same
constant at `(V, v)`. -/
theorem toPresheafFiber_constSection (U : V.Etale) (u : (pointSmallEtale v).fiber.obj U)
    (m : M) :
    (pointSmallEtale v).toPresheafFiber U u (smallEtaleLocallyConstantMapsType V M)
      (constSection M U m) = constGerm M v m := by
  let f : U ⟶ Etale.mk (𝟙 V) := MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial
  have h : (pointSmallEtale v).fiber.map f u = pointSmallEtaleFiberSelf v := by
    apply Over.OverMorphism.ext
    change u.left ≫ U.hom = v
    simpa using Over.w u
  rw [constGerm, ← h, ← Point.toPresheafFiber_w_apply, map_constSection]

/-- **The stalk of a constant sheaf.** The map `M → (M_V)_v` sending `m` to the germ of the
constant map `m` at `(V, v)` is bijective. -/
@[weil "lem_fk104_constant_sheaf_stalk"]
theorem constGerm_bijective : Function.Bijective (constGerm M v) := by
  constructor
  · intro m m' h
    rw [constGerm, constGerm, Point.toPresheafFiber_eq_iff'] at h
    obtain ⟨Y, f, y, -, hf⟩ := h
    rw [map_constSection, map_constSection] at hf
    have hf' : (show LocallyConstant Y.left M from constSection M Y m) =
        (show LocallyConstant Y.left M from constSection M Y m') := hf
    exact DFunLike.congr_fun hf' (y.left.base (default : Spec (.of Ω)))
  · intro p
    obtain ⟨X, x, z, rfl⟩ := (pointSmallEtale v).toPresheafFiber_jointly_surjective p
    let z' : LocallyConstant X.left M := z
    let x₀ : Spec (.of Ω) ⟶ X.left := (show Over.mk v ⟶ (Etale.forget V).obj X from x).left
    have hx₀ : x₀ ≫ X.hom = v := Over.w (show Over.mk v ⟶ (Etale.forget V).obj X from x)
    let m : M := z' (x₀.base (default : Spec (.of Ω)))
    obtain ⟨W, hWm⟩ : ∃ W : X.left.Opens, ∀ y, y ∈ W ↔ z' y = m :=
      ⟨⟨z' ⁻¹' {m}, z'.isLocallyConstant _⟩, fun _ => Iff.rfl⟩
    have hW : Set.range x₀.base ⊆ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨a, rfl⟩
      rw [Subsingleton.elim a default]
      exact (hWm _).2 rfl
    let l : Spec (.of Ω) ⟶ W.toScheme := IsOpenImmersion.lift W.ι x₀ hW
    have hl : l ≫ W.ι = x₀ := IsOpenImmersion.lift_fac W.ι x₀ hW
    let x'₀ : Over.mk v ⟶ (Etale.forget V).obj (Etale.ofOpens X W) :=
      Over.homMk l (by
        change l ≫ W.ι ≫ X.hom = v
        rw [← Category.assoc, hl]
        exact hx₀)
    let x' : (pointSmallEtale v).fiber.obj (Etale.ofOpens X W) := x'₀
    have hx : (pointSmallEtale v).fiber.map (Etale.ofOpensι X W) x' = x := by
      apply Over.OverMorphism.ext
      exact hl
    have hz : (smallEtaleLocallyConstantMapsType V M).map (Etale.ofOpensι X W).op z =
        constSection M (Etale.ofOpens X W) m := by
      apply LocallyConstant.ext
      intro w
      exact (hWm _).1 w.2
    refine ⟨m, ?_⟩
    rw [← hx, ← Point.toPresheafFiber_w_apply, hz, toPresheafFiber_constSection]

/-- The bijection `M ≃ (M_V)_v` of `AlgebraicGeometry.Scheme.constGerm_bijective`. -/
def constGermEquiv :
    M ≃ ToType ((pointSmallEtale v).presheafFiber.obj (smallEtaleLocallyConstantMapsType V M)) :=
  Equiv.ofBijective _ (constGerm_bijective M v)

@[simp]
lemma constGermEquiv_apply (m : M) : constGermEquiv M v m = constGerm M v m :=
  rfl

end AlgebraicGeometry.Scheme

end
