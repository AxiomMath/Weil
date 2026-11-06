module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.Sites
public import Weil.Attr

/-!
# Germs of sections at geometric points

Let `F` be a presheaf on the small étale site of a scheme `X`, let `π : U ⟶ X` be an object of
that site, `α ∈ F(U)` and `ū` a geometric point of `U`. Then `(U, ū)` is an étale neighbourhood
of the geometric point `π ∘ ū` of `X`, and the germ `α_ū ∈ F_{π ∘ ū}` is the image of `α` under
the canonical map from the term `F(U)` indexed by `(U, ū)` to the colimit `F_{π ∘ ū}` over all
étale neighbourhoods of `π ∘ ū`.

The germ is `AlgebraicGeometry.SmallEtale.germ`; this file identifies it with the colimit
insertion of the stalk, and shows that for a locally noetherian `X` the stalk is equally the
colimit over the étale neighbourhoods `(V, v̄)` with `V` noetherian and separated, i.e. over the
neighbourhoods in the category `Et(X)` of the source: these neighbourhoods are cofinal, since
every étale neighbourhood is refined by an affine one.

## Main results

* `AlgebraicGeometry.SmallEtale.germ_eq_toPresheafFiber`: the germ `α_ū` is the colimit
  insertion `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber` at the étale
  neighbourhood `(U, ū)` of `π ∘ ū`.
* `AlgebraicGeometry.SmallEtale.germ_eq_colimit_ι`: the same, as the leg `colimit.ι` of the
  colimit `AlgebraicGeometry.etaleStalk` over the étale neighbourhoods.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.exists_neighborhood_refinement`: every étale
  neighbourhood of a geometric point of a locally noetherian scheme is refined by one whose
  scheme is noetherian and separated.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.initial_neighborhoodPrecomp`: these
  neighbourhoods form an initial subcategory of the étale neighbourhoods.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isColimitPresheafFiberCocone`: the stalk,
  with the colimit insertions, is the colimit of `F` over the étale neighbourhoods in `Et(X)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.exists_toPresheafFiber_eq` and
  `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toPresheafFiber_eq_iff`: for a presheaf of
  sets, every element of the stalk is the germ of a section over a neighbourhood in `Et(X)`, and
  two germs agree if and only if the sections agree on a smaller neighbourhood in `Et(X)`.

## Implementation notes

The small étale site is `AlgebraicGeometry.SmallEtale B X hX` inside a big étale site `B`, and
geometric points are spectra of algebraically closed fields. The source works with the category
`Et(X)` of noetherian separated étale `X`-schemes and geometric points over separably closed
fields; the stalk is formed here on the whole small étale site, and the cofinality results above
identify it with the colimit over `Et(X)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe w v' v u

namespace AlgebraicGeometry

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The germ `α_ū` of a section `α ∈ F(U)` at a geometric point `ū` of `U` is the canonical map
`F(U) ⟶ F_{π ∘ ū}` of the point of the site attached to `π ∘ ū`, at the étale neighbourhood
`(U, ū)`. -/
theorem germ_eq_toPresheafFiber (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}]
    {U : SmallEtale B X hX} (α : F.obj (op U))
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) :
    germ F α ū = (geometricPointSitePoint B X hX (toBaseGeometricPoint U ū)).toPresheafFiber U
      (geometricPointLift U ū) F α :=
  rfl

/-- The germ `α_ū` is the image of `α` under the leg indexed by the étale neighbourhood
`(U, ū)` of the colimit `F_{π ∘ ū}` over all étale neighbourhoods of `π ∘ ū`. -/
@[weil "def_fk103_germ_of_section"]
theorem germ_eq_colimit_ι (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}]
    {U : SmallEtale B X hX} (α : F.obj (op U))
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U)) :
    germ F α ū = colimit.ι
      ((CategoryOfElements.π (geometricPointFiber B X hX (toBaseGeometricPoint U ū))).op ⋙ F)
      (op ⟨U, geometricPointLift U ū⟩) α :=
  rfl

end SmallEtale

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} (x : GeometricPoint X)

variable (B X hX) in
/-- The étale neighbourhoods `(V, v̄)` of a geometric point `x̄` with `V` in `Et(X)`, as étale
neighbourhoods of `x̄` in the small étale site. -/
abbrev neighborhoodPrecomp :
    (inclusion B X hX ⋙ geometricPointFiber B X hX x).Elements ⥤
      (geometricPointFiber B X hX x).Elements :=
  Functor.Elements.precomp (inclusion B X hX) (geometricPointFiber B X hX x)

instance : (neighborhoodPrecomp B X hX x).Faithful where
  map_injective {a b} f g h := by
    apply Subtype.ext
    exact (inclusion B X hX).map_injective (congrArg Subtype.val h)

instance : (neighborhoodPrecomp B X hX x).Full where
  map_surjective {_ _} f := ⟨⟨ObjectProperty.homMk f.1, f.2⟩, rfl⟩

variable [IsLocallyNoetherian X]

/-- **Cofinality of `Et(X)`.** Every étale neighbourhood of a geometric point of a locally
noetherian scheme is refined by an étale neighbourhood whose scheme is noetherian and separated
(indeed affine). -/
theorem exists_neighborhood_refinement (a : (geometricPointFiber B X hX x).Elements) :
    ∃ b : (inclusion B X hX ⋙ geometricPointFiber B X hX x).Elements,
      Nonempty ((neighborhoodPrecomp B X hX x).obj b ⟶ a) := by
  obtain ⟨b, hb, ⟨f⟩⟩ := exists_isAffine_refinement_geometricPointFiber B X hX x a
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj X hX)) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian ((SmallEtale.toScheme B X hX).obj b.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map b.1.obj.hom)
  have : IsNoetherian ((SmallEtale.toScheme B X hX).obj b.1) := {}
  exact ⟨⟨⟨b.1, this, inferInstance⟩, b.2⟩, ⟨f⟩⟩

/-- The étale neighbourhoods with scheme in `Et(X)` form an initial subcategory of the étale
neighbourhoods of a geometric point of a locally noetherian scheme. -/
instance initial_neighborhoodPrecomp : (neighborhoodPrecomp B X hX x).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (exists_neighborhood_refinement x)

/-- **The stalk as a colimit over `Et(X)`.** For a presheaf `F` on the small étale site of a
locally noetherian scheme, the stalk `F_x̄` together with the germ maps
`F(V) ⟶ F_x̄` is the colimit of `F` over the étale neighbourhoods `(V, v̄)` of `x̄` with `V`
noetherian and separated. -/
@[weil "def_fk103_germ_of_section"]
def isColimitPresheafFiberCocone {A : Type v'} [Category.{w} A] [HasColimitsOfSize.{u, u} A]
    (F : (SmallEtale B X hX)ᵒᵖ ⥤ A) :
    IsColimit (((geometricPointSitePoint B X hX x).presheafFiberCocone F).whisker
      (neighborhoodPrecomp B X hX x).op) :=
  (Functor.Final.isColimitWhiskerEquiv (neighborhoodPrecomp B X hX x).op _).symm
    ((geometricPointSitePoint B X hX x).isColimitPresheafFiberCocone F)

/-- For a presheaf of sets on the small étale site of a locally noetherian scheme, every element
of the stalk at a geometric point `x̄` is the germ of a section over an étale neighbourhood of
`x̄` in `Et(X)`. -/
theorem exists_toPresheafFiber_eq (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}]
    (p : (geometricPointSitePoint B X hX x).presheafFiber.obj F) :
    ∃ (V : SmallNoetherianSeparatedEtale B X hX)
      (v : (geometricPointSitePoint B X hX x).fiber.obj ((inclusion B X hX).obj V))
      (z : F.obj (op ((inclusion B X hX).obj V))),
      (geometricPointSitePoint B X hX x).toPresheafFiber _ v F z = p := by
  obtain ⟨U, u, z, rfl⟩ :=
    (geometricPointSitePoint B X hX x).toPresheafFiber_jointly_surjective (P := F) p
  obtain ⟨b, ⟨f⟩⟩ := exists_neighborhood_refinement x ⟨U, u⟩
  refine ⟨b.1, b.2, F.map f.1.op z, ?_⟩
  have h := GrothendieckTopology.Point.toPresheafFiber_w_apply
    (geometricPointSitePoint B X hX x) f.1 b.2 F z
  refine h.trans ?_
  exact congrArg (fun y ↦ (geometricPointSitePoint B X hX x).toPresheafFiber U y F z) f.2

/-- For a presheaf of sets on the small étale site of a locally noetherian scheme, the germs at
`(U, u)` of two sections over `U` agree if and only if the sections agree after restriction to
some étale neighbourhood of `x̄` in `Et(X)` refining `(U, u)`. -/
theorem toPresheafFiber_eq_iff (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}]
    {U : SmallEtale B X hX} (u : (geometricPointSitePoint B X hX x).fiber.obj U)
    (α β : F.obj (op U)) :
    (geometricPointSitePoint B X hX x).toPresheafFiber U u F α =
        (geometricPointSitePoint B X hX x).toPresheafFiber U u F β ↔
      ∃ (V : SmallNoetherianSeparatedEtale B X hX) (g : (inclusion B X hX).obj V ⟶ U)
        (v : (geometricPointSitePoint B X hX x).fiber.obj ((inclusion B X hX).obj V)),
        (geometricPointSitePoint B X hX x).fiber.map g v = u ∧ F.map g.op α = F.map g.op β := by
  refine ((geometricPointSitePoint B X hX x).toPresheafFiber_eq_iff' (P := F) U u α β).trans ?_
  constructor
  · rintro ⟨Y, f, y, hy, h⟩
    obtain ⟨⟨W, w₀⟩, ⟨⟨e₀, he⟩⟩⟩ := exists_neighborhood_refinement x ⟨Y, y⟩
    obtain ⟨e, rfl⟩ : ∃ e : (inclusion B X hX).obj W ⟶ Y, e = e₀ := ⟨_, rfl⟩
    obtain ⟨w, rfl⟩ : ∃ w : (geometricPointSitePoint B X hX x).fiber.obj ((inclusion B X hX).obj W),
      w = w₀ := ⟨_, rfl⟩
    have he' : (geometricPointSitePoint B X hX x).fiber.map e w = y := he
    refine ⟨W, e ≫ f, w, ?_, ?_⟩
    · rw [Functor.map_comp_apply, he', hy]
    · rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h]
  · rintro ⟨V, g, v, hv, h⟩
    exact ⟨_, g, v, hv, h⟩

end SmallNoetherianSeparatedEtale

end AlgebraicGeometry

end
