module

public import WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonMap
public import WeilFrontier.AlgebraicGeometry.Sites.StalkAtEtaleGeometricPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorialBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalkUnconditional
public import WeilFrontier.AlgebraicGeometry.Sites.Bridges.StalkColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.Compact
public import WeilFrontier.AlgebraicGeometry.ComplexPoints.FiniteMorphismBranchedCover

/-!
# The comparison map on `Spec ℂ` and along direct images: generalities

Let `c^ν(X, F) : H^ν_et(X, F) → H^ν(X(ℂ), F_an)` be the comparison map of a scheme `X` locally of
finite type over `ℂ`. This file proves that it is bijective on `Spec ℂ`, and sets up the stalk
computations used in `WeilFrontier.AlgebraicGeometry.ComplexPoints.ComparisonFinite` for direct
images along finite morphisms: the stalk of a direct image at a point, the stalk of a direct
image along a closed map with finite fibres out of a Hausdorff space, and the reduction of the
bijectivity of `c^ν(X, f_* G)` to that of `c^ν(X', G)` once the base change map
`ε^* f_* ⟶ f_an,* ε'^*` is an isomorphism.

On `Spec ℂ` the analytic space is a point and the étale site has the initial neighbourhood
`Spec ℂ → Spec ℂ`; both stalk functors are equivalences of categories, hence so is the analytic
inverse image `ε^*`, and an equivalence is bijective on `Ext`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.Point.pushforwardFiberMap`: for a functor of sites `F`
  and a map `Φ.fiber ⟶ F ⋙ Ψ.fiber` of fibre functors of points, the map from the stalk at `Φ`
  of a direct image to the stalk at `Ψ`.
* `TopCat.Sheaf.pushforwardFiberComponent`: for a continuous map `φ` and `φ x = y`, the map from
  the stalk at `y` of a direct image to the stalk at `x`.

## Main results

* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonBijectiveOn_spec`: `c^ν(Spec ℂ, F)` is
  bijective for every abelian sheaf `F`.
* `TopCat.Sheaf.bijective_pushforwardFiberComponents`: the stalk of a direct image along a closed
  map with finite fibres out of a Hausdorff space is the product of the stalks along the fibre.
* `AlgebraicGeometry.Scheme.ComplexPoints.comparisonMap_pushforward_bijective_iff_of_isIso`:
  `c^ν(X, f_* G)` is bijective if and only if `c^ν(X', G)` is, when the base change map is an
  isomorphism.

## Implementation notes

The analytic inverse image is a left adjoint known only through its right adjoint `ε_*`, so every
map out of a stalk of `ε^* F` is compared through its transpose into a skyscraper sheaf
(`CategoryTheory.Adjunction.homEquiv_eq_homEquiv_leftAdjointUniq_inv`,
`CategoryTheory.Adjunction.homEquiv_mateEquiv_leftAdjointUniq_inv_app_comp`).

The stalk formula of Stacks 03QP is proved in the library for sheaves of sets on the bounded small
étale site of Stacks 021B; it is transported to Mathlib's small étale site along the initial
functor between the two categories of étale neighbourhoods.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [SGA 4, Exposé XVI, §4]
* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.11]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace CategoryTheory.GrothendieckTopology.Point

universe w v u u' v' u'' v''

section Equivalence

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]

/-- If `(X, x)` is an initial element of the fibre functor of a point `Φ` and the fibre of `X`
is a subsingleton, the counit `(skyscraper M)_Φ ⟶ M` is an isomorphism. -/
theorem isIso_skyscraperSheafAdjunction_counit_app (X : C) (x : Φ.fiber.obj X)
    (h : IsInitial (show Φ.fiber.Elements from ⟨X, x⟩)) [Subsingleton (Φ.fiber.obj X)]
    (M : A) : IsIso (Φ.skyscraperSheafAdjunction.counit.app M) := by
  have hg : IsIso (Φ.toPresheafFiber X x (Φ.skyscraperPresheaf M)) :=
    Φ.isIso_toPresheafFiber_of_isInitial X x h _
  let g : (Φ.skyscraperPresheaf M).obj (op X) ⟶ Φ.sheafFiber.obj (Φ.skyscraperSheaf M) :=
    Φ.toPresheafFiber X x (Φ.skyscraperPresheaf M)
  have hfac : g ≫ Φ.skyscraperSheafAdjunction.counit.app M =
      Pi.π (fun _ : Φ.fiber.obj X => M) x := by
    have e := Φ.skyscraperSheafAdjunction_homEquiv_symm_apply (A := A) (𝟙 (Φ.skyscraperSheaf M))
    have e1 : Φ.skyscraperSheafAdjunction.counit.app M =
        (Φ.skyscraperSheafAdjunction.homEquiv _ M).symm (𝟙 (Φ.skyscraperSheaf M)) := by
      simp [Adjunction.homEquiv_counit]
    erw [e1.trans e]
    exact (toPresheafFiber_skyscraperPresheafHomEquiv_symm Φ _ X x).trans (Category.id_comp _)
  have : Unique (Φ.fiber.obj X) := uniqueOfSubsingleton x
  have hπ : IsIso (Pi.π (fun _ : Φ.fiber.obj X => M) x) :=
    ⟨Pi.lift (fun _ => 𝟙 M), by
      refine Pi.hom_ext _ _ fun j => ?_
      rw [Subsingleton.elim j x]
      simp, by simp⟩
  rw [← hfac] at hπ
  have : IsIso g := hg
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ g _ this hπ

/-- A point `Φ` which alone detects isomorphisms of sheaves, and which has an initial element
`(X, x)` with `Φ.fiber.obj X` a subsingleton, has its stalk functor an equivalence of
categories. -/
theorem isEquivalence_sheafFiber_of_isInitial
    (hcons : ∀ {F G : Sheaf J A} (f : F ⟶ G), IsIso (Φ.sheafFiber.map f) → IsIso f)
    (X : C) (x : Φ.fiber.obj X) (h : IsInitial (show Φ.fiber.Elements from ⟨X, x⟩))
    [Subsingleton (Φ.fiber.obj X)] : (Φ.sheafFiber (A := A)).IsEquivalence := by
  let adj := Φ.skyscraperSheafAdjunction (A := A)
  have hc : ∀ M : A, IsIso (adj.counit.app M) := fun M =>
    Φ.isIso_skyscraperSheafAdjunction_counit_app X x h M
  have hu : ∀ F : Sheaf J A, IsIso (adj.unit.app F) := fun F => by
    apply hcons
    have := adj.left_triangle_components F
    have hc' := hc (Φ.sheafFiber.obj F)
    have h1 : IsIso (Φ.sheafFiber.map (adj.unit.app F) ≫ adj.counit.app (Φ.sheafFiber.obj F)) := by
      rw [this]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (Φ.sheafFiber.obj F))
  exact adj.toEquivalence.isEquivalence_functor

end Equivalence

section Skyscraper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]

@[reassoc (attr := simp)]
theorem skyscraperPresheaf_map_π_of_op (M : A) {U V : Cᵒᵖ} (i : U ⟶ V) (t : Φ.fiber.obj V.unop) :
    (Φ.skyscraperPresheaf M).map i ≫ Pi.π (fun _ : Φ.fiber.obj V.unop => M) t =
      Pi.π (fun _ : Φ.fiber.obj U.unop => M) (Φ.fiber.map i.unop t) := by
  simp only [skyscraperPresheafFunctor_obj_map]
  erw [Pi.map'_comp_π, Category.comp_id]

end Skyscraper

section PushforwardFiber

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (F : C ⥤ D) [F.IsContinuous J K]
  {Φ : Point.{w} J} {Ψ : Point.{w} K} (l : Φ.fiber ⟶ F ⋙ Ψ.fiber)
  {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

/-- Given a functor `F` of sites and a map `l : Φ.fiber ⟶ F ⋙ Ψ.fiber` from the fibre functor
of a point `Φ` of the source to that of a point `Ψ` of the target, the stalk at `Φ` of the
direct image of a sheaf `L` maps to the stalk of `L` at `Ψ`: the germ at `(U, t)` of a section
over `F U` goes to its germ at `(F U, l t)`. -/
noncomputable def pushforwardFiberMap (L : Sheaf K A) :
    Φ.sheafFiber.obj ((F.sheafPushforwardContinuous A J K).obj L) ⟶ Ψ.sheafFiber.obj L :=
  Φ.presheafFiberDesc (fun U t => Ψ.toPresheafFiber (F.obj U) (l.app U t) L.obj)
    (fun U V i t => by
      rw [NatTrans.naturality_apply l i t]
      exact Ψ.toPresheafFiber_w (F.map i) _ L.obj)

@[reassoc (attr := simp)]
theorem toPresheafFiber_pushforwardFiberMap (L : Sheaf K A) (U : C) (t : Φ.fiber.obj U) :
    Φ.toPresheafFiber U t ((F.sheafPushforwardContinuous A J K).obj L).obj ≫
        pushforwardFiberMap F l L = Ψ.toPresheafFiber (F.obj U) (l.app U t) L.obj :=
  Φ.toPresheafFiber_presheafFiberDesc _ _ U t

@[reassoc]
theorem pushforwardFiberMap_naturality {L L' : Sheaf K A} (g : L ⟶ L') :
    Φ.sheafFiber.map ((F.sheafPushforwardContinuous A J K).map g) ≫ pushforwardFiberMap F l L' =
      pushforwardFiberMap F l L ≫ Ψ.sheafFiber.map g := by
  refine Φ.presheafFiber_hom_ext fun U t => ?_
  change Φ.toPresheafFiber U t _ ≫ Φ.presheafFiber.map ((F.sheafPushforwardContinuous A J K).map
    g).hom ≫ _ = _
  erw [toPresheafFiber_naturality_assoc, toPresheafFiber_pushforwardFiberMap]
  erw [← Category.assoc, toPresheafFiber_pushforwardFiberMap]
  exact (Ψ.toPresheafFiber_naturality g.hom _ _).symm

variable [HasProducts.{w} A]

/-- The direct image of the skyscraper sheaf at `Ψ` maps to the skyscraper sheaf at `Φ`. -/
noncomputable def pushforwardSkyscraperMap (M : A) :
    (F.sheafPushforwardContinuous A J K).obj (Ψ.skyscraperSheaf M) ⟶ Φ.skyscraperSheaf M :=
  ObjectProperty.homMk
    { app U := Pi.lift fun t => Pi.π (fun _ : Ψ.fiber.obj (F.obj U.unop) => M) (l.app U.unop t)
      naturality U V i := by
        refine Pi.hom_ext _ _ fun t => ?_
        erw [Category.assoc, Pi.lift_π, Category.assoc, skyscraperPresheaf_map_π_of_op, Pi.lift_π]
        erw [Category.comp_id, Pi.lift_π]
        exact congrArg _ (NatTrans.naturality_apply l i.unop t).symm }

omit [HasColimitsOfSize.{w, w} A] in
@[reassoc (attr := simp)]
theorem pushforwardSkyscraperMap_app_π (M : A) (U : Cᵒᵖ) (t : Φ.fiber.obj U.unop) :
    (pushforwardSkyscraperMap F l M).hom.app U ≫ Pi.π (fun _ : Φ.fiber.obj U.unop => M) t =
      Pi.π (fun _ : Ψ.fiber.obj (F.obj U.unop) => M) (l.app U.unop t) :=
  Pi.lift_π _ _

/-- The transpose along the skyscraper adjunction at `Φ` of `pushforwardFiberMap` followed by
`c` is the direct image of the transpose of `c` along the skyscraper adjunction at `Ψ`, followed
by `pushforwardSkyscraperMap`. -/
theorem skyscraperSheafAdjunction_homEquiv_pushforwardFiberMap_comp (L : Sheaf K A) {M : A}
    (c : Ψ.sheafFiber.obj L ⟶ M) :
    Φ.skyscraperSheafAdjunction.homEquiv _ _ (pushforwardFiberMap F l L ≫ c) =
      (F.sheafPushforwardContinuous A J K).map (Ψ.skyscraperSheafAdjunction.homEquiv _ _ c) ≫
        pushforwardSkyscraperMap F l M := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => Pi.hom_ext _ _ fun t => ?_))
  have e1 := Φ.skyscraperSheafAdjunction_homEquiv_apply_hom (pushforwardFiberMap F l L ≫ c)
  have e2 := Ψ.skyscraperSheafAdjunction_homEquiv_apply_hom c
  erw [e1, skyscraperPresheafHomEquiv_app_π]
  change _ = (((F.sheafPushforwardContinuous A J K).map _).hom.app U ≫
    (pushforwardSkyscraperMap F l M).hom.app U) ≫ _
  erw [Category.assoc, pushforwardSkyscraperMap_app_π]
  change _ = ((Ψ.skyscraperSheafAdjunction.homEquiv _ _ c).hom.app (op (F.obj U.unop))) ≫ _
  erw [e2, skyscraperPresheafHomEquiv_app_π]
  exact (Category.assoc _ _ _).symm.trans
    (toPresheafFiber_pushforwardFiberMap_assoc F l L U.unop t c)

end PushforwardFiber

end CategoryTheory.GrothendieckTopology.Point

namespace TopCat.Sheaf

universe u

variable {X Y : TopCat.{u}} (φ : X ⟶ Y)

/-- The direct image of abelian sheaves along `φ`. -/
abbrev pushforwardAb :
    CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} φ

variable {φ} {x : X} {y : Y} (h : φ x = y)

include h in
theorem mem_map_iff_of_eq (V : Opens Y) : x ∈ (Opens.map φ).obj V ↔ y ∈ V := by
  subst h; rfl

/-- The component at `x` of the stalk at `y = φ x` of a direct image: the germ at `y` of a
section over `φ⁻¹ V` goes to its germ at `x`. -/
noncomputable def pushforwardFiberComponent
    (K : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (_root_.Opens.pointGrothendieckTopology y).sheafFiber.obj ((pushforwardAb φ).obj K) ⟶
      (_root_.Opens.pointGrothendieckTopology x).sheafFiber.obj K :=
  (_root_.Opens.pointGrothendieckTopology y).presheafFiberDesc
    (fun V hV => (_root_.Opens.pointGrothendieckTopology x).toPresheafFiber ((Opens.map φ).obj V)
      ⟨⟨(mem_map_iff_of_eq h V).2 hV.down.down⟩⟩ K.obj)
    (fun _ _ i _ => (_root_.Opens.pointGrothendieckTopology x).toPresheafFiber_w
      ((Opens.map φ).map i) _ K.obj)

@[reassoc (attr := simp)]
theorem toPresheafFiber_pushforwardFiberComponent
    (K : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens Y)
    (hV : y ∈ V) :
    (_root_.Opens.pointGrothendieckTopology y).toPresheafFiber V ⟨⟨hV⟩⟩
        ((pushforwardAb φ).obj K).obj ≫ pushforwardFiberComponent h K =
      (_root_.Opens.pointGrothendieckTopology x).toPresheafFiber ((Opens.map φ).obj V)
        ⟨⟨(mem_map_iff_of_eq h V).2 hV⟩⟩ K.obj :=
  (_root_.Opens.pointGrothendieckTopology y).toPresheafFiber_presheafFiberDesc _ _ V ⟨⟨hV⟩⟩

/-- The direct image of the skyscraper sheaf at `x` maps to the skyscraper sheaf at `y = φ x`:
both have sections `M` over the opens containing the point. -/
noncomputable def pushforwardSkyscraperHom (M : AddCommGrpCat.{u}) :
    (pushforwardAb φ).obj ((_root_.Opens.pointGrothendieckTopology x).skyscraperSheaf M) ⟶
      (_root_.Opens.pointGrothendieckTopology y).skyscraperSheaf M :=
  ObjectProperty.homMk
    { app V := Pi.lift fun hV => Pi.π (fun _ => M)
        (⟨⟨(mem_map_iff_of_eq h V.unop).2 hV.down.down⟩⟩ :
          (_root_.Opens.pointGrothendieckTopology x).fiber.obj ((Opens.map φ).obj V.unop))
      naturality V W i := by
        refine Pi.hom_ext _ _ fun hW => ?_
        erw [Category.assoc, Pi.lift_π, Category.assoc,
          GrothendieckTopology.Point.skyscraperPresheaf_map_π_of_op, Pi.lift_π]
        erw [Category.comp_id, Pi.lift_π]
        rfl }

@[reassoc (attr := simp)]
theorem pushforwardSkyscraperHom_app_π (M : AddCommGrpCat.{u}) (V : (Opens Y)ᵒᵖ)
    (hV : (_root_.Opens.pointGrothendieckTopology y).fiber.obj V.unop) :
    (pushforwardSkyscraperHom h M).hom.app V ≫ Pi.π (fun _ => M) hV =
      Pi.π (fun _ => M) (⟨⟨(mem_map_iff_of_eq h V.unop).2 hV.down.down⟩⟩ :
        (_root_.Opens.pointGrothendieckTopology x).fiber.obj ((Opens.map φ).obj V.unop)) :=
  Pi.lift_π _ _

/-- The transpose of `pushforwardFiberComponent` followed by `c`, along the skyscraper
adjunction at `y`, is the direct image of the transpose of `c` along the skyscraper adjunction at
`x`, followed by `pushforwardSkyscraperHom`. -/
theorem skyscraperSheafAdjunction_homEquiv_pushforwardFiberComponent_comp
    (K : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {M : AddCommGrpCat.{u}}
    (c : (_root_.Opens.pointGrothendieckTopology x).sheafFiber.obj K ⟶ M) :
    (_root_.Opens.pointGrothendieckTopology y).skyscraperSheafAdjunction.homEquiv _ _
        (pushforwardFiberComponent h K ≫ c) =
      (pushforwardAb φ).map
        ((_root_.Opens.pointGrothendieckTopology x).skyscraperSheafAdjunction.homEquiv _ _ c) ≫
        pushforwardSkyscraperHom h M := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => Pi.hom_ext _ _ fun hV => ?_))
  have e1 := GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_apply_hom
    (_root_.Opens.pointGrothendieckTopology y) (pushforwardFiberComponent h K ≫ c)
  have e2 := GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_apply_hom
    (_root_.Opens.pointGrothendieckTopology x) c
  erw [e1, GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_π]
  change _ = ((pushforwardAb φ).map _).hom.app V ≫ (Pi.lift _) ≫ _
  erw [Pi.lift_π]
  change _ = (((_root_.Opens.pointGrothendieckTopology x).skyscraperSheafAdjunction.homEquiv _ _
    c).hom.app (op ((Opens.map φ).obj V.unop))) ≫ _
  erw [e2, GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_π]
  obtain ⟨⟨hV⟩⟩ := hV
  exact toPresheafFiber_pushforwardFiberComponent_assoc h K V.unop hV c

omit h in
theorem subsingleton_sections_of_le_bot
    (K : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (O : Opens X) (hO : O ≤ ⊥) :
    Subsingleton (ToType (K.obj.obj (op O))) :=
  ⟨fun s t => TopCat.Sheaf.eq_of_locally_eq' K (fun i : PEmpty.{1} => i.elim) O (fun i => i.elim)
    (by simpa using hO) s t (fun i => i.elim)⟩

variable (φ y) in
/-- The components of the stalk at `y` of a direct image, indexed by the fibre `φ⁻¹ y`. -/
noncomputable def pushforwardFiberComponents
    (K : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (z : ToType ((_root_.Opens.pointGrothendieckTopology y).sheafFiber.obj
      ((pushforwardAb φ).obj K))) (x : {x : X // φ x = y}) :
    ToType ((_root_.Opens.pointGrothendieckTopology x.1).sheafFiber.obj K) :=
  pushforwardFiberComponent x.2 K z

variable (φ y) in
/-- **The stalk of a direct image along a closed map with finite fibres** in a Hausdorff space
is the product of the stalks along the fibre. -/
theorem bijective_pushforwardFiberComponents [T2Space X] (hφ : IsClosedMap φ)
    (hfin : (φ ⁻¹' {y}).Finite)
    (K : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Function.Bijective (pushforwardFiberComponents φ y K) := by
  let P := _root_.Opens.pointGrothendieckTopology y
  let Q := fun x : X => _root_.Opens.pointGrothendieckTopology x
  have germ : ∀ (x : {x : X // φ x = y}) (V : Opens Y) (hV : y ∈ V)
      (s : ToType (((pushforwardAb φ).obj K).obj.obj (op V))),
      pushforwardFiberComponents φ y K (P.toPresheafFiber V ⟨⟨hV⟩⟩ ((pushforwardAb φ).obj K).obj s)
        x = (Q x.1).toPresheafFiber ((Opens.map φ).obj V)
          ⟨⟨(mem_map_iff_of_eq x.2 V).2 hV⟩⟩ K.obj s := fun x V hV s =>
    ConcreteCategory.congr_hom (toPresheafFiber_pushforwardFiberComponent x.2 K V hV) s
  -- shrinking: an open of `X` containing the fibre contains the preimage of a neighbourhood
  have shrink : ∀ (O : Opens X), (∀ x : X, φ x = y → x ∈ O) → ∀ V : Opens Y, y ∈ V →
      ∃ V' : Opens Y, y ∈ V' ∧ V' ≤ V ∧ (Opens.map φ).obj V' ≤ O := by
    intro O hO V hV
    refine ⟨V ⊓ ⟨(φ '' (O : Set X)ᶜ)ᶜ, (hφ _ O.isOpen.isClosed_compl).isOpen_compl⟩,
      ⟨hV, ?_⟩, inf_le_left, fun z hz => ?_⟩
    · rintro ⟨z, hz, hzy⟩
      exact hz (hO z hzy)
    · by_contra hzO
      exact hz.2 ⟨z, hzO, rfl⟩
  constructor
  · intro z₁ z₂ hz
    obtain ⟨V, ⟨⟨hV⟩⟩, s₁, s₂, rfl, rfl⟩ :=
      P.toPresheafFiber_jointly_surjective₂ (P := ((pushforwardAb φ).obj K).obj) z₁ z₂
    have hx : ∀ x : {x : X // φ x = y}, ∃ (W : Opens X) (hW : W ≤ (Opens.map φ).obj V),
        x.1 ∈ W ∧ K.obj.map (homOfLE hW).op s₁ = K.obj.map (homOfLE hW).op s₂ := by
      intro x
      have hzx := congrFun hz x
      rw [germ, germ] at hzx
      obtain ⟨W, i, ⟨⟨w⟩⟩, -, he⟩ := ((Q x.1).toPresheafFiber_eq_iff' _ _ s₁ s₂).1 hzx
      exact ⟨W, i.le, w, he⟩
    choose W hW hxW hWs using hx
    obtain ⟨V', hyV', hV'V, hV'O⟩ := shrink (⨆ x, W x)
      (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hxW _⟩) V hV
    have key : ((pushforwardAb φ).obj K).obj.map (homOfLE hV'V).op s₁ =
        ((pushforwardAb φ).obj K).obj.map (homOfLE hV'V).op s₂ := by
      refine TopCat.Sheaf.eq_of_locally_eq' K (fun x => W x ⊓ (Opens.map φ).obj V')
        ((Opens.map φ).obj V') (fun x => homOfLE inf_le_right)
        (fun z hz => ?_) _ _ (fun x => ?_)
      · obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hV'O hz)
        exact Opens.mem_iSup.2 ⟨x, hx, hz⟩
      · have e : ∀ s : ToType (((pushforwardAb φ).obj K).obj.obj (op V)),
            K.obj.map (homOfLE (inf_le_right : W x ⊓ (Opens.map φ).obj V' ≤ _)).op
              (((pushforwardAb φ).obj K).obj.map (homOfLE hV'V).op s) =
            K.obj.map (homOfLE (inf_le_left : W x ⊓ (Opens.map φ).obj V' ≤ W x)).op
              (K.obj.map (homOfLE (hW x)).op s) := fun s => by
          change (((pushforwardAb φ).obj K).obj.map _ ≫ K.obj.map _) s =
            (K.obj.map _ ≫ K.obj.map _) s
          erw [← K.obj.map_comp, ← K.obj.map_comp]
          rfl
        rw [e, e]
        exact congrArg _ (hWs x)
    have e₁ := P.toPresheafFiber_w_apply (homOfLE hV'V) ⟨⟨hyV'⟩⟩
      ((pushforwardAb φ).obj K).obj s₁
    have e₂ := P.toPresheafFiber_w_apply (homOfLE hV'V) ⟨⟨hyV'⟩⟩
      ((pushforwardAb φ).obj K).obj s₂
    exact e₁.symm.trans ((congrArg _ key).trans e₂)
  · intro t
    have hrep : ∀ x : {x : X // φ x = y}, ∃ (W : Opens X) (hW : x.1 ∈ W)
        (s : ToType (K.obj.obj (op W))), (Q x.1).toPresheafFiber W ⟨⟨hW⟩⟩ K.obj s = t x := by
      intro x
      obtain ⟨W, ⟨⟨hW⟩⟩, s, hs⟩ := (Q x.1).toPresheafFiber_jointly_surjective (P := K.obj) (t x)
      exact ⟨W, hW, s, hs⟩
    choose W hxW s hs using hrep
    obtain ⟨U, hU, hdisj⟩ := hfin.t2_separation
    let W' : {x : X // φ x = y} → Opens X := fun x => W x ⊓ ⟨U x.1, (hU x.1).2⟩
    have hxW' : ∀ x, x.1 ∈ W' x := fun x => ⟨hxW x, (hU x.1).1⟩
    obtain ⟨V, hyV, -, hVO⟩ := shrink (⨆ x, W' x)
      (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hxW' _⟩) ⊤ (Set.mem_univ y)
    let O : {x : X // φ x = y} → Opens X := fun x => W' x ⊓ (Opens.map φ).obj V
    let sf : ∀ x, ToType (K.obj.obj (op (O x))) := fun x =>
      K.obj.map (homOfLE (inf_le_left.trans inf_le_left : O x ≤ W x)).op (s x)
    have compat : TopCat.Presheaf.IsCompatible K.obj O sf := by
      intro i j
      by_cases hij : i = j
      · subst hij
        rfl
      · have : O i ⊓ O j ≤ ⊥ := by
          intro z ⟨hzi, hzj⟩
          have hne : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
          exact (Set.disjoint_left.1 (hdisj i.2 j.2 hne) hzi.1.2 hzj.1.2).elim
        exact (subsingleton_sections_of_le_bot K _ this).elim _ _
    obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' K O ((Opens.map φ).obj V)
      (fun x => homOfLE inf_le_right) (fun z hz => by
        obtain ⟨x, hx⟩ := Opens.mem_iSup.1 (hVO hz)
        exact Opens.mem_iSup.2 ⟨x, hx, hz⟩) sf compat
    refine ⟨P.toPresheafFiber V ⟨⟨hyV⟩⟩ ((pushforwardAb φ).obj K).obj g, funext fun x => ?_⟩
    refine (germ x V hyV g).trans ?_
    rw [← hs x]
    have hxO : x.1 ∈ O x := ⟨hxW' x, (mem_map_iff_of_eq x.2 V).2 hyV⟩
    have e₁ := (Q x.1).toPresheafFiber_w_apply (homOfLE (inf_le_right : O x ≤ _)) ⟨⟨hxO⟩⟩ K.obj g
    have e₂ := (Q x.1).toPresheafFiber_w_apply
      (homOfLE (inf_le_left.trans inf_le_left : O x ≤ W x)) ⟨⟨hxO⟩⟩ K.obj (s x)
    exact e₁.symm.trans ((congrArg _ (hg x)).trans e₂)

@[reassoc]
theorem pushforwardFiberComponent_naturality
    {K L : CategoryTheory.Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (g : K ⟶ L) :
    (_root_.Opens.pointGrothendieckTopology y).sheafFiber.map ((pushforwardAb φ).map g) ≫
        pushforwardFiberComponent h L =
      pushforwardFiberComponent h K ≫
        (_root_.Opens.pointGrothendieckTopology x).sheafFiber.map g := by
  refine (_root_.Opens.pointGrothendieckTopology y).presheafFiber_hom_ext fun V ⟨⟨hV⟩⟩ => ?_
  change (_root_.Opens.pointGrothendieckTopology y).toPresheafFiber V ⟨⟨hV⟩⟩ _ ≫
      (_root_.Opens.pointGrothendieckTopology y).presheafFiber.map ((pushforwardAb φ).map g).hom ≫
        _ = _
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc,
    toPresheafFiber_pushforwardFiberComponent, toPresheafFiber_pushforwardFiberComponent_assoc]
  exact ((_root_.Opens.pointGrothendieckTopology x).toPresheafFiber_naturality g.hom _ _).symm

omit h in
variable (φ) in
/-- The direct image along a closed map with finite fibres out of a Hausdorff space preserves
epimorphisms of abelian sheaves. -/
theorem preservesEpimorphisms_pushforwardAb [T2Space X] (hφ : IsClosedMap φ)
    (hfin : ∀ y : Y, (φ ⁻¹' {y}).Finite) : (pushforwardAb φ).PreservesEpimorphisms := by
  refine ⟨fun {K L} g hg => ?_⟩
  have surj : ∀ y : Y, Function.Surjective
      ((_root_.Opens.pointGrothendieckTopology y).sheafFiber.map ((pushforwardAb φ).map g)) := by
    intro y w
    have hstalk : ∀ x : {x : X // φ x = y}, Function.Surjective
        ((_root_.Opens.pointGrothendieckTopology x.1).sheafFiber.map g) := fun x => by
      rw [← AddCommGrpCat.epi_iff_surjective]
      infer_instance
    choose v hv using fun x => hstalk x (pushforwardFiberComponents φ y L w x)
    obtain ⟨z, hz⟩ := (bijective_pushforwardFiberComponents φ y hφ (hfin y) K).2 v
    refine ⟨z, (bijective_pushforwardFiberComponents φ y hφ (hfin y) L).1 (funext fun x => ?_)⟩
    rw [← hv x, ← hz]
    exact ConcreteCategory.congr_hom (pushforwardFiberComponent_naturality x.2 g) z
  have hpts := ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectEpimorphisms
    (_root_.Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology Y) AddCommGrpCat.{u}
  have : ∀ Φ : (_root_.Opens.pointsGrothendieckTopology Y).FullSubcategory,
      Epi (Φ.obj.sheafFiber.map ((pushforwardAb φ).map g)) := by
    intro Φ
    obtain ⟨y, hy⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
    rw [← hy]
    exact (AddCommGrpCat.epi_iff_surjective _).2 (surj y)
  exact hpts.epi _

end TopCat.Sheaf

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
  {L₁ : C ⥤ C'} {R₁ : C' ⥤ C} (a : L₁ ⊣ R₁) {L₂ : D ⥤ D'} {R₂ : D' ⥤ D} (b : L₂ ⊣ R₂)
  {G : C ⥤ D} {G' : D ⥤ C} (e : G ⊣ G') {H : C' ⥤ D'} {H' : D' ⥤ C'} (e' : H ⊣ H')
  (δ : H' ⋙ R₁ ≅ R₂ ⋙ G')

/-- Let `γ : L₁ ⋙ H ≅ G ⋙ L₂` be the isomorphism of left adjoints induced by an isomorphism
`δ : H' ⋙ R₁ ≅ R₂ ⋙ G'` of right adjoints. Then the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of `γ⁻¹`, followed
by `R₂ ψ` and transposed along `G ⊣ G'`, is `R₁` of the transpose of `ψ` along `H ⊣ H'`, followed
by `δ`. -/
theorem homEquiv_mateEquiv_leftAdjointUniq_inv_app_comp (Y : C') {K : D'} (ψ : H.obj Y ⟶ K) :
    e.homEquiv _ _ ((mateEquiv a b (leftAdjointUniq (a.comp e')
        ((e.comp b).ofNatIsoRight δ.symm)).inv).app Y ≫ R₂.map ψ) =
      R₁.map (e'.homEquiv _ _ ψ) ≫ δ.hom.app K := by
  set γ := leftAdjointUniq (a.comp e') ((e.comp b).ofNatIsoRight δ.symm)
  have h1 : (mateEquiv a b γ.inv).app Y = b.unit.app (G.obj (R₁.obj Y)) ≫
      R₂.map (γ.inv.app (R₁.obj Y) ≫ H.map (a.counit.app Y)) := by
    simp [mateEquiv]
  have h2 : ∀ (y : C) {z : D'} (χ : H.obj (L₁.obj y) ⟶ z),
      ((e.comp b).ofNatIsoRight δ.symm).homEquiv _ _ (γ.inv.app y ≫ χ) =
        (a.comp e').homEquiv _ _ χ := by
    intro y z χ
    rw [homEquiv_naturality_right, leftAdjointUniq_inv_app, homEquiv_leftAdjointUniq_hom_app,
      ← homEquiv_unit]
  have h3 := h2 (R₁.obj Y) (H.map (a.counit.app Y) ≫ ψ)
  rw [homEquiv_ofNatIsoRight_apply, comp_homEquiv] at h3
  simp only [Equiv.trans_apply] at h3
  have h4 : e.homEquiv _ _ (b.unit.app (G.obj (R₁.obj Y)) ≫
      R₂.map (γ.inv.app (R₁.obj Y) ≫ H.map (a.counit.app Y) ≫ ψ)) =
      (e.comp b).homEquiv _ _ (γ.inv.app (R₁.obj Y) ≫ H.map (a.counit.app Y) ≫ ψ) := by
    rw [comp_homEquiv]
    simp only [Equiv.trans_apply]
    congr 1
  rw [h1, Category.assoc, ← R₂.map_comp, Category.assoc, h4]
  have h5 := congrArg (fun φ => φ ≫ δ.hom.app K) h3
  simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id_app, Category.comp_id] at h5
  rw [comp_homEquiv] at h5 ⊢
  simp only [Equiv.trans_apply] at h5 ⊢
  rw [h5, homEquiv_naturality_left, homEquiv_unit, Functor.map_comp, ← Category.assoc,
    right_triangle_components, Category.id_comp]
  rfl

/-- Transposes along `F ⊣ R` are transposes along `F' ⊣ R'` precomposed with the comparison
`F' ≅ F` of left adjoints induced by an isomorphism `R' ≅ R`. -/
theorem homEquiv_eq_homEquiv_leftAdjointUniq_inv {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {R R' : D ⥤ C} (adj : F ⊣ R) (adj' : F' ⊣ R') (i : R' ≅ R) {X : C} {Y : D}
    (χ : F.obj X ⟶ Y) :
    adj.homEquiv X Y χ = adj'.homEquiv X Y
      ((leftAdjointUniq adj (adj'.ofNatIsoRight i)).inv.app X ≫ χ) ≫ i.hom.app Y := by
  rw [← homEquiv_ofNatIsoRight_apply, homEquiv_naturality_right, leftAdjointUniq_inv_app,
    homEquiv_leftAdjointUniq_hom_app, ← homEquiv_unit]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme.ComplexPoints

/-! ### The point `Spec ℂ` -/

section SpecComplex

/-- The structure morphism of `Spec ℂ` over itself. -/
local notation "𝔭" => 𝟙 (Spec (CommRingCat.of ℂ))

/-- The unique complex point of `Spec ℂ`. -/
def specPoint : ComplexPoints 𝔭 := ⟨𝟙 _, Category.comp_id _⟩

instance : Unique (ComplexPoints 𝔭) where
  default := specPoint
  uniq p := ext ((Category.comp_id p.hom).symm.trans p.hom_comp)

instance : Unique (analyticSpace 𝔭) := inferInstanceAs (Unique (ULift (ComplexPoints 𝔭)))

/-- The open `⊤` of the one-point space `Spec ℂ (ℂ)`, with its point, is an initial
neighbourhood of the point. -/
def isInitialAnPointTop :
    IsInitial (show (anPoint 𝔭 specPoint).fiber.Elements from ⟨⊤, ⟨⟨trivial⟩⟩⟩) := by
  refine IsInitial.ofUniqueHom (fun U => ⟨homOfLE fun z _ => ?_, rfl⟩) (fun U m => ?_)
  · have h : (ULift.up specPoint : analyticSpace 𝔭) ∈ U.1 := U.2.down.down
    rwa [Subsingleton.elim z (ULift.up specPoint)]
  · exact Subtype.ext (Subsingleton.elim _ _)

instance : Subsingleton ((anPoint 𝔭 specPoint).fiber.obj ⊤) :=
  inferInstanceAs (Subsingleton (ULift (PLift _)))

instance : Subsingleton ((etPoint 𝔭 specPoint).fiber.obj (Etale.mk (𝟙 (Spec (.of ℂ))))) := by
  refine ⟨fun a b => ?_⟩
  refine Over.OverMorphism.ext ?_
  have ha : a.left ≫ 𝟙 _ = 𝟙 _ := Over.w a
  have hb : b.left ≫ 𝟙 _ = 𝟙 _ := Over.w b
  simp only [Category.comp_id] at ha hb
  exact ha.trans hb.symm

theorem isEquivalence_sheafFiber_anPoint_specPoint :
    ((anPoint 𝔭 specPoint).sheafFiber (A := AddCommGrpCat.{1})).IsEquivalence := by
  refine (anPoint 𝔭 specPoint).isEquivalence_sheafFiber_of_isInitial (fun {F G} f hf => ?_) ⊤
    ⟨⟨trivial⟩⟩ isInitialAnPointTop
  have : ∀ Φ : (_root_.Opens.pointsGrothendieckTopology (analyticSpace 𝔭)).FullSubcategory,
      IsIso (Φ.obj.sheafFiber.map f) := by
    intro Φ
    obtain ⟨z, hz⟩ := (ObjectProperty.ofObj_iff _ _).1 Φ.property
    rw [← hz, Subsingleton.elim z (ULift.up specPoint)]
    exact hf
  exact ((_root_.Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology
    (analyticSpace 𝔭)).jointlyReflectIsomorphisms AddCommGrpCat.{1}).isIso f

/-- An isomorphism of points of a site induces an isomorphism of their stalk functors. -/
private def sheafFiberIsoOfPointIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A : Type*} [Category A] [HasColimitsOfSize.{0, 0} A]
    {Φ₁ Φ₂ : J.Point.{0}} (e : Φ₁ ≅ Φ₂) :
    Φ₂.sheafFiber (A := A) ≅ Φ₁.sheafFiber where
  hom := e.hom.sheafFiber
  inv := e.inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, e.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

theorem isEquivalence_sheafFiber_etPoint_specPoint :
    ((etPoint 𝔭 specPoint).sheafFiber (A := AddCommGrpCat.{1})).IsEquivalence := by
  refine (etPoint 𝔭 specPoint).isEquivalence_sheafFiber_of_isInitial (fun {F G} f hf => ?_)
    _ _ (isInitialPointSmallEtaleEtaleMk (𝟙 (Spec (.of ℂ))))
  rw [Stacks.EtaleCohomology.isIso_iff_forall_isIso_smallEtaleStalkAb]
  intro t
  let a : GeometricPoint.Hom t ⟨ℂ, 𝟙 (Spec (.of ℂ))⟩ := ⟨t.hom, Category.comp_id _⟩
  have := smallEtalePointHom_isIso (Spec (.of ℂ)) a
  exact (NatIso.isIso_map_iff
    (sheafFiberIsoOfPointIso (asIso (smallEtalePointHom _ a))) f).1 hf

/-- On `Spec ℂ` the analytic inverse image is an equivalence of categories. -/
theorem isEquivalence_analyticInverseImage_spec :
    (analyticInverseImage 𝔭).IsEquivalence := by
  have := isEquivalence_sheafFiber_anPoint_specPoint
  have := isEquivalence_sheafFiber_etPoint_specPoint
  have : (analyticInverseImage 𝔭 ⋙ (anPoint 𝔭 specPoint).sheafFiber).IsEquivalence :=
    Functor.isEquivalence_of_iso (stalkIso 𝔭 specPoint).symm
  exact Functor.isEquivalence_of_comp_right _ ((anPoint 𝔭 specPoint).sheafFiber)

/-- **The comparison map is bijective on `Spec ℂ`**, for every abelian sheaf and in every
degree. -/
theorem comparisonBijectiveOn_spec : ComparisonBijectiveOn 𝔭 ⊤ := by
  intro F _ n
  have := isEquivalence_analyticInverseImage_spec
  rw [comparisonMap, Functor.mapExtOfIso_bijective_iff]
  exact Functor.mapExt_bijective_of_preservesInjectiveObjects _ _ _ _

end SpecComplex

/-! ### Direct images along a morphism over `ℂ` -/

section Pushforward

open Stacks.EtaleCohomology

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType x'] (f : X' ⟶ X) (hf : f ≫ x = x')

/-- The direct image of abelian sheaves along `X'(ℂ) → X(ℂ)`, in the spelling of `AnSheaf`. -/
abbrev analyticPushforward :
    Sheaf (_root_.Opens.grothendieckTopology (TopCat.of (ULift.{1} (ComplexPoints x'))))
        AddCommGrpCat.{1} ⥤
      Sheaf (_root_.Opens.grothendieckTopology (TopCat.of (ULift.{1} (ComplexPoints x))))
        AddCommGrpCat.{1} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{1} (analyticMap x x' f hf)

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
/-- The adjunction `f_an^* ⊣ f_an,*`, in the spelling of `AnSheaf`. -/
abbrev analyticPullbackAdjunction : analyticPullback x x' f hf ⊣ analyticPushforward x x' f hf :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{1} (analyticMap x x' f hf)

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
instance preservesFiniteLimits_analyticPullback :
    PreservesFiniteLimits (analyticPullback x x' f hf) := by
  have : (TopologicalSpace.Opens.map (analyticMap x x' f hf)).IsContinuous
      (Opens.grothendieckTopology (analyticSpace x))
      (Opens.grothendieckTopology (analyticSpace x')) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology _
  have : RepresentablyFlat (TopologicalSpace.Opens.map (analyticMap x x' f hf)) :=
    instRepresentablyFlatOpensCarrierMap _
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    _ _ _ _

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
instance preservesFiniteColimits_analyticPullback :
    PreservesFiniteColimits (analyticPullback x x' f hf) := by
  have := (analyticPullbackAdjunction x x' f hf).leftAdjoint_preservesColimits.{0, 0}
  have h : PreservesFiniteColimits
    (TopCat.Sheaf.pullback AddCommGrpCat.{1} (analyticMap x x' f hf)) := inferInstance
  exact h

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
instance additive_analyticPushforward : (analyticPushforward x x' f hf).Additive where
  map_add := rfl

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
instance additive_analyticPullback : (analyticPullback x x' f hf).Additive :=
  (analyticPullbackAdjunction x x' f hf).left_adjoint_additive

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
instance preservesFiniteLimits_analyticPushforward :
    PreservesFiniteLimits (analyticPushforward x x' f hf) :=
  have := (analyticPullbackAdjunction x x' f hf).rightAdjoint_preservesLimits
  inferInstance

omit [LocallyOfFiniteType x] [LocallyOfFiniteType x'] in
instance preservesFiniteLimits_smallEtalePushforwardAb :
    PreservesFiniteLimits (smallEtalePushforwardAb f) :=
  have := (smallEtaleAdjunctionAb f).rightAdjoint_preservesLimits
  inferInstance

/-- The mate identity for the base change map: the transpose along `ε^* ⊣ ε_*` of
`β ≫ f_an,* ψ` is `f_*` of the transpose of `ψ`, followed by `f_* ε'_* ≅ ε_* f_an,*`. -/
theorem homEquiv_pushforwardBaseChange_app_comp (G : EtSheaf X') {K : AnSheaf x'}
    (ψ : (analyticInverseImage x').obj G ⟶ K) :
    (analyticAdjunction x).homEquiv _ _ ((pushforwardBaseChange x x' f hf).app G ≫
        (analyticPushforward x x' f hf).map ψ) =
      (smallEtalePushforwardAb f).map ((analyticAdjunction x').homEquiv _ _ ψ) ≫
        (directImageBaseChangeIso x x' f hf).hom.app K :=
  Adjunction.homEquiv_mateEquiv_leftAdjointUniq_inv_app_comp _ _ _ _ _ G ψ

/-- The base change map on the unit of `f^* ⊣ f_*`. -/
theorem map_unit_comp_pushforwardBaseChange_app (A : EtSheaf X) :
    (analyticInverseImage x).map ((etaleInverseImageAdjunction f).unit.app A) ≫
        (pushforwardBaseChange x x' f hf).app ((etaleAbelianInverseImage.{0, 0} f).obj A) =
      (analyticPullbackAdjunction x x' f hf).unit.app ((analyticInverseImage x).obj A) ≫
        (analyticPushforward x x' f hf).map ((inverseImageIso x x' f hf).inv.app A) :=
  unit_mateEquiv _ _ _ A

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
/-- **The comparison map along a direct image.** If `f_*` and `f_an,*` are exact and the base
change map `ε^* f_* G ⟶ f_an,* ε'^* G` is an isomorphism, then `c^n(X, f_* G)` is bijective if
and only if `c^n(X', G)` is: both are identified with each other through the adjunction
isomorphisms `Ext^n(f^* ℤ, G) ≅ Ext^n(ℤ, f_* G)` on both sides. -/
theorem comparisonMap_pushforward_bijective_iff_of_isIso
    [PreservesFiniteColimits (smallEtalePushforwardAb f)]
    [PreservesFiniteColimits (analyticPushforward x x' f hf)] (G : EtSheaf X')
    [IsIso ((pushforwardBaseChange x x' f hf).app G)] (n : ℕ) :
    Function.Bijective (comparisonMap x ((smallEtalePushforwardAb f).obj G) n) ↔
      Function.Bijective (comparisonMap x' G n) := by
  let A : EtSheaf X := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let a := etaleInverseImageAdjunction f
  let b := analyticPullbackAdjunction x x' f hf
  let γ := inverseImageIso x x' f hf
  let β : smallEtalePushforwardAb f ⋙ analyticInverseImage x ⟶
      analyticInverseImage x' ⋙ analyticPushforward x x' f hf := pushforwardBaseChange x x' f hf
  have : IsIso (β.app G) := ‹_›
  rw [comparisonMap, Functor.mapExtOfIso_bijective_iff, comparisonMap,
    Functor.mapExtOfIso_bijective_iff,
    Functor.mapExtAddHom_bijective_iff_of_iso (analyticInverseImage x')
      (((etaleAbelianInverseImageConstantIso.{0, 0} f).app (AddCommGrpCat.of (ULift ℤ))).symm)]
  have hΦ₁ := Stacks.ExtFunctorial.extAdjunction_bijective.{1, 1} a A G n
  have hΦ₂ := Stacks.ExtFunctorial.extAdjunction_bijective.{1, 1} b
    ((analyticInverseImage x).obj A) ((analyticInverseImage x').obj G) n
  have hT := Functor.bijective_mk₀_hom_extComp.{1} (C := (analyticInverseImage x').obj G)
    (γ.app A).symm n
  have hB := Functor.bijective_extComp_mk₀_hom.{1} (B := (analyticInverseImage x).obj A)
    (asIso (β.app G)) n
  have hsq : ∀ z : Ext.{1} ((etaleAbelianInverseImage.{0, 0} f).obj A) G n,
      ((analyticInverseImage x).mapExtAddHom A _ n
          ((Ext.mk₀ (a.unit.app A)).comp (z.mapExactFunctor (smallEtalePushforwardAb f))
            (zero_add n))).comp (Ext.mk₀ (asIso (β.app G)).hom) (add_zero n) =
        (Ext.mk₀ (b.unit.app ((analyticInverseImage x).obj A))).comp
          (((Ext.mk₀ (γ.app A).symm.hom).comp
            ((analyticInverseImage x').mapExtAddHom _ G n z) (zero_add n)).mapExactFunctor
              (analyticPushforward x x' f hf)) (zero_add n) := by
    intro z
    simp only [asIso_hom, Iso.symm_hom, Iso.app_inv, Functor.mapExtAddHom_apply,
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Stacks.ExtFunctorial.mapExactFunctor_comp_functor]
    rw [Ext.comp_assoc_of_third_deg_zero, ← Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor β,
      Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc, map_unit_comp_pushforwardBaseChange_app]
  have key : (fun w : Ext.{1} ((analyticInverseImage x).obj A)
        ((analyticInverseImage x).obj ((smallEtalePushforwardAb f).obj G)) n =>
        w.comp (Ext.mk₀ (asIso (β.app G)).hom) (add_zero n)) ∘
      ((analyticInverseImage x).mapExtAddHom A ((smallEtalePushforwardAb f).obj G) n) ∘
      (fun z : Ext.{1} ((etaleAbelianInverseImage.{0, 0} f).obj A) G n =>
        (Ext.mk₀ (a.unit.app A)).comp (z.mapExactFunctor (smallEtalePushforwardAb f))
          (zero_add n)) =
      (fun y : Ext.{1} ((analyticPullback x x' f hf).obj ((analyticInverseImage x).obj A))
          ((analyticInverseImage x').obj G) n =>
        (Ext.mk₀ (b.unit.app ((analyticInverseImage x).obj A))).comp
          (y.mapExactFunctor (analyticPushforward x x' f hf)) (zero_add n)) ∘
      (fun y : Ext.{1} ((analyticInverseImage x').obj ((etaleAbelianInverseImage.{0, 0} f).obj A))
          ((analyticInverseImage x').obj G) n => (Ext.mk₀ (γ.app A).symm.hom).comp y (zero_add n)) ∘
      ((analyticInverseImage x').mapExtAddHom ((etaleAbelianInverseImage.{0, 0} f).obj A) G n) :=
    funext hsq
  change Function.Bijective ((analyticInverseImage x).mapExtAddHom A
      ((smallEtalePushforwardAb f).obj G) n) ↔
    Function.Bijective ((analyticInverseImage x').mapExtAddHom
      ((etaleAbelianInverseImage.{0, 0} f).obj A) G n)
  constructor
  · intro h
    have h1 := Eq.mp (congrArg Function.Bijective key) (hB.comp (h.comp hΦ₁))
    exact (Function.Bijective.of_comp_iff' hT _).1 ((Function.Bijective.of_comp_iff' hΦ₂ _).1 h1)
  · intro h
    have h1 := Eq.mpr (congrArg Function.Bijective key) (hΦ₂.comp (hT.comp h))
    exact (Function.Bijective.of_comp_iff _ hΦ₁).1 ((Function.Bijective.of_comp_iff' hB _).1 h1)

end Pushforward

/-! ### Stalks on the bounded and on Mathlib's small étale sites -/

section BoundedStalk

universe u

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (s : GeometricPoint S)
  {A : Type*} [Category A] [HasColimitsOfSize.{u, u} A]

instance initial_toPointSmallEtaleFiberElements :
    (GeometricPoint.EtaleNeighborhood.toPointSmallEtaleFiberElements B hS s).Initial :=
  have : (GeometricPoint.EtaleNeighborhood.toPointSmallEtaleFiberElements B hS s ⋙
      (GeometricPoint.EtaleNeighborhood.equivFiberElements s).inverse).Initial :=
    GeometricPoint.EtaleNeighborhood.initial_ofGeometricPointSitePointFiberElements B hS s
  Functor.initial_of_comp_full_faithful _
    (GeometricPoint.EtaleNeighborhood.equivFiberElements s).inverse

/-- The stalk of [Stacks, Tag 040R] of the restriction of a presheaf on `S.Etale` to the
bounded site maps to its stalk at Mathlib's point `pointSmallEtale s.hom`. -/
noncomputable def etaleStalkToPresheafFiber (P : S.Etaleᵒᵖ ⥤ A) :
    etaleStalk B S hS s ((SmallEtale.toEtaleSite B S hS).op ⋙ P) ⟶
      (pointSmallEtale s.hom).presheafFiber.obj P :=
  colimit.pre ((CategoryOfElements.π (pointSmallEtale s.hom).fiber).op ⋙ P)
    (GeometricPoint.EtaleNeighborhood.toPointSmallEtaleFiberElements B hS s).op

instance (P : S.Etaleᵒᵖ ⥤ A) : IsIso (etaleStalkToPresheafFiber B hS s P) := by
  have : (GeometricPoint.EtaleNeighborhood.toPointSmallEtaleFiberElements B hS s).op.Final :=
    inferInstance
  exact Functor.Final.colimit_pre_isIso _

@[reassoc (attr := simp)]
theorem ι_etaleStalkToPresheafFiber (P : S.Etaleᵒᵖ ⥤ A)
    (V : (geometricPointFiber B S hS s).Elements) :
    colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.toEtaleSite B S hS).op ⋙ P) (op V) ≫ etaleStalkToPresheafFiber B hS s P =
      (pointSmallEtale s.hom).toPresheafFiber ((SmallEtale.toEtaleSite B S hS).obj V.1)
        ((toEtaleSiteFiberIso B S hS s).inv.app V.1 V.2) P :=
  colimit.ι_pre ((CategoryOfElements.π (pointSmallEtale s.hom).fiber).op ⋙ P)
    (GeometricPoint.EtaleNeighborhood.toPointSmallEtaleFiberElements B hS s).op (op V)

end BoundedStalk

/-! ### The skyscraper sheaves of `ε_*` on sections -/

section SkyscraperIso

variable {Y : Scheme.{0}} (y : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType y]

/-- The free–forgetful adjunction for abelian sheaves on `Y(ℂ)`. -/
abbrev freeAdj := Sheaf.adjunction (_root_.Opens.grothendieckTopology (analyticSpace y))
  AddCommGrpCat.adj.{1}

/-- The generator of `ℤ[Φ U](V)` given by a section `σ` of `U(ℂ) → Y(ℂ)` over `V`. -/
noncomputable abbrev sectionGenerator (U : Y.Etale) {V : TopologicalSpace.Opens (analyticSpace y)}
    (σ : (sectionsPresheaf y U).obj (op V)) :
    ToType (((freeSectionsFunctor y).obj U).obj.obj (op V)) :=
  ((freeAdj y).unit.app ((sectionsFunctor y).obj U)).hom.app (op V) σ

/-- The inverse of the stalk identification `ℤ[Φ U]_p ≅ ℤ[fibre of U at p]` sends the
generator `t` to the germ of the generator given by any section through `t`. -/
theorem freeSectionsFunctorCompSheafFiberIso_inv_app_of (p : ComplexPoints y) (U : Y.Etale)
    (t : (etPoint y p).fiber.obj U) (V : TopologicalSpace.Opens (analyticSpace y))
    (hpV : ULift.up p ∈ V)
    (σ : (sectionsPresheaf y U).obj (op V))
    (hσ : sectionsFiberToFiber y p U ((anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩
      (sectionsPresheaf y U) σ) = ULift.up t) :
    (freeSectionsFunctorCompSheafFiberIso y p).inv.app U (FreeAbelianGroup.of (ULift.up t)) =
      (anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ ((freeSectionsFunctor y).obj U).obj
        (sectionGenerator y U σ) := by
  have hgen : sectionGenerator y U σ = (toSheafify (_root_.Opens.grothendieckTopology
      (analyticSpace y)) ((sectionsPresheaf y U) ⋙ AddCommGrpCat.free.{1})).app (op V)
        (FreeAbelianGroup.of σ) := by
    simp only [sectionGenerator, Sheaf.adjunction_unit_app_hom]
    rfl
  have key : (freeSectionsFunctorCompSheafFiberIso y p).hom.app U
      ((anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ ((freeSectionsFunctor y).obj U).obj
        (sectionGenerator y U σ)) = FreeAbelianGroup.of (ULift.up t) := by
    rw [hgen]
    let P := sectionsPresheaf y U ⋙ AddCommGrpCat.free.{1}
    have e1 : ((anPoint y p).presheafToSheafCompSheafFiberIso AddCommGrpCat.{1}).hom.app P
        ((anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ ((presheafToSheaf _ _).obj P).obj
          ((toSheafify _ P).app (op V) (FreeAbelianGroup.of σ))) =
        (anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ P (FreeAbelianGroup.of σ) := by
      have hm : ((toSheafify (_root_.Opens.grothendieckTopology (analyticSpace y)) P).app (op V) ≫
          (anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ ((presheafToSheaf _ _).obj P).obj) ≫
          ((anPoint y p).presheafToSheafCompSheafFiberIso AddCommGrpCat.{1}).hom.app P =
          (anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ P := by
        erw [← (anPoint y p).toPresheafFiber_naturality]
        exact (Category.assoc _ _ _).trans ((congrArg _
          (((anPoint y p).presheafToSheafCompSheafFiberIso AddCommGrpCat.{1}).inv_hom_id_app
            P)).trans
            (Category.comp_id _))
      exact ConcreteCategory.congr_hom hm _
    have e2 := ConcreteCategory.congr_hom
      (GrothendieckTopology.Point.toPresheafFiber_presheafFiberCompIso_hom_app (A := Type 1)
        (anPoint y p) (AddCommGrpCat.free.{1}) V ⟨⟨hpV⟩⟩ (sectionsPresheaf y U))
      (FreeAbelianGroup.of σ)
    change (Functor.isoWhiskerRight (sectionsFunctorCompSheafFiberIso y p)
        AddCommGrpCat.free.{1}).hom.app U
      (((anPoint y p).presheafFiberCompIso (A := Type 1) AddCommGrpCat.free.{1}).hom.app
        (sectionsPresheaf y U)
        (((anPoint y p).presheafToSheafCompSheafFiberIso AddCommGrpCat.{1}).hom.app P
          ((anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ ((presheafToSheaf _ _).obj P).obj
            ((toSheafify _ P).app (op V) (FreeAbelianGroup.of σ))))) = _
    rw [e1]
    erw [e2]
    change AddCommGrpCat.free.{1}.map ((sectionsFunctorCompSheafFiberIso y p).hom.app U)
      (AddCommGrpCat.free.{1}.map ((anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩ (sectionsPresheaf y U))
        (FreeAbelianGroup.of σ)) = _
    erw [AddCommGrpCat.free_map_coe, AddCommGrpCat.free_map_coe]
    dsimp only
    exact congrArg FreeAbelianGroup.of hσ
  refine (congrArg _ key.symm).trans ?_
  exact ConcreteCategory.congr_hom ((freeSectionsFunctorCompSheafFiberIso y p).hom_inv_id_app U) _

/-- The component at a geometric point `t` of `U` over `p` of the identification
`ε_*(skyscraper M at p) ≅ skyscraper M at p̄` is evaluation at the generator given by a section
through `t`. -/
theorem π_skyscraperIso_hom_app (p : ComplexPoints y) (M : AddCommGrpCat.{1}) (U : Y.Etale)
    (t : (etPoint y p).fiber.obj U) (V : TopologicalSpace.Opens (analyticSpace y))
    (hpV : ULift.up p ∈ V) (σ : (sectionsPresheaf y U).obj (op V))
    (hσ : sectionsFiberToFiber y p U ((anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩
      (sectionsPresheaf y U) σ) = ULift.up t)
    (φ : (freeSectionsFunctor y).obj U ⟶ (anPoint y p).skyscraperSheaf M) :
    Pi.π (fun _ => M) t (((skyscraperIso y p).hom.app M).hom.app (op U) φ) =
      Pi.π (fun _ => M) (⟨⟨hpV⟩⟩ : (anPoint y p).fiber.obj V)
        (φ.hom.app (op V) (sectionGenerator y U σ)) := by
  change (Pi.π (fun _ => M) t) ((AddCommGrpCat.freeHomIsoPi _ M).hom
    ((freeSectionsFunctorCompSheafFiberIso y p).inv.app U ≫
      ((anPoint y p).skyscraperSheafAdjunction.homEquiv _ _).symm φ)) = _
  have h1 := ConcreteCategory.congr_hom (AddCommGrpCat.freeHomIsoPi_hom_π _ M t)
    (((freeSectionsFunctorCompSheafFiberIso y p).inv.app U ≫
      ((anPoint y p).skyscraperSheafAdjunction.homEquiv ((freeSectionsFunctor y).obj U) M).symm φ :
        AddCommGrpCat.free.obj (ULift.{1} ((etPoint y p).fiber.obj U)) ⟶ M))
  refine h1.trans ?_
  rw [AddCommGrpCat.freeHomEval_apply]
  change (((anPoint y p).skyscraperSheafAdjunction.homEquiv
      ((freeSectionsFunctor y).obj U) M).symm φ)
    ((freeSectionsFunctorCompSheafFiberIso y p).inv.app U (FreeAbelianGroup.of (ULift.up t))) = _
  rw [freeSectionsFunctorCompSheafFiberIso_inv_app_of y p U t V hpV σ hσ]
  have e := GrothendieckTopology.Point.skyscraperSheafAdjunction_homEquiv_symm_apply (anPoint y p) φ
  have h2 := ConcreteCategory.congr_hom
    (GrothendieckTopology.Point.toPresheafFiber_skyscraperPresheafHomEquiv_symm _ φ.hom V ⟨⟨hpV⟩⟩)
    (sectionGenerator y U σ)
  exact (ConcreteCategory.congr_hom e ((anPoint y p).toPresheafFiber V ⟨⟨hpV⟩⟩
    ((freeSectionsFunctor y).obj U).obj (sectionGenerator y U σ))).trans h2

end SkyscraperIso

/-! ### The base change of skyscraper sheaves -/

section SkyscraperBaseChange

open Stacks.EtaleCohomology

/-- Base change of étale schemes along a morphism of schemes. -/
local notation "𝔅" => Stacks.EtaleCohomology.smallEtaleBaseChange

variable {X X' : Scheme.{0}} (x : X ⟶ Spec (.of ℂ)) (x' : X' ⟶ Spec (.of ℂ))
  [LocallyOfFiniteType x] [LocallyOfFiniteType x'] (f : X' ⟶ X) (hf : f ≫ x = x')

/-- `ℤ[Φ U] ⟶ f_an,* ℤ[Φ (U ×_X X')]` sends the generator of a section `σ` to the generator of
its base change `w ↦ (σ (f w), w)`. -/
theorem freeBaseChangeSections_sectionGenerator (U : X.Etale)
    {V : TopologicalSpace.Opens (analyticSpace x)} (σ : (sectionsPresheaf x U).obj (op V)) :
    (freeBaseChangeSections x x' f hf U).hom.app (op V) (sectionGenerator x U σ) =
      sectionGenerator x' ((𝔅 f).obj U) (baseChangeSection x x' f hf U V σ) := by
  have h := (freeAdj x).homEquiv_unit _ _ (freeBaseChangeSections x x' f hf U)
  rw [freeBaseChangeSections, Equiv.apply_symm_apply] at h
  have h' := congrArg (fun φ => φ.hom.app (op V) σ) h
  exact h'.symm

end SkyscraperBaseChange

end AlgebraicGeometry.Scheme.ComplexPoints
