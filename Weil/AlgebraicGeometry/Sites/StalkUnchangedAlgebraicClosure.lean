module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Weil.Attr

/-!
# Étale stalks are unchanged under extension of a separably closed field

Let `S` be a scheme, `t : Spec Ω' ⟶ S` a morphism from the spectrum of a separably closed
field and `a : Spec Ω ⟶ Spec Ω'` a morphism of spectra of separably closed fields, so that
`s = a ≫ t` is again a point of the small étale site. Precomposition with `a` sends a lift
of `t` to an étale `S`-scheme `U` to a lift of `s`, and this is a bijection: a morphism
`Spec Ω ⟶ U` over `S` corresponds to a point `x ∈ U` and an embedding `κ(x) ⟶ Ω` over
`κ(t₀)`; since `κ(x)` is separable algebraic over `κ(t₀)` and `Ω'` is separably closed, the
image of `κ(x)` lies in `Ω'`, so the lift descends. Hence `a` induces an isomorphism of
points of the small étale site and so an isomorphism of stalk functors `F_t ≅ F_s`, sending
the germ of a section at `(U, u)` to its germ at `(U, a ≫ u)`.

The case of an algebraic closure `k̄` of a separably closed field `k` is the statement that
the stalk at a geometric point does not change when its field is replaced by an algebraic
closure.

## Main definitions

* `AlgebraicGeometry.Scheme.pointSmallEtaleHomOfFac`: the morphism of points of the small
  étale site induced by a morphism of field spectra over `S`.
* `AlgebraicGeometry.Scheme.presheafFiberIsoOfFac`: the induced isomorphism of stalk
  functors.
* `AlgebraicGeometry.Scheme.presheafFiberIsoAlgebraicClosure`: the isomorphism
  `F_y ≅ F_{y_{k̄}}` for an algebraic closure `k̄` of `k`.

## Main results

* `AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed_of_specMap`: a lift to an
  étale scheme of a point `Spec Ω ⟶ Spec Ω' ⟶ S` descends to `Spec Ω'` when `Ω'` is
  separably closed.
* `AlgebraicGeometry.Scheme.isIso_pointSmallEtaleHomOfFac`: the induced morphism of points
  is an isomorphism.
* `AlgebraicGeometry.Scheme.toPresheafFiber_presheafFiberIsoAlgebraicClosure_hom_app`: the
  description of the isomorphism on germs.

## Implementation notes

Stalks are Mathlib's `CategoryTheory.GrothendieckTopology.Point.presheafFiber` at the points
`AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site `S.Etale`, which are
defined for separably closed fields, and the result is proved for an arbitrary morphism of
spectra of separably closed fields over `S`, of which the algebraic closure is a special
case. The proof does not pass through the separable closure of `κ(t₀)` in `Ω'`: the descent
of lifts is proved directly from the separability of residue field extensions of étale
morphisms.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3.
* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
-/

/- Stated on Mathlib's `Scheme.Etale S` / `pointSmallEtale` (separably closed fields), since
StacksFrontier's `GeometricPoint` requires algebraically closed fields and so cannot express
FK's separably closed point `y`. The general isomorphism (any morphism of separably closed
field spectra) is stronger than FK. -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.GrothendieckTopology.Point.Hom

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}
  {A : Type*} [Category* A] [Limits.HasColimitsOfSize.{u, u} A]

/-- An isomorphism of points of a site induces an isomorphism of presheaf fibres. -/
instance isIso_presheafFiber {Φ₁ Φ₂ : Point.{u} J} (f : Φ₁ ⟶ Φ₂) [IsIso f] :
    IsIso (f.presheafFiber (A := A)) :=
  ⟨(inv f).presheafFiber, by
    rw [← presheafFiber_comp, IsIso.inv_hom_id, presheafFiber_id], by
    rw [← presheafFiber_comp, IsIso.hom_inv_id, presheafFiber_id]⟩

end CategoryTheory.GrothendieckTopology.Point.Hom

namespace AlgebraicGeometry.Scheme

lemma exists_fac_of_etale_of_isSepClosed_of_specMap {X S : Scheme.{u}} (f : X ⟶ S) [Etale f]
    {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω'] (ι : Ω' →+* Ω)
    (t : Spec (.of Ω') ⟶ S) (p : Spec (.of Ω) ⟶ X)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ t) :
    ∃ q : Spec (.of Ω') ⟶ X, Spec.map (CommRingCat.ofHom ι) ≫ q = p ∧ q ≫ f = t := by
  obtain ⟨⟨x, c⟩, rfl⟩ := (SpecToEquivOfField Ω X).symm.surjective p
  obtain ⟨⟨y, d⟩, rfl⟩ := (SpecToEquivOfField Ω' S).symm.surjective t
  simp only [SpecToEquivOfField_symm_apply] at hp ⊢
  have hp' : (SpecToEquivOfField Ω S).symm ⟨f x, f.residueFieldMap x ≫ c⟩ =
      (SpecToEquivOfField Ω S).symm ⟨y, d ≫ CommRingCat.ofHom ι⟩ := by
    simp only [SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc,
      Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    exact hp
  obtain ⟨hxy, hcd⟩ := Sigma.mk.inj ((SpecToEquivOfField Ω S).symm.injective hp')
  subst hxy
  have hcd : f.residueFieldMap x ≫ c = d ≫ CommRingCat.ofHom ι := eq_of_heq hcd
  have hcd' : c.hom.comp (f.residueFieldMap x).hom = ι.comp d.hom :=
    congrArg CommRingCat.Hom.hom hcd
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have hrange : ∀ z, c.hom z ∈ ι.range := by
    intro z
    have hsep : (minpoly (S.residueField (f x)) z).Separable :=
      Algebra.IsSeparable.isSeparable _ z
    have hsplit := IsSepClosed.splits_codomain (f := d.hom) _ hsep
    refine hsplit.mem_range_of_isRoot
      (Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsSeparable.isIntegral _ z))) ?_
    rw [Polynomial.map_map, ← hcd', Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.hom_eval₂]
    change c.hom (Polynomial.aeval z (minpoly (S.residueField (f x)) z)) = 0
    rw [minpoly.aeval, map_zero]
  let e : Ω' ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b h => ι.injective (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩
  let b : X.residueField x →+* Ω' := e.symm.toRingHom.comp (c.hom.codRestrict _ hrange)
  have hb : ι.comp b = c.hom := by
    ext z
    change ((e (e.symm ⟨c.hom z, hrange z⟩) : ι.range) : Ω) = c.hom z
    rw [RingEquiv.apply_symm_apply]
  have hb' : CommRingCat.ofHom b ≫ CommRingCat.ofHom ι = c := by
    ext1; exact hb
  have hbd : f.residueFieldMap x ≫ CommRingCat.ofHom b = d := by
    ext1
    apply RingHom.ext
    intro a
    apply ι.injective
    have := congrArg (fun g : _ →+* Ω => g a) hcd'
    simp only [← hb, RingHom.comp_apply] at this
    exact this
  refine ⟨Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hb']
  · rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      ← Spec.map_comp]
    exact congrArg (fun g => Spec.map g ≫ S.fromSpecResidueField (f x)) hbd


variable {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']

/-- A morphism `a : Spec Ω ⟶ Spec Ω'` with `a ≫ t = s` induces a morphism of points
`pointSmallEtale s ⟶ pointSmallEtale t` of the small étale site; on fibres it sends a lift
`u` of `t` to the lift `a ≫ u` of `s`. -/
def pointSmallEtaleHomOfFac (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω')) (ha : a ≫ t = s) :
    pointSmallEtale s ⟶ pointSmallEtale t where
  hom :=
    { app U := ↾ (fun p => (Over.homMk (U := Over.mk s) (V := Over.mk t) a ha) ≫ p)
      naturality := by
        intro U V g
        ext p
        exact (Category.assoc _ _ _).symm }

lemma pointSmallEtaleHomOfFac_hom_app_apply (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω')) (ha : a ≫ t = s) (U : S.Etale)
    (p : (pointSmallEtale t).fiber.obj U) :
    (pointSmallEtaleHomOfFac s t a ha).hom.app U p =
      (Over.homMk (U := Over.mk s) (V := Over.mk t) a ha) ≫ p :=
  rfl

/-- When the target field `Ω'` is separably closed, the morphism of points induced by
`Spec Ω ⟶ Spec Ω'` is an isomorphism: every lift of `s` to an étale `S`-scheme descends
uniquely to a lift of `t`. -/
theorem isIso_pointSmallEtaleHomOfFac (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω')) (ha : a ≫ t = s) :
    IsIso (pointSmallEtaleHomOfFac s t a ha) := by
  let f := pointSmallEtaleHomOfFac s t a ha
  have hf : IsIso f.hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    constructor
    · intro p q hpq
      apply Over.OverMorphism.ext
      have : Epi a := Flat.epi_of_flat_of_surjective a
      exact (cancel_epi a).1 (congrArg (fun m => m.left) hpq)
    · intro p
      obtain ⟨φ, rfl⟩ := Spec.map_surjective a
      obtain ⟨q, hqa, hqf⟩ := exists_fac_of_etale_of_isSepClosed_of_specMap U.hom φ.hom t
        p.left ((Over.w p).trans ha.symm)
      refine ⟨Over.homMk q hqf, ?_⟩
      apply Over.OverMorphism.ext
      exact hqa
  let g : pointSmallEtale t ⟶ pointSmallEtale s := ⟨inv f.hom⟩
  exact ⟨g, GrothendieckTopology.Point.hom_ext (IsIso.inv_hom_id f.hom),
    GrothendieckTopology.Point.hom_ext (IsIso.hom_inv_id f.hom)⟩

variable {A : Type*} [Category* A] [Limits.HasColimitsOfSize.{u, u} A]

/-- The map of étale stalks `F_t ⟶ F_s` induced by `a : Spec Ω ⟶ Spec Ω'` over `S`, natural
in the presheaf `F`, is an isomorphism when `Ω'` is separably closed. -/
def presheafFiberIsoOfFac (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
    (a : Spec (.of Ω) ⟶ Spec (.of Ω')) (ha : a ≫ t = s) :
    (pointSmallEtale t).presheafFiber (A := A) ≅ (pointSmallEtale s).presheafFiber :=
  have := isIso_pointSmallEtaleHomOfFac s t a ha
  asIso (pointSmallEtaleHomOfFac s t a ha).presheafFiber

lemma toPresheafFiber_presheafFiberIsoOfFac_hom_app (s : Spec (.of Ω) ⟶ S)
    (t : Spec (.of Ω') ⟶ S) (a : Spec (.of Ω) ⟶ Spec (.of Ω')) (ha : a ≫ t = s)
    (U : S.Etale) (u : (pointSmallEtale t).fiber.obj U) (F : S.Etaleᵒᵖ ⥤ A) :
    (pointSmallEtale t).toPresheafFiber U u F ≫ (presheafFiberIsoOfFac s t a ha).hom.app F =
      (pointSmallEtale s).toPresheafFiber U
        ((Over.homMk (U := Over.mk s) (V := Over.mk t) a ha) ≫ u) F := by
  simp [presheafFiberIsoOfFac, pointSmallEtaleHomOfFac_hom_app_apply]

section AlgebraicClosure

variable {k : Type u} [Field k] [IsSepClosed k] (y : Spec (.of k) ⟶ S)

/-- **The stalk is unchanged under passage to an algebraic closure.** For a geometric point
`y : Spec k ⟶ S` with `k` separably closed and `ι : Spec k̄ ⟶ Spec k` induced by an
algebraic closure `k̄` of `k`, the map of étale stalks `F_y ⟶ F_{y ∘ ι}` (on germs:
`toPresheafFiber_presheafFiberIsoAlgebraicClosure_hom_app`) is an isomorphism, natural in the
presheaf `F`. -/
@[weil "lem_fk103_stalk_unchanged_algebraic_closure"]
def presheafFiberIsoAlgebraicClosure :
    (pointSmallEtale y).presheafFiber (A := A) ≅
      (pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) ≫ y)).presheafFiber :=
  presheafFiberIsoOfFac _ y _ rfl

/-- The isomorphism `presheafFiberIsoAlgebraicClosure` sends the germ of a section at an étale
neighbourhood `(U, u)` of `y` to its germ at `(U, u ∘ ι)`. -/
@[weil "lem_fk103_stalk_unchanged_algebraic_closure"]
lemma toPresheafFiber_presheafFiberIsoAlgebraicClosure_hom_app (U : S.Etale)
    (u : (pointSmallEtale y).fiber.obj U) (F : S.Etaleᵒᵖ ⥤ A) :
    (pointSmallEtale y).toPresheafFiber U u F ≫
        (presheafFiberIsoAlgebraicClosure (A := A) y).hom.app F =
      (pointSmallEtale _).toPresheafFiber U
        ((Over.homMk (U := Over.mk _) (V := Over.mk y)
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) rfl) ≫ u) F :=
  toPresheafFiber_presheafFiberIsoOfFac_hom_app _ y _ rfl U u F

end AlgebraicClosure

end AlgebraicGeometry.Scheme
