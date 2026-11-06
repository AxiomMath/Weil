module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Stalks of the restriction of an étale presheaf to an étale `X`-scheme

Let `X` be a scheme in a big étale site `B`, let `q : U ⟶ X` be an object of the small étale
site of `X` and let `t` be a geometric point of `U`. The restriction `F|_U` of a presheaf `F` on
the small étale site of `X` is the presheaf `V ↦ F(V)` on the small étale site of `U`, where an
étale `U`-scheme `V` is regarded as étale over `X` through `q`
(`AlgebraicGeometry.smallEtalePostcompose`). An étale neighbourhood `(V, v)` of `t` is then an
étale neighbourhood of `q ∘ t`, which gives a map of stalks `(F|_U)_t ⟶ F_{q ∘ t}` sending the
germ of `a ∈ F(V)` at `(V, v)` to the germ of `a` at `(V, v)`.

This map is bijective and natural in `F`. The functor between the categories of étale
neighbourhoods is initial: an étale neighbourhood `(W, w)` of `q ∘ t` receives the first
projection from the neighbourhood `(W ×_X U, (w, t))` of `t`, and two morphisms from the image
of a neighbourhood of `t` to `(W, w)` factor through `W ×_X U` as two morphisms of
neighbourhoods of `t`, which a further neighbourhood of `t` equalizes because the category of
neighbourhoods is cofiltered. Colimits along an initial functor of the opposite categories agree.

## Main definitions

* `AlgebraicGeometry.geometricPointFiberPostcompose` — the functor from étale neighbourhoods of
  `t` to étale neighbourhoods of `q ∘ t`.
* `AlgebraicGeometry.etaleStalkRestrictionMap` — the map `(F|_U)_t ⟶ F_{q ∘ t}`.
* `AlgebraicGeometry.etaleStalkRestrictionIso` — the natural isomorphism
  `(F|_U)_t ≅ F_{q ∘ t}` of functors on presheaves.

## Main results

* `AlgebraicGeometry.initial_geometricPointFiberPostcompose` — the functor between the
  categories of neighbourhoods is initial.
* `AlgebraicGeometry.etaleStalkRestrictionMap_ι_apply` — the map on germs.
* `AlgebraicGeometry.bijective_etaleStalkRestrictionMap` — for presheaves of sets the map is
  bijective.
* `AlgebraicGeometry.etaleStalkRestrictionMap_naturality` — the map is natural in the presheaf.

## Implementation notes

The statement is made for presheaves on the small étale site `AlgebraicGeometry.SmallEtale`,
with values in any category with small colimits; the sheaf condition is not used. The stalk is
`AlgebraicGeometry.etaleStalk`, the colimit over the category of elements of the functor of lifts
of the geometric point, and geometric points take values in algebraically closed fields.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3 Appendix][FreitagKiehl]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

/- FK states the
lemma for sheaves of sets on the noetherian separated étale category `Et(X)`; it is stated here
on StacksFrontier's `SmallEtale` (the étale site used throughout), for presheaves
with values in any cocomplete category (a generalization; the sheaf condition is not used). The
restriction is `(smallEtalePostcompose B X hX U).op ⋙ F`, the `SmallEtale` counterpart of
`AlgebraicGeometry.EtalePresheaf.restrict`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)

variable (t : GeometricPoint U.obj.left.1)

/-- An étale neighbourhood `(V, v)` of a geometric point `t` of `U` is an étale neighbourhood
`(V, v)` of its image in `X`, with `V` regarded as étale over `X` through `U`. -/
def geometricPointFiberPostcompose :
    (geometricPointFiber B U.obj.left.1 U.obj.left.property t).Elements ⥤
      (geometricPointFiber B X hX (t.map (B.inclusion.map U.obj.hom))).Elements where
  obj V := ⟨(smallEtalePostcompose B X hX U).obj V.1, ⟨V.2.1, by
    change V.2.1 ≫ B.inclusion.map (V.1.obj.hom ≫ U.obj.hom) = t.hom ≫ B.inclusion.map U.obj.hom
    rw [Functor.map_comp, ← Category.assoc]
    exact congrArg (· ≫ B.inclusion.map U.obj.hom) V.2.2⟩⟩
  map {V W} f := ⟨(smallEtalePostcompose B X hX U).map f.1, by
    apply Subtype.ext
    change V.2.1 ≫ (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map f.1 = W.2.1
    exact congrArg Subtype.val f.2⟩

lemma geometricPointFiberPostcompose_comp_π :
    geometricPointFiberPostcompose B X hX U t ⋙ CategoryOfElements.π _ =
      CategoryOfElements.π _ ⋙ smallEtalePostcompose B X hX U :=
  rfl

/-- The fibre product `W ×_X U` of a pullback square in the big étale site stays a pullback
square of schemes. -/
lemma isPullback_inclusion_map_pullback_fst_snd (W : SmallEtale B X hX) :
    IsPullback (B.inclusion.map (pullback.fst W.obj.hom U.obj.hom))
      (B.inclusion.map (pullback.snd W.obj.hom U.obj.hom))
      (B.inclusion.map W.obj.hom) (B.inclusion.map U.obj.hom) :=
  IsPullback.map B.inclusion (IsPullback.of_hasPullback W.obj.hom U.obj.hom)

/-- The first projection `W ×_X U ⟶ W`, as a morphism of the small étale site of `X`, where
`W ×_X U` is étale over `X` through `U`. -/
def smallEtaleBaseChangeFst (W : SmallEtale B X hX) :
    (smallEtalePostcompose B X hX U).obj ((smallEtaleBaseChange B U.obj.hom).obj W) ⟶ W :=
  ObjectProperty.homMk (Over.homMk (pullback.fst W.obj.hom U.obj.hom) pullback.condition)

lemma toScheme_map_smallEtaleBaseChangeFst (W : SmallEtale B X hX) :
    (SmallEtale.toScheme B X hX).map (smallEtaleBaseChangeFst B X hX U W) =
      B.inclusion.map (pullback.fst W.obj.hom U.obj.hom) :=
  rfl

/-- A morphism `V ⟶ W` over `X` from an étale `U`-scheme `V` gives the morphism
`V ⟶ W ×_X U` over `U`. -/
def smallEtaleBaseChangeLiftOfHom {V : SmallEtale B U.obj.left.1 U.obj.left.property}
    {W : SmallEtale B X hX}
    (s : (smallEtalePostcompose B X hX U).obj V ⟶ W) :
    V ⟶ (smallEtaleBaseChange B U.obj.hom).obj W :=
  ObjectProperty.homMk (Over.homMk (pullback.lift s.hom.left V.obj.hom (Over.w s.hom))
    (pullback.lift_snd _ _ _))

lemma toScheme_map_baseChangeLiftOfHom_fst
    {V : SmallEtale B U.obj.left.1 U.obj.left.property} {W : SmallEtale B X hX}
    (s : (smallEtalePostcompose B X hX U).obj V ⟶ W) :
    (SmallEtale.toScheme B _ _).map (smallEtaleBaseChangeLiftOfHom B X hX U s) ≫
        B.inclusion.map (pullback.fst W.obj.hom U.obj.hom) =
      (SmallEtale.toScheme B X hX).map s := by
  exact (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (pullback.lift_fst s.hom.left V.obj.hom (Over.w s.hom)))

lemma toScheme_map_baseChangeLiftOfHom_snd
    {V : SmallEtale B U.obj.left.1 U.obj.left.property} {W : SmallEtale B X hX}
    (s : (smallEtalePostcompose B X hX U).obj V ⟶ W) :
    (SmallEtale.toScheme B _ _).map (smallEtaleBaseChangeLiftOfHom B X hX U s) ≫
        B.inclusion.map (pullback.snd W.obj.hom U.obj.hom) =
      B.inclusion.map V.obj.hom := by
  exact (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (pullback.lift_snd s.hom.left V.obj.hom (Over.w s.hom)))

lemma comp_toScheme_map_baseChangeLiftOfHom_fst {Z : Scheme.{u}}
    {V : SmallEtale B U.obj.left.1 U.obj.left.property} {W : SmallEtale B X hX}
    (p : Z ⟶ (SmallEtale.toScheme B _ _).obj V)
    (s : (smallEtalePostcompose B X hX U).obj V ⟶ W) :
    (p ≫ (SmallEtale.toScheme B _ _).map (smallEtaleBaseChangeLiftOfHom B X hX U s)) ≫
        B.inclusion.map (pullback.fst W.obj.hom U.obj.hom) =
      p ≫ (SmallEtale.toScheme B X hX).map s := by
  rw [Category.assoc, toScheme_map_baseChangeLiftOfHom_fst]

lemma comp_toScheme_map_baseChangeLiftOfHom_snd {Z : Scheme.{u}}
    {V : SmallEtale B U.obj.left.1 U.obj.left.property} {W : SmallEtale B X hX}
    (p : Z ⟶ (SmallEtale.toScheme B _ _).obj V)
    (s : (smallEtalePostcompose B X hX U).obj V ⟶ W) :
    (p ≫ (SmallEtale.toScheme B _ _).map (smallEtaleBaseChangeLiftOfHom B X hX U s)) ≫
        B.inclusion.map (pullback.snd W.obj.hom U.obj.hom) =
      p ≫ B.inclusion.map V.obj.hom := by
  rw [Category.assoc, toScheme_map_baseChangeLiftOfHom_snd]

@[reassoc]
lemma smallEtalePostcompose_map_baseChangeLiftOfHom_comp_fst
    {V : SmallEtale B U.obj.left.1 U.obj.left.property} {W : SmallEtale B X hX}
    (s : (smallEtalePostcompose B X hX U).obj V ⟶ W) :
    (smallEtalePostcompose B X hX U).map (smallEtaleBaseChangeLiftOfHom B X hX U s) ≫
      smallEtaleBaseChangeFst B X hX U W = s := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- An étale neighbourhood `(W, w)` of the image of `t` in `X` gives the étale neighbourhood
`(W ×_X U, (w, t))` of `t`. -/
def geometricPointFiberBaseChange
    (W : (geometricPointFiber B X hX (t.map (B.inclusion.map U.obj.hom))).Elements) :
    (geometricPointFiber B U.obj.left.1 U.obj.left.property t).Elements :=
  ⟨(smallEtaleBaseChange B U.obj.hom).obj W.1,
    ⟨(isPullback_inclusion_map_pullback_fst_snd B X hX U W.1).lift W.2.1 t.hom W.2.2,
      (isPullback_inclusion_map_pullback_fst_snd B X hX U W.1).lift_snd _ _ _⟩⟩

/-- The first projection `(W ×_X U, (w, t)) ⟶ (W, w)` of étale neighbourhoods of the image
of `t` in `X`. -/
def geometricPointFiberBaseChangeFst
    (W : (geometricPointFiber B X hX (t.map (B.inclusion.map U.obj.hom))).Elements) :
    (geometricPointFiberPostcompose B X hX U t).obj (geometricPointFiberBaseChange B X hX U t W) ⟶
      W :=
  ⟨smallEtaleBaseChangeFst B X hX U W.1,
    Subtype.ext ((isPullback_inclusion_map_pullback_fst_snd B X hX U W.1).lift_fst _ _ _)⟩

/-- The functor from étale neighbourhoods of `t` to étale neighbourhoods of its image in `X` is
initial. -/
instance initial_geometricPointFiberPostcompose :
    (geometricPointFiberPostcompose B X hX U t).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · intro W
    exact ⟨_, ⟨geometricPointFiberBaseChangeFst B X hX U t W⟩⟩
  · intro W V s s'
    have hpb := isPullback_inclusion_map_pullback_fst_snd B X hX U W.1
    let D : (geometricPointFiber B U.obj.left.1 U.obj.left.property t).Elements :=
      ⟨(smallEtaleBaseChange B U.obj.hom).obj W.1,
        (geometricPointFiber B _ _ t).map (smallEtaleBaseChangeLiftOfHom B X hX U s.1) V.2⟩
    have hss' :
        (geometricPointFiber B _ _ t).map (smallEtaleBaseChangeLiftOfHom B X hX U s'.1) V.2 =
          D.2 := by
      apply Subtype.ext
      change V.2.1 ≫ (SmallEtale.toScheme B _ _).map (smallEtaleBaseChangeLiftOfHom B X hX U s'.1) =
        V.2.1 ≫ (SmallEtale.toScheme B _ _).map (smallEtaleBaseChangeLiftOfHom B X hX U s.1)
      apply hpb.hom_ext
      · exact (comp_toScheme_map_baseChangeLiftOfHom_fst B X hX U _ s'.1).trans
          (((congrArg Subtype.val s'.2).trans (congrArg Subtype.val s.2).symm).trans
            (comp_toScheme_map_baseChangeLiftOfHom_fst B X hX U _ s.1).symm)
      · exact (comp_toScheme_map_baseChangeLiftOfHom_snd B X hX U _ s'.1).trans
          (comp_toScheme_map_baseChangeLiftOfHom_snd B X hX U _ s.1).symm
    let a : V ⟶ D := ⟨smallEtaleBaseChangeLiftOfHom B X hX U s.1, rfl⟩
    let a' : V ⟶ D := ⟨smallEtaleBaseChangeLiftOfHom B X hX U s'.1, hss'⟩
    obtain ⟨E, e, he⟩ := IsCofilteredOrEmpty.cone_maps a a'
    refine ⟨E, e, ?_⟩
    apply CategoryOfElements.ext
    have he' : e.1 ≫ smallEtaleBaseChangeLiftOfHom B X hX U s.1 =
        e.1 ≫ smallEtaleBaseChangeLiftOfHom B X hX U s'.1 :=
      congrArg Subtype.val he
    change (smallEtalePostcompose B X hX U).map e.1 ≫ s.1 =
      (smallEtalePostcompose B X hX U).map e.1 ≫ s'.1
    rw [← smallEtalePostcompose_map_baseChangeLiftOfHom_comp_fst B X hX U s.1,
      ← smallEtalePostcompose_map_baseChangeLiftOfHom_comp_fst B X hX U s'.1,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, he']

section Stalk

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- **The restriction-stalk map.** For a presheaf `F` on the small étale site of `X`, an object
`q : U ⟶ X` and a geometric point `t` of `U`, the map `(F|_U)_t ⟶ F_{q ∘ t}` sending the germ
of a section `a ∈ F|_U(V) = F(V)` at a neighbourhood `(V, v)` of `t` to the germ of `a` at the
neighbourhood `(V, v)` of `q ∘ t`. -/
@[weil "lem_fk103_restriction_stalk"]
def etaleStalkRestrictionMap (F : (SmallEtale B X hX)ᵒᵖ ⥤ A) :
    etaleStalk B U.obj.left.1 U.obj.left.property t ((smallEtalePostcompose B X hX U).op ⋙ F) ⟶
      etaleStalk B X hX (t.map (B.inclusion.map U.obj.hom)) F :=
  colimit.pre ((CategoryOfElements.π _).op ⋙ F) (geometricPointFiberPostcompose B X hX U t).op

/-- The restriction-stalk map sends the germ of a section at a neighbourhood `(V, v)` of `t` to
its germ at the neighbourhood `(V, v)` of `q ∘ t`. -/
@[reassoc (attr := simp)]
lemma ι_etaleStalkRestrictionMap (F : (SmallEtale B X hX)ᵒᵖ ⥤ A)
    (V : (geometricPointFiber B U.obj.left.1 U.obj.left.property t).Elements) :
    colimit.ι ((CategoryOfElements.π _).op ⋙ (smallEtalePostcompose B X hX U).op ⋙ F) (op V) ≫
        etaleStalkRestrictionMap B X hX U t F =
      colimit.ι ((CategoryOfElements.π _).op ⋙ F)
        (op ((geometricPointFiberPostcompose B X hX U t).obj V)) :=
  colimit.ι_pre ((CategoryOfElements.π _).op ⋙ F) (geometricPointFiberPostcompose B X hX U t).op
    (op V)

/-- The restriction-stalk map is an isomorphism. -/
instance isIso_etaleStalkRestrictionMap (F : (SmallEtale B X hX)ᵒᵖ ⥤ A) :
    IsIso (etaleStalkRestrictionMap B X hX U t F) :=
  haveI := Functor.final_op_of_initial (geometricPointFiberPostcompose B X hX U t)
  inferInstanceAs (IsIso (colimit.pre ((CategoryOfElements.π _).op ⋙ F)
    (geometricPointFiberPostcompose B X hX U t).op))

/-- The restriction-stalk map is natural in the presheaf. -/
@[reassoc, weil "lem_fk103_restriction_stalk"]
lemma etaleStalkRestrictionMap_naturality {F G : (SmallEtale B X hX)ᵒᵖ ⥤ A} (φ : F ⟶ G) :
    (etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property t A).map
        (Functor.whiskerLeft (smallEtalePostcompose B X hX U).op φ) ≫
      etaleStalkRestrictionMap B X hX U t G =
    etaleStalkRestrictionMap B X hX U t F ≫
      (etaleStalkPresheafFunctor B X hX (t.map (B.inclusion.map U.obj.hom)) A).map φ := by
  exact (colimit.pre_map (Functor.whiskerLeft (CategoryOfElements.π _).op φ)
    (geometricPointFiberPostcompose B X hX U t).op).symm

variable (A) in
/-- **The stalk of a restriction is the stalk at the image point**, as a natural isomorphism of
functors on presheaves: `(F|_U)_t ≅ F_{q ∘ t}`, with components the restriction-stalk maps. -/
@[weil "lem_fk103_restriction_stalk"]
def etaleStalkRestrictionIso :
    (Functor.whiskeringLeft _ _ A).obj (smallEtalePostcompose B X hX U).op ⋙
        etaleStalkPresheafFunctor B U.obj.left.1 U.obj.left.property t A ≅
      etaleStalkPresheafFunctor B X hX (t.map (B.inclusion.map U.obj.hom)) A :=
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ _ (isIso_etaleStalkRestrictionMap B X hX U t F))
    (fun φ => etaleStalkRestrictionMap_naturality B X hX U t φ)

@[simp]
lemma etaleStalkRestrictionIso_hom_app (F : (SmallEtale B X hX)ᵒᵖ ⥤ A) :
    (etaleStalkRestrictionIso B X hX U t A).hom.app F = etaleStalkRestrictionMap B X hX U t F :=
  rfl

end Stalk

section Sets

/-- For a presheaf of sets, the restriction-stalk map sends the class of `a ∈ F(V)` at a
neighbourhood `(V, v)` of `t` to the class of `a` at the neighbourhood `(V, v)` of `q ∘ t`. -/
@[weil "lem_fk103_restriction_stalk"]
lemma etaleStalkRestrictionMap_ι_apply (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    (V : (geometricPointFiber B U.obj.left.1 U.obj.left.property t).Elements)
    (a : F.obj (op ((smallEtalePostcompose B X hX U).obj V.1))) :
    etaleStalkRestrictionMap B X hX U t F
        (colimit.ι ((CategoryOfElements.π _).op ⋙ (smallEtalePostcompose B X hX U).op ⋙ F)
          (op V) a) =
      colimit.ι ((CategoryOfElements.π _).op ⋙ F)
        (op ((geometricPointFiberPostcompose B X hX U t).obj V)) a :=
  by rw [← ι_etaleStalkRestrictionMap B X hX U t F V]; rfl

/-- **FK I.3 Appendix, p. 36.** For a presheaf of sets `F` on the small étale site of `X`, an
object `q : U ⟶ X` and a geometric point `t` of `U`, the restriction-stalk map
`(F|_U)_t → F_{q ∘ t}` is bijective. -/
@[weil "lem_fk103_restriction_stalk"]
theorem bijective_etaleStalkRestrictionMap (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u) :
    Function.Bijective (etaleStalkRestrictionMap B X hX U t F) :=
  (isIso_iff_bijective _).1 inferInstance

end Sets

end AlgebraicGeometry
