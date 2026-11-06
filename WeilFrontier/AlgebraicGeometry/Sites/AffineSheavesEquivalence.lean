module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.AffineSheafRestriction
public import WeilFrontier.Defs.AlgebraicGeometry.Topologies.Etale.EtaleSheaf
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Étale sheaves on an affine scheme are sheaves on the étale category of the ring

Let `A` be a noetherian ring and `X = Spec A`. For a presheaf `F` on the étale category `Et(X)`
of noetherian separated étale `X`-schemes, its restriction `F₀` to the étale category `Et(A)` of
étale `A`-algebras has `F₀(B) = F(Spec B)`, computed as the limit of `F(V)` over the morphisms
`V ⟶ Spec B` from objects `V` of `Et(X)`. We show that `F ↦ F₀` is an equivalence from étale
sheaves on `Et(X)` onto sheaves on `Et(A)`, for sheaves of sets, of abelian groups, and more
generally with values in any category with `u`-small limits.

For sheaves of sets, the sheaves on `Et(A)` are the presheaves satisfying the sheaf axioms
`AlgebraicGeometry.EtaleCategory.IsSheafAxioms`: finite products go to products (the empty
family included) and the equalizer condition holds for faithfully flat morphisms. The empty
family forces `G(0)` to be a point, so every such `G` has `G(0) ≠ ∅`.

The proof goes through Mathlib's small étale site `X_et`: `Et(X)` and the affine étale site are
both dense subsites of `X_et`, so a sheaf `H` on `X_et` is the right Kan extension of its
restriction to `Et(X)`, and the value `H(Spec B)` is therefore the limit defining
`(H|_{Et(X)})₀(B)`.

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.toEtaleSite`: the embedding of `Et(S)` into
  Mathlib's small étale site of `S`.
* `AlgebraicGeometry.affineRestriction.fromEtale`: for a presheaf `H` on `X_et`, the comparison
  `H(Spec B) ⟶ (H|_{Et(X)})₀(B)`.
* `AlgebraicGeometry.affineSheafEquiv`: the equivalence `Sh(Et(Spec A)) ≌ Sh(Et(A))`, whose
  functor is `F ↦ F₀` (`AlgebraicGeometry.affineSheafEquiv_functor_obj_obj`).

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.isRightKanExtension_sheaf`: a sheaf on the
  small étale site of a locally noetherian scheme is the right Kan extension of its restriction
  to `Et(S)`.
* `AlgebraicGeometry.affineRestriction.isIso_fromEtale_app`: the comparison is an isomorphism
  for sheaves.
* `AlgebraicGeometry.exists_iso_affineRestriction_iff_isSheafAxioms`: a presheaf of sets on
  `Et(A)` is isomorphic to some `F₀` if and only if it satisfies the sheaf axioms;
  `AlgebraicGeometry.exists_iso_affineRestriction_iff_isSheafAxioms_forget` is the same for
  abelian groups.
* `AlgebraicGeometry.EtaleCategory.IsSheafAxioms.nonempty_obj`: such a presheaf has
  `G(0) ≠ ∅`.

## Implementation notes

The source states the sheaf axioms on `Et(A)` with binary products, and the presheaf `G ≡ ∅`
satisfies them; the condition `G(0) ≠ ∅` in the statement excludes it. Here the sheaf axioms
include the empty family, which is the sheaf condition for the empty covering of the zero ring,
so the condition `G(0) ≠ ∅` is part of being a sheaf. For sheaves of abelian groups it is
automatic.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.2
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The embedding of `Et(S)` into Mathlib's small étale site of `S`. -/
abbrev toEtaleSite : SmallNoetherianSeparatedEtale B S hS ⥤ S.Etale :=
  inclusion B S hS ⋙ SmallEtale.toEtaleSite B S hS

lemma toEtaleSite_comp_forget :
    toEtaleSite B S hS ⋙ Scheme.Etale.forget S = toOver B S hS :=
  rfl

variable [IsLocallyNoetherian S]

instance isContinuous_toEtaleSite :
    (toEtaleSite B S hS).IsContinuous (topology B S hS) S.smallEtaleTopology :=
  haveI := SmallEtale.isContinuous_toEtaleSite B S hS
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS) _

instance isCocontinuous_toEtaleSite :
    (toEtaleSite B S hS).IsCocontinuous (topology B S hS) S.smallEtaleTopology :=
  haveI := SmallEtale.isCocontinuous_toEtaleSite B S hS
  isCocontinuous_comp (inclusion B S hS) (SmallEtale.toEtaleSite B S hS) (topology B S hS)
    (SmallEtale.topology B S hS)

variable (C : Type v) [Category.{w} C] [HasLimitsOfSize.{u, u} C]

instance hasLimitsOfShape_structuredArrow_toEtaleSite_op (X : S.Etaleᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (toEtaleSite B S hS).op) C :=
  hasLimitsOfShape_of_essentiallySmall _ _

/-- Restriction along `toEtaleSite` is the inverse of `sheafEquivEtale`. -/
def sheafPushforwardToEtaleSiteIso :
    (toEtaleSite B S hS).sheafPushforwardContinuous C (topology B S hS) S.smallEtaleTopology ≅
      (sheafEquivEtale B S hS C).inverse :=
  Iso.refl _

instance isEquivalence_sheafPushforwardContinuous_toEtaleSite :
    ((toEtaleSite B S hS).sheafPushforwardContinuous C (topology B S hS)
    S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_iso (sheafPushforwardToEtaleSiteIso B S hS C).symm

/-- A sheaf on the small étale site of `S` is the right Kan extension of its restriction to
`Et(S)`. -/
lemma isRightKanExtension_sheaf (H : Sheaf S.smallEtaleTopology C) :
    H.obj.IsRightKanExtension (𝟙 ((toEtaleSite B S hS).op ⋙ H.obj)) := by
  rw [← Functor.isIso_ranAdjunction_unit_app_iff,
    ← Functor.sheafAdjunctionCocontinuous_unit_app_hom (A := C) (J := topology B S hS)
      (K := S.smallEtaleTopology) (G := toEtaleSite B S hS)]
  exact (sheafToPresheaf S.smallEtaleTopology C).map_isIso
    (((toEtaleSite B S hS).sheafAdjunctionCocontinuous C (topology B S hS)
      S.smallEtaleTopology).unit.app H)

end SmallNoetherianSeparatedEtale

/-- **The sections over the zero ring are nonempty.** For a presheaf of sets on `Et(A)`
satisfying the sheaf axioms, condition (a) for the empty family says that `F(0)` is a point; in
particular `F(0) ≠ ∅`. -/
@[weil "lem_fk102_affine_sheaves_equivalence"]
lemma EtaleCategory.IsSheafAxioms.nonempty_obj {A : CommRingCat.{u}}
    {F : EtaleCategory A ⥤ Type w} (hF : EtaleCategory.IsSheafAxioms F) (Z : EtaleCategory A)
    [Subsingleton Z.ring] : Nonempty (F.obj Z) := by
  obtain ⟨s, -⟩ := (hF.bijective_pi (ι := Empty) (fun k ↦ k.elim) Z (fun k ↦ k.elim)
    ⟨fun a b _ ↦ Subsingleton.elim a b, fun _ ↦ ⟨0, funext fun k ↦ k.elim⟩⟩).2 (fun k ↦ k.elim)
  exact ⟨s⟩

namespace affineRestriction

open SmallNoetherianSeparatedEtale

variable {A : CommRingCat.{u}} (B : BigEtaleSite.{u}) (hS : B.Contains (Spec A))
  {C : Type v} [Category.{w} C] [HasLimitsOfSize.{u, u} C]

/-- The morphism `Spec B ⟶ Spec B'` of étale `Spec A`-schemes underlying a pair `(V, φ)`. -/
def etaleHom {X : EtaleCategory A} (j : affineRestrictionIndex B hS X) :
    (toEtaleSite B (Spec A) hS).obj j.right.unop ⟶ (Scheme.AffineEtale.Spec (Spec A)).obj X.unop :=
  (Scheme.Etale.forgetFullyFaithful (Spec A)).preimage j.hom.unop

lemma forget_map_etaleHom {X : EtaleCategory A} (j : affineRestrictionIndex B hS X) :
    (Scheme.Etale.forget (Spec A)).map (etaleHom B hS j) = j.hom.unop :=
  (Scheme.Etale.forgetFullyFaithful (Spec A)).map_preimage _

@[reassoc]
lemma map_etaleHom {X : EtaleCategory A} {j k : affineRestrictionIndex B hS X} (h : j ⟶ k) :
    (toEtaleSite B (Spec A) hS).map h.right.unop ≫ etaleHom B hS j = etaleHom B hS k := by
  apply (Scheme.Etale.forgetFullyFaithful (Spec A)).map_injective
  rw [Functor.map_comp, forget_map_etaleHom, forget_map_etaleHom]
  have := congrArg Quiver.Hom.unop (StructuredArrow.w h)
  exact this

lemma etaleHom_map {X Y : EtaleCategory A} (g : X ⟶ Y) (j : affineRestrictionIndex B hS Y) :
    etaleHom B hS ((StructuredArrow.map ((EtaleCategory.toOver A).map g)).obj j) =
      etaleHom B hS j ≫ (Scheme.AffineEtale.Spec (Spec A)).map g.unop := by
  apply (Scheme.Etale.forgetFullyFaithful (Spec A)).map_injective
  rw [Functor.map_comp, forget_map_etaleHom, forget_map_etaleHom]
  rfl

/-- The canonical comparison `H(Spec B) ⟶ (H|_{Et(X)})₀(B)` for a presheaf `H` on the small étale
site of `X = Spec A`, sending a section `s` to the family `(φ^* s)_{(V, φ)}`. -/
def fromEtale (H : (Spec A).Etaleᵒᵖ ⥤ C) :
    (Scheme.AffineEtale.Spec (Spec A)).op ⋙ H ⟶
      affineRestriction B hS ((toEtaleSite B (Spec A) hS).op ⋙ H) where
  app X := limit.lift (StructuredArrow.proj ((EtaleCategory.toOver A).obj X)
      (toOver B (Spec A) hS).op ⋙ (toEtaleSite B (Spec A) hS).op ⋙ H)
    { pt := H.obj (op ((Scheme.AffineEtale.Spec (Spec A)).obj X.unop))
      π :=
        { app j := H.map (etaleHom B hS j).op
          naturality j k h := by
            refine (Category.id_comp _).trans ?_
            rw [← map_etaleHom B hS h, op_comp, H.map_comp]
            rfl } }
  naturality X Y g := by
    refine affineRestriction.hom_ext ((toEtaleSite B (Spec A) hS).op ⋙ H) fun j ↦ ?_
    erw [Category.assoc, Category.assoc, map_π, limit.lift_π, limit.lift_π]
    dsimp
    rw [← H.map_comp, ← op_comp, etaleHom_map]

@[reassoc]
lemma fromEtale_app_π (H : (Spec A).Etaleᵒᵖ ⥤ C) (X : EtaleCategory A)
    (j : affineRestrictionIndex B hS X) :
    (fromEtale B hS H).app X ≫ π ((toEtaleSite B (Spec A) hS).op ⋙ H) X j =
      H.map (etaleHom B hS j).op :=
  limit.lift_π _ _

variable [IsNoetherianRing A]

set_option linter.style.haveILetI false in
/-- For a sheaf `H` on the small étale site of `X = Spec A`, the comparison
`H(Spec B) ⟶ (H|_{Et(X)})₀(B)` is an isomorphism. -/
lemma isIso_fromEtale_app (H : Sheaf (Spec A).smallEtaleTopology C) (X : EtaleCategory A) :
    IsIso ((fromEtale B hS H.obj).app X) := by
  have := isRightKanExtension_sheaf B (Spec A) hS C H
  let W : (Spec A).Etaleᵒᵖ := op ((Scheme.AffineEtale.Spec (Spec A)).obj X.unop)
  have hW := Functor.isPointwiseRightKanExtensionOfIsRightKanExtension
    (L := (toEtaleSite B (Spec A) hS).op) (F := (toEtaleSite B (Spec A) hS).op ⋙ H.obj)
    H.obj (𝟙 _) W
  let P : StructuredArrow W (toEtaleSite B (Spec A) hS).op ⥤
      StructuredArrow ((EtaleCategory.toOver A).obj X) (toOver B (Spec A) hS).op :=
    StructuredArrow.post W (toEtaleSite B (Spec A) hS).op
    (Scheme.Etale.forget (Spec A)).op
  let G : StructuredArrow ((EtaleCategory.toOver A).obj X) (toOver B (Spec A) hS).op ⥤ C :=
    StructuredArrow.proj ((EtaleCategory.toOver A).obj X) (toOver B (Spec A) hS).op ⋙
      (toEtaleSite B (Spec A) hS).op ⋙ H.obj
  haveI : (Scheme.Etale.forget (Spec A)).Full := (Scheme.Etale.forgetFullyFaithful _).full
  haveI : (Scheme.Etale.forget (Spec A)).Faithful := (Scheme.Etale.forgetFullyFaithful _).faithful
  haveI : P.IsEquivalence := StructuredArrow.isEquivalence_post _ _ _
  haveI : P.Initial := inferInstance
  haveI hpre : IsIso (limit.pre G P) := Functor.Initial.limit_pre_isIso P
  have key : (fromEtale B hS H.obj).app X ≫ limit.pre G P =
      (hW.conePointUniqueUpToIso (limit.isLimit _)).hom := by
    refine limit.hom_ext fun g ↦ ?_
    erw [IsLimit.conePointUniqueUpToIso_hom_comp, Category.assoc, limit.pre_π]
    erw [fromEtale_app_π]
    dsimp [Functor.RightExtension.coneAt]
    rw [Category.comp_id]
    congr 2
  have hcomp : IsIso ((fromEtale B hS H.obj).app X ≫ limit.pre G P) := by
    rw [key]; exact Iso.isIso_hom _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hpre hcomp

omit [IsNoetherianRing A] in
@[reassoc]
lemma fromEtale_naturality {H H' : (Spec A).Etaleᵒᵖ ⥤ C} (α : H ⟶ H') :
    fromEtale B hS H ≫ map (Functor.whiskerLeft (toEtaleSite B (Spec A) hS).op α) =
      Functor.whiskerLeft (Scheme.AffineEtale.Spec (Spec A)).op α ≫ fromEtale B hS H' := by
  ext X : 2
  refine affineRestriction.hom_ext ((toEtaleSite B (Spec A) hS).op ⋙ H') fun j ↦ ?_
  simp only [NatTrans.comp_app, Category.assoc, map_app_π]
  erw [fromEtale_app_π_assoc, fromEtale_app_π]
  exact α.naturality _

variable (C) in
/-- **Sheaves on the small étale site restrict to `Et(A)` as on `Et(X)`.** For a sheaf `H` on
the small étale site of `X = Spec A`, the values `H(Spec B)` are naturally the values at `B` of
the restriction `F₀` of `F = H|_{Et(X)}`. -/
def fromEtaleIso :
    sheafToPresheaf (Spec A).smallEtaleTopology C ⋙
        (Functor.whiskeringLeft _ _ C).obj (Scheme.AffineEtale.Spec (Spec A)).op ≅
      (toEtaleSite B (Spec A) hS).sheafPushforwardContinuous C (topology B (Spec A) hS)
          (Spec A).smallEtaleTopology ⋙
        sheafToPresheaf (topology B (Spec A) hS) C ⋙ affineRestrictionFunctor B hS C :=
  NatIso.ofComponents
    (fun H ↦ @asIso _ _ _ _ (fromEtale B hS H.obj)
      (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ (fromEtale B hS H.obj) (isIso_fromEtale_app B hS H)))
    (fun α ↦ (fromEtale_naturality B hS α.hom).symm)

end affineRestriction

open SmallNoetherianSeparatedEtale affineRestriction

instance Scheme.AffineEtale.hasLimitsOfShape_structuredArrow_spec_op {S : Scheme.{u}}
    (C : Type v) [Category.{w} C] [HasLimitsOfSize.{u, u} C] (X : S.Etaleᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (Scheme.AffineEtale.Spec S).op) C :=
  hasLimitsOfShape_of_essentiallySmall _ _

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (B : BigEtaleSite.{u})
  (hS : B.Contains (Spec A)) (C : Type v) [Category.{w} C] [HasLimitsOfSize.{u, u} C]

/-- The composite of the comparison equivalences `Sh(Et(X)) ≌ Sh(X_et)` and
`Sh(X_et) ≌ Sh(Et(A))`, before its functor is identified with `F ↦ F₀`. -/
def affineSheafEquivAux :
    EtaleSheaf B (Spec A) hS C ≌ Sheaf (Scheme.AffineEtale.topology (Spec A)) C :=
  (sheafEquivEtale B (Spec A) hS C).trans
    (Functor.IsDenseSubsite.sheafEquiv (Scheme.AffineEtale.topology (Spec A))
      (Spec A).smallEtaleTopology (Scheme.AffineEtale.Spec (Spec A)) C).symm

/-- The functor of `affineSheafEquivAux` is `F ↦ F₀` on underlying presheaves. -/
def affineSheafEquivAuxFunctorIso :
    (affineSheafEquivAux B hS C).functor ⋙ sheafToPresheaf _ C ≅
      sheafToPresheaf (topology B (Spec A) hS) C ⋙ affineRestrictionFunctor B hS C :=
  Functor.isoWhiskerLeft (sheafEquivEtale B (Spec A) hS C).functor (fromEtaleIso B hS C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafEquivEtale B (Spec A) hS C).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- The functor `F ↦ F₀` from étale sheaves on `Et(Spec A)` to sheaves on `Et(A)`. -/
def affineSheafFunctor :
    EtaleSheaf B (Spec A) hS C ⥤ Sheaf (Scheme.AffineEtale.topology (Spec A)) C :=
  ObjectProperty.lift _ (sheafToPresheaf _ C ⋙ affineRestrictionFunctor B hS C) fun F ↦
    (Presheaf.isSheaf_of_iso_iff ((affineSheafEquivAuxFunctorIso B hS C).app F)).1
      ((affineSheafEquivAux B hS C).functor.obj F).property

/-- **Sheaves on `Et(Spec A)` are sheaves on `Et(A)`.** For a noetherian ring `A`, the
restriction `F ↦ F₀` is an equivalence from étale sheaves on `Et(Spec A)` to sheaves on the
étale category `Et(A)`, with values in any category with `u`-small limits. -/
@[weil "lem_fk102_affine_sheaves_equivalence"]
def affineSheafEquiv :
    EtaleSheaf B (Spec A) hS C ≌ Sheaf (Scheme.AffineEtale.topology (Spec A)) C :=
  (affineSheafEquivAux B hS C).changeFunctor
    (Functor.fullyFaithfulCancelRight (G := affineSheafFunctor B hS C) (sheafToPresheaf _ C)
      (affineSheafEquivAuxFunctorIso B hS C))

/-- The functor of `affineSheafEquiv` is the restriction `F ↦ F₀`. -/
@[weil "lem_fk102_affine_sheaves_equivalence", simp]
lemma affineSheafEquiv_functor_obj_obj (F : EtaleSheaf B (Spec A) hS C) :
    ((affineSheafEquiv B hS C).functor.obj F).obj = affineRestriction B hS F.obj :=
  rfl

/-- The functor of `affineSheafEquiv` acts on morphisms by `α ↦ α₀`. -/
@[simp]
lemma affineSheafEquiv_functor_map_hom {F G : EtaleSheaf B (Spec A) hS C} (α : F ⟶ G) :
    ((affineSheafEquiv B hS C).functor.map α).hom = affineRestriction.map α.hom :=
  rfl

/-- **The essential image of `F ↦ F₀`**: a presheaf on `Et(A)` is isomorphic to the
restriction `F₀` of an étale sheaf `F` on `Et(Spec A)` if and only if it is a sheaf. -/
theorem exists_iso_affineRestriction_iff_isSheaf (G : EtaleCategory A ⥤ C) :
    (∃ F : EtaleSheaf B (Spec A) hS C, Nonempty (affineRestriction B hS F.obj ≅ G)) ↔
      Presheaf.IsSheaf (Scheme.AffineEtale.topology (Spec A)) G := by
  constructor
  · rintro ⟨F, ⟨e⟩⟩
    exact (Presheaf.isSheaf_of_iso_iff e).1 ((affineSheafEquiv B hS C).functor.obj F).property
  · intro hG
    refine ⟨(affineSheafEquiv B hS C).inverse.obj ⟨G, hG⟩,
      ⟨(sheafToPresheaf _ C).mapIso ((affineSheafEquiv B hS C).counitIso.app ⟨G, hG⟩)⟩⟩

/-- **The essential image of `F ↦ F₀` on sheaves of abelian groups**: a presheaf of abelian
groups on `Et(A)` is isomorphic to `F₀` for an étale sheaf `F` on `Et(Spec A)` if and only if
its underlying presheaf of sets satisfies the sheaf axioms. -/
@[weil "lem_fk102_affine_sheaves_equivalence"]
theorem exists_iso_affineRestriction_iff_isSheafAxioms_forget [UnivLE.{u, v}]
    (G : EtaleCategory A ⥤ AddCommGrpCat.{v}) :
    (∃ F : EtaleSheaf B (Spec A) hS AddCommGrpCat.{v},
        Nonempty (affineRestriction B hS F.obj ≅ G)) ↔
      EtaleCategory.IsSheafAxioms (G ⋙ forget AddCommGrpCat) := by
  rw [exists_iso_affineRestriction_iff_isSheaf, EtaleCategory.isSheaf_iff_isSheafAxioms_forget]

section Types

variable [UnivLE.{u, v}]

/-- The restriction `F₀` of an étale sheaf of sets on `Et(Spec A)` satisfies the sheaf axioms
on `Et(A)`. -/
theorem isSheafAxioms_affineRestriction (F : EtaleSheaf B (Spec A) hS (Type v)) :
    EtaleCategory.IsSheafAxioms (affineRestriction B hS F.obj) :=
  (EtaleCategory.isSheaf_iff_isSheafAxioms _).1
    ((affineSheafEquiv B hS (Type v)).functor.obj F).property

/-- **The essential image of `F ↦ F₀` on sheaves of sets**: a presheaf of sets on `Et(A)` is
isomorphic to `F₀` for an étale sheaf `F` on `Et(Spec A)` if and only if it satisfies the sheaf
axioms. -/
@[weil "lem_fk102_affine_sheaves_equivalence"]
theorem exists_iso_affineRestriction_iff_isSheafAxioms (G : EtaleCategory A ⥤ Type v) :
    (∃ F : EtaleSheaf B (Spec A) hS (Type v), Nonempty (affineRestriction B hS F.obj ≅ G)) ↔
      EtaleCategory.IsSheafAxioms G := by
  rw [exists_iso_affineRestriction_iff_isSheaf, EtaleCategory.isSheaf_iff_isSheafAxioms]

end Types

end AlgebraicGeometry
