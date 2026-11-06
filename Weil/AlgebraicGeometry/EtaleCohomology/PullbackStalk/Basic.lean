module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.InverseImage
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import Weil.Attr
public import Weil.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic

/-!
# The inverse image of a sheaf with open difference loci

Let `f : T ⟶ S` be a morphism of schemes of a big étale site and `G` an étale sheaf of sets on
`S` with open difference loci. Then the inverse image `f^* G` has open difference loci.

Let `σ ρ ∈ (f^* G)(V)` and let `v ∈ V` be a point over which some geometric point `v̄` sees
different germs of `σ` and `ρ`. The stalk of `f^* G` at `v̄` is the stalk of `G` at the image
geometric point, so on a small enough étale neighbourhood `q : V' ⟶ V` of `v̄` both `σ` and `ρ`
are pulled back from sections `t₁ t₂ ∈ G(W)` along a map `h : V' ⟶ W ×_S T`. The coincidence
set of the two pulled back sections is the preimage of the coincidence set `C(t₁, t₂)` under the
composite `φ : V' ⟶ W`, so its complement is open in `V'`; its image under the étale, hence
open, map `q` is an open neighbourhood of `v` on which the germs of `σ` and `ρ` differ.

## Main results

* `AlgebraicGeometry.SmallEtale.germCoincidenceSet_map_pullbackSectionAlong`: the coincidence
  set of two sections of `f^* G` pulled back from `G` is the preimage of the coincidence set of
  the original sections.
* `AlgebraicGeometry.SmallEtale.HasOpenDifferenceLoci.inverseImage`: the inverse image of a
  sheaf with open difference loci has open difference loci.

## Implementation notes

The sheaves take values in `Type (u + 1)`, the coefficient universe of the comparison of stalks
under inverse image `AlgebraicGeometry.smallEtalePullbackStalkIso`. The inverse image is the
left adjoint of the direct image, `AlgebraicGeometry.smallEtaleInverseImage`; sections pulled
back from `G` are `AlgebraicGeometry.pullbackSectionAlong`, the adjunction unit followed by a
restriction, rather than classes in the presheaf inverse image.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.SmallEtale

section Germs

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}
variable (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type v) [UnivLE.{u, v}]

/-- Equality of the images of two sections in the stalk depends on the geometric point and the
lift only up to equality. -/
lemma toPresheafFiber_eq_iff_of_heq {U : SmallEtale B X hX} {y y' : GeometricPoint X}
    (e : y' = y) {w' : (geometricPointFiber B X hX y').obj U}
    {w : (geometricPointFiber B X hX y).obj U} (hw : HEq w' w) (a b : F.obj (op U)) :
    (geometricPointSitePoint B X hX y').toPresheafFiber U w' F a =
        (geometricPointSitePoint B X hX y').toPresheafFiber U w' F b ↔
      (geometricPointSitePoint B X hX y).toPresheafFiber U w F a =
        (geometricPointSitePoint B X hX y).toPresheafFiber U w F b := by
  subst e
  cases hw
  exact Iff.rfl

/-- Equality of germs at the geometric point defined by a lift `w` of a geometric point `y` of
`X` to `U` is equality in the stalk at `y` of the images from the term indexed by `(U, w)`. -/
lemma germ_eq_germ_iff_toPresheafFiber {U : SmallEtale B X hX} {y : GeometricPoint X}
    (w : (geometricPointFiber B X hX y).obj U) (a b : F.obj (op U)) :
    germ F a { residueField := y.residueField, hom := w.1 } =
        germ F b { residueField := y.residueField, hom := w.1 } ↔
      (geometricPointSitePoint B X hX y).toPresheafFiber U w F a =
        (geometricPointSitePoint B X hX y).toPresheafFiber U w F b := by
  refine toPresheafFiber_eq_iff_of_heq F ?_ ?_ a b
  · cases y with
    | mk k hom => exact congrArg (fun h ↦ (GeometricPoint.mk k h : GeometricPoint X)) w.2
  · refine (Subtype.heq_iff_coe_eq fun z ↦ ?_).2 rfl
    change z ≫ _ = w.1 ≫ _ ↔ z ≫ _ = y.hom
    rw [w.2]

/-- The germs of two restricted sections at a geometric point `ū` agree if and only if the
germs of the sections agree at the image of `ū`. -/
lemma germ_map_eq_germ_map_iff {U U' : SmallEtale B X hX} (g : U' ⟶ U)
    (ū : GeometricPoint ((SmallEtale.toScheme B X hX).obj U')) (a b : F.obj (op U)) :
    germ F (F.map g.op a) ū = germ F (F.map g.op b) ū ↔
      germ F a (ū.map ((SmallEtale.toScheme B X hX).map g)) =
        germ F b (ū.map ((SmallEtale.toScheme B X hX).map g)) := by
  have ha := (geometricPointSitePoint B X hX (toBaseGeometricPoint U' ū)).toPresheafFiber_w_apply
    g (geometricPointLift U' ū) F a
  have hb := (geometricPointSitePoint B X hX (toBaseGeometricPoint U' ū)).toPresheafFiber_w_apply
    g (geometricPointLift U' ū) F b
  refine Iff.trans ?_ (germ_eq_germ_iff_toPresheafFiber F
    ((geometricPointFiber B X hX (toBaseGeometricPoint U' ū)).map g
      (geometricPointLift U' ū)) a b).symm
  exact ⟨fun h ↦ ha.symm.trans (h.trans hb), fun h ↦ ha.trans (h.trans hb.symm)⟩

end Germs

section InverseImage

variable {B : BigEtaleSite.{u}} {S T : B.Scheme} (f : T ⟶ S)
variable (G : Sheaf (SmallEtale.topology B S.1 S.property) (Type (u + 1)))

/-- The stalk comparison for the inverse image sends the germ of a section pulled back to the
base change `W ×_S T` to the germ of the original section. -/
lemma smallEtalePullbackStalkIso_hom_toPresheafFiber (x : GeometricPoint T.1)
    (W : SmallEtale B S.1 S.property)
    (l : (geometricPointFiber B T.1 T.property x).obj ((smallEtaleBaseChange B f).obj W))
    (t : G.obj.obj (op W)) :
    ((smallEtalePullbackStalkIso B f x).hom.app G)
        ((geometricPointSitePoint B T.1 T.property x).toPresheafFiber _ l
          ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
          (pullbackSectionAlong B f G W _ (𝟙 _) t)) =
      (geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))).toPresheafFiber W
        ((geometricPointFiberBaseChangeEquiv B f x W).symm l) G.obj t := by
  refine smallEtalePullbackStalkIso_germ B f x G ⟨_, l⟩ ⟨W, _⟩ (𝟙 _) ?_ t
  dsimp only
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The composite `U ⟶ W ×_S T ⟶ W` of a map to the base change of `W` with the first
projection, a morphism of the underlying schemes. -/
abbrev baseChangeFstComp {W : SmallEtale B S.1 S.property} {U : SmallEtale B T.1 T.property}
    (h : U ⟶ (smallEtaleBaseChange B f).obj W) :
    (SmallEtale.toScheme B T.1 T.property).obj U ⟶ (SmallEtale.toScheme B S.1 S.property).obj W :=
  (SmallEtale.toScheme B T.1 T.property).map h ≫ B.inclusion.map (pullback.fst W.obj.hom f)

/-- The germs of two sections of `f^* G` pulled back from `t₁ t₂ ∈ G(W)` along `h : U ⟶ W ×_S T`
agree at a geometric point `wb` of `U` if and only if the germs of `t₁` and `t₂` agree at the
image of `wb` in `W`. -/
lemma germ_map_pullbackSectionAlong_eq_iff (W : SmallEtale B S.1 S.property)
    {U : SmallEtale B T.1 T.property} (h : U ⟶ (smallEtaleBaseChange B f).obj W)
    (t₁ t₂ : G.obj.obj (op W))
    (wb : GeometricPoint ((SmallEtale.toScheme B T.1 T.property).obj U)) :
    germ ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
        (((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj.map h.op
          (pullbackSectionAlong B f G W _ (𝟙 _) t₁)) wb =
      germ ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
        (((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj.map h.op
          (pullbackSectionAlong B f G W _ (𝟙 _) t₂)) wb ↔
      germ G.obj t₁ (wb.map (baseChangeFstComp f h)) =
        germ G.obj t₂ (wb.map (baseChangeFstComp f h)) := by
  let x := toBaseGeometricPoint U wb
  let Φ := geometricPointSitePoint B T.1 T.property x
  let l := (geometricPointFiber B T.1 T.property x).map h (geometricPointLift U wb)
  have ha := Φ.toPresheafFiber_w_apply h (geometricPointLift U wb)
    ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
    (pullbackSectionAlong B f G W _ (𝟙 _) t₁)
  have hb := Φ.toPresheafFiber_w_apply h (geometricPointLift U wb)
    ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
    (pullbackSectionAlong B f G W _ (𝟙 _) t₂)
  have hinj : Function.Injective ((smallEtalePullbackStalkIso B f x).hom.app G) :=
    (mono_iff_injective _).1 inferInstance
  have hl : ((geometricPointFiberBaseChangeEquiv B f x W).symm l).1 =
      wb.hom ≫ baseChangeFstComp f h := by
    change (wb.hom ≫ _) ≫ eqToHom _ ≫ _ = _
    simp only [baseChangeFstComp, Category.assoc]
    erw [eqToHom_refl, Category.id_comp]
    rfl
  calc _ ↔ Φ.toPresheafFiber _ l ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
          (pullbackSectionAlong B f G W _ (𝟙 _) t₁) =
        Φ.toPresheafFiber _ l ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
          (pullbackSectionAlong B f G W _ (𝟙 _) t₂) :=
        ⟨fun h ↦ ha.symm.trans (h.trans hb), fun h ↦ ha.trans (h.trans hb.symm)⟩
    _ ↔ _ := hinj.eq_iff.symm
    _ ↔ (geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))).toPresheafFiber W
          ((geometricPointFiberBaseChangeEquiv B f x W).symm l) G.obj t₁ =
        (geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))).toPresheafFiber W
          ((geometricPointFiberBaseChangeEquiv B f x W).symm l) G.obj t₂ := by
        rw [smallEtalePullbackStalkIso_hom_toPresheafFiber,
          smallEtalePullbackStalkIso_hom_toPresheafFiber]
        exact Iff.rfl
    _ ↔ _ := (germ_eq_germ_iff_toPresheafFiber G.obj _ t₁ t₂).symm
    _ ↔ _ := by
        rw [hl]
        exact Iff.rfl

/-- The coincidence set of two sections of `f^* G` pulled back from `t₁ t₂ ∈ G(W)` along
`h : U ⟶ W ×_S T` is the preimage of the coincidence set `C(t₁, t₂)` under `U ⟶ W`. -/
theorem germCoincidenceSet_map_pullbackSectionAlong (W : SmallEtale B S.1 S.property)
    {U : SmallEtale B T.1 T.property} (h : U ⟶ (smallEtaleBaseChange B f).obj W)
    (t₁ t₂ : G.obj.obj (op W)) :
    germCoincidenceSet ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
        (((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj.map h.op
          (pullbackSectionAlong B f G W _ (𝟙 _) t₁))
        (((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj.map h.op
          (pullbackSectionAlong B f G W _ (𝟙 _) t₂)) =
      baseChangeFstComp f h ⁻¹' germCoincidenceSet G.obj t₁ t₂ := by
  ext w
  simp only [Set.mem_preimage]
  constructor
  · intro hw
    have hwb := hw _ (GeometricPoint.ofPoint_liesOver _ w)
    rw [germ_map_pullbackSectionAlong_eq_iff] at hwb
    obtain ⟨O, -, hO, hOC⟩ := exists_isOpen_mem_subset_germCoincidenceSet G.obj t₁ t₂ _
      (by
        change ((GeometricPoint.ofPoint _ w).hom ≫ baseChangeFstComp f h) default = _
        rw [Scheme.Hom.comp_apply, GeometricPoint.ofPoint_liesOver _ w]) hwb
    exact hOC hO
  · intro hw wb hwb
    rw [germ_map_pullbackSectionAlong_eq_iff]
    refine hw _ ?_
    change (wb.hom ≫ baseChangeFstComp f h) default = _
    rw [Scheme.Hom.comp_apply, hwb]

/-- **The inverse image of a sheaf with open difference loci has open difference loci.** Let
`f : T ⟶ S` be a morphism of schemes of a big étale site and `G` an étale sheaf of sets on `S`
with open difference loci. Then `f^* G` has open difference loci. -/
@[weil "lem_fk103_open_difference_loci_restrict_etale"]
theorem HasOpenDifferenceLoci.inverseImage (hG : HasOpenDifferenceLoci G.obj) :
    HasOpenDifferenceLoci ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj := by
  intro V σ ρ
  rw [isOpen_iff_forall_mem_open]
  intro v hv
  have hv' : ¬ ∀ vb : GeometricPoint ((SmallEtale.toScheme B T.1 T.property).obj V),
      vb.LiesOver v → germ _ σ vb = germ _ ρ vb := hv
  push Not at hv'
  obtain ⟨vb, hvb, hne⟩ := hv'
  let x := toBaseGeometricPoint V vb
  let Φ := geometricPointSitePoint B T.1 T.property x
  let Ψ := geometricPointSitePoint B S.1 S.property (x.map (B.inclusion.map f))
  have hinj : Function.Injective ((smallEtalePullbackStalkIso B f x).hom.app G) :=
    (mono_iff_injective _).1 inferInstance
  obtain ⟨W, w, t₁, t₂, h₁, h₂⟩ := Ψ.toPresheafFiber_jointly_surjective₂ (P := G.obj)
    ((smallEtalePullbackStalkIso B f x).hom.app G (germ _ σ vb))
    ((smallEtalePullbackStalkIso B f x).hom.app G (germ _ ρ vb))
  let l := geometricPointFiberBaseChangeEquiv B f x W w
  have hl : (geometricPointFiberBaseChangeEquiv B f x W).symm l = w := Equiv.symm_apply_apply _ _
  have k₁ : Φ.toPresheafFiber _ l ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
      (pullbackSectionAlong B f G W _ (𝟙 _) t₁) = germ _ σ vb := hinj (by
    rw [smallEtalePullbackStalkIso_hom_toPresheafFiber, hl]
    exact h₁)
  have k₂ : Φ.toPresheafFiber _ l ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
      (pullbackSectionAlong B f G W _ (𝟙 _) t₂) = germ _ ρ vb := hinj (by
    rw [smallEtalePullbackStalkIso_hom_toPresheafFiber, hl]
    exact h₂)
  let E₁ : Φ.fiber.Elements := ⟨V, geometricPointLift V vb⟩
  let E₂ : Φ.fiber.Elements := ⟨(smallEtaleBaseChange B f).obj W, l⟩
  let gL := IsCofiltered.minToLeft E₁ E₂
  let gR := IsCofiltered.minToRight E₁ E₂
  let E := IsCofiltered.min E₁ E₂
  let F' := ((smallEtaleInverseImage B f (Type (u + 1))).obj G).obj
  have e₁ : Φ.toPresheafFiber E.1 E.2 F' (F'.map gL.1.op σ) =
      Φ.toPresheafFiber E.1 E.2 F' (F'.map gR.1.op (pullbackSectionAlong B f G W _ (𝟙 _) t₁)) := by
    rw [Φ.toPresheafFiber_w_apply, Φ.toPresheafFiber_w_apply, gL.2, gR.2]
    exact k₁.symm
  obtain ⟨V₁, g₁, y₁, hy₁, heq₁⟩ := (Φ.toPresheafFiber_eq_iff' E.1 E.2 _ _).1 e₁
  have e₂ : Φ.toPresheafFiber V₁ y₁ F' (F'.map g₁.op (F'.map gL.1.op ρ)) =
      Φ.toPresheafFiber V₁ y₁ F'
        (F'.map g₁.op (F'.map gR.1.op (pullbackSectionAlong B f G W _ (𝟙 _) t₂))) := by
    simp only [GrothendieckTopology.Point.toPresheafFiber_w_apply, hy₁]
    rw [gL.2, gR.2]
    exact k₂.symm
  obtain ⟨V₂, g₂, y₂, hy₂, heq₂⟩ := (Φ.toPresheafFiber_eq_iff' V₁ y₁ _ _).1 e₂
  let q : V₂ ⟶ V := g₂ ≫ g₁ ≫ gL.1
  let h : V₂ ⟶ (smallEtaleBaseChange B f).obj W := g₂ ≫ g₁ ≫ gR.1
  have hσ : F'.map q.op σ = F'.map h.op (pullbackSectionAlong B f G W _ (𝟙 _) t₁) := by
    simp only [q, h, op_comp, CategoryTheory.Functor.map_comp_apply]
    rw [heq₁]
  have hρ : F'.map q.op ρ = F'.map h.op (pullbackSectionAlong B f G W _ (𝟙 _) t₂) := by
    simp only [q, h, op_comp, CategoryTheory.Functor.map_comp_apply]
    exact heq₂
  have hq : Φ.fiber.map q y₂ = geometricPointLift V vb := by
    simp only [q, CategoryTheory.Functor.map_comp_apply]
    rw [hy₂, hy₁]
    exact gL.2
  let g := (SmallEtale.toScheme B T.1 T.property).map q
  have : Etale g := _root_.AlgebraicGeometry.SmallEtale.etale_toScheme_map q
  have : UniversallyOpen g := UniversallyOpen.of_flat g
  have hC : germCoincidenceSet F' (F'.map q.op σ) (F'.map q.op ρ) =
      baseChangeFstComp f h ⁻¹' germCoincidenceSet G.obj t₁ t₂ := by
    rw [hσ, hρ]
    exact germCoincidenceSet_map_pullbackSectionAlong f G W h t₁ t₂
  have hO' : IsOpen (germCoincidenceSet F' (F'.map q.op σ) (F'.map q.op ρ))ᶜ := by
    rw [hC, ← Set.preimage_compl]
    exact (hG W t₁ t₂).preimage (baseChangeFstComp f h).continuous
  refine ⟨g '' (germCoincidenceSet F' (F'.map q.op σ) (F'.map q.op ρ))ᶜ, ?_,
    g.isOpenMap _ hO', y₂.1 default, ?_, ?_⟩
  · rintro _ ⟨w', hw', rfl⟩ hmem
    apply hw'
    intro wb hwb
    refine (germ_map_eq_germ_map_iff F' q wb σ ρ).2 (hmem _ ?_)
    change (wb.hom ≫ g) default = _
    rw [Scheme.Hom.comp_apply, hwb]
  · intro hmem
    apply hne
    have h' := (germ_eq_germ_iff_toPresheafFiber F' (y := x) y₂ _ _).1
      (hmem { residueField := x.residueField, hom := y₂.1 } rfl)
    rw [Φ.toPresheafFiber_w_apply, Φ.toPresheafFiber_w_apply, hq] at h'
    exact h'
  · have h' : y₂.1 ≫ g = vb.hom := congrArg Subtype.val hq
    rw [← Scheme.Hom.comp_apply, h']
    exact hvb

end InverseImage

end AlgebraicGeometry.SmallEtale

end

/-! ### The canonical stalk map of an inverse image is bijective -/

/-!
# The canonical stalk map of an inverse image is bijective

Let `p : P ⟶ Q` be a morphism in a big étale site, `w` a geometric point of `P` and `F` a sheaf
of sets on the small étale site of `Q`. The canonical map `c_w : F_{p ∘ w} ⟶ (p^* F)_w`
(`AlgebraicGeometry.inverseImageStalkMap`) is bijective: it is the inverse of the identification
of stalks of inverse images of Stacks, Tag 03Q1.

## Main results

* `AlgebraicGeometry.inverseImageStalkMap_bijective`: `c_w` is bijective.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.3][FK]
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- **The canonical stalk map is bijective.** For a morphism `p : P ⟶ Q` in a big étale site, a
geometric point `w` of `P` and a sheaf of sets `F` on the small étale site of `Q`, the map
`c_w : F_{p ∘ w} ⟶ (p^* F)_w` is bijective. -/
@[weil "lem_fk103_inverse_image_stalk_map_bijective"]
theorem inverseImageStalkMap_bijective (B : BigEtaleSite.{u}) {P Q : B.Scheme} (p : P ⟶ Q)
    (w : GeometricPoint P.1)
    (F : Sheaf (SmallEtale.topology B Q.1 Q.property) (Type (max (u + 1) v))) :
    Function.Bijective (inverseImageStalkMap.{u, v} B p w F) := by
  rw [inverseImageStalkMap_eq_inv_app]
  exact (isIso_iff_bijective _).mp inferInstance

end AlgebraicGeometry

end
