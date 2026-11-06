module

public import Weil.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Weil.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Weil.Attr

/-!
# A quotient of a representable étale sheaf is the cokernel of an étale equivalence relation

Let `B` be a big étale site containing a scheme `X`, let `Y` be an object of the small étale
site of `X` and let `φ : h_Y ⟶ F` be an epimorphism of étale sheaves of sets. Then there are
an object `R` of the small étale site and two `X`-morphisms `u v : R ⟶ Y` such that
`h_u, h_v : h_R ⇉ h_Y` represent an equivalence relation (sectionwise injective, with image
an equivalence relation on every set of sections), and `φ` is a cokernel (coequalizer) of
`h_u` and `h_v`.

The proof follows Freitag–Kiehl. The kernel pair `K = h_Y ×_F h_Y` is a subsheaf of the
representable sheaf `h_{Y ×_X Y}`. A subsheaf `G` of a representable sheaf `h_Z` is
represented by an open subscheme of `Z`: the union `W` of the images of the étale morphisms
`U ⟶ Z` which are sections of `G`. Indeed a morphism `t : U ⟶ Z` with image in `W` lies in
`G` étale locally on `U` (over the fibre products `U ×_Z U'` with `U' ⟶ Z` a section of `G`),
hence lies in `G` because `G` is a sheaf. Writing `j : R ⟶ Y ×_X Y` for that open subscheme
and `u, v` for its two projections, the image of `h_R(U) ⟶ h_Y(U)²` is the relation
`φ(a) = φ(b)`, which is an equivalence relation, and an epimorphism of sheaves of sets is the
coequalizer of its kernel pair.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_mono_forall_exists_comp_eq_iff`: a subsheaf of a
  representable sheaf `h_Z` is represented by a subobject `R ⟶ Z` (an open subscheme of `Z`).
* `AlgebraicGeometry.SmallEtale.exists_isEquivalenceRelation_isColimit_cofork`: an
  epimorphism `h_Y ⟶ F` is the cokernel of a pair `h_u, h_v : h_R ⇉ h_Y` representing an
  equivalence relation.

## Implementation notes

The cokernel of a pair of morphisms of sheaves is stated through the universal property, as
`IsColimit (Cofork.ofπ φ _)`: `φ` exhibits `F` as the coequalizer of `h_u` and `h_v` in the
category of étale sheaves of sets. This is FK's `F ≅ Coker(h_u, h_v)`, together with the
compatibility of the isomorphism with `φ`. The equivalence relation is stated in its
sectionwise form: injectivity of `r ↦ (h_u(r), h_v(r))` and the relation it induces on the
sections of `h_Y` being an equivalence relation.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.4
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The `X`-morphism `U ⟶ Z` of the small étale site corresponding to a section of a sheaf
mapping to `h_Z`. -/
noncomputable def representableSectionHom {Z : SmallEtale B X hX}
    {G : Sheaf (topology B X hX) (Type u)}
    (m : G ⟶ (representableSheaf B X hX).obj Z) {U : SmallEtale B X hX}
    (s : G.obj.obj (op U)) : U ⟶ Z :=
  (fullyFaithfulToOver B X hX).preimage (m.hom.app (op U) s)

lemma toOver_map_representableSectionHom {Z : SmallEtale B X hX}
    {G : Sheaf (topology B X hX) (Type u)}
    (m : G ⟶ (representableSheaf B X hX).obj Z) {U : SmallEtale B X hX}
    (s : G.obj.obj (op U)) :
    (toOver B X hX).map (representableSectionHom m s) = m.hom.app (op U) s :=
  (fullyFaithfulToOver B X hX).map_preimage _

/-- The open subscheme of `Z` covered by the images of the sections of a sheaf mapping to
`h_Z`. -/
noncomputable def representableSectionSupport {Z : SmallEtale B X hX}
    {G : Sheaf (topology B X hX) (Type u)}
    (m : G ⟶ (representableSheaf B X hX).obj Z) : ((toScheme B X hX).obj Z).Opens :=
  ⨆ p : Σ U : SmallEtale B X hX, G.obj.obj (op U),
    ⟨Set.range ((toScheme B X hX).map (representableSectionHom m p.2)).base,
      ((toScheme B X hX).map (representableSectionHom m p.2)).isOpenMap.isOpen_range⟩

lemma range_representableSectionHom_subset {Z : SmallEtale B X hX}
    {G : Sheaf (topology B X hX) (Type u)}
    (m : G ⟶ (representableSheaf B X hX).obj Z) {U : SmallEtale B X hX}
    (s : G.obj.obj (op U)) :
    Set.range ((toScheme B X hX).map (representableSectionHom m s)).base ⊆
      (representableSectionSupport m : Set _) := by
  intro x hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, s⟩, hx⟩

/-- The object of the small étale site given by an open subscheme of an object `Z`. -/
noncomputable def ofOpens (Z : SmallEtale B X hX) (W : ((toScheme B X hX).obj Z).Opens) :
    SmallEtale B X hX :=
  ⟨Over.mk ((ObjectProperty.homMk W.ι :
      B.obj (W : Scheme) (Scheme.size_lt_of_isOpenImmersion W.ι Z.obj.left.property) ⟶
        Z.obj.left) ≫ Z.obj.hom), by
    change Etale (W.ι ≫ B.inclusion.map Z.obj.hom)
    infer_instance⟩

/-- The open immersion `W ⟶ Z` in the small étale site. -/
noncomputable def ofOpensι (Z : SmallEtale B X hX) (W : ((toScheme B X hX).obj Z).Opens) :
    ofOpens Z W ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk W.ι) rfl)

lemma toScheme_map_ofOpensι (Z : SmallEtale B X hX) (W : ((toScheme B X hX).obj Z).Opens) :
    (toScheme B X hX).map (ofOpensι Z W) = W.ι :=
  rfl

instance (Z : SmallEtale B X hX) (W : ((toScheme B X hX).obj Z).Opens) :
    IsOpenImmersion ((toScheme B X hX).map (ofOpensι Z W)) :=
  inferInstanceAs (IsOpenImmersion W.ι)

instance (Z : SmallEtale B X hX) (W : ((toScheme B X hX).obj Z).Opens) :
    Mono (ofOpensι Z W) :=
  (toScheme B X hX).mono_of_mono_map inferInstance

lemma exists_comp_ofOpensι_eq_iff (Z : SmallEtale B X hX) (W : ((toScheme B X hX).obj Z).Opens)
    {U : SmallEtale B X hX} (f : U ⟶ Z) :
    (∃ g : U ⟶ ofOpens Z W, g ≫ ofOpensι Z W = f) ↔
      Set.range ((toScheme B X hX).map f).base ⊆ (W : Set _) := by
  constructor
  · rintro ⟨g, rfl⟩
    rintro _ ⟨x, rfl⟩
    change W.ι.base (((toScheme B X hX).map g).base x) ∈ (W : Set _)
    rw [← Scheme.Opens.range_ι W]
    exact ⟨_, rfl⟩
  · intro h
    have h' : Set.range ((toScheme B X hX).map f).base ⊆ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]; exact h
    let l := IsOpenImmersion.lift W.ι ((toScheme B X hX).map f) h'
    refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk l) ?_), ?_⟩
    · apply B.inclusion.map_injective
      change l ≫ W.ι ≫ B.inclusion.map Z.obj.hom = B.inclusion.map U.obj.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact (B.inclusion.map_comp _ _).symm.trans (congrArg _ (Over.w f.hom))
    · apply (toScheme B X hX).map_injective
      exact IsOpenImmersion.lift_fac W.ι ((toScheme B X hX).map f) h'

lemma representableSectionHom_map {Z : SmallEtale B X hX} {G : Sheaf (topology B X hX) (Type u)}
    (m : G ⟶ (representableSheaf B X hX).obj Z) {U V : SmallEtale B X hX} (f : V ⟶ U)
    (s : G.obj.obj (op U)) :
    representableSectionHom m (G.obj.map f.op s) = f ≫ representableSectionHom m s := by
  apply (toOver B X hX).map_injective
  rw [toOver_map_representableSectionHom, Functor.map_comp, toOver_map_representableSectionHom,
    NatTrans.naturality_apply]
  rfl

/-- **Gluing.** Let `m : G ⟶ h_Z` be injective on sections. A morphism `t : U ⟶ Z` whose image
lies in the union of the images of the sections of `G` is (the image of) a section of `G`. -/
lemma exists_representableSectionHom_eq_of_range_subset {Z : SmallEtale B X hX}
    {G : Sheaf (topology B X hX) (Type u)} (m : G ⟶ (representableSheaf B X hX).obj Z)
    (hm : ∀ U, Function.Injective (m.hom.app U)) {U : SmallEtale B X hX} (t : U ⟶ Z)
    (ht : Set.range ((toScheme B X hX).map t).base ⊆ (representableSectionSupport m : Set _)) :
    ∃ s : G.obj.obj (op U), representableSectionHom m s = t := by
  let S : Sieve U :=
    { arrows := fun V f => ∃ s : G.obj.obj (op V), representableSectionHom m s = f ≫ t
      downward_closed := by
        rintro V V' f ⟨s, hs⟩ g
        exact ⟨G.obj.map g.op s, by rw [representableSectionHom_map, hs, Category.assoc]⟩ }
  have hS : S ∈ topology B X hX U := by
    apply mem_topology_of_jointlySurjective
    intro x
    obtain ⟨⟨V, s⟩, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp (ht ⟨x, rfl⟩)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    refine ⟨pullback t (representableSectionHom m s), pullback.fst _ _,
      ⟨G.obj.map (pullback.snd t (representableSectionHom m s)).op s, ?_⟩,
      ⟨(PreservesPullback.iso (toScheme B X hX) t (representableSectionHom m s)).inv z, ?_⟩⟩
    · rw [representableSectionHom_map, ← pullback.condition]
    · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst, hz]
  have hG : Presieve.IsSheaf (topology B X hX) G.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have hZ : Presieve.IsSheaf (topology B X hX) ((representableSheaf B X hX).obj Z).obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((representableSheaf B X hX).obj Z).property
  choose x hx using fun (V : SmallEtale B X hX) (f : V ⟶ U) (hf : S f) => hf
  let fam : Presieve.FamilyOfElements G.obj S.arrows := fun V f hf => x V f hf
  have hfam : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V V' f g hf
    apply hm
    rw [← toOver_map_representableSectionHom, ← toOver_map_representableSectionHom]
    congr 1
    change representableSectionHom m (x _ _ _) =
      representableSectionHom m (G.obj.map g.op (x V f hf))
    rw [representableSectionHom_map, hx, hx, Category.assoc]
  obtain ⟨a, ha, -⟩ := hG S hS fam hfam
  refine ⟨a, (toOver B X hX).map_injective ?_⟩
  rw [toOver_map_representableSectionHom]
  refine (hZ S hS).isSeparatedFor.ext fun V f hf => ?_
  rw [← NatTrans.naturality_apply, ha f hf]
  change m.hom.app _ (x V f hf) = (toOver B X hX).map f ≫ (toOver B X hX).map t
  rw [← toOver_map_representableSectionHom, hx, Functor.map_comp]

/-- **A subsheaf of a representable sheaf is representable.** Let `m : G ⟶ h_Z` be a morphism
of étale sheaves of sets which is injective on sections. Then there is a monomorphism
`j : R ⟶ Z` of the small étale site (an open subscheme of `Z`) such that a morphism `U ⟶ Z`
factors through `j` exactly when it is (the image of) a section of `G`. -/
theorem exists_mono_forall_exists_comp_eq_iff {Z : SmallEtale B X hX}
    {G : Sheaf (topology B X hX) (Type u)} (m : G ⟶ (representableSheaf B X hX).obj Z)
    (hm : ∀ U, Function.Injective (m.hom.app U)) :
    ∃ (R : SmallEtale B X hX) (j : R ⟶ Z), Mono j ∧
      ∀ {U : SmallEtale B X hX} (f : U ⟶ Z),
        (∃ g : U ⟶ R, g ≫ j = f) ↔ ∃ s : G.obj.obj (op U), representableSectionHom m s = f := by
  refine ⟨ofOpens Z (representableSectionSupport m), ofOpensι Z (representableSectionSupport m),
    inferInstance, fun f => ?_⟩
  rw [exists_comp_ofOpensι_eq_iff]
  constructor
  · exact exists_representableSectionHom_eq_of_range_subset m hm f
  · rintro ⟨s, rfl⟩
    exact range_representableSectionHom_subset m s

lemma representableSheaf_map_hom_app {Z Z' : SmallEtale B X hX} (g : Z ⟶ Z')
    (U : (SmallEtale B X hX)ᵒᵖ) (r : ((representableSheaf B X hX).obj Z).obj.obj U) :
    ((representableSheaf B X hX).map g).hom.app U r = r ≫ (toOver B X hX).map g :=
  rfl

lemma preimage_toOver_map_comp {U V Y : SmallEtale B X hX} (g : V ⟶ U)
    (a : (toOver B X hX).obj U ⟶ (toOver B X hX).obj Y) :
    (fullyFaithfulToOver B X hX).preimage ((toOver B X hX).map g ≫ a) =
      g ≫ (fullyFaithfulToOver B X hX).preimage a :=
  (fullyFaithfulToOver B X hX).map_injective (by
    rw [Functor.map_comp, (fullyFaithfulToOver B X hX).map_preimage,
      (fullyFaithfulToOver B X hX).map_preimage])

/-- The morphism from the kernel pair `h_Y ×_F h_Y` of `φ : h_Y ⟶ F` to `h_{Y ×_X Y}`,
sending a pair of sections `(a, b)` to `(a, b) : U ⟶ Y ×_X Y`. -/
noncomputable def kernelPairToRepresentableProd {Y : SmallEtale B X hX}
    {F : Sheaf (topology B X hX) (Type u)} (φ : (representableSheaf B X hX).obj Y ⟶ F) :
    Sheaf.sectionwisePullbackSheaf φ φ ⟶ (representableSheaf B X hX).obj (Y ⨯ Y) :=
  ObjectProperty.homMk
    { app := fun U => TypeCat.ofHom fun p => (toOver B X hX).map
        (prod.lift ((fullyFaithfulToOver B X hX).preimage p.1.1)
          ((fullyFaithfulToOver B X hX).preimage p.1.2))
      naturality := fun U V f => by
        ext p
        change (toOver B X hX).map (prod.lift
            ((fullyFaithfulToOver B X hX).preimage ((toOver B X hX).map f.unop ≫ p.1.1))
            ((fullyFaithfulToOver B X hX).preimage ((toOver B X hX).map f.unop ≫ p.1.2))) =
          (toOver B X hX).map f.unop ≫ (toOver B X hX).map (prod.lift
            ((fullyFaithfulToOver B X hX).preimage p.1.1)
            ((fullyFaithfulToOver B X hX).preimage p.1.2))
        rw [← Functor.map_comp, prod.comp_lift]
        congr 2 }

lemma representableSectionHom_kernelPairToRepresentableProd {Y : SmallEtale B X hX}
    {F : Sheaf (topology B X hX) (Type u)} (φ : (representableSheaf B X hX).obj Y ⟶ F)
    {U : SmallEtale B X hX} (p : (Sheaf.sectionwisePullbackSheaf φ φ).obj.obj (op U)) :
    representableSectionHom (kernelPairToRepresentableProd φ) p =
      prod.lift ((fullyFaithfulToOver B X hX).preimage p.1.1)
        ((fullyFaithfulToOver B X hX).preimage p.1.2) :=
  (fullyFaithfulToOver B X hX).preimage_map _

lemma injective_kernelPairToRepresentableProd_app {Y : SmallEtale B X hX}
    {F : Sheaf (topology B X hX) (Type u)} (φ : (representableSheaf B X hX).obj Y ⟶ F)
    (U : (SmallEtale B X hX)ᵒᵖ) :
    Function.Injective ((kernelPairToRepresentableProd φ).hom.app U) := by
  intro p q h
  have h' := (toOver B X hX).map_injective h
  have h₁ := congrArg (· ≫ prod.fst) h'
  have h₂ := congrArg (· ≫ prod.snd) h'
  simp only [prod.lift_fst, prod.lift_snd] at h₁ h₂
  exact Subtype.ext (Prod.ext ((fullyFaithfulToOver B X hX).homEquiv.symm.injective h₁)
    ((fullyFaithfulToOver B X hX).homEquiv.symm.injective h₂))

/-- **A quotient of a representable étale sheaf is the cokernel of an étale equivalence
relation.** Let `Y` be an object of the small étale site of `X` and `φ : h_Y ⟶ F` an
epimorphism of étale sheaves of sets. Then there are an object `R` of the small étale site
and `X`-morphisms `u v : R ⟶ Y` such that `h_u, h_v : h_R ⇉ h_Y` represent an equivalence
relation (for every `U`, `r ↦ (h_u(r), h_v(r))` is injective on `h_R(U)` and its image is an
equivalence relation on `h_Y(U)`), and `φ` is a cokernel of `h_u` and `h_v`. -/
@[weil "lem_fk104_quotient_of_representable_implies_cokernel_equivalence_relation"]
theorem exists_isEquivalenceRelation_isColimit_cofork {Y : SmallEtale B X hX}
    {F : Sheaf (topology B X hX) (Type u)} (φ : (representableSheaf B X hX).obj Y ⟶ F)
    [Epi φ] :
    ∃ (R : SmallEtale B X hX) (u v : R ⟶ Y)
      (w : (representableSheaf B X hX).map u ≫ φ = (representableSheaf B X hX).map v ≫ φ),
      (∀ U, Function.Injective fun r => (((representableSheaf B X hX).map u).hom.app U r,
          ((representableSheaf B X hX).map v).hom.app U r)) ∧
      (∀ U, Equivalence fun a b => ∃ r, ((representableSheaf B X hX).map u).hom.app U r = a ∧
          ((representableSheaf B X hX).map v).hom.app U r = b) ∧
      Nonempty (IsColimit (Cofork.ofπ φ w)) := by
  obtain ⟨R, j, hj, hfac⟩ := exists_mono_forall_exists_comp_eq_iff
    (kernelPairToRepresentableProd φ) (injective_kernelPairToRepresentableProd_app φ)
  let pre := fun {U : SmallEtale B X hX}
    (a : (toOver B X hX).obj U ⟶ (toOver B X hX).obj Y) => (fullyFaithfulToOver B X hX).preimage a
  have hrel : ∀ (U : SmallEtale B X hX) (a b : ((representableSheaf B X hX).obj Y).obj.obj (op U)),
      (∃ r, ((representableSheaf B X hX).map (j ≫ prod.fst)).hom.app (op U) r = a ∧
        ((representableSheaf B X hX).map (j ≫ prod.snd)).hom.app (op U) r = b) ↔
        φ.hom.app (op U) a = φ.hom.app (op U) b := by
    intro U a b
    constructor
    · rintro ⟨r, rfl, rfl⟩
      obtain ⟨g, rfl⟩ := (toOver B X hX).map_surjective r
      obtain ⟨p, hp⟩ := (hfac (g ≫ j)).1 ⟨g, rfl⟩
      rw [representableSectionHom_kernelPairToRepresentableProd] at hp
      have h₁ := congrArg (· ≫ prod.fst) hp
      have h₂ := congrArg (· ≫ prod.snd) hp
      simp only [prod.lift_fst, prod.lift_snd, Category.assoc] at h₁ h₂
      have e₁ : p.1.1 = (toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.fst) := by
        rw [← (fullyFaithfulToOver B X hX).map_preimage p.1.1, h₁, ← Functor.map_comp]
      have e₂ : p.1.2 = (toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.snd) := by
        rw [← (fullyFaithfulToOver B X hX).map_preimage p.1.2, h₂, ← Functor.map_comp]
      change φ.hom.app _ ((toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.fst)) =
        φ.hom.app _ ((toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.snd))
      rw [← e₁, ← e₂]
      exact p.2
    · intro h
      let p : (Sheaf.sectionwisePullbackSheaf φ φ).obj.obj (op U) := ⟨(a, b), h⟩
      obtain ⟨g, hg⟩ := (hfac (prod.lift (pre a) (pre b))).2
        ⟨p, representableSectionHom_kernelPairToRepresentableProd φ p⟩
      refine ⟨(toOver B X hX).map g, ?_, ?_⟩
      · change (toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.fst) = a
        rw [← Functor.map_comp, ← Category.assoc, hg, prod.lift_fst]
        exact (fullyFaithfulToOver B X hX).map_preimage a
      · change (toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.snd) = b
        rw [← Functor.map_comp, ← Category.assoc, hg, prod.lift_snd]
        exact (fullyFaithfulToOver B X hX).map_preimage b
  have w : (representableSheaf B X hX).map (j ≫ prod.fst) ≫ φ =
      (representableSheaf B X hX).map (j ≫ prod.snd) ≫ φ := by
    apply Sheaf.hom_ext
    ext U r
    exact (hrel U.unop _ _).1 ⟨r, rfl, rfl⟩
  refine ⟨R, j ≫ prod.fst, j ≫ prod.snd, w, ?_, ?_, ?_⟩
  · intro U r r' h
    obtain ⟨g, rfl⟩ := (toOver B X hX).map_surjective r
    obtain ⟨g', rfl⟩ := (toOver B X hX).map_surjective r'
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    change (toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.fst) =
      (toOver B X hX).map g' ≫ (toOver B X hX).map (j ≫ prod.fst) at h₁
    change (toOver B X hX).map g ≫ (toOver B X hX).map (j ≫ prod.snd) =
      (toOver B X hX).map g' ≫ (toOver B X hX).map (j ≫ prod.snd) at h₂
    rw [← Functor.map_comp, ← Functor.map_comp] at h₁ h₂
    have : g ≫ j = g' ≫ j := by
      apply prod.hom_ext
      · simpa only [Category.assoc] using (toOver B X hX).map_injective h₁
      · simpa only [Category.assoc] using (toOver B X hX).map_injective h₂
    exact congrArg _ ((cancel_mono j).1 this)
  · intro U
    have : (fun a b => ∃ r, ((representableSheaf B X hX).map (j ≫ prod.fst)).hom.app U r = a ∧
        ((representableSheaf B X hX).map (j ≫ prod.snd)).hom.app U r = b) =
        fun a b => φ.hom.app U a = φ.hom.app U b := by
      ext a b
      exact hrel U.unop a b
    rw [this]
    exact ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  · -- The small étale site is essentially small, so sheaves of sets in `Type u` admit a
    -- sheafification, and epimorphisms of such sheaves are regular.
    have : HasSheafify (topology B X hX) (Type u) := hasSheafifyEssentiallySmallSite.{u} _ _
    have : IsRegularEpi φ := IsRegularEpiCategory.regularEpiOfEpi φ
    let hc := isColimitCoforkOfEffectiveEpi φ (Sheaf.sectionwisePullbackCone φ φ)
      (Sheaf.isLimitSectionwisePullbackCone φ φ)
    refine ⟨Cofork.IsColimit.mk' _ fun t => ?_⟩
    have ht : (Sheaf.sectionwisePullbackCone φ φ).fst ≫ t.π =
        (Sheaf.sectionwisePullbackCone φ φ).snd ≫ t.π := by
      apply Sheaf.hom_ext
      ext U p
      obtain ⟨r, h₁, h₂⟩ := (hrel U.unop p.1.1 p.1.2).2 p.2
      have hcond := congrArg (fun k => k.hom.app U r) t.condition
      change t.π.hom.app U p.1.1 = t.π.hom.app U p.1.2
      rw [← h₁, ← h₂]
      exact hcond
    refine ⟨hc.desc (Cofork.ofπ t.π ht), hc.fac _ WalkingParallelPair.one, fun {k} hk => ?_⟩
    apply (cancel_epi φ).1
    exact hk.trans (hc.fac (Cofork.ofπ t.π ht) WalkingParallelPair.one).symm

end AlgebraicGeometry.SmallEtale

end
