module

public import Weil.Attr
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Filtered.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleCoequalizerPresentation

/-!
# A sheaf of sets is the filtered colimit of its constructible subsheaves

Let `X` be a Noetherian scheme and `F` a sheaf of sets on the small étale site of `X`. The
constructible subsheaves of `F`, ordered by inclusion, form a nonempty directed family, and `F`,
with the inclusions `G ⊆ F`, is the colimit of this family in the category of sheaves of sets.

The colimit statement is an instance of a fact about any site: if a directed family `S` of
subsheaves of a sheaf of sets `F` exhausts `F` locally (every section of `F` lies in a member of
`S` after restriction to the members of a covering sieve), then `F` is the colimit of `S`. For the
constructible subsheaves the family is directed because the image of `G₁ ⨿ G₂ ⟶ F` contains `G₁`
and `G₂`, and it exhausts `F` locally because, over an affine object `V`, a section `s ∈ F(V)` lies
in the image of the morphism `h_V ⟶ F` it classifies. All these images are constructible: on a
Noetherian scheme a quotient of a constructible sheaf of sets is constructible (Stacks 09BH), and
`h_V` is constructible for `V` quasi-compact and quasi-separated (Stacks 03S8).

## Main definitions

* `CategoryTheory.Subfunctor.sheafDiagram`, `CategoryTheory.Subfunctor.sheafCocone`: a family of
  subsheaves of a sheaf, as a diagram of sheaves indexed by the family ordered by inclusion, and
  the cocone of the inclusions.
* `AlgebraicGeometry.constructibleSubsheaves`: the constructible subsheaves of a sheaf of sets on
  the small étale site.

## Main results

* `CategoryTheory.Subfunctor.isColimitSheafCocone`: a directed family of subsheaves exhausting a
  sheaf of sets locally has the sheaf as its colimit.
* `AlgebraicGeometry.nonempty_and_directedOn_constructibleSubsheaves`: on a Noetherian scheme the
  constructible subsheaves of a sheaf of sets form a nonempty directed family.
* `AlgebraicGeometry.isFiltered_constructibleSubsheaves`: the same, as a filtered category.
* `AlgebraicGeometry.isColimitConstructibleSubsheaves`: a sheaf of sets is the colimit of its
  constructible subsheaves.

## Implementation notes

A subsheaf is a `CategoryTheory.Subfunctor` of the underlying presheaf which is a sheaf. The
objects of the small étale site are arbitrary étale `X`-schemes, not necessarily quasi-compact, so a
section over an object `U` need not lie in a single constructible subsheaf (the image of `h_U` need
not be constructible); it does lie in one locally on `U`, over the affine objects covering `U`,
which is what the colimit statement needs.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FreitagKiehl]
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {F : Sheaf J (Type w)}

namespace Subfunctor

/-- A subfunctor of a sheaf of sets which is itself a sheaf, as an object of the category of
sheaves. -/
def toSheaf (G : Subfunctor F.obj) (hG : Presieve.IsSheaf J G.toFunctor) : Sheaf J (Type w) :=
  ⟨G.toFunctor, (isSheaf_iff_isSheaf_of_type J _).2 hG⟩

variable (S : Set (Subfunctor F.obj)) (hS : ∀ G ∈ S, Presieve.IsSheaf J G.toFunctor)

/-- A family of subsheaves of a sheaf `F`, ordered by inclusion, as a diagram of sheaves. -/
def sheafDiagram : S ⥤ Sheaf J (Type w) where
  obj G := toSheaf G.1 (hS G.1 G.2)
  map h := ⟨homOfLe h.le⟩

/-- The cocone over `sheafDiagram S hS` formed by the inclusions of the subsheaves into `F`. -/
def sheafCocone : Cocone (sheafDiagram S hS) where
  pt := F
  ι := { app G := ⟨G.1.ι⟩ }

variable {S hS}

section IsColimit

variable (hdir : DirectedOn (· ≤ ·) S)
  (hloc : ∀ (U : C) (s : F.obj.obj (op U)), ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
    ∃ G ∈ S, F.obj.map f.op s ∈ G.obj (op V))
  (c : Cocone (sheafDiagram S hS))

/-- The component at `G ∈ S` of a cocone over `sheafDiagram S hS`, evaluated at a section of `F`
lying in `G`. -/
def sheafCoconeApp (G : Subfunctor F.obj) (hG : G ∈ S) {V : C} (t : F.obj.obj (op V))
    (ht : t ∈ G.obj (op V)) : c.pt.obj.obj (op V) :=
  (c.ι.app ⟨G, hG⟩).hom.app (op V) ⟨t, ht⟩

include hdir in
/-- The value of a cocone on a section of `F` does not depend on the subsheaf containing it. -/
theorem sheafCoconeApp_eq (G G' : Subfunctor F.obj) (hG : G ∈ S) (hG' : G' ∈ S) {V : C}
    {t t' : F.obj.obj (op V)} (ht : t ∈ G.obj (op V)) (ht' : t' ∈ G'.obj (op V)) (e : t = t') :
    sheafCoconeApp c G hG t ht = sheafCoconeApp c G' hG' t' ht' := by
  subst e
  obtain ⟨H, hH, hGH, hG'H⟩ := hdir G hG G' hG'
  have h₁ := c.w (show (⟨G, hG⟩ : S) ⟶ ⟨H, hH⟩ from homOfLE hGH)
  have h₂ := c.w (show (⟨G', hG'⟩ : S) ⟶ ⟨H, hH⟩ from homOfLE hG'H)
  have e₁ := congrArg (fun φ => φ.hom.app (op V) ⟨t, ht⟩) h₁
  have e₂ := congrArg (fun φ => φ.hom.app (op V) ⟨t, ht'⟩) h₂
  exact e₁.symm.trans e₂

/-- The components of a cocone commute with restriction. -/
theorem sheafCoconeApp_map (G : Subfunctor F.obj) (hG : G ∈ S) {V W : C} (g : W ⟶ V)
    (t : F.obj.obj (op V)) (ht : t ∈ G.obj (op V)) :
    c.pt.obj.map g.op (sheafCoconeApp c G hG t ht) =
      sheafCoconeApp c G hG (F.obj.map g.op t) (G.map g.op ht) :=
  (NatTrans.naturality_apply (c.ι.app ⟨G, hG⟩).hom g.op ⟨t, ht⟩).symm

/-- `t` is a value of the cocone `c` on the section `s` of `F`: every restriction of `t` to an
object over which `s` lies in some member `G` of `S` is the value of `c` at `G`. -/
def IsSheafCoconeValue {U : C} (s : F.obj.obj (op U)) (t : c.pt.obj.obj (op U)) : Prop :=
  ∀ ⦃V : C⦄ (f : V ⟶ U) (G : Subfunctor F.obj) (hG : G ∈ S) (h : F.obj.map f.op s ∈ G.obj (op V)),
    c.pt.obj.map f.op t = sheafCoconeApp c G hG _ h

include hdir hloc in
/-- A cocone over a directed family of subsheaves exhausting `F` locally has exactly one value on
each section of `F`. -/
theorem existsUnique_isSheafCoconeValue {U : C} (s : F.obj.obj (op U)) :
    ∃! t, IsSheafCoconeValue c s t := by
  have hT := (isSheaf_iff_isSheaf_of_type J c.pt.obj).1 c.pt.property
  obtain ⟨R, hR, hRS⟩ := hloc U s
  choose G hG hsG using hRS
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let x : Presieve.FamilyOfElements c.pt.obj R.arrows := fun V f hf =>
      sheafCoconeApp c (G f hf) (hG f hf) _ (hsG f hf)
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
      simp only [x, sheafCoconeApp_map]
      refine sheafCoconeApp_eq hdir c _ _ _ _ _ _ ?_
      simp only [← Functor.map_comp_apply, ← op_comp, e]
    refine ⟨(hT R hR).amalgamate x hx, ?_⟩
    intro V f G' hG' h
    refine (hT _ (J.pullback_stable f hR)).isSeparatedFor.ext fun W g hg => ?_
    rw [← Functor.map_comp_apply, ← op_comp,
      (hT R hR).valid_glue hx _ hg, sheafCoconeApp_map]
    simp only [x]
    refine sheafCoconeApp_eq hdir c _ _ _ _ _ _ ?_
    simp only [← Functor.map_comp_apply, ← op_comp]
  · intro t₁ t₂ h₁ h₂
    refine (hT R hR).isSeparatedFor.ext fun V f hf => ?_
    rw [h₁ f _ (hG f hf) (hsG f hf), h₂ f _ (hG f hf) (hsG f hf)]

include hdir in
/-- Values of a cocone are compatible with restriction. -/
theorem isSheafCoconeValue_map {U V : C} (g : V ⟶ U) {s : F.obj.obj (op U)}
    {t : c.pt.obj.obj (op U)} (ht : IsSheafCoconeValue c s t) :
    IsSheafCoconeValue c (F.obj.map g.op s) (c.pt.obj.map g.op t) := by
  intro W f G hG h
  have h' : F.obj.map (f ≫ g).op s ∈ G.obj (op W) := by
    rw [op_comp, Functor.map_comp_apply]
    exact h
  rw [← Functor.map_comp_apply, ← op_comp, ht (f ≫ g) G hG h']
  exact sheafCoconeApp_eq hdir c _ _ _ _ _ _ (by rw [op_comp, Functor.map_comp_apply])

include hdir in
/-- On a section lying in a member `G` of the family, the component of the cocone at `G` is a
value of the cocone. -/
theorem isSheafCoconeValue_sheafCoconeApp (G : Subfunctor F.obj) (hG : G ∈ S) {U : C}
    (s : F.obj.obj (op U)) (hs : s ∈ G.obj (op U)) :
    IsSheafCoconeValue c s (sheafCoconeApp c G hG s hs) := by
  intro V f G' hG' h
  rw [sheafCoconeApp_map]
  exact sheafCoconeApp_eq hdir c _ _ _ _ _ _ rfl

include hdir hloc in
/-- **A sheaf is the colimit of a directed family of subsheaves exhausting it locally.** Let `S` be
a directed family of subsheaves of a sheaf of sets `F` such that every section of `F` lies,
locally on a covering sieve, in some member of `S`. Then `F`, with the inclusions, is the colimit
of `S` in the category of sheaves. -/
noncomputable def isColimitSheafCocone : IsColimit (sheafCocone S hS) where
  desc c := ⟨{
    app U := ↾fun s => (existsUnique_isSheafCoconeValue hdir hloc c s).exists.choose
    naturality U V g := by
      ext s
      change (existsUnique_isSheafCoconeValue hdir hloc c (F.obj.map g s)).exists.choose =
        c.pt.obj.map g (existsUnique_isSheafCoconeValue hdir hloc c s).exists.choose
      refine (existsUnique_isSheafCoconeValue hdir hloc c _).unique
        (existsUnique_isSheafCoconeValue hdir hloc c _).exists.choose_spec ?_
      exact isSheafCoconeValue_map hdir c g.unop
        (existsUnique_isSheafCoconeValue hdir hloc c s).exists.choose_spec }⟩
  fac c G := by
    ext U s
    exact (existsUnique_isSheafCoconeValue hdir hloc c s.1).unique
      (existsUnique_isSheafCoconeValue hdir hloc c s.1).exists.choose_spec
      (isSheafCoconeValue_sheafCoconeApp hdir c G.1 G.2 s.1 s.2)
  uniq c m hm := by
    ext U s
    refine (existsUnique_isSheafCoconeValue hdir hloc c s).unique ?_
      (existsUnique_isSheafCoconeValue hdir hloc c s).exists.choose_spec
    intro V f G hG h
    have := congrArg (fun φ => φ.hom.app (op V) ⟨_, h⟩) (hm ⟨G, hG⟩)
    exact (NatTrans.naturality_apply m.hom f.op s).symm.trans this

end IsColimit

end Subfunctor

end CategoryTheory

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- An object of the small étale site is covered by affine objects.

this is the proof of the private
`AlgebraicGeometry.exists_affine_cover_smallEtale` of StacksFrontier's
`ConstructibleCoequalizerPresentation`, which cannot be referenced from here. -/
private theorem exists_isAffine_cover_smallEtale
    (U : SmallEtale B X.obj X.property) :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B X.obj X.property)
      (arrows : ∀ index, V index ⟶ U),
      Sieve.ofArrows V arrows ∈ SmallEtale.topology B X.obj X.property U ∧
      ∀ index, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (V index)) := by
  classical
  let T := (SmallEtale.toScheme B X.obj X.property).obj U
  let cover := T.affineCover
  let family : PreZeroHypercover.{u + 1} U.obj.left :=
    { I₀ := ULift.{u + 1, u} cover.I₀
      X index := B.obj (cover.X index.down)
        (Scheme.size_lt_of_isOpenImmersion (cover.f index.down) U.obj.left.property)
      f index := ObjectProperty.homMk (cover.f index.down) }
  have hfamily : IsEtaleCovering ⟨U.obj.left, family⟩ :=
    (Scheme.presieve₀_mem_precoverage_iff (P := @Etale)
      (family.map B.inclusion)).mpr ⟨fun point => by
        obtain ⟨index, preimage, hpreimage⟩ := cover.exists_eq point
        exact ⟨⟨index⟩, preimage, hpreimage⟩, fun index => by
        change Etale (cover.f index.down)
        infer_instance⟩
  obtain ⟨⟨target, selected⟩, hselected, htarget, hcomb⟩ :=
    B.exists_covering_rep ⟨U.obj.left, family⟩ hfamily
  dsimp at htarget
  subst target
  have hetale : ∀ index, Etale (B.inclusion.map (selected.f index)) :=
    ((Scheme.presieve₀_mem_precoverage_iff (selected.map B.inclusion)).mp hselected.1).2
  let V : selected.I₀ → SmallEtale B X.obj X.property := fun index =>
    ⟨Over.mk (selected.f index ≫ U.obj.hom), by
      change Etale (B.inclusion.map (selected.f index ≫ U.obj.hom))
      rw [Functor.map_comp]
      have := hetale index
      infer_instance⟩
  let arrows : ∀ index, V index ⟶ U := fun index =>
    ObjectProperty.homMk (Over.homMk (selected.f index) rfl)
  let refinement : PreZeroHypercover.{u + 1} U :=
    { I₀ := selected.I₀
      X := V
      f := arrows }
  have hrefinement : SmallEtale.IsCovering B X.obj X.property ⟨U, refinement⟩ := hselected
  refine ⟨selected.I₀, V, arrows, ?_, ?_⟩
  · exact Precoverage.generate_mem_toGrothendieck ⟨refinement, rfl, hrefinement⟩
  · obtain ⟨reindex, hobjects, harrows⟩ := hcomb.2
    intro index
    change IsAffine (B.inclusion.obj (selected.X index))
    rw [hobjects index]
    change IsAffine (cover.X (reindex index).down)
    infer_instance

/-- The constructible subsheaves of a sheaf of sets `F` on the small étale site of `X`: the
subfunctors of `F` which are sheaves and constructible. -/
def constructibleSubsheaves
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    Set (Subfunctor F.obj) :=
  {G | ∃ hG : Presieve.IsSheaf (SmallEtale.topology B X.obj X.property) G.toFunctor,
    IsConstructibleSetSheaf B X (G.toSheaf hG)}

variable {B X}

/-- A constructible subsheaf is a sheaf. -/
theorem isSheaf_of_mem_constructibleSubsheaves
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} {G : Subfunctor F.obj}
    (hG : G ∈ constructibleSubsheaves B X F) :
    Presieve.IsSheaf (SmallEtale.topology B X.obj X.property) G.toFunctor :=
  hG.1

/-- On a Noetherian scheme, the image of a morphism from a constructible sheaf of sets to `F` is
a constructible subsheaf of `F`. -/
theorem sheafify_range_mem_constructibleSubsheaves [IsNoetherian X.obj]
    {A F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (φ : A ⟶ F)
    (hA : IsConstructibleSetSheaf B X A) :
    (Subfunctor.range φ.hom).sheafify (SmallEtale.topology B X.obj X.property) ∈
      constructibleSubsheaves B X F :=
  ⟨Subfunctor.sheafify_isSheaf _ ((isSheaf_iff_isSheaf_of_type _ _).1 F.property),
    isConstructibleSetSheaf_of_epi (Q := Sheaf.image φ) B X
      (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X)
      (Sheaf.toImage φ) hA⟩

/-- A subsheaf `G` of `F` whose inclusion factors through a morphism `φ : A ⟶ F` is contained in
the image of `φ`. -/
theorem le_sheafify_range_of_factorization
    {A F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))} (φ : A ⟶ F)
    {G : Subfunctor F.obj} (hG : Presieve.IsSheaf (SmallEtale.topology B X.obj X.property)
      G.toFunctor) (ψ : G.toSheaf hG ⟶ A) (hψ : ψ ≫ φ = ⟨G.ι⟩) :
    G ≤ (Subfunctor.range φ.hom).sheafify (SmallEtale.topology B X.obj X.property) := by
  refine le_trans ?_ (Subfunctor.le_sheafify _ _)
  intro V t ht
  refine ⟨ψ.hom.app V ⟨t, ht⟩, ?_⟩
  exact congrArg (fun χ => χ.hom.app V ⟨t, ht⟩) hψ

variable (B X) in
/-- On a Noetherian scheme, the constructible subsheaves of a sheaf of sets form a nonempty
directed family. -/
@[weil "lem_fk104_sheaf_is_filtered_colimit_constructible_subsheaves"]
theorem nonempty_and_directedOn_constructibleSubsheaves [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    (constructibleSubsheaves B X F).Nonempty ∧
      DirectedOn (· ≤ ·) (constructibleSubsheaves B X F) := by
  refine ⟨⟨_, sheafify_range_mem_constructibleSubsheaves (initial.to F)
    (isConstructibleSetSheaf_colimit B X (Functor.empty _) (by rintro ⟨⟨⟩⟩))⟩, ?_⟩
  rintro G₁ ⟨h₁, c₁⟩ G₂ ⟨h₂, c₂⟩
  let φ : G₁.toSheaf h₁ ⨿ G₂.toSheaf h₂ ⟶ F := coprod.desc ⟨G₁.ι⟩ ⟨G₂.ι⟩
  refine ⟨_, sheafify_range_mem_constructibleSubsheaves φ
    (isConstructibleSetSheaf_colimit B X (pair _ _) (by rintro ⟨⟨⟩⟩ <;> assumption)),
    le_sheafify_range_of_factorization φ h₁ coprod.inl (coprod.inl_desc _ _),
    le_sheafify_range_of_factorization φ h₂ coprod.inr (coprod.inr_desc _ _)⟩

variable (B X) in
/-- On a Noetherian scheme, the constructible subsheaves of a sheaf of sets, ordered by
inclusion, form a filtered category. -/
theorem isFiltered_constructibleSubsheaves [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsFiltered (constructibleSubsheaves B X F) := by
  obtain ⟨⟨G, hG⟩, hdir⟩ := nonempty_and_directedOn_constructibleSubsheaves B X F
  have : Nonempty (constructibleSubsheaves B X F) := ⟨⟨G, hG⟩⟩
  have : IsDirectedOrder (constructibleSubsheaves B X F) :=
    ⟨fun a b => by
      obtain ⟨c, hc, h₁, h₂⟩ := hdir a.1 a.2 b.1 b.2
      exact ⟨⟨c, hc⟩, h₁, h₂⟩⟩
  infer_instance

/-- On a Noetherian scheme, every section of a sheaf of sets lies, locally on an étale covering,
in a constructible subsheaf: over an affine object `V` the image of the morphism from the
representable sheaf `h_V` classifying the section is one. -/
theorem exists_covering_mem_constructibleSubsheaves [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1)))
    (U : SmallEtale B X.obj X.property) (s : F.obj.obj (op U)) :
    ∃ R ∈ SmallEtale.topology B X.obj X.property U, ∀ ⦃V⦄ (f : V ⟶ U), R f →
      ∃ G ∈ constructibleSubsheaves B X F, F.obj.map f.op s ∈ G.obj (op V) := by
  obtain ⟨I, V, arrows, hcover, haff⟩ := exists_isAffine_cover_smallEtale B X U
  refine ⟨_, hcover, ?_⟩
  rintro W f ⟨T, g, _, ⟨i⟩, rfl⟩
  let J := SmallEtale.topology B X.obj X.property
  let φ : (Sheaf.sheafifiedYoneda J).obj (V i) ⟶ F :=
    (Sheaf.sectionEquiv J).symm (F.obj.map (arrows i).op s)
  have hφ : IsConstructibleSetSheaf B X ((Sheaf.sheafifiedYoneda J).obj (V i)) := by
    have := haff i
    exact representableIsConstructibleSetSheaf B X (V i) inferInstance inferInstance
  refine ⟨_, sheafify_range_mem_constructibleSubsheaves φ hφ, ?_⟩
  have hmem : F.obj.map (arrows i).op s ∈
      ((Subfunctor.range φ.hom).sheafify J).obj (op (V i)) := by
    refine Subfunctor.le_sheafify _ _ _ ⟨Sheaf.sectionEquiv J (𝟙 _), ?_⟩
    rw [← Sheaf.sectionEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]
  rw [op_comp, Functor.map_comp_apply]
  exact Subfunctor.map _ g.op hmem

variable (B X) in
/-- **A sheaf of sets is the filtered colimit of its constructible subsheaves.** On the small
étale site of a Noetherian scheme `X`, a sheaf of sets `F`, with the inclusions `G ⊆ F`, is the
colimit in the category of sheaves of the directed family of its constructible subsheaves
(`nonempty_and_directedOn_constructibleSubsheaves`). -/
@[weil "lem_fk104_sheaf_is_filtered_colimit_constructible_subsheaves"]
noncomputable def isColimitConstructibleSubsheaves [IsNoetherian X.obj]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) :
    IsColimit (Subfunctor.sheafCocone (constructibleSubsheaves B X F)
      (fun _ hG => isSheaf_of_mem_constructibleSubsheaves hG)) :=
  Subfunctor.isColimitSheafCocone (nonempty_and_directedOn_constructibleSubsheaves B X F).2
    (exists_covering_mem_constructibleSubsheaves F)

end AlgebraicGeometry
