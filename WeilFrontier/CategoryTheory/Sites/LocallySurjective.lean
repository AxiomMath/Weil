module

public import Weil.Attr
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Epimorphisms of étale sheaves of sets

A morphism `φ : F ⟶ G` of sheaves of sets on the small étale site of a scheme `X` is an
epimorphism if and only if every section `s ∈ G(U)` becomes, after restriction along a single
surjective étale morphism `V ⟶ U`, a section in the image of `φ_V : F(V) ⟶ G(V)`.

Mathlib characterizes epimorphisms of sheaves of sets as the locally surjective morphisms,
where local surjectivity asks that `s` lies locally in the image of `φ` with respect to a
covering sieve. On the small étale site a covering sieve contains a jointly surjective family
of étale morphisms, and the disjoint union of such a family is a single surjective étale
morphism; the local preimages glue over that disjoint union because the sheaf condition holds
for the family of coprojections of a coproduct.

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.sigmaObj`: the disjoint union of a family of schemes étale
  over `X`, as an object of `X.Etale`.

## Main results

* `AlgebraicGeometry.Scheme.Etale.exists_map_sigmaι_eq`: a family of sections of a sheaf on
  the members of a family glues to a section on its disjoint union.
* `AlgebraicGeometry.Scheme.isLocallySurjective_iff_forall_exists_surjective`: a morphism of
  sheaves on the small étale site is locally surjective if and only if every section is in its
  image after restriction along a single surjective étale morphism.
* `AlgebraicGeometry.Scheme.epi_iff_forall_exists_surjective`: the same characterization of
  epimorphisms of sheaves of sets.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

namespace Etale

set_option backward.isDefEq.respectTransparency.types false in
/-- The disjoint union of a family of schemes étale over `X`, as a scheme étale over `X`. -/
noncomputable def sigmaObj {ι : Type u} (W : ι → X.Etale) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (Sigma.desc fun i ↦ (W i).hom)
    (IsZariskiLocalAtSource.sigmaDesc fun i ↦ (W i).prop)

@[simp]
lemma sigmaObj_left {ι : Type u} (W : ι → X.Etale) :
    (sigmaObj W).left = ∐ fun i ↦ (W i).left := rfl

/-- The coprojection of a member of a family into its disjoint union. -/
noncomputable def sigmaι {ι : Type u} (W : ι → X.Etale) (i : ι) : W i ⟶ sigmaObj W :=
  MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (W i).left) i) (Sigma.ι_desc _ _)

@[simp]
lemma sigmaι_left {ι : Type u} (W : ι → X.Etale) (i : ι) :
    (sigmaι W i).left = Sigma.ι (fun i ↦ (W i).left) i := rfl

/-- The morphism out of a disjoint union induced by a family of morphisms. -/
noncomputable def sigmaDesc {ι : Type u} {W : ι → X.Etale} {U : X.Etale}
    (f : ∀ i, W i ⟶ U) : sigmaObj W ⟶ U :=
  MorphismProperty.Over.homMk (Sigma.desc fun i ↦ (f i).left)
    (by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      change Sigma.ι (fun i ↦ (W i).left) i ≫ (Sigma.desc fun i ↦ (f i).left) ≫ U.hom =
        Sigma.ι (fun i ↦ (W i).left) i ≫ Sigma.desc fun i ↦ (W i).hom
      rw [Sigma.ι_desc_assoc, Sigma.ι_desc]
      simpa using (f i).w)

@[simp]
lemma sigmaDesc_left {ι : Type u} {W : ι → X.Etale} {U : X.Etale} (f : ∀ i, W i ⟶ U) :
    (sigmaDesc f).left = Sigma.desc fun i ↦ (f i).left := rfl

@[reassoc (attr := simp)]
lemma sigmaι_sigmaDesc {ι : Type u} {W : ι → X.Etale} {U : X.Etale} (f : ∀ i, W i ⟶ U)
    (i : ι) : sigmaι W i ≫ sigmaDesc f = f i :=
  MorphismProperty.Over.Hom.ext (Sigma.ι_desc _ _)

lemma ofArrows_sigmaι_mem {ι : Type u} (W : ι → X.Etale) :
    Sieve.ofArrows W (sigmaι W) ∈ X.smallEtaleTopology (sigmaObj W) := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  refine Set.eq_univ_of_forall fun y ↦ ?_
  obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk fun i ↦ (W i).left).surjective y
  exact Set.mem_iUnion.2 ⟨i, x, by rw [sigmaMk_mk]; rfl⟩

/-- On a scheme étale over `X` with empty underlying space, a sheaf has at most one section. -/
lemma subsingleton_of_isEmpty
    (F : Sheaf X.smallEtaleTopology (Type w)) (Z : X.Etale) [IsEmpty Z.left] :
    Subsingleton (F.obj.obj (op Z)) := by
  have hcov : Sieve.ofArrows (fun e : PEmpty.{1} ↦ e.elim) (fun e ↦ e.elim : ∀ e : PEmpty.{1},
      (e.elim : X.Etale) ⟶ Z) ∈ X.smallEtaleTopology Z := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun z ↦ isEmptyElim z
  have h := (Presieve.isSheafFor_iff_generate _).2
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.property _ hcov)
  rw [Presieve.isSheafFor_arrows_iff] at h
  obtain ⟨t, -, ht⟩ := h (fun e ↦ e.elim) (fun e ↦ e.elim)
  exact ⟨fun a b ↦ (ht a fun e ↦ e.elim).trans (ht b fun e ↦ e.elim).symm⟩

lemma isSheafFor_ofArrows_sigmaι (F : Sheaf X.smallEtaleTopology (Type w)) {ι : Type u}
    (W : ι → X.Etale) : Presieve.IsSheafFor F.obj (Presieve.ofArrows W (sigmaι W)) :=
  (Presieve.isSheafFor_iff_generate _).2
    ((isSheaf_iff_isSheaf_of_type _ _).1 F.property _ (ofArrows_sigmaι_mem W))

/-- Sections of a sheaf on the members of a family glue to a section on the disjoint union. -/
lemma exists_map_sigmaι_eq (F : Sheaf X.smallEtaleTopology (Type w)) {ι : Type u}
    (W : ι → X.Etale) (t : ∀ i, F.obj.obj (op (W i))) :
    ∃ t' : F.obj.obj (op (sigmaObj W)), ∀ i, F.obj.map (sigmaι W i).op t' = t i := by
  have h := isSheafFor_ofArrows_sigmaι F W
  rw [Presieve.isSheafFor_arrows_iff] at h
  obtain ⟨t', ht', -⟩ := h t fun i j Z gi gj hij ↦ by
    have hl : gi.left ≫ Sigma.ι (fun i ↦ (W i).left) i =
        gj.left ≫ Sigma.ι (fun i ↦ (W i).left) j := by
      exact congrArg (fun g ↦ g.left) hij
    by_cases hij' : i = j
    · subst hij'
      have : gi = gj := by
        exact MorphismProperty.Over.Hom.ext ((cancel_mono _).1 hl)
      rw [this]
    · have : IsEmpty Z.left := isEmpty_of_commSq_sigmaι_of_ne ⟨hl⟩ hij'
      exact (subsingleton_of_isEmpty F Z).elim _ _
  exact ⟨t', ht'⟩

/-- Two sections of a sheaf on a disjoint union agreeing on every member are equal. -/
lemma ext_of_map_sigmaι_eq (F : Sheaf X.smallEtaleTopology (Type w)) {ι : Type u}
    {W : ι → X.Etale} {a b : F.obj.obj (op (sigmaObj W))}
    (h : ∀ i, F.obj.map (sigmaι W i).op a = F.obj.map (sigmaι W i).op b) : a = b :=
  (isSheafFor_ofArrows_sigmaι F W).isSeparatedFor.ext fun _ _ hf ↦ by obtain ⟨i⟩ := hf; exact h i

end Etale

set_option backward.isDefEq.respectTransparency.types false in
lemma exists_mem_range_of_mem_smallEtaleTopology {U : X.Etale} {S : Sieve U}
    (hS : S ∈ X.smallEtaleTopology U) (x : U.left) :
    ∃ (W : X.Etale) (f : W ⟶ U), S f ∧ x ∈ Set.range f.left := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hS
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
  exact ⟨_, (𝒰.f j).asOverProp X, hle _ _ (Presieve.ofArrows.mk j), y, hy⟩

/-- A morphism of sheaves on the small étale site is locally surjective if and only if every
section of the target lies in the image after restriction along one surjective étale
morphism. -/
theorem isLocallySurjective_iff_forall_exists_surjective
    {F G : Sheaf X.smallEtaleTopology (Type w)} (φ : F ⟶ G) :
    Sheaf.IsLocallySurjective φ ↔ ∀ (U : X.Etale) (s : G.obj.obj (op U)),
      ∃ (V : X.Etale) (f : V ⟶ U), Surjective f.left ∧
        ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map f.op s := by
  constructor
  · intro h U s
    have hS := Presheaf.imageSieve_mem X.smallEtaleTopology φ.hom (U := op U) s
    choose W f hf hx using exists_mem_range_of_mem_smallEtaleTopology hS
    choose t ht using hf
    obtain ⟨t', ht'⟩ := Etale.exists_map_sigmaι_eq F W t
    refine ⟨Etale.sigmaObj W, Etale.sigmaDesc f, ⟨fun y ↦ ?_⟩, t', ?_⟩
    · obtain ⟨z, hz⟩ := hx y
      have hy : Sigma.ι (fun x ↦ (W x).left) y ≫ (Etale.sigmaDesc f).left = (f y).left :=
        congrArg (fun g ↦ g.left) (Etale.sigmaι_sigmaDesc f y)
      exact ⟨Sigma.ι (fun x ↦ (W x).left) y z,
        (Scheme.Hom.comp_apply _ _ z).symm.trans ((congrArg (fun g ↦ g z) hy).trans hz)⟩
    · refine Etale.ext_of_map_sigmaι_eq G fun i ↦ ?_
      rw [← NatTrans.naturality_apply, ht', ht, ← Functor.map_comp_apply, ← op_comp,
        Etale.sigmaι_sigmaDesc]
  · intro h
    refine ⟨fun {U} s ↦ ?_⟩
    obtain ⟨V, f, hf, t, ht⟩ := h U s
    refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows (fun _ : Unit ↦ V)
      (fun _ ↦ f)) ?_ ?_
    · rintro W g ⟨_, a, _, ⟨⟩, rfl⟩
      exact (Presheaf.imageSieve φ.hom s).downward_closed ⟨t, ht⟩ a
    · rw [ofArrows_mem_smallEtaleTopology_iff]
      exact Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨(), f.left.surjective y⟩

/-- A morphism `φ : F ⟶ G` of sheaves of sets on the small étale site of `X` is an epimorphism
if and only if for every `U` étale over `X` and every `s ∈ G(U)` there is a surjective étale
morphism `f : V ⟶ U` such that the restriction of `s` to `V` lies in the image of
`φ_V : F(V) ⟶ G(V)`.

The sheaves take values in any universe `w` for which sheafification of `Type w`-valued
presheaves exists on the small étale site; this holds for `Type u` and for every universe at
least `u + 1`. -/
@[weil "lem_fk104_sheaf_epi_iff_locally_surjective"]
theorem epi_iff_forall_exists_surjective [HasSheafify X.smallEtaleTopology (Type w)]
    {F G : Sheaf X.smallEtaleTopology (Type w)} (φ : F ⟶ G) :
    Epi φ ↔ ∀ (U : X.Etale) (s : G.obj.obj (op U)),
      ∃ (V : X.Etale) (f : V ⟶ U), Surjective f.left ∧
        ∃ t : F.obj.obj (op V), φ.hom.app (op V) t = G.obj.map f.op s := by
  rw [← Sheaf.isLocallySurjective_iff_epi, isLocallySurjective_iff_forall_exists_surjective]

end AlgebraicGeometry.Scheme
