module

public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.LocalRepresentability
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableExtensionOverGenericPointOfBoundary
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Stalk
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.RepresentableSheafOpenDifferenceLoci
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import Weil.Attr

/-!
# The representability criterion for étale sheaves

Let `X` be a noetherian separated scheme and `G` an étale sheaf of sets on `X`. Then `G` is
representable by a noetherian separated étale `X`-scheme if and only if `G` has finite stalks and
open difference loci. Necessity holds for every representable sheaf. Sufficiency is proved by
noetherian induction on the closed subsets `A ⊆ X` such that `G|_{X ∖ A}` is representable: by
the extension of representability over the generic point of a component of the boundary, every
geometric point over the generic point of an irreducible component of `A` has an étale
neighbourhood `(U, u)` on which `G` is representable.

The induction step glues: for an open `V ⊆ X`, if every geometric point of `V` has an étale
neighbourhood `U` with image in `V` and `G|_U` representable, then `G|_V` is representable, by
the étale-local criterion of representability applied on `V`. With `V = ∅` this gives the start
of the induction; with `V = (X ∖ A) ∪ p(U)` it gives a strictly larger open, as `p(U)` contains
the generic point of a component of `A`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.liftObject`: an object `U` of the small étale site of `X` with
  a morphism `U ⟶ O`, viewed as an object of the small étale site of `O`.

## Main results

* `AlgebraicGeometry.SmallEtale.restrictIsRepresentableInEt_liftObject_iff`: restricting `G`
  to `O` and then to `U` is restricting `G` to `U`.
* `AlgebraicGeometry.SmallEtale.restrictIsRepresentableInEt_openObject_of_forall`: the gluing
  step over an open subset.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_of_forall_closed_exists`: the noetherian
  induction.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_iff_hasFiniteStalks_and_hasOpenDifferenceLoci`:
  the representability criterion.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3.15
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- An object `U` of the small étale site of `X` together with a morphism `f : U ⟶ O`, viewed
as an object of the small étale site of `O`: the same scheme, with structure morphism `f`. -/
abbrev liftObject {U O : SmallEtale B X hX} (f : U ⟶ O) :
    SmallEtale B O.obj.left.1 O.obj.left.property :=
  ⟨Over.mk f.hom.left, etale_toScheme_map B X hX f⟩

/-- Composing with `f : U ⟶ O` and then with `O ⟶ X` is composing with `U ⟶ X`. Each
component is the identity of the underlying scheme. -/
noncomputable def smallEtalePostcomposeLiftObjectIso {U O : SmallEtale B X hX} (f : U ⟶ O) :
    smallEtalePostcompose B O.obj.left.1 O.obj.left.property (liftObject f) ⋙
        smallEtalePostcompose B X hX O ≅
      smallEtalePostcompose B X hX U :=
  NatIso.ofComponents
    (fun W => (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
      (Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ W.obj.hom ≫ U.obj.hom = (W.obj.hom ≫ f.hom.left) ≫ O.obj.hom
        rw [Category.id_comp, Category.assoc, Over.w f.hom])))
    (by
      intro W₁ W₂ g
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change g.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ g.hom.left
      rw [Category.comp_id, Category.id_comp])

/-- Restricting a presheaf to `O` and then to `U` (along `f : U ⟶ O`) is restricting it to
`U`: one restriction is representable if and only if the other is. -/
theorem restrictIsRepresentableInEt_liftObject_iff (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    {U O : SmallEtale B X hX} (f : U ⟶ O) :
    RestrictIsRepresentableInEt ((smallEtalePostcompose B X hX O).op ⋙ F) (liftObject f) ↔
      RestrictIsRepresentableInEt F U :=
  (isRepresentableInEt_congr
    (Functor.isoWhiskerRight (NatIso.op (smallEtalePostcomposeLiftObjectIso f)) F)).symm

/-- The structure morphism of the object attached to an open `W ⊆ X` is the inclusion of `W`. -/
theorem map_openObject_final_hom (W : X.Opens) :
    B.inclusion.map (openObject B X hX (SmallEtale.final B X hX) W).obj.hom =
      Scheme.Opens.ι W := by
  have h1 := Over.w (openObjectι B X hX (SmallEtale.final B X hX) W).hom
  have h2 := openObjectι_map B X hX (SmallEtale.final B X hX) W
  rw [← h1]
  exact (congrArg B.inclusion.map (Category.comp_id _)).trans h2

/-- The image of the structure morphism of the object attached to an open `W ⊆ X` is `W`. -/
theorem range_map_openObject_final_hom (W : X.Opens) :
    Set.range (B.inclusion.map (openObject B X hX (SmallEtale.final B X hX) W).obj.hom) =
      (W : Set X) := by
  have h := map_openObject_final_hom (B := B) (hX := hX) W
  have h2 := Scheme.Opens.range_ι W
  exact (congrArg (fun k : (W : Scheme) ⟶ X => Set.range ⇑k) h).trans h2

/-- A morphism into `X` with image in an open `W` factors through the object attached to `W`. -/
theorem lift_comp_map_openObject_final_hom (W : X.Opens) {Y : Scheme.{u}} (g : Y ⟶ X)
    (hg : Set.range g ⊆ Set.range (Scheme.Opens.ι W)) :
    (IsOpenImmersion.lift (Scheme.Opens.ι W) g hg : Y ⟶ (W : Scheme)) ≫
      B.inclusion.map (openObject B X hX (SmallEtale.final B X hX) W).obj.hom = g := by
  have h := map_openObject_final_hom (B := B) (hX := hX) W
  exact (congrArg (fun k => IsOpenImmersion.lift (Scheme.Opens.ι W) g hg ≫ k) h).trans
    (IsOpenImmersion.lift_fac _ _ _)

/-- The scheme underlying the object attached to an open of a noetherian scheme is
noetherian. -/
instance isNoetherian_openObject_final [IsNoetherian X]
    (W : X.Opens) :
    IsNoetherian ((SmallEtale.toScheme B X hX).obj
      (openObject B X hX (SmallEtale.final B X hX) W)) := by
  have : IsNoetherian ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX)) :=
    ‹IsNoetherian X›
  have : IsNoetherian (W : Scheme) :=
    Scheme.isNoetherian_of_locallyOfFiniteType_of_quasiCompact (Scheme.Opens.ι W)
  exact this

/-- The scheme underlying the object attached to an open of a separated scheme is
separated. -/
instance isSeparated_openObject_final [X.IsSeparated]
    (W : X.Opens) :
    ((SmallEtale.toScheme B X hX).obj
      (openObject B X hX (SmallEtale.final B X hX) W)).IsSeparated := by
  have : ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX)).IsSeparated :=
    ‹X.IsSeparated›
  have : (W : Scheme).IsSeparated := Scheme.isSeparated_of_isSeparated_hom (Scheme.Opens.ι W)
  exact this

/-- **Gluing over an open subset.** Let `X` be noetherian and separated, `G` an étale sheaf of
sets on `X` and `W ⊆ X` open. If every geometric point of `X` lying in `W` has an étale
neighbourhood `(U, u)` whose image lies in `W` and on which `G` is representable, then `G|_W`
is representable. -/
theorem restrictIsRepresentableInEt_openObject_of_forall [IsNoetherian X] [X.IsSeparated]
    (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (W : X.Opens)
    (h : ∀ x : GeometricPoint X, x.hom default ∈ W →
      ∃ (U : SmallEtale B X hX) (u : x.source ⟶ (SmallEtale.toScheme B X hX).obj U),
        u ≫ B.inclusion.map U.obj.hom = x.hom ∧
          Set.range (B.inclusion.map U.obj.hom) ⊆ (W : Set X) ∧
            RestrictIsRepresentableInEt G.obj U) :
    RestrictIsRepresentableInEt G.obj (openObject B X hX (SmallEtale.final B X hX) W) := by
  have := smallEtalePostcompose_isContinuous B X hX (openObject B X hX (SmallEtale.final B X hX) W)
  have : IsNoetherian (openObject B X hX (SmallEtale.final B X hX) W).obj.left.1 :=
    isNoetherian_openObject_final (B := B) (hX := hX) W
  have : (openObject B X hX (SmallEtale.final B X hX) W).obj.left.1.IsSeparated :=
    isSeparated_openObject_final (B := B) (hX := hX) W
  let G' := (smallEtalePostcompose B X hX (openObject B X hX (SmallEtale.final B X hX) W)
    ).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B (openObject B X hX (SmallEtale.final B X hX) W).obj.left.1
      (openObject B X hX (SmallEtale.final B X hX) W).obj.left.property)
    (SmallEtale.topology B X hX) |>.obj G
  let O := openObject B X hX (SmallEtale.final B X hX) W
  change IsRepresentableInEt G'.obj
  refine isRepresentableInEt_of_forall_exists_restrictIsRepresentableInEt G' fun x' ↦ ?_
  have hι : B.inclusion.map O.obj.hom = (Scheme.Opens.ι W) := map_openObject_final_hom W
  let x : GeometricPoint X := ⟨x'.residueField, x'.hom ≫ (Scheme.Opens.ι W)⟩
  have hx : x.hom default ∈ W := by
    change (Scheme.Opens.ι W) (x'.hom default) ∈ W
    have := Set.mem_range_self (f := ⇑(Scheme.Opens.ι W)) (x'.hom default)
    rwa [Scheme.Opens.range_ι] at this
  obtain ⟨U, u, hu, hUW, hrep⟩ := h x hx
  have hU : (SmallEtale.toScheme B X hX).map ((finalIsTerminal B X hX).from U) =
      B.inclusion.map U.obj.hom := by
    have := Over.w ((finalIsTerminal B X hX).from U).hom
    simpa [SmallEtale.final] using congrArg B.inclusion.map this
  have hrange : Set.range ((SmallEtale.toScheme B X hX).map
      ((finalIsTerminal B X hX).from U)) ⊆ (W : Set X) :=
    (congrArg (fun k : (SmallEtale.toScheme B X hX).obj U ⟶ X => Set.range ⇑k) hU).subset.trans
      hUW
  let f : U ⟶ O := factorThroughOpenObject B X hX U _ ((finalIsTerminal B X hX).from U) W hrange
  have hf : B.inclusion.map f.hom.left ≫ B.inclusion.map O.obj.hom = B.inclusion.map U.obj.hom := by
    rw [← Functor.map_comp, Over.w f.hom]
  refine ⟨liftObject f, u, ?_, (restrictIsRepresentableInEt_liftObject_iff G.obj f).2 hrep⟩
  change u ≫ B.inclusion.map f.hom.left = x'.hom
  have hι' : B.inclusion.map f.hom.left ≫ Scheme.Opens.ι W = B.inclusion.map U.obj.hom :=
    (congrArg (B.inclusion.map f.hom.left ≫ ·) hι).symm.trans hf
  apply (cancel_mono (Scheme.Opens.ι W)).1
  exact (Category.assoc _ _ _).trans ((congrArg (u ≫ ·) hι').trans hu)

/-- The restriction of an étale sheaf to the empty open subscheme is representable. -/
theorem restrictIsRepresentableInEt_openObject_bot [IsNoetherian X] [X.IsSeparated]
    (G : Sheaf (SmallEtale.topology B X hX) (Type u)) :
    RestrictIsRepresentableInEt G.obj (openObject B X hX (SmallEtale.final B X hX) ⊥) :=
  restrictIsRepresentableInEt_openObject_of_forall G ⊥ fun _ hx ↦ by simp at hx

/-- If the restriction of an étale sheaf to the open subscheme `X` itself is representable,
then so is the sheaf. -/
theorem isRepresentableInEt_of_restrictIsRepresentableInEt_openObject_top
    [IsNoetherian X] [X.IsSeparated] (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (h : RestrictIsRepresentableInEt G.obj (openObject B X hX (SmallEtale.final B X hX) ⊤)) :
    IsRepresentableInEt G.obj := by
  refine isRepresentableInEt_of_forall_exists_restrictIsRepresentableInEt G fun x ↦ ?_
  let W : X.Opens := ⊤
  have hW : Set.range x.hom ⊆ Set.range (Scheme.Opens.ι W) := by
    rw [Scheme.Opens.range_ι]
    exact fun _ _ ↦ trivial
  let l : x.source ⟶ (W : Scheme) := IsOpenImmersion.lift (Scheme.Opens.ι W) x.hom hW
  exact ⟨openObject B X hX (SmallEtale.final B X hX) ⊤, l,
    lift_comp_map_openObject_final_hom W x.hom hW, h⟩

/-- A closed subset `A` of a noetherian space with a point contains a closed irreducible subset
`t` maximal among the irreducible subsets of `A`. -/
theorem exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] {A : Set T} (hA : IsClosed A) (hne : A.Nonempty) :
    ∃ t : Set T, IsClosed t ∧ Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ A) t := by
  classical
  obtain ⟨S, hSf, hScl, hSirr, hAeq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hA
  have hSne : S.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    rw [hAeq] at ha
    obtain ⟨t, ht, -⟩ := ha
    exact ⟨t, ht⟩
  obtain ⟨t, htmax⟩ := hSf.exists_maximal hSne
  have htS : t ∈ S := htmax.prop
  refine ⟨t, hScl t htS, ⟨hSirr t htS, hAeq ▸ Set.subset_sUnion_of_mem htS⟩, ?_⟩
  rintro Z ⟨hZirr, hZA⟩ htZ
  obtain ⟨z, hz, hZz⟩ := isIrreducible_iff_sUnion_isClosed.1 hZirr hSf.toFinset
    (fun z hz ↦ hScl z (hSf.mem_toFinset.1 hz)) (by rwa [hSf.coe_toFinset, ← hAeq])
  have hzS : z ∈ S := hSf.mem_toFinset.1 hz
  exact hZz.trans (htmax.2 hzS (htZ.trans hZz))

/-- **Noetherian induction for representability** (FK, proof of I.3.15). Let `X` be noetherian
and separated and `G` an étale sheaf of sets on `X`. Suppose that whenever `A ⊆ X` is closed
with `G|_{X ∖ A}` representable, every geometric point `a` over a point `α₀` of `A` whose closure
is maximal among the irreducible subsets of `A` has an étale neighbourhood `(U, u)` on which `G`
is representable. Then `G` is representable. -/
theorem isRepresentableInEt_of_forall_closed_exists [IsNoetherian X] [X.IsSeparated]
    (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hext : ∀ (A : Set X)
      (hA : IsClosed A), RestrictIsRepresentableInEt G.obj
        (openObject B X hX (SmallEtale.final B X hX) ⟨Aᶜ, hA.isOpen_compl⟩) →
      ∀ α₀ : X,
        Maximal (fun Z => IsIrreducible Z ∧ Z ⊆ A) (closure {α₀}) →
      ∀ a : GeometricPoint X, a.LiesOver α₀ →
        ∃ (U : SmallEtale B X hX) (_ : (geometricPointFiber B X hX a).obj U),
          RestrictIsRepresentableInEt G.obj U) :
    IsRepresentableInEt G.obj := by
  classical
  let P : X.Opens → Prop := fun W ↦
    RestrictIsRepresentableInEt G.obj (openObject B X hX (SmallEtale.final B X hX) W)
  obtain ⟨W, hW, hmax⟩ := (wellFounded_gt (α := X.Opens)).has_min {W | P W}
    ⟨⊥, restrictIsRepresentableInEt_openObject_bot G⟩
  by_cases htop : W = ⊤
  · exact isRepresentableInEt_of_restrictIsRepresentableInEt_openObject_top G (htop ▸ hW)
  exfalso
  let A : Set X := (W : Set X)ᶜ
  have hA : IsClosed A := W.isOpen.isClosed_compl
  have hAne : A.Nonempty := by
    by_contra hne
    apply htop
    ext x
    simp only [Set.not_nonempty_iff_eq_empty, A, Set.compl_empty_iff] at hne
    simp [hne]
  obtain ⟨t, htcl, htmax⟩ := exists_maximal_isIrreducible_subset hA hAne
  let α₀ : X := htmax.prop.1.genericPoint
  have hα₀ : closure {α₀} = t := by
    have := htmax.prop.1.isGenericPoint_genericPoint_closure
    rw [htcl.closure_eq] at this
    exact this
  have hWA : (⟨Aᶜ, hA.isOpen_compl⟩ : X.Opens) = W := by
    ext x
    simp [A]
  obtain ⟨U, ⟨u, hu⟩, hrepU⟩ := hext A hA (hWA ▸ hW) α₀ (hα₀ ▸ htmax)
    (X.algClosedPoint α₀) (Scheme.algClosedPointHom_apply X α₀ _)
  have : Etale (B.inclusion.map U.obj.hom) := U.property
  let R : X.Opens := ⟨Set.range (B.inclusion.map U.obj.hom),
    (B.inclusion.map U.obj.hom).isOpenMap.isOpen_range⟩
  have hα₀R : α₀ ∈ R := ⟨u default, by
    change (u ≫ B.inclusion.map U.obj.hom) default = α₀
    rw [hu]
    exact Scheme.algClosedPointHom_apply X α₀ _⟩
  have hα₀W : α₀ ∉ W := by
    have : α₀ ∈ t := hα₀ ▸ subset_closure (Set.mem_singleton α₀)
    exact htmax.prop.2 this
  have hP : P (W ⊔ R) := by
    refine restrictIsRepresentableInEt_openObject_of_forall G (W ⊔ R) fun x hx ↦ ?_
    rcases (TopologicalSpace.Opens.mem_sup).1 hx with hxW | hxR
    · have hrange : Set.range x.hom ⊆ Set.range (Scheme.Opens.ι W) := by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        rwa [Subsingleton.elim y default]
      let l : x.source ⟶ (W : Scheme) := IsOpenImmersion.lift (Scheme.Opens.ι W) x.hom hrange
      refine ⟨openObject B X hX (SmallEtale.final B X hX) W, l, ?_, ?_, hW⟩
      · exact lift_comp_map_openObject_final_hom W x.hom hrange
      · rw [range_map_openObject_final_hom]
        exact fun y hy ↦ Or.inl hy
    · obtain ⟨v, hv⟩ := hxR
      obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
        (B.inclusion.map U.obj.hom) x.hom v hv
      exact ⟨U, l, hl, fun y hy ↦ Or.inr hy, hrepU⟩
  exact hmax (W ⊔ R) hP (lt_of_le_of_ne le_sup_left fun h ↦
    hα₀W (h ▸ (le_sup_right : R ≤ W ⊔ R) hα₀R))

/-- **The representability criterion** (FK I.3.15). Let `X` be a noetherian separated scheme and
`G` an étale sheaf of sets on `X`. Then `G` is representable by a noetherian separated étale
`X`-scheme if and only if `G` has finite stalks and open difference loci. -/
@[weil "thm_fk103_representability_criterion"]
theorem isRepresentableInEt_iff_hasFiniteStalks_and_hasOpenDifferenceLoci
    [IsNoetherian X] [X.IsSeparated] (G : Sheaf (SmallEtale.topology B X hX) (Type u)) :
    IsRepresentableInEt G.obj ↔ HasFiniteStalks G ∧ HasOpenDifferenceLoci G.obj := by
  refine ⟨fun h ↦ ⟨hasFiniteStalks_of_isRepresentableInEt G h, h.hasOpenDifferenceLoci⟩,
    fun ⟨hfin, hG⟩ ↦ isRepresentableInEt_of_forall_closed_exists G ?_⟩
  intro A hA hrep α₀ hα₀ a ha
  let Uc := openObject B X hX (SmallEtale.final B X hX) ⟨Aᶜ, hA.isOpen_compl⟩
  let W : X.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
  have hι : B.inclusion.map Uc.obj.hom = Scheme.Opens.ι W := map_openObject_final_hom W
  have hW : IsOpenImmersion (Scheme.Opens.ι W) := inferInstance
  have : IsOpenImmersion (B.inclusion.map Uc.obj.hom) := by
    rw [hι]
    exact hW
  have hUc : Set.range (B.inclusion.map Uc.obj.hom) = Aᶜ :=
    range_map_openObject_final_hom (B := B) (hX := hX) ⟨Aᶜ, hA.isOpen_compl⟩
  obtain ⟨U, u, -, -, hU⟩ :=
    exists_connectedSpace_restrictIsRepresentableInEt_of_compl G hfin hG Uc hUc hrep hα₀ a ha
  exact ⟨U, u, hU⟩

end SmallEtale

end AlgebraicGeometry

end
