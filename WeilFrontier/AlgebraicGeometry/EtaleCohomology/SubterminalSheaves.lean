module

public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubterminalSheavesSupplement
public import Weil.Attr

/-!
# Subsheaves of representable étale sheaves are representable

Let `X` be a scheme, `Y` an object of the étale category `Et(X)` (an étale `X`-scheme whose
underlying scheme is noetherian and separated) and `G ⊆ Ỹ` a subsheaf of the sheaf `Ỹ = Hom(-, Y)`
represented by `Y`. Then `G` is representable: it is represented by an open subscheme of `Y`,
which is again noetherian and separated.

The proof goes through the fibre of `G ⟶ Ỹ` over the tautological section. Over an object
`a : V ⟶ Y` of the slice at `Y` its sections are the `s ∈ G(V)` with image `a`; it is a sheaf on
the slice site, and it has at most one section over each object because `G(V) ⟶ Ỹ(V)` is
injective. Transported along the equivalence between the small étale site of `Y` and the slice
of the small étale site of `X` at `Y`, it becomes a subterminal sheaf on the small étale site of
`Y`, hence is represented by an open `W ⊆ Y` (Stacks 04HV). A morphism `a : U ⟶ Y` then lifts to
`G(U)` exactly when its image lies in `W`, that is, when it factors through `W ⟶ Y`; so `G` is
isomorphic to the sheaf represented by `W`.

## Main results

* `AlgebraicGeometry.SmallEtale.isSheaf_subsheafFiber`: the fibre over the tautological section
  of a morphism of sheaves `G ⟶ Ỹ` is a sheaf on the slice site at `Y`.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_of_injective`: a subsheaf of `Ỹ`, given by a
  morphism `G ⟶ Ỹ` injective on sections, is representable.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_of_mono`: the same for a monomorphism of
  sheaves `G ⟶ Ỹ`.

## Implementation notes

The source deduces the statement from the representability criterion (finite stalks and open
difference loci); the proof here does not pass through the criterion but identifies the
representing object directly as an open subscheme of `Y`, through Stacks 04HV,
`AlgebraicGeometry.existsUnique_open_of_isSubterminal'`, and the localization equivalence
`AlgebraicGeometry.SmallEtale.localizationEquivalence`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.4
* [Stacks Project, Tag 04HV](https://stacks.math.columbia.edu/tag/04HV)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The fibre of a morphism `φ : F ⟶ Ỹ` over the tautological section: the presheaf on the
slice at `Y` whose sections over `a : W ⟶ Y` are the sections `s ∈ F(W)` with `φ(s) = a`. -/
def subsheafFiber {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} {Y : SmallEtale B X hX}
    (φ : F ⟶ (representedSheaf Y).obj) : (Over Y)ᵒᵖ ⥤ Type u where
  obj W := {s : F.obj (op W.unop.left) // φ.app (op W.unop.left) s = W.unop.hom}
  map {W W'} g := TypeCat.ofHom fun s => ⟨F.map g.unop.left.op s.1, by
    rw [NatTrans.naturality_apply, s.2]
    exact Over.w g.unop⟩
  map_id _ := by ext s; simp
  map_comp f g := by
    ext s
    change F.map (f.unop.left.op ≫ g.unop.left.op) s.1 =
      F.map g.unop.left.op (F.map f.unop.left.op s.1)
    exact F.map_comp_apply _ _ _

/-- The fibre includes into the restriction of `F` to the slice. -/
def subsheafFiberInclusion {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u} {Y : SmallEtale B X hX}
    (φ : F ⟶ (representedSheaf Y).obj) : subsheafFiber φ ⟶ (Over.forget Y).op ⋙ F where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

/-- The fibre over the tautological section of a morphism of sheaves `φ : G ⟶ Ỹ` is a sheaf on
the slice site at `Y`. -/
theorem isSheaf_subsheafFiber {G : Sheaf (SmallEtale.topology B X hX) (Type u)}
    {Y : SmallEtale B X hX} (φ : G ⟶ representedSheaf Y) :
    Presheaf.IsSheaf ((SmallEtale.topology B X hX).over Y) (subsheafFiber φ.hom) := by
  rw [isSheaf_iff_isSheaf_of_type]
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 (G.over Y).property
  have hA := ((isSheaf_iff_isSheaf_of_type _ _).1
    ((representedSheaf Y).over Y).property).isSeparated
  intro W S hS x hx
  obtain ⟨s, hs, hsu⟩ := hF S hS (x.map (subsheafFiberInclusion φ.hom)) (hx.map _)
  have hm : φ.hom.app (op W.left) s = W.hom := by
    refine (hA S hS).ext (fun {T} {f} hf => ?_)
    change (representedSheaf Y).obj.map f.left.op (φ.hom.app _ s) = f.left ≫ W.hom
    have h1 : (representedSheaf Y).obj.map f.left.op (φ.hom.app _ s) =
        φ.hom.app _ (x f hf).1 :=
      (φ.hom.naturality_apply f.left.op s).symm.trans (congrArg (φ.hom.app _) (hs f hf))
    rw [h1]
    exact (x f hf).2.trans (Over.w f).symm
  refine ⟨⟨s, hm⟩, fun _ f hf => Subtype.ext (hs f hf), fun y hy => Subtype.ext ?_⟩
  exact hsu y.1 (fun _ f hf => congrArg Subtype.val (hy f hf))

/-- **Freitag–Kiehl I.4**: let `Y ∈ Et(X)` and let `G` be a subsheaf of `Ỹ`, given by a morphism
of sheaves `φ : G ⟶ Ỹ` with every `G(U) ⟶ Ỹ(U)` injective. Then `G` is representable; it is
represented by an open subscheme of `Y`. -/
@[weil "lem_fk104_subsheaf_of_representable_representable"]
theorem isRepresentableInEt_of_injective {Y : SmallEtale B X hX}
    (hY : IsNoetherianSeparated B X hX Y) (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (φ : G ⟶ representedSheaf Y) (hφ : ∀ U, Function.Injective (φ.hom.app U)) :
    IsRepresentableInEt G.obj := by
  let E := localizationEquivalence B X hX Y
  let P : (SmallEtale B Y.obj.left.obj Y.obj.left.property)ᵒᵖ ⥤ Type u :=
    E.functor.op ⋙ subsheafFiber φ.hom
  have hP : Presheaf.IsSheaf (SmallEtale.topology B Y.obj.left.obj Y.obj.left.property) P :=
    Functor.op_comp_isSheaf E.functor _ _ ⟨_, isSheaf_subsheafFiber φ⟩
  have hsub : ∀ T, Subsingleton ((subsheafFiber φ.hom).obj T) := fun T =>
    ⟨fun a b => Subtype.ext (hφ _ (a.2.trans b.2.symm))⟩
  let P' : smallEtaleTopos.{u, u} B Y.obj.left.obj Y.obj.left.property := ⟨P, hP⟩
  have hP' : IsSubterminal P' := by
    intro Z f g
    ext U x
    exact (hsub _).elim _ _
  obtain ⟨W, ⟨e⟩, -⟩ := existsUnique_open_of_isSubterminal'.{u, 0} B _ _ P' hP'
  have key : ∀ V, Nonempty (P.obj (op V)) ↔
      Set.range (smallEtaleMap B _ _ V) ⊆ (W : Set Y.obj.left.obj) := fun V =>
    (⟨fun ⟨x⟩ => ⟨e.hom.hom.app _ x⟩, fun ⟨x⟩ => ⟨e.inv.hom.app _ x⟩⟩ : _ ↔ _).trans
      (nonempty_openRepresentableSheaf_obj_iff.{u, 0} B _ _ W V)
  have hWB : B.Contains W.toScheme :=
    Scheme.size_lt_of_isOpenImmersion W.ι Y.obj.left.property
  let V0 : SmallEtale B Y.obj.left.obj Y.obj.left.property :=
    ⟨Over.mk (ObjectProperty.homMk W.ι :
      B.obj W.toScheme hWB ⟶ B.obj Y.obj.left.obj Y.obj.left.property),
      show Etale W.ι from inferInstance⟩
  have hV0 : Set.range (smallEtaleMap B _ _ V0) = (W : Set Y.obj.left.obj) := by
    change Set.range W.ι.base = (W : Set Y.obj.left.obj)
    simp only [Scheme.Opens.range_ι]
  obtain ⟨s0⟩ := (key V0).2 hV0.le
  let Z := (postcompose B X hX Y).obj V0
  let ι : Z ⟶ Y := (localizationObj B X hX Y V0).hom
  have hs0 : φ.hom.app (op Z) s0.1 = ι := s0.2
  have hZ : IsNoetherianSeparated B X hX Z := by
    have : IsNoetherian Y.obj.left.obj := hY.1
    have : Y.obj.left.obj.IsSeparated := hY.2
    change IsNoetherian W.toScheme ∧ W.toScheme.IsSeparated
    refine ⟨?_, ?_⟩
    · have : CompactSpace W := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (W : Set Y.obj.left.obj))
      exact ⟨⟩
    · constructor
      rw [← Limits.terminal.comp_from W.ι]
      infer_instance
  have hι : (SmallEtale.toScheme B X hX).map ι = W.ι := rfl
  refine ⟨Z, hZ, ⟨?_⟩⟩
  let α : (representedSheaf Z).obj ⟶ G.obj := yonedaEquiv.symm s0.1
  have hα : ∀ (U : SmallEtale B X hX) (g : U ⟶ Z), α.app (op U) g = G.obj.map g.op s0.1 :=
    fun U g => yonedaEquiv_symm_app_apply _ _ _
  have hφα : ∀ (U : SmallEtale B X hX) (g : U ⟶ Z), φ.hom.app (op U) (α.app (op U) g) = g ≫ ι :=
    fun U g => by
      rw [hα]
      exact (φ.hom.naturality_apply g.op s0.1).trans
        (congrArg ((representedSheaf Y).obj.map g.op) hs0)
  have hbij : ∀ U, Function.Bijective (α.app U) := by
    intro U
    induction U using Opposite.rec with | op U => ?_
    refine ⟨fun (g₁ g₂ : U ⟶ Z) h => ?_, fun t => ?_⟩
    · have h' : g₁ ≫ ι = g₂ ≫ ι :=
        (hφα U g₁).symm.trans ((congrArg (φ.hom.app (op U)) h).trans (hφα U g₂))
      apply (SmallEtale.toScheme B X hX).map_injective
      have h'' : (SmallEtale.toScheme B X hX).map g₁ ≫ W.ι =
          (SmallEtale.toScheme B X hX).map g₂ ≫ W.ι := by
        rw [← hι, ← Functor.map_comp, ← Functor.map_comp, h']
      exact (cancel_mono W.ι).1 h''
    · let a : U ⟶ Y := φ.hom.app (op U) t
      let T : Over Y := Over.mk a
      let t' : (subsheafFiber φ.hom).obj (op T) := ⟨t, rfl⟩
      let V := E.inverse.obj T
      have hne : Nonempty (P.obj (op V)) :=
        ⟨(subsheafFiber φ.hom).map (E.counitIso.hom.app T).op t'⟩
      have hr' : Set.range (smallEtaleMap B _ _ V) ⊆ Set.range W.ι := by
        rw [Scheme.Opens.range_ι]
        exact (key V).1 hne
      let l := IsOpenImmersion.lift W.ι (smallEtaleMap B _ _ V) hr'
      have hl : l ≫ W.ι = smallEtaleMap B _ _ V := IsOpenImmersion.lift_fac _ _ _
      let k : V ⟶ V0 := ObjectProperty.homMk (Over.homMk
        (ObjectProperty.homMk l : V.obj.left ⟶ B.obj W.toScheme hWB)
        (B.inclusion.map_injective (by rw [Functor.map_comp]; exact hl)))
      let h : T ⟶ localizationObj B X hX Y V0 :=
        E.counitIso.inv.app T ≫ (E.functor.map k : _ ⟶ localizationObj B X hX Y V0)
      let g : U ⟶ Z := h.left
      exact ⟨g, hφ (op U) ((hφα U g).trans (Over.w h))⟩
  have : ∀ U, IsIso (α.app U) := fun U => (isIso_iff_bijective _).2 (hbij U)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- **Freitag–Kiehl I.4**: a subsheaf `G ⊆ Ỹ` (a monomorphism of étale sheaves of sets) of the
sheaf represented by an object `Y` of `Et(X)` is representable. -/
@[weil "lem_fk104_subsheaf_of_representable_representable"]
theorem isRepresentableInEt_of_mono {Y : SmallEtale B X hX}
    (hY : IsNoetherianSeparated B X hX Y) {G : Sheaf (SmallEtale.topology B X hX) (Type u)}
    (φ : G ⟶ representedSheaf Y) [Mono φ] : IsRepresentableInEt G.obj :=
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  isRepresentableInEt_of_injective hY G φ (fun _ ↦ (mono_iff_injective _).1 inferInstance)

end AlgebraicGeometry.SmallEtale

end
