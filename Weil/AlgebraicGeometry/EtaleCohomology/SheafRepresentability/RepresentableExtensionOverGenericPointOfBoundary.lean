module

public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcomposeBaseChangeAdjunction
public import Weil.AlgebraicGeometry.Etale.SheafMinusSectionsRepresentable
public import Weil.AlgebraicGeometry.EtaleCohomology.RepresentableFromSectionsPlusRest
public import Weil.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.LocalRepresentability
public import Weil.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableOffClosed
public import Weil.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SectionsMorphismSurjectiveGeneric
public import Weil.AlgebraicGeometry.Morphisms.QuasiFinite
public import Weil.Attr

/-!
# Representability extends over the generic point of a component of the boundary

Let `X` be a locally noetherian scheme, `G` an étale sheaf of sets on `X` with finite stalks and
open difference loci, and `A ⊆ X` a closed subset such that `G|_{X ∖ A}` is representable in
`Et(X ∖ A)`. If `ā` is a geometric point of `X` over the generic point `α₀` of an irreducible
component of `A`, then there is a connected étale neighbourhood `(U, ū)` of `ā` such that `G|_U`
is representable in `Et(U)`.

The proof. The `m` elements of the stalk `G_ā` are germs of sections over one étale
neighbourhood `(V, v̄)`; shrinking `V` to a connected component of an affine open of a connected
open neighbourhood of the image `v₀` of `v̄` in which the preimage of `A` has generic point
`v₀`, we get a connected noetherian separated neighbourhood `(U, ū)` with sections
`s₁, …, s_m ∈ G(U)` whose germs exhaust `G_ū`, such that the preimage `A_U` of `A` in `U` has the
image `u₀` of `ū` as generic point. Let `E = {s₁, …, s_m}` and `G°_E ⊆ G|_U` the subsheaf of
sections differing from every `sᵢ` on every connected component.

* Over `A_U` the stalks of `G°_E` are empty: a section of `G°_E` over a connected neighbourhood
  `(W, w̄)` of a geometric point over `A_U` has a germ at a lift of `ū` to `W` (the image of `W`
  is open and contains a specialization of `u₀`, hence `u₀`), which is the germ of some `sᵢ`;
  since the difference loci of `G` are open and `W` is connected, the section is `sᵢ|_W`.
* On `U ∖ A_U`, which lies over `X ∖ A`, the restriction of `G` is representable (by the base
  change of the representing object of `G|_{X ∖ A}`), so `G°_E|_{U ∖ A_U}` is representable.

So `G°_E` is representable on `U`, and `G|_U ≅ (U^{⊔ m} ⊔ W₀)~` is representable.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_connectedSpace_restrictIsRepresentableInEt_of_compl`:
  the statement.
* `AlgebraicGeometry.SmallEtale.RestrictIsRepresentableInEt.of_hom`: if `F|_W` is representable
  and `V ⟶ W` is a morphism with `V` noetherian and separated, then `F|_V` is representable.
* `AlgebraicGeometry.SmallEtale.isEmpty_sheafFiber_sectionsAvoidingSheaf`: the stalks of `H°_E`
  vanish at the geometric points over specializations of a point where the germs of `E`
  exhaust the stalk of `H`.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_of_isEmpty_sheafFiber_sectionsAvoidingSheaf`:
  a sheaf on a connected noetherian separated scheme `S` is representable if, for finitely many
  distinct global sections `E`, it is representable off a closed set `A` over which the stalks
  of `H°_E` are empty.

## Implementation notes

The statement is on the small étale site `AlgebraicGeometry.SmallEtale` of a big étale site,
with geometric points over algebraically closed fields. The open subscheme `X ∖ A` enters as an
object of the small étale site whose structure morphism is an open immersion with image `Aᶜ`;
"`α₀` is the generic point of an irreducible component of `A`" is the maximality of `closure {α₀}`
among the irreducible subsets of `A`. The source assumes `X` noetherian; local noetherianity
suffices. The neighbourhood is moreover noetherian and separated, i.e. an object of `Et(X)`.

The source passes through the inverse image of `G|_U` on the reduced closed subscheme with
support `A_U`, where it identifies the sheaf with `m` copies of the final object. The argument
here stays on `U`: that a section of `G°_E` over a connected neighbourhood of a point of `A_U`
is one of the `sᵢ` is read off directly from a lift of `ū`, which is what the closed-subscheme
detour establishes.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- The source of an open immersion into a noetherian scheme is noetherian. -/
private theorem isNoetherian_of_isOpenImmersion' {Y Z : Scheme.{u}}
    (f : Y ⟶ Z) [IsOpenImmersion f] [IsNoetherian Z] : IsNoetherian Y := by
  have : TopologicalSpace.NoetherianSpace Y := f.isOpenEmbedding.isInducing.noetherianSpace
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  exact (isNoetherian_iff _).2 ⟨inferInstance, inferInstance⟩

/-- A morphism `k : V ⟶ W` of the small étale site of `X`, viewed as an object of the small
étale site of `W`. -/
abbrev homObject {V W : SmallEtale B X hX} (k : V ⟶ W) :
    SmallEtale B W.obj.left.1 W.obj.left.property :=
  ⟨Over.mk k.hom.left, etale_toScheme_map k⟩

/-- Composition with a morphism `k : V ⟶ W` of the small étale site of `X`, as a functor from
the small étale site of `V` to that of `W`. -/
def postcomposeHom {V W : SmallEtale B X hX} (k : V ⟶ W) :
    SmallEtale B V.obj.left.1 V.obj.left.property ⥤
      SmallEtale B W.obj.left.1 W.obj.left.property :=
  smallEtalePostcompose B W.obj.left.1 W.obj.left.property (homObject k)

/-- Composing with `k : V ⟶ W` and then with `W ⟶ X` is composing with `V ⟶ X`. -/
def postcomposeHomIso {V W : SmallEtale B X hX} (k : V ⟶ W) :
    smallEtalePostcompose B X hX V ≅ postcomposeHom k ⋙ smallEtalePostcompose B X hX W :=
  NatIso.ofComponents
    (fun T ↦ (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
      (Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ (T.obj.hom ≫ k.hom.left) ≫ W.obj.hom = T.obj.hom ≫ V.obj.hom
        rw [Category.id_comp, Category.assoc, Over.w k.hom])))
    (fun {T T'} f ↦ by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
      simp)


/-- **Restriction of a representable sheaf along a morphism.** If `F|_W` is representable in
`Et(W)` and `k : V ⟶ W` is a morphism of the small étale site with `V` noetherian and separated,
then `F|_V` is representable in `Et(V)`, by the base change `Y ×_W V` of the representing
object `Y` of `F|_W`. -/
theorem RestrictIsRepresentableInEt.of_hom {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    {V W : SmallEtale B X hX} (k : V ⟶ W) (hV : IsNoetherianSeparated B X hX V)
    (h : RestrictIsRepresentableInEt F W) : RestrictIsRepresentableInEt F V := by
  obtain ⟨Y, hY, ⟨ε⟩⟩ := h
  let adj := postcomposeBaseChangeAdjunction B W.obj.left.1 W.obj.left.property (homObject k)
  let Z : SmallEtale B V.obj.left.1 V.obj.left.property :=
    (smallEtaleBaseChange B (homObject k).obj.hom).obj Y
  refine ⟨Z, ?_, ⟨?_⟩⟩
  · have hp : IsPullback (B.inclusion.map (pullback.fst Y.obj.hom k.hom.left))
        (B.inclusion.map (pullback.snd Y.obj.hom k.hom.left))
        (B.inclusion.map Y.obj.hom) (B.inclusion.map k.hom.left) :=
      (IsPullback.of_hasPullback Y.obj.hom k.hom.left).map B.inclusion
    have : IsNoetherian (B.inclusion.obj Y.obj.left) := hY.1
    have : (B.inclusion.obj Y.obj.left).IsSeparated := hY.2
    have : IsNoetherian ((SmallEtale.toScheme B X hX).obj V) := hV.1
    have : ((SmallEtale.toScheme B X hX).obj V).IsSeparated := hV.2
    have hqc : QuasiCompact (B.inclusion.map Y.obj.hom) :=
      quasiCompact_of_noetherianSpace_source _
    have hsep : IsSeparated (B.inclusion.map Y.obj.hom) := inferInstance
    let g : B.inclusion.obj Z.obj.left ⟶ B.inclusion.obj V.obj.left := B.inclusion.map Z.obj.hom
    have : QuasiCompact g := MorphismProperty.of_isPullback (P := @QuasiCompact) hp hqc
    have : IsSeparated g := MorphismProperty.of_isPullback (P := @IsSeparated) hp hsep
    have : Etale g := Z.property
    have : IsNoetherian (B.inclusion.obj V.obj.left) := hV.1
    have : (B.inclusion.obj V.obj.left).IsSeparated := hV.2
    exact ⟨Scheme.isNoetherian_of_locallyOfFiniteType_of_quasiCompact g,
      Scheme.isSeparated_of_isSeparated_hom g⟩
  · exact adj.compYonedaIso.app Y ≪≫ Functor.isoWhiskerLeft (postcomposeHom k).op ε ≪≫
      Functor.isoWhiskerRight (NatIso.op (postcomposeHomIso k)) F


/-- For an object `U` of the small étale site of `X` and an object `O` of that of `U`, the
small étale site of `O` is that of its image in the small étale site of `X`. -/
def postcomposePostcompose (U : SmallEtale B X hX)
    (O : SmallEtale B U.obj.left.1 U.obj.left.property) :
    SmallEtale B O.obj.left.1 O.obj.left.property ⥤ SmallEtale B X hX :=
  smallEtalePostcompose B X hX ((smallEtalePostcompose B X hX U).obj O)

/-- Composing with `O ⟶ U` and then with `U ⟶ X` is composing with `O ⟶ X`. -/
def smallEtalePostcomposeCompIso (U : SmallEtale B X hX)
    (O : SmallEtale B U.obj.left.1 U.obj.left.property) :
    smallEtalePostcompose B U.obj.left.1 U.obj.left.property O ⋙
        smallEtalePostcompose B X hX U ≅ postcomposePostcompose U O :=
  NatIso.ofComponents
    (fun T ↦ (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
      (Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ T.obj.hom ≫ O.obj.hom ≫ U.obj.hom = (T.obj.hom ≫ O.obj.hom) ≫ U.obj.hom
        rw [Category.id_comp, Category.assoc])))
    (fun {T T'} f ↦ by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
      simp)

/-- `(F|_U)|_O` is representable if and only if `F|_O` is, for `O` an étale `U`-scheme viewed
as an étale `X`-scheme. -/
theorem restrictIsRepresentableInEt_postcompose_iff {F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B X hX) (O : SmallEtale B U.obj.left.1 U.obj.left.property) :
    RestrictIsRepresentableInEt ((smallEtalePostcompose B X hX U).op ⋙ F) O ↔
      RestrictIsRepresentableInEt F ((smallEtalePostcompose B X hX U).obj O) :=
  isRepresentableInEt_congr
    (Functor.isoWhiskerRight (NatIso.op (smallEtalePostcomposeCompIso U O)).symm F)


/-- A Zariski open `W` of an étale `U`-scheme `V`, viewed over `X`, is the Zariski open `W` of
`V` viewed over `X`. -/
def postcomposeOpenObjectIso (U : SmallEtale B X hX)
    (V : SmallEtale B U.obj.left.1 U.obj.left.property)
    (W : ((SmallEtale.toScheme B _ U.obj.left.property).obj V).Opens) :
    (smallEtalePostcompose B X hX U).obj (openObject B _ U.obj.left.property V W) ≅
      openObject B X hX ((smallEtalePostcompose B X hX U).obj V) W :=
  (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
    (Over.isoMk (Iso.refl _) (by
      exact (Category.id_comp _).trans (Category.assoc _ _ _).symm))

theorem postcomposeOpenObjectIso_hom_comp_openObjectι (U : SmallEtale B X hX)
    (V : SmallEtale B U.obj.left.1 U.obj.left.property)
    (W : ((SmallEtale.toScheme B _ U.obj.left.property).obj V).Opens) :
    (postcomposeOpenObjectIso U V W).hom ≫
        openObjectι B X hX ((smallEtalePostcompose B X hX U).obj V) W =
      (smallEtalePostcompose B X hX U).map (openObjectι B _ U.obj.left.property V W) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact Category.id_comp _

/-- The sections avoiding a set `E` of global sections, for the restriction `F|_U` of `F` and
the restrictions of the elements of `E` to `U`, are the sections of `F` avoiding `E`. -/
theorem mem_sectionsAvoiding_postcompose_iff (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    (E : Set (F.obj (op (SmallEtale.final B X hX)))) (U : SmallEtale B X hX)
    (V : SmallEtale B U.obj.left.1 U.obj.left.property)
    (σ : F.obj (op ((smallEtalePostcompose B X hX U).obj V))) :
    σ ∈ sectionsAvoiding ((smallEtalePostcompose B X hX U).op ⋙ F)
        (globalRestrict F ((smallEtalePostcompose B X hX U).obj
          (SmallEtale.final B _ U.obj.left.property)) '' E) V ↔
      σ ∈ sectionsAvoiding F E ((smallEtalePostcompose B X hX U).obj V) := by
  let P := smallEtalePostcompose B X hX U
  rw [mem_sectionsAvoiding_iff, mem_sectionsAvoiding_iff]
  refine forall_congr' fun W ↦ imp_congr_right fun _ ↦ ?_
  simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun e _ ↦ ?_
  let c := postcomposeOpenObjectIso U V W
  have hinj : Function.Injective (F.map c.hom.op) :=
    ((isIso_iff_bijective _).1 (inferInstance : IsIso (F.map c.hom.op))).1
  have h1 : (P.op ⋙ F).map (openObjectι B _ U.obj.left.property V W).op σ =
      F.map c.hom.op (F.map (openObjectι B X hX (P.obj V) W).op σ) := by
    have h := postcomposeOpenObjectIso_hom_comp_openObjectι U V W
    exact (congrArg (fun f ↦ F.map f.op σ) h).symm.trans
      (Functor.map_comp_apply F _ _ σ)
  have h2 : globalRestrict (P.op ⋙ F) (openObject B _ U.obj.left.property V W)
        (globalRestrict F (P.obj (SmallEtale.final B _ U.obj.left.property)) e) =
      F.map c.hom.op (globalRestrict F (openObject B X hX (P.obj V) W) e) := by
    change F.map (P.map _).op (globalRestrict F _ e) = _
    rw [globalRestrict_map, globalRestrict_map]
  rw [h1, h2, hinj.ne_iff]


/-- **Representability from finitely many sections, off a closed set.** Let `S` be connected,
noetherian and separated, `H` an étale sheaf of sets on `S` with open difference loci,
`s₀, …, s_{m-1}` pairwise distinct global sections with set `E`, and `A ⊆ S` with complement
the image of an open immersion `O ⟶ S` in the small étale site. If `H|_O` is representable in
`Et(O)` and the stalks of `H°_E` at all geometric points over `A` are empty, then `H` is
representable in `Et(S)`. -/
theorem isRepresentableInEt_of_isEmpty_sheafFiber_sectionsAvoidingSheaf {S : Scheme.{u}}
    {hS : B.Contains S} [ConnectedSpace S] [IsNoetherian S] [S.IsSeparated]
    (H : smallEtaleTopos.{u, u} B S hS) (hH : HasOpenDifferenceLoci H.obj) {m : ℕ}
    {s : Fin m → H.obj.obj (op (SmallEtale.final B S hS))} (hs : Function.Injective s)
    (A : Set S) (O : SmallEtale B S hS) [IsOpenImmersion (B.inclusion.map O.obj.hom)]
    (hO : Set.range (B.inclusion.map O.obj.hom) = Aᶜ)
    (hrep : RestrictIsRepresentableInEt H.obj O)
    (hempty : ∀ x : GeometricPoint S, x.hom default ∈ A →
      IsEmpty (((geometricPointSitePoint B S hS x).sheafFiber (A := Type u)).obj
        (sectionsAvoidingSheaf H hH (Set.range s)))) :
    IsRepresentableInEt H.obj := by
  obtain ⟨Z, hZ, ⟨ε⟩⟩ := hrep
  let P := smallEtalePostcompose B S hS O
  have : Etale (B.inclusion.map O.obj.hom) := O.property
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj S hS)) :=
    inferInstanceAs (IsLocallyNoetherian S)
  have : IsLocallyNoetherian O.obj.left.1 :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map O.obj.hom)
  have : IsSeparated (B.inclusion.map Z.obj.hom) := by
    have : (B.inclusion.obj Z.obj.left).IsSeparated := hZ.2
    infer_instance
  let E' := globalRestrict H.obj (P.obj (SmallEtale.final B _ O.obj.left.property)) ''
    Set.range s
  have hE' : E'.Finite := (Set.finite_range s).image _
  obtain ⟨Z', hZ', ⟨θ⟩⟩ := isRepresentableInEt_sectionsAvoidingSubfunctorOfIso ε hE' hZ
  let ψ : (sectionsAvoidingSubfunctorOfIso ε hE').toFunctor ≅
      P.op ⋙ (sectionsAvoidingSheaf H hH (Set.range s)).obj :=
    NatIso.ofComponents (fun V ↦ Equiv.toIso (Equiv.subtypeEquivRight fun σ ↦
      mem_sectionsAvoiding_postcompose_iff H.obj (Set.range s) O V.unop σ)) (fun _ ↦ rfl)
  obtain ⟨e⟩ := nonempty_iso_representedSheaf_postcompose_of_range_eq_compl O A hO
    (sectionsAvoidingSheaf H hH (Set.range s)) Z' (θ ≪≫ ψ) hempty
  exact isRepresentableInEt_of_iso_sectionsAvoidingSheaf H hH hs (W := P.obj Z') hZ' e


/-- **Empty stalks of `H°_E` near a geometric point where `E` exhausts the stalk.** Let `H` be an
étale sheaf of sets with open difference loci on a locally noetherian scheme `S`, `ū` a
geometric point of `S` and `s₀, …, s_{m-1}` global sections whose germs at `ū` exhaust the stalk
`H_ū`. Then the stalk of `H°_E`, `E = {s₀, …, s_{m-1}}`, is empty at every geometric point `x̄`
over a specialization of the image of `ū`: a section of `H°_E` over a connected neighbourhood
`(W, w̄)` of `x̄` has a germ at a lift of `ū` to `W`, which is the germ of some `sᵢ`, so it equals
`sᵢ|_W`, which is not in `H°_E(W)`. -/
theorem isEmpty_sheafFiber_sectionsAvoidingSheaf {S : Scheme.{u}} {hS : B.Contains S}
    [IsLocallyNoetherian S] (H : smallEtaleTopos.{u, u} B S hS) (hH : HasOpenDifferenceLoci H.obj)
    {m : ℕ} (s : Fin m → H.obj.obj (op (SmallEtale.final B S hS))) (u : GeometricPoint S)
    (hsu : Set.range (fun i ↦ (geometricPointSitePoint B S hS u).toPresheafFiber
      (SmallEtale.final B S hS) (SmallEtale.finalLift B S hS u) H.obj (s i)) = Set.univ)
    (x : GeometricPoint S) (hx : u.hom default ⤳ x.hom default) :
    IsEmpty (((geometricPointSitePoint B S hS x).sheafFiber (A := Type u)).obj
      (sectionsAvoidingSheaf H hH (Set.range s))) := by
  refine ⟨fun z ↦ ?_⟩
  let T := SmallEtale.toScheme B S hS
  obtain ⟨⟨V⟩, a, -⟩ := Types.jointly_surjective' z
  obtain ⟨p, hp⟩ := V.2
  let v : T.obj V.1 := p default
  let W₀ := connectedComponentObject V.1 v
  let ι : W₀ ⟶ V.1 := openObjectι B S hS V.1 ⟨connectedComponent v, isOpen_connectedComponent⟩
  let σ : H.obj.obj (op W₀) := H.obj.map ι.op a.1
  have hσ : σ ∈ sectionsAvoiding H.obj (Set.range s) W₀ :=
    map_mem_sectionsAvoiding H hH _ ι a.2
  let π₀ : T.obj W₀ ⟶ S := B.inclusion.map W₀.obj.hom
  have : Etale π₀ := W₀.property
  have hxr : x.hom default ∈ Set.range π₀ := by
    obtain ⟨w, hw⟩ : v ∈ Set.range (T.map ι).base := by
      rw [openObjectι_range]
      exact mem_connectedComponent
    refine ⟨w, ?_⟩
    have h1 : T.map ι ≫ B.inclusion.map V.1.obj.hom = π₀ := SmallEtale.toScheme_map_comp B S hS ι
    rw [← h1, Scheme.Hom.comp_apply, hw, ← hp]
    rfl
  obtain ⟨y, hy⟩ := hx.mem_open π₀.isOpenMap.isOpen_range hxr
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed π₀ u.hom y hy
  let p' : (geometricPointFiber B S hS u).obj W₀ := ⟨l, hl⟩
  let Φ := geometricPointSitePoint B S hS u
  let r : W₀ ⟶ SmallEtale.final B S hS := (SmallEtale.finalIsTerminal B S hS).from W₀
  obtain ⟨i, hi⟩ : Φ.toPresheafFiber W₀ p' H.obj σ ∈ Set.range (fun i ↦
      Φ.toPresheafFiber (SmallEtale.final B S hS) (SmallEtale.finalLift B S hS u) H.obj (s i)) :=
    hsu ▸ Set.mem_univ _
  have hgerm : Φ.toPresheafFiber W₀ p' H.obj σ =
      Φ.toPresheafFiber W₀ p' H.obj (globalRestrict H.obj W₀ (s i)) := by
    refine hi.symm.trans ?_
    change _ = Φ.toPresheafFiber W₀ p' H.obj (H.obj.map r.op (s i))
    rw [Φ.toPresheafFiber_w_apply r p' H.obj (s i),
      geometricPointFiber_final_eq B S hS u (Φ.fiber.map r p')]
  have heq : σ = globalRestrict H.obj W₀ (s i) :=
    HasOpenDifferenceLoci.eq_of_germ_eq hH { residueField := u.residueField, hom := l }
      ((germ_eq_germ_iff_toPresheafFiber_eq H.obj σ _ u p').2 hgerm)
  exact (mem_sectionsAvoiding_iff_of_connectedSpace H.obj _ σ).1 hσ (s i) ⟨i, rfl⟩ heq


/-- **FK I.3: representability extends over the generic point of a component of the
boundary.** Let `X` be locally noetherian, `G` an étale sheaf of sets on `X` with finite stalks
and open difference loci, and `A ⊆ X` a subset whose complement is the image of an open
immersion `X ∖ A ⟶ X` in the small étale site such that `G|_{X ∖ A}` is representable in
`Et(X ∖ A)`. Let `ā` be a geometric point of `X` over the generic point `α₀` of an irreducible
component of `A`. Then there is an étale neighbourhood `(U, ū)` of `ā` with `U` connected
(and noetherian and separated) such that `G|_U` is representable in `Et(U)`. -/
@[weil "lem_fk103_representable_extension_over_generic_point_of_boundary"]
theorem exists_connectedSpace_restrictIsRepresentableInEt_of_compl [IsLocallyNoetherian X]
    (G : smallEtaleTopos.{u, u} B X hX) (hfin : HasFiniteStalks G)
    (hG : HasOpenDifferenceLoci G.obj) {A : Set X} (Uc : SmallEtale B X hX)
    [IsOpenImmersion (B.inclusion.map Uc.obj.hom)]
    (hUc : Set.range (B.inclusion.map Uc.obj.hom) = Aᶜ)
    (hrep : RestrictIsRepresentableInEt G.obj Uc) {α₀ : X}
    (hα₀ : Maximal (fun Z : Set X ↦ IsIrreducible Z ∧ Z ⊆ A) (closure {α₀}))
    (a : GeometricPoint X) (ha : a.LiesOver α₀) :
    ∃ (U : SmallEtale B X hX) (_ : (geometricPointFiber B X hX a).obj U),
      ConnectedSpace ((SmallEtale.toScheme B X hX).obj U) ∧ IsNoetherianSeparated B X hX U ∧
      RestrictIsRepresentableInEt G.obj U := by
  classical
  let T := SmallEtale.toScheme B X hX
  let Φ := geometricPointSitePoint B X hX a
  have := hfin a
  set m := Nat.card (Φ.sheafFiber.obj G) with hm
  let en : Fin m ≃ Φ.sheafFiber.obj G := (Finite.equivFin _).symm
  have hA : IsClosed A := by
    rw [← compl_compl A, ← hUc]
    exact (B.inclusion.map Uc.obj.hom).isOpenEmbedding.isOpen_range.isClosed_compl
  -- Step 1: the elements of the stalk are germs of sections over one neighbourhood `(V, v)`.
  obtain ⟨V, v, t, ht⟩ := Φ.exists_toPresheafFiber_eq_of_finite G.obj (fun i ↦ en i)
  let π : T.obj V ⟶ X := B.inclusion.map V.obj.hom
  have : Etale π := V.property
  have : IsLocallyNoetherian (T.obj V) := LocallyOfFiniteType.isLocallyNoetherian π
  let v₀ : T.obj V := v.1 default
  have hv₀ : π v₀ = α₀ := by
    rw [← ha, ← v.2]
    rfl
  -- Step 2: a connected open neighbourhood `V'` of `v₀` in which `π⁻¹(A)` has generic point `v₀`.
  obtain ⟨V', hv₀V', -, hgen⟩ := exists_isConnected_isGenericPoint_preimage π hA hα₀ hv₀
  have hspec : ∀ z ∈ (V' : Set (T.obj V)), π z ∈ A → v₀ ⤳ z := by
    intro z hz hzA
    have : (⟨v₀, hv₀V'⟩ : V') ⤳ ⟨z, hz⟩ :=
      (isGenericPoint_iff_specializes.1 hgen _).2 hzA
    exact this.map continuous_subtype_val
  -- Step 3: an affine open `W ⊆ V'` containing `v₀`, and the connected component `U` of `W`.
  obtain ⟨_, ⟨W, hW, rfl⟩, hv₀W, hWV'⟩ :=
    (T.obj V).isBasis_affineOpens.exists_subset_of_mem_open hv₀V' V'.isOpen
  let Y₁ := openObject B X hX V W
  let ι₁ : Y₁ ⟶ V := openObjectι B X hX V W
  have hrange₁ : Set.range (T.map ι₁) = W := openObjectι_range B X hX V W
  have hv₁ : Set.range v.1 ⊆ Set.range (T.map ι₁) := by
    rintro _ ⟨z, rfl⟩
    rw [hrange₁, Subsingleton.elim z default]
    exact hv₀W
  let l₁ : a.source ⟶ T.obj Y₁ := IsOpenImmersion.lift (T.map ι₁) v.1 hv₁
  have hl₁ : l₁ ≫ T.map ι₁ = v.1 := IsOpenImmersion.lift_fac _ _ _
  let w₀ : T.obj Y₁ := l₁ default
  let C : (T.obj Y₁).Opens := ⟨connectedComponent w₀, isOpen_connectedComponent⟩
  let U := connectedComponentObject Y₁ w₀
  let ι₂ : U ⟶ Y₁ := openObjectι B X hX Y₁ C
  have hrange₂ : Set.range (T.map ι₂) = connectedComponent w₀ := openObjectι_range B X hX Y₁ C
  have hv₂ : Set.range l₁ ⊆ Set.range (T.map ι₂) := by
    rintro _ ⟨z, rfl⟩
    rw [hrange₂, Subsingleton.elim z default]
    exact mem_connectedComponent
  let l : a.source ⟶ T.obj U := IsOpenImmersion.lift (T.map ι₂) l₁ hv₂
  have hl₂ : l ≫ T.map ι₂ = l₁ := IsOpenImmersion.lift_fac _ _ _
  let ι : U ⟶ V := ι₂ ≫ ι₁
  have hTι : T.map ι = T.map ι₂ ≫ T.map ι₁ := T.map_comp _ _
  have : IsOpenImmersion (T.map ι) := by rw [hTι]; infer_instance
  have hl : l ≫ T.map ι = v.1 := by rw [hTι, ← Category.assoc, hl₂, hl₁]
  have hy : l ≫ B.inclusion.map U.obj.hom = a.hom := by
    rw [← SmallEtale.toScheme_map_comp B X hX ι, ← Category.assoc, hl]
    exact v.2
  let y : (geometricPointFiber B X hX a).obj U := ⟨l, hy⟩
  let u₀ : T.obj U := l default
  have hu₀ : T.map ι u₀ = v₀ := by
    change (l ≫ T.map ι) default = _
    rw [hl]
  -- `U` is noetherian and separated.
  have : _root_.AlgebraicGeometry.IsAffine (T.obj Y₁) := hW
  have : Etale (B.inclusion.map Y₁.obj.hom) := Y₁.property
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj X hX)) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian (T.obj Y₁) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map Y₁.obj.hom)
  have : IsNoetherian (T.obj Y₁) := (isNoetherian_iff _).mpr ⟨inferInstance, inferInstance⟩
  have hUN : IsNoetherian (T.obj U) := isNoetherian_of_isOpenImmersion' (T.map ι₂)
  have hUS : (T.obj U).IsSeparated := Scheme.isSeparated_of_isSeparated_hom (T.map ι₂)
  have hUC : ConnectedSpace (T.obj U) := connectedSpace_connectedComponentObject Y₁ w₀
  refine ⟨U, y, hUC, ⟨hUN, hUS⟩, ?_⟩
  -- `u₀` is the generic point of the preimage `A_U` of `A` in `U`.
  let πU : T.obj U ⟶ X := B.inclusion.map U.obj.hom
  have hπU : T.map ι ≫ π = πU := SmallEtale.toScheme_map_comp B X hX ι
  let AU : Set (T.obj U) := πU ⁻¹' A
  have hspecU : ∀ z ∈ AU, u₀ ⤳ z := by
    intro z hz
    have hzV' : T.map ι z ∈ (V' : Set (T.obj V)) := by
      refine hWV' ?_
      rw [← hrange₁]
      exact ⟨T.map ι₂ z, by rw [hTι, Scheme.Hom.comp_apply]⟩
    have hzA : π (T.map ι z) ∈ A := by
      rw [← Scheme.Hom.comp_apply, hπU]
      exact hz
    have := hspec _ hzV' hzA
    rw [← hu₀] at this
    exact (T.map ι).isOpenEmbedding.isInducing.specializes_iff.1 this
  -- Step 4: the restricted sheaf `H = G|_U` and the sections `s_i = t_i|_U`.
  let P := smallEtalePostcompose B X hX U
  let F₀ := SmallEtale.final B _ U.obj.left.property
  let e : P.obj F₀ ≅ U := (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
    (Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ U.obj.hom = 𝟙 _ ≫ U.obj.hom
      rfl))
  have hTe : T.map e.hom = 𝟙 _ := by
    simp [T, e, SmallEtale.toScheme]
    rfl
  let g : P.obj F₀ ⟶ V := e.hom ≫ ι
  have : (smallEtalePostcompose B X hX U).IsContinuous
      (SmallEtale.topology B _ U.obj.left.property) (SmallEtale.topology B X hX) :=
    smallEtalePostcompose_isContinuous B X hX U
  let H := ((smallEtalePostcompose B X hX U).sheafPushforwardContinuous (Type u)
    (SmallEtale.topology B _ U.obj.left.property) (SmallEtale.topology B X hX)).obj G
  let s : Fin m → H.obj.obj (op F₀) := fun i ↦ G.obj.map g.op (t i)
  let y' : GeometricPoint U.obj.left.1 := { residueField := a.residueField, hom := l }
  let q : (geometricPointFiber B X hX a).obj (P.obj F₀) := ⟨l, by
    change l ≫ B.inclusion.map (𝟙 _ ≫ U.obj.hom) = _
    rw [Category.id_comp]
    exact hy⟩
  have hfib : (geometricPointFiber B X hX a).map g q = v := by
    apply Subtype.ext
    change l ≫ T.map (e.hom ≫ ι) = v.1
    erw [Functor.map_comp, hTe, Category.id_comp, hl]
  have hgerm : ∀ i j, germ H.obj (s i) y' = germ H.obj (s j) y' ↔ i = j := by
    intro i j
    change germ (P.op ⋙ G.obj) (s i) y' = germ (P.op ⋙ G.obj) (s j) y' ↔ _
    refine (germ_smallEtalePostcompose_eq_iff G.obj U (s i) (s j) y').trans
      ((germ_eq_germ_iff_toPresheafFiber_eq G.obj (s i) (s j) a q).trans ?_)
    change Φ.toPresheafFiber _ q G.obj (G.obj.map g.op (t i)) =
      Φ.toPresheafFiber _ q G.obj (G.obj.map g.op (t j)) ↔ _
    have h1 : ∀ k, Φ.toPresheafFiber _ q G.obj (G.obj.map g.op (t k)) = en k := fun k ↦
      (Φ.toPresheafFiber_w_apply g q G.obj (t k)).trans
        ((congrArg (fun z ↦ Φ.toPresheafFiber V z G.obj (t k)) hfib).trans (ht k))
    exact ⟨fun h ↦ en.injective ((h1 i).symm.trans (h.trans (h1 j))), fun h ↦ h ▸ rfl⟩
  have hsinj : Function.Injective s := fun i j hij ↦ (hgerm i j).1 (by rw [hij])
  -- The stalk of `H` at `y'` has `m` elements, so the germs of the `s_i` exhaust it.
  let Ψ := geometricPointSitePoint B _ U.obj.left.property y'
  have hx' : y'.map (B.inclusion.map U.obj.hom) = a := by
    change ({ residueField := a.residueField, hom := l ≫ B.inclusion.map U.obj.hom } :
      GeometricPoint X) = a
    rw [hy]
  have hcard : Nat.card (Ψ.presheafFiber.obj H.obj) = m :=
    (Nat.card_congr (Equiv.ofBijective _
      (bijective_etaleStalkRestrictionMap B X hX U y' G.obj))).trans
      (congrArg (fun z ↦ Nat.card ((geometricPointSitePoint B X hX z).presheafFiber.obj G.obj))
        hx')
  have : Finite (Ψ.presheafFiber.obj H.obj) := by
    exact @Finite.of_equiv _ _ (hfin (y'.map (B.inclusion.map U.obj.hom))) (Equiv.ofBijective _
      (bijective_etaleStalkRestrictionMap B X hX U y' G.obj)).symm
  let φ : Fin m → Ψ.presheafFiber.obj H.obj := fun i ↦
    Ψ.toPresheafFiber F₀ (SmallEtale.finalLift B _ _ y') H.obj (s i)
  have hφ : Function.Injective φ := fun i j hij ↦
    (hgerm i j).1 ((germ_eq_germ_iff_toPresheafFiber_eq H.obj (s i) (s j) y'
      (SmallEtale.finalLift B _ _ y')).2 hij)
  have hs : Set.range φ = Set.univ :=
    Set.range_eq_univ.2 (hφ.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])).2
  -- Step 5: the open `O = U ∖ A_U`, and the representability of `H|_O`.
  let TU := SmallEtale.toScheme B _ U.obj.left.property
  have hAU : IsOpen AUᶜ := (hA.preimage πU.continuous).isOpen_compl
  let WO : (TU.obj F₀).Opens := ⟨AUᶜ, hAU⟩
  let O := openObject B _ U.obj.left.property F₀ WO
  have hOim : IsOpenImmersion (TU.map (openObjectι B _ U.obj.left.property F₀ WO)) :=
    isOpenImmersion_openObjectι B _ U.obj.left.property F₀ WO
  have hOι : B.inclusion.map O.obj.hom = TU.map (openObjectι B _ U.obj.left.property F₀ WO) := by
    exact (SmallEtale.toScheme_map_comp_inclusion_map_hom
      (openObjectι B _ U.obj.left.property F₀ WO)).symm.trans
        ((congrArg (_ ≫ ·) (B.inclusion.map_id _)).trans (Category.comp_id _))
  have : IsOpenImmersion (B.inclusion.map O.obj.hom) := by rw [hOι]; exact hOim
  have hOr : Set.range (B.inclusion.map O.obj.hom) = AUᶜ := by
    rw [hOι]
    exact openObjectι_range B _ U.obj.left.property F₀ WO
  -- `O` lies over `X ∖ A`, so `H|_O = G|_O` is representable.
  let PO := P.obj O
  let fO : T.obj PO ⟶ X := B.inclusion.map PO.obj.hom
  have hfO : ∀ z, fO z = πU (B.inclusion.map O.obj.hom z) := fun z ↦ by
    change (B.inclusion.map (O.obj.hom ≫ U.obj.hom)) z = _
    rw [Functor.map_comp]
    rfl
  have hsub : Set.range fO ⊆ Set.range (B.inclusion.map Uc.obj.hom) := by
    rw [hUc]
    rintro _ ⟨z, rfl⟩
    have hz : B.inclusion.map O.obj.hom z ∈ AUᶜ := hOr ▸ ⟨z, rfl⟩
    rw [hfO]
    exact hz
  let L := IsOpenImmersion.lift (B.inclusion.map Uc.obj.hom) fO hsub
  let k : PO ⟶ Uc := ObjectProperty.homMk (Over.homMk (B.inclusion.preimage L)
    (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.map_preimage]
      exact IsOpenImmersion.lift_fac _ _ _)))
  have : IsNoetherian (TU.obj F₀) := hUN
  have : (TU.obj F₀).IsSeparated := hUS
  have hPON : IsNoetherianSeparated B X hX PO :=
    ⟨@isNoetherian_of_isOpenImmersion' _ _
        (TU.map (openObjectι B _ U.obj.left.property F₀ WO)) hOim _,
      @Scheme.isSeparated_of_isSeparated_hom _ _
        (TU.map (openObjectι B _ U.obj.left.property F₀ WO)) _
        (@IsSeparated.isSeparated_of_mono _ _ _ (@IsOpenImmersion.mono _ _ _ hOim))⟩
  have hrepO : RestrictIsRepresentableInEt H.obj O :=
    (restrictIsRepresentableInEt_postcompose_iff (F := G.obj) U O).2 (hrep.of_hom k hPON)
  -- Step 6: the stalks of `H°_E` over `A_U` are empty, and the conclusion.
  have hHG : HasOpenDifferenceLoci H.obj := hG.smallEtalePostcompose U
  have : IsNoetherian U.obj.left.1 := hUN
  have : U.obj.left.1.IsSeparated := hUS
  have : ConnectedSpace U.obj.left.1 := hUC
  have hempty : ∀ x : GeometricPoint U.obj.left.1, x.hom default ∈ AU →
      IsEmpty (((geometricPointSitePoint B _ U.obj.left.property x).sheafFiber
        (A := Type u)).obj (sectionsAvoidingSheaf H hHG (Set.range s))) :=
    fun x hx ↦ isEmpty_sheafFiber_sectionsAvoidingSheaf H hHG s y' hs x (hspecU _ hx)
  exact isRepresentableInEt_of_isEmpty_sheafFiber_sectionsAvoidingSheaf H hHG hsinj AU O hOr
    hrepO hempty

end AlgebraicGeometry.SmallEtale
