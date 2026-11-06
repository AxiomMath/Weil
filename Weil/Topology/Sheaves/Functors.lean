module

public import Weil.Attr
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Base change of a direct image along a local homeomorphism

Let `q : V ⟶ W` be a local homeomorphism of topological spaces, `g : Z ⟶ W` a continuous map
and `Z' = V ×_W Z` the fibre product, with projections `g' = pullback.fst q g : Z' ⟶ V` and
`q' = pullback.snd q g : Z' ⟶ Z`. For every sheaf `F` on `Z` (of sets, of abelian groups, or
with values in any concrete category for which `TopCat.Sheaf.pullback` is defined) there is an
isomorphism `q^* g_* F ≅ g'_* q'^* F` of sheaves on `V`, natural in `F`.

The proof goes through the presheaf pullback along an open map `f`, which is the presheaf
`U ↦ P(f(U))` (`IsOpenMap.pullbackIso`). Because `q'(g'⁻¹(U)) = g⁻¹(q(U))`, the presheaves
`q^{-1} g_* F` and `g'_* q'^{-1} F` on `V` are literally equal, so `q^* g_* F` is the
sheafification of `g'_* (q'^{-1} F)`, while `g'_* q'^* F` is the direct image of the
sheafification of `q'^{-1} F`. The comparison map between the two is an isomorphism on every
open `U` on which `q` is injective: on such a `U` the restrictions of both presheaves are
sheaves (they are precompositions of `F` with the image functor of an open embedding), and
the sheafification unit of a presheaf is invertible over an open on which the presheaf is
already a sheaf. These opens form a basis of `V`.

## Main definitions

* `TopCat.Presheaf.pushforwardSheafifyComparison`: the comparison `(f_* P)^# ⟶ f_* (P^#)`.
* `TopCat.Sheaf.pushforwardCompPullbackIsoOfIsLocalHomeomorph`: the natural isomorphism
  `q^* ∘ g_* ≅ g'_* ∘ q'^*`.

## Main results

* `TopCat.Presheaf.isIso_toSheafify_app_of_isSheaf_comp`: the sheafification unit of a
  presheaf is invertible over an open subset on which the presheaf restricts to a sheaf.
* `TopCat.isOpenMap_pullback_snd`: the base change of an open map is open.
* `TopCat.Presheaf.isIso_pushforwardSheafifyComparison_app`: for a local homeomorphism `q`,
  sheafification commutes with `g'_*` on the presheaves `q'^{-1} F`.

## Implementation notes

The isomorphism is assembled from canonical isomorphisms and the comparison map; it is not
shown here to agree with the base-change morphism obtained from the unit and counit of the
adjunctions `q^* ⊣ q_*` and `q'^* ⊣ q'_*`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][freitag-kiehl], I.1
-/

@[expose] public section

noncomputable section

universe w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open scoped AlgebraicGeometry

namespace TopCat

variable (A : Type*) [Category.{w} A] {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA] [HasColimits A]
variable [HasLimits A] [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

theorem _root_.IsOpenMap.functor_isCocontinuous {X Y : TopCat.{w}} {f : X ⟶ Y}
    (hf : IsOpenMap f) :
    hf.functor.IsCocontinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := by
  rw [hf.adjunction.isCocontinuous_iff_coverPreserving]
  exact CoverPreserving.of_isContinuous _ _ _

namespace Presheaf

variable {A}

theorem isIso_toSheafify_app_of_isSheaf_comp {X Y : TopCat.{w}} {ι : Y ⟶ X}
    (hι : IsOpenEmbedding ι) (P : X.Presheaf A)
    (hP : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology Y) (hι.functor.op ⋙ P))
    (U : Opens Y) :
    IsIso ((toSheafify (Opens.grothendieckTopology X) P).app (op (hι.functor.obj U))) := by
  have := hι.functor_isContinuous
  have := hι.isOpenMap.functor_isCocontinuous
  have e := Functor.toSheafify_pullbackSheafificationCompatibility hι.functor A
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) P
  have := isIso_toSheafify (Opens.grothendieckTopology Y) hP
  have : IsIso (Functor.whiskerLeft hι.functor.op
      (toSheafify (Opens.grothendieckTopology X) P)) := by
    rw [← e]
    refine IsIso.comp_isIso' inferInstance ?_
    exact Functor.map_isIso (sheafToPresheaf (Opens.grothendieckTopology Y) A)
      ((hι.functor.pushforwardContinuousSheafificationCompatibility A
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).hom.app P)
  exact NatIso.isIso_app_of_isIso
    (Functor.whiskerLeft hι.functor.op (toSheafify (Opens.grothendieckTopology X) P)) (op U)

end Presheaf

section Topology

variable {V W Z : TopCat.{w}} (q : V ⟶ W) (g : Z ⟶ W)

theorem exists_pullback_fst_snd_eq {a : V} {z : Z} (h : q a = g z) :
    ∃ p : ↑(pullback q g), pullback.fst q g p = a ∧ pullback.snd q g p = z :=
  ⟨(pullbackIsoProdSubtype q g).inv ⟨(a, z), h⟩,
    pullbackIsoProdSubtype_inv_fst_apply q g _, pullbackIsoProdSubtype_inv_snd_apply q g _⟩

theorem pullback_ext_of_fst_snd {p₁ p₂ : ↑(pullback q g)}
    (h₁ : pullback.fst q g p₁ = pullback.fst q g p₂)
    (h₂ : pullback.snd q g p₁ = pullback.snd q g p₂) : p₁ = p₂ := by
  have e : (pullbackIsoProdSubtype q g).hom p₁ = (pullbackIsoProdSubtype q g).hom p₂ := by
    apply Subtype.ext
    exact Prod.ext h₁ h₂
  simpa using congrArg (pullbackIsoProdSubtype q g).inv e

/-- The base change of an open map is open. -/
theorem isOpenMap_pullback_snd (hq : IsOpenMap q) : IsOpenMap (pullback.snd q g) := by
  intro O hO
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨p, hp, rfl⟩
  let e := TopCat.homeoOfIso (pullbackIsoProdSubtype q g)
  have hS : IsOpen (e '' O) := e.isOpenMap O hO
  obtain ⟨T, hT, hTS⟩ := isOpen_induced_iff.mp hS
  have he : ∀ x, ((e x : _) : V × Z) = (pullback.fst q g x, pullback.snd q g x) := fun x => by
    change (((pullbackIsoProdSubtype q g).hom x : _) : V × Z) = _
    rw [pullbackIsoProdSubtype_hom_apply]
  have hpT : (pullback.fst q g p, pullback.snd q g p) ∈ T := by
    rw [← he]
    have : e p ∈ e '' O := ⟨p, hp, rfl⟩
    rw [← hTS] at this
    exact this
  obtain ⟨A, B, hA, hB, haA, hzB, hAB⟩ := isOpen_prod_iff.mp hT _ _ hpT
  refine ⟨B ∩ g ⁻¹' (q '' A), ?_, hB.inter ((hq A hA).preimage g.hom.continuous), hzB, ?_⟩
  · rintro z ⟨hz, a, ha, haz⟩
    obtain ⟨p', hp'1, hp'2⟩ := exists_pullback_fst_snd_eq q g haz
    have : e p' ∈ e '' O := by
      rw [← hTS]
      change ((e p' : _) : V × Z) ∈ T
      rw [he, hp'1, hp'2]
      exact hAB ⟨ha, hz⟩
    obtain ⟨o, ho, heo⟩ := this
    exact ⟨o, ho, by rw [e.injective heo, hp'2]⟩
  · refine ⟨pullback.fst q g p, haA, ?_⟩
    exact (ConcreteCategory.congr_hom pullback.condition p).symm ▸ rfl

theorem injOn_pullback_snd_preimage {U : Set V} (hU : Set.InjOn q U) :
    Set.InjOn (pullback.snd q g) (pullback.fst q g ⁻¹' U) := by
  intro p₁ h₁ p₂ h₂ h
  refine pullback_ext_of_fst_snd q g (hU h₁ h₂ ?_) h
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, pullback.condition,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h]

/-- Taking preimages along `g` after images along the open map `q` is taking images along the
base change of `q` after preimages along the base change of `g`. -/
theorem isOpenMap_functor_comp_map_eq (hq : IsOpenMap q) :
    hq.functor ⋙ Opens.map g =
      Opens.map (pullback.fst q g) ⋙ (isOpenMap_pullback_snd q g hq).functor :=
  CategoryTheory.Functor.ext
    (fun U => Opens.ext (pullback_snd_image_fst_preimage q g (U : Set V)).symm)
    (fun _ _ _ => Subsingleton.elim _ _)

theorem isOpenEmbedding_comp_of_injOn {X Y T : TopCat.{w}} {ι : Y ⟶ X} (hι : IsOpenEmbedding ι)
    {f : X ⟶ T} (hf : IsOpenMap f) (hinj : Set.InjOn f (Set.range ι)) :
    IsOpenEmbedding (ι ≫ f) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (ι ≫ f).hom.continuous ?_ ?_
  · intro a b h
    exact hι.injective (hinj ⟨a, rfl⟩ ⟨b, rfl⟩ h)
  · change IsOpenMap (f ∘ ι)
    exact hf.comp hι.isOpenMap

theorem isOpenEmbedding_functor_comp_eq {X Y T : TopCat.{w}} {ι : Y ⟶ X}
    (hι : IsOpenEmbedding ι) {f : X ⟶ T} (hf : IsOpenMap f) (h : IsOpenEmbedding (ι ≫ f)) :
    hι.functor ⋙ hf.functor = h.functor :=
  CategoryTheory.Functor.ext (fun U => Opens.ext (Set.image_comp f ι (U : Set Y)).symm)
    (fun _ _ _ => Subsingleton.elim _ _)

end Topology

namespace Presheaf

/-- The comparison `(f_* P)^# ⟶ f_* (P^#)` between sheafifying a direct image and taking the
direct image of a sheafification, adjoint to `f_*` of the unit `P ⟶ P^#`. -/
def pushforwardSheafifyComparison {X Y : TopCat.{w}} (f : X ⟶ Y) :
    Presheaf.pushforward A f ⋙ presheafToSheaf (Opens.grothendieckTopology Y) A ⟶
      presheafToSheaf (Opens.grothendieckTopology X) A ⋙ Sheaf.pushforward A f where
  app P := ((sheafificationAdjunction (Opens.grothendieckTopology Y) A).homEquiv _ _).symm
    ((Presheaf.pushforward A f).map (toSheafify (Opens.grothendieckTopology X) P))
  naturality P Q u := by
    have key : ∀ (P' : Y.Presheaf A) (S : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) A)
        (h : P' ⟶ (sheafToPresheaf _ A).obj S),
        toSheafify _ P' ≫ (sheafToPresheaf _ A).map
          (((sheafificationAdjunction (Opens.grothendieckTopology Y) A).homEquiv P' S).symm h) =
          h := fun P' S h => by
      rw [← sheafificationAdjunction_unit_app, ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply]
    apply ((sheafificationAdjunction (Opens.grothendieckTopology Y) A).homEquiv _ _).injective
    simp only [Functor.comp_obj, Functor.comp_map, Adjunction.homEquiv_naturality_right]
    simp only [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
    erw [key]
    rw [Category.assoc]
    erw [← toSheafify_naturality_assoc]
    erw [key]
    have := congrArg (Presheaf.pushforward A f).map
      (toSheafify_naturality (Opens.grothendieckTopology X) u)
    simp only [Functor.map_comp] at this
    exact this

theorem toSheafify_comp_pushforwardSheafifyComparison_app {X Y : TopCat.{w}} (f : X ⟶ Y)
    (P : X.Presheaf A) :
    toSheafify (Opens.grothendieckTopology Y) (f _* P) ≫
        ((pushforwardSheafifyComparison A f).app P).hom =
      (Presheaf.pushforward A f).map (toSheafify (Opens.grothendieckTopology X) P) := by
  have := Adjunction.homEquiv_unit (sheafificationAdjunction (Opens.grothendieckTopology Y) A)
    (X := f _* P) (Y := (Sheaf.pushforward A f).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) A).obj P))
    ((pushforwardSheafifyComparison A f).app P)
  exact this.symm.trans (Equiv.apply_symm_apply _ _)

theorem range_inclusion' {X : TopCat.{w}} (U : Opens X) :
    Set.range U.inclusion' = (U : Set X) := by
  rw [Opens.coe_inclusion']
  exact Subtype.range_coe

/-- Over an open set on which the local homeomorphism `q` is injective, the presheaf
`V₀ ↦ F(q'(V₀))` on the fibre product is a sheaf after restriction, and so is its direct image;
hence sheafification commutes with the direct image along `pullback.fst q g` on such
presheaves. -/
theorem isIso_pushforwardSheafifyComparison_app {V W Z : TopCat.{w}} {q : V ⟶ W} (g : Z ⟶ W)
    (hq : IsLocalHomeomorph q) (F : Z.Sheaf A) :
    IsIso ((pushforwardSheafifyComparison A (pullback.fst q g)).app
      ((isOpenMap_pullback_snd q g hq.isOpenMap).functor.op ⋙ F.obj)) := by
  have hqo := hq.isOpenMap
  have hq'o := isOpenMap_pullback_snd q g hqo
  let B : {U : Opens V // Set.InjOn q U} → Opens V := Subtype.val
  have hB : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro O x hx
    obtain ⟨e, hxe, hfe⟩ := hq x
    refine ⟨O ⊓ ⟨e.source, e.open_source⟩, ⟨⟨_, ?_⟩, rfl⟩, ⟨hx, hxe⟩, inf_le_left⟩
    intro a ha b hb hab
    rw [hfe] at hab
    exact e.injOn ha.2 hb.2 hab
  refine TopCat.Sheaf.isIso_iff_isIso_basis hB ?_
  rintro ⟨U, hU⟩
  dsimp only [B]
  set P := hq'o.functor.op ⋙ F.obj
  have h1 : IsIso ((toSheafify (Opens.grothendieckTopology V)
      ((pullback.fst q g) _* P)).app (op U)) := by
    have hι := U.isOpenEmbedding
    have hemb : IsOpenEmbedding (U.inclusion' ≫ q) :=
      isOpenEmbedding_comp_of_injOn hι hqo (by rwa [range_inclusion'])
    have hs : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology _)
        (hι.functor.op ⋙ ((pullback.fst q g) _* P)) := by
      have e1 := isOpenMap_functor_comp_map_eq q g hqo
      have e2 := isOpenEmbedding_functor_comp_eq hι hqo hemb
      have : hι.functor.op ⋙ ((pullback.fst q g) _* P) =
          (hemb.functor ⋙ Opens.map g).op ⋙ F.obj := by
        rw [← e2, Functor.assoc, e1]
        rfl
      rw [this]
      exact isSheaf_of_isOpenEmbedding hemb (Sheaf.pushforward_sheaf_of_sheaf g F.property)
    have := isIso_toSheafify_app_of_isSheaf_comp hι _ hs ⊤
    rwa [Opens.isOpenEmbedding_obj_top] at this
  have h2 : IsIso ((toSheafify (Opens.grothendieckTopology _) P).app
      (op ((Opens.map (pullback.fst q g)).obj U))) := by
    set U' := (Opens.map (pullback.fst q g)).obj U
    have hι := U'.isOpenEmbedding
    have hemb : IsOpenEmbedding (U'.inclusion' ≫ pullback.snd q g) :=
      isOpenEmbedding_comp_of_injOn hι hq'o
        (by rw [range_inclusion']; exact injOn_pullback_snd_preimage q g hU)
    have hs : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology _)
        (hι.functor.op ⋙ P) := by
      have e2 := isOpenEmbedding_functor_comp_eq hι hq'o hemb
      have : hι.functor.op ⋙ P = hemb.functor.op ⋙ F.obj := by
        rw [← e2]
        rfl
      rw [this]
      exact isSheaf_of_isOpenEmbedding hemb F.property
    have := isIso_toSheafify_app_of_isSheaf_comp hι _ hs ⊤
    rwa [Opens.isOpenEmbedding_obj_top] at this
  have fac := NatTrans.congr_app
    (toSheafify_comp_pushforwardSheafifyComparison_app A (pullback.fst q g) P) (op U)
  rw [NatTrans.comp_app] at fac
  have h3 : IsIso ((toSheafify (Opens.grothendieckTopology V)
      ((pullback.fst q g) _* P)).app (op U) ≫
        ((pushforwardSheafifyComparison A (pullback.fst q g)).app P).hom.app (op U)) := by
    rw [fac]
    exact h2
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h1 h3

end Presheaf

namespace Sheaf

theorem isIso_whiskerLeft_pushforwardSheafifyComparison {V W Z : TopCat.{w}} {q : V ⟶ W}
    (g : Z ⟶ W) (hq : IsLocalHomeomorph q) :
    IsIso (Functor.whiskerLeft
      (forget A Z ⋙ (Functor.whiskeringLeft _ _ A).obj
        (isOpenMap_pullback_snd q g hq.isOpenMap).functor.op)
      (Presheaf.pushforwardSheafifyComparison A (Limits.pullback.fst q g))) := by
  have h : ∀ F : Z.Sheaf A, IsIso ((Functor.whiskerLeft
      (forget A Z ⋙ (Functor.whiskeringLeft _ _ A).obj
        (isOpenMap_pullback_snd q g hq.isOpenMap).functor.op)
      (Presheaf.pushforwardSheafifyComparison A (Limits.pullback.fst q g))).app F) :=
    fun F => Presheaf.isIso_pushforwardSheafifyComparison_app A g hq F
  exact NatIso.isIso_of_isIso_app _

/-- **Base change along a local homeomorphism.** Let `q : V ⟶ W` be a local homeomorphism,
`g : Z ⟶ W` continuous, and `Z' = V ×_W Z` with projections `pullback.fst q g : Z' ⟶ V` and
`pullback.snd q g : Z' ⟶ Z`. Then `q^* g_* ≅ (pullback.fst q g)_* (pullback.snd q g)^*` as
functors from sheaves on `Z` to sheaves on `V`, for sheaves with values in any concrete
category `A` of the kind `TopCat.Sheaf.pullback` allows (sheaves of sets, of abelian groups,
…). -/
@[weil "lem_fk111_space_local_homeomorphism_base_change"]
def pushforwardCompPullbackIsoOfIsLocalHomeomorph {V W Z : TopCat.{w}} {q : V ⟶ W} (g : Z ⟶ W)
    (hq : IsLocalHomeomorph q) :
    pushforward A g ⋙ pullback A q ≅
      pullback A (Limits.pullback.snd q g) ⋙ pushforward A (Limits.pullback.fst q g) :=
  Functor.isoWhiskerLeft (pushforward A g) (pullbackIso A q) ≪≫
    Functor.isoWhiskerLeft (pushforward A g ⋙ forget A W)
      (Functor.isoWhiskerRight hq.isOpenMap.pullbackIso
        (presheafToSheaf (Opens.grothendieckTopology V) A)) ≪≫
    Functor.isoWhiskerLeft (forget A Z)
      (Functor.isoWhiskerRight ((Functor.whiskeringLeft _ _ A).mapIso
        (eqToIso (congrArg Functor.op (isOpenMap_functor_comp_map_eq q g hq.isOpenMap))))
        (presheafToSheaf (Opens.grothendieckTopology V) A)) ≪≫
    @asIso _ _ _ _ (Functor.whiskerLeft
      (forget A Z ⋙ (Functor.whiskeringLeft _ _ A).obj
        (isOpenMap_pullback_snd q g hq.isOpenMap).functor.op)
      (Presheaf.pushforwardSheafifyComparison A (Limits.pullback.fst q g)))
      (isIso_whiskerLeft_pushforwardSheafifyComparison A g hq) ≪≫
    Functor.isoWhiskerLeft (forget A Z)
      (Functor.isoWhiskerRight (isOpenMap_pullback_snd q g hq.isOpenMap).pullbackIso.symm
        (presheafToSheaf (Opens.grothendieckTopology _) A ⋙
          pushforward A (Limits.pullback.fst q g))) ≪≫
    Functor.isoWhiskerRight (pullbackIso A (Limits.pullback.snd q g)).symm
      (pushforward A (Limits.pullback.fst q g))

end Sheaf

end TopCat
