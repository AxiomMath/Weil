module

public import WeilFrontier.AlgebraicGeometry.Etale.SheafMinusSectionsSubsheaf
public import WeilFrontier.AlgebraicGeometry.Etale.SupportSections
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDisjointUnionRepresentable
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.RepresentableEtaleSheaf
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQcqs
public import Weil.Attr

/-!
# An étale sheaf made of finitely many global sections and a representable rest

Let `X` be a connected scheme, `G` an étale sheaf of sets on `X` with open difference loci,
`s₀, …, s_{m-1} ∈ G(X)` pairwise distinct global sections with set `E`, and `W` an object of
the small étale site of `X` together with an isomorphism `θ : W̃ ≅ G°_E` from the sheaf
represented by `W` onto the subsheaf of sections avoiding `E`. Then
`G ≅ (X^{⊔ m} ⊔ W)~`; in particular `G` is representable when `X` and `W` are noetherian and
separated.

The isomorphism is `ψ_U(a) = a^* ζ^{⊔}`, where `ζ^{⊔} ∈ G(X^{⊔ m} ⊔ W)` is the section
restricting to `sᵢ` on the `i`-th copy of `X` and to `ζ = θ_W(id_W)` on `W`. For a connected
object `U`, a morphism `U ⟶ X^{⊔ m} ⊔ W` factors through exactly one member, so
`Hom(U, X^{⊔ m} ⊔ W) = {0, …, m-1} ⊔ Hom(U, W)`, and under this decomposition `ψ_U` is
`i ↦ sᵢ|_U` on the first part and `θ_U` on the second; it is bijective because
`G(U) = {sᵢ|_U} ⊔ G°_E(U)`. A morphism of sheaves bijective on connected objects is an
isomorphism, since connected components cover every object.

## Main definitions

* `AlgebraicGeometry.SmallEtale.copiesFinalSum`: the object `X^{⊔ m} ⊔ W`.

## Main results

* `AlgebraicGeometry.SmallEtale.nonempty_iso_representedSheaf_copiesFinalSum`:
  `G ≅ (X^{⊔ m} ⊔ W)~`.
* `AlgebraicGeometry.SmallEtale.isRepresentableInEt_of_iso_sectionsAvoidingSheaf`: `G` is
  representable by a noetherian separated object.
* `AlgebraicGeometry.SmallEtale.bijective_sigma_comp_disjointUnionHom_of_connectedSpace`:
  morphisms from a connected object into a finite disjoint union.
* `AlgebraicGeometry.SmallEtale.exists_map_disjointUnionHom_eq`: sections over the members of a
  finite disjoint union glue.
* `AlgebraicGeometry.SmallEtale.isIso_of_bijective_app_of_connectedSpace`: a morphism of sheaves
  of sets bijective on connected objects is an isomorphism.
* `AlgebraicGeometry.isSeparated_sigmaObj`, `AlgebraicGeometry.isNoetherian_sigmaObj`: finite
  coproducts of separated (noetherian) schemes are separated (noetherian).

## Implementation notes

The sections are a family `s : Fin m → G(X)` indexed by `0, …, m - 1`, injective, with
`E = Set.range s`. The source works with noetherian schemes; the isomorphism is proved assuming
only that every object of the small étale site is locally connected (an instance when `X` is
locally noetherian) and for an arbitrary object `W`. Noetherianity and separatedness of `X` and
`W` are used only for the representability statement, whose representing object must lie in
`Et(X)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology

universe v u

namespace AlgebraicGeometry

/-- The coproduct of a finite family of separated morphisms, viewed as a morphism between the
coproducts, is separated. -/
theorem isSeparated_sigmaMap {ι : Type v} [Finite ι] {Z Y : ι → Scheme.{u}}
    (g : ∀ j, Z j ⟶ Y j) [∀ j, IsSeparated (g j)] : IsSeparated (Limits.Sigma.map g) := by
  have hg : ∀ j, IsSeparated (g j) := fun j => inferInstance
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsSeparated) (sigmaOpenCover Y) fun j => ?_
  have h : IsSeparated (pullback.snd (Limits.Sigma.map g) (Sigma.ι Y j)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsSeparated
        (isPullback_sigmaMap g j).isoPullback.hom,
      (isPullback_sigmaMap g j).isoPullback_hom_snd]
    exact hg j
  exact h

/-- A finite coproduct of separated schemes is separated. -/
theorem isSeparated_sigmaObj {ι : Type v} [Finite ι] (Z : ι → Scheme.{u})
    [∀ j, (Z j).IsSeparated] : (∐ Z).IsSeparated := by
  have := isSeparated_sigmaMap (fun j => terminal.from (Z j))
  have := isAffineHom_sigmaDesc_id (ι := ι) (⊤_ Scheme.{u})
  refine ⟨?_⟩
  rw [terminal.hom_ext (terminal.from (∐ Z))
    (Limits.Sigma.map (fun j => terminal.from (Z j)) ≫ Sigma.desc (fun _ : ι => 𝟙 _))]
  infer_instance

/-- A finite coproduct of noetherian schemes is noetherian. -/
theorem isNoetherian_sigmaObj {ι : Type v} [Finite ι] [Small.{u} ι] (Z : ι → Scheme.{u})
    (hZ : ∀ j, IsNoetherian (Z j)) : IsNoetherian (∐ Z) := by
  have (j : ι) : CompactSpace (Z j) := (hZ j).toCompactSpace
  have := compactSpace_sigmaObj Z
  have : IsLocallyNoetherian (∐ Z) := by
    rw [isLocallyNoetherian_iff_openCover (sigmaOpenCover Z)]
    intro j
    exact (hZ j).toIsLocallyNoetherian
  exact ⟨⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- **Morphisms from a connected object into a finite disjoint union.** For a connected object
`U` of the small étale site and a finite family `V`, every morphism `U ⟶ ⊔ V_k` factors
uniquely through exactly one of the inclusions `V_k ⟶ ⊔ V_k`. -/
theorem bijective_sigma_comp_disjointUnionHom_of_connectedSpace {n : ℕ}
    (V : Fin n → SmallEtale B X hX) (U : SmallEtale B X hX)
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] :
    Function.Bijective fun p : Σ k, (U ⟶ V k) => p.2 ≫ disjointUnionHom B hX V p.1 := by
  let F := SmallEtale.toScheme B X hX
  let g : Fin n → Scheme.{u} := fun k => F.obj (V k)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (F.obj U))
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ hab
    have hab' : F.map a ≫ Sigma.ι g i = F.map b ≫ Sigma.ι g j := by
      have := congrArg F.map hab
      rwa [Functor.map_comp, Functor.map_comp, toScheme_map_disjointUnionHom,
        toScheme_map_disjointUnionHom] at this
    by_cases hij : i = j
    · subst hij
      have : F.map a = F.map b := (cancel_mono (Sigma.ι g i)).mp hab'
      rw [hom_ext B hX this]
    · exact (isEmpty_of_commSq_sigmaι_of_ne (g := g) ⟨hab'⟩ hij).elim x₀
  · intro a
    let φ : F.obj U ⟶ ∐ g := F.map a
    have hcov : ∀ y : ↥(∐ g), ∃ i, y ∈ Set.range (Sigma.ι g i) := fun y => by
      obtain ⟨k, hk⟩ := (sigmaOpenCover g).exists_eq y
      exact ⟨k, hk⟩
    have huniq : ∀ (y : ↥(∐ g)) (i j : Fin n), y ∈ Set.range (Sigma.ι g i) →
        y ∈ Set.range (Sigma.ι g j) → i = j := by
      intro y i j hi hj
      by_contra hne
      have hd := disjoint_opensRange_sigmaι g i j hne
      exact (eq_bot_iff.mp (disjoint_iff.mp hd) (show y ∈ _ ⊓ _ from ⟨hi, hj⟩) :)
    let idx : F.obj U → Fin n := fun x => Classical.choose (hcov (φ x))
    have hidx_spec : ∀ x, φ x ∈ Set.range (Sigma.ι g (idx x)) := fun x =>
      Classical.choose_spec (hcov (φ x))
    have hidx : Continuous idx := by
      rw [continuous_discrete_rng]
      intro i
      have : idx ⁻¹' {i} = φ ⁻¹' Set.range (Sigma.ι g i) := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => h ▸ hidx_spec x, fun h => huniq _ _ _ (hidx_spec x) h⟩
      rw [this]
      exact (Sigma.ι g i).opensRange.2.preimage φ.continuous
    have hrange : Set.range φ ⊆ Set.range (Sigma.ι g (idx x₀)) := by
      rintro _ ⟨x, rfl⟩
      have hx : idx x = idx x₀ := PreconnectedSpace.constant inferInstance hidx
      exact hx ▸ hidx_spec x
    let b := IsOpenImmersion.lift (Sigma.ι g (idx x₀)) φ hrange
    have hb : b ≫ Sigma.ι g (idx x₀) = φ := IsOpenImmersion.lift_fac _ _ _
    have hb' : b ≫ B.inclusion.map (V (idx x₀)).obj.hom = B.inclusion.map U.obj.hom := by
      rw [← ι_comp_inclusion_map_hom_disjointUnionObj B hX V (idx x₀)]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans
        (Stacks.EtaleCohomology.toScheme_map_comp_hom B hX a))
    refine ⟨⟨idx x₀, mkHom B hX b hb'⟩, ?_⟩
    apply hom_ext B hX
    change F.map (mkHom B hX b hb') ≫ F.map (disjointUnionHom B hX V (idx x₀)) = φ
    rw [toScheme_map_mkHom, toScheme_map_disjointUnionHom]
    exact hb

/-- A sheaf of sets on the small étale site has at most one section over an object with empty
underlying scheme. -/
theorem subsingleton_obj_of_isEmpty (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    {Z : SmallEtale B X hX} (hZ : IsEmpty ((SmallEtale.toScheme B X hX).obj Z)) :
    Subsingleton (F.obj.obj (op Z)) := by
  have hsf := ((isSheaf_iff_isSheaf_of_type _ F.obj).1 F.property) _ (bot_mem_topology B hX hZ)
  refine ⟨fun a b => hsf.isSeparatedFor.ext fun _ f hf => ?_⟩
  exact hf.elim

/-- Sections of a sheaf of sets over the members of a finite disjoint union glue to a section
over the union. -/
theorem exists_map_disjointUnionHom_eq (F : Sheaf (SmallEtale.topology B X hX) (Type v))
    {n : ℕ} (V : Fin n → SmallEtale B X hX) (t : ∀ k, F.obj.obj (op (V k))) :
    ∃ x : F.obj.obj (op (disjointUnionObj B hX V)),
      ∀ k, F.obj.map (disjointUnionHom B hX V k).op x = t k := by
  have hcomp : Presieve.Arrows.Compatible F.obj (disjointUnionHom B hX V) t := by
    intro i j Z a b hab
    by_cases hij : i = j
    · subst hij
      have hu : (SmallEtale.toScheme B X hX).map a = (SmallEtale.toScheme B X hX).map b :=
        (cancel_mono (Sigma.ι (fun k => (SmallEtale.toScheme B X hX).obj (V k)) i)).mp
          (congrArg (SmallEtale.toScheme B X hX).map hab)
      rw [hom_ext B hX hu]
    · have hempty : IsEmpty ((SmallEtale.toScheme B X hX).obj Z) :=
        AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
          (g := fun k => (SmallEtale.toScheme B X hX).obj (V k))
          ⟨congrArg (SmallEtale.toScheme B X hX).map hab⟩ hij
      have := subsingleton_obj_of_isEmpty F hempty
      exact Subsingleton.elim _ _
  have hsf : Presieve.IsSheafFor F.obj (Presieve.ofArrows V (disjointUnionHom B hX V)) :=
    (Presieve.isSheafFor_iff_generate _).2
      ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B X hX) F.obj).1 F.property _
        (ofArrows_disjointUnionHom_mem_topology B hX V))
  obtain ⟨x, hx, -⟩ :=
    (Presieve.isSheafFor_arrows_iff F.obj (disjointUnionHom B hX V)).1 hsf _ hcomp
  exact ⟨x, hx⟩


/-- The family `(X^{⊔ m}, W)` whose disjoint union is `X^{⊔ m} ⊔ W`. -/
abbrev copiesFinalSumFamily (m : ℕ) (W : SmallEtale B X hX) : Fin 2 → SmallEtale B X hX :=
  ![disjointCopies B hX (SmallEtale.final B X hX) m, W]

/-- The object `X^{⊔ m} ⊔ W` of the small étale site of `X`: the disjoint union of `m` copies
of the final object and of `W`. -/
abbrev copiesFinalSum (m : ℕ) (W : SmallEtale B X hX) : SmallEtale B X hX :=
  disjointUnionObj B hX (copiesFinalSumFamily m W)

/-- `X^{⊔ m} ⊔ W` is noetherian and separated when `X` and `W` are. -/
theorem isNoetherianSeparated_copiesFinalSum [IsNoetherian X] [X.IsSeparated] (m : ℕ)
    {W : SmallEtale B X hX} (hW : IsNoetherianSeparated B X hX W) :
    IsNoetherianSeparated B X hX (copiesFinalSum m W) := by
  have : IsNoetherian ((SmallEtale.toScheme B X hX).obj W) := hW.1
  have : ((SmallEtale.toScheme B X hX).obj W).IsSeparated := hW.2
  have : IsNoetherian ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX)) :=
    inferInstanceAs (IsNoetherian X)
  have : ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX)).IsSeparated :=
    inferInstanceAs X.IsSeparated
  have hc : IsNoetherianSeparated B X hX (disjointCopies B hX (SmallEtale.final B X hX) m) :=
    ⟨isNoetherian_sigmaObj _ fun _ => inferInstance, isSeparated_sigmaObj _⟩
  have h : ∀ k, IsNoetherianSeparated B X hX (copiesFinalSumFamily m W k) := by
    intro k
    fin_cases k
    · exact hc
    · exact hW
  have : ∀ k, IsNoetherian ((SmallEtale.toScheme B X hX).obj (copiesFinalSumFamily m W k)) :=
    fun k => (h k).1
  have : ∀ k, ((SmallEtale.toScheme B X hX).obj (copiesFinalSumFamily m W k)).IsSeparated :=
    fun k => (h k).2
  exact ⟨isNoetherian_sigmaObj _ fun _ => inferInstance, isSeparated_sigmaObj _⟩

section LocallyConnected

variable [∀ U : SmallEtale B X hX, LocallyConnectedSpace ((SmallEtale.toScheme B X hX).obj U)]

/-- The connected component of a point of `U`, as an object of the small étale site, open in
`U`. -/
abbrev connectedComponentObject (U : SmallEtale B X hX) (x : (SmallEtale.toScheme B X hX).obj U) :
    SmallEtale B X hX :=
  openObject B X hX U ⟨connectedComponent x, isOpen_connectedComponent⟩


instance connectedSpace_connectedComponentObject (U : SmallEtale B X hX)
    (x : (SmallEtale.toScheme B X hX).obj U) :
    ConnectedSpace ((SmallEtale.toScheme B X hX).obj (connectedComponentObject U x)) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- A sieve containing every arrow out of a connected object is a covering sieve. -/
theorem mem_topology_of_connectedSpace {U : SmallEtale B X hX} (S : Sieve U)
    (hS : ∀ (V : SmallEtale B X hX) (f : V ⟶ U),
      ConnectedSpace ((SmallEtale.toScheme B X hX).obj V) → S f) :
    S ∈ SmallEtale.topology B X hX U := by
  refine mem_topology_of_jointlySurjective fun x => ⟨connectedComponentObject U x,
    openObjectι B X hX U _, hS _ _ inferInstance, ?_⟩
  have h := openObjectι_range B X hX U ⟨connectedComponent x, isOpen_connectedComponent⟩
  change x ∈ Set.range ((SmallEtale.toScheme B X hX).map (openObjectι B X hX U _)).base
  rw [h]
  exact mem_connectedComponent

/-- A morphism of sheaves of sets on the small étale site which is bijective on every
connected object is an isomorphism, when every object is locally connected. -/
theorem isIso_of_bijective_app_of_connectedSpace
    {F G : Sheaf (SmallEtale.topology B X hX) (Type v)} (f : F ⟶ G)
    (hf : ∀ (U : SmallEtale B X hX) [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)],
      Function.Bijective (f.hom.app (op U))) : IsIso f := by
  have : (SmallEtale.topology B X hX).HasSheafCompose (forget (Type v)) := ⟨fun _ hP => hP⟩
  rw [← Sheaf.isLocallyBijective_iff_isIso f]
  refine ⟨⟨fun {U} x y hxy => mem_topology_of_connectedSpace _ fun V g hV => ?_⟩,
    ⟨fun {U} t => mem_topology_of_connectedSpace _ fun V g hV => ?_⟩⟩
  · refine (hf V).1 ?_
    change f.hom.app (op V) (F.obj.map g.op x) = f.hom.app (op V) (F.obj.map g.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  · obtain ⟨a, ha⟩ := (hf V).2 (G.obj.map g.op t)
    exact ⟨a, ha⟩


/-- **A sheaf made of finitely many global sections and a represented rest.** Let `X` be
connected, `G` an étale sheaf of sets with open difference loci, `s : Fin m → G(X)` an injective
family of global sections with range `E`, and `θ : W̃ ≅ G°_E` an isomorphism from the sheaf
represented by `W` onto the subsheaf of sections avoiding `E`. Then `G ≅ (X^{⊔ m} ⊔ W)~`. -/
@[weil "lem_fk103_representable_from_sections_plus_rest"]
theorem nonempty_iso_representedSheaf_copiesFinalSum [ConnectedSpace X]
    (G : Sheaf (SmallEtale.topology B X hX) (Type u)) (hG : HasOpenDifferenceLoci G.obj)
    {m : ℕ} {s : Fin m → G.obj.obj (op (SmallEtale.final B X hX))} (hs : Function.Injective s)
    (W : SmallEtale B X hX)
    (θ : representedSheaf W ≅ sectionsAvoidingSheaf G hG (Set.range s)) :
    Nonempty (G ≅ representedSheaf (copiesFinalSum m W)) := by
  let ζ : G.obj.obj (op W) := (θ.hom.hom.app (op W) (𝟙 W)).1
  obtain ⟨σ, hσ⟩ := exists_map_disjointUnionHom_eq G
    (fun _ : Fin m => SmallEtale.final B X hX) s
  obtain ⟨τ, hτ⟩ := exists_map_disjointUnionHom_eq G (copiesFinalSumFamily m W)
    (Fin.cons (α := fun k => G.obj.obj (op (copiesFinalSumFamily m W k))) σ
      (Fin.cons ζ finZeroElim))
  have hτ₀ : G.obj.map (disjointUnionHom B hX (copiesFinalSumFamily m W) 0).op τ = σ := hτ 0
  have hτ₁ : G.obj.map (disjointUnionHom B hX (copiesFinalSumFamily m W) 1).op τ = ζ := hτ 1
  let ψ : representedSheaf (copiesFinalSum m W) ⟶ G :=
    ObjectProperty.homMk (show (representedSheaf (copiesFinalSum m W)).obj ⟶ G.obj from
      yonedaEquiv.symm τ)
  have hψ : ∀ (U : SmallEtale B X hX) (a : U ⟶ copiesFinalSum m W),
      ψ.hom.app (op U) a = G.obj.map a.op τ := fun _ _ => rfl
  have key : ∀ (U : SmallEtale B X hX) [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)],
      Function.Bijective (ψ.hom.app (op U)) := by
    intro U _
    let π := (SmallEtale.finalIsTerminal B X hX).from U
    let d' : Fin m ⊕ (U ⟶ W) → Σ k, (U ⟶ copiesFinalSumFamily m W k) :=
      Sum.elim (fun i => ⟨0, π ≫ disjointCopiesι B hX (SmallEtale.final B X hX) m i⟩)
        (fun b => ⟨1, b⟩)
    have hd' : Function.Bijective d' := by
      have hc := bijective_comp_disjointCopiesι_of_connectedSpace B hX U m
      constructor
      · refine Function.Injective.sumElim (fun i j h => hc.1 ?_) (fun b b' h => ?_)
          (fun i b h => Fin.zero_ne_one (congrArg Sigma.fst h))
        · exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
        · exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      · rintro ⟨⟨_ | _ | k, hk⟩, a⟩
        · obtain ⟨i, hi⟩ := hc.2 a
          exact ⟨Sum.inl i, congrArg
            (Sigma.mk (β := fun k => U ⟶ copiesFinalSumFamily m W k) 0) hi⟩
        · exact ⟨Sum.inr a, rfl⟩
        · omega
    have hd := (bijective_sigma_comp_disjointUnionHom_of_connectedSpace
      (copiesFinalSumFamily m W) U).comp hd'
    let θU : (U ⟶ W) → sectionsAvoiding G.obj (Set.range s) U := θ.hom.hom.app (op U)
    have hθU : Function.Bijective θU :=
      (((sheafToPresheaf _ _).mapIso θ).app (op U)).toEquiv.bijective
    have h1 := (sumElim_globalRestrict_sectionsAvoiding_bijective G hG hs U).comp
      (Function.bijective_id.sumMap hθU)
    refine (Function.Bijective.of_comp_iff _ hd).1 ?_
    convert h1 using 1
    funext x
    rcases x with i | b
    · change G.obj.map ((π ≫ disjointCopiesι B hX (SmallEtale.final B X hX) m i) ≫
        disjointUnionHom B hX (copiesFinalSumFamily m W) 0).op τ = globalRestrict G.obj U (s i)
      erw [op_comp, Functor.map_comp_apply, hτ₀, op_comp, Functor.map_comp_apply]
      erw [hσ]
      rfl
    · change G.obj.map (b ≫ disjointUnionHom B hX (copiesFinalSumFamily m W) 1).op τ =
        (θ.hom.hom.app (op U) b).1
      erw [op_comp, Functor.map_comp_apply, hτ₁]
      have h := NatTrans.naturality_apply θ.hom.hom b.op (𝟙 W)
      have hb : (representedSheaf W).obj.map b.op (𝟙 W) = b := by
        erw [representedSheaf_map, Category.comp_id]
      erw [hb] at h
      erw [h]
      rfl
  have := isIso_of_bijective_app_of_connectedSpace ψ key
  exact ⟨(asIso ψ).symm⟩


end LocallyConnected

/-- **A sheaf made of finitely many global sections and a represented rest is representable.**
Under the hypotheses of `nonempty_iso_representedSheaf_copiesFinalSum`, with `X` noetherian and
separated and `W` an object of `Et(X)`, the sheaf `G` is representable in `Et(X)`. -/
@[weil "lem_fk103_representable_from_sections_plus_rest"]
theorem isRepresentableInEt_of_iso_sectionsAvoidingSheaf [ConnectedSpace X] [IsNoetherian X]
    [X.IsSeparated]
    (G : Sheaf (SmallEtale.topology B X hX) (Type u)) (hG : HasOpenDifferenceLoci G.obj)
    {m : ℕ} {s : Fin m → G.obj.obj (op (SmallEtale.final B X hX))} (hs : Function.Injective s)
    {W : SmallEtale B X hX} (hW : IsNoetherianSeparated B X hX W)
    (θ : representedSheaf W ≅ sectionsAvoidingSheaf G hG (Set.range s)) :
    IsRepresentableInEt G.obj := by
  obtain ⟨e⟩ := nonempty_iso_representedSheaf_copiesFinalSum G hG hs W θ
  exact ⟨copiesFinalSum m W, isNoetherianSeparated_copiesFinalSum m hW,
    ⟨(sheafToPresheaf _ _).mapIso e.symm⟩⟩

end AlgebraicGeometry.SmallEtale
