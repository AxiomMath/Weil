module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCohomologyIdentityLawTransport
public import Weil.Defs.AlgebraicGeometry.AffineTransitionLimit
public import Weil.Attr

/-!
# Cohomology along a projective limit of schemes, for an arbitrary abelian sheaf

Let `X = lim X_α` be a projective system of schemes with limit, `α₀` an index and `F_{α₀}` an
abelian sheaf on the small étale site of `X_{α₀}`, with inverse images `F_α` on `X_α` (`α ≥ α₀`)
and `F` on `X`. Then for every `i ≥ 0` the canonical maps `H^i(X_α, F_α) → H^i(X, F)` induce a
bijection
`colim_{α ≥ α₀} H^i(X_α, F_α) ≅ H^i(X, F)`.

This is the case of [Stacks, Tag 09YQ] in which the system of sheaves is the system of inverse
images of one sheaf, and it is deduced from
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_pullbackPresentedSystem`.
The one thing to add is the identity law: for the system of inverse images of one sheaf the
transition maps on cohomology form a functor on the index, so that the cohomology groups
`H^i(X_α, F_α)` themselves (and not only their stable parts) form the diagram whose colimit is
taken.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.hasCohomologyIdentityLaw_of_isIso` — a
  presented system whose transition maps at identity indices are isomorphisms satisfies the
  identity law on cohomology.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPullbackLevelCohomologyCocone`
  for a directed inverse system of quasi-compact quasi-separated schemes over a base `S` with
  affine transitions and limit `X`, and an abelian sheaf `G` on `S`,
  `H^p(X, G|_X) = colim_i H^p(X_i, G|_{X_i})`, as a colimit cocone in abelian groups.
* `AlgebraicGeometry.IsProjectiveSystemWithLimit.bijective_colimitDesc_levelCohomologyCocone` —
  the statement above for a projective system of schemes with limit and a sheaf on the stage
  `X_{α₀}`: the map from `colim_{α ≥ α₀} H^p(X_α, F_α)` to `H^p(X, F)` is bijective.

## Implementation notes

The étale site is Mathlib's small étale site `X.smallEtaleTopology`, with coefficients in
`AddCommGrpCat.{u + 1}`, and cohomology is `CategoryTheory.Sheaf.H`; this is the site on which
[Stacks, Tag 09YQ] is available. The canonical map `H^p(X_α, F_α) → H^p(X, F)` is restriction
along the projection `X ⟶ X_α` followed by the canonical identification of the inverse image of
`F_α` with `F` (`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg`).

The indices `α ≥ α₀` are the subtype `Set.Ici α₀`; the restricted cone is still a limit cone,
because the inclusion of `Set.Ici α₀` into a directed set is final.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4.18.
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

section IdentityLaw

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]

/-- The transition of a system along an identity index is injective on cohomology as soon as the
map the system attaches to that index is an isomorphism: restriction along `D.map (𝟙 i)` has a
left inverse, the canonical comparison of the inverse image along it with the identity. -/
theorem injective_etaleCohomologyTransition_id (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (i : Iᵒᵖ) [IsIso (systemTransitionMap F (𝟙 i))] (p : ℕ) :
    Function.Injective (etaleCohomologyTransition F (𝟙 i) p) := by
  have key : ∀ z : Sheaf.H.{u + 1, u + 1} (F.obj i) p,
      Sheaf.H.map ((etaleSheafPullbackComparison.{u, u + 1} (D.obj i) (D.map (𝟙 i))
          (smallEtaleBaseChangeIdOf (D.map (𝟙 i)) (D.map_id i)).symm).hom.app (F.obj i)) p
        (Sheaf.H.map (inv (systemTransitionMap F (𝟙 i))) p
          (etaleCohomologyTransition F (𝟙 i) p z)) = z := by
    intro z
    rw [show etaleCohomologyTransition F (𝟙 i) p z =
        Sheaf.H.map (systemTransitionMap F (𝟙 i)) p
          (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (D.map (𝟙 i)) (F.obj i) p z) from rfl,
      ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, IsIso.hom_inv_id_assoc]
    exact etaleCohomologyRestrictionMap_comparison_eq_self.{u, u + 1, u + 1} (D.map (𝟙 i))
      (smallEtaleBaseChangeIdOf (D.map (𝟙 i)) (D.map_id i)).symm (F.obj i) p z
  intro x y hxy
  rw [← key x, ← key y, hxy]

variable {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]
  {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}

/-- **The identity law on cohomology for a system with invertible identity transitions.** The
transition along an identity index is an idempotent on cohomology (by the cocycle law) and is
injective (`injective_etaleCohomologyTransition_id`), hence the identity. -/
theorem hasCohomologyIdentityLaw_of_isIso (E : PresentedSystem P)
    (h : ∀ i : Iᵒᵖ, IsIso (systemTransitionMap E.sys (𝟙 i))) (p : ℕ) :
    HasCohomologyIdentityLaw E p := fun i x =>
  injective_etaleCohomologyTransition_id E.sys i p
    ((E.transition_comp (𝟙 i) (𝟙 i) p x).trans (by rw [Category.comp_id]))

end IdentityLaw

section PullbackSystem

variable {S : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{u}}
  (G : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1}) (s : ∀ i : Iᵒᵖ, D.obj i ⟶ S)
  (hs : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), s i = D.map a ≫ s j)
  {c : Cone D} (sc : c.pt ⟶ S) (hsc : ∀ i : Iᵒᵖ, sc = conePi c i ≫ s i)

/-- **The identity law for the system of inverse images of one sheaf**: its transitions along
identity indices act as the identity on cohomology, in every degree. -/
theorem hasCohomologyIdentityLaw_pullbackPresentedSystem (p : ℕ) :
    HasCohomologyIdentityLaw (pullbackPresentedSystem G s hs sc hsc) p :=
  hasCohomologyIdentityLaw_of_isIso _ (fun i => by
    change IsIso (systemTransitionMap (pullbackSystem G s hs) (𝟙 i))
    rw [systemTransitionMap_pullbackSystem]
    exact inferInstanceAs (IsIso ((etaleAbelianInverseImageCompIso'.{u, u + 1} _ _ _
      (hs (𝟙 i))).app G).inv)) p

variable [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]

/-- **[Stacks, Tag 09YQ] for the inverse images of one sheaf, as a colimit of groups.** For a
nonempty directed inverse system `(X_i)` of quasi-compact quasi-separated schemes over `S` with
affine transition morphisms and limit `X`, and an abelian sheaf `G` on the small étale site of
`S`, the cohomology `H^p(X, G|_X)` is the colimit of the diagram `i ↦ H^p(X_i, G|_{X_i})`, along
the canonical maps. -/
def isColimitPullbackLevelCohomologyCocone (hc : IsLimit c) (p : ℕ) :
    IsColimit (levelCohomologyCocone (pullbackPresentedSystem G s hs sc hsc) p
      (hasCohomologyIdentityLaw_pullbackPresentedSystem G s hs sc hsc p)) :=
  isColimit_levelCohomologyCocone _ p _
    (isCohomologyColimit_pullbackPresentedSystem G s hs hc sc hsc p)

end PullbackSystem

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

namespace AlgebraicGeometry.IsProjectiveSystemWithLimit

open Stacks.EtaleCohomology Stacks.EtaleCohomology.SmallEtaleLimitCohomology

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (α₀ : I)

/-- The inclusion of the indices `α ≥ α₀`. -/
abbrev iciInclusion : Set.Ici α₀ ⥤ I := (Subtype.mono_coe (· ∈ Set.Ici α₀)).functor

variable (D c) in
/-- The restriction of the projective system to the indices `α ≥ α₀`. -/
abbrev iciDiagram : (Set.Ici α₀)ᵒᵖ ⥤ Scheme.{u} := (iciInclusion α₀).op ⋙ D

variable (c) in
/-- The restriction of the cone to the indices `α ≥ α₀`. -/
abbrev iciCone : Cone (iciDiagram D α₀) := c.whisker (iciInclusion α₀).op

variable (D) in
/-- The transition morphisms `X_α ⟶ X_{α₀}`, `α ≥ α₀`. -/
abbrev iciToBase (α : (Set.Ici α₀)ᵒᵖ) : (iciDiagram D α₀).obj α ⟶ D.obj (op α₀) :=
  D.map (homOfLE α.unop.2).op

theorem iciToBase_comp {α β : (Set.Ici α₀)ᵒᵖ} (a : α ⟶ β) :
    iciToBase D α₀ α = (iciDiagram D α₀).map a ≫ iciToBase D α₀ β := by
  simp only [iciToBase, Functor.comp_map, Functor.op_map, ← D.map_comp]
  rfl

theorem iciCone_π_comp (α : (Set.Ici α₀)ᵒᵖ) :
    c.π.app (op α₀) = conePi (iciCone c α₀) α ≫ iciToBase D α₀ α :=
  (c.w (homOfLE α.unop.2).op).symm

instance [IsDirected I (· ≤ ·)] : IsDirected (Set.Ici α₀) (· ≤ ·) where
  directed a b := by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩

/-- The inclusion of the indices `α ≥ α₀` into a directed set is final. -/
instance final_iciInclusion [IsDirected I (· ≤ ·)] : (iciInclusion α₀).Final := by
  have : IsFilteredOrEmpty (Set.Ici α₀) := inferInstance
  refine Functor.final_of_exists_of_isFiltered _ (fun d => ?_) (fun _ _ => ?_)
  · obtain ⟨k, hdk, hk⟩ := directed_of (· ≤ ·) d α₀
    exact ⟨⟨k, hk⟩, ⟨homOfLE hdk⟩⟩
  · exact ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

variable {α₀}

theorem isDirected_of_isProjectiveSystemWithLimit (h : IsProjectiveSystemWithLimit D c) :
    IsDirected I (· ≤ ·) := by
  have := h.isCofiltered
  have : IsFiltered I := isFiltered_of_isCofiltered_op I
  exact ⟨fun a b => ⟨IsFiltered.max a b, leOfHom (IsFiltered.leftToMax a b),
    leOfHom (IsFiltered.rightToMax a b)⟩⟩

/-- The restriction of a projective system with limit to the indices `α ≥ α₀` is still a limit
cone. -/
def isLimitIciCone (h : IsProjectiveSystemWithLimit D c) : IsLimit (iciCone c α₀) := by
  have := isDirected_of_isProjectiveSystemWithLimit h
  exact (Functor.Initial.isLimitWhiskerEquiv (iciInclusion α₀).op c).symm h.nonempty_isLimit.some

variable (α₀) in
/-- The system of inverse images `F_α = p_{αα₀}^{-1} F_{α₀}`, `α ≥ α₀`, of a sheaf on `X_{α₀}`,
presented on the limit by `F = p_{α₀}^{-1} F_{α₀}`. -/
abbrev iciPullbackPresentedSystem [IsDirected I (· ≤ ·)]
    (F₀ : Sheaf (smallEtaleTopology (D.obj (op α₀))) AddCommGrpCat.{u + 1}) :
    PresentedSystem (c := iciCone c α₀) IsColimitPresentation :=
  pullbackPresentedSystem F₀ (iciToBase D α₀) (fun a => iciToBase_comp α₀ a) (c.π.app (op α₀))
    (iciCone_π_comp α₀)

/-- **Cohomology along a projective limit, for an arbitrary abelian sheaf.** Let `X = lim X_α`
be a projective system of schemes with limit, `α₀` an index and `F_{α₀}` an abelian sheaf on
the small étale site of `X_{α₀}`, with inverse images `F_α` on `X_α` (`α ≥ α₀`) and `F` on `X`.
For every `p`, the cohomology groups `H^p(X_α, F_α)`, `α ≥ α₀`, with the canonical transition
maps, form a diagram whose colimit is `H^p(X, F)` along the canonical maps
`H^p(X_α, F_α) → H^p(X, F)`. -/
def isColimitIciLevelCohomologyCocone (h : IsProjectiveSystemWithLimit D c)
    (F₀ : Sheaf (smallEtaleTopology (D.obj (op α₀))) AddCommGrpCat.{u + 1}) (p : ℕ) :
    letI := isDirected_of_isProjectiveSystemWithLimit h
    IsColimit (levelCohomologyCocone (iciPullbackPresentedSystem α₀ (c := c) F₀) p
      (hasCohomologyIdentityLaw_pullbackPresentedSystem _ _ _ _ _ p)) := by
  let := isDirected_of_isProjectiveSystemWithLimit h
  have : ∀ {i j : (Set.Ici α₀)ᵒᵖ} (a : i ⟶ j), IsAffineHom ((iciDiagram D α₀).map a) :=
    fun a => h.isAffineHom_map _
  have : ∀ i : (Set.Ici α₀)ᵒᵖ, IsNoetherian ((iciDiagram D α₀).obj i) :=
    fun i => h.isNoetherian_obj _
  exact isColimitPullbackLevelCohomologyCocone _ _ _ _ _ (isLimitIciCone h) p

/-- **[FK, I.4.18 1)]** Let `X = lim X_α` be a projective system of schemes with limit, `α₀` an
index and `F_{α₀}` an arbitrary abelian sheaf on the small étale site of `X_{α₀}`, with inverse
images `F_α` on `X_α` and `F` on `X`. For every `p ≥ 0` the canonical maps
`H^p(X_α, F_α) → H^p(X, F)` induce a bijection `colim_{α ≥ α₀} H^p(X_α, F_α) → H^p(X, F)`. -/
@[weil "lem_fk104_cohomology_projective_limits_arbitrary_abelian"]
theorem bijective_colimitDesc_levelCohomologyCocone (h : IsProjectiveSystemWithLimit D c)
    (F₀ : Sheaf (smallEtaleTopology (D.obj (op α₀))) AddCommGrpCat.{u + 1}) (p : ℕ) :
    letI := isDirected_of_isProjectiveSystemWithLimit h
    Function.Bijective (colimit.desc _ (levelCohomologyCocone
      (iciPullbackPresentedSystem α₀ (c := c) F₀) p
      (hasCohomologyIdentityLaw_pullbackPresentedSystem _ _ _ _ _ p))) := by
  let := isDirected_of_isProjectiveSystemWithLimit h
  have hc := isColimitIciLevelCohomologyCocone h F₀ p
  have := IsColimit.hom_isIso (colimit.isColimit _) hc (colimit.coconeMorphism _)
  have : IsIso (colimit.desc _ (levelCohomologyCocone
      (iciPullbackPresentedSystem α₀ (c := c) F₀) p
      (hasCohomologyIdentityLaw_pullbackPresentedSystem _ _ _ _ _ p))) :=
    inferInstanceAs (IsIso ((Cocone.forget _).map (colimit.coconeMorphism _)))
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.IsProjectiveSystemWithLimit
