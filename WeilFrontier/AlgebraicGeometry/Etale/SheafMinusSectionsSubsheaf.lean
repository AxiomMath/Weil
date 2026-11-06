module

public import WeilFrontier.Defs.AlgebraicGeometry.Etale.SupportSections
public import WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafOpenDifferenceLoci
public import WeilFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafCoincidenceLocusOpen
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import Weil.Attr
public import WeilFrontier.AlgebraicGeometry.Etale.SupportSections

/-!
# The sections avoiding a set of global sections form a subsheaf

Let `G` be an étale sheaf of sets on a scheme `X` with open difference loci and let
`E ⊆ G(X)` be a set of global sections. For an object `U` of the small étale site,
`G°_E(U) ⊆ G(U)` is the set of sections `σ` with `σ|_{U_c} ≠ e|_{U_c}` for every open connected
component `U_c` of `U` and every `e ∈ E`. When every object of the site is locally connected
(for instance when `X` is locally noetherian), `U ↦ G°_E(U)` is a subsheaf of `G`.

*Stability under restriction.* Let `h : V → U` be a morphism of the site, `σ ∈ G°_E(U)`, and
`V_c` an open connected component of `V`. The image `h(V_c)` is connected, hence lies in a
connected component `U_c` of `U`, which is open. If `(h^* σ)|_{V_c} = e|_{V_c}`, then the
coincidence set of `σ|_{U_c}` and `e|_{U_c}` contains the image of `V_c`; it is open (for any
presheaf) and closed (open difference loci), hence all of the connected `U_c`, and a sheaf is
separated, so `σ|_{U_c} = e|_{U_c}`, a contradiction.

*Sheaf condition.* If the restrictions of `σ ∈ G(U)` along a covering sieve lie in `G°_E`
and `σ|_{U_c} = e|_{U_c}` on an open connected component `U_c`, some arrow `V → U` of the sieve
hits `U_c`; the open connected component of `V` through such a point maps into `U_c`, and
there the restriction of `σ` equals that of `e`, a contradiction.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionsAvoidingSubfunctor`: the subpresheaf `G°_E` of `G`.

## Main results

* `AlgebraicGeometry.SmallEtale.map_mem_sectionsAvoiding`: `G°_E` is stable under the
  restriction maps of `G`.
* `AlgebraicGeometry.SmallEtale.isSheaf_sectionsAvoidingSubfunctor`: `G°_E` is a sheaf.

## Implementation notes

The source works over a connected noetherian `X`, with a finite set `E`. Neither connectedness
of `X` nor finiteness of `E` is used. What is used is that every object of the small étale
site is locally connected, so that its connected components are open; it is a typeclass
assumption, provided by an instance when `X` is locally noetherian (an object étale over `X` is
then locally noetherian). The sheaf condition of the source's form (disjoint unions and
surjective descent) is replaced by the sheaf condition for the small étale topology.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.3
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace SmallEtale

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X}

/-- An object of the small étale site of a locally noetherian scheme is locally connected. -/
instance locallyConnectedSpace_toScheme_obj [IsLocallyNoetherian X] (U : SmallEtale B X hX) :
    LocallyConnectedSpace ((SmallEtale.toScheme B X hX).obj U) := by
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj X hX)) := ‹IsLocallyNoetherian X›
  have : IsLocallyNoetherian ((SmallEtale.toScheme B X hX).obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map U.obj.hom)
  infer_instance

/-- If two sections of a presheaf agree after restriction along `f : V ⟶ U`, then the image of
`f` lies in their coincidence set. -/
theorem range_subset_germCoincidenceSet_of_map_eq (F : (SmallEtale B X hX)ᵒᵖ ⥤ Type u)
    {U V : SmallEtale B X hX} (f : V ⟶ U) {α β : F.obj (op U)}
    (hf : F.map f.op α = F.map f.op β) :
    Set.range ((SmallEtale.toScheme B X hX).map f) ⊆ germCoincidenceSet F α β := by
  set g := (SmallEtale.toScheme B X hX).map f with hg_def
  have hgU : g ≫ B.inclusion.map U.obj.hom = B.inclusion.map V.obj.hom := by
    rw [hg_def, SmallEtale.toScheme_map_comp]
  rintro _ ⟨v, rfl⟩ ū' hū'
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g ū'.hom v hū'.symm
  let y' : (geometricPointFiber B X hX (toBaseGeometricPoint U ū')).obj V :=
    ⟨l, by
      change l ≫ B.inclusion.map V.obj.hom = ū'.hom ≫ B.inclusion.map U.obj.hom
      rw [← hgU, ← Category.assoc, hl]⟩
  let Φ := geometricPointSitePoint B X hX (toBaseGeometricPoint U ū')
  have hlift : Φ.fiber.map f y' = geometricPointLift U ū' := Subtype.ext hl
  have key := Φ.toPresheafFiber_w_apply f y' F
  change Φ.toPresheafFiber U (geometricPointLift U ū') F α =
    Φ.toPresheafFiber U (geometricPointLift U ū') F β
  rw [← hlift, ← key, ← key, hf]

/-- On a connected object, two sections of a sheaf with open difference loci whose coincidence
set is nonempty are equal. -/
theorem eq_of_germCoincidenceSet_nonempty (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hG : HasOpenDifferenceLoci G.obj) {U : SmallEtale B X hX}
    [ConnectedSpace ((SmallEtale.toScheme B X hX).obj U)] {α β : G.obj.obj (op U)}
    (hne : (germCoincidenceSet G.obj α β).Nonempty) : α = β :=
  eq_of_germCoincidenceSet_eq_univ G
    (IsClopen.eq_univ ⟨hG.isClosed α β, isOpen_germCoincidenceSet G.obj α β⟩ hne)

/-- A morphism `f : V ⟶ U` of the small étale site maps the connected component of `V`
through `v` into the connected component of `U` through `f v`. -/
theorem range_openObjectι_comp_subset_connectedComponent {U V : SmallEtale B X hX}
    (f : V ⟶ U) (W : ((SmallEtale.toScheme B X hX).obj V).Opens)
    {v : (SmallEtale.toScheme B X hX).obj V} (hW : (W : Set _) = connectedComponent v) :
    Set.range ((SmallEtale.toScheme B X hX).map (openObjectι B X hX V W ≫ f)).base ⊆
      connectedComponent ((SmallEtale.toScheme B X hX).map f v) := by
  rintro _ ⟨w, rfl⟩
  have hw : ((SmallEtale.toScheme B X hX).map (openObjectι B X hX V W)).base w ∈ (W : Set _) := by
    rw [← openObjectι_range B X hX V W]
    exact ⟨w, rfl⟩
  rw [hW] at hw
  have himage := (isPreconnected_connectedComponent.image _
    ((SmallEtale.toScheme B X hX).map f).continuous.continuousOn).subset_connectedComponent
      (Set.mem_image_of_mem _ (mem_connectedComponent (x := v)))
  rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app]
  exact himage (Set.mem_image_of_mem _ hw)

variable [∀ U : SmallEtale B X hX, LocallyConnectedSpace ((SmallEtale.toScheme B X hX).obj U)]

/-- **`G°_E` is stable under restriction.** For a sheaf of sets `G` on the small étale site with
open difference loci and a set `E` of global sections, the restriction of a section of `G°_E(U)`
along a morphism `V ⟶ U` lies in `G°_E(V)`. -/
@[weil "lem_fk103_sheaf_minus_sections_subsheaf"]
theorem map_mem_sectionsAvoiding (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hG : HasOpenDifferenceLoci G.obj) (E : Set (G.obj.obj (op (SmallEtale.final B X hX))))
    {U V : SmallEtale B X hX} (f : V ⟶ U) {σ : G.obj.obj (op U)}
    (hσ : σ ∈ sectionsAvoiding G.obj E U) :
    G.obj.map f.op σ ∈ sectionsAvoiding G.obj E V := by
  rintro W ⟨v, hW⟩ e he hσW
  let C : ((SmallEtale.toScheme B X hX).obj U).Opens :=
    ⟨connectedComponent ((SmallEtale.toScheme B X hX).map f v), isOpen_connectedComponent⟩
  have hrange := range_openObjectι_comp_subset_connectedComponent f W hW
  let k := factorThroughOpenObject B X hX _ U (openObjectι B X hX V W ≫ f) C hrange
  have hk : k ≫ openObjectι B X hX U C = openObjectι B X hX V W ≫ f :=
    factorThroughOpenObject_fac B X hX _ U (openObjectι B X hX V W ≫ f) C hrange
  have hmap : G.obj.map k.op (G.obj.map (openObjectι B X hX U C).op σ) =
      G.obj.map k.op (globalRestrict G.obj _ e) := by
    rw [globalRestrict_map, ← Functor.map_comp_apply, ← op_comp, hk, op_comp,
      Functor.map_comp_apply, hσW]
  have : ConnectedSpace ((SmallEtale.toScheme B X hX).obj (openObject B X hX U C)) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hne : (germCoincidenceSet G.obj (G.obj.map (openObjectι B X hX U C).op σ)
      (globalRestrict G.obj _ e)).Nonempty := by
    have w : (SmallEtale.toScheme B X hX).obj (openObject B X hX V W) :=
      ⟨v, by rw [SetLike.mem_coe.symm, hW]; exact mem_connectedComponent⟩
    exact ⟨_, range_subset_germCoincidenceSet_of_map_eq G.obj k hmap ⟨w, rfl⟩⟩
  exact hσ C ⟨_, rfl⟩ e he (eq_of_germCoincidenceSet_nonempty G hG hne)

/-- The subpresheaf `U ↦ G°_E(U)` of a sheaf of sets `G` with open difference loci on the
small étale site: the sections avoiding the restrictions of `E` on every open connected
component. -/
def sectionsAvoidingSubfunctor (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hG : HasOpenDifferenceLoci G.obj) (E : Set (G.obj.obj (op (SmallEtale.final B X hX)))) :
    Subfunctor G.obj where
  obj U := sectionsAvoiding G.obj E U.unop
  map f _ hσ := map_mem_sectionsAvoiding G hG E f.unop hσ

@[simp]
lemma sectionsAvoidingSubfunctor_obj (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hG : HasOpenDifferenceLoci G.obj) (E : Set (G.obj.obj (op (SmallEtale.final B X hX))))
    (U : (SmallEtale B X hX)ᵒᵖ) :
    (sectionsAvoidingSubfunctor G hG E).obj U = sectionsAvoiding G.obj E U.unop :=
  rfl

/-- **`G°_E` is an étale sheaf.** For a sheaf of sets `G` on the small étale site with open
difference loci and a set `E` of global sections, the subpresheaf `U ↦ G°_E(U)` of `G` is a
sheaf for the small étale topology. -/
@[weil "lem_fk103_sheaf_minus_sections_subsheaf"]
theorem isSheaf_sectionsAvoidingSubfunctor (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hG : HasOpenDifferenceLoci G.obj) (E : Set (G.obj.obj (op (SmallEtale.final B X hX)))) :
    Presieve.IsSheaf (SmallEtale.topology B X hX)
      (sectionsAvoidingSubfunctor G hG E).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)]
  intro U σ hσ
  rintro W ⟨x, hW⟩ e he hσW
  obtain ⟨V, f, hf, v, hv⟩ := exists_mem_arrows_mem_range B X hX hσ x
  let W' : ((SmallEtale.toScheme B X hX).obj V).Opens :=
    ⟨connectedComponent v, isOpen_connectedComponent⟩
  have hrange : Set.range ((SmallEtale.toScheme B X hX).map
      (openObjectι B X hX V W' ≫ f)).base ⊆ W := by
    have := range_openObjectι_comp_subset_connectedComponent f W' (v := v) rfl
    rwa [hv, ← hW] at this
  let k := factorThroughOpenObject B X hX _ U.unop (openObjectι B X hX V W' ≫ f) W hrange
  have hk : k ≫ openObjectι B X hX U.unop W = openObjectι B X hX V W' ≫ f :=
    factorThroughOpenObject_fac B X hX _ U.unop (openObjectι B X hX V W' ≫ f) W hrange
  apply hf W' ⟨v, rfl⟩ e he
  rw [← Functor.map_comp_apply, ← op_comp, ← hk, op_comp, Functor.map_comp_apply,
    hσW, globalRestrict_map]

/-- The subsheaf `G°_E` of `G`, as a sheaf on the small étale site. -/
def sectionsAvoidingSheaf (G : Sheaf (SmallEtale.topology B X hX) (Type u))
    (hG : HasOpenDifferenceLoci G.obj) (E : Set (G.obj.obj (op (SmallEtale.final B X hX)))) :
    Sheaf (SmallEtale.topology B X hX) (Type u) :=
  ⟨(sectionsAvoidingSubfunctor G hG E).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_sectionsAvoidingSubfunctor G hG E)⟩

end SmallEtale

end AlgebraicGeometry

end
