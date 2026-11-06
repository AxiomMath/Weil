module

public import StacksFrontier.Algebra.Homology.InjectiveQuasiIsoMap
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import
  WeilFrontier.Defs.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StructureAndBaseChangeMapping
public import Weil.Attr

/-!
# The base change morphism vanishes in low degrees

Let `f : X ⟶ S` and `g : T ⟶ S` be morphisms of schemes, with `f' : X ×_S T ⟶ T` and
`g' : X ×_S T ⟶ X` the projections. Let `G` be a complex of abelian étale sheaves on `X` with
`G^j = 0` for `j ≤ N`, and `(ι, q)` a choice of resolutions: quasi-isomorphisms `ι : G ⟶ I` and
`q : g'^* I ⟶ J` with `I`, `J` bounded below complexes of injective sheaves. Then the source
and the target of the base change morphism `γ : g^* f_* I ⟶ f'_* J` have vanishing cohomology
in degrees `≤ N`: `H^j(g^* f_* I) = 0` and `H^j(f'_* J) = 0` for `j ≤ N`.

The key step is general: a bounded below complex `K` of injective objects of an abelian
category with `H^j(K) = 0` for `j ≤ N` is quasi-isomorphic to a complex of injectives `K''`
with `K''^j = 0` for `j ≤ N`. Indeed, if `K` is strictly `≥ a` and exact at `a`, then the
canonical truncation `τ^{≥ a+1} K` has injective terms (its degree `a + 1` term is the cokernel
of the split monomorphism `K^a ⟶ K^{a+1}`), and `K ⟶ τ^{≥ a+1} K` is a quasi-isomorphism;
one iterates. Both complexes being bounded below complexes of injectives, any additive functor
carries this quasi-isomorphism to a quasi-isomorphism, so `H^j(F(K)) ≅ H^j(F(K'')) = 0`.
For `I` this is applied to `F = g^* f_*`; for `J`, exactness of `g'^*` makes
`g'^* G ⟶ g'^* I ⟶ J` a quasi-isomorphism from a complex vanishing in degrees `≤ N`, and the
key step is applied to `F = f'_*`.

## Main results

* `CochainComplex.exists_quasiIso_injective_isStrictlyGE_of_isGE` — a bounded below complex of
  injectives which is cohomologically `≥ n` is quasi-isomorphic to a complex of injectives
  strictly `≥ n`.
* `CochainComplex.exactAt_mapHomologicalComplex_of_injective` — an additive functor preserves
  acyclicity in degrees `≤ N` of a bounded below complex of injectives.
* `Stacks.EtaleCohomology.isZero_homology_etaleAbelianDirectImage_comp_inverseImage_of_isStrictlyGE`
  — `H^j(g^* f_* I) = 0` for `j ≤ N`.
* `Stacks.EtaleCohomology.isZero_homology_etaleAbelianDirectImage_snd_of_isStrictlyGE` —
  `H^j(f'_* J) = 0` for `j ≤ N`.

## Implementation notes

The fibre product is `CategoryTheory.Limits.pullback f g`, with `g' = pullback.fst f g` and
`f' = pullback.snd f g`, and sheaves are abelian sheaves on Mathlib's small étale site
`X.smallEtaleTopology`, as for `Stacks.EtaleCohomology.etaleAbelianPullbackResolutionBaseChange`.
The source proves the homotopy equivalence `K ≃ K''` by splitting off the cocycles degree by
degree; here the same complex `K''` is reached by iterated canonical truncation, and only the
quasi-isomorphism `K ⟶ K''` is used, through
`CochainComplex.quasiIso_map_of_injective`. Boundedness below of `G` is automatic from
`G^j = 0` for `j ≤ N`.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.6][FreitagKiehl1988]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- A bounded below complex of injectives which is cohomologically `≥ n` is quasi-isomorphic to a
complex of injectives which is strictly `≥ n`. -/
theorem exists_quasiIso_injective_isStrictlyGE_of_isGE (k : ℕ) :
    ∀ (a : ℤ) (K : CochainComplex C ℤ) [K.IsStrictlyGE a] [∀ i, Injective (K.X i)]
      [K.IsGE (a + k)],
      ∃ (L : CochainComplex C ℤ) (φ : K ⟶ L) (_ : QuasiIso φ) (_ : ∀ i, Injective (L.X i)),
        L.IsStrictlyGE (a + k) := by
  induction k with
  | zero => intro a K _ _ _; exact ⟨K, 𝟙 K, inferInstance, inferInstance, by simpa⟩
  | succ k ih =>
    intro a K _ _ _
    have : K.IsGE (a + 1) := K.isGE_of_ge (a + 1) (a + (k + 1 : ℕ)) (by push_cast; lia)
    have hinj : Injective (K.opcycles (a + 1)) :=
      K.injective_opcycles a (a + 1) (K.exactAt_of_isGE (a + 1) a)
    have : ∀ i, Injective ((K.truncGE (a + 1)).X i) := fun i => by
      obtain h | rfl | h := lt_trichotomy i (a + 1)
      · exact ((K.truncGE (a + 1)).isZero_of_isStrictlyGE (a + 1) i h).injective
      · exact Injective.of_iso (K.truncGEXIsoOpcycles (a + 1)).symm hinj
      · exact Injective.of_iso (K.truncGEXIso (a + 1) i h).symm inferInstance
    have : (K.truncGE (a + 1)).IsGE (a + 1 + k) := by
      rw [isGE_iff]
      intro i hi
      rw [← exactAt_iff_of_quasiIsoAt (K.πTruncGE (a + 1)) i]
      exact K.exactAt_of_isGE (a + (k + 1 : ℕ)) i (by push_cast at hi ⊢; lia)
    obtain ⟨L, φ, _, hL, hL'⟩ := ih (a + 1) (K.truncGE (a + 1))
    refine ⟨L, K.πTruncGE (a + 1) ≫ φ, inferInstance, hL, ?_⟩
    have e : a + 1 + (k : ℤ) = a + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at hL'
    exact hL'

/-- **An additive functor preserves acyclicity in low degrees of a bounded below complex of
injectives.** Let `K` be a bounded below complex of injective objects with `H^j(K) = 0` for
`j ≤ N`. Then `H^j(H(K)) = 0` for `j ≤ N`, for every additive functor `H`. -/
theorem exactAt_mapHomologicalComplex_of_injective {D : Type*} [Category* D] [Preadditive D]
    [CategoryWithHomology D] (H : C ⥤ D) [H.Additive] (K : CochainComplex C ℤ) (a N : ℤ)
    [K.IsStrictlyGE a] [∀ i, Injective (K.X i)] (hK : ∀ j ≤ N, K.ExactAt j) (j : ℤ)
    (hj : j ≤ N) : ((H.mapHomologicalComplex _).obj K).ExactAt j := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a + k = max a (N + 1) := ⟨(max a (N + 1) - a).toNat, by lia⟩
  have : K.IsGE (a + k) := by
    rw [isGE_iff]
    intro i hi
    by_cases hia : i < a
    · exact K.exactAt_of_isGE a i hia
    · exact hK i (by lia)
  obtain ⟨L, φ, _, hL, hL'⟩ := exists_quasiIso_injective_isStrictlyGE_of_isGE k a K
  have : L.IsStrictlyGE a := L.isStrictlyGE_of_ge a (a + k) (by lia)
  have := quasiIso_map_of_injective H φ a
  rw [exactAt_iff_of_quasiIsoAt ((H.mapHomologicalComplex _).map φ) j]
  exact ShortComplex.exact_of_isZero_X₂ _
    (H.map_isZero (L.isZero_of_isStrictlyGE (a + k) j (by lia)))

end CochainComplex

open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
attribute [local instance 10001] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

universe u v

namespace Stacks.EtaleCohomology

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (N : ℤ)
  {G I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}
  {J : CochainComplex (Sheaf (pullback f g).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) ℤ}

/-- **The source of the base change morphism vanishes in low degrees.** Let `G` be a complex of
abelian sheaves on `X` with `G^j = 0` for `j ≤ N`, and `ι : G ⟶ I` a quasi-isomorphism to a
bounded below complex of injective sheaves. Then `H^j(g^* f_* I) = 0` for `j ≤ N`. -/
@[weil "lem_fk106_base_change_morphism_vanishes_low_degrees"]
theorem isZero_homology_etaleAbelianDirectImage_comp_inverseImage_of_isStrictlyGE
    [G.IsStrictlyGE (N + 1)] (ι : G ⟶ I) [QuasiIso ι] (a : ℤ) [I.IsStrictlyGE a]
    [∀ n, Injective (I.X n)] (j : ℤ) (hj : j ≤ N) :
    IsZero ((((etaleAbelianDirectImage.{u, v} f ⋙
        etaleAbelianInverseImage.{u, v} g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).homology j) := by
  have hI : ∀ j ≤ N, I.ExactAt j := fun j hj =>
    (exactAt_iff_of_quasiIsoAt ι j).1
      (ShortComplex.exact_of_isZero_X₂ _ (G.isZero_of_isStrictlyGE (N + 1) j (by lia)))
  exact (CochainComplex.exactAt_mapHomologicalComplex_of_injective _ I a N hI j hj).isZero_homology

/-- **The target of the base change morphism vanishes in low degrees.** Let `G` be a complex of
abelian sheaves on `X` with `G^j = 0` for `j ≤ N`, `ι : G ⟶ I` and `q : pr₁^* I ⟶ J`
quasi-isomorphisms. If `J` is a bounded below complex of injective sheaves, then
`H^j(pr₂_* J) = 0` for `j ≤ N`. -/
@[weil "lem_fk106_base_change_morphism_vanishes_low_degrees"]
theorem isZero_homology_etaleAbelianDirectImage_snd_of_isStrictlyGE
    [G.IsStrictlyGE (N + 1)] (ι : G ⟶ I) [QuasiIso ι]
    (q : ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso q] (b : ℤ) [J.IsStrictlyGE b]
    [∀ n, Injective (J.X n)] (j : ℤ) (hj : j ≤ N) :
    IsZero ((((etaleAbelianDirectImage.{u, v} (pullback.snd f g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).homology j) := by
  have : QuasiIso (((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map ι) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have hJ : ∀ j ≤ N, J.ExactAt j := fun j hj =>
    (exactAt_iff_of_quasiIsoAt
      (((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ι ≫ q) j).1
      (ShortComplex.exact_of_isZero_X₂ _
        ((etaleAbelianInverseImage.{u, v} (pullback.fst f g)).map_isZero
          (G.isZero_of_isStrictlyGE (N + 1) j (by lia))))
  exact (CochainComplex.exactAt_mapHomologicalComplex_of_injective _ J b N hJ j hj).isZero_homology

end Stacks.EtaleCohomology

end

