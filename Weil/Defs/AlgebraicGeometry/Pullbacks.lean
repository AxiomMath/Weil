module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Weil.Attr

/-!
# The descent sequence of morphisms of schemes

Let `f : T ⟶ S` be a morphism of schemes and `X`, `X'` schemes over `S`. Write
`X_T = X ×_S T` and `X_{T ×_S T} = X ×_S (T ×_S T)`, and let `p₁, p₂ : T ×_S T ⟶ T` be the two
projections. The descent sequence of morphisms is the diagram of sets
```
Hom_S(X, X') ⟶ Hom_T(X_T, X'_T) ⇉ Hom_{T ×_S T}(X_{T ×_S T}, X'_{T ×_S T})
```
whose first map is base change `u ↦ u ×_S id_T` and whose two parallel maps send a
`T`-morphism `g` to the `T ×_S T`-morphism with components `π_{X'} ∘ g ∘ (id_X × p_k)` and the
projection to `T ×_S T`. It is *exact* when the first map is injective with image the set of
`g` equalised by the two parallel maps.

Exactness of this diagram is the sheaf condition, in `Over S`, of the representable presheaf
of `X'` for the singleton presieve on the projection `X_T ⟶ X`. We do not introduce a new
predicate: we define the maps of the diagram and prove that the Mathlib sheaf condition
`Presieve.IsSheafFor (yoneda.obj X') (Presieve.singleton (baseChangeProj f X))` is equivalent
to the exactness of the diagram as stated in the source.

## Main definitions

* `AlgebraicGeometry.DescentSequence.baseChangeHom`: the first map `u ↦ u_T`.
* `AlgebraicGeometry.DescentSequence.pullbackHom`: the map `g ↦ p^* g` for a morphism
  `p : T ×_S T ⟶ T` over `S` (applied to `p₁ = pullback.fst f f` and `p₂ = pullback.snd f f`).
* `AlgebraicGeometry.DescentSequence.baseChangeProj`: the projection `X_T ⟶ X` in `Over S`.

## Main results

* `AlgebraicGeometry.DescentSequence.isSheafFor_singleton_iff`: the sheaf condition of
  `yoneda.obj X'` for the singleton presieve on `X_T ⟶ X` holds iff the descent sequence is
  exact (base change is injective and its image is the equaliser of `p₁^*` and `p₂^*`).
* `AlgebraicGeometry.DescentSequence.pullbackHom_baseChangeHom`: the image of base change lies
  in the equaliser.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Appendix A III, (∗).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

/- with the Mathlib version used here, `simp` does not use
`pullback.lift_fst`/`pullback.lift_snd` here, so they are added locally. -/
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

namespace AlgebraicGeometry.DescentSequence

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- The morphism `T ×_S T ⟶ S`, `q = f ∘ p₁ = f ∘ p₂`. -/
abbrev doubleStructure : pullback f f ⟶ S := pullback.fst f f ≫ f

/-- The first map `Hom_S(X, X') ⟶ Hom_T(X_T, X'_T)` of the descent sequence, `u ↦ u ×_S id_T`. -/
@[weil "def_fka3_descent_sequence_schemes"]
def baseChangeHom (X X' : Over S) (u : X ⟶ X') :
    (Over.pullback f).obj X ⟶ (Over.pullback f).obj X' :=
  (Over.pullback f).map u

@[simp]
lemma baseChangeHom_left_fst (X X' : Over S) (u : X ⟶ X') :
    (baseChangeHom f X X' u).left ≫ pullback.fst X'.hom f = pullback.fst X.hom f ≫ u.left := by
  simp [baseChangeHom]

@[simp]
lemma baseChangeHom_left_snd (X X' : Over S) (u : X ⟶ X') :
    (baseChangeHom f X X' u).left ≫ pullback.snd X'.hom f = pullback.snd X.hom f := by
  simp [baseChangeHom]

/-- The morphism `id_X × p : X ×_S (T ×_S T) ⟶ X ×_S T` induced by `p : T ×_S T ⟶ T` over `S`. -/
def idProd (X : Over S) (p : pullback f f ⟶ T) (hp : p ≫ f = doubleStructure f) :
    pullback X.hom (doubleStructure f) ⟶ pullback X.hom f :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
    rw [pullback.condition, Category.assoc, hp])

@[reassoc (attr := simp)]
lemma idProd_fst (X : Over S) (p : pullback f f ⟶ T) (hp : p ≫ f = doubleStructure f) :
    idProd f X p hp ≫ pullback.fst X.hom f = pullback.fst _ _ := by
  simp [idProd]

@[reassoc (attr := simp)]
lemma idProd_snd (X : Over S) (p : pullback f f ⟶ T) (hp : p ≫ f = doubleStructure f) :
    idProd f X p hp ≫ pullback.snd X.hom f = pullback.snd _ _ ≫ p := by
  simp [idProd]

/-- For `p : T ×_S T ⟶ T` over `S` and a `T`-morphism `g : X_T ⟶ X'_T`, the
`T ×_S T`-morphism `p^* g : X_{T ×_S T} ⟶ X'_{T ×_S T}` with components
`π_{X'} ∘ g ∘ (id_X × p)` and the projection to `T ×_S T`. -/
@[weil "def_fka3_descent_sequence_schemes"]
def pullbackHom (X X' : Over S) (p : pullback f f ⟶ T) (hp : p ≫ f = doubleStructure f)
    (g : (Over.pullback f).obj X ⟶ (Over.pullback f).obj X') :
    (Over.pullback (doubleStructure f)).obj X ⟶ (Over.pullback (doubleStructure f)).obj X' :=
  Over.homMk
    (pullback.lift (idProd f X p hp ≫ g.left ≫ pullback.fst X'.hom f) (pullback.snd _ _) (by
      have hg : g.left ≫ pullback.snd X'.hom f = pullback.snd X.hom f := Over.w g
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% hg, idProd_snd_assoc, hp]))
    (by simp)

@[reassoc (attr := simp)]
lemma pullbackHom_left_fst (X X' : Over S) (p : pullback f f ⟶ T)
    (hp : p ≫ f = doubleStructure f) (g : (Over.pullback f).obj X ⟶ (Over.pullback f).obj X') :
    (pullbackHom f X X' p hp g).left ≫ pullback.fst _ _ =
      idProd f X p hp ≫ g.left ≫ pullback.fst X'.hom f := by
  simp [pullbackHom]

@[reassoc (attr := simp)]
lemma pullbackHom_left_snd (X X' : Over S) (p : pullback f f ⟶ T)
    (hp : p ≫ f = doubleStructure f) (g : (Over.pullback f).obj X ⟶ (Over.pullback f).obj X') :
    (pullbackHom f X X' p hp g).left ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [pullbackHom]

lemma fst_comp_eq : pullback.fst f f ≫ f = doubleStructure f := rfl

lemma snd_comp_eq : pullback.snd f f ≫ f = doubleStructure f := pullback.condition.symm

/-- `p₁^* g = p₂^* g` iff the two `X'`-components agree. -/
lemma pullbackHom_fst_eq_snd_iff (X X' : Over S)
    (g : (Over.pullback f).obj X ⟶ (Over.pullback f).obj X') :
    pullbackHom f X X' _ (fst_comp_eq f) g = pullbackHom f X X' _ (snd_comp_eq f) g ↔
      idProd f X _ (fst_comp_eq f) ≫ g.left ≫ pullback.fst X'.hom f =
        idProd f X _ (snd_comp_eq f) ≫ g.left ≫ pullback.fst X'.hom f := by
  constructor
  · intro h
    rw [← pullbackHom_left_fst, ← pullbackHom_left_fst, h]
  · intro h
    ext
    apply pullback.hom_ext
    · simpa using h
    · simp

/-- The image of base change lies in the equaliser of `p₁^*` and `p₂^*`. -/
lemma pullbackHom_baseChangeHom (X X' : Over S) (u : X ⟶ X') :
    pullbackHom f X X' _ (fst_comp_eq f) (baseChangeHom f X X' u) =
      pullbackHom f X X' _ (snd_comp_eq f) (baseChangeHom f X X' u) := by
  rw [pullbackHom_fst_eq_snd_iff]
  simp

/-- The object `X_T` of `Over S`, with structure morphism `X_T ⟶ T ⟶ S`. -/
abbrev baseChangeOver (X : Over S) : Over S := Over.mk (pullback.snd X.hom f ≫ f)

/-- The projection `π_X : X_T ⟶ X`, as a morphism of `Over S`. -/
def baseChangeProj (X : Over S) : baseChangeOver f X ⟶ X :=
  Over.homMk (pullback.fst X.hom f) pullback.condition

@[simp]
lemma baseChangeProj_left (X : Over S) : (baseChangeProj f X).left = pullback.fst X.hom f := rfl

/-- `T`-morphisms `X_T ⟶ X'_T` are the same as `S`-morphisms `X_T ⟶ X'`, by the universal
property of `X'_T = X' ×_S T`. -/
def homEquiv (X X' : Over S) :
    ((Over.pullback f).obj X ⟶ (Over.pullback f).obj X') ≃ (baseChangeOver f X ⟶ X') where
  toFun g := Over.homMk (g.left ≫ pullback.fst X'.hom f) (by
    have hg : g.left ≫ pullback.snd X'.hom f = pullback.snd X.hom f := Over.w g
    simp only [Category.assoc, Over.mk_hom]
    rw [pullback.condition, reassoc_of% hg])
  invFun x := Over.homMk (pullback.lift x.left (pullback.snd X.hom f) (by simp))
    (by simp)
  left_inv g := by
    have hg : g.left ≫ pullback.snd X'.hom f = pullback.snd X.hom f := Over.w g
    ext
    apply pullback.hom_ext <;> simp [hg]
  right_inv x := by
    ext
    simp

@[simp]
lemma homEquiv_apply_left (X X' : Over S)
    (g : (Over.pullback f).obj X ⟶ (Over.pullback f).obj X') :
    (homEquiv f X X' g).left = g.left ≫ pullback.fst X'.hom f := rfl

lemma homEquiv_baseChangeHom (X X' : Over S) (u : X ⟶ X') :
    homEquiv f X X' (baseChangeHom f X X' u) = baseChangeProj f X ≫ u := by
  ext
  simp

/-- The object `X_{T ×_S T}` of `Over S`. -/
abbrev doubleBaseChangeOver (X : Over S) : Over S :=
  Over.mk (pullback.snd X.hom (doubleStructure f) ≫ doubleStructure f)

/-- `id_X × p`, as a morphism of `Over S`. -/
def idProdOver (X : Over S) (p : pullback f f ⟶ T) (hp : p ≫ f = doubleStructure f) :
    doubleBaseChangeOver f X ⟶ baseChangeOver f X :=
  Over.homMk (idProd f X p hp) (by simp [hp])

/-- The sheaf compatibility condition for `x : X_T ⟶ X'` (equality after any two morphisms with
the same composite to `X`) is equivalent to equality after `id_X × p₁` and `id_X × p₂`. -/
lemma compatible_iff (X X' : Over S) (x : baseChangeOver f X ⟶ X') :
    (∀ {Z : Over S} (q₁ q₂ : Z ⟶ baseChangeOver f X),
        q₁ ≫ baseChangeProj f X = q₂ ≫ baseChangeProj f X → q₁ ≫ x = q₂ ≫ x) ↔
      idProd f X _ (fst_comp_eq f) ≫ x.left = idProd f X _ (snd_comp_eq f) ≫ x.left := by
  constructor
  · intro h
    have := h (idProdOver f X _ (fst_comp_eq f)) (idProdOver f X _ (snd_comp_eq f)) (by
      ext
      simp [idProdOver])
    simpa [idProdOver] using congrArg CommaMorphism.left this
  · intro h Z q₁ q₂ hq
    have hq' : q₁.left ≫ pullback.fst X.hom f = q₂.left ≫ pullback.fst X.hom f := by
      simpa using congrArg CommaMorphism.left hq
    have w₁ : q₁.left ≫ pullback.snd X.hom f ≫ f = Z.hom := by simpa using Over.w q₁
    have w₂ : q₂.left ≫ pullback.snd X.hom f ≫ f = Z.hom := by simpa using Over.w q₂
    let t : Z.left ⟶ pullback f f :=
      pullback.lift (q₁.left ≫ pullback.snd _ _) (q₂.left ≫ pullback.snd _ _) (by
        simp only [Category.assoc, w₁, w₂])
    let m : Z.left ⟶ pullback X.hom (doubleStructure f) :=
      pullback.lift (q₁.left ≫ pullback.fst _ _) t (by
        simp only [t, Category.assoc, doubleStructure, pullback.lift_fst_assoc]
        rw [pullback.condition])
    have e₁ : q₁.left = m ≫ idProd f X _ (fst_comp_eq f) := by
      apply pullback.hom_ext <;> simp [m, t]
    have e₂ : q₂.left = m ≫ idProd f X _ (snd_comp_eq f) := by
      apply pullback.hom_ext
      · simp [m, hq']
      · simp [m, t]
    ext
    simp only [Over.comp_left, e₁, e₂, Category.assoc, h]

/-- **Exactness of the descent sequence of morphisms of schemes.** The sheaf condition of the
representable presheaf of `X'` on `Over S` for the singleton presieve on the projection
`X_T ⟶ X` is equivalent to the exactness of
`Hom_S(X, X') ⟶ Hom_T(X_T, X'_T) ⇉ Hom_{T ×_S T}(X_{T ×_S T}, X'_{T ×_S T})`:
base change `u ↦ u_T` is injective, and its image is the set of `g` with `p₁^* g = p₂^* g`. -/
@[weil "def_fka3_descent_sequence_schemes"]
theorem isSheafFor_singleton_iff (X X' : Over S) :
    Presieve.IsSheafFor (yoneda.obj X') (Presieve.singleton (baseChangeProj f X)) ↔
      Function.Injective (baseChangeHom f X X') ∧
        Set.range (baseChangeHom f X X') =
          {g | pullbackHom f X X' _ (fst_comp_eq f) g =
            pullbackHom f X X' _ (snd_comp_eq f) g} := by
  have hy : ∀ {Z W : Over S} (p : Z ⟶ W) (y : W ⟶ X'), (yoneda.obj X').map p.op y = p ≫ y :=
    fun _ _ => rfl
  rw [Presieve.isSheafFor_singleton]
  simp only [hy]
  have key : ∀ x : baseChangeOver f X ⟶ X',
      (∀ {Z : Over S} (q₁ q₂ : Z ⟶ baseChangeOver f X),
        q₁ ≫ baseChangeProj f X = q₂ ≫ baseChangeProj f X → q₁ ≫ x = q₂ ≫ x) ↔
      pullbackHom f X X' _ (fst_comp_eq f) ((homEquiv f X X').symm x) =
        pullbackHom f X X' _ (snd_comp_eq f) ((homEquiv f X X').symm x) := by
    intro x
    rw [pullbackHom_fst_eq_snd_iff]
    have hx : ((homEquiv f X X').symm x).left ≫ pullback.fst X'.hom f = x.left := by
      rw [← homEquiv_apply_left, Equiv.apply_symm_apply]
    rw [hx]
    exact compatible_iff f X X' x
  have hbase : ∀ (u : X ⟶ X') (g), baseChangeHom f X X' u = g ↔
      baseChangeProj f X ≫ u = homEquiv f X X' g := by
    intro u g
    rw [← homEquiv_baseChangeHom]
    exact (homEquiv f X X').injective.eq_iff.symm
  constructor
  · intro h
    refine ⟨fun u v huv => ?_, ?_⟩
    · obtain ⟨y, -, hy⟩ := h (homEquiv f X X' (baseChangeHom f X X' u)) (by
        rw [key, Equiv.symm_apply_apply]
        exact pullbackHom_baseChangeHom f X X' u)
      exact (hy u ((hbase u _).1 rfl)).trans (hy v ((hbase v _).1 huv.symm)).symm
    · ext g
      refine ⟨?_, fun hg => ?_⟩
      · rintro ⟨u, rfl⟩
        exact pullbackHom_baseChangeHom f X X' u
      · obtain ⟨y, hy, -⟩ := h (homEquiv f X X' g) (by rwa [key, Equiv.symm_apply_apply])
        exact ⟨y, (hbase y g).2 hy⟩
  · rintro ⟨hinj, hrange⟩ x hx
    rw [key] at hx
    obtain ⟨u, hu⟩ : (homEquiv f X X').symm x ∈ Set.range (baseChangeHom f X X') := by
      rw [hrange]
      exact hx
    refine ⟨u, ?_, fun v hv => hinj ?_⟩
    · change baseChangeProj f X ≫ u = x
      rw [(hbase u _).1 hu, Equiv.apply_symm_apply]
    · have hv' : baseChangeProj f X ≫ v = x := hv
      rw [hu, (hbase v ((homEquiv f X X').symm x)).2 (by rw [Equiv.apply_symm_apply, hv'])]

end AlgebraicGeometry.DescentSequence

end
