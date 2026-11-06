module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArCanonicalFunctor
public import WeilFrontier.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The Artin–Rees category is additive

Let `𝒫` be the category of projective systems of `l`-power torsion `Λ`-modules and `AR` its
Artin–Rees category, whose morphisms `F ⟶ G` are the classes `[r, f]` of pairs `(r, f)` with
`f : F[r] ⟶ G`. We show that the relation `≈` on pairs is an equivalence relation, that the
composition and the sum of `AR` computed on representatives do not depend on the
representatives, and that `AR` is an additive category: the canonical functor `q : 𝒫 ⥤ AR` is
additive, `q(0)` is a zero object, and for projective systems `F` and `G` the image under `q` of
the biproduct `F ⊞ G`, with the images of its injections and projections, is a biproduct of `F`
and `G` in `AR`.

## Main results

* `CategoryTheory.ProjectiveSystem.ArHom.rel_equivalence`: `≈` is an equivalence relation.
* `CategoryTheory.ProjectiveSystem.ArHom.rel_compRep`: if `(r, f) ≈ (r', f')` and
  `(s, g) ≈ (s', g')`, then `(r + s, g ∘ f[s]) ≈ (r' + s', g' ∘ f'[s'])`.
* `CategoryTheory.ProjectiveSystem.ArHom.rel_addRep`: if `(r, f) ≈ (r', f')` and
  `(s, g) ≈ (s', g')`, the representatives of the sums computed at any common indices are
  related.
* `CategoryTheory.ProjectiveSystem.toArCategory_additive`: the canonical functor `q` is
  additive.
* `CategoryTheory.ProjectiveSystem.ArCategory.isZero_of_zero`: `q(0)` is a zero object.
* `CategoryTheory.ProjectiveSystem.ArCategory.isBilimitMapBinaryBicone`: `q(F ⊞ G)`, with `q` of
  the injections and projections, is a biproduct of `F` and `G`.
* `CategoryTheory.ProjectiveSystem.ArCategory.hasFiniteBiproducts`: the A–R category has finite
  biproducts, so with its preadditive structure it is an additive category.

## Implementation notes

The composition and the sum of the A–R category are defined on the quotient `ArHom F G` by
lifting functions on pairs, which already proves that they do not depend on the
representatives; `rel_compRep` and `rel_addRep` state this independence for the relation `≈`
itself, as in the source. Mathlib has no bundled notion of additive category: it is a
preadditive category with finite biproducts (`HasFiniteBiproducts`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits

open scoped ZeroObject

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

namespace ArHom

variable {F G H : ProjectiveSystem.{v} Λ l}

/-- Characterization of `≈` through a common index: `(r, f) ≈ (s, g)` if and only if `f` and `g`
agree after precomposition with `F[t] ⟶ F[r]` and `F[t] ⟶ F[s]` for every large `t`. -/
lemma rel_iff_forall_ge {r s : ℕ} (f : (shift (r : ℤ)).obj F ⟶ G)
    (g : (shift (s : ℤ)).obj F ⟶ G) :
    Rel F G ⟨r, f⟩ ⟨s, g⟩ ↔ ∃ t₀ : ℕ, ∀ (t : ℕ) (hr : r ≤ t) (hs : s ≤ t), t₀ ≤ t →
      shiftMap F hr ≫ f = shiftMap F hs ≫ g := by
  constructor
  · rintro ⟨t₀, hr₀, hs₀, e⟩
    refine ⟨t₀, fun t hr hs ht => ?_⟩
    rw [← shiftMap_comp_shiftMap_assoc F hr₀ ht, ← shiftMap_comp_shiftMap_assoc F hs₀ ht, e]
  · rintro ⟨t₀, h⟩
    exact ⟨max t₀ (max r s), by omega, by omega, h _ _ _ (le_max_left _ _)⟩

/-- **The relation `≈` on pairs `(r, f)` is an equivalence relation.** -/
@[weil "lem_fk112_ar_category_well_defined"]
theorem rel_equivalence (F G : ProjectiveSystem.{v} Λ l) : _root_.Equivalence (Rel F G) where
  refl p := ⟨p.1, le_rfl, le_rfl, rfl⟩
  symm {p q} h := by
    obtain ⟨r, f⟩ := p
    obtain ⟨s, g⟩ := q
    obtain ⟨t, hr, hs, e⟩ := h
    exact ⟨t, hs, hr, e.symm⟩
  trans {p q w} h₁ h₂ := by
    obtain ⟨r, f⟩ := p
    obtain ⟨s, g⟩ := q
    obtain ⟨u, k⟩ := w
    obtain ⟨t₁, e₁⟩ := (rel_iff_forall_ge f g).1 h₁
    obtain ⟨t₂, e₂⟩ := (rel_iff_forall_ge g k).1 h₂
    refine (rel_iff_forall_ge f k).2 ⟨max (max t₁ t₂) s, fun t hr hu ht => ?_⟩
    have hs : s ≤ t := by omega
    rw [e₁ t hr hs (by omega), e₂ t hs hu (by omega)]

/-- `Rel F G` is its own equivalence closure. -/
lemma eqvGen_rel_iff (a b : Σ r : ℕ, (shift (r : ℤ)).obj F ⟶ G) :
    Relation.EqvGen (Rel F G) a b ↔ Rel F G a b :=
  Equivalence.eqvGen_iff (rel_equivalence F G)

/-- `[r, f] = [s, g]` if and only if `(r, f) ≈ (s, g)`. -/
lemma mk_eq_mk_iff_rel {r s : ℕ} (f : (shift (r : ℤ)).obj F ⟶ G)
    (g : (shift (s : ℤ)).obj F ⟶ G) : mk r f = mk s g ↔ Rel F G ⟨r, f⟩ ⟨s, g⟩ :=
  (mk_eq_mk_iff f g).trans (eqvGen_rel_iff _ _)

/-- **The composition does not depend on the representatives**: if `(r, f) ≈ (r', f')` and
`(s, g) ≈ (s', g')`, then `(r + s, g ∘ f[s]) ≈ (r' + s', g' ∘ f'[s'])`. -/
@[weil "lem_fk112_ar_category_well_defined"]
theorem rel_compRep {r r' s s' : ℕ} {f : (shift (r : ℤ)).obj F ⟶ G}
    {f' : (shift (r' : ℤ)).obj F ⟶ G} {g : (shift (s : ℤ)).obj G ⟶ H}
    {g' : (shift (s' : ℤ)).obj G ⟶ H} (hf : Rel F G ⟨r, f⟩ ⟨r', f'⟩)
    (hg : Rel G H ⟨s, g⟩ ⟨s', g'⟩) :
    Rel F H ⟨r + s, compRep f g⟩ ⟨r' + s', compRep f' g'⟩ := by
  rw [← mk_eq_mk_iff_rel]
  have hf' := (mk_eq_mk_iff_rel f f').2 hf
  have hg' := (mk_eq_mk_iff_rel g g').2 hg
  change comp (mk r f) (mk s g) = comp (mk r' f') (mk s' g')
  rw [hf', hg']

/-- **The sum does not depend on the representatives**: if `(r, f) ≈ (r', f')` and
`(s, g) ≈ (s', g')`, then the representatives `f ∘ ε^{t-r} + g ∘ ε^{t-s}` and
`f' ∘ ε^{t'-r'} + g' ∘ ε^{t'-s'}` of the sums, computed at any `t ≥ max r s` and
`t' ≥ max r' s'`, are related. -/
@[weil "lem_fk112_ar_category_well_defined"]
theorem rel_addRep {r r' s s' t t' : ℕ} {f : (shift (r : ℤ)).obj F ⟶ G}
    {f' : (shift (r' : ℤ)).obj F ⟶ G} {g : (shift (s : ℤ)).obj F ⟶ G}
    {g' : (shift (s' : ℤ)).obj F ⟶ G} (hr : r ≤ t) (hs : s ≤ t) (hr' : r' ≤ t') (hs' : s' ≤ t')
    (hf : Rel F G ⟨r, f⟩ ⟨r', f'⟩) (hg : Rel F G ⟨s, g⟩ ⟨s', g'⟩) :
    Rel F G ⟨t, shiftMap F hr ≫ f + shiftMap F hs ≫ g⟩
      ⟨t', shiftMap F hr' ≫ f' + shiftMap F hs' ≫ g'⟩ := by
  rw [← mk_eq_mk_iff_rel, ← mk_add_mk t hr hs, ← mk_add_mk t' hr' hs',
    (mk_eq_mk_iff_rel f f').2 hf, (mk_eq_mk_iff_rel g g').2 hg]

end ArHom

/-- **The canonical functor `q` to the A–R category is additive**: `q(f + g) = q(f) + q(g)`. -/
@[weil "lem_fk112_ar_category_well_defined"]
instance toArCategory_additive : (toArCategory.{v} Λ l).Additive where
  map_add {F _ f g} := by
    simp only [toArCategory_map, Preadditive.comp_add]
    refine Eq.trans ?_ (ArCategory.homMk_add_homMk 0 le_rfl le_rfl _ _).symm
    rw [shiftMap_refl, Category.id_comp, Category.id_comp]

namespace ArCategory

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **`q(0)` is a zero object of the A–R category.** -/
@[weil "lem_fk112_ar_category_well_defined"]
theorem isZero_of_zero : IsZero (of (0 : ProjectiveSystem.{v} Λ l)) :=
  (toArCategory.{v} Λ l).map_isZero (isZero_zero _)

/-- The image under `q` of a zero object of projective systems is a zero object of the A–R
category. -/
lemma isZero_of {F : ProjectiveSystem.{v} Λ l} (hF : IsZero F) : IsZero (of F) :=
  (toArCategory.{v} Λ l).map_isZero hF

instance hasZeroObject : HasZeroObject (ArCategory.{v} Λ l) :=
  ⟨⟨_, isZero_of_zero⟩⟩

/-- **`q(F ⊞ G)`, with `q` of the injections and projections of `F ⊞ G`, is a biproduct of `F`
and `G` in the A–R category.** -/
@[weil "lem_fk112_ar_category_well_defined"]
noncomputable def isBilimitMapBinaryBicone (F G : ProjectiveSystem.{v} Λ l) :
    ((toArCategory.{v} Λ l).mapBinaryBicone (BinaryBiproduct.bicone F G)).IsBilimit :=
  have := preservesBinaryBiproducts_of_preservesBiproducts (toArCategory.{v} Λ l)
  isBinaryBilimitOfPreserves _ (BinaryBiproduct.isBilimit F G)

instance hasBinaryBiproducts : HasBinaryBiproducts (ArCategory.{v} Λ l) where
  has_binary_biproduct X Y := HasBinaryBiproduct.mk
    { bicone := (toArCategory.{v} Λ l).mapBinaryBicone (BinaryBiproduct.bicone X.obj Y.obj)
      isBilimit := isBilimitMapBinaryBicone X.obj Y.obj }

/-- **The A–R category has finite biproducts**: with its preadditive structure
(`ArCategory.preadditive`) it is an additive category. Every finite biproduct is the image under
`q` of the biproduct of projective systems. -/
@[weil "lem_fk112_ar_category_well_defined"]
instance hasFiniteBiproducts : HasFiniteBiproducts (ArCategory.{v} Λ l) where
  out _ := ⟨fun f => HasBiproduct.mk
    { bicone := (toArCategory.{v} Λ l).mapBicone (biproduct.bicone fun j => (f j).obj)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }⟩

end ArCategory

end ProjectiveSystem

end CategoryTheory
