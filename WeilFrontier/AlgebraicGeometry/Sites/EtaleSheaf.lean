module

public import Weil.Attr
public import WeilFrontier.Defs.AlgebraicGeometry.Sites.EtaleCoveringFk101
public import WeilFrontier.AlgebraicGeometry.Sites.Etale
public import WeilFrontier.AlgebraicGeometry.Sites.EtaleCoveringFk101
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Sheaves on the étale category of a ring

Let `A` be a commutative ring and `Et(A)` its étale category (`AlgebraicGeometry.EtaleCategory A`,
the opposite of the affine étale site `Scheme.AffineEtale (Spec A)`). A presheaf of sets `F` on
`Et(A)` satisfies the *sheaf axioms* if
* (a) for every finite family of morphisms `pₖ : D ⟶ Bₖ` of `Et(A)` (the family may be empty)
  such that the induced homomorphism `D → ∏ₖ Bₖ` is bijective, the map `F(D) → ∏ₖ F(Bₖ)` is
  bijective;
* (b) for every faithfully flat morphism `g : B ⟶ C` of `Et(A)`, the map `F(g)` is injective and
  its image consists of the sections `s` of `F(C)` with `F(u)(s) = F(v)(s)` for all pairs of
  morphisms `u v : C ⟶ D` with `g ≫ u = g ≫ v`.

We show that these are exactly the sheaves for the étale topology
`Scheme.AffineEtale.topology (Spec A)`. Accordingly, the category `Sh(A, 𝒞)` of sheaves with
values in `𝒞` (sets or abelian groups) is `CategoryTheory.Sheaf (Scheme.AffineEtale.topology
(Spec A)) 𝒞`, the full subcategory of presheaves which are sheaves.

## Main definitions

- `AlgebraicGeometry.EtaleCategory.IsSheafAxioms F`: the sheaf axioms (a) and (b) for a presheaf
  of sets `F` on `Et(A)`.
- `AlgebraicGeometry.EtaleCategory.finiteCoverage A`: the coverage of the affine étale site of
  `Spec A` by finite covering families.

## Main results

- `AlgebraicGeometry.EtaleCategory.isSheaf_iff_isSheafAxioms`: a presheaf of sets on `Et(A)` is
  a sheaf for the étale topology if and only if it satisfies the sheaf axioms.
- `AlgebraicGeometry.EtaleCategory.isSheaf_iff_isSheafAxioms_forget`: a presheaf of abelian
  groups is a sheaf if and only if its underlying presheaf of sets satisfies the sheaf axioms.
- `AlgebraicGeometry.EtaleCategory.finiteCoverage_toGrothendieck`: the finite covering families
  generate the étale topology of the affine étale site.
- `AlgebraicGeometry.EtaleCategory.bijective_pi_of_isSheaf`: condition (a) holds for sheaves for
  finite families indexed by a type in any universe.

## Implementation notes

In condition (a) the index types are finite types in `Type`; for a sheaf the condition then
holds for finite index types in every universe (`bijective_pi_of_isSheaf`). The sheaf axioms
are proved to imply the sheaf condition for a finite covering family `(gᵢ : B ⟶ Cᵢ)ᵢ` by passing
to the single faithfully flat morphism `B ⟶ ∏ᵢ Cᵢ`: a pair of morphisms `u v : ∏ᵢ Cᵢ ⟶ D` splits
`D` into the factors `D ⧸ (1 - u(eᵢ) v(eⱼ))` cut out by the idempotents `eᵢ` of the product, on
each of which `u` and `v` factor through the projections.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe t w u

open CategoryTheory Opposite

section RingLemmas

/-- If a ring `R` is identified with a finite product `∏ᵢ Sᵢ` by the maps `fᵢ : R → Sᵢ`, every
prime ideal of `R` is the preimage of a prime ideal of some `Sᵢ`. -/
lemma RingHom.exists_comap_eq_of_bijective_pi {R : Type*} [CommRing R] {ι : Type*} [_root_.Finite ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] (f : ∀ i, R →+* S i)
    (hf : Function.Bijective (RingHom.pi f)) (p : PrimeSpectrum R) :
    ∃ i, ∃ q : PrimeSpectrum (S i), PrimeSpectrum.comap (f i) q = p := by
  classical
  have := Fintype.ofFinite ι
  let e := RingEquiv.ofBijective (RingHom.pi f) hf
  have he (r : R) (j : ι) : e r j = f j r := rfl
  let d : ι → R := fun i ↦ e.symm (Pi.single i 1)
  have hd (i j : ι) : f j (d i) = Pi.single i (1 : S i) j := by
    rw [← he]; simp [d]
  have hsum : ∑ i, d i = 1 := by
    apply e.injective
    rw [map_sum, map_one]
    simp only [d, RingEquiv.apply_symm_apply]
    exact Finset.univ_sum_single (fun i ↦ (1 : S i))
  obtain ⟨i, hi⟩ : ∃ i, d i ∉ p.asIdeal := by
    by_contra! h
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hsum ▸ Ideal.sum_mem _ fun i _ ↦ h i))
  have hsurj : Function.Surjective (f i) := fun y ↦ ⟨e.symm (Pi.single i y), by
    rw [← he]; simp⟩
  have hker : RingHom.ker (f i) ≤ p.asIdeal := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hxd : x * d i = 0 := by
      apply e.injective
      rw [map_mul, map_zero]
      funext j
      rw [Pi.mul_apply, he, he, hd]
      by_cases hj : j = i
      · subst hj; simp [hx]
      · simp [hj]
    have : x * d i ∈ p.asIdeal := hxd ▸ p.asIdeal.zero_mem
    exact (p.isPrime.mem_or_mem this).resolve_right hi
  have : (Ideal.map (f i) p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  refine ⟨i, ⟨Ideal.map (f i) p.asIdeal, inferInstance⟩, PrimeSpectrum.ext ?_⟩
  change Ideal.comap (f i) (Ideal.map (f i) p.asIdeal) = p.asIdeal
  rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
  exact le_trans (by rw [← RingHom.ker_eq_comap_bot]) hker

/-- A ring homomorphism out of a product `∏ⱼ Rⱼ` sending the idempotent `Pi.single i 1` to `1`
factors through the projection to `Rᵢ`. -/
lemma RingHom.exists_comp_evalRingHom_eq {ι : Type*} [DecidableEq ι] {R : ι → Type*}
    [∀ i, CommRing (R i)] {E : Type*} [CommRing E] (φ : (∀ i, R i) →+* E) (i : ι)
    (h : φ (Pi.single i 1) = 1) :
    ∃ ψ : R i →+* E, ψ.comp (Pi.evalRingHom R i) = φ := by
  refine ⟨{ toFun := fun y ↦ φ (Pi.single i y)
            map_one' := h
            map_mul' := fun x y ↦ by rw [← map_mul, Pi.single_mul]
            map_zero' := by simp
            map_add' := fun x y ↦ by rw [← map_add, Pi.single_add] }, ?_⟩
  ext c
  simp only [RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_apply, Pi.evalRingHom_apply]
  have hc : Pi.single i (c i) = c * Pi.single i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [hc, map_mul, h, mul_one]

/-- Two idempotents with product `1` are both equal to `1`. -/
lemma IsIdempotentElem.eq_one_of_mul_eq_one {R : Type*} [CommRing R] {x y : R}
    (hx : IsIdempotentElem x) (h : x * y = 1) : x = 1 := by
  calc x = x * (x * y) := by rw [h, mul_one]
    _ = x * y := by rw [← mul_assoc, hx.eq]
    _ = 1 := h

private lemma quotient_mk_span_one_sub_self {R : Type*} [CommRing R] (y : R) :
    Ideal.Quotient.mk (Ideal.span {1 - y}) y = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have := (Ideal.span {1 - y}).neg_mem (Ideal.subset_span rfl : 1 - y ∈ Ideal.span {1 - y})
  rwa [neg_sub] at this

end RingLemmas

namespace AlgebraicGeometry

namespace EtaleCategory

variable {A : CommRingCat.{u}}

/-- The structure map `A ⟶ B` of an object `B` of the étale category of `A`. -/
def structureMap (B : EtaleCategory A) : A ⟶ B.ring :=
  Spec.preimage B.unop.hom

lemma spec_map_structureMap (B : EtaleCategory A) :
    Spec.map (structureMap B) = B.unop.hom :=
  Spec.map_preimage _

lemma etale_structureMap (B : EtaleCategory A) : (structureMap B).hom.Etale := by
  rw [← HasRingHomProperty.Spec_iff (P := @Etale), spec_map_structureMap]
  exact B.unop.prop

@[simp]
lemma ringHom_id (B : EtaleCategory A) : ringHom (𝟙 B) = 𝟙 B.ring := rfl

attribute [local simp] ringHom_comp

set_option backward.isDefEq.respectTransparency.types false in
lemma structureMap_comp_ringHom {B C : EtaleCategory A} (g : B ⟶ C) :
    structureMap B ≫ ringHom g = structureMap C := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_map_structureMap, spec_map_structureMap]
  exact g.unop.w

lemma hom_ext {B C : EtaleCategory A} {f g : B ⟶ C} (h : ringHom f = ringHom g) : f = g :=
  Quiver.Hom.unop_inj (MorphismProperty.CostructuredArrow.Hom.ext (Quiver.Hom.unop_inj h))

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism of the étale category given by a ring homomorphism compatible with the
structure maps. -/
def homMk {B C : EtaleCategory A} (φ : B.ring ⟶ C.ring)
    (h : structureMap B ≫ φ = structureMap C) : B ⟶ C :=
  Quiver.Hom.op (X := C.unop) (Y := B.unop)
    (MorphismProperty.CostructuredArrow.homMk φ.op trivial (by
      change Spec.map φ ≫ B.unop.hom = C.unop.hom
      rw [← spec_map_structureMap B, ← spec_map_structureMap C, ← h, Spec.map_comp]))

@[simp]
lemma ringHom_homMk {B C : EtaleCategory A} (φ : B.ring ⟶ C.ring)
    (h : structureMap B ≫ φ = structureMap C) : ringHom (homMk φ h) = φ := rfl

/-- The object of the étale category given by a ring homomorphism `A ⟶ R` which is étale. -/
def mk {R : CommRingCat.{u}} (φ : A ⟶ R) (hφ : φ.hom.Etale) : EtaleCategory A :=
  haveI : Etale (Spec.map φ) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 hφ
  op (Scheme.AffineEtale.mk (Spec.map φ))

@[simp]
lemma ring_mk {R : CommRingCat.{u}} (φ : A ⟶ R) (hφ : φ.hom.Etale) : (mk φ hφ).ring = R := rfl

@[simp]
lemma structureMap_mk {R : CommRingCat.{u}} (φ : A ⟶ R) (hφ : φ.hom.Etale) :
    structureMap (mk φ hφ) = φ :=
  Spec.preimage_map φ

lemma flat_ringHom {B C : EtaleCategory A} (g : B ⟶ C) : (ringHom g).hom.Flat := by
  rw [← HasRingHomProperty.Spec_iff (P := @Flat)]
  have : Etale (Spec.map (ringHom g) ≫ B.unop.hom) := by
    rw [← spec_map_structureMap B, ← Spec.map_comp, structureMap_comp_ringHom,
      spec_map_structureMap]
    exact C.unop.prop
  have : Etale B.unop.hom := B.unop.prop
  have : Etale (Spec.map (ringHom g)) := Etale.of_comp _ B.unop.hom
  infer_instance


/-! ### The sheaf axioms -/

/-- The sheaf axioms for a presheaf of sets `F` on the étale category `Et(A)`:
(a) for every finite family of morphisms `pₖ : D ⟶ Bₖ` such that `D → ∏ₖ Bₖ` is bijective, the
map `F(D) → ∏ₖ F(Bₖ)` is bijective; (b) for every faithfully flat morphism `g : B ⟶ C`, the map
`F(g)` is injective with image the set of sections `s` of `F(C)` with `F(u)(s) = F(v)(s)` for
every pair of morphisms `u v : C ⟶ D` with `g ≫ u = g ≫ v`. -/
@[weil "def_fk101_etale_sheaf"]
structure IsSheafAxioms (F : EtaleCategory A ⥤ Type w) : Prop where
  /-- Condition (a): finite products. -/
  bijective_pi : ∀ {ι : Type} [Finite ι] (B : ι → EtaleCategory A) (D : EtaleCategory A)
    (p : ∀ k, D ⟶ B k), Function.Bijective (RingHom.pi fun k ↦ (ringHom (p k)).hom) →
      Function.Bijective (fun s : F.obj D ↦ fun k ↦ F.map (p k) s)
  /-- Condition (b), injectivity. -/
  injective_of_faithfullyFlat : ∀ {B C : EtaleCategory A} (g : B ⟶ C),
    (ringHom g).hom.FaithfullyFlat → Function.Injective (F.map g)
  /-- Condition (b), the image. -/
  range_of_faithfullyFlat : ∀ {B C : EtaleCategory A} (g : B ⟶ C),
    (ringHom g).hom.FaithfullyFlat →
      Set.range (F.map g) = {s | ∀ ⦃D : EtaleCategory A⦄ (u v : C ⟶ D), g ≫ u = g ≫ v →
        F.map u s = F.map v s}

variable {F : EtaleCategory A ⥤ Type w}

lemma arrows_compatible_iff {B : EtaleCategory A} {ι : Type*} {C : ι → EtaleCategory A}
    (g : ∀ i, B ⟶ C i) (x : ∀ i, F.obj (C i)) :
    Presieve.Arrows.Compatible F (fun i ↦ (g i).unop) x ↔
      ∀ i j (Z : EtaleCategory A) (a : C i ⟶ Z) (b : C j ⟶ Z), g i ≫ a = g j ≫ b →
        F.map a (x i) = F.map b (x j) := by
  constructor
  · intro h i j Z a b hab
    exact h i j (unop Z) a.unop b.unop (congrArg Quiver.Hom.unop hab)
  · intro h i j Z a b hab
    exact h i j (op Z) a.op b.op (congrArg Quiver.Hom.op hab)

/-- A sheaf satisfies the sheaf condition for every covering family of `Et(A)`. -/
lemma existsUnique_of_isSheaf_of_isCovering
    (hF : Presieve.IsSheaf (Scheme.AffineEtale.topology (Spec A)) F)
    {B : EtaleCategory A} {ι : Type*} {C : ι → EtaleCategory A} (g : ∀ i, B ⟶ C i)
    (hg : IsCovering g) (x : ∀ i, F.obj (C i))
    (hx : ∀ i j (Z : EtaleCategory A) (a : C i ⟶ Z) (b : C j ⟶ Z), g i ≫ a = g j ≫ b →
        F.map a (x i) = F.map b (x j)) :
    ∃! s, ∀ i, F.map (g i) s = x i := by
  have hS := hF _ hg.mem_topology
  rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  exact hS x ((arrows_compatible_iff g x).2 hx)

lemma isCovering_of_bijective_pi {ι : Type*} [Finite ι] {B : ι → EtaleCategory A}
    {D : EtaleCategory A} (p : ∀ k, D ⟶ B k)
    (hp : Function.Bijective (RingHom.pi fun k ↦ (ringHom (p k)).hom)) : IsCovering p :=
  ⟨inferInstance, RingHom.exists_comap_eq_of_bijective_pi _ hp⟩

/-- The sections of a sheaf over the zero ring form a subsingleton. -/
lemma subsingleton_of_isSheaf (hF : Presieve.IsSheaf (Scheme.AffineEtale.topology (Spec A)) F)
    (Z : EtaleCategory A) [Subsingleton Z.ring] : Subsingleton (F.obj Z) := by
  have hcov : IsCovering (C := fun i : PEmpty.{1} ↦ i.elim) (B := Z) (fun i ↦ i.elim) :=
    ⟨inferInstance, fun p ↦ (p.isPrime.ne_top (Subsingleton.elim _ _)).elim⟩
  obtain ⟨t, -, ht⟩ := existsUnique_of_isSheaf_of_isCovering hF _ hcov (fun i ↦ i.elim)
    (fun i ↦ i.elim)
  exact ⟨fun a b ↦ (ht a fun i ↦ i.elim).trans (ht b fun i ↦ i.elim).symm⟩

/-- Condition (a) of the sheaf axioms holds for a sheaf, for families indexed by any finite
type. -/
lemma bijective_pi_of_isSheaf (hF : Presieve.IsSheaf (Scheme.AffineEtale.topology (Spec A)) F)
    {ι : Type t} [Finite ι] (B : ι → EtaleCategory A) (D : EtaleCategory A)
    (p : ∀ k, D ⟶ B k) (hp : Function.Bijective (RingHom.pi fun k ↦ (ringHom (p k)).hom)) :
    Function.Bijective (fun s : F.obj D ↦ fun k ↦ F.map (p k) s) := by
  classical
  have hsurj (i : ι) (y : (B i).ring) : ∃ d, (ringHom (p i)).hom d = y := by
    obtain ⟨d, hd⟩ := hp.2 (Pi.single i y)
    exact ⟨d, by simpa using congrFun hd i⟩
  have hx (x : ∀ k, F.obj (B k)) : ∀ i j (Z : EtaleCategory A) (a : B i ⟶ Z) (b : B j ⟶ Z),
      p i ≫ a = p j ≫ b → F.map a (x i) = F.map b (x j) := by
    intro i j Z a b hab
    have hab' := congrArg (fun f ↦ (ringHom f).hom) hab
    simp only [ringHom_comp, CommRingCat.hom_comp] at hab'
    by_cases hij : i = j
    · subst hij
      have : a = b := by
        apply hom_ext
        ext y
        obtain ⟨d, rfl⟩ := hsurj i y
        exact congrFun (congrArg DFunLike.coe hab') d
      rw [this]
    · obtain ⟨d, hd⟩ := hp.2 (Pi.single i 1)
      have h1 : (ringHom (p i)).hom d = 1 := by simpa using congrFun hd i
      have h0 : (ringHom (p j)).hom d = 0 := by
        simpa [Pi.single_apply, Ne.symm hij] using congrFun hd j
      have h := congrFun (congrArg DFunLike.coe hab') d
      simp only [RingHom.coe_comp, Function.comp_apply, h1, h0, map_one, map_zero] at h
      have : Subsingleton Z.ring := subsingleton_of_zero_eq_one h.symm
      have := subsingleton_of_isSheaf hF Z
      exact Subsingleton.elim _ _
  have hcov := isCovering_of_bijective_pi p hp
  refine ⟨fun s₁ s₂ h ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := existsUnique_of_isSheaf_of_isCovering hF p hcov _
      (hx fun k ↦ F.map (p k) s₁)
    exact (ht s₁ fun i ↦ rfl).trans (ht s₂ fun i ↦ (congrFun h i).symm).symm
  · obtain ⟨t, ht, -⟩ := existsUnique_of_isSheaf_of_isCovering hF p hcov x (hx x)
    exact ⟨t, funext ht⟩

lemma isCovering_of_faithfullyFlat {B C : EtaleCategory A} (g : B ⟶ C)
    (hg : (ringHom g).hom.FaithfullyFlat) :
    IsCovering (C := fun _ : PUnit.{1} ↦ C) (fun _ ↦ g) := by
  refine ⟨inferInstance, fun p ↦ ?_⟩
  obtain ⟨q, hq⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.1 hg).2 p
  exact ⟨PUnit.unit, q, hq⟩

/-- Condition (b) of the sheaf axioms holds for a sheaf. -/
lemma injective_and_range_of_isSheaf
    (hF : Presieve.IsSheaf (Scheme.AffineEtale.topology (Spec A)) F)
    {B C : EtaleCategory A} (g : B ⟶ C) (hg : (ringHom g).hom.FaithfullyFlat) :
    Function.Injective (F.map g) ∧
      Set.range (F.map g) = {s | ∀ ⦃D : EtaleCategory A⦄ (u v : C ⟶ D), g ≫ u = g ≫ v →
        F.map u s = F.map v s} := by
  have hcov := isCovering_of_faithfullyFlat g hg
  have key (s : F.obj C) (hs : ∀ ⦃D : EtaleCategory A⦄ (u v : C ⟶ D), g ≫ u = g ≫ v →
      F.map u s = F.map v s) := existsUnique_of_isSheaf_of_isCovering hF _ hcov (fun _ ↦ s)
    (fun _ _ Z a b hab ↦ hs a b hab)
  have himage (t : F.obj B) ⦃D : EtaleCategory A⦄ (u v : C ⟶ D) (huv : g ≫ u = g ≫ v) :
      F.map u (F.map g t) = F.map v (F.map g t) := by
    rw [← Functor.map_comp_apply, huv, Functor.map_comp_apply]
  refine ⟨fun t₁ t₂ h ↦ ?_, Set.ext fun s ↦ ⟨?_, fun hs ↦ ?_⟩⟩
  · obtain ⟨t, -, ht⟩ := key _ (himage t₁)
    exact (ht t₁ fun _ ↦ rfl).trans (ht t₂ fun _ ↦ h.symm).symm
  · rintro ⟨t, rfl⟩
    exact himage t
  · obtain ⟨t, ht, -⟩ := key s hs
    exact ⟨t, ht PUnit.unit⟩

/-- A sheaf on `Et(A)` satisfies the sheaf axioms. -/
lemma IsSheafAxioms.of_isSheaf (hF : Presieve.IsSheaf (Scheme.AffineEtale.topology (Spec A)) F) :
    IsSheafAxioms F where
  bijective_pi B D p hp := bijective_pi_of_isSheaf hF B D p hp
  injective_of_faithfullyFlat g hg := (injective_and_range_of_isSheaf hF g hg).1
  range_of_faithfullyFlat g hg := (injective_and_range_of_isSheaf hF g hg).2

/-! ### Finite products and idempotent decompositions in `Et(A)` -/

/-- The products `aᵢ bⱼ` of two complete families of orthogonal idempotents form a complete
family of orthogonal idempotents. -/
lemma _root_.CompleteOrthogonalIdempotents.mul_prod {R : Type*} [CommRing R] {I J : Type*}
    [Fintype I] [Fintype J] {a : I → R} {b : J → R} (ha : CompleteOrthogonalIdempotents a)
    (hb : CompleteOrthogonalIdempotents b) :
    CompleteOrthogonalIdempotents (fun k : I × J ↦ a k.1 * b k.2) := by
  refine ⟨⟨fun k ↦ (ha.idem k.1).mul (hb.idem k.2), ?_⟩, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    dsimp only
    by_cases hi : i = i'
    · subst hi
      have hj : j ≠ j' := fun hj ↦ hne (by rw [hj])
      calc a i * b j * (a i * b j') = a i * a i * (b j * b j') := by ring
        _ = 0 := by rw [hb.ortho hj, mul_zero]
    · calc a i * b j * (a i' * b j') = a i * a i' * (b j * b j') := by ring
        _ = 0 := by rw [ha.ortho hi, zero_mul]
  · rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, ha.complete, hb.complete, one_mul]

section Pi

variable {ι : Type} [Finite ι] (C : ι → EtaleCategory A)

lemma etale_pi_structureMap : (RingHom.pi fun i ↦ (structureMap (C i)).hom).Etale := by
  let : ∀ i, Algebra A (C i).ring := fun i ↦ (structureMap (C i)).hom.toAlgebra
  have : ∀ i, Algebra.Etale A (C i).ring := fun i ↦ etale_structureMap (C i)
  exact RingHom.etale_algebraMap.2 inferInstance

/-- The product of a finite family of objects of `Et(A)`. -/
def finiteProductObj : EtaleCategory A :=
  mk (R := CommRingCat.of (∀ i, (C i).ring))
    (CommRingCat.ofHom (RingHom.pi fun i ↦ (structureMap (C i)).hom)) (etale_pi_structureMap C)

lemma structureMap_piObj :
    structureMap (finiteProductObj C) = CommRingCat.ofHom (RingHom.pi fun i ↦ (structureMap (C i)).hom) :=
  structureMap_mk _ _

/-- The projections out of `finiteProductObj C`. -/
def piπ (i : ι) : finiteProductObj C ⟶ C i :=
  homMk (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ (C i).ring) i)) (by
    rw [structureMap_piObj]; rfl)

variable {C} in
/-- The morphism into `finiteProductObj C` induced by a family of morphisms. -/
def piLift {B : EtaleCategory A} (g : ∀ i, B ⟶ C i) : B ⟶ finiteProductObj C :=
  homMk (CommRingCat.ofHom (RingHom.pi fun i ↦ (ringHom (g i)).hom)) (by
    rw [structureMap_piObj]
    ext x
    funext i
    exact congrArg (fun f ↦ f.hom x) (structureMap_comp_ringHom (g i)))

variable {C} in
@[reassoc (attr := simp)]
lemma piLift_π {B : EtaleCategory A} (g : ∀ i, B ⟶ C i) (i : ι) :
    piLift g ≫ piπ C i = g i :=
  hom_ext rfl

lemma bijective_pi_piπ : Function.Bijective (RingHom.pi fun k ↦ (ringHom (piπ C k)).hom) :=
  ⟨fun _ _ h ↦ funext fun k ↦ congrFun h k, fun y ↦ ⟨y, rfl⟩⟩

variable {C} in
lemma faithfullyFlat_piLift {B : EtaleCategory A} {g : ∀ i, B ⟶ C i} (hg : IsCovering g) :
    (ringHom (piLift g)).hom.FaithfullyFlat := by
  refine RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.2 ⟨flat_ringHom _, fun p ↦ ?_⟩
  obtain ⟨i, q, hq⟩ := hg.exists_comap_eq p
  exact ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun i ↦ (C i).ring) i) q, by
    rw [← hq]; rfl⟩

variable {C} in
/-- A morphism out of `finiteProductObj C` which sends the `i`-th idempotent to `1` factors through the
`i`-th projection. -/
lemma exists_comp_eq_piπ [DecidableEq ι] {D Q : EtaleCategory A} (u : finiteProductObj C ⟶ D) (r : D ⟶ Q)
    (i : ι)
    (h : (ringHom r).hom ((ringHom u).hom (Pi.single (M := fun i ↦ (C i).ring) i 1)) = 1) :
    ∃ a : C i ⟶ Q, u ≫ r = piπ C i ≫ a := by
  classical
  obtain ⟨ψ, hψ⟩ := RingHom.exists_comp_evalRingHom_eq (R := fun i ↦ (C i).ring)
    (ringHom u ≫ ringHom r).hom i h
  refine ⟨homMk (CommRingCat.ofHom ψ) ?_, hom_ext ?_⟩
  · rw [← structureMap_comp_ringHom (piπ C i), ← structureMap_comp_ringHom r,
      ← structureMap_comp_ringHom u, Category.assoc, Category.assoc]
    congr 1
    ext x
    exact RingHom.congr_fun hψ x
  · ext x
    exact (RingHom.congr_fun hψ x).symm

end Pi

lemma etale_quotient_mk_span_one_sub {R : Type u} [CommRing R] {e : R}
    (he : IsIdempotentElem e) : (Ideal.Quotient.mk (Ideal.span {1 - e})).Etale := by
  have := IsLocalization.Away.quotient_of_isIdempotentElem he
  exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway e)

/-- The factor `D ⧸ (1 - e)` of an object `D` of `Et(A)` cut out by an idempotent `e`. -/
def quotObj (D : EtaleCategory A) {e : D.ring} (he : IsIdempotentElem e) : EtaleCategory A :=
  mk (structureMap D ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e})))
    (RingHom.Etale.stableUnderComposition _ _ (etale_structureMap D)
      (etale_quotient_mk_span_one_sub he))

/-- The projection `D ⟶ D ⧸ (1 - e)`. -/
def quotπ (D : EtaleCategory A) {e : D.ring} (he : IsIdempotentElem e) : D ⟶ quotObj D he :=
  homMk (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e}))) (structureMap_mk _ _).symm

/-! ### The sheaf axioms imply the sheaf condition -/

/-- A presheaf satisfying the sheaf axioms satisfies the sheaf condition for every covering
family of `Et(A)`. -/
lemma existsUnique_of_isSheafAxioms (hF : IsSheafAxioms F) {B : EtaleCategory A} {ι : Type}
    [Finite ι] {C : ι → EtaleCategory A} (g : ∀ i, B ⟶ C i) (hg : IsCovering g)
    (x : ∀ i, F.obj (C i))
    (hx : ∀ i j (Z : EtaleCategory A) (a : C i ⟶ Z) (b : C j ⟶ Z), g i ≫ a = g j ≫ b →
        F.map a (x i) = F.map b (x j)) :
    ∃! s, ∀ i, F.map (g i) s = x i := by
  classical
  have := Fintype.ofFinite ι
  have hπ := hF.bijective_pi C (finiteProductObj C) (piπ C) (bijective_pi_piπ C)
  obtain ⟨s, hs⟩ := hπ.2 x
  have hs' (i : ι) : F.map (piπ C i) s = x i := congrFun hs i
  have hG := faithfullyFlat_piLift hg
  have hsG : s ∈ {s | ∀ ⦃D : EtaleCategory A⦄ (u v : finiteProductObj C ⟶ D),
      piLift g ≫ u = piLift g ≫ v → F.map u s = F.map v s} := by
    intro D u v huv
    have hsingle := CompleteOrthogonalIdempotents.single (fun i ↦ (C i).ring)
    have he := (hsingle.map (ringHom u).hom).mul_prod (hsingle.map (ringHom v).hom)
    have hbij := hF.bijective_pi (fun k ↦ quotObj D (he.idem k)) D
      (fun k ↦ quotπ D (he.idem k)) he.bijective_pi
    apply hbij.1
    funext k
    dsimp only
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    -- the images of the two idempotents in the factor are `1`
    have hk := quotient_mk_span_one_sub_self
      ((ringHom u).hom (Pi.single (M := fun i ↦ (C i).ring) k.1 1) *
        (ringHom v).hom (Pi.single (M := fun i ↦ (C i).ring) k.2 1))
    rw [map_mul] at hk
    have h₁ := ((hsingle.idem k.1).map
      ((Ideal.Quotient.mk _).comp (ringHom u).hom)).eq_one_of_mul_eq_one hk
    have h₂ := ((hsingle.idem k.2).map
      ((Ideal.Quotient.mk _).comp (ringHom v).hom)).eq_one_of_mul_eq_one
      ((mul_comm _ _).trans hk)
    obtain ⟨a, ha⟩ := exists_comp_eq_piπ u (quotπ D (he.idem k)) k.1 h₁
    obtain ⟨b, hb⟩ := exists_comp_eq_piπ v (quotπ D (he.idem k)) k.2 h₂
    rw [ha, hb, Functor.map_comp_apply, Functor.map_comp_apply, hs', hs']
    apply hx
    rw [← piLift_π g k.1, ← piLift_π g k.2, Category.assoc, Category.assoc, ← ha, ← hb,
      ← Category.assoc, huv, Category.assoc]
  rw [← hF.range_of_faithfullyFlat _ hG] at hsG
  obtain ⟨t, ht⟩ := hsG
  refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ ?_⟩
  · rw [← piLift_π g i, Functor.map_comp_apply, ht, hs']
  · apply hF.injective_of_faithfullyFlat _ hG
    rw [ht]
    apply hπ.1
    funext i
    dsimp only
    rw [← Functor.map_comp_apply, piLift_π, ht', hs']

/-! ### The comparison with the étale topology -/

/-- Every covering sieve of the affine étale topology of `Spec A` contains a finite covering
family. -/
lemma exists_finite_of_mem_topology {X : Scheme.AffineEtale (Spec A)} {S : Sieve X}
    (hS : S ∈ Scheme.AffineEtale.topology (Spec A) X) :
    ∃ (ι : Type) (_ : Finite ι) (Y : ι → Scheme.AffineEtale (Spec A)) (g : ∀ i, Y i ⟶ X),
      (∀ i, S (g i)) ∧ Sieve.ofArrows Y g ∈ Scheme.AffineEtale.topology (Spec A) X := by
  have hS' : S.functorPushforward (Scheme.AffineEtale.Spec (Spec A)) ∈
      (Spec A).smallEtaleTopology ((Scheme.AffineEtale.Spec (Spec A)).obj X) :=
    (Functor.mem_inducedTopology_iff_of_isCoverDense (G := Scheme.AffineEtale.Spec (Spec A))
      (K := (Spec A).smallEtaleTopology) S).1 hS
  rw [Scheme.mem_smallEtaleTopology_iff_forall_exists_mem_range] at hS'
  choose W h hh hx using hS'
  choose Z v w hv hw using hh
  have hcov : ⋃ x, Set.range ((Scheme.AffineEtale.Spec (Spec A)).map (v x)).left = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, ?_⟩
    obtain ⟨y, hy⟩ := hx x
    rw [hw x] at hy
    exact ⟨(w x).left y, hy⟩
  have : CompactSpace ((Scheme.AffineEtale.Spec (Spec A)).obj X).left := by
    change CompactSpace (Spec X.left.unop); infer_instance
  obtain ⟨s, hs⟩ := Scheme.exists_finite_isEtaleCovering
    (φ := fun x ↦ ((Scheme.AffineEtale.Spec (Spec A)).map (v x)).left) hcov
  let e : Fin s.card ≃ s := s.equivFin.symm
  refine ⟨Fin s.card, inferInstance, fun i ↦ Z (e i), fun i ↦ v (e i), fun i ↦ hv _, ?_⟩
  have hB := (isCovering_iff_mem_topology (B := op X) (C := fun i ↦ op (Z (e i)))
    (fun i ↦ (v (e i)).op)).1 ?_
  · exact hB.2
  rw [isCovering_iff_iUnion_range]
  refine ⟨inferInstance, Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_⟩
  obtain ⟨⟨y, hy⟩, hx'⟩ := hs.exists_mem_range x
  obtain ⟨i, hi⟩ := e.surjective ⟨y, hy⟩
  refine ⟨i, ?_⟩
  rw [hi]
  exact hx'

variable (A) in
/-- The coverage of the affine étale site of `Spec A` by finite covering families. -/
def finiteCoverage : Coverage (Scheme.AffineEtale (Spec A)) where
  coverings X := {R | ∃ (ι : Type) (_ : Finite ι) (Y : ι → Scheme.AffineEtale (Spec A))
    (g : ∀ i, Y i ⟶ X), R = Presieve.ofArrows Y g ∧
      Sieve.ofArrows Y g ∈ Scheme.AffineEtale.topology (Spec A) X}
  pullback X Y f R hR := by
    obtain ⟨ι, _, Yi, g, rfl, hg⟩ := hR
    obtain ⟨κ, _, Z, h, hh, hZ⟩ :=
      exists_finite_of_mem_topology ((Scheme.AffineEtale.topology (Spec A)).pullback_stable f hg)
    refine ⟨Presieve.ofArrows Z h, ⟨κ, inferInstance, Z, h, rfl, hZ⟩, ?_⟩
    rintro _ _ ⟨k⟩
    obtain ⟨W, i, e, he, heq⟩ := hh k
    exact ⟨W, i, e, he, heq⟩

lemma finiteCoverage_toGrothendieck :
    (finiteCoverage A).toGrothendieck = Scheme.AffineEtale.topology (Spec A) := by
  refine le_antisymm ?_ fun X S hS ↦ ?_
  · rw [Coverage.toGrothendieck_eq_sInf]
    refine sInf_le fun X R hR ↦ ?_
    obtain ⟨ι, _, Y, g, rfl, hg⟩ := hR
    exact hg
  · obtain ⟨ι, _, Y, g, hgS, hg⟩ := exists_finite_of_mem_topology hS
    refine Coverage.mem_toGrothendieck_sieves_of_superset _ ?_ ⟨ι, inferInstance, Y, g, rfl, hg⟩
    rintro _ _ ⟨i⟩
    exact hgS i

/-- **Sheaves on the étale category** [FK, I.1]. A presheaf of sets on `Et(A)` is a sheaf for
the étale topology if and only if it satisfies the sheaf axioms `IsSheafAxioms`: it takes finite
products to products and satisfies the equalizer condition for faithfully flat morphisms. -/
@[weil "def_fk101_etale_sheaf"]
theorem isSheaf_iff_isSheafAxioms (F : EtaleCategory A ⥤ Type w) :
    Presheaf.IsSheaf (Scheme.AffineEtale.topology (Spec A)) F ↔ IsSheafAxioms F := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine ⟨IsSheafAxioms.of_isSheaf, fun hF ↦ ?_⟩
  rw [← finiteCoverage_toGrothendieck, Presieve.isSheaf_coverage]
  rintro X R ⟨ι, _, Y, g, rfl, hg⟩
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hcov : IsCovering (B := op X) (C := fun i ↦ op (Y i)) (fun i ↦ (g i).op) :=
    (isCovering_iff_mem_topology _).2 ⟨inferInstance, hg⟩
  exact existsUnique_of_isSheafAxioms hF _ hcov x
    ((arrows_compatible_iff (fun i ↦ (g i).op) x).1 hx)

/-- A presheaf of abelian groups on `Et(A)` is a sheaf if and only if its underlying presheaf
of sets satisfies the sheaf axioms. -/
@[weil "def_fk101_etale_sheaf"]
theorem isSheaf_iff_isSheafAxioms_forget (F : EtaleCategory A ⥤ AddCommGrpCat.{w}) :
    Presheaf.IsSheaf (Scheme.AffineEtale.topology (Spec A)) F ↔
      IsSheafAxioms (F ⋙ forget AddCommGrpCat) := by
  rw [← isSheaf_iff_isSheafAxioms]
  exact ⟨fun h ↦ GrothendieckTopology.HasSheafCompose.isSheaf _ h,
    Presheaf.isSheaf_of_isSheaf_comp _ _ _⟩

end EtaleCategory

end AlgebraicGeometry
