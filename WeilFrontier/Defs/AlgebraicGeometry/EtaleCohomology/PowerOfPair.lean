module

public import Mathlib.Algebra.Homology.Additive
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import WeilFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleInverseImageAbelian
public import Weil.Attr

/-!
# Pairs on a scheme and their powers

Let `V` be a scheme. A *pair* on `V` is `(h, φ)` with `h : V ⟶ V` a morphism and
`φ : h^* G ⟶ G` a morphism of sheaves (or of complexes of sheaves) on the small étale site of
`V`. For `d ≥ 1` its `d`-th power is `(h, φ)^d = (h^d, φ^(d))`, where `φ^(1) = φ` and
`φ^(m+1) = φ ∘ h^*(φ^(m))`, read as a morphism `(h^(m+1))^* G ⟶ G` through the canonical
isomorphism `h^* (h^m)^* ≅ (h^(m+1))^*` of composite inverse images. The geometric Frobenius
`(F_U, F_G)` of a sheaf on a variety over a finite field is the `d`-th power of the pair
`(Fr_U, Fr_G)`.

The construction only uses the inverse image functors `h^*` and the isomorphisms
`g^* ⋙ f^* ≅ (f ≫ g)^*`. It is therefore made for an arbitrary family of functors
`I : (V ⟶ V) → (C ⥤ C)` indexed by the endomorphisms of an object `V` of a category, with
isomorphisms `θ : I g ⋙ I f ≅ I fg` whenever `f ≫ g = fg`, and then specialised to sheaves
and to complexes of sheaves on the small étale site.

## Main definitions

* `CategoryTheory.InverseImagePair` — a pair `(h, φ : (I h).obj G ⟶ G)`.
* `CategoryTheory.InverseImagePair.powSuccMap` — `φ^(n+1) : (I (h ^ (n + 1))).obj G ⟶ G`.
* `CategoryTheory.InverseImagePair.powSucc` — the pair `(h, φ)^(n+1)`.
* `CategoryTheory.InverseImagePair.pow` — the pair `(h, φ)^d` for `d ≠ 0`.
* `AlgebraicGeometry.SmallEtalePair` — pairs of sheaves on the small étale site of `V`, with
  `AlgebraicGeometry.SmallEtalePair.pow` their powers.
* `AlgebraicGeometry.smallEtaleInverseImage_additive` — the inverse image of abelian sheaves
  is additive, so that it acts termwise on complexes.
* `AlgebraicGeometry.SmallEtaleComplexPair` — pairs of complexes of sheaves on the small étale
  site of `V`, with `AlgebraicGeometry.SmallEtaleComplexPair.pow` their powers.

## Main results

* `CategoryTheory.InverseImagePair.powSuccMap_zero`, `powSuccMap_succ` — the recursion
  `φ^(1) = φ`, `φ^(m+2) = θ⁻¹ ≫ h^*(φ^(m+1)) ≫ φ`.
* `CategoryTheory.InverseImagePair.pow_one`, `pow_succ` — the same for `pow`.

## Implementation notes

Powers of an endomorphism are taken in the monoid `CategoryTheory.End V`, where
`f * g = g ≫ f`; thus `h ^ (n + 1) = h ≫ h ^ n` (`pow_succ`), which is the composite whose
inverse image is `h^* ∘ (h^n)^*`. The power is defined for `d ≥ 1` only, as in the source:
`φ^(1)` is `φ` itself and not a composite with an identification `(𝟙 V)^* ≅ 𝟭`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, II.3][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {X : Type*} [Category X] {V : X} {C : Type*} [Category C]

/-- A *pair* `(h, φ)` for a family of inverse image functors `I` indexed by the endomorphisms of
`V`: an endomorphism `h : V ⟶ V` and a morphism `φ : (I h).obj G ⟶ G`. -/
@[ext, weil "def_fk203_power_of_pair"]
structure InverseImagePair (I : (V ⟶ V) → C ⥤ C) (G : C) where
  /-- The endomorphism `h`. -/
  hom : V ⟶ V
  /-- The morphism `φ : h^* G ⟶ G`. -/
  map : (I hom).obj G ⟶ G

namespace InverseImagePair

variable {I : (V ⟶ V) → C ⥤ C} {G : C}
  (θ : ∀ (f g fg : V ⟶ V), f ≫ g = fg → (I g ⋙ I f ≅ I fg))

/-- `h ^ (n + 1) = h ≫ h ^ n` in the monoid of endomorphisms. -/
lemma comp_pow_eq_pow_succ (h : V ⟶ V) (n : ℕ) :
    h ≫ (End.of h) ^ n = (End.of h) ^ (n + 1) :=
  (_root_.pow_succ (End.of h) n).symm

/-- The morphism `φ^(n+1) : (h ^ (n + 1))^* G ⟶ G`, by `φ^(1) = φ` and
`φ^(m+2) = φ ∘ h^*(φ^(m+1))`, through `θ : h^* (h ^ (m + 1))^* ≅ (h ^ (m + 2))^*`. -/
def powSuccMap (p : InverseImagePair I G) : (n : ℕ) → (I ((End.of p.hom) ^ (n + 1))).obj G ⟶ G
  | 0 => eqToHom (congrArg (fun f => (I f).obj G) (_root_.pow_one (End.of p.hom))) ≫ p.map
  | n + 1 =>
      (θ p.hom _ _ (comp_pow_eq_pow_succ p.hom (n + 1))).inv.app G ≫
        (I p.hom).map (powSuccMap p n) ≫ p.map

/-- `φ^(1) = φ`, up to `h ^ 1 = h`. -/
lemma powSuccMap_zero (p : InverseImagePair I G) :
    p.powSuccMap θ 0 =
      eqToHom (congrArg (fun f => (I f).obj G) (_root_.pow_one (End.of p.hom))) ≫ p.map :=
  rfl

/-- `φ^(m+2) = φ ∘ h^*(φ^(m+1))`, through `θ`. -/
lemma powSuccMap_succ (p : InverseImagePair I G) (n : ℕ) :
    p.powSuccMap θ (n + 1) =
      (θ p.hom _ _ (comp_pow_eq_pow_succ p.hom (n + 1))).inv.app G ≫
        (I p.hom).map (p.powSuccMap θ n) ≫ p.map :=
  rfl

/-- The pair `(h, φ)^(n+1) = (h ^ (n + 1), φ^(n+1))`. -/
def powSucc (p : InverseImagePair I G) (n : ℕ) : InverseImagePair I G where
  hom := (End.of p.hom) ^ (n + 1)
  map := p.powSuccMap θ n

/-- **The `d`-th power of a pair**, `d ≥ 1`: `(h, φ)^d = (h ^ d, φ^(d))`, where `φ^(1) = φ`,
`φ^(m+1) = φ ∘ h^*(φ^(m))`, and `h^* (h^m)^*` is identified with `(h^(m+1))^*` by `θ`. -/
@[weil "def_fk203_power_of_pair"]
def pow (p : InverseImagePair I G) (d : ℕ) (hd : d ≠ 0) : InverseImagePair I G where
  hom := (End.of p.hom) ^ d
  map := eqToHom (by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)]) ≫
    p.powSuccMap θ (d - 1)

/-- The endomorphism of `(h, φ)^d` is `h ^ d`. -/
@[simp]
lemma pow_hom (p : InverseImagePair I G) (d : ℕ) (hd : d ≠ 0) :
    (p.pow θ d hd).hom = (End.of p.hom) ^ d :=
  rfl

/-- The endomorphism of `(h, φ)^(n+1)` is `h ^ (n + 1)`. -/
@[simp]
lemma powSucc_hom (p : InverseImagePair I G) (n : ℕ) :
    (p.powSucc θ n).hom = (End.of p.hom) ^ (n + 1) :=
  rfl

/-- The `(n + 1)`-st power is `powSucc`. -/
lemma pow_add_one (p : InverseImagePair I G) (n : ℕ) :
    p.pow θ (n + 1) n.succ_ne_zero = p.powSucc θ n := by
  ext
  · rfl
  · simp [pow, powSucc]

/-- `(h, φ)^1 = (h, φ)`. -/
lemma pow_one (p : InverseImagePair I G) : p.pow θ 1 one_ne_zero = p := by
  rw [pow_add_one]
  ext
  · exact _root_.pow_one (End.of p.hom)
  · simp [powSucc, powSuccMap_zero]

/-- The recursion `φ^(m+2) = φ ∘ h^*(φ^(m+1))` for `pow`. -/
lemma pow_succ_map (p : InverseImagePair I G) (n : ℕ) :
    (p.pow θ (n + 2) (by omega)).map =
      (θ p.hom _ _ (comp_pow_eq_pow_succ p.hom (n + 1))).inv.app G ≫
        (I p.hom).map (p.pow θ (n + 1) n.succ_ne_zero).map ≫ p.map := by
  simp [pow, powSuccMap_succ]

end InverseImagePair

end CategoryTheory

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (V : B.Scheme)
variable (A : Type w) [Category.{v} A] [HasColimitsOfSize.{u, u + 1} A]
  [HasWeakSheafify (SmallEtale.topology B V.obj V.property) A]

/-- **A pair of sheaves on the small étale site of `V`**: `(h, φ)` with `h : V ⟶ V` and
`φ : h^* G ⟶ G` a morphism of sheaves with values in `A`. -/
@[weil "def_fk203_power_of_pair"]
abbrev SmallEtalePair (G : Sheaf (SmallEtale.topology B V.obj V.property) A) :=
  InverseImagePair (fun h : V ⟶ V => smallEtaleInverseImage B h A) G

variable {B V A} in
/-- **The `d`-th power of a pair of sheaves**, `d ≥ 1`, through the isomorphisms of composite
inverse images `smallEtaleInverseImageComp`. -/
@[weil "def_fk203_power_of_pair"]
abbrev SmallEtalePair.pow {G : Sheaf (SmallEtale.topology B V.obj V.property) A}
    (p : SmallEtalePair B V A G) (d : ℕ) (hd : d ≠ 0) : SmallEtalePair B V A G :=
  InverseImagePair.pow (fun f g fg hfg => smallEtaleInverseImageComp B A f g fg hfg) p d hd

/-- The inverse image of abelian sheaves on the small étale sites is additive: it preserves
finite products (`smallEtaleInverseImage_preservesFiniteLimits`). -/
instance smallEtaleInverseImage_additive {S T : B.Scheme} (f : T ⟶ S) :
    (smallEtaleInverseImage B f AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

variable [Preadditive A] [∀ h : V ⟶ V, (smallEtaleInverseImage B h A).Additive]
  {ι : Type*} (c : ComplexShape ι)

/-- **A pair of complexes of sheaves on the small étale site of `V`**: `(h, φ)` with
`h : V ⟶ V` and `φ : h^* G ⟶ G` a morphism of complexes, `h^*` acting termwise. -/
@[weil "def_fk203_power_of_pair"]
abbrev SmallEtaleComplexPair
    (G : HomologicalComplex (Sheaf (SmallEtale.topology B V.obj V.property) A) c) :=
  InverseImagePair (fun h : V ⟶ V => (smallEtaleInverseImage B h A).mapHomologicalComplex c) G

variable {B V A c} in
/-- **The `d`-th power of a pair of complexes of sheaves**, `d ≥ 1`, through the termwise
isomorphisms of composite inverse images. -/
@[weil "def_fk203_power_of_pair"]
abbrev SmallEtaleComplexPair.pow
    {G : HomologicalComplex (Sheaf (SmallEtale.topology B V.obj V.property) A) c}
    (p : SmallEtaleComplexPair B V A c G) (d : ℕ) (hd : d ≠ 0) :
    SmallEtaleComplexPair B V A c G :=
  InverseImagePair.pow (fun f g fg hfg =>
    Functor.mapHomologicalComplexCompIso (smallEtaleInverseImageComp B A f g fg hfg) c) p d hd

end AlgebraicGeometry

end
