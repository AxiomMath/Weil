module

public import Weil.Attr
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.MittagLefflerArtinRees
public import WeilFrontier.Defs.CategoryTheory.Sites.Cohomology.Torsion.MittagLefflerArtinReesSheaves
public import WeilFrontier.Defs.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The A–R `l`-adic conditions

Let `F` be a projective system of `l`-power torsion `Λ`-modules, or an object of the category
`P_X` of projective systems of `l`-torsion sheaves on the small étale site of a scheme `X`, and
let `F̄` be its system of universal images, `F̄_n = ⋂_{t ≥ 0} im(F_{n+t} ⟶ F_n)`. For integers
`r, s ≥ 0`, the system `F` *satisfies the A–R `l`-adic conditions with constants `(r, s)`* if

* (a) `F` satisfies the Mittag-Leffler–Artin–Rees condition with constant `r`, and
* (b) for all `n ≥ 0` and `t ≥ s` the map
  `F̄_{n+t} / l^{n+1} F̄_{n+t} ⟶ F̄_{n+s} / l^{n+1} F̄_{n+s}` induced by the transition map
  `F̄_{n+t} ⟶ F̄_{n+s}` is an isomorphism.

## Main definitions

* `CategoryTheory.Functor.powSMulCokernelMap G l k h`: for a projective system
  `G : ℤᵒᵖ ⥤ C` in an `R`-linear category and `m ≤ n`, the map
  `G_n / l^k G_n ⟶ G_m / l^k G_m` induced by `G_n ⟶ G_m`; here `G_n / l^k G_n` is the cokernel
  of `l^k • 𝟙 : G_n ⟶ G_n`.
* `CategoryTheory.Functor.IsLAdicStableFrom G l s`: condition (b) for `G`: the maps
  `G_{n+t} / l^{n+1} G_{n+t} ⟶ G_{n+s} / l^{n+1} G_{n+s}` are isomorphisms for `n ≥ 0`, `t ≥ s`.
* `ModuleCat.cokernelPowSMulIso M l k`: the cokernel of `l^k • 𝟙` on a module `M` is the
  quotient module `M ⧸ l^k M`.
* `CategoryTheory.ProjectiveSystem.SatisfiesArLAdicConditions F r s`: the A–R `l`-adic
  conditions with constants `(r, s)` for a projective system of `l`-power torsion modules.
* `AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem.SatisfiesArLAdicConditions F r s`: the
  A–R `l`-adic conditions with constants `(r, s)` for an object of `P_X`.

## Main results

* `CategoryTheory.Functor.isIso_powSMulCokernelMap_refl`: the map along `n ≤ n` is an
  isomorphism, so condition (b) holds trivially for `t = s`.
* `ModuleCat.isIso_powSMulCokernelMap_iff_bijective`: for modules, condition (b)
  is the bijectivity of the induced map of quotient modules
  `G_n ⧸ l^k G_n → G_m ⧸ l^k G_m`.

## Implementation notes

The quotient `G_n / l^{k} G_n` is the cokernel of the endomorphism `l^{k} • 𝟙` of `G_n`, which
makes sense in any `R`-linear category with cokernels: in `ModuleCat Λ` with `R = Λ` it is the
quotient module, and in a category of abelian sheaves with `R = ℕ` it is the cokernel sheaf of
multiplication by `l^k`. The constants are allowed to be any natural numbers; the source asks
for `r ≥ 1`, and since MLAR with constant `r` implies MLAR with any larger constant this is no
restriction on the systems that satisfy the conditions for some constants.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.12.8][FreitagKiehl]
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v u w

namespace CategoryTheory

namespace Functor

variable {R : Type*} [Semiring R] {C : Type*} [Category C] [Preadditive C]
  [CategoryTheory.Linear R C] [HasCokernels C] (G : ℤᵒᵖ ⥤ C)

/-- For a projective system `G : ℤᵒᵖ ⥤ C` in an `R`-linear category, `l : R`, `k : ℕ` and
`m ≤ n`, the map `G_n / l^k G_n ⟶ G_m / l^k G_m` of cokernels of `l^k • 𝟙` induced by the
transition map `G_n ⟶ G_m`. -/
def powSMulCokernelMap (l : R) (k : ℕ) {m n : ℤ} (h : m ≤ n) :
    cokernel (l ^ k • 𝟙 (G.obj (op n))) ⟶ cokernel (l ^ k • 𝟙 (G.obj (op m))) :=
  cokernel.map _ _ (G.map (homOfLE h).op) (G.map (homOfLE h).op) (by
    rw [CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul, Category.id_comp,
      Category.comp_id])

@[reassoc (attr := simp)]
theorem π_powSMulCokernelMap (l : R) (k : ℕ) {m n : ℤ} (h : m ≤ n) :
    cokernel.π _ ≫ G.powSMulCokernelMap l k h = G.map (homOfLE h).op ≫ cokernel.π _ := by
  simp [powSMulCokernelMap]

/-- The map along `n ≤ n` is the identity. -/
theorem powSMulCokernelMap_refl (l : R) (k : ℕ) (n : ℤ) :
    G.powSMulCokernelMap l k (le_refl n) = 𝟙 _ := by
  ext
  rw [π_powSMulCokernelMap, show (homOfLE (le_refl n)).op = 𝟙 (op n) from rfl, G.map_id,
    Category.id_comp, Category.comp_id]

theorem isIso_powSMulCokernelMap_refl (l : R) (k : ℕ) (n : ℤ) :
    IsIso (G.powSMulCokernelMap l k (le_refl n)) := by
  rw [powSMulCokernelMap_refl]
  infer_instance

/-- The maps along `m ≤ n` and `n ≤ p` compose to the map along `m ≤ p`. -/
@[reassoc]
theorem powSMulCokernelMap_comp (l : R) (k : ℕ) {m n p : ℤ} (h₁ : m ≤ n) (h₂ : n ≤ p) :
    G.powSMulCokernelMap l k h₂ ≫ G.powSMulCokernelMap l k h₁ =
      G.powSMulCokernelMap l k (h₁.trans h₂) := by
  ext
  rw [π_powSMulCokernelMap_assoc, π_powSMulCokernelMap, π_powSMulCokernelMap, ← G.map_comp_assoc]
  rfl

/-- **Condition (b) of the A–R `l`-adic conditions** for a projective system `G : ℤᵒᵖ ⥤ C`: for
all `n ≥ 0` and `t ≥ s` the map `G_{n+t} / l^{n+1} G_{n+t} ⟶ G_{n+s} / l^{n+1} G_{n+s}` induced
by the transition map `G_{n+t} ⟶ G_{n+s}` is an isomorphism. -/
def IsLAdicStableFrom (l : R) (s : ℕ) : Prop :=
  ∀ (n t : ℕ) (hst : s ≤ t),
    IsIso (G.powSMulCokernelMap l (n + 1) (by omega : (n : ℤ) + s ≤ n + t))

end Functor

end CategoryTheory

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

/-- The cokernel of `l^k • 𝟙` on a module `M` is the quotient `M ⧸ l^k M`. -/
def cokernelPowSMulIso (M : ModuleCat.{v} Λ) (l : Λ) (k : ℕ) :
    cokernel (l ^ k • 𝟙 M) ≅
      ModuleCat.of Λ (M ⧸ LinearMap.range (l ^ k • LinearMap.id : M →ₗ[Λ] M)) :=
  ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp)]
theorem cokernel_π_cokernelPowSMulIso_hom (M : ModuleCat.{v} Λ) (l : Λ) (k : ℕ) :
    cokernel.π _ ≫ (cokernelPowSMulIso M l k).hom =
      ModuleCat.ofHom (LinearMap.range (l ^ k • LinearMap.id : M →ₗ[Λ] M)).mkQ :=
  ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _

theorem range_powSMul_le_comap {M N : ModuleCat.{v} Λ} (f : M ⟶ N) (l : Λ) (k : ℕ) :
    LinearMap.range (l ^ k • LinearMap.id : M →ₗ[Λ] M) ≤
      (LinearMap.range (l ^ k • LinearMap.id : N →ₗ[Λ] N)).comap f.hom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f.hom x, by simp⟩

/-- For a projective system of modules, the map `G_n / l^k G_n ⟶ G_m / l^k G_m` is an
isomorphism if and only if the induced map of quotient modules is bijective. -/
theorem isIso_powSMulCokernelMap_iff_bijective (G : ℤᵒᵖ ⥤ ModuleCat.{v} Λ) (l : Λ) (k : ℕ)
    {m n : ℤ} (h : m ≤ n) :
    IsIso (G.powSMulCokernelMap l k h) ↔
      Function.Bijective (Submodule.mapQ _ _ (G.map (homOfLE h).op).hom
        (range_powSMul_le_comap (G.map (homOfLE h).op) l k)) := by
  have e : (cokernelPowSMulIso (G.obj (op n)) l k).inv ≫ G.powSMulCokernelMap l k h ≫
      (cokernelPowSMulIso (G.obj (op m)) l k).hom =
        ModuleCat.ofHom (Submodule.mapQ _ _ (G.map (homOfLE h).op).hom
          (range_powSMul_le_comap (G.map (homOfLE h).op) l k)) := by
    rw [← cancel_epi (cokernelPowSMulIso (G.obj (op n)) l k).hom, Iso.hom_inv_id_assoc,
      ← cancel_epi (cokernel.π _), Functor.π_powSMulCokernelMap_assoc,
      cokernel_π_cokernelPowSMulIso_hom, cokernel_π_cokernelPowSMulIso_hom_assoc]
    ext x
    rfl
  have hb : IsIso (ModuleCat.ofHom (Submodule.mapQ _ _
      (G.map (homOfLE h).op).hom (range_powSMul_le_comap (G.map (homOfLE h).op) l k))) ↔
      Function.Bijective (Submodule.mapQ _ _
        (G.map (homOfLE h).op).hom (range_powSMul_le_comap (G.map (homOfLE h).op) l k)) :=
    ConcreteCategory.isIso_iff_bijective _
  rw [← e] at hb
  refine Iff.trans ?_ hb
  constructor
  · intro _
    infer_instance
  · intro _
    have : G.powSMulCokernelMap l k h = (cokernelPowSMulIso (G.obj (op n)) l k).hom ≫
        ((cokernelPowSMulIso (G.obj (op n)) l k).inv ≫ G.powSMulCokernelMap l k h ≫
          (cokernelPowSMulIso (G.obj (op m)) l k).hom) ≫
        (cokernelPowSMulIso (G.obj (op m)) l k).inv := by simp
    rw [this]
    infer_instance

end ModuleCat

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- **The A–R `l`-adic conditions with constants `(r, s)`** for a projective system `F` of
`l`-power torsion `Λ`-modules: (a) `F` satisfies the Mittag-Leffler–Artin–Rees condition with
constant `r`, and (b) for all `n ≥ 0` and `t ≥ s` the map
`F̄_{n+t} / l^{n+1} F̄_{n+t} ⟶ F̄_{n+s} / l^{n+1} F̄_{n+s}` induced by the transition map of the
system `F̄` of universal images is an isomorphism. -/
@[weil "def_fk112_ar_l_adic_criterion_conditions"]
structure SatisfiesArLAdicConditions (F : ProjectiveSystem.{v} Λ l) (r s : ℕ) : Prop where
  /-- (a) `F` satisfies MLAR with constant `r`. -/
  isMittagLefflerArtinReesWith : F.IsMittagLefflerArtinReesWith r
  /-- (b) The maps `F̄_{n+t} / l^{n+1} F̄_{n+t} ⟶ F̄_{n+s} / l^{n+1} F̄_{n+s}`, `t ≥ s`, are
  isomorphisms. -/
  isLAdicStableFrom : F.universalImageSystem.obj.IsLAdicStableFrom l s

end ProjectiveSystem

end CategoryTheory

namespace AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {l : ℕ}

/-- **The A–R `l`-adic conditions with constants `(r, s)`** for an object `F` of the category
`P_S` of projective systems of `l`-torsion sheaves: (a) `F` satisfies the
Mittag-Leffler–Artin–Rees condition with constant `r`, and (b) for all `n ≥ 0` and `t ≥ s` the
morphism `F̄_{n+t} / l^{n+1} F̄_{n+t} ⟶ F̄_{n+s} / l^{n+1} F̄_{n+s}` of cokernel sheaves induced by
the transition map of the system `F̄` of universal images is an isomorphism. -/
@[weil "def_fk112_ar_l_adic_criterion_conditions"]
structure SatisfiesArLAdicConditions (F : LTorsionProjectiveSystem.{u} B S hS l) (r s : ℕ) :
    Prop where
  /-- (a) `F` satisfies MLAR with constant `r`. -/
  isMittagLefflerArtinReesWith : IsMittagLefflerArtinReesWith F r
  /-- (b) The maps `F̄_{n+t} / l^{n+1} F̄_{n+t} ⟶ F̄_{n+s} / l^{n+1} F̄_{n+s}`, `t ≥ s`, are
  isomorphisms. -/
  isLAdicStableFrom : F.universalImageSystem.obj.IsLAdicStableFrom l s

end AlgebraicGeometry.SmallEtale.LTorsionProjectiveSystem

end
