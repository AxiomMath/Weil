module

public import Weil.Attr
public import Weil.Defs.CategoryTheory.ObjectProperty.ArCategory
public import Weil.Defs.CategoryTheory.ObjectProperty.ArHom
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# The projective-limit functor on the Artin–Rees category

For a projective system `F = (F_n, u_n)_{n ∈ ℤ}` of `l`-power torsion `Λ`-modules, the projective
limit `lim F` is the `Λ`-module of families `(x_n) ∈ ∏_{n ∈ ℤ} F_n` with `u_n(x_n) = x_{n-1}` for
all `n`. For an A–R morphism `φ : F → G` with representative `(r, f)`, `f : F[r] ⟶ G`, the map
`lim_{(r, f)} : lim F → ∏_n G_n` is `(x_n)_n ↦ (f_n(x_{n+r}))_n`. It takes values in `lim G`, is
`Λ`-linear and does not depend on the representative, and these maps make `F ↦ lim F` a functor
from the A–R category to `Λ`-modules.

## Main definitions

* `CategoryTheory.ProjectiveSystem.limMapRep r f`: the linear map
  `lim_{(r, f)} : lim F → ∏_n G_n`, `(x_n)_n ↦ (f_n(x_{n+r}))_n`.
* `CategoryTheory.ProjectiveSystem.ArHom.limMap φ`: the linear map `lim F → lim G` of an A–R
  morphism `φ`, equal to `lim_{(r, f)}` for every representative `(r, f)` of `φ`.
* `CategoryTheory.ProjectiveSystem.ArCategory.limFunctor`: the projective-limit functor from the
  A–R category to `Λ`-modules.

## Main results

* `CategoryTheory.ProjectiveSystem.mem_sectionsSubmodule_iff`: a family `(x_n)` lies in `lim F`
  if and only if `u_n(x_n) = x_{n-1}` for all `n`.
* `CategoryTheory.ProjectiveSystem.limMapRep_mem`: `lim_{(r, f)}` takes values in `lim G`.
* `CategoryTheory.ProjectiveSystem.limMapRep_shiftMap_comp`: `lim_{(r, f)}` is unchanged when
  `(r, f)` is replaced by `(t, f ∘ (F[t] ⟶ F[r]))`, so it only depends on the class `[r, f]`.
* `CategoryTheory.ProjectiveSystem.ArCategory.limFunctor_map_homMk_apply`: the map of `[r, f]` is
  `lim_{(r, f)}`.

## Implementation notes

The projective limit of `F` is Mathlib's module of sections `ModuleCat.sectionsSubmodule F.obj`
of the functor `F.obj : ℤᵒᵖ ⥤ ModuleCat Λ`, which is the limit of `F.obj` in `ModuleCat Λ`
(`ModuleCat.limitConeIsLimit`). Its families are indexed by `ℤᵒᵖ` and are compatible with all
the maps `F_n ⟶ F_m`, `m ≤ n`; these are composites of the maps `u_n`, so this is the source's
condition (`mem_sectionsSubmodule_iff`).

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- An element of `lim F` is compatible with every map of the functor `F.obj`. -/
lemma map_apply_of_mem_sectionsSubmodule (F : ProjectiveSystem.{v} Λ l)
    {x : ∀ n : ℤᵒᵖ, F.obj.obj n} (hx : x ∈ ModuleCat.sectionsSubmodule F.obj)
    {a b : ℤᵒᵖ} (h : a ⟶ b) : F.obj.map h (x a) = x b :=
  hx h

/-- A family `(x_n) ∈ ∏_n F_n` lies in `lim F` if and only if `u_n(x_n) = x_{n-1}` for all `n`. -/
@[weil "def_fk112_ar_limit_functor"]
lemma mem_sectionsSubmodule_iff (F : ProjectiveSystem.{v} Λ l) (x : ∀ n : ℤᵒᵖ, F.obj.obj n) :
    x ∈ ModuleCat.sectionsSubmodule F.obj ↔
      ∀ n : ℤ, F.transition n (x (op n)) = x (op (n - 1)) := by
  constructor
  · intro hx n
    exact hx _
  · intro hx
    have adj : ∀ (m n : ℤ) (hmn : m ≤ n), m = n - 1 →
        F.obj.map (homOfLE hmn).op (x (op n)) = x (op m) := by
      rintro m n hmn rfl
      exact hx n
    have key : ∀ (b a : ℤ) (hba : b ≤ a), F.obj.map (homOfLE hba).op (x (op a)) = x (op b) := by
      intro b a hba
      induction a, hba using Int.leInduction with
      | base =>
        change F.obj.map (𝟙 _) (x (op b)) = x (op b)
        simp
      | succ a hba ih =>
        have e : (homOfLE (Int.le_add_one hba)).op =
            (homOfLE (Int.le_add_one (le_refl a))).op ≫ (homOfLE hba).op := Subsingleton.elim _ _
        rw [e, Functor.map_comp, ModuleCat.comp_apply, adj a (a + 1) _ (by omega), ih]
    rintro ⟨a⟩ ⟨b⟩ h
    have hba : b ≤ a := leOfHom h.unop
    obtain rfl : h = (homOfLE hba).op := Subsingleton.elim _ _
    exact key b a hba

variable {F G : ProjectiveSystem.{v} Λ l}

/-- The map `lim_{(r, f)} : lim F → ∏_n G_n`, `(x_n)_n ↦ (f_n(x_{n+r}))_n`, of a representative
`(r, f)`, `f : F[r] ⟶ G`, of an A–R morphism. -/
@[weil "def_fk112_ar_limit_functor"]
def limMapRep (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G) :
    ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] (∀ n : ℤᵒᵖ, G.obj.obj n) where
  toFun x n := (app f n.unop).hom (x.1 (op (n.unop + r)))
  map_add' x y := by
    funext n
    exact map_add (app f n.unop).hom _ _
  map_smul' c x := by
    funext n
    exact (app f n.unop).hom.map_smul c _

@[simp]
lemma limMapRep_apply (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G)
    (x : ModuleCat.sectionsSubmodule F.obj) (n : ℤᵒᵖ) :
    limMapRep r f x n = (app f n.unop).hom (x.1 (op (n.unop + r))) := rfl

/-- `lim_{(r, f)}` takes values in `lim G`. -/
lemma limMapRep_mem (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G)
    (x : ModuleCat.sectionsSubmodule F.obj) :
    limMapRep r f x ∈ ModuleCat.sectionsSubmodule G.obj := by
  rintro ⟨a⟩ ⟨b⟩ h
  have hn := ConcreteCategory.congr_hom (f.hom.naturality h) (x.1 (op (a + r)))
  change G.obj.map h ((app f a).hom (x.1 (op (a + r)))) = (app f b).hom (x.1 (op (b + r)))
  refine hn.symm.trans ?_
  exact congrArg (app f b).hom (x.2 ((translate (r : ℤ)).map h))

/-- `lim_{(r, f)}` is unchanged when `(r, f)` is replaced by `(t, f ∘ (F[t] ⟶ F[r]))`. -/
lemma limMapRep_shiftMap_comp {r t : ℕ} (h : r ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G) :
    limMapRep t (shiftMap F h ≫ f) = limMapRep r f := by
  ext x n
  exact congrArg (app f n.unop).hom (x.2 (homOfLE (by omega : n.unop + r ≤ n.unop + t)).op)

/-- `lim_{(r, f)}` as a linear map `lim F → lim G`. -/
def limMapRepRestrict (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G) :
    ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule G.obj :=
  (limMapRep r f).codRestrict _ (limMapRep_mem r f)

@[simp]
lemma coe_limMapRepRestrict_apply (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G)
    (x : ModuleCat.sectionsSubmodule F.obj) :
    (limMapRepRestrict r f x : ∀ n : ℤᵒᵖ, G.obj.obj n) = limMapRep r f x := rfl

lemma limMapRepRestrict_shiftMap_comp {r t : ℕ} (h : r ≤ t) (f : (shift (r : ℤ)).obj F ⟶ G) :
    limMapRepRestrict t (shiftMap F h ≫ f) = limMapRepRestrict r f := by
  ext x : 2
  simp [limMapRep_shiftMap_comp]

namespace ArHom

/-- The linear map `lim φ : lim F → lim G` of an A–R morphism `φ`: it is `lim_{(r, f)}` for any
representative `(r, f)` of `φ` (`limMap_mk`). -/
def limMap (φ : ArHom F G) :
    ModuleCat.sectionsSubmodule F.obj →ₗ[Λ] ModuleCat.sectionsSubmodule G.obj :=
  lift (fun p => limMapRepRestrict p.1 p.2) (fun _ _ h f => limMapRepRestrict_shiftMap_comp h f) φ

@[simp]
lemma limMap_mk (r : ℕ) (f : (shift (r : ℤ)).obj F ⟶ G) :
    limMap (mk r f) = limMapRepRestrict r f := rfl

end ArHom

namespace ArCategory

/-- The *projective-limit functor* on the A–R category: it sends a projective system `F` to
`lim F = {(x_n) ∈ ∏_n F_n : u_n(x_n) = x_{n-1}}` (`mem_sectionsSubmodule_iff`), and an A–R
morphism `φ` with representative `(r, f)` to `lim_{(r, f)}`, `(x_n)_n ↦ (f_n(x_{n+r}))_n`
(`limFunctor_map_homMk_apply`). -/
@[weil "def_fk112_ar_limit_functor"]
def limFunctor : ArCategory.{v} Λ l ⥤ ModuleCat.{v} Λ where
  obj X := ModuleCat.of Λ (ModuleCat.sectionsSubmodule X.obj.obj)
  map φ := ModuleCat.ofHom (ArHom.limMap φ)
  map_id X := by
    ext x : 2
    apply Subtype.ext
    funext n
    exact x.2 (homOfLE (by simp : n.unop ≤ n.unop + ((0 : ℕ) : ℤ))).op
  map_comp {X Y Z} φ ψ := by
    induction φ using hom_induction with
    | h r f =>
    induction ψ using hom_induction with
    | h s g =>
    ext x : 2
    apply Subtype.ext
    funext n
    exact congrArg (fun y => (app g n.unop).hom ((app f (n.unop + s)).hom y))
      (x.2 (homOfLE (by push_cast; omega : n.unop + s + r ≤ n.unop + ((r + s : ℕ) : ℤ))).op)

lemma limFunctor_obj (F : ProjectiveSystem.{v} Λ l) :
    limFunctor.obj (of F) = ModuleCat.of Λ (ModuleCat.sectionsSubmodule F.obj) := rfl

/-- The map of the A–R morphism `[r, f]` under the projective-limit functor is `lim_{(r, f)}`,
`(x_n)_n ↦ (f_n(x_{n+r}))_n`. -/
@[weil "def_fk112_ar_limit_functor"]
lemma limFunctor_map_homMk_apply {F G : ProjectiveSystem.{v} Λ l} (r : ℕ)
    (f : (shift (r : ℤ)).obj F ⟶ G) (x : ModuleCat.sectionsSubmodule F.obj) :
    ((limFunctor.map (homMk r f)).hom x : ModuleCat.sectionsSubmodule G.obj).1 =
      limMapRep r f x := rfl

end ArCategory

end ProjectiveSystem

end CategoryTheory
