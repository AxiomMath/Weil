module

public import Weil.Attr
public import WeilFrontier.Defs.Algebra.Category.ModuleCat.Limits
public import WeilFrontier.Defs.CategoryTheory.ObjectProperty.ArCanonicalFunctor

/-!
# The projective-limit functor on the Artin–Rees category is well defined and additive

For an A–R morphism `φ : F → G` with representative `(r, f)`, `f : F[r] ⟶ G`, the map
`lim_{(r, f)} : (x_n)_n ↦ (f_n(x_{n+r}))_n` takes values in `lim G`, is `Λ`-linear and does not
depend on the representative: it is the map of `φ` under the projective-limit functor
`CategoryTheory.ProjectiveSystem.ArCategory.limFunctor`. This functor is additive, and on the
image of a morphism `g` of projective systems under the canonical functor `q` it is the usual map
`(x_n)_n ↦ (g_n(x_n))_n`.

## Main results

* `CategoryTheory.ProjectiveSystem.ArCategory.limMapRep_eq_limFunctor_map`: for every
  representative `(r, f)` of `φ`, `lim_{(r, f)} x = lim φ x`; in particular `lim_{(r, f)}` takes
  values in `lim G` and only depends on `φ`.
* `CategoryTheory.ProjectiveSystem.ArCategory.limMapRep_eq_of_homMk_eq`: two representatives of
  one A–R morphism give the same map.
* `CategoryTheory.ProjectiveSystem.ArCategory.limFunctor_additive`: the projective-limit functor
  is additive.
* `CategoryTheory.ProjectiveSystem.ArCategory.limFunctor_map_toArCategory_map_apply`:
  `lim q(g)` is `(x_n)_n ↦ (g_n(x_n))_n`.

## References

* [FK] E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, Chapter I, §12.
-/

@[expose] public section

universe v u

open Opposite

namespace CategoryTheory

namespace ProjectiveSystem

variable {Λ : Type u} [CommRing Λ] {l : Λ}

/-- `lim_{(r, f)}` is additive in `f`. -/
lemma limMapRep_add {F G : ProjectiveSystem.{v} Λ l} (r : ℕ) (f g : (shift (r : ℤ)).obj F ⟶ G) :
    limMapRep r (f + g) = limMapRep r f + limMapRep r g := by
  ext x n
  rfl

namespace ArCategory

/-- For every representative `(r, f)` of an A–R morphism `φ : F → G`, the map
`lim_{(r, f)} : (x_n)_n ↦ (f_n(x_{n+r}))_n` agrees with the map of `φ` under the projective-limit
functor. Hence `lim_{(r, f)}` takes values in `lim G`, is `Λ`-linear, and does not depend on the
representative. -/
@[weil "lem_fk112_ar_limit_functor_well_defined"]
theorem limMapRep_eq_limFunctor_map {F G : ProjectiveSystem.{v} Λ l} (φ : of F ⟶ of G) (r : ℕ)
    (f : (shift (r : ℤ)).obj F ⟶ G) (hφ : homMk r f = φ)
    (x : ModuleCat.sectionsSubmodule F.obj) :
    limMapRep r f x = ((limFunctor.map φ).hom x : ModuleCat.sectionsSubmodule G.obj).1 := by
  subst hφ
  rfl

/-- Two representatives of the same A–R morphism give the same map `lim F → ∏_n G_n`. -/
@[weil "lem_fk112_ar_limit_functor_well_defined"]
theorem limMapRep_eq_of_homMk_eq {F G : ProjectiveSystem.{v} Λ l} {r s : ℕ}
    (f : (shift (r : ℤ)).obj F ⟶ G) (g : (shift (s : ℤ)).obj F ⟶ G)
    (h : homMk r f = homMk s g) : limMapRep r f = limMapRep s g := by
  ext x : 1
  rw [limMapRep_eq_limFunctor_map _ r f h, limMapRep_eq_limFunctor_map _ s g rfl]

/-- The projective-limit functor on the A–R category is additive. -/
@[weil "lem_fk112_ar_limit_functor_well_defined"]
instance limFunctor_additive : (limFunctor.{v} (Λ := Λ) (l := l)).Additive where
  map_add {X Y φ ψ} := by
    induction φ using hom_induction with
    | h r f =>
    induction ψ using hom_induction with
    | h s g =>
    rw [homMk_add_homMk (max r s) (le_max_left r s) (le_max_right r s)]
    ext x : 2
    apply Subtype.ext
    have key : limMapRep (max r s) (X.obj.shiftMap (le_max_left r s) ≫ f +
        X.obj.shiftMap (le_max_right r s) ≫ g) = limMapRep r f + limMapRep s g := by
      rw [limMapRep_add, limMapRep_shiftMap_comp, limMapRep_shiftMap_comp]
    exact congrArg (fun m => m x) key

/-- The map of `q(g)`, for a morphism `g : F ⟶ G` of projective systems, under the
projective-limit functor is the usual map `(x_n)_n ↦ (g_n(x_n))_n`. -/
@[weil "lem_fk112_ar_limit_functor_well_defined"]
theorem limFunctor_map_toArCategory_map_apply {F G : ProjectiveSystem.{v} Λ l} (g : F ⟶ G)
    (x : ModuleCat.sectionsSubmodule F.obj) (n : ℤ) :
    ((limFunctor.map ((toArCategory Λ l).map g)).hom x :
        ModuleCat.sectionsSubmodule G.obj).1 (op n) = (app g n).hom (x.1 (op n)) := by
  change limMapRep 0 (natMap F 0 ≫ g) x (op n) = _
  rw [limMapRep_apply, comp_app, natMap_app]
  exact congrArg (app g n).hom (x.2 _)

end ArCategory

end ProjectiveSystem

end CategoryTheory
