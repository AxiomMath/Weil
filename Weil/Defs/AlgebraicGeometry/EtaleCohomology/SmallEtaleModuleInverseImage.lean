module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import Weil.Attr

/-!
# The inverse-image map on `Ext` groups of étale sheaves of modules

Let `h : Z' ⟶ Z` be a morphism of schemes and `Λ` a ring. The inverse image
`h^* : Mod_Λ(Z) ⥤ Mod_Λ(Z')` of sheaves of `Λ`-modules on the small étale sites
(`Stacks.EtaleCohomology.etaleModuleInverseImage`) is exact. An exact functor between abelian
categories acts on `Ext` groups, so for sheaves `A, B` of `Λ`-modules on `Z` and `p : ℕ` there
is an additive map
`h^* : Ext^p_Λ(Z; A, B) ⟶ Ext^p_Λ(Z'; h^* A, h^* B)`,
the *inverse-image map on `Ext` groups*. In degree `0` it is `h^*` on morphisms, it is compatible
with the Yoneda product, and it carries the extension class of a short exact sequence to the
extension class of its inverse image.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtInverseImage`: the inverse-image map
  `Ext^p_Λ(Z; A, B) →+ Ext^p_Λ(Z'; h^* A, h^* B)`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleExtInverseImage_mk₀`: in degree `0` it is `h^*` on
  morphisms.
* `Stacks.EtaleCohomology.etaleModuleExtInverseImage_comp`: it is compatible with the Yoneda
  product of `Ext` classes; in particular it is natural in both variables
  (`etaleModuleExtInverseImage_mk₀_comp`, `etaleModuleExtInverseImage_comp_mk₀`).
* `Stacks.EtaleCohomology.etaleModuleExtInverseImage_extClass`: it carries the extension class
  of a short exact sequence to that of its inverse image.

## Implementation notes

The source defines a map `Ext^p(A, B) ⟶ Ext^p(h^* A, h^* B)` to be an inverse-image map when it
is `H^p` of the composite
`Hom(A, I^•_B) ⟶ Hom(h^* A, h^* I^•_B) ⟶ Hom(h^* A, I^•_{h^* B})` for some chain map
`h^* I^•_B ⟶ I^•_{h^* B}` of injective resolutions over `h^* B`, and then shows that there is
exactly one such map. Here `Ext` is Mathlib's `CategoryTheory.Abelian.Ext`, computed in the
derived category, and the map is defined directly as the action
`CategoryTheory.Abelian.Ext.mapExactFunctor` of the exact functor `h^*`; the description by
injective resolutions is a property of this map. The schemes are arbitrary: the source's
hypotheses that `Z` and `Z'` are noetherian and separated are not needed for the definition.
Sheaves are taken on Mathlib's small étale site `Z.smallEtaleTopology`, where the exact inverse
image of sheaves of modules is available.

## References

* [Freitag, Kiehl, *Étale Cohomology and the Weil Conjecture*, I.4][FK88]
-/

/- FK's "is an inverse-image map" predicate on maps of Ext groups is replaced by the map itself;
its injective-resolution characterization is proved separately.
Stated on Mathlib's `Z.Etale`, not StacksFrontier's `SmallEtale`: the exact module inverse image
exists only there; the SmallEtale form transports along `SmallEtale.sheafEquiv`. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe w u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ] {Z' Z : Scheme.{u}} (h : Z' ⟶ Z)
  [HasExt.{w} (EtaleModules.{u, r} Λ Z)] [HasExt.{w} (EtaleModules.{u, r} Λ Z')]

/-- **The inverse-image map on `Ext` groups** of sheaves of `Λ`-modules on small étale sites,
`h^* : Ext^p_Λ(Z; A, B) →+ Ext^p_Λ(Z'; h^* A, h^* B)` for a morphism of schemes `h : Z' ⟶ Z`:
the action on `Ext` of the exact inverse-image functor `h^*`. -/
@[weil "def_fk104_inverse_image_map_on_extgroups"]
def etaleModuleExtInverseImage (A B : EtaleModules.{u, r} Λ Z) (p : ℕ) :
    Ext.{w} A B p →+
      Ext.{w} ((etaleModuleInverseImage Λ h).obj A) ((etaleModuleInverseImage Λ h).obj B) p :=
  (etaleModuleInverseImage Λ h).mapExtAddHom A B p

variable {Λ h}

theorem etaleModuleExtInverseImage_apply {A B : EtaleModules.{u, r} Λ Z} {p : ℕ}
    (a : Ext.{w} A B p) :
    etaleModuleExtInverseImage Λ h A B p a = a.mapExactFunctor (etaleModuleInverseImage Λ h) :=
  rfl

/-- In degree `0` the inverse-image map on `Ext` is the inverse image of morphisms. -/
@[simp]
theorem etaleModuleExtInverseImage_mk₀ {A B : EtaleModules.{u, r} Λ Z} (f : A ⟶ B) :
    etaleModuleExtInverseImage Λ h A B 0 (Ext.mk₀ f) =
      Ext.mk₀ ((etaleModuleInverseImage Λ h).map f) :=
  Ext.mapExactFunctor_mk₀ _ f

/-- The inverse-image map on `Ext` is compatible with the Yoneda product. -/
theorem etaleModuleExtInverseImage_comp {A B C : EtaleModules.{u, r} Λ Z} {a b c : ℕ}
    (α : Ext.{w} A B a) (β : Ext.{w} B C b) (hc : a + b = c) :
    etaleModuleExtInverseImage Λ h A C c (α.comp β hc) =
      (etaleModuleExtInverseImage Λ h A B a α).comp (etaleModuleExtInverseImage Λ h B C b β) hc :=
  Ext.mapExactFunctor_comp _ α β hc

/-- Naturality of the inverse-image map on `Ext` in the first variable: for `u : A' ⟶ A`,
`h^* (u^* α) = (h^* u)^* (h^* α)`. -/
theorem etaleModuleExtInverseImage_mk₀_comp {A' A B : EtaleModules.{u, r} Λ Z} {p : ℕ}
    (u : A' ⟶ A) (α : Ext.{w} A B p) :
    etaleModuleExtInverseImage Λ h A' B p ((Ext.mk₀ u).comp α (zero_add p)) =
      (Ext.mk₀ ((etaleModuleInverseImage Λ h).map u)).comp
        (etaleModuleExtInverseImage Λ h A B p α) (zero_add p) := by
  rw [etaleModuleExtInverseImage_comp, etaleModuleExtInverseImage_mk₀]

/-- Naturality of the inverse-image map on `Ext` in the second variable: for `v : B ⟶ B'`,
`h^* (v_* α) = (h^* v)_* (h^* α)`. -/
theorem etaleModuleExtInverseImage_comp_mk₀ {A B B' : EtaleModules.{u, r} Λ Z} {p : ℕ}
    (α : Ext.{w} A B p) (v : B ⟶ B') :
    etaleModuleExtInverseImage Λ h A B' p (α.comp (Ext.mk₀ v) (add_zero p)) =
      (etaleModuleExtInverseImage Λ h A B p α).comp
        (Ext.mk₀ ((etaleModuleInverseImage Λ h).map v)) (add_zero p) := by
  rw [etaleModuleExtInverseImage_comp, etaleModuleExtInverseImage_mk₀]

/-- The inverse-image map on `Ext¹` carries the extension class of a short exact sequence to the
extension class of its inverse image. -/
theorem etaleModuleExtInverseImage_extClass {S : ShortComplex (EtaleModules.{u, r} Λ Z)}
    (hS : S.ShortExact) :
    etaleModuleExtInverseImage Λ h S.X₃ S.X₁ 1 hS.extClass =
      (hS.map_of_exact (etaleModuleInverseImage Λ h)).extClass :=
  Ext.mapExactFunctor_extClass _ hS

end Stacks.EtaleCohomology
