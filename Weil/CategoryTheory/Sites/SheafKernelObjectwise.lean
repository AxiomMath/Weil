module

public import Weil.Attr
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# The objectwise kernel of a morphism of abelian sheaves

Let `α : F ⟶ G` be a morphism of presheaves of abelian groups on a category `C`. The
*objectwise kernel* of `α` is the presheaf `U ↦ ker (α_U)`, with the restriction maps of `F`;
together with its inclusion into `F` it is a kernel of `α` in the category of presheaves.

When `F` and `G` are sheaves for a Grothendieck topology `J` on `C`, the objectwise kernel is
again a sheaf, and its inclusion into `F` is a kernel of `α` in the category of sheaves of
abelian groups. Applied to the étale topology `Scheme.AffineEtale.topology (Spec A)` of the étale
category `Et(A)` of a commutative ring `A`, this is the statement that kernels of morphisms of
abelian étale sheaves on `Et(A)` are computed objectwise.

## Main definitions

- `CategoryTheory.Presheaf.objectwiseKernel α`: the presheaf `U ↦ ker (α_U)`.
- `CategoryTheory.Presheaf.objectwiseKernelι α`: its inclusion into the source of `α`.
- `CategoryTheory.Sheaf.objectwiseKernel α`: the objectwise kernel of a morphism of sheaves of
  abelian groups, as a sheaf.

## Main results

- `CategoryTheory.Presheaf.isLimitObjectwiseKernelFork`: the objectwise kernel is a kernel in
  presheaves.
- `CategoryTheory.Presheaf.isSheaf_objectwiseKernel`: the objectwise kernel of a morphism of
  sheaves is a sheaf.
- `CategoryTheory.Sheaf.isLimitObjectwiseKernelFork`: the objectwise kernel is a kernel in the
  category of sheaves of abelian groups.

## Implementation notes

The results are stated for an arbitrary site; the étale category `Et(A)` with its étale topology
is the case `J = Scheme.AffineEtale.topology (Spec A)`. That the objectwise kernel is a sheaf is
deduced from the fact that a limit, formed in presheaves, of a diagram of sheaves is a sheaf
(`CategoryTheory.Sheaf.isSheaf_of_isLimit`).

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FreitagKiehl1988], I.1
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Presheaf

variable {C : Type u} [Category.{v} C] {F G : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (α : F ⟶ G)

/-- The objectwise kernel `U ↦ ker (α_U)` of a morphism `α` of presheaves of abelian groups,
with the restriction maps induced by those of the source. -/
def objectwiseKernel : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (α.app U).hom.ker
  map {U V} g := AddCommGrpCat.ofHom <|
    ((F.map g).hom.comp (α.app U).hom.ker.subtype).codRestrict _ fun x ↦ by
      have := congrArg (fun h ↦ h.hom x.1) (α.naturality g)
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at this
      simp [AddMonoidHom.mem_ker, this, AddMonoidHom.mem_ker.1 x.2]
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp

@[simp]
lemma objectwiseKernel_obj (U : Cᵒᵖ) :
    (objectwiseKernel α).obj U = AddCommGrpCat.of (α.app U).hom.ker := rfl

@[simp]
lemma coe_objectwiseKernel_map_apply {U V : Cᵒᵖ} (g : U ⟶ V) (x : (objectwiseKernel α).obj U) :
    (((objectwiseKernel α).map g).hom x).1 = (F.map g).hom x.1 := rfl

/-- The inclusion of the objectwise kernel of `α` into the source of `α`. -/
def objectwiseKernelι : objectwiseKernel α ⟶ F where
  app U := AddCommGrpCat.ofHom (α.app U).hom.ker.subtype
  naturality _ _ _ := rfl

@[simp]
lemma objectwiseKernelι_app_apply (U : Cᵒᵖ) (x : (objectwiseKernel α).obj U) :
    ((objectwiseKernelι α).app U).hom x = x.1 := rfl

@[reassoc (attr := simp)]
lemma objectwiseKernelι_comp : objectwiseKernelι α ≫ α = 0 := by
  ext U x
  exact AddMonoidHom.mem_ker.1 x.2

/-- The objectwise kernel of `α` as a kernel fork of `α`. -/
abbrev objectwiseKernelFork : KernelFork α :=
  KernelFork.ofι (objectwiseKernelι α) (objectwiseKernelι_comp α)

/-- The morphism into the objectwise kernel induced by a morphism `h` with `h ≫ α = 0`. -/
def objectwiseKernelLift {T : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (h : T ⟶ F) (hh : h ≫ α = 0) :
    T ⟶ objectwiseKernel α where
  app U := AddCommGrpCat.ofHom <| (h.app U).hom.codRestrict _ fun x ↦ by
    have := congrArg (fun k ↦ (k.app U).hom x) hh
    simpa using this
  naturality U V g := by
    ext x
    apply Subtype.ext
    exact congrArg (fun k ↦ k.hom x) (h.naturality g)

@[reassoc (attr := simp)]
lemma objectwiseKernelLift_ι {T : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (h : T ⟶ F) (hh : h ≫ α = 0) :
    objectwiseKernelLift α h hh ≫ objectwiseKernelι α = h := rfl

lemma objectwiseKernel_hom_ext {T : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {f g : T ⟶ objectwiseKernel α}
    (h : f ≫ objectwiseKernelι α = g ≫ objectwiseKernelι α) : f = g := by
  ext U x
  apply Subtype.ext
  exact congrArg (fun k ↦ (k.app U).hom x) h

/-- The objectwise kernel of a morphism of presheaves of abelian groups is a kernel in the
category of presheaves. -/
def isLimitObjectwiseKernelFork : IsLimit (objectwiseKernelFork α) :=
  KernelFork.IsLimit.ofι _ _ (fun h hh ↦ objectwiseKernelLift α h hh)
    (fun h hh ↦ objectwiseKernelLift_ι α h hh)
    (fun h hh m hm ↦ objectwiseKernel_hom_ext α (by rw [hm, objectwiseKernelLift_ι]))

/-- **The objectwise kernel of a morphism of sheaves is a sheaf** [FK, I.1]. If `α` is a
morphism of presheaves of abelian groups whose source and target are sheaves for `J`, then the
presheaf `U ↦ ker (α_U)` is a sheaf for `J`. -/
@[weil "lem_fk101_sheaf_kernel_objectwise"]
theorem isSheaf_objectwiseKernel (J : GrothendieckTopology C) (hF : IsSheaf J F)
    (hG : IsSheaf J G) : IsSheaf J (objectwiseKernel α) := by
  refine ObjectProperty.prop_of_isLimit (IsSheaf J (A := AddCommGrpCat.{w}))
    (isLimitObjectwiseKernelFork α) ?_
  rintro (_ | _)
  exacts [hF, hG]

end Presheaf

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J AddCommGrpCat.{w}} (α : F ⟶ G)

/-- The objectwise kernel `U ↦ ker (α_U)` of a morphism of sheaves of abelian groups, as a
sheaf. -/
def objectwiseKernel : Sheaf J AddCommGrpCat.{w} :=
  ⟨Presheaf.objectwiseKernel α.hom,
    Presheaf.isSheaf_objectwiseKernel α.hom J F.property G.property⟩

@[simp]
lemma objectwiseKernel_obj : (objectwiseKernel α).obj = Presheaf.objectwiseKernel α.hom := rfl

/-- The inclusion of the objectwise kernel of `α` into the source of `α`. -/
def objectwiseKernelι : objectwiseKernel α ⟶ F :=
  ObjectProperty.homMk (Presheaf.objectwiseKernelι α.hom)

@[simp]
lemma objectwiseKernelι_hom : (objectwiseKernelι α).hom = Presheaf.objectwiseKernelι α.hom := rfl

@[reassoc (attr := simp)]
lemma objectwiseKernelι_comp : objectwiseKernelι α ≫ α = 0 :=
  Sheaf.hom_ext (Presheaf.objectwiseKernelι_comp α.hom)

/-- The morphism into the objectwise kernel induced by a morphism `h` with `h ≫ α = 0`. -/
def objectwiseKernelLift {T : Sheaf J AddCommGrpCat.{w}} (h : T ⟶ F) (hh : h ≫ α = 0) :
    T ⟶ objectwiseKernel α :=
  ObjectProperty.homMk (Presheaf.objectwiseKernelLift α.hom h.hom (by
    simpa using congrArg (fun k ↦ k.hom) hh))

@[reassoc (attr := simp)]
lemma objectwiseKernelLift_ι {T : Sheaf J AddCommGrpCat.{w}} (h : T ⟶ F) (hh : h ≫ α = 0) :
    objectwiseKernelLift α h hh ≫ objectwiseKernelι α = h :=
  Sheaf.hom_ext (Presheaf.objectwiseKernelLift_ι _ _ (by
    simpa using congrArg (fun k ↦ k.hom) hh))

lemma objectwiseKernel_hom_ext {T : Sheaf J AddCommGrpCat.{w}} {f g : T ⟶ objectwiseKernel α}
    (h : f ≫ objectwiseKernelι α = g ≫ objectwiseKernelι α) : f = g :=
  Sheaf.hom_ext (Presheaf.objectwiseKernel_hom_ext α.hom (congrArg (fun k ↦ k.hom) h))

/-- **The objectwise kernel is a kernel in sheaves** [FK, I.1]. For a morphism `α` of sheaves of
abelian groups, the objectwise kernel `U ↦ ker (α_U)` with its inclusion into the source is a
kernel of `α` in the category of sheaves of abelian groups. -/
@[weil "lem_fk101_sheaf_kernel_objectwise"]
def isLimitObjectwiseKernelFork :
    IsLimit (KernelFork.ofι (objectwiseKernelι α) (objectwiseKernelι_comp α)) :=
  KernelFork.IsLimit.ofι _ _ (fun h hh ↦ objectwiseKernelLift α h hh)
    (fun h hh ↦ objectwiseKernelLift_ι α h hh)
    (fun h hh m hm ↦ objectwiseKernel_hom_ext α (by rw [hm, objectwiseKernelLift_ι]))

end Sheaf

end CategoryTheory
