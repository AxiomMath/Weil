module

public import Weil.Attr
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Weil.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import Weil.AlgebraicGeometry.Topologies.Etale.NoetherianSeparatedComparison
public import Weil.Defs.AlgebraicGeometry.Topologies.Etale.SheafRestriction

/-!
# The constant sheaf `F_S` and restriction, on the small étale site

For a set (resp. an abelian group) `F`, the presheaf of locally constant `F`-valued maps on the
étale category `Et(S)` of noetherian separated étale `S`-schemes is an étale sheaf `F_S`. This
file gives the same statements on the small étale site `SmallEtale B S hS` of [Stacks, Tag 021B]
and compares the two sides.

On the small étale site the presheaf `V ↦ LocallyConstant |V| F` satisfies the sheaf condition
for every jointly surjective presieve, by the same argument as on `Et(S)`, the fibre products
now being those of the small étale site. Hence it is a sheaf of sets, and a sheaf of abelian
groups, for the étale topology, for `F` in any universe. For `S` locally noetherian the
comparison equivalence between sheaves on `Et(S)` and on the small étale site
(`AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquiv`, whose inverse is restriction)
matches `F_S` with this small étale sheaf.

Restriction of a presheaf on `Et(S)` to `Et(U)` corresponds to restriction of a presheaf on the
small étale site of `S` to that of `U`, along composition with `U ⟶ S`
(`AlgebraicGeometry.smallEtalePostcompose`).

## Main definitions

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantSheafSmallEtale`,
  `locallyConstantSheafAbSmallEtale` — the sheaves of locally constant maps on the small étale
  site.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantEtSheaf`,
  `locallyConstantEtSheafAb` — `F_S` as a sheaf for the topology of `Et(S)`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.sheafEquivFunctorObjLocallyConstantEtSheafIso`,
  `sheafEquivFunctorObjLocallyConstantEtSheafAbIso` — `F_S` corresponds to the small étale
  sheaf under `sheafEquiv`.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheafEquivFin_smallEtale`
  — sections over a noetherian separated `V` are the maps from the connected components of `V`.

## Main results

* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheaf_isSheafFor_smallEtale`,
  `locallyConstantPresheafAb_isSheafFor_smallEtale` — the sheaf condition for jointly
  surjective presieves of the small étale site.
* `AlgebraicGeometry.SmallNoetherianSeparatedEtale.locallyConstantPresheaf_isSheaf_smallEtale`,
  `locallyConstantPresheafAb_isSheaf_smallEtale` — the sheaf property for the étale topology.
* `AlgebraicGeometry.EtalePresheaf.restrict_inclusion_op_comp`,
  `AlgebraicGeometry.EtalePresheaf.restrict_sheafEquiv_inverse_obj_obj` — restriction to `Et(U)`
  commutes with restriction to the small étale site of `U`.

## Implementation notes

The abelian sheaf property is deduced from that of the underlying presheaf of sets with
`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`, using that the forgetful functor of abelian
groups reflects limits of every size; so no universe constraint on `F` is needed, unlike for
`AlgebraicGeometry.locallyConstantMapsAb_isSheaf_smallEtale`, which asks `F : Type (max (u+1) v)`.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*, I.2][FreitagKiehl]
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v' u'

namespace AlgebraicGeometry

namespace SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Points of `V₁` and `V₂` with the same image in `U` under morphisms of the small étale site
come from one point of the fibre product `V₁ ×_U V₂`. -/
lemma exists_pullback_point_smallEtale {U V₁ V₂ : SmallEtale B S hS}
    (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U) (a : (SmallEtale.toScheme B S hS).obj V₁)
    (b : (SmallEtale.toScheme B S hS).obj V₂)
    (hab : ((SmallEtale.toScheme B S hS).map f₁).base a =
      ((SmallEtale.toScheme B S hS).map f₂).base b) :
    ∃ z : (SmallEtale.toScheme B S hS).obj (pullback f₁ f₂),
      ((SmallEtale.toScheme B S hS).map (pullback.fst f₁ f₂)).base z = a ∧
        ((SmallEtale.toScheme B S hS).map (pullback.snd f₁ f₂)).base z = b := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
  refine ⟨(PreservesPullback.iso (SmallEtale.toScheme B S hS) f₁ f₂).inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_fst]
    exact hz₁
  · rw [← Scheme.Hom.comp_apply, PreservesPullback.iso_inv_snd]
    exact hz₂

/-- Transport of `locallyConstantPresheaf_isSheafFor` to the small étale site. -/
theorem locallyConstantPresheaf_isSheafFor_smallEtale (F : Type w) {U : SmallEtale B S hS}
    (R : Presieve U)
    (hR : ∀ x : (SmallEtale.toScheme B S hS).obj U, ∃ (V : SmallEtale B S hS)
      (f : V ⟶ U), R f ∧ x ∈ Set.range ((SmallEtale.toScheme B S hS).map f).base) :
    Presieve.IsSheafFor
      ((SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsType.{w, u} F) R :=
  isSheafFor_locallyConstantMapsType_comp (SmallEtale.toScheme B S hS) F R hR
    (fun _ f _ => ((SmallEtale.toScheme B S hS).map f).isOpenMap)
    (fun _ _ f₁ f₂ _ _ a b hab =>
      ⟨pullback f₁ f₂, pullback.fst f₁ f₂, pullback.snd f₁ f₂, pullback.condition,
        exists_pullback_point_smallEtale f₁ f₂ a b hab⟩)

/-- Transport of `locallyConstantPresheaf_isSheafFor` to the small étale site, for the topology. -/
@[weil "lem_fk102_constant_sheaf_is_sheaf"]
theorem locallyConstantPresheaf_isSheaf_smallEtale (F : Type w) :
    Presieve.IsSheaf (SmallEtale.topology B S hS)
      ((SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsType.{w, u} F) :=
  fun _ R hR => locallyConstantPresheaf_isSheafFor_smallEtale F R.arrows fun x =>
    SmallEtale.exists_mem_arrows_mem_range B S hS hR x

/-- Transport of `locallyConstantPresheafAb_isSheafFor` to the small étale site. -/
theorem locallyConstantPresheafAb_isSheafFor_smallEtale (F : Type w) [AddCommGroup F]
    {U : SmallEtale B S hS} (R : Presieve U)
    (hR : ∀ x : (SmallEtale.toScheme B S hS).obj U, ∃ (V : SmallEtale B S hS)
      (f : V ⟶ U), R f ∧ x ∈ Set.range ((SmallEtale.toScheme B S hS).map f).base) :
    Presieve.IsSheafFor
      ((SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsAb.{u, w} F ⋙ forget AddCommGrpCat)
      R :=
  Presieve.isSheafFor_iso
    (Functor.isoWhiskerLeft (SmallEtale.toScheme B S hS).op
      (locallyConstantMapsAbForgetIso.{w, u} F)).symm
    (locallyConstantPresheaf_isSheafFor_smallEtale F R hR)

/-- Transport of `locallyConstantPresheafAb_isSheafFor` to the small étale site, as a sheaf of
abelian groups for the topology. -/
@[weil "lem_fk102_constant_sheaf_is_sheaf"]
theorem locallyConstantPresheafAb_isSheaf_smallEtale (F : Type w) [AddCommGroup F] :
    Presheaf.IsSheaf (SmallEtale.topology B S hS)
      ((SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsAb.{u, w} F) := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{max u w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  exact fun _ R hR => locallyConstantPresheafAb_isSheafFor_smallEtale F R.arrows fun x =>
    SmallEtale.exists_mem_arrows_mem_range B S hS hR x

variable (B S hS) in
/-- The small étale form of `locallyConstantPresheaf`: the sheaf of sets of locally constant
`F`-valued maps on the small étale site. -/
@[weil "def_fk102_constant_sheaf"]
def locallyConstantSheafSmallEtale (F : Type w) :
    Sheaf (SmallEtale.topology B S hS) (Type (max u w)) :=
  ⟨(SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsType.{w, u} F,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (locallyConstantPresheaf_isSheaf_smallEtale F)⟩

variable (B S hS) in
/-- The small étale form of `locallyConstantPresheafAb`: the sheaf of abelian groups of locally
constant `F`-valued maps on the small étale site. -/
@[weil "def_fk102_constant_sheaf"]
def locallyConstantSheafAbSmallEtale (F : Type w) [AddCommGroup F] :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max u w} :=
  ⟨(SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsAb.{u, w} F,
    locallyConstantPresheafAb_isSheaf_smallEtale F⟩

@[simp]
lemma locallyConstantSheafSmallEtale_obj (F : Type w) :
    (locallyConstantSheafSmallEtale B S hS F).obj =
      (SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsType.{w, u} F :=
  rfl

@[simp]
lemma locallyConstantSheafAbSmallEtale_obj (F : Type w) [AddCommGroup F] :
    (locallyConstantSheafAbSmallEtale B S hS F).obj =
      (SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsAb.{u, w} F :=
  rfl

/-- Transport of `locallyConstantPresheafEquivFin` to the small étale site: on a noetherian
separated object `V`, the sections are the maps from the connected components of `V` to `F`. -/
noncomputable def locallyConstantPresheafEquivFin_smallEtale (F : Type w) (V : SmallEtale B S hS)
    (hV : SmallEtale.IsNoetherianSeparated B S hS V) :
    (locallyConstantSheafSmallEtale B S hS F).obj.obj (op V) ≃
      (Fin (Nat.card (_root_.ConnectedComponents ((SmallEtale.toScheme B S hS).obj V))) → F) :=
  locallyConstantPresheafEquivFin F ⟨V, hV⟩

/-- Transport of `locallyConstantPresheafAbEquivFin` to the small étale site. -/
noncomputable def locallyConstantPresheafAbEquivFin_smallEtale (F : Type w) [AddCommGroup F]
    (V : SmallEtale B S hS) (hV : SmallEtale.IsNoetherianSeparated B S hS V) :
    LocallyConstant ((SmallEtale.toScheme B S hS).obj V) F ≃+
      (Fin (Nat.card (_root_.ConnectedComponents ((SmallEtale.toScheme B S hS).obj V))) → F) :=
  locallyConstantPresheafAbEquivFin F ⟨V, hV⟩

/-- The presheaf `F_S` on `Et(S)` is the restriction of its small étale form along the
inclusion. -/
lemma inclusion_op_comp_locallyConstantSheafSmallEtale_obj (F : Type w) :
    (inclusion B S hS).op ⋙ (locallyConstantSheafSmallEtale B S hS F).obj =
      locallyConstantPresheaf B S hS F :=
  rfl

/-- The abelian presheaf `F_S` on `Et(S)` is the restriction of its small étale form along the
inclusion. -/
lemma inclusion_op_comp_locallyConstantSheafAbSmallEtale_obj (F : Type w) [AddCommGroup F] :
    (inclusion B S hS).op ⋙ (locallyConstantSheafAbSmallEtale B S hS F).obj =
      locallyConstantPresheafAb B S hS F :=
  rfl

section LocallyNoetherian

variable [IsLocallyNoetherian S]

/-- `locallyConstantPresheaf_isSheafFor` for the covering sieves of the topology of `Et(S)`. -/
theorem locallyConstantPresheaf_isSheaf (F : Type w) :
    Presieve.IsSheaf (topology B S hS) (locallyConstantPresheaf B S hS F) :=
  fun _ R hR =>
    locallyConstantPresheaf_isSheafFor F R.arrows ((mem_topology_iff B S hS R).mp hR)

/-- `locallyConstantPresheafAb_isSheafFor` for the topology of `Et(S)`, as a sheaf of abelian
groups. -/
theorem locallyConstantPresheafAb_isSheaf (F : Type w) [AddCommGroup F] :
    Presheaf.IsSheaf (topology B S hS) (locallyConstantPresheafAb B S hS F) := by
  refine Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{max u w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  exact fun _ R hR =>
    locallyConstantPresheafAb_isSheafFor F R.arrows ((mem_topology_iff B S hS R).mp hR)

variable (B S hS) in
/-- `locallyConstantPresheaf` as a sheaf of sets on `Et(S)`. -/
def locallyConstantEtSheaf (F : Type w) : Sheaf (topology B S hS) (Type (max u w)) :=
  ⟨locallyConstantPresheaf B S hS F,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (locallyConstantPresheaf_isSheaf F)⟩

variable (B S hS) in
/-- `locallyConstantPresheafAb` as a sheaf of abelian groups on `Et(S)`. -/
def locallyConstantEtSheafAb (F : Type w) [AddCommGroup F] :
    Sheaf (topology B S hS) AddCommGrpCat.{max u w} :=
  ⟨locallyConstantPresheafAb B S hS F, locallyConstantPresheafAb_isSheaf F⟩

variable (B S hS) in
/-- Transport of `locallyConstantPresheaf`: restricting the small étale constant sheaf along
`Et(S) ⊆ SmallEtale` gives `F_S`. -/
def sheafEquivInverseObjLocallyConstantSheafSmallEtaleIso (F : Type w) :
    (sheafEquiv B S hS (Type (max u w))).inverse.obj (locallyConstantSheafSmallEtale B S hS F) ≅
      locallyConstantEtSheaf B S hS F :=
  Iso.refl _

variable (B S hS) in
/-- The sheaf `F_S` on `Et(S)` corresponds, under `sheafEquiv`, to the small étale constant
sheaf of locally constant maps. -/
def sheafEquivFunctorObjLocallyConstantEtSheafIso (F : Type w) :
    (sheafEquiv B S hS (Type (max u w))).functor.obj (locallyConstantEtSheaf B S hS F) ≅
      locallyConstantSheafSmallEtale B S hS F :=
  (sheafEquiv B S hS _).functor.mapIso
      (sheafEquivInverseObjLocallyConstantSheafSmallEtaleIso B S hS F).symm ≪≫
    (sheafEquiv B S hS _).counitIso.app _

variable (B S hS) in
/-- Transport of `locallyConstantPresheafAb`: restricting the small étale abelian constant sheaf
along `Et(S) ⊆ SmallEtale` gives the abelian `F_S`. -/
def sheafEquivInverseObjLocallyConstantSheafAbSmallEtaleIso (F : Type w) [AddCommGroup F] :
    (sheafEquiv B S hS AddCommGrpCat.{max u w}).inverse.obj
        (locallyConstantSheafAbSmallEtale B S hS F) ≅
      locallyConstantEtSheafAb B S hS F :=
  Iso.refl _

variable (B S hS) in
/-- The abelian sheaf `F_S` on `Et(S)` corresponds, under `sheafEquiv`, to the small étale
abelian constant sheaf of locally constant maps. -/
def sheafEquivFunctorObjLocallyConstantEtSheafAbIso (F : Type w) [AddCommGroup F] :
    (sheafEquiv B S hS AddCommGrpCat.{max u w}).functor.obj (locallyConstantEtSheafAb B S hS F) ≅
      locallyConstantSheafAbSmallEtale B S hS F :=
  (sheafEquiv B S hS _).functor.mapIso
      (sheafEquivInverseObjLocallyConstantSheafAbSmallEtaleIso B S hS F).symm ≪≫
    (sheafEquiv B S hS _).counitIso.app _

end LocallyNoetherian

/-- The scheme underlying an object of `Et(S)`, read as the base of its own small étale site, is
locally noetherian. -/
instance isLocallyNoetherian_inclusion_obj_left (U : SmallNoetherianSeparatedEtale B S hS) :
    IsLocallyNoetherian ((inclusion B S hS).obj U).obj.left.obj :=
  inferInstanceAs (IsLocallyNoetherian ((toScheme B S hS).obj U))

end SmallNoetherianSeparatedEtale

namespace EtalePresheaf

open SmallNoetherianSeparatedEtale

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {C : Type v'}
  [Category.{u'} C]

/-- Transport of `restrictSlice`: restricting to the slice `Et(S)/U` the restriction of a
presheaf `L` on the small étale site is restricting `L` to the slice over `U`. -/
lemma restrictSlice_inclusion_op_comp (L : (SmallEtale B S hS)ᵒᵖ ⥤ C)
    (U : SmallNoetherianSeparatedEtale B S hS) :
    restrictSlice ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ L) U =
      (Over.post (SmallNoetherianSeparatedEtale.inclusion B S hS)).op ⋙
        (Over.forget ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U)).op ⋙ L :=
  rfl

/-- Transport of `restrict`: the restriction to `Et(U)` of the restriction to `Et(S)` of a
presheaf `L` on the small étale site of `S` is the restriction to `Et(U)` of the restriction of
`L` to the small étale site of `U` along `smallEtalePostcompose`. -/
lemma restrict_inclusion_op_comp (L : (SmallEtale B S hS)ᵒᵖ ⥤ C)
    (U : SmallNoetherianSeparatedEtale B S hS) :
    restrict ((SmallNoetherianSeparatedEtale.inclusion B S hS).op ⋙ L) U =
      (SmallNoetherianSeparatedEtale.inclusion B _ _).op ⋙
        (smallEtalePostcompose B S hS
          ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U)).op ⋙ L :=
  rfl

/-- Transport of `restrict` to sheaves: for a sheaf `L` on the small étale site of a locally
noetherian `S`, restricting its `Et(S)`-form to `Et(U)` gives the `Et(U)`-form of the restriction
of `L` to the small étale site of `U`. -/
lemma restrict_sheafEquiv_inverse_obj_obj [IsLocallyNoetherian S] (A : Type v') [Category.{u'} A]
    [HasLimitsOfSize.{u, u} A] (L : Sheaf (SmallEtale.topology B S hS) A)
    (U : SmallNoetherianSeparatedEtale B S hS) :
    restrict ((sheafEquiv B S hS A).inverse.obj L).obj U =
      ((sheafEquiv B _ _ A).inverse.obj
        ((Functor.sheafPushforwardContinuous
          (smallEtalePostcompose B S hS ((SmallNoetherianSeparatedEtale.inclusion B S hS).obj U)) A
          (SmallEtale.topology _ _ _) (SmallEtale.topology B S hS)).obj L)).obj :=
  rfl

end EtalePresheaf

end AlgebraicGeometry

end
