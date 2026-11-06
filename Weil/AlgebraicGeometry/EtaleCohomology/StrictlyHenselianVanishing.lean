module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import Weil.Attr

/-!
# Étale cohomology of a strictly Henselian local ring

Let `R` be a strictly Henselian local ring and `S = Spec R`. On the small étale site of `S`
every covering sieve of the final object `S` contains the identity: a covering family has a
member through which a geometric point over the closed point lifts, and that lift extends to a
section of the member because the final object, with its lift of the geometric point, is an
initial étale neighbourhood. Hence global sections of abelian étale sheaves turn epimorphisms
into surjections, the constant sheaf `ℤ` is a projective object, and every abelian étale sheaf
`F` on `S` has `H^i(S, F) = 0` for `i > 0`.

## Main results

* `Stacks.StrictlyHenselian.id_mem_of_mem_topology_final`: covering sieves of the final object
  of the small étale site of a strictly Henselian local scheme contain the identity.
* `Stacks.StrictlyHenselian.surjective_app_final_of_epi`: an epimorphism of abelian étale
  sheaves is surjective on global sections.
* `Stacks.StrictlyHenselian.projective_constantSheaf_ulift_int`: the constant sheaf `ℤ` is
  projective among abelian étale sheaves.
* `Stacks.StrictlyHenselian.subsingleton_sheafH_of_pos`: the positive-degree étale cohomology
  of an abelian sheaf on a strictly Henselian local scheme vanishes.

## Implementation notes

Cohomology is `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ℤ`, on the
small étale site `AlgebraicGeometry.SmallEtale.topology`, with coefficients in abelian groups of
the universe of the site. The source states the theorem for noetherian rings and computes the
cohomology by an injective resolution, splicing the short exact sequences of global sections;
here no noetherian hypothesis is needed, and the vanishing is read off the projectivity of the
constant sheaf `ℤ`, which is the same exactness of global sections. The Stacks Project version
`Stacks.StrictlyHenselian.subsingleton_etaleCohomology` has coefficients in the next universe.

## References

* [E. Freitag, R. Kiehl, *Étale Cohomology and the Weil Conjecture*][FK], I.1.19
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v u

namespace Stacks.StrictlyHenselian

/-- The integers, lifted to any universe, form a projective abelian group. -/
theorem projective_addCommGrpCat_ulift_int :
    Projective (AddCommGrpCat.of (ULift.{v, 0} ℤ)) := by
  constructor
  intro E X f e he
  have hsurj : Function.Surjective e.hom :=
    (AddCommGrpCat.epi_iff_surjective e).mp he
  obtain ⟨y, hy⟩ := hsurj (f.hom (ULift.up 1))
  refine ⟨AddCommGrpCat.ofHom (uliftZMultiplesHom E y), ?_⟩
  apply AddCommGrpCat.hom_ext
  ext z
  change e.hom ((uliftZMultiplesHom E y) z) = f.hom z
  rw [uliftZMultiplesHom_apply_apply]
  have hz : z = z.down • (ULift.up (1 : ℤ)) := by
    apply ULift.ext
    simp
  calc
    e.hom (z.down • y) = z.down • e.hom y := map_zsmul _ _ _
    _ = z.down • f.hom (ULift.up 1) := by rw [hy]
    _ = f.hom (z.down • ULift.up 1) := (map_zsmul _ _ _).symm
    _ = f.hom z := (congrArg f.hom hz).symm

/-- The geometric point of the spectrum of a local ring given by an algebraic closure of the
residue field. -/
def residueAlgebraicClosurePoint (R : Type u) [CommRing R] [IsLocalRing R] :
    GeometricPoint (Spec (.of R)) :=
  ⟨AlgebraicClosure (IsLocalRing.ResidueField R),
    Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField R)
          (AlgebraicClosure (IsLocalRing.ResidueField R))).comp
        (IsLocalRing.residue R)))⟩

/-- The geometric point `residueAlgebraicClosurePoint R` lies over the closed point. -/
theorem residueAlgebraicClosurePoint_liesOver (R : Type u) [CommRing R] [IsLocalRing R] :
    (residueAlgebraicClosurePoint R).LiesOver (IsLocalRing.closedPoint R) := by
  dsimp only [GeometricPoint.LiesOver, residueAlgebraicClosurePoint]
  let K := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure K
  let f : R →+* Ω := (algebraMap K Ω).comp (IsLocalRing.residue R)
  have hf : RingHom.ker f = IsLocalRing.maximalIdeal R := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap K Ω).injective]
    exact IsLocalRing.ker_residue
  change (Spec.map (CommRingCat.ofHom f)) _ = IsLocalRing.closedPoint R
  apply PrimeSpectrum.ext
  rw [Spec.map_apply]
  change Ideal.comap f _ = _
  have hbot : (default : Spec (.of Ω)).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime Ω _ _ (default : Spec (.of Ω)).isPrime
  rw [hbot]
  exact hf

variable (B : BigEtaleSite.{u}) (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
  (hS : B.Contains (Spec (.of R)))

/-- Over a strictly Henselian local ring, every covering sieve of the final object of the small
étale site contains the identity. -/
theorem id_mem_of_mem_topology_final {P : Sieve (SmallEtale.final B (Spec (.of R)) hS)}
    (hP : P ∈ SmallEtale.topology B (Spec (.of R)) hS (SmallEtale.final B (Spec (.of R)) hS)) :
    P (𝟙 _) := by
  let s := residueAlgebraicClosurePoint R
  have hs := residueAlgebraicClosurePoint_liesOver R
  let I := finalNeighborhood B R hS s
  obtain ⟨hI⟩ := nonempty_isInitial_finalNeighborhood B R hS s hs
  obtain ⟨Y, f, hf, y, hy⟩ :=
    (geometricPointSitePoint B (Spec (.of R)) hS s).jointly_surjective P hP I.2
  let g : I ⟶ ⟨Y, y⟩ := hI.to _
  have hgf : g.1 ≫ f = 𝟙 (SmallEtale.final B (Spec (.of R)) hS) :=
    (SmallEtale.finalIsTerminal B (Spec (.of R)) hS).hom_ext _ _
  exact hgf ▸ P.downward_closed hf g.1

/-- Over a strictly Henselian local ring, an epimorphism of abelian sheaves on the small étale
site is surjective on sections over the final object. -/
theorem surjective_app_final_of_epi
    {F G : Sheaf (SmallEtale.topology B (Spec (.of R)) hS) AddCommGrpCat.{u}} (φ : F ⟶ G)
    [Epi φ] :
    Function.Surjective (φ.hom.app (op (SmallEtale.final B (Spec (.of R)) hS))) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := φ)).mpr inferInstance
  intro x
  have hmem := Presheaf.imageSieve_mem (SmallEtale.topology B (Spec (.of R)) hS) φ.hom x
  obtain ⟨t, ht⟩ := id_mem_of_mem_topology_final B R hS hmem
  exact ⟨t, by simpa using ht⟩

/-- Over a strictly Henselian local ring, the constant sheaf `ℤ` is a projective abelian sheaf
on the small étale site. -/
theorem projective_constantSheaf_ulift_int :
    Projective ((constantSheaf (SmallEtale.topology B (Spec (.of R)) hS) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift ℤ))) := by
  let J := SmallEtale.topology B (Spec (.of R)) hS
  let hterm := SmallEtale.finalIsTerminal B (Spec (.of R)) hS
  have : ((sheafSections J AddCommGrpCat.{u}).obj
      (op (SmallEtale.final B (Spec (.of R)) hS))).PreservesEpimorphisms := by
    constructor
    intro F G φ _
    rw [AddCommGrpCat.epi_iff_surjective]
    exact surjective_app_final_of_epi B R hS φ
  exact (constantSheafAdj J AddCommGrpCat.{u} hterm).map_projective _
    projective_addCommGrpCat_ulift_int.{u}

/-- **Étale cohomology of a strictly Henselian local ring vanishes in positive degrees.** Let
`R` be a strictly Henselian local ring and `F` an abelian sheaf on the small étale site of
`Spec R`. Then `H^i(Spec R, F) = 0` for every `i > 0`. -/
@[weil "thm_fk101_strictly_henselian_cohomology_vanishes"]
theorem subsingleton_sheafH_of_pos
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Spec (.of R)) hS) AddCommGrpCat.{u})]
    (F : Sheaf (SmallEtale.topology B (Spec (.of R)) hS) AddCommGrpCat.{u}) (i : ℕ) (hi : 0 < i) :
    Subsingleton (Sheaf.H.{w} F i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  have := projective_constantSheaf_ulift_int B R hS
  exact Abelian.Ext.subsingleton_of_projective _ _ n

end Stacks.StrictlyHenselian
