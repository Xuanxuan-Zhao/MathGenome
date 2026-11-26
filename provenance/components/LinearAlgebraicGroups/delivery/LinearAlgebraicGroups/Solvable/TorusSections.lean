import Specs.LinearAlgebraicGroups.Solvable.TorusSections
import LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
import LinearAlgebraicGroups.Solvable.AffineAdditiveTorsors
import LinearAlgebraicGroups.Solvable.RegularTorusCohomology
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace LinearAlgebraicGroups.TorusSections

noncomputable section

open _root_.LinearAlgebraicGroups.Specs
open Specs.EquivariantUnipotentSeries
open LinearAlgebraicGroups.RegularTorusCohomology
  (constantCoefficient translation translationInvariant)
open private StandardGroups.exponentEvaluation StandardGroups.exponentsEquiv
  from LinearAlgebraicGroups.Affine.StandardGroups

variable {k : Type u} [Field k] {T : Specs.GroupScheme k}

private abbrev torusPoints (T : Specs.GroupScheme k) :=
  (groupPointsFunctor k).obj T

private abbrev changePoints {H : Specs.GroupScheme k} {R S : TestAlgebra k} (a : R ⟶ S) :=
  ((torusPoints H).map a).hom

private lemma changePoints_comp {H : Specs.GroupScheme k} {R S A : TestAlgebra k}
    (a : R ⟶ S) (b : S ⟶ A) (t : GroupPoints H R) :
    changePoints (H := H) (a ≫ b) t = changePoints b (changePoints a t) := by
  exact congrArg (fun f => f t) ((torusPoints H).map_comp a b)

private lemma pointComp {G H L : Specs.GroupScheme k} (f : G ⟶ H) (g : H ⟶ L)
    (R : TestAlgebra k) (x : GroupPoints G R) :
    onPoints (f ≫ g) R x = onPoints g R (onPoints f R x) := rfl

private lemma pointNatural {G H : Specs.GroupScheme k} (f : G ⟶ H)
    {R S : TestAlgebra k} (a : R ⟶ S) (x : GroupPoints G R) :
    changePoints a (onPoints f R x) = onPoints f S (changePoints a x) :=
  (congrArg (fun g => g x) (((groupPointsFunctor k).map f).naturality a)).symm

private abbrev Exponents (I : Type u) := Multiplicative (I → ℤ)

section Averaging

variable {I : Type u} [Fintype I] [DecidableEq I]
  (e : torusPoints T ≅ Specs.StandardGroups.multiplicativePowerPoints k I)

private abbrev laurentTest (I : Type u) (R : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (MonoidAlgebra R (Exponents I))

private def laurentInclusion (I : Type u) (R : TestAlgebra k) : R ⟶ laurentTest I R :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (MonoidAlgebra R (Exponents I)))

private def universalPoint (R : TestAlgebra k) : GroupPoints T (laurentTest I R) :=
  e.inv.app _ (fun i => (MonoidHom.toHomUnits (MonoidAlgebra.of R (Exponents I)))
    (Multiplicative.ofAdd (Pi.single i 1)))

private def laurentMap {R S : TestAlgebra k} (a : R ⟶ S) :
    laurentTest I R ⟶ laurentTest I S :=
  CommAlgCat.ofHom (MonoidAlgebra.mapAlgHom (Exponents I) a.hom)

private lemma laurentInclusion_natural {R S : TestAlgebra k} (a : R ⟶ S) :
    laurentInclusion I R ≫ laurentMap (I := I) a = a ≫ laurentInclusion I S := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro r
  exact DFunLike.congr_fun (MonoidAlgebra.mapRingHom_comp_algebraMap
    (M := Exponents I) a.hom.toRingHom) r

private lemma universalPoint_natural {R S : TestAlgebra k} (a : R ⟶ S) :
    changePoints (H := T) (laurentMap (I := I) a) (universalPoint e R) =
      universalPoint e S := by
  rw [universalPoint, universalPoint]
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom
    (e.inv.naturality (laurentMap (I := I) a)))
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at h
  rw [← h]
  congr 1
  funext i
  apply Units.ext
  change (laurentMap (I := I) a).hom (MonoidAlgebra.single
    (Multiplicative.ofAdd (Pi.single i 1)) 1) = MonoidAlgebra.single _ 1
  rw [laurentMap, CommAlgCat.hom_ofHom, MonoidAlgebra.mapAlgHom_single, map_one]

private def translatePoint (R : TestAlgebra k) (t : GroupPoints T R) :
    laurentTest I R ⟶ laurentTest I R :=
  CommAlgCat.ofHom ((translation (StandardGroups.exponentEvaluation
    (show I → Rˣ from e.hom.app R t))).restrictScalars k)

private lemma translatePoint_inclusion (R : TestAlgebra k) (t : GroupPoints T R) :
    laurentInclusion I R ≫ translatePoint e R t = laurentInclusion I R :=
  CommAlgCat.hom_ext (AlgHom.ext fun r => AlgHom.commutes (translation _) r)

private lemma translatePoint_universal (R : TestAlgebra k) (t : GroupPoints T R) :
    changePoints (H := T) (translatePoint e R t) (universalPoint e R) =
      changePoints (H := T) (laurentInclusion I R) t * universalPoint e R := by
  let a := translatePoint e R t
  let b := laurentInclusion I R
  apply ((e.app (laurentTest I R)).groupIsoToMulEquiv).injective
  change e.hom.app _ (((torusPoints T).map a) (universalPoint e R)) =
    e.hom.app _ ((((torusPoints T).map b) t) * universalPoint e R)
  rw [map_mul]
  have ha := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.hom.naturality a))
    (universalPoint e R)
  have hb := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.hom.naturality b)) t
  simp only [GrpCat.hom_comp, MonoidHom.comp_apply] at ha hb
  rw [ha, hb]
  have hu := ConcreteCategory.congr_hom (e.inv_hom_id_app (laurentTest I R))
    (fun i => (MonoidHom.toHomUnits (MonoidAlgebra.of R (Exponents I)))
      (Multiplicative.ofAdd (Pi.single i 1)))
  change e.hom.app _ (universalPoint e R) = _ at hu
  rw [hu]
  funext i
  apply Units.ext
  change translation (StandardGroups.exponentEvaluation
    (show I → Rˣ from e.hom.app R t)) (MonoidAlgebra.of R _ (Multiplicative.ofAdd (Pi.single i 1))) =
      algebraMap R (MonoidAlgebra R (Exponents I))
        ((show I → Rˣ from e.hom.app R t) i).val *
      MonoidAlgebra.of R _ (Multiplicative.ofAdd (Pi.single i 1))
  let v : I → Rˣ := e.hom.app R t
  let m : Exponents I := Multiplicative.ofAdd (Pi.single i 1)
  have h : StandardGroups.exponentEvaluation v m = v i :=
    congrFun ((StandardGroups.exponentsEquiv R).right_inv v) i
  change translation (StandardGroups.exponentEvaluation v) (MonoidAlgebra.of R _ m) =
    algebraMap R (MonoidAlgebra R (Exponents I)) (v i).val * MonoidAlgebra.of R _ m
  rw [show MonoidAlgebra.of R (Exponents I) m = MonoidAlgebra.single m 1 from rfl,
    translation, MonoidAlgebra.lift_single, one_smul]
  change algebraMap R (MonoidAlgebra R (Exponents I))
    (StandardGroups.exponentEvaluation v m).val * MonoidAlgebra.of R _ m = _
  rw [h]
  rfl

private lemma mean_translation (R : TestAlgebra k) (t : GroupPoints T R) (c : laurentTest I R) :
    constantCoefficient R (Exponents I) ((translatePoint e R t).hom c) =
      constantCoefficient R (Exponents I) c :=
  (translationInvariant R R (Exponents I)).2 _ c

private lemma mean_scalar (R : TestAlgebra k) (r : R) (c : laurentTest I R) :
    constantCoefficient R (Exponents I) ((laurentInclusion I R).hom r * c) =
      r * constantCoefficient R (Exponents I) c := by
  change constantCoefficient R (Exponents I)
    (algebraMap R (MonoidAlgebra R (Exponents I)) r * c) = _
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

private lemma mean_constant (R : TestAlgebra k) (r : R) :
    constantCoefficient R (Exponents I) ((laurentInclusion I R).hom r) = r := by
  change (MonoidAlgebra.single (1 : Exponents I) r).coeff 1 = r
  simp

include e

/-- Averaging a regular two-cocycle in its last variable gives a regular primitive.
Naturality on all commutative test algebras expresses regularity. -/
private theorem averageTwo (χ : ∀ R : TestAlgebra k, GroupPoints T R → R)
    (hχ : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T R),
      a.hom (χ R t) = χ S (changePoints a t))
    (c : ∀ R : TestAlgebra k, GroupPoints T R → GroupPoints T R → R)
    (hc : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (t s : GroupPoints T R),
      a.hom (c R t s) = c S (changePoints a t) (changePoints a s))
    (h : ∀ (R : TestAlgebra k) (t s z : GroupPoints T R),
      χ R t * c R s z - c R (t * s) z + c R t (s * z) = c R t s) :
    ∃ b : ∀ R : TestAlgebra k, GroupPoints T R → R,
      (∀ {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T R),
        a.hom (b R t) = b S (changePoints a t)) ∧
      (∀ (R : TestAlgebra k) (t s : GroupPoints T R),
        χ R t * b R s - b R (t * s) + b R t = c R t s) := by
  let b (R : TestAlgebra k) (t : GroupPoints T R) :=
    constantCoefficient R (Exponents I)
      (c (laurentTest I R) (changePoints (laurentInclusion I R) t) (universalPoint e R))
  refine ⟨b, ?_, ?_⟩
  · intro R S a t
    unfold b
    simp only [LinearAlgebraicGroups.RegularTorusCohomology.constantCoefficient_apply]
    rw [← MonoidAlgebra.coeff_mapAlgHom (M := Exponents I) a.hom]
    change constantCoefficient _ _ ((laurentMap (I := I) a).hom _) = _
    rw [hc, universalPoint_natural]
    rw [← changePoints_comp, laurentInclusion_natural, changePoints_comp]
    rfl
  · intro R t s
    let t' := changePoints (H := T) (laurentInclusion I R) t
    let s' := changePoints (H := T) (laurentInclusion I R) s
    let z := universalPoint e R
    let mean := constantCoefficient R (Exponents I)
    have ht : mean (c _ t' (s' * z)) = b R t := by
      have hfix : changePoints (H := T) (translatePoint e R s) t' = t' := by
        dsimp only [t']
        rw [← changePoints_comp, translatePoint_inclusion]
      rw [← translatePoint_universal e R s, ← hfix, ← hc, mean_translation]
    have heq := congrArg mean (h (laurentTest I R) t' s' z)
    rw [map_add, map_sub, ht, ← hχ, mean_scalar, ← hc, mean_constant] at heq
    simpa only [b, mean, t', s', z, map_mul] using heq

/-- Averaging a regular crossed homomorphism gives a constant conjugator. -/
private theorem averageOne (χ : ∀ R : TestAlgebra k, GroupPoints T R → R)
    (hχ : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T R),
      a.hom (χ R t) = χ S (changePoints a t))
    (c : ∀ R : TestAlgebra k, GroupPoints T R → R)
    (hc : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T R),
      a.hom (c R t) = c S (changePoints a t))
    (h : ∀ (R : TestAlgebra k) (t s : GroupPoints T R), c R (t * s) = c R t + χ R t * c R s) :
    ∃ w : k, ∀ (R : TestAlgebra k) (t : GroupPoints T R),
      c R t = algebraMap k R w - χ R t * algebraMap k R w := by
  let K : TestAlgebra k := CommAlgCat.of k k
  let w := constantCoefficient K (Exponents I) (c _ (universalPoint e K))
  refine ⟨w, ?_⟩
  intro R t
  let t' := changePoints (H := T) (laurentInclusion I R) t
  let z := universalPoint e R
  let mean := constantCoefficient R (Exponents I)
  have hz : mean (c _ z) = algebraMap k R w := by
    let a : K ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have he := hc (laurentMap (I := I) a) (universalPoint e K)
    rw [universalPoint_natural] at he
    rw [← he]
    exact MonoidAlgebra.coeff_mapAlgHom (M := Exponents I) a.hom _ _
  have ht : mean (c _ (t' * z)) = mean (c _ z) := by
    rw [← translatePoint_universal e R t, ← hc, mean_translation]
  have heq := congrArg mean (h (laurentTest I R) t' z)
  rw [ht, map_add, ← hc, mean_constant, ← hχ, mean_scalar, hz] at heq
  exact eq_sub_of_add_eq heq.symm

end Averaging

section AdditiveQuotients

open Specs.HomogeneousQuotient (rightMultiplication)
open private EquivariantUnipotentSeries.quotient_kernel_pair
  EquivariantUnipotentSeries.sections_comp EquivariantUnipotentSeries.sections_inv
  EquivariantUnipotentSeries.sections_one
  from LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {E Y : Specs.AffineAlgebraicGroup k} {N : Specs.ClosedSubgroup E.val}

/-- A faithfully flat quotient by an additive kernel has a section of schemes over
its affine target. In particular, the same section lifts all points of that target. -/
private theorem additiveQuotientSection (q : E.val ⟶ Y.val)
    (hq : Specs.Fppf.IsFppf q.hom.hom.left) (hk : IsSchemeKernel q N)
    (e : torusPoints N.group ≅ Specs.StandardGroups.additivePoints k) :
    ∃ j : Y.val.X ⟶ E.val.X, j ≫ q.hom.hom = 𝟙 _ := by
  let P : Over Y.val.X := Over.mk q.hom.hom
  have hp := EquivariantUnipotentSeries.quotient_kernel_pair hk
  have hmul {X : SchemeOver k} (g : X ⟶ E.val.X) (a : X ⟶ N.group.X) :
      prod.lift g a ≫ rightMultiplication N = g * (a ≫ N.inclusion.hom.hom) := by
    simp [rightMultiplication, MonObj.comp_mul]
  let act : Specs.Fppf.SchemeRightAction P N.group :=
    { action := Over.homMk (rightMultiplication N) hp.w.symm
      one := by
        intro X x
        apply Over.OverMorphism.ext
        change prod.lift x.left (1 : _ ⟶ N.group.X) ≫ rightMultiplication N = x.left
        rw [hmul, EquivariantUnipotentSeries.sections_one, mul_one]
      mul := by
        intro X x a b
        apply Over.OverMorphism.ext
        let x' : X.left ⟶ E.val.X := x.left
        let a' : X.left ⟶ N.group.X := a.down
        let b' : X.left ⟶ N.group.X := b.down
        change prod.lift (prod.lift x' a' ≫ rightMultiplication N) b' ≫
            rightMultiplication N = prod.lift x' (a' * b') ≫ rightMultiplication N
        rw [hmul (prod.lift x' a' ≫ rightMultiplication N) b',
          hmul x' a', hmul x' (a' * b'), EquivariantUnipotentSeries.sections_comp, mul_assoc] }
  have hcomp : Specs.Fppf.comparison act = hp.isoPullback.hom := by
    apply pullback.hom_ext
    · change pullback.lift prod.fst (rightMultiplication N) _ ≫
        pullback.fst q.hom.hom q.hom.hom = hp.isoPullback.hom ≫ _
      rw [pullback.lift_fst]
      exact hp.isoPullback_hom_fst.symm
    · change pullback.lift prod.fst (rightMultiplication N) _ ≫
        pullback.snd q.hom.hom q.hom.hom = hp.isoPullback.hom ≫ _
      rw [pullback.lift_snd]
      exact hp.isoPullback_hom_snd.symm
  letI : IsIso (Specs.Fppf.comparison act) := hcomp ▸ inferInstanceAs (IsIso hp.isoPullback.hom)
  let B := Specs.Unipotent.closedSubgroupAlgebraicGroup N
  have ht : Specs.Fppf.IsTorsor (Specs.Fppf.representedAction act) :=
    (Fppf.representedTorsorCriterion B.property.2 act).2 ⟨hq, inferInstance⟩
  obtain ⟨x⟩ := AdditiveDescent.affineAdditiveTorsorSection e Y.val.X Y.property.1
    ⟨Specs.Fppf.representedAction act, ht⟩
  let j : Over.mk (𝟙 Y.val.X) ⟶ P := x.down
  exact ⟨j.left, Over.w j⟩

end AdditiveQuotients

section SectionLifting

open private Unipotent.onPoints_injective
  Unipotent.group_hom_ext Unipotent.scheme_hom_spec
  from LinearAlgebraicGroups.Unipotent.CentralSeries
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {E Y T₀ : Specs.AffineAlgebraicGroup k} {N : Specs.ClosedSubgroup E.val}
  {q : E.val ⟶ Y.val}
  (e : torusPoints N.group ≅ Specs.StandardGroups.additivePoints k)

private def additiveInclusion (R : TestAlgebra k) :
    Multiplicative R →* GroupPoints E.val R :=
  (onPoints N.inclusion R).comp (e.inv.app R).hom

private lemma additiveInclusion_injective (R : TestAlgebra k) :
    Function.Injective (additiveInclusion e R) :=
  (Unipotent.onPoints_injective N.inclusion N.isClosedImmersion R).comp
    (e.app R).symm.groupIsoToMulEquiv.injective

private lemma additiveInclusion_natural {R S : TestAlgebra k} (a : R ⟶ S) (r : R) :
    changePoints a (additiveInclusion e R (Multiplicative.ofAdd r)) =
      additiveInclusion e S (Multiplicative.ofAdd (a.hom r)) := by
  have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.inv.naturality a))
    (Multiplicative.ofAdd r)
  simp only [GrpCat.hom_comp] at h
  unfold additiveInclusion
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, pointNatural]
  congr 1
  exact h.symm

private lemma additiveInclusion_kernel (hk : IsSchemeKernel q N) (R : TestAlgebra k)
    (v : GroupPoints E.val R) :
    onPoints q R v = 1 ↔ ∃ r : R, additiveInclusion e R (Multiplicative.ofAdd r) = v := by
  change v ≫ q.hom.hom = 1 ↔ _
  rw [← schemeKernel_sections hk]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨r, hr⟩ := (e.app R).symm.groupIsoToMulEquiv.surjective x
    exact ⟨r.toAdd, congrArg (onPoints N.inclusion R) hr |>.trans hx⟩
  · rintro ⟨r, hr⟩
    exact ⟨e.inv.app R (Multiplicative.ofAdd r), hr⟩

private abbrev IsScalarConjugation (p : E.val ⟶ T₀.val)
    (χ : ∀ R : TestAlgebra k, GroupPoints T₀.val R → R) : Prop :=
  ∀ (R : TestAlgebra k) (g : GroupPoints E.val R) (r : R),
    g * additiveInclusion e R (Multiplicative.ofAdd r) * g⁻¹ =
      additiveInclusion e R (Multiplicative.ofAdd (χ R (onPoints p R g) * r))

private abbrev IsNaturalScalar
    (χ : ∀ R : TestAlgebra k, GroupPoints T₀.val R → R) : Prop :=
  ∀ {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T₀.val R),
    a.hom (χ R t) = χ S (changePoints a t)

private lemma additiveInclusion_add {R : TestAlgebra k} (a b : R) :
    additiveInclusion e R (Multiplicative.ofAdd (a + b)) =
      additiveInclusion e R (Multiplicative.ofAdd a) *
        additiveInclusion e R (Multiplicative.ofAdd b) :=
  map_mul (additiveInclusion e R) _ _

/-- A group section of the lower quotient lifts through an additive kernel with
scalar conjugation. The correction is the mean of the multiplication defect. -/
private theorem liftSection (p₀ : Y.val ⟶ T₀.val) (s : T₀.val ⟶ Y.val)
    (hs : s ≫ p₀ = 𝟙 _) (hk : IsSchemeKernel q N) (hq : Specs.Fppf.IsFppf q.hom.hom.left)
    (χ : ∀ R : TestAlgebra k, GroupPoints T₀.val R → R) (hχ : IsNaturalScalar χ)
    (hact : IsScalarConjugation e (q ≫ p₀) χ) (hT : IsSplitTorus T₀.val) :
    ∃ σ : T₀.val ⟶ E.val, σ ≫ q = s := by
  obtain ⟨r, ⟨iso⟩⟩ := hT
  let te : torusPoints T₀.val ≅
      Specs.StandardGroups.multiplicativePowerPoints k (Specs.Unipotent.Index r) :=
    (groupPointsFunctor k).mapIso iso ≪≫ StandardGroups.multiplicativePowerGroupPointsIso k (Specs.Unipotent.Index r)
  obtain ⟨j, hj⟩ := additiveQuotientSection q hq hk e
  let liftP (R : TestAlgebra k) (t : GroupPoints T₀.val R) : GroupPoints E.val R :=
    onPoints s R t ≫ j
  have hl (R) (t : GroupPoints T₀.val R) : onPoints q R (liftP R t) = onPoints s R t := by
    change (onPoints s R t ≫ j) ≫ q.hom.hom = _
    rw [Category.assoc, hj, Category.comp_id]
  have hlt (R) (t : GroupPoints T₀.val R) : onPoints (q ≫ p₀) R (liftP R t) = t := by
    rw [pointComp, hl, ← pointComp, hs]
    exact Category.comp_id t
  have hlN {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T₀.val R) :
      changePoints a (liftP R t) = liftP S (changePoints a t) :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) (pointNatural s a t))
  let I (R : TestAlgebra k) (w : R) := additiveInclusion e R (Multiplicative.ofAdd w)
  have hi (R : TestAlgebra k) : Function.Injective (I R) :=
    (additiveInclusion_injective e R).comp Multiplicative.ofAdd.injective
  have hdef (R : TestAlgebra k) (t u : GroupPoints T₀.val R) :
      ∃ w : R, I R w = liftP R t * liftP R u * (liftP R (t * u))⁻¹ := by
    apply (additiveInclusion_kernel e hk R _).mp
    simp only [map_mul, map_inv, hl, mul_inv_cancel]
  choose c hc using hdef
  have hcN {R S : TestAlgebra k} (a : R ⟶ S) (t u : GroupPoints T₀.val R) :
      a.hom (c R t u) = c S (changePoints a t) (changePoints a u) := by
    apply hi S
    change additiveInclusion e S (Multiplicative.ofAdd (a.hom (c R t u))) = _
    rw [← additiveInclusion_natural, show additiveInclusion e R _ = I R (c R t u) from rfl,
      hc, map_mul, map_mul, map_inv, hlN, hlN, hlN, map_mul, ← hc]
  have hcoc (R : TestAlgebra k) (t u v : GroupPoints T₀.val R) :
      χ R t * c R u v - c R (t * u) v + c R t (u * v) = c R t u := by
    have h : χ R t * c R u v + c R t (u * v) = c R t u + c R (t * u) v := by
      apply hi R
      change additiveInclusion e R _ = additiveInclusion e R _
      rw [additiveInclusion_add, additiveInclusion_add]
      change I R (χ R t * c R u v) * I R (c R t (u * v)) =
        I R (c R t u) * I R (c R (t * u) v)
      have ha := hact R (liftP R t) (c R u v)
      rw [hlt] at ha
      change liftP R t * I R (c R u v) * (liftP R t)⁻¹ = I R (χ R t * c R u v) at ha
      rw [← ha, hc, hc, hc, hc, mul_assoc t]
      group
    linear_combination h
  obtain ⟨b, hbN, hb⟩ := averageTwo te χ hχ c hcN hcoc
  let f (R : TestAlgebra k) (t : GroupPoints T₀.val R) := I R (-b R t) * liftP R t
  have hf (R : TestAlgebra k) (t u : GroupPoints T₀.val R) :
      f R (t * u) = f R t * f R u := by
    have h : -(b R t) + χ R t * -(b R u) + c R t u = -(b R (t * u)) := by
      linear_combination -(hb R t u)
    have hs : I R (-b R t) * I R (χ R t * -b R u) * I R (c R t u) =
        I R (-b R (t * u)) := by
      simpa only [I, additiveInclusion_add] using congrArg (I R) h
    unfold f
    have ha := hact R (liftP R t) (-b R u)
    rw [hlt] at ha
    change liftP R t * I R (-b R u) * (liftP R t)⁻¹ = I R (χ R t * -b R u) at ha
    rw [← hs, ← ha, hc]
    group
  let α : torusPoints T₀.val ⟶ torusPoints E.val :=
    { app := fun R => GrpCat.ofHom
        { toFun := f R
          map_one' := by
            have h := hf R 1 1
            rw [one_mul] at h
            apply mul_left_cancel (a := f R 1)
            simpa only [mul_one] using h.symm
          map_mul' := hf R }
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro t
        change f S (changePoints a t) = changePoints a (f R t)
        simp only [f, I, map_mul, additiveInclusion_natural, hlN, map_neg, hbN] }
  let σ := (AffineAlgebraicGroup.groupHomEquiv T₀ E).symm α
  refine ⟨σ, Unipotent.group_hom_ext T₀.property.1 ?_⟩
  intro R t
  rw [pointComp, Unipotent.scheme_hom_spec α]
  change onPoints q R (f R t) = _
  rw [show f R t = I R (-b R t) * liftP R t from rfl, map_mul, hl]
  rw [(additiveInclusion_kernel e hk R _).2 ⟨_, rfl⟩, one_mul]

private abbrev groundTest (k : Type u) [Field k] : TestAlgebra k := CommAlgCat.of k k

private def fromGround (R : TestAlgebra k) : groundTest k ⟶ R :=
  CommAlgCat.ofHom (Algebra.ofId k R)

private abbrev rationalAt {H : Specs.GroupScheme k} (a : GroupPoints H (groundTest k))
    (R : TestAlgebra k) : GroupPoints H R := changePoints (fromGround R) a

private lemma rationalAt_natural {H : Specs.GroupScheme k}
    (x : GroupPoints H (groundTest k)) {R S : TestAlgebra k} (a : R ⟶ S) :
    changePoints a (rationalAt x R) = rationalAt x S := by
  rw [← changePoints_comp]
  have h : fromGround R ≫ a = fromGround S := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro r
    exact a.hom.commutes r
  rw [h]

/-- Two group sections with the same image in the previous quotient differ by
conjugation by a rational point of the additive kernel. -/
private theorem conjugacyInAdditiveKernel (p₀ : Y.val ⟶ T₀.val)
    (s₁ s₂ : T₀.val ⟶ E.val) (hs₁ : s₁ ≫ q ≫ p₀ = 𝟙 _) (hs : s₁ ≫ q = s₂ ≫ q)
    (hk : IsSchemeKernel q N)
    (χ : ∀ R : TestAlgebra k, GroupPoints T₀.val R → R) (hχ : IsNaturalScalar χ)
    (hact : IsScalarConjugation e (q ≫ p₀) χ) (hT : IsSplitTorus T₀.val) :
    ∃ a : GroupPoints N.group (groundTest k),
      ∀ (R : TestAlgebra k) (t : GroupPoints T₀.val R),
        onPoints s₂ R t = onPoints N.inclusion R (rationalAt a R) *
          onPoints s₁ R t * (onPoints N.inclusion R (rationalAt a R))⁻¹ := by
  obtain ⟨r, ⟨iso⟩⟩ := hT
  let te : torusPoints T₀.val ≅
      Specs.StandardGroups.multiplicativePowerPoints k (Specs.Unipotent.Index r) :=
    (groupPointsFunctor k).mapIso iso ≪≫ StandardGroups.multiplicativePowerGroupPointsIso k (Specs.Unipotent.Index r)
  let I (R : TestAlgebra k) (w : R) := additiveInclusion e R (Multiplicative.ofAdd w)
  have hi (R : TestAlgebra k) : Function.Injective (I R) :=
    (additiveInclusion_injective e R).comp Multiplicative.ofAdd.injective
  have hdef (R : TestAlgebra k) (t : GroupPoints T₀.val R) :
      ∃ w : R, I R w = onPoints s₂ R t * (onPoints s₁ R t)⁻¹ := by
    apply (additiveInclusion_kernel e hk R _).mp
    simp only [map_mul, map_inv, ← pointComp, hs, mul_inv_cancel]
  choose c hc using hdef
  have hcN {R S : TestAlgebra k} (a : R ⟶ S) (t : GroupPoints T₀.val R) :
      a.hom (c R t) = c S (changePoints a t) := by
    apply hi S
    change additiveInclusion e S (Multiplicative.ofAdd (a.hom (c R t))) = _
    rw [← additiveInclusion_natural, show additiveInclusion e R _ = I R (c R t) from rfl,
      hc, map_mul, map_inv, pointNatural, pointNatural, ← hc]
  have hcoc (R : TestAlgebra k) (t u : GroupPoints T₀.val R) :
      c R (t * u) = c R t + χ R t * c R u := by
    have ht : onPoints (q ≫ p₀) R (onPoints s₁ R t) = t := by
      rw [← pointComp, hs₁]
      exact Category.comp_id t
    have ha := hact R (onPoints s₁ R t) (c R u)
    rw [ht] at ha
    change onPoints s₁ R t * I R (c R u) * (onPoints s₁ R t)⁻¹ = I R (χ R t * c R u) at ha
    apply hi R
    change I R (c R (t * u)) = additiveInclusion e R (Multiplicative.ofAdd _)
    rw [additiveInclusion_add]
    change I R (c R (t * u)) = I R (c R t) * I R (χ R t * c R u)
    rw [← ha, hc, hc, hc, map_mul, map_mul]
    group
  obtain ⟨w, hw⟩ := averageOne te χ hχ c hcN hcoc
  let a : GroupPoints N.group (groundTest k) := e.inv.app _ (Multiplicative.ofAdd w)
  refine ⟨a, ?_⟩
  intro R t
  have ha := additiveInclusion_natural e (fromGround R) w
  have ha' : onPoints N.inclusion R (rationalAt a R) = I R (algebraMap k R w) := by
    rw [← pointNatural]
    exact ha
  rw [ha']
  have ht : onPoints (q ≫ p₀) R (onPoints s₁ R t) = t := by
    rw [← pointComp, hs₁]
    exact Category.comp_id t
  have hA := hact R (onPoints s₁ R t) (algebraMap k R w)
  rw [ht] at hA
  have hd := hc R t
  rw [hw] at hd
  change additiveInclusion e R (Multiplicative.ofAdd
    (algebraMap k R w - χ R t * algebraMap k R w)) = _ at hd
  rw [show Multiplicative.ofAdd (algebraMap k R w - χ R t * algebraMap k R w) =
    Multiplicative.ofAdd (algebraMap k R w) *
      (Multiplicative.ofAdd (χ R t * algebraMap k R w))⁻¹ from congrArg Multiplicative.ofAdd (sub_eq_add_neg _ _), map_mul, map_inv,
    ← hA] at hd
  have h := congrArg (· * onPoints s₁ R t) hd.symm
  change (onPoints s₂ R t * (onPoints s₁ R t)⁻¹) * onPoints s₁ R t =
    (I R (algebraMap k R w) * (onPoints s₁ R t * I R (algebraMap k R w) *
      (onPoints s₁ R t)⁻¹)⁻¹) * onPoints s₁ R t at h
  calc
    _ = (onPoints s₂ R t * (onPoints s₁ R t)⁻¹) * onPoints s₁ R t := by group
    _ = _ := h
    _ = _ := by group

end SectionLifting

section QuotientTower

open private schemeKernel_exists schemeKernel_sections
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private EquivariantUnipotentSeries.liftGroupHomOfQuotient
  EquivariantUnipotentSeries.epiOver_of_flat_surjective
  from LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private Unipotent.represented_quotient_of_kernel Unipotent.closedSeries_inclusion_closed
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private Unipotent.factor_through_closed Unipotent.scheme_kernel_of_points
  Unipotent.scheme_kernel_of_iso Unipotent.kernel_points
  Unipotent.onPoints_injective
  from LinearAlgebraicGroups.Unipotent.CentralSeries

open Specs.Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup ClosedSeries)

private lemma fppf_of_faithfullyFlat {G E Y : Specs.AffineAlgebraicGroup k}
    (q : G.val ⟶ E.val) (p : E.val ⟶ Y.val)
    (hf : Flat q.hom.hom.left) (hs : Surjective q.hom.hom.left)
    (hfp : Flat (q ≫ p).hom.hom.left) (hsp : Surjective (q ≫ p).hom.hom.left) :
    Specs.Fppf.IsFppf p.hom.hom.left := by
  obtain ⟨V, v, i, hvi, _, _⟩ := schemeImageFactorization E Y p
  letI := hf
  letI := hs
  letI := hvi.2.1
  letI := hvi.2.2.1
  letI := hvi.2.2.2.1
  have heq : (q ≫ v) ≫ i = q ≫ p := by rw [Category.assoc, hvi.1]
  obtain ⟨e, ⟨_, he⟩, _⟩ := schemeImageUniqueness G Y (q ≫ p) (I := V.val) (J := Y.val) (q ≫ v) i (q ≫ p) (𝟙 _)
    heq (Category.comp_id _) (by change Flat (_ ≫ _); infer_instance)
    (by change Surjective (_ ≫ _); infer_instance) hvi.2.2.2.2.2 hfp hsp
    (inferInstanceAs (IsClosedImmersion (𝟙 Y.val.X.left)))
  have hi : i = e.hom := he.symm.trans (Category.comp_id _)
  letI : IsIso i := hi ▸ inferInstanceAs (IsIso e.hom)
  letI : IsIso i.hom.hom.left :=
    (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso i
  rw [← hvi.1]
  change Specs.Fppf.IsFppf (v.hom.hom.left ≫ i.hom.hom.left)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private lemma killKernel {G Y : Specs.GroupScheme k} {N : Specs.ClosedSubgroup G}
    {p : G ⟶ Y} (h : IsSchemeKernel p N) : N.inclusion.hom.hom ≫ p.hom.hom = 1 :=
  h.w

private lemma cancelQuotient {G Y V : Specs.GroupScheme k}
    (p : G ⟶ Y) (hf : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left)
    {a b : Y ⟶ V} (h : p ≫ a = p ≫ b) : a = b := by
  letI := hf
  letI := hs
  letI : Epi p.hom.hom := EquivariantUnipotentSeries.epiOver_of_flat_surjective _
  exact Grp.hom_ext _ _ ((cancel_epi p.hom.hom).mp
    (congrArg (fun x : G ⟶ V => x.hom.hom) h))

private lemma quotientIso {G E Y : Specs.AffineAlgebraicGroup k}
    {N : Specs.ClosedSubgroup G.val} {p : G.val ⟶ E.val} {q : G.val ⟶ Y.val}
    (hp : IsFppfGroupQuotient N p) (hq : IsFppfGroupQuotient N q) :
    ∃ e : E.val ≅ Y.val, p ≫ e.hom = q := by
  obtain ⟨a, ha⟩ := EquivariantUnipotentSeries.liftGroupHomOfQuotient p hp q (killKernel hq.1)
  obtain ⟨b, hb⟩ := EquivariantUnipotentSeries.liftGroupHomOfQuotient q hq p (killKernel hp.1)
  exact ⟨⟨a, b,
    cancelQuotient p hp.2.1 hp.2.2.1 (by rw [← Category.assoc, ha, hb, Category.comp_id]),
    cancelQuotient q hq.2.1 hq.2.2.1 (by rw [← Category.assoc, hb, ha, Category.comp_id])⟩, ha⟩

/-- The kernel of a transition in a tower of quotients is the corresponding
quotient of the two kernels. Its quotient projection is a base change. -/
private theorem transitionKernel {G E Y A B Q : Specs.AffineAlgebraicGroup k}
    (j : A.val ⟶ G.val) (hj : IsClosedImmersion j.hom.hom.left)
    (b : B.val ⟶ A.val) (hb : IsClosedImmersion b.hom.hom.left)
    (hbj : IsClosedImmersion (b ≫ j).hom.hom.left)
    (p : G.val ⟶ Y.val) (q : G.val ⟶ E.val) (π : E.val ⟶ Y.val) (hπ : q ≫ π = p)
    (hp : IsSchemeKernel p ⟨_, j, hj⟩)
    (hq : IsFppfGroupQuotient ⟨_, b ≫ j, hbj⟩ q)
    (f : A.val ⟶ Q.val) (hf : IsFppfGroupQuotient ⟨_, b, hb⟩ f) :
    ∃ (K : Specs.ClosedSubgroup E.val) (v : A.val ⟶ K.group) (e : Q.val ≅ K.group),
      IsSchemeKernel π K ∧
      Flat v.hom.hom.left ∧ Surjective v.hom.hom.left ∧
      v ≫ K.inclusion = j ≫ q ∧ f ≫ e.hom = v := by
  letI := Y.property.1
  obtain ⟨K, hK⟩ := schemeKernel_exists π
  let A' := closedSubgroupAlgebraicGroup K
  obtain ⟨v, hv⟩ := Unipotent.factor_through_closed (A := A) (B := A') (C := E)
    (j ≫ q) K.inclusion K.isClosedImmersion (fun R x => by
      apply (Unipotent.kernel_points π K hK R _).mp
      rw [← pointComp, Category.assoc, hπ, pointComp]
      exact (Unipotent.kernel_points p ⟨_, j, hj⟩ hp R _).mpr ⟨x, rfl⟩)
  have hv' : v.hom.hom ≫ K.inclusion.hom.hom = j.hom.hom ≫ q.hom.hom :=
    congrArg (fun a : A.val ⟶ E.val => a.hom.hom) hv
  have hp' : IsPullback j.hom.hom (toUnit A.val.X) (q.hom.hom ≫ π.hom.hom) η[Y.val.X] := by
    change IsPullback _ _ (q ≫ π).hom.hom _
    rw [hπ]
    exact hp
  have hpb : IsPullback j.hom.hom v.hom.hom q.hom.hom K.inclusion.hom.hom := by
    rw [← comp_toUnit v.hom.hom] at hp'
    exact hp'.of_bot hv'.symm hK
  have hpb' := hpb.map (Over.forget (Spec (CommRingCat.of k)))
  have hvf : Flat v.hom.hom.left := MorphismProperty.of_isPullback hpb' hq.2.1
  have hvs : Surjective v.hom.hom.left := MorphismProperty.of_isPullback hpb' hq.2.2.1
  have hvp : LocallyOfFinitePresentation v.hom.hom.left :=
    MorphismProperty.of_isPullback hpb' hq.2.2.2.1
  have hvk : IsSchemeKernel v ⟨_, b, hb⟩ := by
    apply Unipotent.scheme_kernel_of_points
    intro R x
    have hx : onPoints K.inclusion R (onPoints v R x) =
        onPoints q R (onPoints j R x) := congrArg (fun a : A.val ⟶ E.val => onPoints a R x) hv
    constructor
    · intro h
      rw [h, map_one] at hx
      obtain ⟨y, hy⟩ := (Unipotent.kernel_points q ⟨_, b ≫ j, hbj⟩ hq.1 R _).mp hx.symm
      exact ⟨y, Unipotent.onPoints_injective j hj R hy⟩
    · rintro ⟨y, rfl⟩
      apply Unipotent.onPoints_injective K.inclusion K.isClosedImmersion R
      rw [hx, map_one]
      exact (Unipotent.kernel_points q ⟨_, b ≫ j, hbj⟩ hq.1 R _).mpr ⟨y, rfl⟩
  obtain ⟨e, he⟩ := quotientIso hf (Unipotent.represented_quotient_of_kernel v ⟨_, b, hb⟩ hvk hvf hvs hvp)
  exact ⟨K, v, e, hK, hvf, hvs, hv, he⟩

/-- A point of a faithfully flat morphism's target lifts after an affine
faithfully flat extension of its test algebra. -/
private theorem liftPointLocally {G Y : Specs.AffineAlgebraicGroup k}
    (p : G.val ⟶ Y.val) (hf : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left)
    (R : TestAlgebra k) (x : GroupPoints Y.val R) :
    ∃ (S : TestAlgebra k) (a : R ⟶ S),
      Epi ((testSpec k).map a.op) ∧
        ∃ y : GroupPoints G.val S, onPoints p S y = changePoints a x := by
  let f := p.hom.hom
  let X := (testSpec k).obj (op R)
  let x' : X ⟶ Y.val.X := x
  let P := pullback f x'
  let pr := pullback.snd f x'
  have hpb : IsPullback (pullback.fst f x').left pr.left f.left x'.left :=
    (IsPullback.of_hasPullback f x').map (Over.forget (Spec (CommRingCat.of k)))
  have ha : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  haveI : IsAffine (pullback f.left x'.left) :=
    @AlgebraicGeometry.Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _ _
      f.left x'.left G.property.1 ha Y.property.1
  have haff : IsAffine P.left := IsAffine.of_isIso hpb.isoPullback.hom
  obtain ⟨S, ⟨i⟩⟩ := essImage_algSpec.mpr haff
  let a : R ⟶ S.unop := (AlgebraicGeometry.algSpec.fullyFaithful.preimage (i.hom ≫ pr)).unop
  have ha : (testSpec k).map a.op = i.hom ≫ pr :=
    AlgebraicGeometry.algSpec.fullyFaithful.map_preimage _
  letI : Flat pr.left := MorphismProperty.of_isPullback hpb hf
  letI : Surjective pr.left := MorphismProperty.of_isPullback hpb hs
  refine ⟨S.unop, a, ha ▸ ?_, i.hom ≫ pullback.fst f x', ?_⟩
  · letI : Epi pr := EquivariantUnipotentSeries.epiOver_of_flat_surjective _
    infer_instance
  · change (i.hom ≫ pullback.fst f x') ≫ f = (testSpec k).map a.op ≫ x'
    rw [ha, Category.assoc, Category.assoc, pullback.condition]

/-- The conjugation identity on the normal series passes to the additive kernel
of each transition, since the ambient points and the additive points both lift
locally through faithfully flat projections. -/
private theorem descendScalarConjugation {G E A Q T₀ : Specs.AffineAlgebraicGroup k}
    {K : Specs.ClosedSubgroup E.val}
    (q : G.val ⟶ E.val) (qf : Flat q.hom.hom.left) (qs : Surjective q.hom.hom.left)
    (j : A.val ⟶ G.val) (hj : IsNormalSubgroup j)
    (f : A.val ⟶ Q.val) (v : A.val ⟶ K.group) (e : Q.val ≅ K.group)
    (vf : Flat v.hom.hom.left) (vs : Surjective v.hom.hom.left)
    (hv : v ≫ K.inclusion = j ≫ q) (he : f ≫ e.hom = v)
    (p : G.val ⟶ T₀.val) (p' : E.val ⟶ T₀.val) (hp : q ≫ p' = p)
    (eQ : torusPoints Q.val ≅ Specs.StandardGroups.additivePoints k)
    (χ : ∀ R : TestAlgebra k, GroupPoints T₀.val R → R) (hχ : IsNaturalScalar χ)
    (hact : ∀ (R : TestAlgebra k) (g : GroupPoints G.val R)
        (y z : GroupPoints A.val R),
      onPoints j R z = g * onPoints j R y * g⁻¹ →
      Multiplicative.toAdd (show Multiplicative R from eQ.hom.app R (onPoints f R z)) =
        χ R (onPoints p R g) *
          Multiplicative.toAdd (show Multiplicative R from eQ.hom.app R (onPoints f R y))) :
    IsScalarConjugation ((groupPointsFunctor k).mapIso e.symm ≪≫ eQ) p' χ := by
  let eK := (groupPointsFunctor k).mapIso e.symm ≪≫ eQ
  let value (R : TestAlgebra k) (y : GroupPoints A.val R) : R :=
    Multiplicative.toAdd (show Multiplicative R from eQ.hom.app R (onPoints f R y))
  let I (R : TestAlgebra k) (w : R) := additiveInclusion eK R (Multiplicative.ofAdd w)
  have hi (R) : Function.Injective (I R) :=
    (additiveInclusion_injective eK R).comp Multiplicative.ofAdd.injective
  have hvalue (R : TestAlgebra k) (y : GroupPoints A.val R) :
      I R (value R y) = onPoints q R (onPoints j R y) := by
    have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (eQ.hom_inv_id_app R))
      (onPoints f R y)
    change (eQ.inv.app R).hom ((eQ.hom.app R).hom (onPoints f R y)) = _ at h
    rw [GrpCat.hom_id, MonoidHom.id_apply] at h
    change onPoints K.inclusion R (onPoints e.hom R
      ((eQ.inv.app R).hom ((eQ.hom.app R).hom (onPoints f R y)))) = _
    rw [h, ← pointComp f e.hom, he, ← pointComp v K.inclusion, hv]
    rfl
  intro R g r
  obtain ⟨S, a, ha, g₁, hg₁⟩ := liftPointLocally q qf qs R g
  obtain ⟨B, b, hb, y, hy⟩ := liftPointLocally (Y := closedSubgroupAlgebraicGroup K) v vf vs
    S (eK.inv.app S (Multiplicative.ofAdd (a.hom r)))
  letI := ha
  letI := hb
  let gg := changePoints (H := G.val) b g₁
  have hgg : onPoints q B gg = changePoints b (changePoints a g) := by
    rw [← pointNatural, hg₁]
  have hy' : I B (value B y) = I B (b.hom (a.hom r)) := by
    have hy' : onPoints v B y = changePoints b
        (eK.inv.app S (Multiplicative.ofAdd (a.hom r))) := hy
    rw [hvalue, ← pointComp j q, ← hv, pointComp v K.inclusion, hy']
    rw [← pointNatural]
    exact additiveInclusion_natural eK b (a.hom r)
  have hyr : value B y = b.hom (a.hom r) := hi B hy'
  obtain ⟨z, hz⟩ := normalSubgroup_conjugate_sections hj gg y
  have hz' : onPoints j B z = gg * onPoints j B y * gg⁻¹ := hz
  have hscalar := hact B gg y z hz'
  have hpgg : onPoints p B gg = changePoints b (changePoints a (onPoints p' R g)) := by
    rw [← hp, pointComp, hgg, ← pointNatural,
      ← pointNatural]
  change g * I R r * g⁻¹ = I R (χ R (onPoints p' R g) * r)
  apply (cancel_epi ((testSpec k).map a.op)).mp
  apply (cancel_epi ((testSpec k).map b.op)).mp
  change changePoints b (changePoints a (g * I R r * g⁻¹)) =
    changePoints b (changePoints a (I R (χ R (onPoints p' R g) * r)))
  unfold I
  simp only [map_mul, map_inv, additiveInclusion_natural, hχ]
  change changePoints b (changePoints a g) * I B (b.hom (a.hom r)) *
    (changePoints b (changePoints a g))⁻¹ =
    I B (χ B (changePoints b (changePoints a (onPoints p' R g))) * b.hom (a.hom r))
  rw [← hgg, ← hyr, ← hpgg, ← hscalar, hvalue, hvalue, hz', map_mul, map_mul, map_inv]

end QuotientTower

section Assembly

open private Unipotent.group_hom_ext Unipotent.scheme_hom_spec Unipotent.kernel_points
  from LinearAlgebraicGroups.Unipotent.CentralSeries
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

variable {E Y T₀ : Specs.AffineAlgebraicGroup k}

/-- Splitting with rational conjugators in the scheme kernel of the projection. -/
private def Splits (p : E.val ⟶ T₀.val) : Prop :=
  (∃ s : T₀.val ⟶ E.val, s ≫ p = 𝟙 _) ∧
  ∀ s₁ s₂ : T₀.val ⟶ E.val, s₁ ≫ p = 𝟙 _ → s₂ ≫ p = 𝟙 _ →
    ∃ g : GroupPoints E.val (groundTest k), onPoints p (groundTest k) g = 1 ∧
      ∀ (R : TestAlgebra k) (t : GroupPoints T₀.val R),
        onPoints s₂ R t = rationalAt g R * onPoints s₁ R t * (rationalAt g R)⁻¹

private theorem conjugateSection (s : T₀.val ⟶ E.val)
    (g : GroupPoints E.val (groundTest k)) :
    ∃ s' : T₀.val ⟶ E.val, ∀ (R : TestAlgebra k) (t : GroupPoints T₀.val R),
      onPoints s' R t = rationalAt g R * onPoints s R t * (rationalAt g R)⁻¹ := by
  let α : torusPoints T₀.val ⟶ torusPoints E.val :=
    { app R := GrpCat.ofHom ((MulAut.conj (rationalAt g R)).toMonoidHom.comp (onPoints s R))
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro t
        change rationalAt g S * onPoints s S (changePoints a t) * (rationalAt g S)⁻¹ =
          changePoints a (rationalAt g R * onPoints s R t * (rationalAt g R)⁻¹)
        rw [map_mul, map_mul, map_inv, rationalAt_natural, pointNatural] }
  exact ⟨_, Unipotent.scheme_hom_spec α⟩

private theorem splits_of_additiveTransition {N : Specs.ClosedSubgroup E.val}
    (q : E.val ⟶ Y.val) (p₀ : Y.val ⟶ T₀.val)
    (hk : IsSchemeKernel q N) (hq : Specs.Fppf.IsFppf q.hom.hom.left)
    (e : torusPoints N.group ≅ Specs.StandardGroups.additivePoints k)
    (χ : ∀ R : TestAlgebra k, GroupPoints T₀.val R → R) (hχ : IsNaturalScalar χ)
    (hact : IsScalarConjugation e (q ≫ p₀) χ) (hT : IsSplitTorus T₀.val)
    (h₀ : Splits p₀) : Splits (q ≫ p₀) := by
  constructor
  · obtain ⟨s, hs⟩ := h₀.1
    obtain ⟨σ, hσ⟩ := liftSection e p₀ s hs hk hq χ hχ hact hT
    exact ⟨σ, by rw [← Category.assoc, hσ, hs]⟩
  · intro s₁ s₂ hs₁ hs₂
    have h₁ : (s₁ ≫ q) ≫ p₀ = 𝟙 _ := (Category.assoc ..).trans hs₁
    have h₂ : (s₂ ≫ q) ≫ p₀ = 𝟙 _ := (Category.assoc ..).trans hs₂
    obtain ⟨a, ha, hac⟩ := h₀.2 (s₁ ≫ q) (s₂ ≫ q) h₁ h₂
    obtain ⟨j, hj⟩ := additiveQuotientSection q hq hk e
    let b : GroupPoints E.val (groundTest k) := a ≫ j
    have hba : onPoints q (groundTest k) b = a := by
      change (a ≫ j) ≫ q.hom.hom = a
      rw [Category.assoc, hj, Category.comp_id]
    obtain ⟨s', hs'⟩ := conjugateSection s₁ b
    have hsame : s' ≫ q = s₂ ≫ q := by
      apply Unipotent.group_hom_ext T₀.property.1
      intro R t
      rw [pointComp, hs', map_mul, map_mul, map_inv]
      have h : onPoints q R (rationalAt b R) = rationalAt a R := by
        rw [← pointNatural, hba]
      rw [h, ← pointComp]
      exact (hac R t).symm
    have hst : s' ≫ q ≫ p₀ = 𝟙 _ := by rw [← Category.assoc, hsame, h₂]
    obtain ⟨c, hc⟩ := conjugacyInAdditiveKernel e p₀ s' s₂ hst hsame hk χ hχ hact hT
    let g := onPoints N.inclusion (groundTest k) c * b
    refine ⟨g, ?_, ?_⟩
    · have hck : onPoints q (groundTest k) (onPoints N.inclusion (groundTest k) c) = 1 :=
        (Unipotent.kernel_points q N hk _ _).mpr ⟨c, rfl⟩
      dsimp only [g]
      rw [pointComp, map_mul, hck, hba, one_mul, ha]
    · intro R t
      have hg : rationalAt g R = onPoints N.inclusion R (rationalAt c R) * rationalAt b R := by
        change changePoints (fromGround R) (onPoints N.inclusion (groundTest k) c * b) = _
        rw [map_mul, pointNatural]
      rw [hc, hs', hg, mul_inv_rev]
      group

private theorem splits_comp_iso (q : E.val ≅ Y.val) (p : Y.val ⟶ T₀.val)
    (h : Splits p) : Splits (q.hom ≫ p) := by
  constructor
  · obtain ⟨s, hs⟩ := h.1
    exact ⟨s ≫ q.inv, by simp [hs]⟩
  · intro s₁ s₂ h₁ h₂
    obtain ⟨g, hg, hconj⟩ := h.2 (s₁ ≫ q.hom) (s₂ ≫ q.hom)
      ((Category.assoc ..).trans h₁) ((Category.assoc ..).trans h₂)
    refine ⟨onPoints q.inv (groundTest k) g, ?_, ?_⟩
    · rw [← pointComp, Iso.inv_hom_id_assoc]
      exact hg
    · intro R t
      have he := congrArg (onPoints q.inv R) (hconj R t)
      rw [map_mul, map_mul, map_inv, ← pointNatural q.inv] at he
      rw [← pointComp (s₁ ≫ q.hom) q.inv, ← pointComp (s₂ ≫ q.hom) q.inv,
        Category.assoc s₁, Category.assoc s₂, Iso.hom_inv_id, Category.comp_id,
        Category.comp_id] at he
      exact he

private theorem splits_id (T₀ : Specs.AffineAlgebraicGroup k) : Splits (𝟙 T₀.val) := by
  refine ⟨⟨𝟙 _, Category.id_comp _⟩, ?_⟩
  intro s₁ s₂ h₁ h₂
  have h₁' : s₁ = 𝟙 _ := (Category.comp_id _).symm.trans h₁
  have h₂' : s₂ = 𝟙 _ := (Category.comp_id _).symm.trans h₂
  subst s₁
  subst s₂
  refine ⟨1, map_one _, ?_⟩
  intro R t
  have h : rationalAt (1 : GroupPoints T₀.val (groundTest k)) R = 1 :=
    (changePoints (fromGround R)).map_one
  rw [h, one_mul, inv_one, mul_one]

private lemma groundStructureMap :
    ((testSpec k).obj (op (groundTest k))).hom = 𝟙 (Spec (CommRingCat.of k)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
  have h : CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) :=
    CommRingCat.hom_ext (RingHom.ext fun x => rfl)
  exact (congrArg Spec.map h).trans (Spec.map_id (CommRingCat.of k))

private def groundIso : (testSpec k).obj (op (groundTest k)) ≅ 𝟙_ (SchemeOver k) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of k)))
    ((Category.id_comp (𝟙 (Spec (CommRingCat.of k)))).trans (groundStructureMap (k := k)).symm)

private lemma rationalAt_const {H : Specs.GroupScheme k}
    (a : GroupPoints H (groundTest k)) (R : TestAlgebra k) :
    rationalAt a R = toUnit ((testSpec k).obj (op R)) ≫ (groundIso (k := k)).inv ≫ a := by
  let X := (testSpec k).obj (op R)
  let X₀ := (testSpec k).obj (op (groundTest k))
  let i : 𝟙_ (SchemeOver k) ⟶ X₀ := (groundIso (k := k)).inv
  let f : X ⟶ X₀ := (testSpec k).map (fromGround R).op
  have hT : IsTerminal X₀ := (isTerminalTensorUnit (C := SchemeOver k)).ofIso
    (groundIso (k := k)).symm
  have h : f = toUnit X ≫ i := hT.hom_ext _ _
  exact (congrArg (fun u : X ⟶ X₀ => u ≫ a) h).trans (Category.assoc _ _ _)

end Assembly

open private Unipotent.represented_quotient_of_kernel Unipotent.closedSeries_inclusion_closed
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private Unipotent.scheme_kernel_of_points Unipotent.scheme_kernel_of_iso Unipotent.kernel_points
  from LinearAlgebraicGroups.Unipotent.CentralSeries
open private EquivariantUnipotentSeries.liftGroupHomOfQuotient
  from LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes

theorem splitTorusExtension : Specs.TorusSections.SplitTorusExtension.{u} := by
  intro k _ _ G T U p hk hf hs hT hUs hUc hU
  have hffp := fppf_of_faithfullyFlat (G := G) (E := G) (Y := T) (𝟙 _) p
    (inferInstanceAs (Flat (𝟙 G.val.X.left))) (inferInstanceAs (Surjective (𝟙 G.val.X.left)))
    (by simpa only [Category.id_comp] using hf) (by simpa only [Category.id_comp] using hs)
  have hp := Unipotent.represented_quotient_of_kernel p U hk hf hs hffp.2.2
  obtain ⟨n, S, _, _, hN, hF⟩ :=
    EquivariantUnipotentSeries.stableSeriesForTorusExtension G T U p hp hT hUs hUc hU
  let j (i : ℕ) := S.inclusion i ≫ U.inclusion
  have hj (i : ℕ) : IsClosedImmersion (j i).hom.hom.left := by
    letI := Unipotent.closedSeries_inclusion_closed S i
    letI := U.isClosedImmersion
    change IsClosedImmersion ((S.inclusion i).hom.hom.left ≫ U.inclusion.hom.hom.left)
    infer_instance
  let N (i : ℕ) : Specs.ClosedSubgroup G.val := ⟨_, j i, hj i⟩
  have jnext (i : ℕ) : j (i + 1) = S.step i ≫ j i := by
    change (S.step i ≫ S.inclusion i) ≫ U.inclusion = _
    exact Category.assoc ..
  have stage (i : ℕ) (hi : i ≤ n) :
      ∃ (E : Specs.AffineAlgebraicGroup k) (q : G.val ⟶ E.val) (p' : E.val ⟶ T.val),
        Specs.Unipotent.IsFppfGroupQuotient (N i) q ∧ q ≫ p' = p ∧ Splits p' := by
    induction i with
    | zero =>
      have hk' : IsSchemeKernel p (N 0) :=
        Unipotent.scheme_kernel_of_iso p (j 0) (hj 0) U hk S.top rfl
      exact ⟨T, p, 𝟙 _, Unipotent.represented_quotient_of_kernel p _ hk' hf hs hffp.2.2,
        Category.comp_id _, splits_id T⟩
    | succ i ih =>
      obtain ⟨Y, q₀, p₀, hq₀, hq₀p, h₀⟩ := ih (by omega)
      obtain ⟨_, _, E, q, _, _, hqk, hfq, _, hre⟩ :=
        normalAffineQuotient G (N (i + 1)) (hN (i + 1) hi)
      have hq : Specs.Unipotent.IsFppfGroupQuotient (N (i + 1)) q :=
        ⟨hqk, hfq.2.1, hfq.2.2.1, hfq.2.2.2.1, hre⟩
      have hkill : (N (i + 1)).inclusion.hom.hom ≫ q₀.hom.hom = 1 := by
        change (j (i + 1)).hom.hom ≫ q₀.hom.hom = 1
        rw [jnext]
        change ((S.step i).hom.hom ≫ (j i).hom.hom) ≫ q₀.hom.hom = 1
        rw [Category.assoc, show (j i).hom.hom ≫ q₀.hom.hom = 1 from killKernel hq₀.1,
          MonObj.comp_one]
      obtain ⟨π, hπ⟩ := EquivariantUnipotentSeries.liftGroupHomOfQuotient q hq q₀ hkill
      have hπf := fppf_of_faithfullyFlat q π hq.2.1 hq.2.2.1
        (hπ.symm ▸ hq₀.2.1) (hπ.symm ▸ hq₀.2.2.1)
      obtain ⟨Q, f, eQ, M, eM, char, hfactor, hact⟩ := hF i (by omega)
      have hclose : IsClosedImmersion (S.step i ≫ j i).hom.hom.left := by
        rw [← jnext]
        exact hj (i + 1)
      have hq' : Specs.Unipotent.IsFppfGroupQuotient ⟨_, S.step i ≫ j i, hclose⟩ q := by
        have he : (⟨(S.term (i + 1)).val, S.step i ≫ j i, hclose⟩ : Specs.ClosedSubgroup G.val) =
            N (i + 1) := by
          change _ = (⟨(S.term (i + 1)).val, j (i + 1), hj (i + 1)⟩ :
            Specs.ClosedSubgroup G.val)
          revert hclose
          rw [← jnext]
          intro hclose
          rfl
        rw [he]
        exact hq
      obtain ⟨K, v, e, hK, hvf, hvs, hv, he⟩ :=
        transitionKernel (j i) (hj i) (S.step i) (S.closed i) hclose q₀ q π hπ hq₀.1 hq' f hfactor
      let χ (R : TestAlgebra k) (t : GroupPoints T.val R) : R :=
        (show Rˣ from eM.hom.app R (onPoints char R t)).val
      have hχ : IsNaturalScalar χ := by
        intro R S a t
        have hm := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (eM.hom.naturality a))
          (onPoints char R t)
        change (eM.hom.app S).hom (changePoints a (onPoints char R t)) =
          Units.map a.hom.toMonoidHom (eM.hom.app R (onPoints char R t)) at hm
        rw [pointNatural] at hm
        exact (congrArg (fun x : Sˣ => x.val) hm).symm
      have hqp : q ≫ π ≫ p₀ = p := by rw [← Category.assoc, hπ, hq₀p]
      have hact' := descendScalarConjugation q hq.2.1 hq.2.2.1 (j i) (hN i (by omega))
        f v e hvf hvs hv he p (π ≫ p₀) hqp eQ χ hχ hact
      exact ⟨E, q, π ≫ p₀, hq, hqp,
        splits_of_additiveTransition π p₀ hK hπf _ χ hχ hact' hT h₀⟩
  obtain ⟨E, q, p', hq, hqp, he⟩ := stage n le_rfl
  have hid : IsSchemeKernel (𝟙 G.val) (N n) := by
    apply Unipotent.scheme_kernel_of_points
    intro R x
    have hsub (a : GroupPoints (S.term n).val R) : a = 1 := by
      have inj := (CategoryTheory.Iso.app ((groupPointsFunctor k).mapIso S.bottom) R).groupIsoToMulEquiv.injective
      apply inj
      exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
    constructor
    · intro hx
      have hx' : x = 1 := (Category.comp_id x).symm.trans hx
      exact ⟨1, (onPoints (j n) R).map_one.trans hx'.symm⟩
    · rintro ⟨a, ha⟩
      rw [hsub a, map_one] at ha
      exact (Category.comp_id x).trans ha.symm
  have hidQ := Unipotent.represented_quotient_of_kernel (𝟙 G.val) (N n) hid
    (inferInstanceAs (Flat (𝟙 G.val.X.left))) (inferInstanceAs (Surjective (𝟙 G.val.X.left)))
    (inferInstanceAs (LocallyOfFinitePresentation (𝟙 G.val.X.left)))
  obtain ⟨iso, hiso⟩ := quotientIso hidQ hq
  have hiso' : iso.hom = q := (Category.id_comp _).symm.trans hiso
  have ht : Splits p := by
    rw [← hqp, ← hiso']
    exact splits_comp_iso iso p' he
  refine ⟨ht.1, ?_⟩
  intro s₁ s₂ h₁ h₂
  obtain ⟨g, hg, hconj⟩ := ht.2 s₁ s₂ h₁ h₂
  obtain ⟨a, ha⟩ := (Unipotent.kernel_points p U hk _ _).mp hg
  let a' : (testSpec k).obj (op (groundTest k)) ⟶ U.group.X := a
  have ha' : a' ≫ U.inclusion.hom.hom = g := ha
  let b : 𝟙_ (SchemeOver k) ⟶ U.group.X := (groundIso (k := k)).inv ≫ a'
  let c : T.val.X ⟶ G.val.X := toUnit T.val.X ≫ b ≫ U.inclusion.hom.hom
  refine ⟨b, ?_⟩
  change s₂.hom.hom = c * s₁.hom.hom * c⁻¹
  apply hom_ext_of_points T.property.1
  intro R t
  have hc : t ≫ c = rationalAt g R := by
    dsimp only [c, b]
    rw [← Category.assoc t, comp_toUnit, rationalAt_const, Category.assoc, ha']
  simp only [MonObj.comp_mul, GrpObj.comp_inv, hc]
  exact hconj R t

end

end LinearAlgebraicGroups.TorusSections
