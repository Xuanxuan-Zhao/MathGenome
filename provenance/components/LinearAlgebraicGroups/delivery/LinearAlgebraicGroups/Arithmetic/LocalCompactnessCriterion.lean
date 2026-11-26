import Specs.LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
import LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
import LinearAlgebraicGroups.Arithmetic.ReductiveModelSpreading
import LinearAlgebraicGroups.Arithmetic.SmoothBorelParameter
import LinearAlgebraicGroups.Reductive.RationalOppositeBorels
import LinearAlgebraicGroups.Arithmetic.CharacteristicZeroCompactness
import LinearAlgebraicGroups.Arithmetic.CompactProductIsolation
import LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import LinearAlgebraicGroups.Descent.FiniteFieldFlags
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.Topology.Algebra.MvPolynomial

open AlgebraicGeometry CategoryTheory Filter Set Topology
open scoped Classical RestrictedProduct

noncomputable section

universe u v v'

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion

open AdelicGroups ArithmeticLatticeProjection CompactProductIsolation ProjectiveRecurrence
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization)
open Specs.AnisotropicAdNilpotents (IsAnisotropic)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.LocalCompactnessCriterion
open Specs.Arithmetic.ProjectiveRecurrence

open private cosetMap continuous_cosetMap surjective_cosetMap
  from LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

local instance numberCompletionField {K : Type u} [Field K] [hK : NumberField K]
    (w : NumberPlace K) : Field ((GlobalFieldData.number.{u, v} hK).Completion w) :=
  GlobalFieldData.instFieldCompletion (GlobalFieldData.number.{u, v} hK) w

local instance numberCompletionTopology {K : Type u} [Field K] [hK : NumberField K]
    (w : NumberPlace K) : TopologicalSpace ((GlobalFieldData.number.{u, v} hK).Completion w) :=
  GlobalFieldData.instTopologicalSpaceCompletion (GlobalFieldData.number.{u, v} hK) w

local instance numberCompletionAlgebra {K : Type u} [Field K] [hK : NumberField K]
    (w : NumberPlace K) : Algebra K ((GlobalFieldData.number.{u, v} hK).Completion w) :=
  completionAlgebra (GlobalFieldData.number.{u, v} hK) w

private def numberLocalChange {K : Type u} [Field K] [hK : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (w : (GlobalFieldData.number.{u, v} hK).Place) :
    LocalPoints (GlobalFieldData.number.{u, v} hK) i w →*
      LocalPoints (GlobalFieldData.number.{u, v'} hK) i w := by
  cases w <;> exact MonoidHom.id _

private theorem numberLocalChange_mem {K : Type u} [Field K] [hK : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (w : (GlobalFieldData.number.{u, v} hK).Place)
    (x : LocalPoints (GlobalFieldData.number.{u, v} hK) i w)
    (hx : x ∈ localSubgroup (GlobalFieldData.number.{u, v} hK) i w) :
    numberLocalChange.{u, v, v'} i w x ∈ localSubgroup (GlobalFieldData.number.{u, v'} hK) i w := by
  cases w <;> exact hx

private def numberAdelicChange {K : Type u} [Field K] [hK : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    Adeles (GlobalFieldData.number.{u, v} hK) i S →*
      Adeles (GlobalFieldData.number.{u, v'} hK) i S :=
  RestrictedProduct.mapAlongMonoidHom _ _ id tendsto_id
    (fun w => numberLocalChange.{u, v, v'} i w.val)
    (Eventually.of_forall fun w => numberLocalChange_mem.{u, v, v'} i w.val)

private theorem numberAdelicChange_continuous {K : Type u} [Field K] [hK : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    Continuous (numberAdelicChange.{u, v, v'} i S) := by
  let D := GlobalFieldData.number.{u, v} hK
  let E := GlobalFieldData.number.{u, v'} hK
  exact RestrictedProduct.mapAlong_continuous
    (fun w : Outside D S => LocalPoints D i w.val) (fun w : Outside E S => LocalPoints E i w.val)
    (A₁ := fun w => localSubgroup D i w.val) (A₂ := fun w => localSubgroup E i w.val)
    id tendsto_id
    (fun w => numberLocalChange.{u, v, v'} i w.val)
    (Eventually.of_forall fun w => numberLocalChange_mem.{u, v, v'} i w.val)
    (by rintro ⟨_ | _, _⟩ <;> exact continuous_id)

private theorem numberAdelicChange_surjective {K : Type u} [Field K] [hK : NumberField K]
    {G : AffineAlgebraicGroup K} (i : MatrixRealization G) (S : Finset (NumberPlace K)) :
    Function.Surjective (numberAdelicChange.{u, v, v'} i S) := by
  intro x
  refine ⟨numberAdelicChange.{u, v', v} i S x, ?_⟩
  apply RestrictedProduct.ext
  rintro ⟨_ | _, _⟩ <;> rfl

private theorem compactFullQuotient {K : Type u} [Field K] [NumberField K]
    (D : GlobalFieldData.{u, u} K) (hD : D = .number inferInstance)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hss : IsSemisimple G) (han : IsAnisotropic G.val) :
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) := by
  subst D
  obtain ⟨d, hd, hc⟩ :=
    CharacteristicZeroCompactness.anisotropicAdelicCompactness G hss han i
  letI := hc
  letI : IsTopologicalGroup (Adeles (GlobalFieldData.number.{u, 0} inferInstance) i ∅) :=
    AdelicGroups.adelicTopology (GlobalFieldData.number.{u, 0} inferInstance) i ∅
  letI : IsTopologicalGroup (Adeles (GlobalFieldData.number.{u, u} inferInstance) i ∅) :=
    AdelicGroups.adelicTopology (GlobalFieldData.number.{u, u} inferInstance) i ∅
  let f := numberAdelicChange.{u, 0, u} i ∅
  have hf : d.range ≤ (diagonalSubgroup (GlobalFieldData.number.{u, u} inferInstance) i).comap f := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    rintro ⟨w | w, hw⟩
    · exact hd g ⟨.inl w, hw⟩
    · exact hd g ⟨.inr w, hw⟩
  exact ⟨(Function.Surjective.range_eq
    (surjective_cosetMap f hf (numberAdelicChange_surjective i ∅))) ▸
    isCompact_range (continuous_cosetMap f hf (numberAdelicChange_continuous i ∅))⟩

theorem cocompactLattice : CocompactLattice.{u} := by
  intro K _ _ D hD G i hG han S T hS hST hSn hArch
  let U := integralOutside D i T
  have hq := compactFullQuotient D hD G i hG.1 han
  obtain ⟨hc, ho⟩ := compactOpenOutside D i T hArch
  obtain ⟨hinj, hclosed, hdiscrete, hcompact, _, _, hmeasure⟩ :=
    latticeConstruction D i T U hq (hS.mono hST) hc ho
  exact ⟨hc, ho, hinj, hclosed, hdiscrete, hcompact, hmeasure,
    fun J hJ hJn hJS => projectionProperties D i S T J U hST hJ hq hSn hJn hJS hc ho⟩

open private joinAdeles joinAdeles_continuous projectFinite_joinAdeles
  forgetOutside_joinAdeles joinAdeles_project joinAdeles_one
  from LinearAlgebraicGroups.Arithmetic.CompactProductIsolation

/-- A subgroup of finite index contains a suitable conjugating power, so the
contraction can be computed in the subgroup topology. -/
private theorem contracted_in_finiteIndex {J : Type u} [Group J] [TopologicalSpace J]
    (H : Subgroup J) [H.FiniteIndex] (x : H) (hx : Contracted (x : J)) :
    Contracted x := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨n, hn, _, hpow⟩ := H.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := H)) a
  refine ⟨⟨a ^ n, hpow⟩, ?_⟩
  apply tendsto_subtype_rng.mpr
  have hsub : Tendsto (fun m : ℕ => n * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by
      simpa using Nat.mul_le_mul_right m (Nat.succ_le_of_lt hn)) tendsto_id
  have h := ha.comp hsub
  change Tendsto (fun m : ℕ => a ^ (n * m) * (x : J) * (a ^ (n * m))⁻¹) atTop (𝓝 1) at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_one,
    pow_mul] using h

/-- The compact-product quotient can be applied over the projected closure
itself, even when that closure has proper finite index. -/
private theorem insertContracted {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G)
    (S J : Finset D.Place) (h : Disjoint J S) (U : Subgroup (Adeles D i (S ∪ J)))
    (hUc : IsCompact (U : Set (Adeles D i (S ∪ J))))
    (hUo : IsOpen (U : Set (Adeles D i (S ∪ J))))
    (H : Subgroup (FinitePoints D i J)) [H.FiniteIndex]
    (hH : (H : Set (FinitePoints D i J)) = closure (projectedArithmetic D i S J U : Set _))
    (x : H) (hx : Contracted (x : FinitePoints D i J)) :
    insertFinite D i S J x ∈ diagonalClosure D i S := by
  let join := (joinAdeles D i S J).comp (H.subtype.prodMap U.subtype)
  let Z := diagonalClosedSubgroup D i S
  let P : Subgroup (H × U) := Z.comap join
  have hZ : (Z : Set (Adeles D i S)) = diagonalClosure D i S := diagonalClosedSubgroup_coe D i S
  have hjoin : Continuous join := (joinAdeles_continuous D i S J).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  have hZclosed : IsClosed (Z : Set (Adeles D i S)) := hZ.symm ▸ isClosed_closure
  have hP : IsClosed (P : Set (H × U)) := hZclosed.preimage hjoin
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  have hon : Function.Surjective ((MonoidHom.fst H U).comp P.subtype) := by
    intro y
    have hy : (y : FinitePoints D i J) ∈
        (projectFinite D i h) '' compatibleAdeles D i S J U := by
      rw [(isolateAdelicFactors D i S J h U hUc hUo).1, ← hH]
      exact y.property
    obtain ⟨z, ⟨hz, hu⟩, hzy⟩ := hy
    refine ⟨⟨(y, ⟨_, hu⟩), ?_⟩, rfl⟩
    change joinAdeles D i S J ((y : FinitePoints D i J),
      forgetOutside D i Finset.subset_union_left z) ∈ Z
    rw [← hzy, joinAdeles_project D i h]
    change z ∈ (Z : Set (Adeles D i S))
    rwa [hZ]
  obtain ⟨_, hN, φ, ⟨_, hcontract, hker, _⟩, _⟩ := compactProductIsolation P hP hon
  have hm := (hker x).mp (hcontract x (contracted_in_finiteIndex H x hx))
  change joinAdeles D i S J ((x : FinitePoints D i J), ((1 : U) : Adeles D i (S ∪ J))) ∈ Z at hm
  rw [Subgroup.coe_one, joinAdeles_one] at hm
  exact hZ ▸ hm

private theorem eval_smul_homogeneous {I F : Type*} [Field F]
    {p : MvPolynomial I F} {d : ℕ} (hp : p.IsHomogeneous d) (t : F) (y : I → F) :
    p.eval (t • y) = t ^ d * p.eval y := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support hm]
  ring

/-- A common fiber of homogeneous polynomials of positive degree is bounded
if their common zero locus consists only of the origin. -/
private theorem boundedInvariantFiber {I A F : Type*} [Fintype I] [Fintype A]
    [NormedField F] [ProperSpace F] (p : A → MvPolynomial I F) (d : A → ℕ)
    (hd : ∀ a, 0 < d a) (hp : ∀ a, (p a).IsHomogeneous (d a))
    (hzero : ∀ y : I → F, y ≠ 0 → ∃ a, (p a).eval y ≠ 0) (x : I → F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : I → F, (∀ a, (p a).eval y = (p a).eval x) → ‖y‖ ≤ C := by
  classical
  let B : Set (I → F) := Metric.sphere 0 1
  have hnorm {y : I → F} (hy : y ≠ 0) :
      ∃ j : I, ‖y j‖ = ‖y‖ := by
    obtain ⟨j, hj⟩ : ∃ j : I, y j ≠ 0 := by
      by_contra! h
      exact hy (funext h)
    obtain ⟨j', _, hmax⟩ := Finset.univ.exists_max_image (fun j => ‖y j‖)
      ⟨j, Finset.mem_univ j⟩
    exact ⟨j', le_antisymm (norm_le_pi_norm y j') ((pi_norm_le_iff_of_nonneg
      (norm_nonneg (y j'))).mpr fun l => hmax l (Finset.mem_univ l))⟩
  have hscale {y : I → F} (hy : y ≠ 0) :
      ∃ t : F, ‖t‖ = ‖y‖ ∧ t⁻¹ • y ∈ B := by
    obtain ⟨j, hj⟩ := hnorm hy
    refine ⟨y j, hj, ?_⟩
    change dist ((y j)⁻¹ • y) 0 = 1
    rw [dist_zero_right, norm_smul, norm_inv, hj, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  by_cases hB : B.Nonempty
  · let f : (I → F) → ℝ := fun y => ∑ a, ‖(p a).eval y‖
    have hf : Continuous f :=
      continuous_finsetSum _ fun a _ => (MvPolynomial.continuous_eval (p a)).norm
    obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_sphere (0 : I → F) 1).exists_isMinOn hB hf.continuousOn
    have hy₀n : y₀ ≠ 0 := by
      intro he
      simp [he] at hy₀
    obtain ⟨a, ha⟩ := hzero y₀ hy₀n
    have hfpos : 0 < f y₀ := Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨a, Finset.mem_univ _, norm_pos_iff.mpr ha⟩
    let C := max 1 (f x / f y₀)
    refine ⟨C, (zero_le_one : (0 : ℝ) ≤ 1).trans (le_max_left _ _), fun y hy => ?_⟩
    by_cases hy1 : ‖y‖ ≤ 1
    · exact hy1.trans (le_max_left _ _)
    have hyn : y ≠ 0 := by
      intro he
      exact hy1 (by simp [he])
    obtain ⟨t, ht, hb⟩ := hscale hyn
    have htl : 1 ≤ ‖t‖ := ht ▸ (le_of_not_ge hy1)
    have htn : ‖t‖ ≠ 0 := ne_of_gt (zero_lt_one.trans_le htl)
    have hbound : f (t⁻¹ • y) ≤ (‖t‖)⁻¹ * f x := by
      unfold f
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      rw [eval_smul_homogeneous (hp a), hy a, norm_mul, norm_pow, norm_inv]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa using pow_le_pow_of_le_one (inv_nonneg.mpr (norm_nonneg t))
        (inv_le_one_of_one_le₀ htl) (Nat.succ_le_of_lt (hd a))
    have h := (hmin hb).trans hbound
    rw [← div_eq_inv_mul, le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) htn.symm)] at h
    have hxle := (le_div_iff₀ hfpos).mpr (by simpa only [mul_comm] using h)
    exact ht ▸ hxle.trans (le_max_right _ _)
  · refine ⟨0, le_rfl, fun y _ => ?_⟩
    by_cases hy : y = 0
    · simp [hy]
    obtain ⟨t, _, ht⟩ := hscale hy
    exact (hB ⟨t⁻¹ • y, ht⟩).elim

open private bracketMatrix_mulVec from LinearAlgebraicGroups.Arithmetic.CharacteristicZeroCompactness
open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private compactLocalBasisBox from LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds
open private presentation matrixEntry pullback_finite pointEvaluation_matrixEntry
  continuous_pointEvaluation pointEvaluation_root pointEvaluation exists_compact_of_monic_roots
  from LinearAlgebraicGroups.Arithmetic.FiniteAdelicMorphism

/-- A finite morphism over a proper normed field has compact source points
when the target point space is compact. -/
private theorem compactOfFinite {F : Type u} [NormedField F] [ProperSpace F]
    {G Q : AffineAlgebraicGroup F} (q : G.val ⟶ Q.val)
    (hq : IsFinite q.hom.hom.left)
    (i : MatrixRealization G) (j : MatrixRealization Q) [CompactSpace (PointsIn j F)] :
    CompactSpace (PointsIn i F) := by
  let P := presentation i
  let T := presentation j
  have hinv : Tendsto (Inv.inv : F → F) (cocompact F) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hbound (a b : Specs.Unipotent.Index.{u} i.size) :
      ∃ B : Set F, IsCompact B ∧ ∀ g : PointsIn i F, (asMatrix i F g).val a b ∈ B := by
    obtain ⟨p, hp, hr⟩ := (pullback_finite P T q hq).to_isIntegral (matrixEntry P a b)
    obtain ⟨B, hB, hroot⟩ := exists_compact_of_monic_roots hinv
      (fun g : PointsIn j F => (pointEvaluation T g).toRingHom)
      (continuous_pointEvaluation T) p hp univ isCompact_univ
    refine ⟨B, hB, fun g => ?_⟩
    rw [← pointEvaluation_matrixEntry P]
    exact hroot _ (mem_univ _) _ (pointEvaluation_root P T q _ p hr g)
  choose B hB hm using hbound
  let C := ⋃ a, ⋃ b, B a b
  have hC : IsCompact C := isCompact_iUnion fun a => isCompact_iUnion (hB a)
  refine ⟨IsCompact.of_isClosed_subset
    ((asMatrix_isClosedEmbedding i F).isCompact_preimage (compactLocalBasisBox C hC))
    isClosed_univ ?_⟩
  intro g _
  have hmem (x : PointsIn i F) (a b) : (asMatrix i F x).val a b ∈ C :=
    mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b, hm a b x⟩⟩
  refine ⟨hmem g, fun a b => ?_⟩
  simpa only [map_inv] using hmem g⁻¹ a b

/-- Adjoint invariant fibers bound every column of every matrix and inverse
matrix in the adjoint image. -/
private theorem compactOfAnisotropic {F : Type u} [NormedField F] [ProperSpace F] [CharZero F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (hG : IsSemisimple G) (ha : IsAnisotropic G.val) :
    CompactSpace (PointsIn i F) := by
  classical
  open CharacteristicZeroCompactness in
  obtain ⟨Z, Q, q, _, _, hfin, _, s, n, b, T, L, l, A, j, ι, _, hclosed, _, _, _,
    hlocal, _⟩ := LinearAlgebraicGroups.AdjointLieAutomorphisms.adjointRealization G hG
  let := s.lieRing
  let := s.lieAlgebra
  let J : MatrixRealization Q := ⟨n, L, l, ι ≫ j, hclosed⟩
  let I := Specs.Unipotent.Index.{u} n
  let c := CharacteristicZeroCompactness.bracketConstants b
  let p := CharacteristicZeroCompactness.adjointCoefficient c
  have hinv (g : PointsIn J F) (x : I → F) (r : Fin (Fintype.card I)) :
      (p r).eval ((asMatrix J F g).val.mulVec x) = (p r).eval x := by
    have h := CharacteristicZeroCompactness.adjointCoefficient_invariant c (RingHom.id F)
      (asMatrix J F g) x
      (CharacteristicZeroCompactness.bracketMatrix_conj c _ _ (by
        intro y z
        rw [bracketMatrix_mulVec, bracketMatrix_mulVec]
        exact (hlocal (CommAlgCat.of F F) g).1 y z) x) r
    simpa only [MvPolynomial.eval₂_id] using h
  have hcol (a : I) :
      ∃ R : ℝ, 0 ≤ R ∧ ∀ g : PointsIn J F, ∀ k : I, ‖(asMatrix J F g).val k a‖ ≤ R := by
    obtain ⟨R, hR, h⟩ := boundedInvariantFiber p (fun r => Fintype.card I - r)
      (fun r => Nat.sub_pos_of_lt r.isLt)
      (CharacteristicZeroCompactness.adjointCoefficient_homogeneous c)
      (CharacteristicZeroCompactness.exists_nonzero_invariant G hG ha s b)
      (Pi.single a 1)
    refine ⟨R, hR, fun g k => ?_⟩
    have hbound := h _ (hinv g (Pi.single a 1))
    have he := (norm_le_pi_norm ((asMatrix J F g).val.mulVec (Pi.single a 1)) k).trans hbound
    simpa [Matrix.mulVec_single] using he
  choose R hR hb using hcol
  let B : Set F := ⋃ a : I, Metric.closedBall 0 (R a)
  have hB : IsCompact B := isCompact_iUnion fun a => isCompact_closedBall 0 (R a)
  have hb' (g : PointsIn J F) (a k : I) : (asMatrix J F g).val k a ∈ B :=
    mem_iUnion.mpr ⟨a, Metric.mem_closedBall.mpr (by simpa using hb a g k)⟩
  letI : CompactSpace (PointsIn J F) := by
    refine ⟨IsCompact.of_isClosed_subset
      ((asMatrix_isClosedEmbedding J F).isCompact_preimage (compactLocalBasisBox B hB))
      isClosed_univ ?_⟩
    intro g _
    refine ⟨fun k a => hb' g a k, fun k a => ?_⟩
    simpa only [map_inv] using hb' g⁻¹ a k
  exact compactOfFinite q hfin i J

open private empty_power_iso dimension_of_iso standard_torus_dimension split_dimension_le_rank
  from LinearAlgebraicGroups.Descent.RelativeRank
open private matrixPresentation continuous_glEvaluation coordinateMap_of_map
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private coordinateMap from LinearAlgebraicGroups.Arithmetic.IntegralModels
open private glEvaluation from LinearAlgebraicGroups.Affine.StandardGroups

/-- A nontrivial split torus contributes an unbounded coordinate function on
its rational point group. Its point group is closed in the ambient group. -/
private theorem anisotropicOfCompact {F : Type u} [NormedField F]
    (hF : ∃ t : F, 1 < ‖t‖) (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (hcompact : CompactSpace (PointsIn i F)) : IsAnisotropic G.val := by
  classical
  letI := hcompact
  intro T hT
  obtain ⟨n, ⟨e⟩⟩ := hT
  cases n with
  | zero => exact ⟨e ≪≫ empty_power_iso⟩
  | succ n =>
    exfalso
    let I := ULift.{u} (Fin (n + 1))
    let idx : I := ⟨0⟩
    let H := Specs.Unipotent.closedSubgroupAlgebraicGroup T
    let j : MatrixRealization H :=
      ⟨i.size, i.ambient, i.matrix, T.inclusion ≫ i.embedding, by
        letI := T.isClosedImmersion
        letI := i.closed
        change IsClosedImmersion (T.inclusion.hom.hom.left ≫ i.embedding.hom.hom.left)
        infer_instance⟩
    let incl := FiniteAdelicMorphism.pointsMap T.inclusion j i F
    letI : CompactSpace (PointsIn j F) := by
      have hc : IsCompact (range (asMatrix i F)) :=
        isCompact_range (asMatrix_isClosedEmbedding i F).continuous
      refine ⟨IsCompact.of_isClosed_subset ((asMatrix_isClosedEmbedding j F).isCompact_preimage hc)
        isClosed_univ fun g _ => ⟨incl g, ?_⟩⟩
      simp only [asMatrix, j, incl, FiniteAdelicMorphism.pointsMap, Functor.map_comp,
        NatTrans.comp_app]
      rfl
    let A := CommAlgCat.of F (Specs.StandardGroups.LaurentPowerCoordinates F I)
    let E : (testSpec F).obj (Opposite.op A) ≅ H.val.X := (Grp.forget _).mapIso e.symm
    let x := Specs.StandardGroups.laurentVariable F I idx
    let coord (g : PointsIn j F) : F := (coordinateMap (g ≫ E.inv)).hom x
    have hcont : Continuous coord := by
      obtain ⟨a, ha, heval⟩ := matrixPresentation A E j
      obtain ⟨z, hz⟩ := ha x
      have hh : coord = fun g => glEvaluation (asMatrix j F g) z := by
        funext g
        have h := DFunLike.congr_fun (heval F g) z
        change _ = (coordinateMap (g ≫ E.inv)).hom (a.hom z) at h
        rw [hz] at h
        exact h.symm
      rw [hh]
      exact (continuous_glEvaluation z).comp continuous_induced_dom
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (isCompact_range hcont).isBounded
    obtain ⟨t, ht⟩ := hF
    have ht0 : t ≠ 0 := by
      intro he
      rw [he, norm_zero] at ht
      exact (not_lt_of_ge zero_le_one) ht
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C ht
    let a : I → Fˣ := fun _ => Units.mk0 t ht0 ^ m
    let f : Multiplicative (I → ℤ) →* F :=
      (Units.coeHom F).comp
      { toFun := fun z => a idx ^ (z.toAdd idx)
        map_one' := zpow_zero _
        map_mul' := fun z w => zpow_add _ _ _ }
    let φ : A ⟶ CommAlgCat.of F F := CommAlgCat.ofHom (AddMonoidAlgebra.lift F F (I → ℤ) f)
    let g : PointsIn j F := (testSpec F).map φ.op ≫ E.hom
    have hg : coord g = t ^ m := by
      have he : g ≫ E.inv = (testSpec F).map φ.op := by
        change ((testSpec F).map φ.op ≫ E.hom) ≫ E.inv = _
        simp
      change (coordinateMap (g ≫ E.inv)).hom x = _
      rw [he, coordinateMap_of_map]
      change AddMonoidAlgebra.lift F F (I → ℤ) f
        (AddMonoidAlgebra.single (Pi.single idx 1) 1) = t ^ m
      rw [AddMonoidAlgebra.lift_single, one_smul]
      change ((a idx ^ ((Pi.single idx 1 : I → ℤ) idx) : Fˣ) : F) = _
      simp [a]
    have hb := hC _ (mem_range_self g)
    rw [hg, norm_pow] at hb
    exact hm.not_ge hb

private theorem rankPositiveOfIsotropic {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (ha : ¬ IsAnisotropic G.val) :
    0 < Specs.RelativeRank.relativeRank G := by
  classical
  obtain ⟨S, hS⟩ := not_forall.mp ha
  obtain ⟨⟨r, ⟨e⟩⟩, hnt⟩ := not_imp.mp hS
  have hr : 0 < r := Nat.pos_of_ne_zero (fun hr => by
    subst r
    exact hnt ⟨e ≪≫ empty_power_iso⟩)
  have h := split_dimension_le_rank G S ⟨r, ⟨e⟩⟩
  rw [dimension_of_iso e, standard_torus_dimension] at h
  exact (show (0 : WithBot ℕ∞) < r by exact_mod_cast hr).trans_le h

open scoped NumberField
open Specs.PadicLogarithmChart (completionNormedField rationalPrime)

private theorem normedCompactnessCriterion {E F : Type*} [NontriviallyNormedField E]
    [NormedField F] [CharZero F] [NormedAlgebra E F] [ProperSpace F]
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G) (hG : IsSemisimple G) :
    CompactSpace (PointsIn i F) ↔ IsAnisotropic G.val := by
  refine ⟨anisotropicOfCompact ?_ G i, compactOfAnisotropic G i hG⟩
  obtain ⟨t, ht⟩ := NormedField.exists_one_lt_norm E
  exact ⟨algebraMap E F t, by simpa only [norm_algebraMap'] using ht⟩

theorem localFieldCompactness : LocalFieldCompactness.{u} := by
  intro F _ _ _
  exact normedCompactnessCriterion (E := F) (F := F)

theorem localCompactness : LocalCompactness.{u} := by
  intro K _ _ D hD w
  subst D
  cases w with
  | inl w =>
    obtain ⟨p, hp, hwp⟩ := PadicLogarithmChart.numberPlacePrime K w
    letI : Fact p.Prime := ⟨hp⟩
    letI : w.asIdeal.LiesOver (rationalPrime p).asIdeal := hwp
    let F := w.adicCompletion K
    letI : NormedField F := completionNormedField p w
    obtain ⟨a, ha⟩ := PadicLogarithmChart.numberCompletionPadic p K w
    letI : NormedAlgebra (Padic p) F := a
    letI : FiniteDimensional (Padic p) F := ha
    letI : ProperSpace F := FiniteDimensional.proper (Padic p) F
    letI : CharZero F := charZero_of_injective_algebraMap (algebraMap (Padic p) F).injective
    change ∀ (G : AffineAlgebraicGroup F) (i : MatrixRealization G),
      IsSemisimple G → (CompactSpace (PointsIn i F) ↔ IsAnisotropic G.val)
    exact normedCompactnessCriterion (E := Padic p) (F := F)
  | inr w =>
    obtain ⟨a, ha, _⟩ := ArchimedeanLieChart.completionRealStructures K w
    letI := a
    letI := ha
    letI : ProperSpace w.Completion := FiniteDimensional.proper ℝ w.Completion
    letI : CharZero w.Completion := charZero_of_injective_algebraMap
      (algebraMap ℝ w.Completion).injective
    change ∀ (G : AffineAlgebraicGroup w.Completion) (i : MatrixRealization G),
      IsSemisimple G → (CompactSpace (PointsIn i w.Completion) ↔ IsAnisotropic G.val)
    exact normedCompactnessCriterion (E := ℝ) (F := w.Completion)

open Specs.Unipotent (baseChangedAlgebraicGroup)
open private localPointSet_eq_image from LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence

private def singletonEvaluation {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G) (v : D.Place) :
    FinitePoints D i {v} ≃ₜ* LocalPoints D i v := by
  let k : ↥({v} : Finset D.Place) := ⟨v, Finset.mem_singleton_self _⟩
  letI : Unique ↥({v} : Finset D.Place) := ⟨⟨k⟩, fun a =>
    Subtype.ext (Finset.mem_singleton.mp a.property)⟩
  exact {
    toMulEquiv := MulEquiv.piUnique (fun a : ↥({v} : Finset D.Place) => LocalPoints D i a.val)
    continuous_toFun := continuous_apply k
    continuous_invFun := (Homeomorph.piUnique
      (fun a : ↥({v} : Finset D.Place) => LocalPoints D i a.val)).symm.continuous }

private theorem mapContracted {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (f : A →* B) (hf : Continuous f)
    {x : A} (hx : Contracted x) : Contracted (f x) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨f a, ?_⟩
  have h := (hf.tendsto (1 : A)).comp ha
  change Tendsto (fun n : ℕ => f (a ^ n * x * (a ^ n)⁻¹)) atTop (𝓝 (f 1)) at h
  simpa only [map_one, map_mul, map_pow, map_inv] using h

private theorem contractedParabolicRadical {F : Type u} {E : Type v} [Field F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] [NontriviallyNormedField E] [Algebra E F]
    (hEF : Continuous (algebraMap E F)) (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    {g : PointsIn i F} (hg : g ∈ parabolicRadicalPoints G) : Contracted g := by
  obtain ⟨P, hP, U, hU, hg⟩ := hg
  obtain ⟨c, D, _, _, hRad, hcon⟩ :=
    LocalCocharacterEvaluation.parabolicRadicalEvaluation.{u, v} G i P hP
  obtain ⟨e, he⟩ := hRad U hU
  obtain ⟨y, hy⟩ := hg
  have hg' : g ∈ ((((groupPointsFunctor F).map D.contracting.inclusion).app
      (CommAlgCat.of F F)).hom).range := by
    refine ⟨(((groupPointsFunctor F).map e.hom).app (CommAlgCat.of F F)).hom y, ?_⟩
    rw [← hy, ← he, Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := E)
  exact ⟨_, hcon hEF t ht g hg'⟩

private theorem numberFiniteRadicalContracted {K : Type u} [Field K] [NumberField K]
    (w : NumberFinitePlace K) (G : AffineAlgebraicGroup (w.adicCompletion K))
    (i : MatrixRealization G) {g : PointsIn i (w.adicCompletion K)}
    (hg : g ∈ parabolicRadicalPoints G) : Contracted g := by
  let F := w.adicCompletion K
  obtain ⟨p, hp, hwp⟩ := PadicLogarithmChart.numberPlacePrime K w
  letI : Fact p.Prime := ⟨hp⟩
  letI : w.asIdeal.LiesOver (rationalPrime p).asIdeal := hwp
  letI : NormedField F := completionNormedField p w
  obtain ⟨a, ha⟩ := PadicLogarithmChart.numberCompletionPadic p K w
  letI : NormedAlgebra (Padic p) F := a
  letI : FiniteDimensional (Padic p) F := ha
  have hEF : Continuous (algebraMap (Padic p) F) :=
    (Algebra.linearMap (Padic p) F).continuous_of_finiteDimensional
  exact contractedParabolicRadical (F := F) (E := Padic p) hEF G i hg

private theorem singletonInsertion {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G)
    (S : Finset D.Place) (v : Outside D S) (a : LocalPoints D i v.val) :
    insertFinite D i S {v.val} ((singletonEvaluation D i v.val).symm a) =
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.val) v a := by
  apply RestrictedProduct.ext
  intro k
  by_cases hk : k = v
  · subst k
    rw [insertFinite_apply, dite_eq_left (Finset.mem_singleton_self _), RestrictedProduct.mulSingle_eq_same]
    exact (singletonEvaluation D i v.val).apply_symm_apply a
  · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hk, insertFinite_apply]
    exact dite_eq_right (fun hm => hk (Subtype.ext (Finset.mem_singleton.mp hm)))

theorem isolateParabolicRadicals : IsolateParabolicRadicals.{u} := by
  classical
  intro K _ hn D hD G i hG han S hS hSn hArch
  subst D
  let D : GlobalFieldData.{u, u} K := .number hn
  intro w hw hnc T U hv A v
  let F := w.adicCompletion K
  letI : Algebra K F := completionAlgebra D (.inl w)
  let G₀ := baseChangedAlgebraicGroup F G
  let J : Finset D.Place := {Sum.inl w}
  have hJS : Disjoint J S := Finset.disjoint_left.mpr (by
    intro a ha hs
    have he : a = Sum.inl w := Finset.mem_singleton.mp ha
    exact hw (he ▸ hs))
  have hq := compactFullQuotient D rfl G i hG.1 han
  obtain ⟨hUc, hUo⟩ := compactOpenOutside D i T (fun a ha =>
    hArch a (fun hs => ha (Finset.mem_union_left J hs)))
  obtain ⟨_, j₀, _, e₀, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization G₀ := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i (.inl w) := e₀
  have hs₀ : IsSemisimple G₀ :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G
      hG.1.1 hG.1.2.1).mpr hG.1
  have han₀ : ¬ IsAnisotropic G₀.val := by
    intro han
    have hc : CompactSpace (PointsIn j F) :=
      (localCompactness D rfl (.inl w) G₀ j hs₀).mpr han
    letI := hc
    exact hnc ⟨(Function.Surjective.range_eq e.surjective) ▸ isCompact_range e.continuous⟩
  obtain ⟨H, hH, hOpen, hindex, hrad, _⟩ :=
    padicLatticeProjection G i D rfl w S T U Finset.subset_union_left hw hv hq hSn hUc hUo
      hG (rankPositiveOfIsotropic G₀ han₀)
  refine ⟨⟨H, hH, hOpen, hindex, hrad⟩, ?_⟩
  let σ := singletonEvaluation D i (Sum.inl w)
  let HJ := H.comap σ.toMonoidHom
  letI := hindex
  have hHJ : (HJ : Set (FinitePoints D i J)) =
      closure (projectedArithmetic D i S J U : Set (FinitePoints D i J)) := by
    change σ ⁻¹' (H : Set _) = _
    rw [hH]
    have hproj : (lattice D i T U).map (evaluatePlace D i hv) =
        (projectedArithmetic D i S J U).map σ.toMonoidHom := by
      rw [projectedArithmetic, Subgroup.map_map]
      rfl
    rw [hproj, Subgroup.coe_map]
    change σ ⁻¹' closure (σ.toHomeomorph '' (projectedArithmetic D i S J U : Set _)) = _
    rw [← σ.toHomeomorph.image_closure]
    exact σ.injective.preimage_image _
  let Z := diagonalClosedSubgroup D i S
  let emb := RestrictedProduct.mulSingleMonoidHom
    (fun k : Outside D S => localSubgroup D i k.val) v
  have hgen : A ≤ Z.comap emb := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    have hgH := hrad (Subgroup.subset_closure hg)
    have hcon : Contracted g := by
      change g ∈ localPointSet D i (Sum.inl w) (parabolicRadicalPoints G₀) at hg
      rw [localPointSet_eq_image D i (Sum.inl w) j e he] at hg
      obtain ⟨x, hx, rfl⟩ := hg
      have hx' : Contracted x := numberFiniteRadicalContracted w G₀ j hx
      exact mapContracted e.toMonoidHom e.continuous hx'
    let x : HJ := ⟨σ.symm g, by
      change σ (σ.symm g) ∈ H
      rw [σ.apply_symm_apply]
      exact hgH⟩
    have hx : Contracted (x : FinitePoints D i J) := by
      change Contracted (σ.symm g)
      exact mapContracted (A := LocalPoints D i (.inl w)) (B := FinitePoints D i J)
        σ.symm.toMonoidHom σ.symm.continuous hcon
    have hh := insertContracted D i S J hJS U hUc hUo HJ hHJ x hx
    change (emb g) ∈ (Z : Set _)
    rw [diagonalClosedSubgroup_coe D i S]
    change RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.val)
      v g ∈ diagonalClosure D i S
    rw [← singletonInsertion D i S v g]
    exact hh
  intro a ha
  have ha' := hgen ha
  change emb a ∈ (Z : Set _) at ha'
  rwa [diagonalClosedSubgroup_coe D i S] at ha'

/-- Full isolation at a cofinite set of finite places gives the restricted
product inclusion and reduces density to its finite complement. -/
private theorem reduceToRemainingPlaces {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G) (S : Finset D.Place)
    (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∈ S)
    (E : Set D.FinitePlace) (hE : Eᶜ.Finite)
    (hIso : ∀ (w : D.FinitePlace), w ∈ E → ∀ (hw : Sum.inl w ∉ S),
      ∀ a : LocalPoints D i (.inl w),
        RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.val)
          (⟨.inl w, hw⟩ : Outside D S) a ∈ diagonalClosure D i S) :
    ∃ J : Finset D.Place, Disjoint J S ∧
      (∀ w : D.FinitePlace, Sum.inl w ∈ J ↔ Sum.inl w ∉ S ∧ w ∉ E) ∧
      {x : Adeles D i S | ∀ w : Outside D S, w.val ∈ J → x w = 1} ⊆ diagonalClosure D i S ∧
      (DenseRange (rationalProjection D i J) ↔ StrongApproximation D i S) := by
  classical
  let J := (hE.toFinset.image (Sum.inl : D.FinitePlace → D.Place)).filter (· ∉ S)
  have hd : Disjoint J S := Finset.disjoint_left.mpr fun w hw hs =>
    (Finset.mem_filter.mp hw).2 hs
  have hmem (w : D.FinitePlace) : Sum.inl w ∈ J ↔ Sum.inl w ∉ S ∧ w ∉ E := by
    constructor
    · intro hw
      obtain ⟨hi, hs⟩ := Finset.mem_filter.mp hw
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hi
      exact ⟨hs, (Sum.inl.inj he) ▸ hE.mem_toFinset.mp hv⟩
    · rintro ⟨hs, he⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (hE.mem_toFinset.mpr he), hs⟩
  have hsingle : ∀ w : Outside D S, w.val ∉ J → ∀ a : LocalPoints D i w.val,
      RestrictedProduct.mulSingle (fun k : Outside D S => localSubgroup D i k.val) w a ∈
        diagonalClosure D i S := by
    rintro ⟨w | w, hw⟩ hwJ a
    · apply hIso w _ hw a
      by_contra hn
      exact hwJ ((hmem w).mpr ⟨hw, hn⟩)
    · exact (hw (hArch w)).elim
  refine ⟨J, hd, hmem, ?_, ((projectToRemainingPlaces D i S J hd).2 hsingle).2.2⟩
  let Z := diagonalClosedSubgroup D i S
  have hZ : (Z : Set (Adeles D i S)) = diagonalClosure D i S := diagonalClosedSubgroup_coe D i S
  rw [← hZ]
  apply Subset.trans _ (isolatedFactorsSpan D i S {w | w.val ∉ J} Z
    (by rw [hZ]; exact isClosed_closure) (fun w hw a => by
      change _ ∈ (Z : Set (Adeles D i S))
      rw [hZ]
      exact hsingle w hw a))
  intro x hx w hw
  exact fun hwJ => hw (hx w hwJ)

open private smooth_extend_iff from LinearAlgebraicGroups.RootData.BorelNormalizer
open private inclusion_mono from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem rationalBorelParabolic {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (hG : Specs.GeometricRadicals.IsReductive G)
    (B : Specs.ClosedSubgroup G.val) (hB : Specs.GeometricBorelConjugacy.IsKBorel B) :
    Specs.BorelProper.IsParabolic G B := by
  obtain ⟨hc, hb⟩ := hB
  exact ⟨hG, (smooth_extend_iff (AlgebraicClosure F) B.group.X).mp hb.1.1,
    hc, _, hb, ⟨𝟙 _, Category.id_comp _⟩⟩

/-- In a geometrically nontrivial semisimple group, a rational Borel is a
proper parabolic. Thus a quasi-split form has positive split rank. -/
private theorem rankPositiveOfQuasiSplit {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (hG : IsSemisimple G)
    (hnt : ¬ Nonempty ((Specs.GeometricRadicals.GeometricGroup G).val ≅
      Grp.trivial (SchemeOver (AlgebraicClosure F))))
    (hqs : Specs.GeometricBorelConjugacy.IsQuasiSplit G) :
    0 < Specs.RelativeRank.relativeRank G := by
  obtain ⟨hred, B, hB⟩ := hqs
  refine (Descent.RelativeRank.semisimpleParabolicCriterion G hG).mp
    ⟨B, rationalBorelParabolic G hred B hB, fun hIso => ?_⟩
  letI := hIso
  obtain ⟨hc, hb⟩ := hB
  let B₀ := Specs.GeometricRadicals.baseChangedSubgroup (AlgebraicClosure F) B hc
  let M := Specs.GeometricRadicals.geometricSolvableRadical G
  haveI : IsIso B₀.inclusion := Functor.map_isIso (groupBaseChange F (AlgebraicClosure F)) _
  have hNormal : Specs.IsNormalSubgroup B₀.inclusion := by
    refine ⟨Specs.subgroupConjugation B₀.inclusion ≫ (inv B₀.inclusion).hom.hom, ?_⟩
    change Specs.subgroupConjugation B₀.inclusion ≫ (Grp.forget _).map (inv B₀.inclusion) ≫
      (Grp.forget _).map B₀.inclusion = _
    rw [← Functor.map_comp, IsIso.inv_hom_id]
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  obtain ⟨j, hj⟩ := (LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G).2.2
    B₀ ⟨hb.1.1, hb.1.2.1, hNormal⟩ hb.1.2.2
  have hs : (inv B₀.inclusion ≫ j) ≫ M.inclusion = 𝟙 _ := by
    rw [Category.assoc, hj, IsIso.inv_hom_id]
  letI := inclusion_mono M
  haveI : IsSplitEpi M.inclusion := IsSplitEpi.mk' ⟨_, hs⟩
  letI : IsIso M.inclusion := isIso_of_mono_of_isSplitEpi _
  obtain ⟨e⟩ := hG.2.2
  exact hnt ⟨(asIso M.inclusion).symm ≪≫ e⟩

/-- Once the good factors are noncompact and generated by the rational
parabolic radicals, the local isolation theorem gives the finite remainder. -/
private theorem goodPlacesFromLocalGeneration (hisolate : IsolateParabolicRadicals.{u})
    {K : Type u} [Field K] [NumberField K] (D : GlobalFieldData.{u, u} K)
    (hD : D = .number inferInstance) (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : Specs.IsAbsolutelyAlmostSimple G) (han : IsAnisotropic G.val)
    (S : Finset D.Place) (hS : S.Nonempty) (hnc : ¬ CompactSpace (FinitePoints D i S))
    (hArch : ∀ w : D.InfinitePlace, Sum.inr w ∈ S) (E : Set D.FinitePlace) (hE : Eᶜ.Finite)
    (hLocal : ∀ w ∈ E, ¬ CompactSpace (LocalPoints D i (.inl w)) ∧
      Subgroup.closure (localPointSet D i (.inl w)
        (parabolicRadicalPoints (baseChangedAlgebraicGroup (D.Completion (.inl w)) G))) = ⊤) :
    ∃ J : Finset D.Place, Disjoint J S ∧
      (∀ w : D.FinitePlace, Sum.inl w ∈ J ↔ Sum.inl w ∉ S ∧ w ∉ E) ∧
      {x : Adeles D i S | ∀ w : Outside D S, w.val ∈ J → x w = 1} ⊆ diagonalClosure D i S ∧
      (DenseRange (rationalProjection D i J) ↔ StrongApproximation D i S) := by
  refine reduceToRemainingPlaces D i S hArch E hE (fun w hw hwS a => ?_)
  obtain ⟨hn, hg⟩ := hLocal w hw
  have h := hisolate D hD G i hG han S hS hnc (fun t ht => (ht (hArch t)).elim) w hwS hn
  exact h.2 a (hg.symm ▸ Subgroup.mem_top a)

section GoodPlaces

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 450000

open LinearAlgebraicGroups.Specs (ClosedSubgroup)
open Specs.GeometricBorelConjugacy (IsKBorel IsQuasiSplit)
open Specs.GeometricRadicals (GeometricGroup IsReductive)
open private trivial_baseChange_iff groupBaseChangeTower
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange

/-- A field extension cannot make a geometrically nontrivial affine group trivial. -/
private theorem geometricNontrivialAfterBaseChange
    {K F : Type u} [Field K] [Field F] [Algebra K F] (G : AffineAlgebraicGroup K)
    (hG : ¬ Nonempty ((GeometricGroup G).val ≅ Grp.trivial (SchemeOver (AlgebraicClosure K)))) :
    ¬ Nonempty ((GeometricGroup (baseChangedAlgebraicGroup F G)).val ≅
      Grp.trivial (SchemeOver (AlgebraicClosure F))) := by
  let C := AlgebraicClosure K
  let L := AlgebraicClosure F
  let f : C →ₐ[K] L := IsAlgClosed.lift
  letI : Algebra C L := f.toRingHom.toAlgebra
  letI : IsScalarTower K C L := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => (f.commutes a).symm)
  let e : (groupBaseChange C L).obj (GeometricGroup G).val ≅
      (GeometricGroup (baseChangedAlgebraicGroup F G)).val :=
    ((groupBaseChangeTower (k := K) (K := C) L).app G.val).symm ≪≫
      (groupBaseChangeTower (k := K) (K := F) L).app G.val
  rintro ⟨h⟩
  exact hG ((trivial_baseChange_iff (K := L) (GeometricGroup G).val).mp ⟨e ≪≫ h⟩)

open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.IntegralSemisimpleModel (fibre)
open private exists_split_maximalTorus_finiteGalois from LinearAlgebraicGroups.Arithmetic.CentralCover
open private referenceTarget geometricSimpleConnectednessOfForm from LinearAlgebraicGroups.Arithmetic.CentralCoverDescent
open private fibreTowerIso realization_corootSpan noCentralCovers_of_span centralIsogeny_postIso
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence

private theorem simplyConnectedAfterBaseChange
    {K F : Type u} [Field K] [Field F] [Algebra K F] (G : AffineAlgebraicGroup K)
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G) :
    GeometricallySimplyConnected (baseChangedAlgebraicGroup F G) := by
  obtain ⟨E, hE, hAlg, hFin, hGal, T, _, hs, hm⟩ := exists_split_maximalTorus_finiteGalois G hG
  letI := hE
  letI := hAlg
  letI := hFin
  letI := hGal
  obtain ⟨P, j, _, hP, _⟩ := referenceTarget G hG T hs hm
  have hscP : GeometricallySimplyConnected P.G := geometricSimpleConnectednessOfForm j hsc
  let D := Classification.Pinning.attachedDatum P
  letI := D.comm
  have hD : corootLattice D = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion P.G hP P.T P.split P.maximal D.datum).mp hscP
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨A, V, e, _, _, _⟩ := M.fieldFibre K
  obtain ⟨R, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A P
  let Pp : Specs.Pinning.PinnedGroup A := ⟨P, R, p⟩
  obtain ⟨b, _⟩ := pinnedLift V.pinned Pp V.attached D
    (Groupoid.inv (show D.toBased ⟶ V.attached.toBased from V.datumIso))
  let L := AlgebraicClosure F
  let t : E →ₐ[K] L := IsAlgClosed.lift
  letI : Algebra E L := t.toRingHom.toAlgebra
  letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun x => (t.commutes x).symm)
  let baseE := groupBaseChangeTower (k := K) (K := E) L
  let baseF := groupBaseChangeTower (k := K) (K := F) L
  obtain ⟨_, W, eL, _, _, _⟩ := M.fieldFibre L
  let c : (GeometricGroup (baseChangedAlgebraicGroup F G)).val ≅ W.pinned.pair.G.val :=
    (baseF.app G.val).symm ≪≫ baseE.app G.val ≪≫
      (groupBaseChange E L).mapIso j.symm ≪≫ (baseE.app P.G.val).symm ≪≫
      ((groupBaseChange K L).mapIso (e ≪≫ b.group)).symm ≪≫
      ((fibreTowerIso K L).app M.group).symm ≪≫ eL
  intro H hH f hf
  letI := noCentralCovers_of_span W.pinned.pair W.attached (realization_corootSpan W hD)
    H hH (f ≫ c.hom) (centralIsogeny_postIso c hf)
  exact IsIso.of_isIso_comp_right f c.hom

/-- A nonzero denominator in a number field's integers becomes a unit in all
but finitely many of its completed valuation rings. -/
private theorem finiteNonunitDenominator {K : Type u} [Field K] [NumberField K]
    (d : 𝓞 K) (hd : d ≠ 0) :
    {w : NumberFinitePlace K |
      ¬ IsUnit (algebraMap (𝓞 K) (w.adicCompletionIntegers K) d)}.Finite := by
  have hdK : algebraMap (𝓞 K) K d ≠ 0 :=
    fun h => hd ((IsFractionRing.injective (𝓞 K) K) (h.trans (map_zero _).symm))
  refine (number_nonintegral_finite (algebraMap (𝓞 K) K d)⁻¹).subset ?_
  intro w hw hx
  let F := w.adicCompletion K
  let R := w.adicCompletionIntegers K
  let y : R := ⟨algebraMap K F (algebraMap (𝓞 K) K d)⁻¹, hx⟩
  apply hw
  refine IsUnit.of_mul_eq_one y ?_
  apply Subtype.ext
  change algebraMap (𝓞 K) F d * algebraMap K F (algebraMap (𝓞 K) K d)⁻¹ = 1
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K F, ← map_mul, mul_inv_cancel₀ hdK, map_one]

private theorem liftPointOfSmoothAffine
    {R A : Type u} [CommRing R] [CommRing A]
    (I : Ideal R) [IsAdicComplete I R]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (R ⧸ I)) ⟶ Spec (CommRingCat.of A))
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A), s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ s = x := by
  let p := Spec.preimage f
  let q := Spec.preimage x
  letI : Algebra R A := p.hom.toAlgebra
  have hSmooth : p.hom.Smooth := (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    (Spec.map_preimage f ▸ (inferInstance : Smooth f))
  letI : Algebra.Smooth R A := RingHom.smooth_algebraMap.mp hSmooth
  have hpq : p ≫ q = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, hx]
  let x' : A →ₐ[R] R ⧸ I :=
    { toRingHom := q.hom
      commutes' := fun r => congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of (R ⧸ I) =>
        h.hom r) hpq }
  obtain ⟨s, hs⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete x'
  use Spec.map (CommRingCat.ofHom s.toRingHom)
  constructor
  · rw [← Spec.map_preimage f, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact s.commutes r
  · rw [← Spec.map_preimage x, ← Spec.map_comp]
    congr 1
    ext a
    exact congrArg (fun t : A →ₐ[R] R ⧸ I => t a) hs

/-- A residue-field point on a smooth scheme over an adically complete local
ring lifts to a section. Choose an affine chart at the residue point and use
formal smoothness of its coordinate algebra. -/
private theorem liftPointOfSmooth
    {R : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ s = x := by
  let k := IsLocalRing.ResidueField R
  let x₀ := IsLocalRing.closedPoint k
  obtain ⟨U, hU, hx₀, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x x₀) (by simp)
  let j := hU.fromSpec
  have hrange : Set.range x ⊆ Set.range j := by
    rw [hU.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    have h : a = x₀ := Subsingleton.elim _ _
    rw [h]
    exact hx₀
  let x' := IsOpenImmersion.lift j x hrange
  have hx' : x' ≫ j = x := IsOpenImmersion.lift_fac j x hrange
  have hh : x' ≫ (j ≫ f) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal R))) := by
    rw [← Category.assoc, hx']
    exact hx
  letI : Smooth (j ≫ f) := inferInstance
  obtain ⟨s, hs, hsx⟩ := liftPointOfSmoothAffine (IsLocalRing.maximalIdeal R) (j ≫ f) x' hh
  refine ⟨s ≫ j, ?_, ?_⟩
  · rw [Category.assoc, hs]
  · rw [← Category.assoc]
    exact (congrArg (· ≫ j) hsx).trans hx'

/-- A smooth scheme over the valuation ring that parametrizes actual Borels
on the two field fibres gives quasi-splitness of its generic-fibre group. -/
private theorem quasiSplitOfSmoothBorelScheme
    {R F : Type u} [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Finite (IsLocalRing.ResidueField R)] [Field F] [Algebra R F]
    (G₀ : AffineAlgebraicGroup (IsLocalRing.ResidueField R)) (hG₀ : IsReductive G₀)
    (G : AffineAlgebraicGroup F) (hG : IsReductive G)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (residuePointOfBorel :
      {B : ClosedSubgroup G₀.val // IsKBorel B} →
      {x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X //
        x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))})
    (genericBorelOfPoint :
      {x : Spec (CommRingCat.of F) ⟶ X //
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R F))} →
        {B : ClosedSubgroup G.val // IsKBorel B}) :
    IsQuasiSplit G := by
  letI := Fintype.ofFinite (IsLocalRing.ResidueField R)
  obtain ⟨_, B₀, hB₀⟩ := Descent.FiniteFieldFlags.reductiveQuasiSplit G₀ hG₀
  let x := residuePointOfBorel ⟨B₀, hB₀⟩
  obtain ⟨s, hs, _⟩ := liftPointOfSmooth f x.val x.property
  let j := Spec.map (CommRingCat.ofHom (algebraMap R F))
  let B := genericBorelOfPoint ⟨j ≫ s, by rw [Category.assoc, hs, Category.comp_id]⟩
  exact ⟨hG, B.val, B.property⟩

open scoped ValuativeRel

private theorem numberCompletionIntegers_isAdicComplete
    {K : Type u} [Field K] [NumberField K] (w : NumberFinitePlace K) :
    IsAdicComplete (IsLocalRing.maximalIdeal (w.adicCompletionIntegers K))
      (w.adicCompletionIntegers K) := by
  let F := w.adicCompletion K
  letI : IsNonarchimedeanLocalField F := numberFiniteCompletion_isLocalField w
  have hR := GlobalFieldData.integers_eq_valuationSubring (GlobalFieldData.number.{u, u} inferInstance) w
  change w.adicCompletionIntegers K = (ValuativeRel.valuation F).valuationSubring at hR
  let P (R : ValuationSubring F) := IsAdicComplete (IsLocalRing.maximalIdeal R) R
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have h : P (ValuativeRel.valuation F).valuationSubring := by
    dsimp only [P]
    exact inferInstanceAs (IsAdicComplete 𝓂[F] 𝒪[F])
  exact hR.symm ▸ h

open CategoryTheory.Limits
open scoped TensorProduct

open Specs.Pinning (BasedRootDatum)
open Specs.ReductiveModelSpreading (SplitModel)
open private FullCorootRank fullCorootRank_iff semisimple_iff_fullCorootRank
  from LinearAlgebraicGroups.Arithmetic.ReductiveModelSpreading
open private semisimple_of_iso from LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel

/-- Full coroot rank implies that the rational cocharacters annihilated by
all the roots are zero. -/
private theorem rootAnnihilatorOfFullCorootRank (D : BasedRootDatum.{u})
    (hD : FullCorootRank D) : RootData.rationalRootAnnihilator D.datum = ⊥ := by
  classical
  letI := D.freeX
  letI := D.freeY
  letI := D.finiteX
  letI := D.finiteY
  letI := D.finiteRoots
  letI := D.reduced
  let N := Submodule.span ℤ (D.datum.coroot '' D.base.support)
  have hN : Module.finrank ℤ N = Module.finrank ℤ D.Y := by
    change Module.finrank ℤ (Submodule.span ℤ (D.datum.coroot '' (D.base.support : Set D.I))) =
      Module.finrank ℤ D.Y
    rw [D.base.span_int_coroot_support]
    exact hD
  have hr : Module.finrank ℚ (N.baseChange ℚ) = Module.finrank ℚ (ℚ ⊗[ℤ] D.Y) := by
    rw [← (Submodule.toBaseChange.toLinearEquiv ℚ N).finrank_eq,
      Module.finrank_baseChange, Module.finrank_baseChange, hN]
  have hspan : RootData.rationalSimpleCorootSpan D.datum D.base = N.baseChange ℚ := by
    change RootData.rationalSimpleCorootSpan D.datum D.base =
      (Submodule.span ℤ (D.datum.coroot '' (D.base.support : Set D.I))).baseChange ℚ
    rw [Submodule.baseChange_span, Set.image_image, RootData.rationalSimpleCorootSpan]
    congr 1
    exact (Set.image_eq_range (fun i : D.I => (1 : ℚ) ⊗ₜ[ℤ] D.datum.coroot i)
      (D.base.support : Set D.I)).symm
  have htop := Submodule.eq_top_of_finrank_eq hr
  simpa [hspan, htop] using (RootData.rationalComplement D.datum D.base).2.disjoint

/-- A split integral model with semisimple field fibres has full rational
coroot span in the marked datum of the integral model. -/
private theorem rootAnnihilatorOfSplitModel (M : SplitModel.{u}) (k : Type u) [Field k] :
    RootData.rationalRootAnnihilator M.datum.datum = ⊥ := by
  obtain ⟨_, V, e, _, _, _, _, _, _⟩ := M.model.fieldFibre k
  obtain ⟨H, hH, ⟨j⟩⟩ := M.semisimple k
  have hV : IsSemisimple V.pinned.pair.G :=
    semisimple_of_iso (j.symm ≪≫ e) hH V.pinned.pair.reductive.1 V.pinned.pair.reductive.2.1
  exact rootAnnihilatorOfFullCorootRank M.datum
    ((fullCorootRank_iff V.datumIso).mpr ((semisimple_iff_fullCorootRank V.attached).mp hV))

open Specs.ReductiveModelSpreading (ReductiveModel scalarExtension)
open Specs.SmoothBorelParameter (Presentation affineFibre residueSpecMap
  algebraSpecMap ringSpec HasSplitModel)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private reductive_of_groupIso fieldFibres_of_split
  from LinearAlgebraicGroups.Arithmetic.ReductiveModelSpreading
open private transportSubgroup from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private pushKBorel from LinearAlgebraicGroups.Classification.PinnedEquivalence

/-- The residue Borel yields a point of the smooth parameter scheme.
A lift of that point gives a Borel in the generic fibre. -/
private theorem quasiSplitOfBorelPresentation
    {R F : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
    [Field F] [Algebra R F] {X : Grp (Over (ringSpec R))}
    [IsAffineHom X.X.hom] [LocallyOfFinitePresentation X.X.hom] [QuasiCompact X.X.hom]
    (P : Presentation X)
    (h₀ : IsReductive (affineFibre (G := X) (residueSpecMap R)))
    (h₁ : IsReductive (affineFibre (G := X) (algebraSpecMap R F))) :
    IsQuasiSplit (affineFibre (G := X) (algebraSpecMap R F)) := by
  letI := P.smooth
  refine quasiSplitOfSmoothBorelScheme _ h₀ _ h₁ P.scheme.hom ?_ ?_
  · intro B
    let r := residueSpecMap R
    have h := (SmoothBorelParameter.fieldComparison P (IsLocalRing.ResidueField R) r).2
      B.val B.property
    let x := h.exists.choose
    exact ⟨x.left, Over.w x⟩
  · intro x
    let y : Over.mk (algebraSpecMap R F) ⟶ P.scheme := Over.homMk x.val x.property
    exact ⟨(P.universal.pullback y).fieldSubgroup,
      (SmoothBorelParameter.fieldComparison P F (algebraSpecMap R F)).1 y⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quasiSplitOfCompletedReductiveModel
    {K : Type u} [Field K] [NumberField K] {G : AffineAlgebraicGroup K}
    {d : 𝓞 K} [Algebra (Localization.Away d) K]
    [IsScalarTower (𝓞 K) (Localization.Away d) K]
    (M : ReductiveModel G (R := Localization.Away d))
    (hD : RootData.rationalRootAnnihilator M.split.datum.datum = ⊥)
    (w : NumberFinitePlace K) (hw : IsUnit (algebraMap (𝓞 K) (w.adicCompletionIntegers K) d)) :
    IsQuasiSplit (baseChangedAlgebraicGroup (w.adicCompletion K) G) := by
  let R := Localization.Away d
  let O := w.adicCompletionIntegers K
  let F := w.adicCompletion K
  obtain ⟨a, _, ⟨e⟩, hFin, hFlat, hEt, ⟨j⟩⟩ :=
    ReductiveModelSpreading.completedBaseChange K G d M w hw
  letI := a
  letI := M.coverRing
  letI := M.coverAlgebra
  let A := O ⊗[R] M.cover
  letI : Module.FaithfullyFlat O A := hFlat
  let X := (scalarExtension R O).obj M.group
  let p := algebraSpecMap R O
  letI : IsAffine M.group.X.left := M.affine
  letI : IsAffineHom M.group.X.hom := isAffineHom_of_isAffine _
  letI : LocallyOfFinitePresentation M.group.X.hom := M.finitePresentation
  letI : QuasiCompact M.group.X.hom := M.quasiCompact
  letI : Smooth M.group.X.hom := M.smooth
  letI : IsAffineHom X.X.hom := inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom p))
  letI : LocallyOfFinitePresentation X.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd M.group.X.hom p))
  letI : QuasiCompact X.X.hom := inferInstanceAs (QuasiCompact (pullback.snd M.group.X.hom p))
  have hs : Smooth X.X.hom := inferInstanceAs (Smooth (pullback.snd M.group.X.hom p))
  letI : IsAdicComplete (IsLocalRing.maximalIdeal O) O := numberCompletionIntegers_isAdicComplete w
  let k := IsLocalRing.ResidueField O
  letI : Finite k :=
    (GlobalFieldData.integers_properties (GlobalFieldData.number.{u, u} inferInstance) w).2.2
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let B := affineFibre (G := X) (residueSpecMap O)
  let H := affineFibre (G := X) (algebraSpecMap O F)
  have hB : IsReductive B := fieldFibres_of_split M.split j k B (Iso.refl _)
  have hH : IsReductive H := fieldFibres_of_split M.split j F H (Iso.refl _)
  have hSplit : HasSplitModel X := ⟨A, inferInstance, inferInstance,
    hFin, hFlat, hEt, M.split.datum, hD, M.split.model, ⟨j⟩⟩
  obtain ⟨P⟩ := SmoothBorelParameter.smoothBorelParameter O F X hs hB hH hSplit
  obtain ⟨_, C, hC⟩ := quasiSplitOfBorelPresentation P hB hH
  let H' := baseChangedAlgebraicGroup F G
  let e' : H.val ≅ H'.val := e
  exact ⟨reductive_of_groupIso e'.symm hH, transportSubgroup e' C, pushKBorel e' hC⟩

/-- A semisimple group over a number field is quasi-split at every finite
place where the denominator of its reductive model remains a unit. -/
theorem quasiSplitAtAlmostAllFinitePlaces : QuasiSplitAtAlmostAllFinitePlaces.{u} := by
  intro K _ _ D hD G hG
  subst D
  obtain ⟨d, hd, a, ha, ⟨M⟩⟩ := ReductiveModelSpreading.reductiveModelSpreading K G hG
  letI := a
  letI := ha
  have hAnn := rootAnnihilatorOfSplitModel M.split K
  refine (finiteNonunitDenominator d hd).subset ?_
  intro w hw hunit
  exact hw (quasiSplitOfCompletedReductiveModel M hAnn w hunit)

open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.QuasiSplitLocalGeneration (IsLocalField generatedByBorelRadicals)
open Specs.QuasiSplitPinnedPairModel (BorelPair)

/-- Both specified Borel radicals already occur among the rational parabolic radicals. -/
private theorem parabolicGenerationOfBorelGeneration {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (M : BorelPair G)
    (hp : Specs.BorelProper.IsParabolic G M.positive)
    (hm : Specs.BorelProper.IsParabolic G M.negative)
    (hgen : generatedByBorelRadicals M = ⊤) :
    Subgroup.closure (parabolicRadicalPoints G) = ⊤ := by
  apply top_le_iff.mp
  rw [← hgen]
  exact sup_le
    (fun _ hx => Subgroup.subset_closure
      ⟨M.positive, hp, M.positiveRadical, M.positiveUnipotentRadical, hx⟩)
    (fun _ hx => Subgroup.subset_closure
      ⟨M.negative, hm, M.negativeRadical, M.negativeUnipotentRadical, hx⟩)

private theorem relativeRank_le_zero_of_anisotropic {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (hG : IsAnisotropic G.val) :
    Specs.RelativeRank.relativeRank G ≤ 0 := by
  unfold Specs.RelativeRank.relativeRank
  apply iSup_le
  intro T
  obtain ⟨e⟩ := hG T.val T.property
  rw [dimension_of_iso e, ← dimension_of_iso (empty_power_iso (k := F)), standard_torus_dimension]
  simp

private theorem localPropertiesOfQuasiSplit (hcompact : LocalCompactness.{u})
    {K : Type u} [Field K] [NumberField K]
    (D : GlobalFieldData.{u, u} K) (hD : D = .number inferInstance)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G)
    (hG : Specs.IsAbsolutelyAlmostSimple G) (w : D.FinitePlace)
    (hqs : IsQuasiSplit (baseChangedAlgebraicGroup (D.Completion (.inl w)) G)) :
    ¬ IsAnisotropic (baseChangedAlgebraicGroup (D.Completion (.inl w)) G).val ∧
      ¬ CompactSpace (LocalPoints D i (.inl w)) := by
  let F := D.Completion (.inl w)
  let G₀ := baseChangedAlgebraicGroup F G
  have hs := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G hG.1.1 hG.1.2.1).mpr hG.1
  have hnt := geometricNontrivialAfterBaseChange (F := F) G hG.2.1
  have hr := rankPositiveOfQuasiSplit G₀ hs hnt hqs
  have ha : ¬ IsAnisotropic G₀.val := fun han => hr.not_ge (relativeRank_le_zero_of_anisotropic G₀ han)
  refine ⟨ha, ?_⟩
  obtain ⟨_, j, _, e, _, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  intro c
  letI := c
  have c' : CompactSpace (PointsIn j F) :=
    ⟨e.symm.surjective.range_eq ▸ isCompact_range e.symm.continuous⟩
  exact ha ((hcompact D hD (.inl w) G₀ j hs).mp c')

private theorem localPointSet_generates_of_parabolicRadicals {K : Type u} [Field K]
    (D : GlobalFieldData.{u, u} K) {G : AffineAlgebraicGroup K} (i : MatrixRealization G)
    (w : D.Place) (hgen : Subgroup.closure
      (parabolicRadicalPoints (baseChangedAlgebraicGroup (D.Completion w) G)) = ⊤) :
    Subgroup.closure (localPointSet D i w
      (parabolicRadicalPoints (baseChangedAlgebraicGroup (D.Completion w) G))) = ⊤ := by
  let F := D.Completion w
  let G₀ := baseChangedAlgebraicGroup F G
  obtain ⟨_, j₀, _, e₀, he, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization G₀ := j₀
  let e : PointsIn j F ≃ₜ* LocalPoints D i w := e₀
  have heq := localPointSet_eq_image D i w j e he (parabolicRadicalPoints G₀)
  rw [heq]
  let A : Set (PointsIn j F) := parabolicRadicalPoints G₀
  have hA : Subgroup.closure A = ⊤ := hgen
  calc
    Subgroup.closure (e '' A) = (Subgroup.closure A).map e.toMonoidHom :=
      (MonoidHom.map_closure e.toMonoidHom A).symm
    _ = (⊤ : Subgroup (PointsIn j F)).map e.toMonoidHom :=
      congrArg (Subgroup.map e.toMonoidHom) hA
    _ = ⊤ := Subgroup.map_top_of_surjective e.toMonoidHom e.surjective

private theorem borelRadicalExists {F : Type u} [Field F]
    (G : AffineAlgebraicGroup F) (hG : IsReductive G) (B : ClosedSubgroup G.val)
    (hB : IsKBorel B) :
    ∃ U : ClosedSubgroup B.group, IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U := by
  obtain ⟨_, _, _, U, _, _, _, _, _, _, _, _, _, _, hU, _⟩ :=
    LinearAlgebraicGroups.Relative.Parabolics.rationalParabolics.1 G B
      (rationalBorelParabolic G hG B hB)
  exact ⟨U, hU⟩

/-- Pass from cofinite quasi-splitness to full-factor isolation once the
local generation theorem and existence of opposite rational Borels are available. -/
private theorem goodPlacesOfQuasiSplit
    (hcompact : LocalCompactness.{u}) (hisolate : IsolateParabolicRadicals.{u})
    (hcofinite : QuasiSplitAtAlmostAllFinitePlaces.{u})
    (hgen : Specs.QuasiSplitLocalGeneration.Statement.{u})
    (hpair : ∀ {F : Type u} [Field F] [CharZero F] (G : AffineAlgebraicGroup F),
      IsQuasiSplit G → Nonempty (BorelPair G)) :
    GoodPlacesReduction.{u} := by
  intro K _ _ D hD G i hG han hsc S hS hnc hArch
  let E : Set D.FinitePlace :=
    {w | IsQuasiSplit (baseChangedAlgebraicGroup (D.Completion (.inl w)) G)}
  have hE : Eᶜ.Finite := hcofinite D hD G hG.1
  refine ⟨fun w _ hqs => (localPropertiesOfQuasiSplit hcompact D hD G i hG w hqs).1, ?_⟩
  refine goodPlacesFromLocalGeneration hisolate D hD G i hG han S hS hnc hArch E hE
    (fun w hqs => ⟨(localPropertiesOfQuasiSplit hcompact D hD G i hG w hqs).2, ?_⟩)
  let F := D.Completion (.inl w)
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let G₀ := baseChangedAlgebraicGroup F G
  have hs := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G hG.1.1 hG.1.2.1).mpr hG.1
  have hsc₀ := simplyConnectedAfterBaseChange (F := F) G hG.1 hsc
  obtain ⟨M⟩ := hpair G₀ hqs
  have hF : IsLocalField F := Or.inl
    ⟨inferInstanceAs (ValuativeRel (D.FiniteCompletion w)), inferInstance,
      GlobalFieldData.finiteCompletion_isLocalField D w⟩
  exact localPointSet_generates_of_parabolicRadicals D i (.inl w)
    (parabolicGenerationOfBorelGeneration G₀ M
      (rationalBorelParabolic G₀ hqs.1 M.positive M.positiveBorel)
      (rationalBorelParabolic G₀ hqs.1 M.negative M.negativeBorel)
      (hgen hF G₀ hs hsc₀ M))

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open private sections_of_subgroup from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

/-- The two inclusions of the common torus give the intersection on all test schemes. -/
private theorem schemeIntersectionOfPullback {F : Type u} [Field F] {G : GroupScheme F}
    {B C T : ClosedSubgroup G} {i : T.group ⟶ B.group} {j : T.group ⟶ C.group}
    (hi : i ≫ B.inclusion = T.inclusion) (hj : j ≫ C.inclusion = T.inclusion)
    (h : IsPullback i.hom.hom j.hom.hom B.inclusion.hom.hom C.inclusion.hom.hom) :
    IsSchemeIntersection {B, C} T := by
  intro Y y
  constructor
  · intro hy H hH
    rcases Set.mem_insert_iff.mp hH with rfl | hH
    · exact sections_of_subgroup ⟨i, hi⟩ hy
    · obtain rfl := Set.mem_singleton_iff.mp hH
      exact sections_of_subgroup ⟨j, hj⟩ hy
  · intro hy
    have hb := hy B (by simp)
    have hc := hy C (by simp)
    change (∃ b : Y ⟶ B.group.X, b ≫ B.inclusion.hom.hom = y) at hb
    change (∃ c : Y ⟶ C.group.X, c ≫ C.inclusion.hom.hom = y) at hc
    obtain ⟨b, hb⟩ := hb
    obtain ⟨c, hc⟩ := hc
    let t := h.lift b c (hb.trans hc.symm)
    have htb : t ≫ i.hom.hom = b := h.lift_fst _ _ _
    change ∃ r : Y ⟶ T.group.X, r ≫ T.inclusion.hom.hom = y
    refine ⟨t, ?_⟩
    have hi' : i.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
      (Grp.forget _).congr_map hi
    rw [← hi', ← Category.assoc, htb, hb]

private theorem borelPairOfQuasiSplit {F : Type u} [Field F] [CharZero F]
    (G : AffineAlgebraicGroup F) (hG : IsQuasiSplit G) : Nonempty (BorelPair G) := by
  obtain ⟨hr, B, hB⟩ := hG
  obtain ⟨C, T, _, hC, hT, hmax, i, j, hi, hj, hp⟩ :=
    Reductive.RationalOppositeBorels.rationalOppositeBorelsExist G hr B hB
  obtain ⟨U, hU⟩ := borelRadicalExists G hr B hB
  obtain ⟨V, hV⟩ := borelRadicalExists G hr C hC
  exact ⟨⟨B, C, T, U, V, hB, hC, hT.1, hmax, schemeIntersectionOfPullback hi hj hp, hU, hV⟩⟩

/-- Full isolation at the good finite places leaves a finite product on
which weak approximation is equivalent to strong approximation away from S. -/
theorem goodPlacesReduction : GoodPlacesReduction.{u} :=
  goodPlacesOfQuasiSplit localCompactness isolateParabolicRadicals quasiSplitAtAlmostAllFinitePlaces
    QuasiSplitLocalGeneration.quasiSplitLocalGeneration borelPairOfQuasiSplit

end GoodPlaces

end LinearAlgebraicGroups.Arithmetic.LocalCompactnessCriterion
