import Specs.LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing
import LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import LinearAlgebraicGroups.Arithmetic.LocalMixingExceptionalRootData
import LinearAlgebraicGroups.Arithmetic.LocalMixingHermitianRankOne
import LinearAlgebraicGroups.Arithmetic.LocalMixingHighestRootSL2
import LinearAlgebraicGroups.Arithmetic.LocalMixingQuadraticSpinRankOne
import LinearAlgebraicGroups.Arithmetic.LocalMixingQuaternionSpinRankOne
import LinearAlgebraicGroups.Arithmetic.LocalMixingSingletonRootSL2
import LinearAlgebraicGroups.Arithmetic.LocalMixingTrialitarianRootData
import LinearAlgebraicGroups.Arithmetic.QuasiSplitRadicalGeneration
import LinearAlgebraicGroups.Arithmetic.SplitLocalGeneration
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

import LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRadicalGeneration
open Filter Matrix MeasureTheory Set
open scoped ContinuousLinearMapWOT
open scoped InnerProductSpace Matrix Topology

universe u v

namespace LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing

open LinearAlgebraicGroups.Specs.Arithmetic.LocalQuotientMixing
open LinearAlgebraicGroups.Specs.ExceptionalLocalRadicalGeneration
  (ExceptionalRootSystemsAndLevis LocalRadicalGeneration)
open LinearAlgebraicGroups.Specs.UnitaryRankOne (splitUpper splitLower)

section RankOne

variable {F : Type u} [Field F]

private theorem upper_matrix (x : F) :
    (splitUpper x).val = !![1, x; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitUpper, SpecialLinearGroup.transvection_coe]

private theorem lower_matrix (x : F) :
    (splitLower x).val = !![1, 0; x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [splitLower, SpecialLinearGroup.transvection_coe]

/-- A determinant-one matrix on the curve with fixed diagonal and with
vanishing upper-right entry. -/
private def lowerTriangular (t : Fˣ) (s : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(t : F), 0; s, (↑t⁻¹ : F)], by simp [Matrix.det_fin_two_of]⟩

private theorem lowerTriangular_word (t : Fˣ) (s : F) (hs : s ≠ 0) :
    splitUpper (((t : F) - 1) / s) * splitLower s *
      splitUpper (-((t : F) - 1) / (s * t)) = lowerTriangular t s := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, upper_matrix, lower_matrix, Matrix.mul_fin_two,
    mul_zero, add_zero, zero_add, one_mul, mul_one, lowerTriangular,
    Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hs, Units.ne_zero t] <;> ring

/-- Conjugation by the inverse diagonal contracts the lower root when the
diagonal parameter tends to zero. -/
private theorem lower_conjugation (t : Fˣ) (x : F) :
    lowerTriangular t⁻¹ 0 * splitLower x * lowerTriangular t 0 =
      splitLower ((t : F) ^ 2 * x) := by
  apply Subtype.ext
  change (lowerTriangular t⁻¹ 0).val * (splitLower x).val * (lowerTriangular t 0).val =
    (splitLower ((t : F) ^ 2 * x)).val
  simp [lower_matrix, lowerTriangular, Units.val_inv_eq_inv_val, Units.ne_zero t,
    pow_two, mul_left_comm, mul_comm]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem tendsto_valuation_lt_one {t : F} (ht : ValuativeRel.valuation F t < 1) :
    Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := ValuativeRel.isRankLeOne_iff_mulArchimedean.mp
    (inferInstance : ValuativeRel.IsRankLeOne F)
  exact Valued.tendsto_zero_pow_of_v_lt_one (Γ₀ := ValuativeRel.ValueGroupWithZero F) ht

private theorem exists_contractingUnit :
    ∃ t : Fˣ, Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0) := by
  obtain ⟨t, ht, hlt⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation F)
  exact ⟨Units.mk0 t ht, tendsto_valuation_lt_one hlt⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem continuous_lowerTriangular (t : Fˣ) :
    Continuous (lowerTriangular t) := by
  apply Continuous.subtype_mk
  exact continuous_matrix fun i j => by fin_cases i <;> fin_cases j <;>
    first | exact continuous_const | exact continuous_id

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem continuous_splitLower : Continuous (splitLower (R := F)) := by
  apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
  change Continuous (fun x : F => (splitLower x).val)
  simp only [lower_matrix]
  exact continuous_matrix fun i j => by fin_cases i <;> fin_cases j <;>
    first | exact continuous_const | exact continuous_id

end RankOne

private theorem apply_mul {A : Type*} [Group A] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →* (V ≃ₗᵢ[ℂ] V)) (a b : A) (x : V) :
    ρ (a * b) x = ρ a (ρ b x) := by
  rw [map_mul]
  rfl

private theorem apply_one {A : Type*} [Group A] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : A →* (V ≃ₗᵢ[ℂ] V)) (x : V) : ρ 1 x = x := by
  rw [map_one]
  rfl

/-- The upper-root fixed-vector implication for the split rank-one group. -/
theorem upperRootFixedVector_conditional
    (_ : ExceptionalRootSystemsAndLevis.{u}) (_ : LocalRadicalGeneration.{u}) :
    UpperRootFixedVector.{u, v} := by
  intro F _ _ _ _ V _ _ ρ hρ w hw
  obtain ⟨p, hp⟩ := exists_contractingUnit (F := F)
  have hdiag (t : Fˣ) : ρ (lowerTriangular t 0) w = w := by
    let f : ℕ → ℂ := fun n => ⟪w, ρ (lowerTriangular t ((p : F) ^ n)) w⟫_ℂ
    have hlim : Tendsto f atTop (𝓝 ⟪w, ρ (lowerTriangular t 0) w⟫_ℂ) :=
      ((continuous_const.inner ((hρ w).comp (continuous_lowerTriangular t))).tendsto 0).comp hp
    have heq (n : ℕ) :
        f n = ⟪w, ρ (splitLower ((p : F) ^ n)) w⟫_ℂ := by
      dsimp only [f]
      rw [← lowerTriangular_word t _ (pow_ne_zero _ (Units.ne_zero p))]
      simp only [apply_mul, hw]
      let U := ρ (splitUpper (((t : F) - 1) / (p : F) ^ n))
      change ⟪w, U (ρ (splitLower ((p : F) ^ n)) w)⟫_ℂ = _
      calc
        _ = ⟪U w, U (ρ (splitLower ((p : F) ^ n)) w)⟫_ℂ := by rw [show U w = w from hw _]
        _ = _ := U.inner_map_map _ _
    have hzero : splitLower (0 : F) = 1 := SpecialLinearGroup.transvection_coeff_zero _
    have hlim' : Tendsto f atTop (𝓝 ⟪w, w⟫_ℂ) := by
      refine Tendsto.congr (fun n => (heq n).symm) ?_
      have hcont : Continuous (fun z : F => ⟪w, ρ (splitLower z) w⟫_ℂ) :=
        continuous_const.inner ((hρ w).comp continuous_splitLower)
      convert (hcont.tendsto 0).comp hp using 1 <;> first | rfl | rw [hzero, apply_one]
    have hinner := tendsto_nhds_unique hlim hlim'
    symm
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hs := norm_sub_sq (𝕜 := ℂ) w (ρ (lowerTriangular t 0) w)
    rw [hinner, inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map] at hs
    nlinarith
  have hlower (x : F) : ρ (splitLower x) w = w := by
    let f : ℕ → ℝ := fun n => ‖ρ (splitLower ((((p : F) ^ n) ^ 2) * x)) w - w‖
    have hpar : Tendsto (fun n : ℕ => ((p : F) ^ n) ^ 2 * x) atTop (𝓝 0) := by
      simpa using (hp.pow 2).mul_const x
    have hzero : splitLower (0 : F) = 1 := SpecialLinearGroup.transvection_coeff_zero _
    have hlim : Tendsto f atTop (𝓝 0) := by
      have hcont : Continuous (fun z : F => ‖ρ (splitLower z) w - w‖) :=
        (((hρ w).comp continuous_splitLower).sub continuous_const).norm
      convert (hcont.tendsto 0).comp hpar using 1 <;> first | rfl |
        rw [hzero, apply_one, sub_self, norm_zero]
    have hd (n : ℕ) : f n = ‖ρ (splitLower x) w - w‖ := by
      dsimp only [f]
      rw [← show lowerTriangular (p ^ n)⁻¹ 0 * splitLower x * lowerTriangular (p ^ n) 0 =
          splitLower ((((p : F) ^ n) ^ 2) * x) by
        simpa using lower_conjugation (p ^ n) x]
      rw [apply_mul, apply_mul, hdiag]
      let D := ρ (lowerTriangular (p ^ n)⁻¹ 0)
      change ‖D (ρ (splitLower x) w) - w‖ = _
      calc
        _ = ‖D (ρ (splitLower x) w) - D w‖ := by rw [show D w = w from hdiag _]
        _ = _ := by rw [← D.map_sub, D.norm_map]
    have hc := hlim.congr hd
    exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hc))
  intro g
  apply Matrix.SL2.transvection_induction (fun m => ρ m w = w) _ _ g
  · intro i j hij x
    fin_cases i
    · obtain rfl : j = 1 := by fin_cases j <;> tauto
      exact hw x
    · obtain rfl : j = 0 := by fin_cases j <;> tauto
      exact hlower x
  · intro a b ha hb
    rw [apply_mul, hb, ha]

section WeakOperatorLimits

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Extract a weak operator limit along an ultrafilter by taking weak-star limits
of the Riesz functionals and representing them by vectors. -/
private theorem exists_weakOperatorLimit {ι : Type*} (l : Ultrafilter ι)
    (U : ι → E →ₗᵢ[ℂ] E) :
    ∃ B : E →WOT[ℂ] E,
      Tendsto (fun i => ContinuousLinearMapWOT.ofCLM (U i).toContinuousLinearMap) l (𝓝 B) := by
  classical
  have hv (f : E) : ∃ v : E, ‖v‖ ≤ ‖f‖ ∧
      ∀ g : E, Tendsto (fun i => ⟪g, U i f⟫_ℂ) l (𝓝 ⟪g, v⟫_ℂ) := by
    let D := InnerProductSpace.toDual ℂ E
    let Φ (i : ι) : WeakDual ℂ E := (D (U i f)).toWeakDual
    let C := WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ E) ‖f‖
    have hC : IsCompact C := WeakDual.isCompact_closedBall 0 ‖f‖
    have hΦ (i : ι) : Φ i ∈ C := by
      change D (U i f) ∈ Metric.closedBall (0 : StrongDual ℂ E) ‖f‖
      rw [Metric.mem_closedBall, dist_zero_right, D.norm_map, (U i).norm_map]
    have hm : C ∈ l.map Φ := Ultrafilter.mem_map.mpr (Filter.Eventually.of_forall hΦ)
    obtain ⟨φ, hφ, hlim⟩ := hC.ultrafilter_le_nhds' (l.map Φ) hm
    let v := D.symm φ.toStrongDual
    refine ⟨v, ?_, fun g => ?_⟩
    · change ‖D.symm φ.toStrongDual‖ ≤ ‖f‖
      change φ.toStrongDual ∈ Metric.closedBall (0 : StrongDual ℂ E) ‖f‖ at hφ
      simpa only [D.symm.norm_map, Metric.mem_closedBall, dist_zero_right] using hφ
    · have heval : Continuous (fun ψ : WeakDual ℂ E => ψ g) := WeakDual.eval_continuous g
      have h := (heval.tendsto φ).comp (show Tendsto Φ l (𝓝 φ) from hlim)
      have hh : Tendsto (fun i => ⟪U i f, g⟫_ℂ) l (𝓝 ⟪v, g⟫_ℂ) := by
        change Tendsto (fun i => D (U i f) g) l (𝓝 (D v g))
        rw [D.apply_symm_apply]
        exact h
      have hc := (continuous_star.tendsto ⟪v, g⟫_ℂ).comp hh
      change Tendsto (fun i => star ⟪U i f, g⟫_ℂ) l (𝓝 (star ⟪v, g⟫_ℂ)) at hc
      have hstar (r s : E) : star (inner ℂ r s) = inner ℂ s r := inner_conj_symm s r
      simpa only [hstar] using hc
  choose b hb hlim using hv
  let B : E →ₗ[ℂ] E :=
    { toFun := b
      map_add' := fun f f' => by
        apply ext_inner_left ℂ
        intro g
        rw [inner_add_right]
        exact tendsto_nhds_unique (hlim (f + f') g) (by
          simpa only [map_add, inner_add_right] using (hlim f g).add (hlim f' g))
      map_smul' := fun c f => by
        apply ext_inner_left ℂ
        intro g
        rw [inner_smul_right]
        exact tendsto_nhds_unique (hlim (c • f) g) (by
          simpa only [map_smul, inner_smul_right, RingHom.id_apply] using
            (hlim f g).const_mul c) }
  refine ⟨ContinuousLinearMapWOT.ofCLM (B.mkContinuous 1 (fun f => ?_)), ?_⟩
  · change ‖b f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using hb f
  · exact ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr hlim

variable {A : Type u} [Group A] [TopologicalSpace A]
    (ρ : A →* (E ≃ₗᵢ[ℂ] E))

/-- Any weak operator limit of the powers has range fixed by the elements
whose conjugates under the inverse powers tend to the identity. -/
private theorem weakOperatorLimit_fixed (hρ : ∀ f : E, Continuous (fun x => ρ x f))
    (a x : A) {l : Filter ℕ} [l.NeBot]
    (hcontract : Tendsto (fun n : ℕ => (a ^ n)⁻¹ * x * a ^ n) l (𝓝 1))
    {B : E →WOT[ℂ] E}
    (hB : Tendsto (fun n : ℕ =>
      ContinuousLinearMapWOT.ofCLM (ρ (a ^ n)).toLinearIsometry.toContinuousLinearMap) l (𝓝 B))
    (f : E) : ρ x (B f) = B f := by
  have hstrong : Tendsto (fun n : ℕ => ρ ((a ^ n)⁻¹ * x * a ^ n) f) l (𝓝 f) := by
    have h := ((hρ f).tendsto (1 : A)).comp hcontract
    convert h using 1 <;> first | rfl | rw [apply_one]
  have hdist : Tendsto (fun n : ℕ => dist (ρ x (ρ (a ^ n) f)) (ρ (a ^ n) f)) l (𝓝 0) := by
    refine (show Tendsto (fun n : ℕ => dist (ρ ((a ^ n)⁻¹ * x * a ^ n) f) f) l (𝓝 0) by
      simpa only [dist_self] using hstrong.dist (tendsto_const_nhds (x := f))).congr ?_
    intro n
    rw [← (ρ (a ^ n)).isometry.dist_eq, ← apply_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, apply_mul]
  apply ext_inner_left ℂ
  intro g
  have hcoeff := ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp hB
  have hg : UniformContinuous (fun z : E => ⟪g, z⟫_ℂ) :=
    (innerSL ℂ g).uniformContinuous
  have hpair : Tendsto (fun n : ℕ => (ρ x (ρ (a ^ n) f), ρ (a ^ n) f)) l (uniformity E) :=
    tendsto_uniformity_iff_dist_tendsto_zero.mpr hdist
  have hnear : Tendsto (fun n => dist ⟪g, ρ x (ρ (a ^ n) f)⟫_ℂ
      ⟪g, ρ (a ^ n) f⟫_ℂ) l (𝓝 0) :=
    tendsto_uniformity_iff_dist_tendsto_zero.mp (Tendsto.comp hg hpair)
  have hc : Tendsto (fun n : ℕ => ⟪g, ρ x (ρ (a ^ n) f)⟫_ℂ) l (𝓝 ⟪g, B f⟫_ℂ) :=
    (tendsto_iff_of_dist hnear).mpr (hcoeff f g)
  have htrans (w : E) : ⟪g, ρ x w⟫_ℂ = ⟪(ρ x).symm g, w⟫_ℂ := by
    rw [← (ρ x).inner_map_map ((ρ x).symm g) w, (ρ x).apply_symm_apply]
  have hc' : Tendsto (fun n : ℕ => ⟪g, ρ x (ρ (a ^ n) f)⟫_ℂ) l (𝓝 ⟪g, ρ x (B f)⟫_ℂ) := by
    simp_rw [htrans]
    exact hcoeff f ((ρ x).symm g)
  exact tendsto_nhds_unique hc' hc

omit [CompleteSpace E] in
/-- A vector fixed by the element defining the contraction is also fixed by
the contracted element. -/
private theorem fixed_of_contraction (hρ : ∀ f : E, Continuous (fun x => ρ x f))
    (a x : A) (f : E) (hf : ρ a f = f)
    (hcontract : Tendsto (fun n : ℕ => (a ^ n)⁻¹ * x * a ^ n) atTop (𝓝 1)) :
    ρ x f = f := by
  have hp (n : ℕ) : ρ (a ^ n) f = f := by
    induction n with
    | zero => rw [pow_zero, apply_one]
    | succ n ih => rw [pow_succ, apply_mul, hf, ih]
  have hstrong : Tendsto (fun n : ℕ => ρ ((a ^ n)⁻¹ * x * a ^ n) f) atTop (𝓝 f) := by
    convert ((hρ f).tendsto (1 : A)).comp hcontract using 1 <;> first | rfl | rw [apply_one]
  have hdist (n : ℕ) : dist (ρ ((a ^ n)⁻¹ * x * a ^ n) f) f = dist (ρ x f) f := by
    rw [← (ρ (a ^ n)).isometry.dist_eq, ← apply_mul, hp,
      ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, apply_mul, hp]
  have h := (hstrong.dist (tendsto_const_nhds (x := f))).congr hdist
  rw [dist_self] at h
  exact dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds h)

omit [CompleteSpace E] in
private theorem fixed_of_dense_generators (hρ : ∀ f : E, Continuous (fun x => ρ x f))
    (f : E) (s : Set A) (hs : Dense (Subgroup.closure s : Set A))
    (hfix : ∀ x ∈ s, ρ x f = f) : ∀ a : A, ρ a f = f := by
  let K : Subgroup A :=
    { carrier := {x | ρ x f = f}
      one_mem' := apply_one ρ f
      mul_mem' := fun {x y} hx hy => by
        change ρ (x * y) f = f
        rw [apply_mul, show ρ y f = f from hy, show ρ x f = f from hx]
      inv_mem' := fun {x} hx => by
        change ρ x⁻¹ f = f
        calc
          _ = ρ x⁻¹ (ρ x f) := by rw [show ρ x f = f from hx]
          _ = f := by rw [← apply_mul, inv_mul_cancel, apply_one] }
  have hK : IsClosed (K : Set A) := isClosed_eq (hρ f) continuous_const
  have hcl : Subgroup.closure s ≤ K := (Subgroup.closure_le (k := s) (K := K)).2 hfix
  intro a
  exact (closure_minimal hcl hK) (hs a)

end WeakOperatorLimits

section Quotient

open LocalQuotientTransport (RightCosets rightTranslate coset RightInvariant L2 rightOperator)

variable {A : Type u} [Group A] {H : Subgroup A}

private theorem rightTranslate_mul (a b : A) (x : RightCosets H) :
    rightTranslate b (rightTranslate a x) = rightTranslate (a * b) x := by
  induction x using Quotient.inductionOn' with
  | _ c =>
    change coset H ((c * a) * b) = coset H (c * (a * b))
    rw [mul_assoc]

private theorem rightTranslate_transitive (x y : RightCosets H) :
    ∃ a : A, rightTranslate a x = y := by
  induction x using Quotient.inductionOn' with
  | _ b =>
    induction y using Quotient.inductionOn' with
    | _ c =>
      refine ⟨b⁻¹ * c, ?_⟩
      change coset H (b * (b⁻¹ * c)) = coset H c
      rw [← mul_assoc, mul_inv_cancel, one_mul]

variable [TopologicalSpace A] {ν : Measure (RightCosets H)} (hν : RightInvariant ν)

private theorem ae_rightOperator (a : A) (f : L2 ν) :
    (rightOperator hν a f : RightCosets H → ℂ) =ᵐ[ν] f ∘ rightTranslate a :=
  Lp.coeFn_compMeasurePreserving f (hν a)

/-- An invariant vector on a transitive right quotient is almost everywhere
constant. The Haar measure is used in the group variable of Fubini's theorem. -/
private theorem ae_const_of_rightInvariant [MeasurableSpace A] [MeasurableMul A]
    [IsFiniteMeasure ν] (hν₀ : ν ≠ 0)
    (κ : Measure A) [SigmaFinite κ] [κ.IsMulLeftInvariant] (hκ₀ : κ ≠ 0)
    (haction : Measurable (fun p : RightCosets H × A => rightTranslate p.2 p.1))
    (f : L2 ν) (hf : ∀ a : A, rightOperator hν a f = f) :
    ∃ c : ℂ, (f : RightCosets H → ℂ) =ᵐ[ν] fun _ => c := by
  let : NeZero ν := ⟨hν₀⟩
  let : NeZero κ := ⟨hκ₀⟩
  have hm := (Lp.stronglyMeasurable f).measurable
  have hfixed (a : A) : ∀ᵐ x ∂ν, f (rightTranslate a x) = f x := by
    have h := (ae_rightOperator hν a f).symm
    rwa [hf a] at h
  have hmfixed : MeasurableSet {p : RightCosets H × A | f (rightTranslate p.2 p.1) = f p.1} :=
    measurableSet_eq_fun (hm.comp haction) (hm.comp measurable_fst)
  have h := (Measure.ae_ae_comm (μ := ν) (ν := κ) hmfixed).mpr
    (Eventually.of_forall hfixed)
  obtain ⟨x₀, hx₀⟩ := h.exists
  let c : ℂ := f x₀
  have hevery (x : RightCosets H) : ∀ᵐ a ∂κ, f (rightTranslate a x) = c := by
    obtain ⟨b, hb⟩ := rightTranslate_transitive x₀ x
    have h := (measurePreserving_mul_left κ b).quasiMeasurePreserving.ae hx₀
    refine h.mono fun a ha => ?_
    change f (rightTranslate (b * a) x₀) = c at ha
    simpa only [← rightTranslate_mul, hb] using ha
  have hmconst : MeasurableSet {p : RightCosets H × A | f (rightTranslate p.2 p.1) = c} :=
    measurableSet_eq_fun (hm.comp haction) measurable_const
  have h := (Measure.ae_ae_comm (μ := ν) (ν := κ) hmconst).mp
    (Eventually.of_forall hevery)
  obtain ⟨a, ha⟩ := h.exists
  refine ⟨c, ?_⟩
  have hmap := (ae_map_iff (hν a).measurable.aemeasurable
    (measurableSet_eq_fun hm measurable_const)).mpr ha
  rwa [(hν a).map_eq] at hmap

/-- The isometries of the right action with their inverses. -/
private noncomputable def rightRepresentation : A →* (L2 ν ≃ₗᵢ[ℂ] L2 ν) := by
  let hlaw := LocalQuotientTransport.representation_law hν
  let U (a : A) := LinearIsometryEquiv.ofSurjective (rightOperator hν a) (by
    intro f
    exact ⟨rightOperator hν a⁻¹ f, by rw [← hlaw.2, mul_inv_cancel, hlaw.1]⟩)
  refine { toFun := U, map_one' := ?_, map_mul' := ?_ }
  · exact LinearIsometryEquiv.ext hlaw.1
  · intro a b
    exact LinearIsometryEquiv.ext (hlaw.2 a b)

private theorem rightRepresentation_apply (a : A) (f : L2 ν) :
    rightRepresentation hν a f = rightOperator hν a f := rfl

private theorem rightQuotient_t2 [IsTopologicalGroup A] (hH : IsClosed (H : Set A)) :
    T2Space (RightCosets H) := by
  have hq := (LocalQuotientTransport.quotient_action H).1
  apply (t2Space_iff_of_isOpenQuotientMap hq).mpr
  have ht : IsClosed ((fun p : A × A => p.2 * p.1⁻¹) ⁻¹' (H : Set A)) :=
    hH.preimage (continuous_snd.mul continuous_fst.inv)
  convert ht using 1
  ext p
  exact ⟨fun hp => (QuotientGroup.rightRel_apply).mp (Quotient.exact' hp),
    fun hp => Quotient.sound' (QuotientGroup.rightRel_apply.mpr hp)⟩

private theorem rightOperator_continuous [IsTopologicalGroup A] [T2Space (RightCosets H)]
    [ν.InnerRegularCompactLTTop] [IsFiniteMeasure ν] (f : L2 ν) :
    Continuous (fun a : A => rightOperator hν a f) := by
  have hact := (LocalQuotientTransport.quotient_action H).2.2
  let T (a : A) : C(RightCosets H, RightCosets H) :=
    ⟨rightTranslate a, hact.comp (continuous_id.prodMk continuous_const)⟩
  have hT : Continuous T :=
    ContinuousMap.continuous_of_continuous_uncurry T (hact.comp continuous_swap)
  exact Continuous.compMeasurePreservingLp
    (f := fun _ : A => f) (g := T) continuous_const hT hν (by norm_num)

private theorem rightOperator_integral (a : A) (f : L2 ν) :
    (∫ x, (rightOperator hν a f : RightCosets H → ℂ) x ∂ν) = ∫ x, f x ∂ν := by
  rw [integral_congr_ae (ae_rightOperator hν a f)]
  have hm := integral_map (μ := ν) (hν a).measurable.aemeasurable
    ((Lp.stronglyMeasurable f).aestronglyMeasurable)
  rw [(hν a).map_eq] at hm
  exact hm.symm

/-- If all weak operator limits have constant range, their coefficients are
determined by preservation of the integral. -/
private theorem quotient_mixing_of_constant_range [IsFiniteMeasure ν] (hν₀ : ν ≠ 0)
    (a : A)
    (hconst : ∀ (l : Ultrafilter ℕ), (l : Filter ℕ) ≤ atTop → ∀ (B : L2 ν →WOT[ℂ] L2 ν),
      Tendsto (fun n : ℕ => ContinuousLinearMapWOT.ofCLM
        (rightOperator hν (a ^ n)).toContinuousLinearMap) (l : Filter ℕ) (𝓝 B) →
      ∀ f : L2 ν, ∃ c : ℂ, (B f : RightCosets H → ℂ) =ᵐ[ν] fun _ => c)
    (f g : L2 ν) :
    Tendsto (fun n : ℕ => ⟪g, rightOperator hν (a ^ n) f⟫_ℂ) atTop
      (𝓝 (((∫ x, f x ∂ν) * (∫ x, star (g x) ∂ν)) / ((ν Set.univ).toReal : ℂ))) := by
  refine (tendsto_iff_ultrafilter _ _ _).mpr fun l hl => ?_
  obtain ⟨B, hB⟩ := exists_weakOperatorLimit l (fun n => rightOperator hν (a ^ n))
  obtain ⟨c, hc⟩ := hconst l hl B hB f
  have hlim := ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mp hB
  let one : L2 ν := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top ν Set.univ) (1 : ℂ)
  have hone (w : L2 ν) : ⟪one, w⟫_ℂ = ∫ x, w x ∂ν := by
    simpa only [one, setIntegral_univ] using
      L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top ν Set.univ) w
  have hi := hlim f one
  change Tendsto (fun n : ℕ => ⟪one, rightOperator hν (a ^ n) f⟫_ℂ) l
    (𝓝 ⟪one, B f⟫_ℂ) at hi
  simp_rw [hone, rightOperator_integral] at hi
  have hI := tendsto_nhds_unique tendsto_const_nhds hi
  have hcI : (∫ x, f x ∂ν) = ((ν Set.univ).toReal : ℂ) * c := by
    rw [hI, integral_congr_ae hc, integral_const]
    rfl
  have hm : ((ν Set.univ).toReal : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
      ⟨fun h => hν₀ (Measure.measure_univ_eq_zero.mp h), measure_ne_top ν Set.univ⟩)
  have hBg : ⟪g, B f⟫_ℂ = c * ∫ x, star (g x) ∂ν := by
    rw [MeasureTheory.L2.inner_def]
    have he : (fun x => ⟪g x, B f x⟫_ℂ) =ᵐ[ν] fun x => c * star (g x) :=
      hc.mono fun x hx => by
        change ⟪g x, B f x⟫_ℂ = c * star (g x)
        rw [show B f x = c from hx, RCLike.inner_apply]
        rfl
    rw [integral_congr_ae he, integral_const_mul]
  have hz : c * (∫ x, star (g x) ∂ν) =
      ((∫ x, f x ∂ν) * (∫ x, star (g x) ∂ν)) / ((ν Set.univ).toReal : ℂ) := by
    rw [hcI, mul_assoc, mul_comm ((ν Set.univ).toReal : ℂ), mul_div_cancel_right₀ _ hm]
  have h := hlim f g
  change Tendsto (fun n : ℕ => ⟪g, rightOperator hν (a ^ n) f⟫_ℂ) (l : Filter ℕ)
    (𝓝 ⟪g, B f⟫_ℂ) at h
  rwa [hBg, hz] at h

end Quotient

/-- Either elementary root group suffices for the rank-one fixed-vector
implication. Conjugation by the signed row interchange exchanges them. -/
private theorem fixed_of_either_root
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (hMautner : UpperRootFixedVector.{u,v})
    (ρ : SpecialLinearGroup (Fin 2) F →* (E ≃ₗᵢ[ℂ] E))
    (hρ : ∀ f : E, Continuous (fun x => ρ x f)) (f : E)
    (hfix : (∀ x : F, ρ (splitUpper x) f = f) ∨ (∀ x : F, ρ (splitLower x) f = f)) :
    ∀ g, ρ g f = f := by
  rcases hfix with hu | hl
  · exact hMautner F E ρ hρ f hu
  · let s : SpecialLinearGroup (Fin 2) F :=
      ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
    let t : SpecialLinearGroup (Fin 2) F :=
      ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩
    have hts : t * s = 1 := by
      apply Subtype.ext
      change (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = 1
      simp [Matrix.one_fin_two]
    have ht : s⁻¹ = t := inv_eq_of_mul_eq_one_left hts
    have hx (a : F) : s * splitUpper a * s⁻¹ = splitLower (-a) := by
      rw [ht]
      apply Subtype.ext
      change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * (splitUpper a).val *
        !![0, 1; -1, 0] = (splitLower (-a)).val
      simp [upper_matrix, lower_matrix]
    let ψ := ρ.comp (MulAut.conj s).toMonoidHom
    have hψ (w : E) : Continuous (fun g => ψ g w) :=
      (hρ w).comp ((continuous_const.mul continuous_id).mul continuous_const)
    have hupper (a : F) : ψ (splitUpper a) f = f := by
      change ρ (s * splitUpper a * s⁻¹) f = f
      rw [hx]
      exact hl _
    intro g
    obtain ⟨g', rfl⟩ := (MulAut.conj s).surjective g
    exact hMautner F E ψ hψ f hupper g'

/-- A family of rank-one subgroups propagates the initial contraction to a
dense generating set once the elements of that set contract under powers of
elements of the rank-one subgroups. -/
private theorem quotient_mixing_of_rankOne
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] {H : Subgroup A}
    {ν : Measure (LocalQuotientTransport.RightCosets H)} [IsFiniteMeasure ν]
    (hH : IsClosed (H : Set A))
    (hν : LocalQuotientTransport.RightInvariant ν) (hν₀ : ν ≠ 0)
    (hMautner : UpperRootFixedVector.{u,u}) (a : A)
    {I : Type*} (J : I → SpecialLinearGroup (Fin 2) F →* A) (hJ : ∀ i, Continuous (J i))
    (hroot : ∀ i, (∀ x : F, Tendsto (fun n : ℕ => (a ^ n)⁻¹ * J i (splitUpper x) * a ^ n)
      atTop (𝓝 1)) ∨
      (∀ x : F, Tendsto (fun n : ℕ => (a ^ n)⁻¹ * J i (splitLower x) * a ^ n) atTop (𝓝 1)))
    (s : Set A) (hs : Dense (Subgroup.closure s : Set A))
    (hgen : ∀ x ∈ s, ∃ i b, Tendsto (fun n : ℕ => (J i b ^ n)⁻¹ * x * J i b ^ n)
      atTop (𝓝 1))
    (f g : LocalQuotientTransport.L2 ν) :
    Tendsto (fun n : ℕ => ⟪g, LocalQuotientTransport.rightOperator hν (a ^ n) f⟫_ℂ) atTop
      (𝓝 (((∫ x, f x ∂ν) * (∫ x, star (g x) ∂ν)) / ((ν Set.univ).toReal : ℂ))) := by
  let X := LocalQuotientTransport.RightCosets H
  have hq := (LocalQuotientTransport.quotient_action H).1
  let : T2Space X := rightQuotient_t2 hH
  let : LocallyCompactSpace X := hq.locallyCompactSpace
  let : SecondCountableTopology X := Topology.IsOpenQuotientMap.secondCountableTopology hq
  let : ν.InnerRegularCompactLTTop := inferInstance
  let : MeasurableSpace A := borel A
  let : BorelSpace A := ⟨rfl⟩
  let κ : Measure A := Measure.haar
  have hκ₀ : κ ≠ 0 := NeZero.ne κ
  have haction : Measurable (fun p : X × A => LocalQuotientTransport.rightTranslate p.2 p.1) :=
    (LocalQuotientTransport.quotient_action H).2.2.measurable
  let ρ := rightRepresentation hν
  have hρ (w : LocalQuotientTransport.L2 ν) : Continuous (fun x : A => ρ x w) :=
    rightOperator_continuous hν w
  apply quotient_mixing_of_constant_range hν hν₀ a _ f g
  intro l hl B hB w
  have hfixed (x : A)
      (hx : Tendsto (fun n : ℕ => (a ^ n)⁻¹ * x * a ^ n) atTop (𝓝 1)) :
      ρ x (B w) = B w :=
    weakOperatorLimit_fixed ρ hρ a x (hx.mono_left hl) hB w
  have hSL (i : I) (b : SpecialLinearGroup (Fin 2) F) : ρ (J i b) (B w) = B w := by
    apply fixed_of_either_root hMautner (ρ.comp (J i)) (fun z => (hρ z).comp (hJ i)) (B w)
    exact (hroot i).imp (fun h x => hfixed _ (h x)) (fun h x => hfixed _ (h x))
  apply ae_const_of_rightInvariant hν hν₀ κ hκ₀ haction (B w)
  apply fixed_of_dense_generators ρ hρ (B w) s hs
  intro x hx
  obtain ⟨i, b, hc⟩ := hgen x hx
  exact fixed_of_contraction ρ hρ (J i b) x (B w) (hSL i b) hc

section RankOneContinuity

variable {F : Type u} [Field F]

private theorem factor_of_topLeft_ne_zero (g : SpecialLinearGroup (Fin 2) F)
    (ha : g.val 0 0 ≠ 0) :
    g = splitLower (g.val 1 0 / g.val 0 0) *
      SpecialLinearGroup.diag2 (g.val 0 0) ha * splitUpper (g.val 0 1 / g.val 0 0) := by
  apply Subtype.ext
  change g.val = ((splitLower _).val * (SpecialLinearGroup.diag2 _ ha).val) *
    (splitUpper _).val
  simp only [lower_matrix, upper_matrix, SpecialLinearGroup.diag2_coe', Matrix.mul_fin_two]
  have hd := SpecialLinearGroup.det_coe g
  rw [Matrix.det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [ha]
  linear_combination hd

variable [TopologicalSpace F] [IsTopologicalDivisionRing F] [T1Space F]

/-- The two elementary coordinate curves determine continuity of an SL₂
homomorphism by Gaussian elimination near the identity. -/
private theorem continuous_rankOneHom {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (j : SpecialLinearGroup (Fin 2) F →* A)
    (hu : Continuous (fun t : F => j (splitUpper t)))
    (hl : Continuous (fun t : F => j (splitLower t))) : Continuous j := by
  let SL := SpecialLinearGroup (Fin 2) F
  let m (i k : Fin 2) (g : SL) := g.val i k
  have hm (i k : Fin 2) : Continuous (m i k) :=
    (continuous_apply k).comp (SpecialLinearGroup.continuous_apply id continuous_id i)
  let u (t : F) := j (splitUpper t)
  let v (t : F) := j (splitLower t)
  let d (t : F) := u t * v (-t⁻¹) * u t * u (-1) * v 1 * u (-1)
  have hd : ContinuousAt d (1 : F) := by
    have hInv : ContinuousAt (fun t : F => -t⁻¹) 1 :=
      (continuousAt_inv₀ (show (1 : F) ≠ 0 from one_ne_zero)).neg
    exact (((((hu.continuousAt.mul (hl.continuousAt.comp hInv)).mul
      hu.continuousAt).mul continuousAt_const).mul continuousAt_const).mul continuousAt_const)
  let P (g : SL) := v (m 1 0 g / m 0 0 g) * d (m 0 0 g) * u (m 0 1 g / m 0 0 g)
  have htop : m 0 0 (1 : SL) = 1 := by simp [m, SL, SpecialLinearGroup.coe_one]
  have hzero : m 0 0 (1 : SL) ≠ 0 := by rw [htop]; exact one_ne_zero
  have hd' : ContinuousAt d (m 0 0 (1 : SL)) := htop.symm ▸ hd
  have hP : ContinuousAt P (1 : SL) :=
    ((hl.continuousAt.comp ((hm 1 0).continuousAt.div (hm 0 0).continuousAt hzero)).mul
      (hd'.comp (hm 0 0).continuousAt)).mul
        (hu.continuousAt.comp ((hm 0 1).continuousAt.div (hm 0 0).continuousAt hzero))
  have heq (g : SL) (hg : m 0 0 g ≠ 0) : j g = P g := by
    have hh := congrArg j (factor_of_topLeft_ne_zero g hg)
    rw [Matrix.diag2_decompose] at hh
    simpa only [map_mul, P, d, u, v, m, splitUpper, splitLower] using hh
  apply continuous_of_continuousAt_one j
  have hne : ∀ᶠ g in 𝓝 (1 : SL), m 0 0 g ≠ 0 :=
    ((hm 0 0).continuousAt (x := (1 : SL))).tendsto.eventually_ne hzero
  exact hP.congr (hne.mono fun g hg => (heq g hg).symm)

end RankOneContinuity


section LocalTopology

open AlgebraicGeometry CategoryTheory
open LocalAlgebraicTransport (RationalPoints pointTopology evaluation IsUniformizingUnit)
open CocharacterDynamics (polynomialAlgebra polynomialEvaluate polynomialToLaurent
  cocharacterPoint orbit HasLimit oppositeCocharacter mapPoints_comp)
open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open private unitPointHom unitPointHom_apply evalLaurent orbit_eval opposite_point
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open scoped CategoryTheory.MonObj

private theorem uniformizer_powers {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : Fˣ) (hπ : IsUniformizingUnit π) :
    Tendsto (fun n : ℕ => (π : F) ^ n) atTop (𝓝 0) := by
  exact tendsto_valuation_lt_one ((ValuativeRel.valuation F).vlt_one_iff.mp hπ.1)

private theorem localField_topology (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    T2Space F ∧ SecondCountableTopology F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let : (Valued.v (R := F)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := F) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  let : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  exact ⟨inferInstance, inferInstance⟩

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

set_option backward.isDefEq.respectTransparency false in
/-- Coordinates of a polynomial presentation realize its rational points as
the closed set cut out by the kernel equations. -/
private theorem presentation_closedEmbedding {A I : Type u} [CommRing A] [Algebra F A]
    [T2Space F] (φ : MvPolynomial I F →ₐ[F] A) (hφ : Function.Surjective φ) :
    let := Specs.ExceptionalIwahoriCongruence.affinePointTopology F A F
    Topology.IsClosedEmbedding
      (fun p : A →ₐ[F] F => fun i : I => p (φ (MvPolynomial.X i))) := by
  let P := A →ₐ[F] F
  let t := Specs.ExceptionalIwahoriCongruence.affinePointTopology F A F
  let c (f : P) (i : I) := f (φ (MvPolynomial.X i))
  let ev := fun f : P => (f : A → F)
  have hEval (f : P) (p : MvPolynomial I F) : MvPolynomial.eval (c f) p = f (φ p) := by
    change MvPolynomial.aeval (c f) p = (f.comp φ) p
    have he : MvPolynomial.aeval (c f) = f.comp φ := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      rfl
    rw [he]
  have hinj : Function.Injective c := by
    intro f g h
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hφ a
    rw [← hEval, ← hEval, h]
  have hind : t = TopologicalSpace.induced c inferInstance := by
    apply le_antisymm
    · let := t
      exact continuous_iff_le_induced.mp (continuous_pi fun i =>
        (continuous_apply (φ (MvPolynomial.X i))).comp continuous_induced_dom)
    · let := TopologicalSpace.induced c inferInstance
      have hc : Continuous c := continuous_induced_dom
      apply continuous_iff_le_induced.mp
      change Continuous ev
      apply continuous_pi
      intro a
      obtain ⟨p, rfl⟩ := hφ a
      change Continuous (fun f : P => f (φ p))
      simp_rw [← hEval]
      exact (MvPolynomial.continuous_eval p).comp hc
  let := t
  refine ⟨⟨⟨hind⟩, hinj⟩, ?_⟩
  have hRange : Set.range c =
      ⋂ q : RingHom.ker φ.toRingHom, {v : I → F | MvPolynomial.eval v q.val = 0} := by
    ext v
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨f, rfl⟩ q
      have hq : φ q.val = 0 := RingHom.mem_ker.mp q.property
      rw [hEval, hq, map_zero]
    · intro hz
      let e := Ideal.quotientKerAlgEquivOfSurjective hφ
      let f := Ideal.Quotient.liftₐ (RingHom.ker φ.toRingHom) (MvPolynomial.aeval v)
        (fun p hp => hz ⟨p, hp⟩)
      refine ⟨f.comp e.symm.toAlgHom, ?_⟩
      funext i
      have hq : e (Ideal.Quotient.mk (RingHom.ker φ.toRingHom) (MvPolynomial.X i)) = φ (MvPolynomial.X i) := rfl
      change f (e.symm (φ (MvPolynomial.X i))) = v i
      rw [← hq, e.symm_apply_apply]
      exact MvPolynomial.aeval_X v i
  rw [hRange]
  exact isClosed_iInter fun q => isClosed_singleton.preimage
    (MvPolynomial.continuous_eval q.val)

omit [IsTopologicalRing F] in
set_option backward.isDefEq.respectTransparency false in
private theorem affinePoints_homeomorph
    (X : SchemeOver F) (B : TestAlgebra F) (e : (testSpec F).obj (.op B) ≅ X) :
    let := pointTopology X
    let := Specs.ExceptionalIwahoriCongruence.affinePointTopology F B F
    ∃ h : (B →ₐ[F] F) ≃ₜ RationalPoints X, ∀ p : B →ₐ[F] F,
      h p = (testSpec F).map (CommAlgCat.ofHom p).op ≫ e.hom := by
  let := pointTopology X
  let := Specs.ExceptionalIwahoriCongruence.affinePointTopology F B F
  let f (p : B →ₐ[F] F) : RationalPoints X :=
    (testSpec F).map (CommAlgCat.ofHom p).op ≫ e.hom
  let hff := AlgebraicGeometry.algSpec.fullyFaithful (R := CommRingCat.of F)
  have hf : Function.Bijective f := by
    constructor
    · intro p q h
      have he : (testSpec F).map (CommAlgCat.ofHom p).op =
          (testSpec F).map (CommAlgCat.ofHom q).op := (cancel_mono e.hom).mp h
      exact congrArg (fun a => a.unop.hom) (hff.map_injective he)
    · intro p
      let a := (hff.preimage (p ≫ e.inv)).unop
      refine ⟨a.hom, ?_⟩
      change (testSpec F).map a.op ≫ e.hom = p
      rw [show (testSpec F).map a.op = p ≫ e.inv from hff.map_preimage _,
        Category.assoc, e.inv_hom_id, Category.comp_id]
  let E := Equiv.ofBijective f hf
  let b := (Scheme.Γ.mapIso (Iso.op ((Over.forget (Spec (CommRingCat.of F))).mapIso e))) ≪≫
    Scheme.ΓSpecIso (CommRingCat.of B)
  have hEval (p : B →ₐ[F] F) (a : Γ(X.left, ⊤)) : evaluation (E p) a = p (b.hom a) := by
    change ((Spec.map (CommRingCat.ofHom p.toRingHom) ≫ e.hom.left).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom a = _
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rfl
  have hcont (a : Γ(X.left, ⊤)) : Continuous (fun p : RationalPoints X => evaluation p a) :=
    (continuous_apply a).comp continuous_induced_dom
  refine ⟨{ toEquiv := E, continuous_toFun := ?_, continuous_invFun := ?_ }, ?_⟩
  · apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    change Continuous (fun p => evaluation (E p) a)
    simp_rw [hEval]
    exact (continuous_apply (b.hom a)).comp continuous_induced_dom
  · apply continuous_induced_rng.mpr
    apply continuous_pi
    intro c
    let a := b.inv c
    have h (p : RationalPoints X) : E.symm p c = evaluation p a := by
      conv_rhs => rw [← E.apply_symm_apply p, hEval]
      simp [a]
    change Continuous (fun p => E.symm p c)
    simp_rw [h]
    exact hcont a
  · intro p
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The rational points of an affine finite-type scheme over the local field
have their usual locally compact, second countable, Hausdorff topology. -/
private theorem rationalPoints_topology [T2Space F] [LocallyCompactSpace F]
    [SecondCountableTopology F] (X : SchemeOver F) (hX : IsAffine X.left)
    (hXft : LocallyOfFiniteType X.hom) :
    let := pointTopology X
    T2Space (RationalPoints X) ∧ LocallyCompactSpace (RationalPoints X) ∧
      SecondCountableTopology (RationalPoints X) := by
  let := pointTopology X
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  let := hXft
  have hB : LocallyOfFiniteType ((testSpec F).obj B).hom := by
    rw [← Over.w e.hom]
    infer_instance
  let R := Opposite.unop B
  let := Specs.ExceptionalIwahoriCongruence.affinePointTopology F R F
  have hft : Algebra.FiniteType F R := by
    have hF : RingHom.FiniteType (algebraMap F R) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hB
    exact RingHom.finiteType_algebraMap.mp hF
  obtain ⟨I, hI, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp hft
  let := hI
  obtain ⟨b, _⟩ := affinePoints_homeomorph X R e
  have h := (presentation_closedEmbedding φ hφ).comp b.symm.isClosedEmbedding
  exact ⟨h.isEmbedding.t2Space, h.locallyCompactSpace, h.isEmbedding.secondCountableTopology⟩

set_option backward.isDefEq.respectTransparency false in
/-- Polynomial families of rational points are continuous at every scalar,
including the specialization at zero. -/
private theorem continuous_polynomialPoint (X : SchemeOver F)
    (p : LinearAlgebraicGroups.Points X (polynomialAlgebra (CommAlgCat.of F F))) :
    let := pointTopology X
    Continuous (fun t : F => LinearAlgebraicGroups.mapPoints
      (polynomialEvaluate (CommAlgCat.of F F) t) p) := by
  let := pointTopology X
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  let P := (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (Polynomial F))).hom).hom a
  have h (t : F) :
      evaluation (LinearAlgebraicGroups.mapPoints
        (polynomialEvaluate (CommAlgCat.of F F) t) p) a = P.eval t := by
    change ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t)) ≫ p.left).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom).hom a = _
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rfl
  change Continuous (fun t : F => evaluation (LinearAlgebraicGroups.mapPoints
    (polynomialEvaluate (CommAlgCat.of F F) t) p) a)
  simpa only [h] using P.continuous

private noncomputable def cocharacterHom {G : GroupScheme F} (c : Cocharacter G) (R : TestAlgebra F) :
    Rˣ →* GroupPoints G R :=
  (((groupPointsFunctor F).map c).app R).hom.comp (unitPointHom R)

omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem cocharacterHom_apply {G : GroupScheme F} (c : Cocharacter G)
    (R : TestAlgebra F) (t : Rˣ) :
    cocharacterHom c R t = cocharacterPoint c R t := by
  simp only [cocharacterHom, MonoidHom.comp_apply, unitPointHom_apply, cocharacterPoint]

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace F] [IsTopologicalRing F] in
private theorem evaluatePolynomialViaLaurent (t : Fˣ) :
    polynomialToLaurent (CommAlgCat.of F F) ≫ evalLaurent (𝟙 (CommAlgCat.of F F)) t =
      polynomialEvaluate (CommAlgCat.of F F) (t : F) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro p
  change LaurentPolynomial.eval₂ (RingHom.id F) t (Polynomial.toLaurent p) =
    Polynomial.eval (t : F) p
  rw [LaurentPolynomial.eval₂_toLaurent]
  rfl

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]

set_option backward.isDefEq.respectTransparency false in
/-- Algebraic extension of the conjugation family at zero gives convergence
of conjugation by positive powers of the evaluated cocharacter. -/
private theorem cocharacter_contraction {G : GroupScheme F}
    (c : Cocharacter G) (π : Fˣ) (hπ : IsUniformizingUnit π)
    (x z : GroupPoints G (CommAlgCat.of F F)) (h : HasLimit c x z) :
    let : TopologicalSpace (GroupPoints G (CommAlgCat.of F F)) := pointTopology G.X
    let a := cocharacterPoint c (CommAlgCat.of F F) π
    Tendsto (fun n : ℕ => a ^ n * x * (a ^ n)⁻¹) atTop (𝓝 z) := by
  let : TopologicalSpace (GroupPoints G (CommAlgCat.of F F)) := pointTopology G.X
  let R := CommAlgCat.of F F
  let a := cocharacterPoint c R π
  obtain ⟨p, hp, hz⟩ := h
  have hcurve (t : Fˣ) :
      mapPoints (polynomialEvaluate R (t : F)) (X := G.X) p =
        cocharacterPoint c R t * x * (cocharacterPoint c R t)⁻¹ := by
    have he : polynomialEvaluate R (t : F) = polynomialToLaurent R ≫ evalLaurent (𝟙 R) t :=
      (evaluatePolynomialViaLaurent t).symm
    rw [he, mapPoints_comp (X := G.X), hp, orbit_eval]
    simp only [mapPoints, CategoryTheory.op_id]
    rw [(testSpec F).map_id, Category.id_comp]
  have hpow (n : ℕ) : cocharacterPoint c R (π ^ n) = a ^ n := by
    simp only [← cocharacterHom_apply, map_pow, a]
  have hcont : @Continuous F (GroupPoints G R) _ (pointTopology G.X)
      (fun t : F => (mapPoints (polynomialEvaluate R t) (X := G.X) p : GroupPoints G R)) :=
    continuous_polynomialPoint G.X p
  have hv := (hcont.tendsto 0).comp (uniformizer_powers π hπ)
  have ht : Tendsto (fun n : ℕ => (mapPoints (polynomialEvaluate R ((π ^ n : Fˣ) : F))
      (X := G.X) p : GroupPoints G R)) atTop
        (@nhds (GroupPoints G R) (pointTopology G.X) z) := by
    rw [← hz]
    exact hv
  change Tendsto (fun n : ℕ => a ^ n * x * (a ^ n)⁻¹) atTop (𝓝 z)
  simpa only [hcurve, hpow] using ht

set_option backward.isDefEq.respectTransparency false in
private theorem oppositeCocharacter_contraction {G : GroupScheme F}
    (c : Cocharacter G) (π : Fˣ) (hπ : IsUniformizingUnit π)
    (x z : GroupPoints G (CommAlgCat.of F F)) (h : HasLimit (oppositeCocharacter c) x z) :
    let : TopologicalSpace (GroupPoints G (CommAlgCat.of F F)) := pointTopology G.X
    let a := cocharacterPoint c (CommAlgCat.of F F) π
    Tendsto (fun n : ℕ => (a ^ n)⁻¹ * x * a ^ n) atTop (𝓝 z) := by
  let : TopologicalSpace (GroupPoints G (CommAlgCat.of F F)) := pointTopology G.X
  have he : cocharacterPoint (oppositeCocharacter c) (CommAlgCat.of F F) π =
      (cocharacterPoint c (CommAlgCat.of F F) π)⁻¹ := by
    rw [opposite_point, ← cocharacterHom_apply, map_inv, cocharacterHom_apply]
  have hc := cocharacter_contraction (oppositeCocharacter c) π hπ x z h
  simpa only [he, inv_pow, inv_inv] using hc

/-- Topological hypotheses of the quotient mixing argument on the original
rational points in their affine coordinate topology. -/
private theorem localGroup_topology (G : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F) :
    let := pointTopology G.val.X
    IsTopologicalGroup (RationalPoints G.val.X) ∧ T2Space (RationalPoints G.val.X) ∧
      LocallyCompactSpace (RationalPoints G.val.X) ∧
      SecondCountableTopology (RationalPoints G.val.X) := by
  let := pointTopology G.val.X
  obtain ⟨hT₂, hSecond⟩ := localField_topology F
  let := hT₂
  let := hSecond
  exact ⟨LocalAlgebraicTransport.rationalPointTopologicalGroup G,
    rationalPoints_topology G.val.X G.prop.1 G.prop.2.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- Applies the quotient argument directly to scheme-theoretic contraction
of the rational points associated to two opposite sign choices. -/
private theorem localQuotient_mixing_of_algebraic_contractions
    (G : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F)
    (hMautner : UpperRootFixedVector.{u,u}) (c : Cocharacter G.val)
    (π : Fˣ) (hπ : IsUniformizingUnit π)
    (I : Type u) (J : I → SpecialLinearGroup (Fin 2) F →* RationalPoints G.val.X)
    (s : Set (RationalPoints G.val.X)) :
    let R := CommAlgCat.of F F
    let : TopologicalSpace (RationalPoints G.val.X) := pointTopology G.val.X
    (∀ i, Continuous (fun t : F => J i (splitUpper t))) →
    (∀ i, Continuous (fun t : F => J i (splitLower t))) →
    (∀ i, (∀ t : F, HasLimit (oppositeCocharacter c) (J i (splitUpper t)) 1) ∨
      (∀ t : F, HasLimit (oppositeCocharacter c) (J i (splitLower t)) 1)) →
    Dense (Subgroup.closure s : Set (RationalPoints G.val.X)) →
    (∀ x ∈ s, ∃ (i : I) (b : SpecialLinearGroup (Fin 2) F) (d : Cocharacter G.val),
      J i b = cocharacterPoint d R π ∧ HasLimit (oppositeCocharacter d) x 1) →
    ∀ (H : Subgroup (RationalPoints G.val.X)), IsClosed (H : Set (RationalPoints G.val.X)) →
      ∀ (ν : Measure (LocalQuotientTransport.RightCosets H)) [IsFiniteMeasure ν], ν ≠ 0 →
        ∀ (hν : LocalQuotientTransport.RightInvariant ν) (f g : LocalQuotientTransport.L2 ν),
          let a : RationalPoints G.val.X := cocharacterPoint c R π
          Tendsto (fun n : ℕ => ⟪g, LocalQuotientTransport.rightOperator hν (a ^ n) f⟫_ℂ) atTop
            (𝓝 (((∫ x, f x ∂ν) * (∫ x, star (g x) ∂ν)) / ((ν Set.univ).toReal : ℂ))) := by
  let : TopologicalSpace (RationalPoints G.val.X) := pointTopology G.val.X
  let : T2Space F := (localField_topology F).1
  obtain ⟨htop, hT₂, hLc, hSc⟩ := localGroup_topology G
  let := htop
  let := hT₂
  let := hLc
  let := hSc
  dsimp only
  intro hu hl hroot hs hgen H hH ν _ hν₀ hν f g
  let a : RationalPoints G.val.X := cocharacterPoint c (CommAlgCat.of F F) π
  change Tendsto (fun n : ℕ => ⟪g, LocalQuotientTransport.rightOperator hν (a ^ n) f⟫_ℂ)
    atTop _
  apply quotient_mixing_of_rankOne hH hν hν₀ hMautner a J
    (fun i => continuous_rankOneHom (J i) (hu i) (hl i)) _ s hs _ f g
  · intro i
    rcases hroot i with hu' | hl'
    · exact Or.inl fun t => oppositeCocharacter_contraction c π hπ (J i (splitUpper t)) 1 (hu' t)
    · exact Or.inr fun t => oppositeCocharacter_contraction c π hπ (J i (splitLower t)) 1 (hl' t)
  · intro x hx
    obtain ⟨i, b, d, he, hc⟩ := hgen x hx
    refine ⟨i, b, ?_⟩
    rw [he]
    exact oppositeCocharacter_contraction d π hπ x 1 hc

end LocalTopology

section RelativeRankOne

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Arithmetic.TrialitarianFixedRootSL2 (RankOne)
open Specs.ExceptionalLocalRadicalGeneration (AdaptedBorel HasProjectedRootSystem SplitRootSL2
  projectedRoots)
open Specs.RootGroups (Proportional)
open Specs.Arithmetic.LocalMixingExceptionalRootData (MarkedTorus Projection cartanForm)
open Specs.ExceptionalAffineRootSystems (exceptionalCartan)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.GeometricRadicals (IsMaximalTorus baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private extendSubgroup from LinearAlgebraicGroups.RootData.RankOneFlag
open private maximal_of_square from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private groupBaseChangeTowerIso from LinearAlgebraicGroups.Relative.RationalCocharacter
open private maximalTorus_ringEquiv from LinearAlgebraicGroups.Arithmetic.LocalMixingExceptionalRootData

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

set_option backward.isDefEq.respectTransparency false in
/-- A marked torus over the separable closure gives geometric maximality of
the original torus, using the comparison of the two algebraic closures. -/
private theorem adaptedTorus_geometricallyMaximal {n : ℕ} (A : AdaptedBorel G n) :
    IsGeometricallyMaximal A.T := by
  let K := SeparableClosure F
  let L := AlgebraicClosure K
  let M := AlgebraicClosure F
  let B := groupBaseChange K L
  obtain ⟨hP, hmax⟩ := A.P.maximal
  let T := extendSubgroup L (extendSubgroup K A.T)
  have hT : IsMaximalTorus T := by
    apply maximal_of_square (B.mapIso A.ambient) (baseChangedSubgroup L A.P.T hP) T
      (B.mapIso A.torus.symm) _ hmax
    change B.map A.torus.inv ≫ B.map ((groupBaseChange F K).map A.T.inclusion) =
      B.map A.P.T.inclusion ≫ B.map A.ambient.hom
    rw [← B.map_comp, ← B.map_comp, ← A.torus_eq, Iso.inv_hom_id_assoc]
  let e : L ≃ₐ[F] M := IsAlgClosure.equiv F L M
  let : Algebra L M := e.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  let tower := Functor.isoWhiskerRight
    (groupBaseChangeTowerIso (k := F) (K := K) (L := L)) (groupBaseChange L M) ≪≫
      groupBaseChangeTowerIso (k := F) (K := L) (L := M)
  let Tgeom := extendSubgroup M A.T
  have hM := maximalTorus_ringEquiv e.toRingEquiv (fun _ => rfl)
    (baseChangedAlgebraicGroup L (baseChangedAlgebraicGroup K G)) T hT
  exact ⟨Tgeom.isClosedImmersion, maximal_of_square (tower.app G.val)
    (extendSubgroup M T) Tgeom (tower.app A.T.group)
    (tower.hom.naturality A.T.inclusion).symm hM⟩

private theorem cartanForm_single {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    cartanForm n (Pi.single i (1 : ℝ)) x =
      ∑ j, (exceptionalCartan n i j : ℝ) * x j := by
  classical
  unfold cartanForm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private theorem selectedRoot_orthogonal {n m : ℕ} (p : Projection n m) (x : Fin n → ℝ)
    (hx : p.projectReal x = 0) :
    cartanForm n (Pi.single p.selectedIndex (1 : ℝ)) x = 0 := by
  classical
  cases p with
  | innerE6 =>
    have h1 : x 1 = 0 := congrFun hx (0 : Fin 2)
    have h3 : x 3 = 0 := congrFun hx (1 : Fin 2)
    have hrow (j : Fin 6) : exceptionalCartan 6 1 j = (![0, 2, 0, -1, 0, 0] : Fin 6 → ℤ) j := by
      fin_cases j <;> decide
    simp only [cartanForm_single, Projection.selectedIndex, hrow]
    norm_num [Fin.sum_univ_succ, h1, h3]
  | innerE7 =>
    have h0 : x 0 = 0 := congrFun hx (0 : Fin 4)
    have h2 : x 2 = 0 := congrFun hx (1 : Fin 4)
    have h3 : x 3 = 0 := congrFun hx (2 : Fin 4)
    have hrow (j : Fin 7) : exceptionalCartan 7 2 j = (![-1, 0, 2, -1, 0, 0, 0] : Fin 7 → ℤ) j := by
      fin_cases j <;> decide
    simp only [cartanForm_single, Projection.selectedIndex, hrow]
    norm_num [Fin.sum_univ_succ, h0, h2, h3]
  | outerE6 =>
    have h1 : x 1 = 0 := congrFun hx (0 : Fin 4)
    have h3 : x 3 = 0 := congrFun hx (1 : Fin 4)
    have hrow (j : Fin 6) : exceptionalCartan 6 1 j = (![0, 2, 0, -1, 0, 0] : Fin 6 → ℤ) j := by
      fin_cases j <;> decide
    simp only [cartanForm_single, Projection.selectedIndex, hrow]
    norm_num [Fin.sum_univ_succ, h1, h3]

set_option backward.isDefEq.respectTransparency false in
private theorem exceptionalRootData_of_projection
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (hG : IsAbsolutelyAlmostSimple G) (hSC : GeometricallySimplyConnected G)
    (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    {n m count : ℕ} (A : AdaptedBorel G n) (p : Projection n m)
    (L : SplitRootSL2 A (A.numbering p.selectedIndex).val)
    (h : HasProjectedRootSystem A p.project count p.selectedIndex L) :
    HasReducedRoots S ∧ HasLongestSingleRoot S := by
  obtain ⟨coeff, encode, hencode, hcoeff, _, hrestrict, hroots, _, _, a, θ, α,
    ha, _, _, _, _, hsingle, _⟩ := h
  let M : MarkedTorus A.S p := {
    maximalSplit := A.maximalSplit
    torus := A.T
    isTorus := A.maximalTorus.1
    isMaximal := adaptedTorus_geometricallyMaximal A
    inclusion := A.intoTorus
    inclusion_comp := A.intoTorus_eq
    pair := A.P
    datum := A.D
    groupIso := A.ambient
    torusIso := A.torus.symm
    inclusions_commute := by rw [← A.torus_eq, Iso.symm_hom, Iso.inv_hom_id_assoc]
    multiplicative := A.multiplicative
    preservesUnits := A.multiplicative_eq
    numbering := A.numbering
    cartan_eq := fun i j => (A.cartan_eq i j).symm
    coordinates := coeff
    coordinates_eq := hcoeff
    encode := encode
    encode_injective := hencode
    restriction_eq := hrestrict
    relativeRoots_eq := by
      rw [hroots]
      ext b
      constructor
      · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hv0⟩, rfl⟩
        exact ⟨⟨v, hv⟩, fun he => hv0 (Set.mem_singleton_iff.mpr he), rfl⟩
      · rintro ⟨v, hv0, rfl⟩
        exact ⟨p.project v.val, ⟨⟨v.val, v.property, rfl⟩,
          fun he => hv0 (Set.mem_singleton_iff.mp he)⟩, rfl⟩
    selected := a
    selected_eq := ha
    orthogonal := selectedRoot_orthogonal p
    singleton := ⟨(A.numbering p.selectedIndex).val,
      ((hsingle _).1).mpr rfl, fun b hb => ((hsingle b).1).mp hb⟩ }
  exact LocalMixingExceptionalRootData.exceptionalRootData F G hG hSC S hS A.S p M

/-- The singleton split root subgroup and its highest-root version. -/
theorem longRootRankOne_conditional
    (_ : ExceptionalRootSystemsAndLevis.{u}) (_ : LocalRadicalGeneration.{u}) :
    LongRootRankOne.{u} := by
  intro F _ _ _ _ G hG hSC S hS a hlong hsingle
  have hrank := LocalMixingSingletonRootSL2.singletonRootSL2 F G hG hSC S hS
  exact ⟨hrank a hsingle, fun hred =>
    LocalMixingHighestRootSL2.highestRootSL2 F G hG hSC S hS hred ⟨a, hlong, hsingle⟩ hrank⟩

/-- The marked exceptional and trialitarian systems give a split subgroup
at the highest root of the actual relative system. -/
theorem exceptionalAndTrialitarianRankOne_conditional
    (systems : ExceptionalRootSystemsAndLevis.{u}) (_ : LocalRadicalGeneration.{u}) :
    ExceptionalAndTrialitarianRankOne.{u} := by
  intro F _ _ _ _ G hG hSC hcase S hS
  have hreduced : HasReducedRoots S ∧ HasLongestSingleRoot S := by
    rcases hcase with hexc | ⟨htrial, hqs⟩
    · have htypes := systems F G hG hSC
      rcases hexc with ⟨habs, hinner, hsplit⟩ | ⟨habs, hinner, hsplit⟩ | ⟨habs, houter⟩
      · obtain ⟨A, L, _, _, h, _⟩ := htypes.1 habs hinner hsplit
        exact exceptionalRootData_of_projection hG hSC S hS A .innerE6 L h
      · obtain ⟨A, L, _, _, h, _⟩ := htypes.2.1 habs hinner hsplit
        exact exceptionalRootData_of_projection hG hSC S hS A .innerE7 L h
      · obtain ⟨A, L, h⟩ := htypes.2.2 habs houter
        exact exceptionalRootData_of_projection hG hSC S hS A .outerE6 L h
    · exact LocalMixingTrialitarianRootData.trialitarianRootData F G hG hSC htrial hqs S hS
  exact ⟨hreduced.1, hreduced.2,
    LocalMixingHighestRootSL2.highestRootSL2 F G hG hSC S hS hreduced.1 hreduced.2
      (LocalMixingSingletonRootSL2.singletonRootSL2 F G hG hSC S hS)⟩

end RelativeRankOne

section RankOneDynamics

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup SubgroupSections)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (relativeRoots IsRegular)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Arithmetic.TrialitarianFixedRootSL2 (RankOne)
open Specs.Arithmetic.LocalMixingHermitianRankOne (RankOneIndex transvectionPoint)
open Specs.Arithmetic.QuaternionSpinCharacteristicTwo (oppositeWords)
open Specs.GeneralLinearStructure (SpecialMatrixPoints)
open Specs.GeometricRadicals (IsSplitReductive)
open Specs.GeometricBorelConjugacy (IsQuasiSplit)
open Specs.RootGroups (IsRootSubgroup rootPoint)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open LocalAlgebraicTransport (RationalPoints pointTopology IsUniformizingUnit)
open CocharacterDynamics
  (HasLimit LimitDecomposition cocharacterPoint oppositeCocharacter polynomialAlgebra polynomialEvaluate)
open private reindexSpecialLinear from LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitPinnedModels
open private reindexTransvection from LinearAlgebraicGroups.Arithmetic.TrialitarianFixedRootSL2
open private transvectionHom transvectionPoint_natural cocharacterPoint_comp
  from LinearAlgebraicGroups.Arithmetic.LocalMixingHermitianRankOne
open private opposite_point from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private opposite_opposite from LinearAlgebraicGroups.RootData.RankOneFlag

variable {F : Type u} [Field F] {G A : AffineAlgebraicGroup F}

local notation "R₀" => CommAlgCat.of F F

/-- The marked algebraic rank-one embedding on rational determinant-one matrices. -/
private noncomputable def rankOneHom (j : A.val ⟶ G.val) (e : SpecialMatrixPoints A 2) :
    SpecialLinearGroup (Fin 2) F →* RationalPoints G.val.X :=
  (transvectionHom (R := R₀) j e).comp
    (reindexSpecialLinear (Equiv.ulift.symm : Fin 2 ≃ RankOneIndex.{u})).toMonoidHom

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneHom_point (j : A.val ⟶ G.val) (e : SpecialMatrixPoints A 2)
    (p : GroupPoints A.val R₀) :
    p ≫ j.hom.hom ∈ (rankOneHom j e).range := by
  let q := reindexSpecialLinear (R := F) (Equiv.ulift.symm : Fin 2 ≃ RankOneIndex.{u})
  refine ⟨q.symm (e.hom.app R₀ p), ?_⟩
  change (e.inv.app R₀ (q (q.symm (e.hom.app R₀ p))) : GroupPoints A.val R₀) ≫
    j.hom.hom = p ≫ j.hom.hom
  rw [q.apply_symm_apply]
  exact congrArg (fun z : GroupPoints A.val R₀ => z ≫ j.hom.hom)
    ((e.app R₀).groupIsoToMulEquiv.symm_apply_apply p)

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneHom_upper (j : A.val ⟶ G.val) (e : SpecialMatrixPoints A 2)
    (x : F) :
    rankOneHom j e (splitUpper x) = transvectionPoint j e R₀
      (i := ⟨0⟩) (k := ⟨1⟩) (by decide) x := by
  exact congrArg (transvectionHom (R := R₀) j e)
    (reindexTransvection (R := F) 0 1 (by decide) x)

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneHom_lower (j : A.val ⟶ G.val) (e : SpecialMatrixPoints A 2)
    (x : F) :
    rankOneHom j e (splitLower x) = transvectionPoint j e R₀
      (i := ⟨1⟩) (k := ⟨0⟩) (by decide) x := by
  exact congrArg (transvectionHom (R := R₀) j e)
    (reindexTransvection (R := F) 1 0 (by decide) x)

variable [TopologicalSpace F] in
set_option backward.isDefEq.respectTransparency false in
/-- Specializing a transvection over the polynomial algebra gives a continuous curve. -/
private theorem continuous_transvectionPoint [IsTopologicalRing F]
    (j : A.val ⟶ G.val) (e : SpecialMatrixPoints A 2)
    {i k : RankOneIndex.{u}} (hik : i ≠ k) :
    @Continuous F (GroupPoints G.val R₀) _ (pointTopology G.val.X)
      (fun x : F => transvectionPoint j e R₀ hik x) := by
  let p := transvectionPoint j e (polynomialAlgebra R₀) hik Polynomial.X
  have h := continuous_polynomialPoint G.val.X p
  have he (x : F) :
      mapPoints (polynomialEvaluate R₀ x) p = transvectionPoint j e R₀ hik x := by
    rw [show p = transvectionPoint j e (polynomialAlgebra R₀) hik Polynomial.X from rfl,
      transvectionPoint_natural]
    have hx : (polynomialEvaluate R₀ x).hom (Polynomial.X : Polynomial F) = x :=
      Polynomial.aevalTower_X _ _
    rw [hx]
  simpa only [he] using h

/-- The original regular cocharacter contracts one of the two marked lines. -/
private def HasContractedTransvection (c : Cocharacter G.val)
    (J : SpecialLinearGroup (Fin 2) F →* RationalPoints G.val.X) : Prop :=
  (∀ t : F, HasLimit (oppositeCocharacter c) (J (splitUpper t)) 1) ∨
    (∀ t : F, HasLimit (oppositeCocharacter c) (J (splitLower t)) 1)

private theorem rankOneDiagonal_mem_range (j : A.val ⟶ G.val) (e : SpecialMatrixPoints A 2)
    (b : Cocharacter A.val) (t : Fˣ) :
    cocharacterPoint (b ≫ j) R₀ t ∈ (rankOneHom j e).range := by
  rw [cocharacterPoint_comp]
  exact rankOneHom_point j e (cocharacterPoint b R₀ t)

/-- The diagonal and its inverse contract the two sets of radical points. -/
private theorem contraction_from_diagonal
    {J : SpecialLinearGroup (Fin 2) F →* RationalPoints G.val.X}
    (d : Cocharacter G.val) (hDiag : ∀ t : Fˣ, cocharacterPoint d R₀ t ∈ J.range)
    (π : Fˣ) (x : RationalPoints G.val.X)
    (hx : HasLimit d x 1 ∨ HasLimit (oppositeCocharacter d) x 1) :
    ∃ b : SpecialLinearGroup (Fin 2) F, ∃ c : Cocharacter G.val,
      J b = cocharacterPoint c R₀ π ∧ HasLimit (oppositeCocharacter c) x 1 := by
  rcases hx with h | h
  · obtain ⟨b, hb⟩ := hDiag π⁻¹
    exact ⟨b, oppositeCocharacter d, hb.trans (opposite_point d R₀ π).symm,
      by simpa only [opposite_opposite] using h⟩
  · obtain ⟨b, hb⟩ := hDiag π
    exact ⟨b, d, hb, h⟩

variable [TopologicalSpace F]

private def HasRankOneMixingData (c : Cocharacter G.val) : Prop :=
  ∃ (A : AffineAlgebraicGroup F) (j : A.val ⟶ G.val) (e : SpecialMatrixPoints A 2)
    (d : Cocharacter G.val),
    (∀ t : Fˣ, cocharacterPoint d R₀ t ∈ (rankOneHom j e).range) ∧
    HasContractedTransvection c (rankOneHom j e) ∧
    @Dense (GroupPoints G.val R₀) (pointTopology G.val.X)
      (oppositeWords d : Set (GroupPoints G.val R₀))

/-- The limit on every finite-measure closed-subgroup quotient for the given
cocharacter and uniformizer. -/
private def QuotientMixingAt (c : Cocharacter G.val) (π : Fˣ) : Prop :=
  letI := pointTopology G.val.X
  let a : RationalPoints G.val.X := cocharacterPoint c R₀ π
  ∀ (H : Subgroup (RationalPoints G.val.X)), IsClosed (H : Set (RationalPoints G.val.X)) →
    ∀ (ν : Measure (LocalQuotientTransport.RightCosets H)) [IsFiniteMeasure ν], ν ≠ 0 →
      ∀ (hν : LocalQuotientTransport.RightInvariant ν) (f g : LocalQuotientTransport.L2 ν),
        Tendsto (fun n : ℕ => ⟪g, LocalQuotientTransport.rightOperator hν (a ^ n) f⟫_ℂ) atTop
          (𝓝 (((∫ x, f x ∂ν) * (∫ x, star (g x) ∂ν)) / ((ν Set.univ).toReal : ℂ)))

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]

set_option backward.isDefEq.respectTransparency false in
private theorem quotientMixing_of_rankOneData
    (hMautner : UpperRootFixedVector.{u,u}) (c : Cocharacter G.val)
    (π : Fˣ) (hπ : IsUniformizingUnit π) (h : HasRankOneMixingData c) :
    QuotientMixingAt c π := by
  obtain ⟨A, j, e, d, hDiag, hroot, hgen⟩ := h
  let J (_ : PUnit.{u + 1}) := rankOneHom j e
  let s := {x : RationalPoints G.val.X | HasLimit d x 1 ∨ HasLimit (oppositeCocharacter d) x 1}
  apply localQuotient_mixing_of_algebraic_contractions G hMautner c π hπ (PUnit.{u + 1}) J s
  · intro i
    simpa only [J, rankOneHom_upper] using continuous_transvectionPoint j e
      (i := ⟨0⟩) (k := ⟨1⟩) (by decide)
  · intro i
    simpa only [J, rankOneHom_lower] using continuous_transvectionPoint j e
      (i := ⟨1⟩) (k := ⟨0⟩) (by decide)
  · intro i
    exact hroot
  · exact hgen
  · intro x hx
    obtain ⟨b, c', he, hl⟩ := contraction_from_diagonal d hDiag π x hx
    exact ⟨PUnit.unit, b, c', he, hl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneData_of_hermitian (hG : IsAbsolutelyAlmostSimple G)
    (h : IsIsotropicSpecialUnitary G) (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : IsRegular S c) :
    HasRankOneMixingData (c ≫ S.inclusion) := by
  obtain ⟨E, _, _, _, _, n, H, hH, hiso, hmodel⟩ := h
  obtain ⟨A, j, e, b, _, _, _, _, hroot, hgen⟩ :=
    LocalMixingHermitianRankOne.hermitianRankOne F G hG E H hH hiso hmodel S hS c hc
  refine ⟨A, j, e, b ≫ j, rankOneDiagonal_mem_range j e b, ?_, hgen⟩
  simpa only [HasContractedTransvection, rankOneHom_upper, rankOneHom_lower] using hroot

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneData_of_quadraticSpin (hG : IsAbsolutelyAlmostSimple G)
    (h : IsIsotropicQuadraticSpin G) (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : IsRegular S c) :
    HasRankOneMixingData (c ≫ S.inclusion) := by
  obtain ⟨V, _, _, _, q, ρ, hrank, hreg, hiso, hmodel⟩ := h
  obtain ⟨_, _, _, A, j, _, e, b, _, _, _, hroot, hgen⟩ :=
    LocalMixingQuadraticSpinRankOne.quadraticSpinRankOne F G hG V q ρ hrank hreg hiso hmodel S hS c hc
  refine ⟨A, j, e, b ≫ j, rankOneDiagonal_mem_range j e b, ?_, hgen⟩
  simpa only [HasContractedTransvection, rankOneHom_upper, rankOneHom_lower, transvectionPoint,
    Specs.Arithmetic.LocalMixingQuadraticSpinRankOne.upper,
    Specs.Arithmetic.LocalMixingQuadraticSpinRankOne.lower] using hroot

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneData_of_quaternionSpin (hG : IsAbsolutelyAlmostSimple G)
    (h : IsIsotropicQuaternionicSpin G) (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : IsRegular S c) :
    HasRankOneMixingData (c ≫ S.inclusion) := by
  obtain ⟨K, I, B, _, _, _, _, _, _, _, _, ρ, D, hB, d, hrank, hdeg, hd, ⟨M⟩, ⟨Q⟩⟩ := h
  obtain ⟨A, e, j, b, _, _, _, _, _, hroot, hgen⟩ :=
    LocalMixingQuaternionSpinRankOne.quaternionSpinRankOne M hG hrank hB hdeg hd Q S hS c hc
  refine ⟨A, j, e, b ≫ j, rankOneDiagonal_mem_range j e b, ?_, hgen⟩
  have hincl (p : GroupPoints A.val R₀) :
      ((groupPointsFunctor F).map j).app R₀ p = p ≫ j.hom.hom := rfl
  simpa only [HasContractedTransvection, rankOneHom_upper, rankOneHom_lower, transvectionPoint,
    hincl] using hroot

open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.QuasiSplitLocalGeneration (IsLocalField)
open Specs.ExceptionalLocalRadicalGeneration (HasAbsoluteTypeE localPointTopology)
open Specs.ExceptionalMarkedRootDescent (coordinatePointEquiv)
open Specs.QuasiSplitOrbitAmbientWords (groundPointIso)
open private pairing_inv from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private opposite_pairing from LinearAlgebraicGroups.Classification.RankTwoRelations
open private rootPoint_hasLimit from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private subgroupInclusionFactors centralizes_hasLimit
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private isIso_of_section from LinearAlgebraicGroups.Relative.RelativeChambers
open private testPointSections from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso from LinearAlgebraicGroups.Relative.RationalDensity
open private rational_limit_mem localField_infinite
  from LinearAlgebraicGroups.Arithmetic.LocalMixingHermitianRankOne

variable {S : ClosedSubgroup G.val}

omit [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] in
set_option backward.isDefEq.respectTransparency false in
private theorem rankOne_contractedHalf
    (hS : IsMaximalSplitTorus S) (c : Cocharacter S.group) (hc : IsRegular S c)
    (a : relativeRoots S) (L : RankOne S) (hL : IsRankOneAt S a L) :
    HasContractedTransvection (c ≫ S.inclusion) (rankOneHom L.embedding L.matrix) := by
  have he : oppositeCocharacter (c ≫ S.inclusion) = oppositeCocharacter c ≫ S.inclusion := by
    simp only [oppositeCocharacter, Category.assoc]
  rcases lt_or_gt_of_ne (hc a) with hneg | hpos
  · left
    intro x
    have hx : rankOneHom L.embedding L.matrix (splitUpper x) =
        rootPoint (L.upper.hom ≫ L.positive.inclusion) R₀ x :=
      (rankOneHom_upper L.embedding L.matrix x).trans (L.upperFormula R₀ x)
    rw [hx, he]
    apply rootPoint_hasLimit hL.1
    have h := opposite_pairing hS.1 a.val⁻¹ c
    rw [inv_inv, pairing_inv _ hS.1] at h
    exact h.symm ▸ neg_pos.mpr hneg
  · right
    intro x
    have hx : rankOneHom L.embedding L.matrix (splitLower x) =
        rootPoint (L.lower.hom ≫ L.negative.inclusion) R₀ x :=
      (rankOneHom_lower L.embedding L.matrix x).trans (L.lowerFormula R₀ x)
    rw [hx, he]
    apply rootPoint_hasLimit hL.2.1
    rw [opposite_pairing hS.1]
    exact hpos

omit [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem markedDiagonal_mem_range (L : RankOne S) (t : Fˣ) :
    cocharacterPoint (L.cochar ≫ S.inclusion) R₀ t ∈
      (rankOneHom L.embedding L.matrix).range := by
  obtain ⟨p, hp, _⟩ := L.diagonalFormula R₀ t
  rw [← hp]
  exact rankOneHom_point L.embedding L.matrix p

omit [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] in
set_option backward.isDefEq.respectTransparency false in
private theorem properLimit_noncentral {d : Cocharacter G.val} (D : LimitDecomposition d)
    (h : ¬ IsIso D.parabolic.inclusion) :
    ∃ (X : SchemeOver F) (g : X ⟶ G.val.X), ¬ Centralizes d g := by
  classical
  by_contra! hcentral
  obtain ⟨f, hf⟩ := subgroupInclusionFactors G.prop.1 D.parabolic (𝟙 G.val) (fun R x => by
    have hx : HasLimit d x x := centralizes_hasLimit d (hcentral _ x)
    obtain ⟨z, hz⟩ := (D.parabolic_points R x).mp ⟨x, hx⟩
    refine ⟨z, ?_⟩
    change ((groupPointsFunctor F).map D.parabolic.inclusion).app R z = x ≫ 𝟙 G.val.X
    exact hz.trans (Category.comp_id x).symm)
  exact h (isIso_of_section _ f hf)

omit [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] in
private theorem evaluate_section (x : (𝟙_ (SchemeOver F)) ⟶ G.val.X) :
    (testPointSections G.val).symm x = toUnit ((testSpec F).obj (.op R₀)) ≫ x := by
  change (rationalSourceIso F).inv ≫ x = _
  rw [toUnit_unique (rationalSourceIso F).inv (toUnit ((testSpec F).obj (.op R₀)))]

private theorem subgroup_join_image {K M : Type*} [Group K] [Group M]
    (e : K →* M) (U V W : Subgroup K) (h : U ⊔ V = W) (s t : Set M)
    (hs : ∀ y ∈ U, e y ∈ s) (ht : ∀ y ∈ V, e y ∈ t) {x : K} (hx : x ∈ W) :
    e x ∈ Subgroup.closure (s ∪ t) := by
  let B := (Subgroup.closure (s ∪ t)).comap e
  have hU : U ≤ B := fun y hy => Subgroup.subset_closure (Or.inl (hs y hy))
  have hV : V ≤ B := fun y hy => Subgroup.subset_closure (Or.inr (ht y hy))
  have hW : W ≤ B := h ▸ sup_le hU hV
  exact hW hx

set_option backward.isDefEq.respectTransparency false in
private theorem generatedRadicals_contained (hG : IsAbsolutelyAlmostSimple G)
    (d : Cocharacter G.val)
    (P : LimitDecomposition d) (Q : LimitDecomposition (oppositeCocharacter d))
    (hProper : ¬ IsIso P.parabolic.inclusion) (x : (𝟙_ (SchemeOver F)) ⟶ G.val.X)
    (hx : x ∈ unipotentGenerated G) : (testPointSections G.val).symm x ∈ oppositeWords d := by
  let : Infinite F := localField_infinite F
  have hUV := RelativeRayGeneration.twoRadicalsGenerate G hG d (properLimit_noncentral P hProper) P Q
  exact subgroup_join_image (testPointSections G.val).symm.toMonoidHom _ _ _ hUV
    {g : GroupPoints G.val R₀ | HasLimit d g 1}
    {g : GroupPoints G.val R₀ | HasLimit (oppositeCocharacter d) g 1}
    (rational_limit_mem P) (rational_limit_mem Q) hx

set_option backward.isDefEq.respectTransparency false in
private theorem dense_diagonal_radicals (hG : IsAbsolutelyAlmostSimple G)
    (hDense : HasDenseRadicals G) (d : Cocharacter G.val)
    (P : LimitDecomposition d) (Q : LimitDecomposition (oppositeCocharacter d))
    (hProper : ¬ IsIso P.parabolic.inclusion) :
    @Dense (GroupPoints G.val R₀) (pointTopology G.val.X)
      (oppositeWords d : Set (GroupPoints G.val R₀)) := by
  let : TopologicalSpace (RationalPoints G.val.X) := pointTopology G.val.X
  refine hDense.mono ?_
  rintro x ⟨a, ha, hx⟩
  have he : (testPointSections G.val).symm a = x := (evaluate_section a).trans hx
  exact he ▸ generatedRadicals_contained hG d P Q hProper a ha

set_option backward.isDefEq.respectTransparency false in
private theorem rankOneData_of_denseRadicals (hG : IsAbsolutelyAlmostSimple G)
    (hDense : HasDenseRadicals G) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : IsRegular S c)
    (a : relativeRoots S) (L : RankOne S) (hL : IsRankOneAt S a L) :
    HasRankOneMixingData (c ≫ S.inclusion) := by
  let d := L.cochar ≫ S.inclusion
  obtain ⟨P, Q, _, _, hProper, _⟩ := hL.2.2
  exact ⟨L.group, L.embedding, L.matrix, d, markedDiagonal_mem_range L,
    rankOne_contractedHalf hS c hc a L hL, dense_diagonal_radicals hG hDense d P Q hProper⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quotientMixing_of_split (hMautner : UpperRootFixedVector.{u,u})
    (hG : IsAbsolutelyAlmostSimple G) (hSC : GeometricallySimplyConnected G)
    (hsplit : IsSplitReductive G) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (hc : IsRegular S c) (π : Fˣ) (hπ : IsUniformizingUnit π) :
    QuotientMixingAt (c ≫ S.inclusion) π := by
  classical
  let : TopologicalSpace (RationalPoints G.val.X) := pointTopology G.val.X
  obtain ⟨hmax, hfamily⟩ := LocalMixingSingletonRootSL2.splitCase F G hG hSC hsplit S hS
  choose L hL hUpper hLower using fun a => (hfamily a).2
  let J (a : relativeRoots S) := rankOneHom (L a).embedding (L a).matrix
  let generators := {x : GroupPoints G.val R₀ |
    ∃ α ∈ absoluteRoots S, ∃ U : ClosedSubgroup G.val, IsRootSubgroup S U α ∧
      ∃ p : GroupPoints U.group R₀, p ≫ U.inclusion.hom.hom = x}
  have hgen : Subgroup.closure generators = ⊤ :=
    SplitLocalGeneration.splitLocalGeneration G hG.1 hSC S hS.1 hmax
  apply localQuotient_mixing_of_algebraic_contractions G hMautner (c ≫ S.inclusion) π hπ
    (relativeRoots S) J generators
  · intro a
    simpa only [J, rankOneHom_upper] using continuous_transvectionPoint (L a).embedding (L a).matrix
      (i := ⟨0⟩) (k := ⟨1⟩) (by decide)
  · intro a
    simpa only [J, rankOneHom_lower] using continuous_transvectionPoint (L a).embedding (L a).matrix
      (i := ⟨1⟩) (k := ⟨0⟩) (by decide)
  · intro a
    exact rankOne_contractedHalf hS c hc a (L a) (hL a)
  · rw [hgen]
    exact dense_univ
  · rintro x ⟨α, hα, U, hU, p, rfl⟩
    let a : relativeRoots S := ⟨α, hα⟩
    let d := (L a).cochar ≫ S.inclusion
    obtain ⟨P, Q, _, _, _, _, _, _, _, _, hInc, _⟩ := (hL a).2.2
    have hred := reductive_of_semisimple G hG.1
    obtain ⟨_, _, V, _, _, _, _, hV⟩ :=
      (_root_.LinearAlgebraicGroups.RootData.RootGroups.rootSubgroups G hred S hS.1 hmax).2 α hα
    have hUP : IsSubgroupOf U P.contracting :=
      subgroupOf_trans (subgroupOf_trans (hV U hU).2 (hV _ (hUpper a)).1) hInc
    obtain ⟨i, hi⟩ := hUP
    have hx : HasLimit d (p ≫ U.inclusion.hom.hom) 1 := by
      apply (P.contracting_points R₀ _).mpr
      refine ⟨p ≫ i.hom.hom, ?_⟩
      calc
        _ = p ≫ (i ≫ P.contracting.inclusion).hom.hom := Category.assoc _ _ _
        _ = _ := congrArg (fun k : U.group ⟶ G.val => p ≫ k.hom.hom) hi
    obtain ⟨b, c', hb, hl⟩ := contraction_from_diagonal d (markedDiagonal_mem_range (L a))
      π _ (Or.inl hx)
    exact ⟨a, b, c', hb, hl⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
set_option backward.isDefEq.respectTransparency false in
/-- Terminal sections and rational test-algebra points carry the same local topology. -/
private theorem denseRadicals_of_terminalSections
    (h : @Dense ((𝟙_ (SchemeOver F)) ⟶ G.val.X) (localPointTopology G)
      (unipotentGenerated G : Set _)) : HasDenseRadicals G := by
  let : TopologicalSpace ((𝟙_ (SchemeOver F)) ⟶ G.val.X) := localPointTopology G
  let : TopologicalSpace (GroupPoints G.val R₀) := pointTopology G.val.X
  let : TopologicalSpace (RationalPoints G.val.X) := pointTopology G.val.X
  let B : TestAlgebra F := CommAlgCat.of F (Specs.AdjointCocharacters.coordinateHopf G)
  let : TopologicalSpace (B →ₐ[F] F) := Specs.ExceptionalIwahoriCongruence.affinePointTopology F B F
  let e : (testSpec F).obj (.op B) ≅ G.val.X :=
    (Grp.forget (SchemeOver F)).mapIso (Specs.AdjointCocharacters.coordinateHopfIso G)
  obtain ⟨H, hH⟩ := affinePoints_homeomorph G.val.X B e
  let f := (testPointSections G.val).symm
  have hf : Continuous f := by
    have hh : (groundPointIso F).inv = toUnit ((testSpec F).obj (.op R₀)) :=
      toUnit_unique _ _
    have hcomp : (f : ((𝟙_ (SchemeOver F)) ⟶ G.val.X) → RationalPoints G.val.X) =
        fun x => H (((coordinatePointEquiv G R₀).symm
        ((groundPointIso F).inv ≫ x)).ofConv) := by
      funext x
      let p := (coordinatePointEquiv G R₀).symm ((groundPointIso F).inv ≫ x)
      calc
        f x = toUnit ((testSpec F).obj (.op R₀)) ≫ x := evaluate_section x
        _ = (groundPointIso F).inv ≫ x := congrArg (fun a => a ≫ x) hh.symm
        _ = coordinatePointEquiv G R₀ p := ((coordinatePointEquiv G R₀).apply_symm_apply _).symm
        _ = H p.ofConv := (hH p.ofConv).symm
    rw [hcomp]
    exact H.continuous.comp continuous_induced_dom
  refine (f.surjective.denseRange.dense_image hf h).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx, (evaluate_section x).symm⟩

private theorem quasiSplitPointDensity (hG : IsAbsolutelyAlmostSimple G)
    (hSC : GeometricallySimplyConnected G) (hq : IsQuasiSplit G) : HasDenseRadicals G := by
  let : TopologicalSpace ((𝟙_ (SchemeOver F)) ⟶ G.val.X) := localPointTopology G
  have hF : IsLocalField F := Or.inl ⟨inferInstance, inferInstance, inferInstance⟩
  have ht : unipotentGenerated G = ⊤ :=
    QuasiSplitRadicalGeneration.quasiSplitRadicalGeneration hF G hG.1 hSC hq
  apply denseRadicals_of_terminalSections
  rw [ht, Subgroup.coe_top]
  exact dense_univ

set_option backward.isDefEq.respectTransparency false in
/-- Mixing for the original local group and its closed-subgroup quotients. -/
theorem localQuotientMixing_conditional
    (systems : ExceptionalRootSystemsAndLevis.{u}) (generation : LocalRadicalGeneration.{u}) :
    Statement.{u} := by
  intro F _ _ _ _ G hG hcases S hS c hc π hπ
  have hMautner := upperRootFixedVector_conditional.{u,u} systems generation
  rcases hcases with ⟨hsplit, hSC⟩ | hunitary | hspin | hquat | ⟨hSC, hcases⟩
  · exact quotientMixing_of_split hMautner hG hSC hsplit hS c hc π hπ
  · exact quotientMixing_of_rankOneData hMautner _ π hπ (rankOneData_of_hermitian hG hunitary S hS c hc)
  · exact quotientMixing_of_rankOneData hMautner _ π hπ (rankOneData_of_quadraticSpin hG hspin S hS c hc)
  · exact quotientMixing_of_rankOneData hMautner _ π hπ (rankOneData_of_quaternionSpin hG hquat S hS c hc)
  · have mix (hd : HasDenseRadicals G) (a : relativeRoots S) (L : RankOne S) (hL : IsRankOneAt S a L) :=
      quotientMixing_of_rankOneData hMautner _ π hπ (rankOneData_of_denseRadicals hG hd hS c hc a L hL)
    have mixHighest (hd : HasDenseRadicals G) (h : IsExceptionalCase G ∨ IsTrialitarianCase G) :
        QuotientMixingAt (c ≫ S.inclusion) π := by
      have hh := exceptionalAndTrialitarianRankOne_conditional systems generation F G hG hSC h S hS
      obtain ⟨_, a, L, _, _, _, _, hL, _⟩ := hh.2.2
      exact mix hd a L hL
    rcases hcases with hexc | htrial | ⟨hd, T, hT, a, _, hsingle⟩
    · have ht : HasAbsoluteTypeE G 6 ∨ HasAbsoluteTypeE G 7 ∨ HasAbsoluteTypeE G 8 := by
        rcases hexc with ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨h, _⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
      exact mixHighest (denseRadicals_of_terminalSections (generation F G hG hSC ht).2) (Or.inl hexc)
    · exact mixHighest (quasiSplitPointDensity hG hSC htrial.2) (Or.inr htrial)
    · obtain ⟨g, e, he⟩ := Relative.MaximalSplitTori.maximalSplitToriConjugate G
        (reductive_of_semisimple G hG.1) T S hT hS
      obtain ⟨hb, hiff⟩ := LocalMixingSingletonRootSL2.conjugationInvariance F G hG hSC
        T S hT hS g e he a
      let b : relativeRoots S := ⟨e.inv ≫ a.val, hb⟩
      obtain ⟨L, hL⟩ := LocalMixingSingletonRootSL2.singletonRootSL2 F G hG hSC S hS b (hiff.mp hsingle)
      exact mix hd b L hL

end RankOneDynamics

end LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing

universe v8_closure_aa97d9d086e8fc54_u0 v8_closure_aa97d9d086e8fc54_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«exceptionalAndTrialitarianRankOne» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«LocalQuotientMixing».«ExceptionalAndTrialitarianRankOne».{v8_closure_aa97d9d086e8fc54_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«exceptionalAndTrialitarianRankOne_conditional».{v8_closure_aa97d9d086e8fc54_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«exceptionalRootSystemsAndLevis».{v8_closure_aa97d9d086e8fc54_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«localRadicalGeneration».{v8_closure_aa97d9d086e8fc54_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«localQuotientMixing» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«LocalQuotientMixing».«Statement».{v8_closure_aa97d9d086e8fc54_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«localQuotientMixing_conditional».{v8_closure_aa97d9d086e8fc54_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«exceptionalRootSystemsAndLevis».{v8_closure_aa97d9d086e8fc54_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«localRadicalGeneration».{v8_closure_aa97d9d086e8fc54_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«longRootRankOne» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«LocalQuotientMixing».«LongRootRankOne».{v8_closure_aa97d9d086e8fc54_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«longRootRankOne_conditional».{v8_closure_aa97d9d086e8fc54_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«exceptionalRootSystemsAndLevis».{v8_closure_aa97d9d086e8fc54_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«localRadicalGeneration».{v8_closure_aa97d9d086e8fc54_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«upperRootFixedVector» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«LocalQuotientMixing».«UpperRootFixedVector».{v8_closure_aa97d9d086e8fc54_u0, v8_closure_aa97d9d086e8fc54_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«upperRootFixedVector_conditional».{v8_closure_aa97d9d086e8fc54_u0, v8_closure_aa97d9d086e8fc54_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«exceptionalRootSystemsAndLevis».{v8_closure_aa97d9d086e8fc54_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalLocalRadicalGeneration».«localRadicalGeneration».{v8_closure_aa97d9d086e8fc54_u0})
