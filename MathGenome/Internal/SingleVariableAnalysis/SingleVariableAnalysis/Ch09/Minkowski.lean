import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Minkowski
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Holder

/-!
Minkowski for the proper Darboux integral, K03.09.minkowski.
Apply finite weighted Minkowski to each tagged partition and pass to the
Darboux values using a common sequence of meshes tending to zero. This route
uses the finite Hölder-based library proof, including p=1 and zero sums.
No Riemann/Lebesgue comparison or quotient of functions is needed.
-/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology
open Filter
namespace M
export Specs.SingleVariableAnalysis.Ch09.Minkowski (lpSeminormValue pointSpikeValue)
end M

noncomputable def lpSeminorm : Specs.SingleVariableAnalysis.Ch09.Minkowski.lpSeminormType :=
  @M.lpSeminormValue
noncomputable def pointSpike : Specs.SingleVariableAnalysis.Ch09.Minkowski.pointSpikeType :=
  @M.pointSpikeValue

/-- Nonnegativity and absolute homogeneity hold even at zero seminorm. -/
theorem lp_seminorm_laws : Specs.SingleVariableAnalysis.Ch09.Minkowski.seminormLaws := by
  intro K _ p hp f a b hf
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hI : 0 ≤ realIntegral _ hf :=
    realIntegral_nonneg hf (fun x _ => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨Real.rpow_nonneg hI _, ?_⟩
  intro c
  have hfun : (fun x => ‖c * f x‖ ^ p) = (fun x => ‖c‖ ^ p * ‖f x‖ ^ p) := by
    funext x
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  obtain ⟨hc, he⟩ : ∃ hc : RealIntegrable (fun x => ‖c * f x‖ ^ p) a b,
      realIntegral _ hc = ‖c‖ ^ p * realIntegral _ hf := by
    simpa only [hfun] using real_mul_value hf (‖c‖ ^ p)
  refine ⟨hc, ?_⟩
  change realIntegral _ hc ^ (1 / p) = ‖c‖ * realIntegral _ hf ^ (1 / p)
  rw [he, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) hI]
  congr 1
  simpa only [one_div] using Real.rpow_rpow_inv (norm_nonneg c) hp0.ne'

/-- Finite Minkowski with nonnegative cell-length weights. -/
theorem weighted_minkowski {ι : Type*} (s : Finset ι) (w u v : ι → ℝ)
    {p : ℝ} (hp : 1 ≤ p) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) :
    (∑ i ∈ s, w i * (u i + v i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, w i * u i ^ p) ^ (1 / p) +
      (∑ i ∈ s, w i * v i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h := Real.Lp_add_le_of_nonneg s (p := p) hp
    (f := fun i => w i ^ (1 / p) * u i)
    (g := fun i => w i ^ (1 / p) * v i)
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hu i hi))
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hw i hi) _) (hv i hi))
  have hpower (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
      (∑ i ∈ s, (w i ^ (1 / p) * z i) ^ p) = ∑ i ∈ s, w i * z i ^ p := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i hi) _) (hz i hi)]
    congr 1
    simpa only [one_div] using Real.rpow_inv_rpow (hw i hi) hp0.ne'
  simp_rw [← mul_add] at h
  rwa [hpower (fun i => u i + v i) (fun i hi => add_nonneg (hu i hi) (hv i hi)),
    hpower u hu, hpower v hv] at h

/-- Only integrability of the three powered norms is needed for the inequality. -/
theorem minkowski_of_power_integrable {K : Type} [NormedAddCommGroup K]
    {f g : ℝ → K} {a b p : ℝ} (hp : 1 ≤ p)
    (hf : RealIntegrable (fun x => ‖f x‖ ^ p) a b)
    (hg : RealIntegrable (fun x => ‖g x‖ ^ p) a b)
    (hs : RealIntegrable (fun x => ‖f x + g x‖ ^ p) a b) :
    lpSeminorm (fun x => f x + g x) p hs ≤
      lpSeminorm f p hf + lpSeminorm g p hg := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hr : 0 ≤ 1 / p := by positivity
  obtain ⟨P, ξ, hm⟩ := exists_tagged_partition_sequence hf.ordered
  have hlim {h : ℝ → ℝ} (hh : RealIntegrable h a b) :
      Tendsto (fun n => taggedSum (P n) (ξ n) h ^ (1 / p)) atTop
        (𝓝 (realIntegral h hh ^ (1 / p))) :=
    ((Real.continuous_rpow_const hr).tendsto _).comp
      (((real_tagged_equivalence h hh.ordered hh.bounded _).mp ⟨hh, rfl⟩).tendsto P ξ hm)
  apply le_of_tendsto_of_tendsto (hlim hs) ((hlim hf).add (hlim hg))
  apply Filter.Eventually.of_forall
  intro n
  have hnorm :
      (∑ i : Fin (P n).n, cellLength (P n) i * ‖f (ξ n i) + g (ξ n i)‖ ^ p) ^ (1 / p) ≤
      (∑ i : Fin (P n).n, cellLength (P n) i * (‖f (ξ n i)‖ + ‖g (ξ n i)‖) ^ p) ^ (1 / p) := by
    apply Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (cell_positive _ _).le (Real.rpow_nonneg (norm_nonneg _) _))) _ hr
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp0) (cell_positive _ _).le
  have hfinite := weighted_minkowski Finset.univ (cellLength (P n))
    (fun i => ‖f (ξ n i)‖) (fun i => ‖g (ξ n i)‖) hp
    (fun i _ => (cell_positive _ _).le) (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
  simpa only [taggedSum, S.sumValue, smul_eq_mul, Function.comp_apply] using hnorm.trans hfinite

theorem real_minkowski : Specs.SingleVariableAnalysis.Ch09.Minkowski.realMinkowski := by
  intro p hp f g a b hf hg
  have hs := (real_add_value hf hg).choose
  have hfp := (RealIntegrable.norm hf).rpow (zero_le_one.trans hp)
  have hgp := (RealIntegrable.norm hg).rpow (zero_le_one.trans hp)
  have hsp := (RealIntegrable.norm hs).rpow (zero_le_one.trans hp)
  exact ⟨hfp, hgp, hsp, minkowski_of_power_integrable hp hfp hgp hsp⟩

theorem complex_minkowski : Specs.SingleVariableAnalysis.Ch09.Minkowski.complexMinkowski := by
  intro p hp f g a b hf hg
  have hs := (complex_add_value hf hg).choose
  have hfp := (ComplexIntegrable.norm hf).rpow (zero_le_one.trans hp)
  have hgp := (ComplexIntegrable.norm hg).rpow (zero_le_one.trans hp)
  have hsp := (ComplexIntegrable.norm hs).rpow (zero_le_one.trans hp)
  exact ⟨hfp, hgp, hsp, minkowski_of_power_integrable hp hfp hgp hsp⟩

/-- Only the first cell can have the left endpoint as a tag. Thus the norm
of a tagged sum of an endpoint spike is at most its height times the mesh. -/
theorem taggedSum_pointSpike_bound (c : ℝ) {a b : ℝ}
    (P : Partition a b) (ξ : Tagging P) :
    ‖taggedSum P ξ (pointSpike c a)‖ ≤ |c| * mesh P := by
  classical
  by_cases hn : P.n = 0
  · have he : taggedSum P ξ (pointSpike c a) = 0 := by
      simp only [taggedSum, S.sumValue]
      exact Finset.sum_eq_zero (fun i _ => False.elim (by have := i.isLt; omega))
    rw [he, norm_zero]
    exact mul_nonneg (abs_nonneg _) (mesh_nonneg _)
  · let i₀ : Fin P.n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hzero (i : Fin P.n) (hi : i ≠ i₀) : pointSpike c a (ξ i) = 0 := by
      have hpos : 0 < i.val := by
        have hne : i.val ≠ 0 := by
          intro he
          apply hi
          exact Fin.ext he
        omega
      have hlt : a < P.point i.castSucc := by
        simpa only [P.first] using
          P.strictMono (show (0 : Fin (P.n + 1)) < i.castSucc from hpos)
      have hne : (ξ i : ℝ) ≠ a := ne_of_gt (hlt.trans_le (ξ i).property.1)
      simp [pointSpike, M.pointSpikeValue, hne]
    have he : taggedSum P ξ (pointSpike c a) =
        cellLength P i₀ * pointSpike c a (ξ i₀) := by
      simp only [taggedSum, S.sumValue, smul_eq_mul]
      exact Finset.sum_eq_single i₀ (fun i _ hi => by rw [hzero i hi, mul_zero])
        (fun hi => False.elim (hi (Finset.mem_univ _)))
    have hheight : |pointSpike c a (ξ i₀)| ≤ |c| := by
      unfold pointSpike M.pointSpikeValue
      split_ifs <;> simp
    rw [he, Real.norm_eq_abs, abs_mul, abs_of_pos (cell_positive P i₀)]
    calc
      cellLength P i₀ * |pointSpike c a (ξ i₀)| ≤ cellLength P i₀ * |c| :=
        mul_le_mul_of_nonneg_left hheight (cell_positive P i₀).le
      _ ≤ |c| * mesh P := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (cellLength_le_mesh P i₀) (abs_nonneg c)

/-- Endpoint spikes have proper Darboux integral zero on every ordered interval. -/
theorem pointSpike_integral_zero (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ hi : RealIntegrable (pointSpike c a) a b, realIntegral _ hi = 0 := by
  have hb : BoundedOnInterval (pointSpike c a) a b := by
    apply boundedOnInterval_of_abs (M := |c|)
    intro x _
    unfold pointSpike M.pointSpikeValue
    split_ifs <;> simp
  apply (real_tagged_equivalence _ hab hb 0).mpr
  intro ε hε
  refine ⟨ε / (|c| + 1), by positivity, ?_⟩
  intro P ξ hm
  rw [sub_zero]
  have hbound := taggedSum_pointSpike_bound c P ξ
  have he := (lt_div_iff₀ (show 0 < |c| + 1 by positivity)).mp hm
  have hm0 := mesh_nonneg P
  nlinarith

/-- A positive power of the norm of a spike is again an endpoint spike. -/
theorem pointSpike_norm_rpow {K : Type} [NormedAddCommGroup K]
    (c : K) (a : ℝ) {p : ℝ} (hp : 0 < p) :
    (fun x => ‖pointSpike c a x‖ ^ p) = pointSpike (‖c‖ ^ p) a := by
  funext x
  by_cases hx : x = a
  · simp [pointSpike, M.pointSpikeValue, hx]
  · simp [pointSpike, M.pointSpikeValue, hx, Real.zero_rpow hp.ne']

theorem pointSpike_seminorm_zero {K : Type} [NormedAddCommGroup K]
    (c : K) {a b p : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) :
    ∃ hi : RealIntegrable (fun x => ‖pointSpike c a x‖ ^ p) a b,
      lpSeminorm (pointSpike c a) p hi = 0 := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨hi, he⟩ : ∃ hi : RealIntegrable (fun x => ‖pointSpike c a x‖ ^ p) a b,
      realIntegral _ hi = 0 := by
    simpa only [pointSpike_norm_rpow c a hp0] using
      pointSpike_integral_zero (‖c‖ ^ p) hab
  refine ⟨hi, ?_⟩
  change realIntegral _ hi ^ (1 / p) = 0
  rw [he, Real.zero_rpow (by positivity : 1 / p ≠ 0)]

theorem zero_lp_seminorm : Specs.SingleVariableAnalysis.Ch09.Minkowski.zeroSeminorm := by
  intro K _ p hp a b hab
  change ∃ hz : RealIntegrable (fun _ : ℝ => ‖(0 : K)‖ ^ p) a b,
    lpSeminorm (fun _ => (0 : K)) p hz = 0
  have he : pointSpike (0 : K) a = (fun _ => 0) := by
    funext x
    by_cases hx : x = a <;> simp [pointSpike, M.pointSpikeValue, hx]
  simpa only [he] using pointSpike_seminorm_zero (0 : K) hab hp

theorem real_point_spike : Specs.SingleVariableAnalysis.Ch09.Minkowski.realPointSpike := by
  intro a b hab c hc
  refine ⟨by simpa [M.pointSpikeValue] using hc,
    (fun x hx => by simp [M.pointSpikeValue, hx]), ?_⟩
  obtain ⟨hi, _⟩ := pointSpike_integral_zero c hab.le
  exact ⟨hi, fun p hp => pointSpike_seminorm_zero c hab.le hp⟩

theorem complex_point_spike : Specs.SingleVariableAnalysis.Ch09.Minkowski.complexPointSpike := by
  intro a b hab c hc
  refine ⟨by simpa [M.pointSpikeValue] using hc,
    (fun x hx => by simp [M.pointSpikeValue, hx]), ?_⟩
  have hr : (fun x => (pointSpike c a x).re) = pointSpike c.re a := by
    funext x
    by_cases hx : x = a <;> simp [pointSpike, M.pointSpikeValue, hx]
  have him : (fun x => (pointSpike c a x).im) = pointSpike c.im a := by
    funext x
    by_cases hx : x = a <;> simp [pointSpike, M.pointSpikeValue, hx]
  have hi : ComplexIntegrable (pointSpike c a) a b := by
    constructor
    · rw [hr]
      exact (pointSpike_integral_zero c.re hab.le).choose
    · rw [him]
      exact (pointSpike_integral_zero c.im hab.le).choose
  exact ⟨hi, fun p hp => pointSpike_seminorm_zero c hab.le hp⟩

end SingleVariableAnalysis.Riemann
