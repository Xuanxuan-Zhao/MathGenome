import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.CalderonZygmundDecomposition
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The corrected Calderón–Zygmund decomposition in positive Euclidean dimension.
Concrete dyadic maximal selection and differentiation establish the selected
family. Integration and disjoint-support convergence give the exact estimates
and the series identities in both L¹ and L², for real or complex scalars.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.SingularIntegrals.CZ

lemma side_pos {d : ℕ} (q : DyadicCube d) : 0 < side q := by
  exact zpow_pos (by norm_num) _

lemma cube_measurable {d : ℕ} (q : DyadicCube d) : MeasurableSet (cube q) := by
  unfold cube
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_Ico).preimage (by fun_prop)

lemma side_parent {d : ℕ} (q : DyadicCube d) : side (parent q) = 2 * side q := by
  simp only [side, parent, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

lemma cube_volume {d : ℕ} (q : DyadicCube d) :
    volume (cube q) = ENNReal.ofReal (side q ^ d) := by
  let S : Set (Fin d → ℝ) := Set.pi univ
    (fun i => Ico (side q * (q.2 i : ℝ)) (side q * ((q.2 i : ℝ) + 1)))
  have hS : MeasurableSet S := MeasurableSet.pi (Set.to_countable _) (fun i _ => measurableSet_Ico)
  have heq : cube q = WithLp.ofLp ⁻¹' S := by
    ext x
    simp [cube, S]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hS.nullMeasurableSet]
  dsimp only [S]
  rw [Real.volume_pi_Ico]
  simp only [show ∀ i : Fin d,
    side q * ((q.2 i : ℝ) + 1) - side q * (q.2 i : ℝ) = side q by intro i; ring]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (side_pos q).le d).symm

lemma cube_volume_pos {d : ℕ} (q : DyadicCube d) : 0 < volume (cube q) := by
  rw [cube_volume, ENNReal.ofReal_pos]
  exact pow_pos (side_pos q) _

lemma cube_volume_lt_top {d : ℕ} (q : DyadicCube d) : volume (cube q) < ∞ := by
  rw [cube_volume]
  exact ENNReal.ofReal_lt_top

lemma cube_subset_parent {d : ℕ} (q : DyadicCube d) : cube q ⊆ cube (parent q) := by
  intro x hx i
  have hxi := hx i
  have hlow : (q.2 i / 2 : ℤ) * 2 ≤ q.2 i := Int.ediv_mul_le _ (by norm_num)
  have hhigh : q.2 i < (q.2 i / 2 + 1 : ℤ) * 2 := by omega
  have hlow' : (q.2 i / 2 : ℤ) * (2 : ℝ) ≤ (q.2 i : ℝ) := by exact_mod_cast hlow
  have hhigh' : (q.2 i : ℝ) + 1 ≤ ((q.2 i / 2 : ℤ) + (1 : ℝ)) * 2 := by
    have : q.2 i + 1 ≤ (q.2 i / 2 + 1 : ℤ) * 2 := by omega
    exact_mod_cast this
  change side (parent q) * (q.2 i / 2 : ℤ) ≤ x i ∧
    x i < side (parent q) * ((q.2 i / 2 : ℤ) + 1)
  rw [side_parent]
  constructor
  · calc
      2 * side q * (q.2 i / 2 : ℤ) = side q * ((q.2 i / 2 : ℤ) * (2 : ℝ)) := by ring
      _ ≤ side q * (q.2 i : ℝ) := mul_le_mul_of_nonneg_left hlow' (side_pos q).le
      _ ≤ x i := hxi.1
  · calc
      x i < side q * ((q.2 i : ℝ) + 1) := hxi.2
      _ ≤ side q * (((q.2 i / 2 : ℤ) + (1 : ℝ)) * 2) :=
        mul_le_mul_of_nonneg_left hhigh' (side_pos q).le
      _ = 2 * side q * ((q.2 i / 2 : ℤ) + 1) := by ring

lemma cube_parent_volume {d : ℕ} (q : DyadicCube d) :
    volume (cube (parent q)) = 2 ^ d * volume (cube q) := by
  rw [cube_volume, side_parent, mul_pow, cube_volume,
    ENNReal.ofReal_mul (by positivity)]
  norm_num

lemma cube_eq_of_same_level_of_mem {d : ℕ} {q r : DyadicCube d}
    (hk : q.1 = r.1) {x : Point d} (hxq : x ∈ cube q) (hxr : x ∈ cube r) : q = r := by
  have hs : side q = side r := by simp only [side, hk]
  apply Prod.ext hk
  funext i
  have hqr : (q.2 i : ℝ) < (r.2 i : ℝ) + 1 := by
    have h : side q * (q.2 i : ℝ) < side q * ((r.2 i : ℝ) + 1) := by
      simpa only [hs] using (hxq i).1.trans_lt (hxr i).2
    exact (mul_lt_mul_iff_right₀ (side_pos q)).mp h
  have hrq : (r.2 i : ℝ) < (q.2 i : ℝ) + 1 := by
    have h : side q * (r.2 i : ℝ) < side q * ((q.2 i : ℝ) + 1) := by
      simpa only [hs] using (hxr i).1.trans_lt (hxq i).2
    exact (mul_lt_mul_iff_right₀ (side_pos q)).mp h
  have hqr' : q.2 i < r.2 i + 1 := by exact_mod_cast hqr
  have hrq' : r.2 i < q.2 i + 1 := by exact_mod_cast hrq
  omega

lemma ancestor_level {d : ℕ} (q : DyadicCube d) (n : ℕ) :
    (parent^[n] q).1 = q.1 + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', show (parent (parent^[n] q)).1 =
      (parent^[n] q).1 + 1 from rfl, ih]
    push_cast
    ring

lemma cube_subset_ancestor {d : ℕ} (q : DyadicCube d) (n : ℕ) :
    cube q ⊆ cube (parent^[n] q) := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (cube_subset_parent _)

lemma cube_nested_of_level_le {d : ℕ} {q r : DyadicCube d} (hk : q.1 ≤ r.1)
    (hqr : (cube q ∩ cube r).Nonempty) : cube q ⊆ cube r := by
  obtain ⟨x, hxq, hxr⟩ := hqr
  let n : ℕ := (r.1 - q.1).toNat
  have hn : q.1 + (n : ℤ) = r.1 := by dsimp only [n]; omega
  have heq : parent^[n] q = r := cube_eq_of_same_level_of_mem
    ((ancestor_level q n).trans hn) (cube_subset_ancestor q n hxq) hxr
  rw [← heq]
  exact cube_subset_ancestor q n

lemma cube_nested_or_disjoint {d : ℕ} (q r : DyadicCube d) :
    cube q ⊆ cube r ∨ cube r ⊆ cube q ∨ Disjoint (cube q) (cube r) := by
  by_cases h : Disjoint (cube q) (cube r)
  · exact Or.inr (Or.inr h)
  have hn : (cube q ∩ cube r).Nonempty := not_disjoint_iff_nonempty_inter.mp h
  rcases le_total q.1 r.1 with h | h
  · exact Or.inl (cube_nested_of_level_le h hn)
  · exact Or.inr (Or.inl (cube_nested_of_level_le h (by simpa [inter_comm] using hn)))

/-- Every point belongs to a cube of each integer level; no a.e. exception
is needed for this half-open convention. -/
lemma exists_cube_at_level {d : ℕ} (k : ℤ) (x : Point d) :
    ∃ q : DyadicCube d, q.1 = k ∧ x ∈ cube q := by
  let q : DyadicCube d := (k, fun i => ⌊x i / (2 : ℝ) ^ k⌋)
  refine ⟨q, rfl, ?_⟩
  intro i
  have hpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hl := Int.floor_le (x i / (2 : ℝ) ^ k)
  have hu := Int.lt_floor_add_one (x i / (2 : ℝ) ^ k)
  change (2 : ℝ) ^ k * (⌊x i / (2 : ℝ) ^ k⌋ : ℝ) ≤ x i ∧
    x i < (2 : ℝ) ^ k * ((⌊x i / (2 : ℝ) ^ k⌋ : ℝ) + 1)
  constructor
  · simpa only [mul_comm] using (le_div_iff₀ hpos).mp hl
  · simpa only [mul_comm] using (div_lt_iff₀ hpos).mp hu

lemma badPiece_support {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (q : DyadicCube d) :
    Function.support (badPiece f q) ⊆ cube q := by
  exact support_indicator_subset

lemma cubeAverage_integral_norm_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (q : DyadicCube d) :
    volume.real (cube q) * ‖cubeAverage f q‖ ≤ ∫ x in cube q, ‖f x‖ := by
  have hpos : 0 < volume.real (cube q) :=
    ENNReal.toReal_pos (cube_volume_pos q).ne' (cube_volume_lt_top q).ne
  rw [cubeAverage, setAverage_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
    ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  exact norm_integral_le_integral_norm _

lemma badPiece_integrable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume) (q : DyadicCube d)
    (hq : volume (cube q) < ∞) : Integrable (badPiece f q) volume := by
  unfold badPiece
  rw [integrable_indicator_iff (cube_measurable q)]
  exact hf.integrableOn.sub (integrableOn_const hq.ne)

lemma badPiece_integral {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (q : DyadicCube d)
    (hq : volume (cube q) < ∞) : (∫ x, badPiece f q x) = 0 := by
  rw [badPiece, integral_indicator (cube_measurable q)]
  exact setAverage_sub_setAverage hq.ne f

lemma badPiece_memLp {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (q : DyadicCube d)
    (hq : volume (cube q) < ∞) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hf : MemLp f p volume) : MemLp (badPiece f q) p volume := by
  unfold badPiece
  rw [indicator_sub]
  exact (hf.indicator (cube_measurable q).nullMeasurableSet).sub
    (memLp_indicator_const p (cube_measurable q).nullMeasurableSet _ (Or.inr hq.ne))

lemma badPiece_integral_norm_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume) (q : DyadicCube d) :
    (∫ x, ‖badPiece f q x‖) ≤ 2 * ∫ x in cube q, ‖f x‖ := by
  have hfin := cube_volume_lt_top q
  have hnorm : (fun x => ‖badPiece f q x‖) =
      (cube q).indicator (fun x => ‖f x - cubeAverage f q‖) := by
    ext x
    by_cases hx : x ∈ cube q <;> simp [badPiece, hx]
  rw [hnorm, integral_indicator (cube_measurable q)]
  calc
    _ ≤ ∫ x in cube q, (‖f x‖ + ‖cubeAverage f q‖) := by
      apply integral_mono
      · exact (hf.integrableOn.sub (integrableOn_const hfin.ne)).norm
      · exact hf.norm.integrableOn.add (integrableOn_const hfin.ne)
      · intro x
        exact norm_sub_le _ _
    _ = (∫ x in cube q, ‖f x‖) + volume.real (cube q) * ‖cubeAverage f q‖ := by
      rw [integral_add hf.norm.integrableOn (integrableOn_const hfin.ne), integral_const,
        MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul]
    _ ≤ 2 * ∫ x in cube q, ‖f x‖ := by
      linarith [cubeAverage_integral_norm_le f q]

lemma badPiece_eLpNorm_one_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume) (q : DyadicCube d) :
    eLpNorm (badPiece f q) 1 volume ≤ 2 * ∫⁻ x in cube q, ‖f x‖ₑ := by
  have hb := badPiece_integrable f hf q (cube_volume_lt_top q)
  rw [eLpNorm_one_eq_lintegral_enorm hb.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hb]
  have h := ENNReal.ofReal_le_ofReal (badPiece_integral_norm_le f hf q)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ofReal_integral_norm_eq_lintegral_enorm hf.integrableOn] at h
  simpa using h

lemma goodPart_outside {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (Q : Set (DyadicCube d)) (x : Point d)
    (hx : x ∉ badRegion Q) : goodPart f Q x = f x := by
  have hb (q : Q) : badPiece f q.1 x = 0 := by
    apply indicator_of_notMem
    intro h
    exact hx (mem_iUnion.mpr ⟨q, h⟩)
  simp [goodPart, hb]

lemma goodPart_inside {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube)
    (q : Q) (x : Point d) (hx : x ∈ cube q.1) :
    goodPart f Q x = cubeAverage f q.1 := by
  have hsum : (∑' r : Q, badPiece f r.1 x) = badPiece f q.1 x := by
    apply tsum_eq_single q
    intro r hr
    have hdis : Disjoint (cube r.1) (cube q.1) :=
      hd r.2 q.2 (fun h => hr (Subtype.ext h))
    apply indicator_of_notMem
    intro hxr
    exact Set.disjoint_left.mp hdis hxr hx
  change f x - (∑' r : Q, badPiece f r.1 x) = _
  rw [hsum]
  simp [badPiece, hx]

lemma cubeAverage_norm_le_of_selection {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) (Q : Set (DyadicCube d))
    (hQ : Selection f t Q) (q : Q) : ‖cubeAverage f q.1‖ ≤ 2 ^ d * t := by
  have hpos : 0 < volume.real (cube q.1) :=
    ENNReal.toReal_pos (cube_volume_pos q.1).ne' (cube_volume_lt_top q.1).ne
  have hnorm := cubeAverage_integral_norm_le f q.1
  have hu := hQ.upper q.1 q.2
  nlinarith

lemma goodPart_ae_norm_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) (ht : 0 < t) (Q : Set (DyadicCube d))
    (hQ : Selection f t Q) : ∀ᵐ x ∂volume, ‖goodPart f Q x‖ ≤ 2 ^ d * t := by
  filter_upwards [hQ.outside] with x hx
  by_cases h : x ∈ badRegion Q
  · obtain ⟨q, hq⟩ := mem_iUnion.mp h
    rw [goodPart_inside f Q hQ.disjoint q x hq]
    exact cubeAverage_norm_le_of_selection f t Q hQ q
  · rw [goodPart_outside f Q x h]
    exact (hx h).trans (le_mul_of_one_le_left ht.le (one_le_pow₀ (by norm_num)))

lemma selection_measure_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume) (t : ℝ) (ht : 0 < t)
    (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    (∑' q : Q, volume (cube q.1)) ≤ eLpNorm f 1 volume / ENNReal.ofReal t := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr ht).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [← ENNReal.tsum_mul_right]
  calc
    _ ≤ ∑' q : Q, ∫⁻ x in cube q.1, ‖f x‖ₑ := by
      apply ENNReal.tsum_le_tsum
      intro q
      have h := ENNReal.ofReal_le_ofReal (hQ.lower q.1 q.2).le
      simp only [measureReal_def] at h
      rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal (cube_volume_lt_top q.1).ne,
        ofReal_integral_norm_eq_lintegral_enorm hf.integrableOn] at h
      simpa [mul_comm] using h
    _ = ∫⁻ x in badRegion Q, ‖f x‖ₑ := by
      exact (lintegral_iUnion (fun q : Q => cube_measurable q.1)
        (hQ.disjoint.subtype _) _).symm
    _ ≤ ∫⁻ x, ‖f x‖ₑ := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = eLpNorm f 1 volume := (eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable).symm

lemma selection_bad_one_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume) (t : ℝ)
    (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    (∑' q : Q, eLpNorm (badPiece f q.1) 1 volume) ≤ 2 * eLpNorm f 1 volume := by
  calc
    _ ≤ ∑' q : Q, 2 * ∫⁻ x in cube q.1, ‖f x‖ₑ :=
      ENNReal.tsum_le_tsum (fun q => badPiece_eLpNorm_one_le f hf q.1)
    _ = 2 * ∫⁻ x in badRegion Q, ‖f x‖ₑ := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      exact (lintegral_iUnion (fun q : Q => cube_measurable q.1)
        (hQ.disjoint.subtype _) _).symm
    _ ≤ 2 * eLpNorm f 1 volume := by
      rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
      gcongr
      exact Measure.restrict_le_self


lemma badRegion_measurable {d : ℕ} (Q : Set (DyadicCube d)) :
    MeasurableSet (badRegion Q) :=
  MeasurableSet.iUnion (fun q : Q => cube_measurable q.1)

lemma goodPart_integrableOn_cube {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube)
    (q : Q) : IntegrableOn (goodPart f Q) (cube q.1) volume := by
  apply (integrableOn_const (C := cubeAverage f q.1) (cube_volume_lt_top q.1).ne).congr_fun
  · intro x hx
    exact (goodPart_inside f Q hd q x hx).symm
  · exact cube_measurable q.1

lemma goodPart_integral_norm_cube_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube)
    (q : Q) : (∫ x in cube q.1, ‖goodPart f Q x‖) ≤ ∫ x in cube q.1, ‖f x‖ := by
  calc
    _ = volume.real (cube q.1) * ‖cubeAverage f q.1‖ := by
      rw [setIntegral_congr_fun (cube_measurable q.1)
        (fun x hx => congrArg norm (goodPart_inside f Q hd q x hx)), integral_const,
        MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul]
    _ ≤ _ := cubeAverage_integral_norm_le f q.1

lemma goodPart_integrable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume)
    (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube) :
    Integrable (goodPart f Q) volume := by
  have hs : Summable (fun q : Q => ∫ x in cube q.1, ‖f x‖) :=
    (hasSum_integral_iUnion (fun q : Q => cube_measurable q.1)
      (hd.subtype _) hf.norm.integrableOn).summable
  have hgU : IntegrableOn (goodPart f Q) (badRegion Q) volume := by
    apply integrableOn_iUnion_of_summable_integral_norm
      (fun q : Q => goodPart_integrableOn_cube f Q hd q)
    exact Summable.of_nonneg_of_le
      (fun q => integral_nonneg (fun x => norm_nonneg _))
      (fun q => goodPart_integral_norm_cube_le f Q hd q) hs
  have hgC : IntegrableOn (goodPart f Q) (badRegion Q)ᶜ volume := by
    apply hf.integrableOn.congr_fun
    · intro x hx
      exact (goodPart_outside f Q x hx).symm
    · exact (badRegion_measurable Q).compl
  rw [← integrableOn_univ, ← union_compl_self (badRegion Q)]
  exact hgU.union hgC

lemma goodPart_integral_norm_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume)
    (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube) :
    (∫ x, ‖goodPart f Q x‖) ≤ ∫ x, ‖f x‖ := by
  have hg := goodPart_integrable f hf Q hd
  have hm := badRegion_measurable Q
  rw [← integral_add_compl hm hg.norm, ← integral_add_compl hm hf.norm]
  apply add_le_add
  · rw [show badRegion Q = ⋃ q : Q, cube q.1 from rfl,
      integral_iUnion (fun q : Q => cube_measurable q.1) (hd.subtype _) hg.norm.integrableOn,
      integral_iUnion (fun q : Q => cube_measurable q.1) (hd.subtype _) hf.norm.integrableOn]
    apply Summable.tsum_le_tsum
    · exact fun q => goodPart_integral_norm_cube_le f Q hd q
    · exact (hasSum_integral_iUnion (fun q : Q => cube_measurable q.1)
        (hd.subtype _) hg.norm.integrableOn).summable
    · exact (hasSum_integral_iUnion (fun q : Q => cube_measurable q.1)
        (hd.subtype _) hf.norm.integrableOn).summable
  · apply le_of_eq
    apply setIntegral_congr_fun hm.compl
    intro x hx
    exact congrArg norm (goodPart_outside f Q x hx)

lemma goodPart_eLpNorm_one_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume)
    (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube) :
    eLpNorm (goodPart f Q) 1 volume ≤ eLpNorm f 1 volume := by
  have hg := goodPart_integrable f hf Q hd
  rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hg,
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  exact ENNReal.ofReal_le_ofReal (goodPart_integral_norm_le f hf Q hd)

lemma goodPart_eLpNorm_infinity_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    eLpNorm (goodPart f Q) ∞ volume ≤ ENNReal.ofReal ((2 : ℝ) ^ d * t) := by
  rw [eLpNorm_exponent_top (goodPart_integrable f hf Q hQ.disjoint).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound (goodPart_ae_norm_le f t ht Q hQ)

lemma goodPart_memLp_two {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (Q : Set (DyadicCube d)) (hQ : Selection f t Q) :
    MemLp (goodPart f Q) 2 volume := by
  have hg := goodPart_integrable f hf Q hQ.disjoint
  apply (integrable_norm_rpow_iff hg.aestronglyMeasurable (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply (hg.norm.const_mul ((2 : ℝ) ^ d * t)).mono'
  · exact hg.aestronglyMeasurable.norm.pow 2
  · filter_upwards [goodPart_ae_norm_le f t ht Q hQ] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (goodPart f Q x)]

lemma badPiece_eq_indicator_sub_good {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube)
    (q : Q) : badPiece f q.1 = (cube q.1).indicator (f - goodPart f Q) := by
  ext x
  by_cases hx : x ∈ cube q.1
  · simp only [badPiece, indicator_of_mem hx, Pi.sub_apply,
      goodPart_inside f Q hd q x hx]
  · simp [badPiece, hx]

/-- Disjoint indicator pieces converge in every finite Lp exponent. This does
not assert absolute summability of their Lp norms. -/
lemma hasSum_indicator_disjoint {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube)
    (h : Point d → 𝕜) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hh : MemLp h p volume) (hout : ∀ x, x ∉ badRegion Q → h x = 0) :
    HasSum (fun q : Q => (hh.indicator (cube_measurable q.1).nullMeasurableSet).toLp
      ((cube q.1).indicator h)) (hh.toLp h) := by
  classical
  let b (q : Q) : Point d → 𝕜 := (cube q.1).indicator h
  have hb (q : Q) : MemLp (b q) p volume :=
    hh.indicator (cube_measurable q.1).nullMeasurableSet
  let P (s : Finset Q) : Point d → 𝕜 := fun x => ∑ q ∈ s, b q x
  have hP (s : Finset Q) : MemLp (P s) p volume := memLp_finsetSum s (fun q _ => hb q)
  have hsingle (q : Q) (x : Point d) (hx : x ∈ cube q.1) (r : Q) (hr : r ≠ q) :
      b r x = 0 := by
    apply indicator_of_notMem
    intro hxr
    exact Set.disjoint_left.mp (hd r.2 q.2 (fun he => hr (Subtype.ext he))) hxr hx
  have hP_at (s : Finset Q) (x : Point d) (q : Q) (hx : x ∈ cube q.1) :
      P s x = if q ∈ s then h x else 0 := by
    by_cases hqs : q ∈ s
    · rw [ite_eq_left hqs]
      dsimp only [P]
      rw [Finset.sum_eq_single q]
      · exact indicator_of_mem hx _
      · intro r _ hr
        exact hsingle q x hx r hr
      · exact fun hn => (hn hqs).elim
    · rw [ite_eq_right hqs]
      apply Finset.sum_eq_zero
      intro r hrs
      exact hsingle q x hx r (fun hr => hqs (hr ▸ hrs))
  have hP_out (s : Finset Q) (x : Point d) (hx : x ∉ badRegion Q) : P s x = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    apply indicator_of_notMem
    intro hqx
    exact hx (mem_iUnion.mpr ⟨q, hqx⟩)
  have hbound (s : Finset Q) (x : Point d) : ‖P s x - h x‖ₑ ≤ ‖h x‖ₑ := by
    by_cases hx : x ∈ badRegion Q
    · obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      rw [hP_at s x q hq]
      split_ifs <;> simp
    · rw [hP_out s x hx, hout x hx]
      simp
  have hlim (x : Point d) : ∀ᶠ s : Finset Q in atTop, P s x - h x = 0 := by
    by_cases hx : x ∈ badRegion Q
    · obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      filter_upwards [eventually_ge_atTop ({q} : Finset Q)] with s hs
      rw [hP_at s x q hq, ite_eq_left (hs (Finset.mem_singleton_self q)), sub_self]
    · exact Eventually.of_forall (fun s => by rw [hP_out s x hx, hout x hx, sub_self])
  have hI : Tendsto (fun s : Finset Q => ∫⁻ x, ‖P s x - h x‖ₑ ^ p.toReal)
      atTop (𝓝 0) := by
    have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hh
    have H := tendsto_lintegral_filter_of_dominated_convergence' (f := fun _ => 0)
      (fun x => ‖h x‖ₑ ^ p.toReal)
      (Eventually.of_forall (fun s => ((hP s).sub hh).aestronglyMeasurable.enorm.pow_const p.toReal))
      (Eventually.of_forall (fun s => Eventually.of_forall
        (fun x => ENNReal.rpow_le_rpow (hbound s x) ENNReal.toReal_nonneg))) hfin.ne
      (Eventually.of_forall (fun x => (tendsto_const_nhds.congr'
        ((hlim x).mono (fun s hs => by simp [hs, ENNReal.toReal_pos hp0 hp])))))
    simpa using H
  have hnorm : Tendsto (fun s : Finset Q => eLpNorm (P s - h) p volume) atTop (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp ((hP _).sub hh).aestronglyMeasurable]
    have H := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp hI
    simpa [Function.comp_def, ENNReal.toReal_pos hp0 hp] using H
  have hconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' P hP h hh).mpr hnorm
  change Tendsto (fun s : Finset Q => ∑ q ∈ s, (hb q).toLp (b q)) atTop (𝓝 (hh.toLp h))
  convert hconv using 1
  funext s
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun q => (hb q).toLp (b q)),
    (hP s).coeFn_toLp, ae_all_iff.mpr (fun q : Q => (hb q).coeFn_toLp)] with x hs hps hbs
  rw [hs, hps]
  exact Finset.sum_congr rfl (fun q _ => hbs q)

lemma badSeries_of_memLp {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (Q : Set (DyadicCube d)) (hd : Q.PairwiseDisjoint cube)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hf : MemLp f p volume) (hg : MemLp (goodPart f Q) p volume) :
    BadSeries f (goodPart f Q) Q p := by
  have hh := hf.sub hg
  have hb (q : Q) : MemLp (badPiece f q.1) p volume :=
    badPiece_memLp f q.1 (cube_volume_lt_top q.1) hf
  refine ⟨hg, hb, hh, ?_⟩
  have H := hasSum_indicator_disjoint Q hd (f - goodPart f Q) hp0 hp hh
    (fun x hx => by simp only [Pi.sub_apply, goodPart_outside f Q x hx, sub_self])
  convert H using 1
  funext q
  apply Lp.ext
  filter_upwards [(hb q).coeFn_toLp,
    (hh.indicator (cube_measurable q.1).nullMeasurableSet).coeFn_toLp] with x hx hy
  rw [hx, hy, badPiece_eq_indicator_sub_good f Q hd q]

/-- The same coordinate cube in the finite product with its supremum metric.
This is used only to apply differentiation; volume is transported explicitly. -/
def piCube {d : ℕ} (q : DyadicCube d) : Set (Fin d → ℝ) :=
  Set.pi univ (fun i => Ico (side q * (q.2 i : ℝ)) (side q * ((q.2 i : ℝ) + 1)))

def piCenter {d : ℕ} (q : DyadicCube d) : Fin d → ℝ :=
  fun i => side q * ((q.2 i : ℝ) + 1 / 2)

lemma piCube_measurable {d : ℕ} (q : DyadicCube d) : MeasurableSet (piCube q) :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ico)

lemma cube_eq_preimage_piCube {d : ℕ} (q : DyadicCube d) :
    cube q = WithLp.ofLp ⁻¹' piCube q := by
  ext x
  simp [cube, piCube]

lemma piCube_ae_closedBall {d : ℕ} (q : DyadicCube d) :
    piCube q =ᵐ[volume] Metric.closedBall (piCenter q) (side q / 2) := by
  have heq : Metric.closedBall (piCenter q) (side q / 2) =
      Set.pi univ (fun i => Icc (side q * (q.2 i : ℝ)) (side q * ((q.2 i : ℝ) + 1))) := by
    rw [closedBall_pi _ (by exact div_nonneg (side_pos q).le (by norm_num))]
    congr 1
    funext i
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> dsimp [piCenter] <;> ring
  rw [heq]
  exact Measure.pi_Ico_ae_eq_pi_Icc

lemma mem_piClosedBall {d : ℕ} (q : DyadicCube d) (x : Point d) (hx : x ∈ cube q) :
    WithLp.ofLp x ∈ Metric.closedBall (piCenter q) (side q / 2) := by
  rw [closedBall_pi _ (by exact div_nonneg (side_pos q).le (by norm_num))]
  intro i _
  change x i ∈ Metric.closedBall (piCenter q i) (side q / 2)
  rw [Real.closedBall_eq_Icc]
  have hi := hx i
  dsimp [piCenter]
  constructor <;> linarith

lemma cube_norm_average_eq_pi_average {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (q : DyadicCube d) :
    (volume.real (cube q))⁻¹ * (∫ x in cube q, ‖f x‖) =
      ⨍ y in Metric.closedBall (piCenter q) (side q / 2), ‖f (WithLp.toLp 2 y)‖ := by
  rw [← setAverage_congr (piCube_ae_closedBall q), setAverage_eq, smul_eq_mul,
    cube_eq_preimage_piCube]
  have hm := (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (piCube_measurable q).nullMeasurableSet
  rw [show volume.real (WithLp.ofLp ⁻¹' piCube q) = volume.real (piCube q) from
    congrArg ENNReal.toReal hm]
  congr 1
  exact (PiLp.volume_preserving_ofLp (Fin d)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
    (fun y => ‖f (WithLp.toLp 2 y)‖) (piCube q)

/-- If all dyadic averages through a point are bounded, differentiation bounds
its value almost everywhere. Half-open cubes are equal a.e. to closed balls
in the supremum metric; no differentiation property is assumed for the grid. -/
lemma ae_norm_le_of_cube_averages {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume) (t : ℝ) :
    ∀ᵐ x ∂volume, (∀ q : DyadicCube d, x ∈ cube q →
      (∫ y in cube q, ‖f y‖) ≤ t * volume.real (cube q)) → ‖f x‖ ≤ t := by
  have hpi : Integrable (fun y : Fin d → ℝ => ‖f (WithLp.toLp 2 y)‖) volume :=
    (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_of_integrable hf.norm
  have H := IsUnifLocDoublingMeasure.ae_tendsto_average volume hpi.locallyIntegrable 1
  filter_upwards [(PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae H] with x hx hbound
  choose q hlevel hmem using (fun n : ℕ => exists_cube_at_level (-(n : ℤ)) x)
  have hside (n : ℕ) : side (q n) = (1 / 2 : ℝ) ^ n := by
    simp [side, hlevel n, zpow_neg, inv_pow, one_div]
  have hr : Tendsto (fun n => side (q n) / 2) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun n => show 0 < side (q n) / 2 from
      div_pos (side_pos _) (by norm_num))⟩
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).div_const 2
    simpa [hside] using hh
  have hlim := hx (fun n => piCenter (q n)) (fun n => side (q n) / 2) hr
    (Eventually.of_forall (fun n => by simpa using mem_piClosedBall (q n) x (hmem n)))
  have hb (n : ℕ) :
      (⨍ y in Metric.closedBall (piCenter (q n)) (side (q n) / 2), ‖f (WithLp.toLp 2 y)‖) ≤ t := by
    rw [← cube_norm_average_eq_pi_average]
    have hv : 0 < volume.real (cube (q n)) :=
      ENNReal.toReal_pos (cube_volume_pos _).ne' (cube_volume_lt_top _).ne
    exact (inv_mul_le_iff₀ hv).mpr (by simpa [mul_comm] using hbound (q n) (hmem n))
  exact le_of_tendsto hlim (Eventually.of_forall hb)

/-- Bad cubes selected by the last bad ancestor. -/
def isBad {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) (q : DyadicCube d) : Prop :=
  t * volume.real (cube q) < ∫ x in cube q, ‖f x‖

def maximalBadCubes {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) : Set (DyadicCube d) :=
  {q | isBad f t q ∧ ∀ n : ℕ, 0 < n → ¬ isBad f t (parent^[n] q)}

lemma cube_parent_volume_real {d : ℕ} (q : DyadicCube d) :
    volume.real (cube (parent q)) = (2 : ℝ) ^ d * volume.real (cube q) := by
  simp only [measureReal_def, cube_parent_volume, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat]

lemma cube_ancestor_volume_real {d : ℕ} (q : DyadicCube d) (n : ℕ) :
    volume.real (cube (parent^[n] q)) = ((2 : ℝ) ^ d) ^ n * volume.real (cube q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', cube_parent_volume_real, ih, pow_succ]
    ring

lemma eventually_not_bad_ancestor {d : ℕ} (hd : 0 < d)
    {𝕜 : Type*} [RCLike 𝕜] (f : Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (q : DyadicCube d) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ isBad f t (parent^[n] q) := by
  have hv : 0 < volume.real (cube q) :=
    ENNReal.toReal_pos (cube_volume_pos _).ne' (cube_volume_lt_top _).ne
  have htwo : (2 : ℝ) ≤ 2 ^ d := le_self_pow₀ (by norm_num) hd.ne'
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x, ‖f x‖) / (t * volume.real (cube q)))
  refine ⟨N, fun n hn hbad => ?_⟩
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ≤ ((2 : ℝ) ^ d) ^ n := by
    have h := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ (2 : ℝ) ^ d by linarith) n
    have hnonneg : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hlarge : (∫ x, ‖f x‖) < t * volume.real (cube q) * n := by
    simpa only [mul_comm] using (div_lt_iff₀ (mul_pos ht hv)).mp (hN.trans_le hn')
  have hmono : (∫ x in cube (parent^[n] q), ‖f x‖) ≤ ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm (Eventually.of_forall (fun x => norm_nonneg _))
  unfold isBad at hbad
  rw [cube_ancestor_volume_real] at hbad
  have hh := mul_le_mul_of_nonneg_left hpow (mul_pos ht hv).le
  nlinarith

lemma bad_cube_covered_by_maximal {d : ℕ} (hd : 0 < d)
    {𝕜 : Type*} [RCLike 𝕜] (f : Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) (q : DyadicCube d) (hq : isBad f t q) :
    ∃ r ∈ maximalBadCubes f t, cube q ⊆ cube r := by
  classical
  obtain ⟨N, hN⟩ := eventually_not_bad_ancestor hd f hf t ht q
  let P : ℕ → Prop := fun n => isBad f t (parent^[n] q)
  let n := Nat.findGreatest P N
  have hzero : P 0 := by simpa [P] using hq
  have hn : P n := Nat.findGreatest_spec (Nat.zero_le _) hzero
  refine ⟨parent^[n] q, ⟨hn, ?_⟩, cube_subset_ancestor q n⟩
  intro m hm hbad
  have hmn : P (n + m) := by
    simpa only [P, Function.iterate_add_apply, Nat.add_comm] using hbad
  by_cases hle : n + m ≤ N
  · have hmax := Nat.le_findGreatest hle hmn
    change n + m ≤ n at hmax
    omega
  · exact hN (n + m) (by omega) hmn

lemma maximalBadCubes_disjoint {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (t : ℝ) : (maximalBadCubes f t).PairwiseDisjoint cube := by
  intro q hq r hr hne
  by_contra hdisj
  obtain ⟨x, hxq, hxr⟩ := not_disjoint_iff_nonempty_inter.mp hdisj
  have hancestor {q r : DyadicCube d} (hk : q.1 < r.1)
      (hxq : x ∈ cube q) (hxr : x ∈ cube r) :
      ∃ n : ℕ, 0 < n ∧ parent^[n] q = r := by
    let n := (r.1 - q.1).toNat
    have hn : q.1 + (n : ℤ) = r.1 := by dsimp only [n]; omega
    refine ⟨n, by dsimp only [n]; omega, ?_⟩
    exact cube_eq_of_same_level_of_mem ((ancestor_level q n).trans hn)
      (cube_subset_ancestor q n hxq) hxr
  rcases lt_trichotomy q.1 r.1 with hlt | heq | hgt
  · obtain ⟨n, hn, heq⟩ := hancestor hlt hxq hxr
    exact hq.2 n hn (by rw [heq]; exact hr.1)
  · exact hne (cube_eq_of_same_level_of_mem heq hxq hxr)
  · obtain ⟨n, hn, heq⟩ := hancestor hgt hxr hxq
    exact hr.2 n hn (by rw [heq]; exact hq.1)

lemma maximalBadCubes_upper {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Point d → 𝕜) (hf : Integrable f volume) (t : ℝ)
    (q : DyadicCube d) (hq : q ∈ maximalBadCubes f t) :
    (∫ x in cube q, ‖f x‖) ≤ (2 : ℝ) ^ d * t * volume.real (cube q) := by
  have hparent : ¬ isBad f t (parent q) := by
    simpa only [Function.iterate_one] using hq.2 1 (by norm_num)
  have hparent' : (∫ x in cube (parent q), ‖f x‖) ≤ t * volume.real (cube (parent q)) :=
    le_of_not_gt hparent
  calc
    (∫ x in cube q, ‖f x‖) ≤ ∫ x in cube (parent q), ‖f x‖ :=
      setIntegral_mono_set hf.norm.integrableOn
        (Eventually.of_forall (fun x => norm_nonneg _))
        (Eventually.of_forall (cube_subset_parent q))
    _ ≤ t * volume.real (cube (parent q)) := hparent'
    _ = (2 : ℝ) ^ d * t * volume.real (cube q) := by
      rw [cube_parent_volume_real]
      ring

lemma maximalBadCubes_selection {d : ℕ} (hd : 0 < d)
    {𝕜 : Type*} [RCLike 𝕜] (f : Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) : Selection f t (maximalBadCubes f t) := by
  refine ⟨fun q _ => cube_measurable q, fun q _ => cube_volume_pos q,
    fun q _ => cube_volume_lt_top q, maximalBadCubes_disjoint f t,
    fun q hq => hq.1, fun q hq => maximalBadCubes_upper f hf t q hq, ?_⟩
  filter_upwards [ae_norm_le_of_cube_averages f hf t] with x hx hout
  apply hx
  intro q hxq
  by_contra hbad
  have hq : isBad f t q := lt_of_not_ge hbad
  obtain ⟨r, hr, hqr⟩ := bad_cube_covered_by_maximal hd f hf t ht q hq
  apply hout
  exact mem_iUnion.mpr ⟨⟨r, hr⟩, hqr hxq⟩

lemma selection_exists {d : ℕ} (hd : 0 < d)
    {𝕜 : Type*} [RCLike 𝕜] (f : Point d → 𝕜) (hf : Integrable f volume)
    (t : ℝ) (ht : 0 < t) : ∃ Q : Set (DyadicCube d), Selection f t Q :=
  ⟨maximalBadCubes f t, maximalBadCubes_selection hd f hf t ht⟩

end ExpandedFA.SingularIntegrals.CZ

namespace ExpandedFA.SingularIntegrals
open CZ

/-- All analytical conclusions for a selected family, including the actual
L¹ and L² series in the complete quotient spaces. -/
theorem calderonZygmund_assemble_selection : CalderonZygmundDecompositionSpec.AssembleSelection := by
  intro d 𝕜 _ f hf t ht Q hQ
  refine ⟨goodPart f Q, ?_⟩
  have hg := goodPart_integrable f hf Q hQ.disjoint
  refine {
    disjoint := hQ.disjoint
    good_outside := fun x hx => goodPart_outside f Q x hx
    good_inside := fun q hq x hx => goodPart_inside f Q hQ.disjoint ⟨q, hq⟩ x hx
    measure_bound := selection_measure_bound f hf t ht Q hQ
    good_integrable := hg
    good_infinity := goodPart_eLpNorm_infinity_le f hf t ht Q hQ
    good_one := goodPart_eLpNorm_one_le f hf Q hQ.disjoint
    bad_integrable := fun q => badPiece_integrable f hf q.1 (cube_volume_lt_top q.1)
    bad_mean := fun q => badPiece_integral f q.1 (cube_volume_lt_top q.1)
    bad_support := fun q => badPiece_support f q.1
    bad_one_bound := selection_bad_one_bound f hf t Q hQ
    series_one := badSeries_of_memLp f Q hQ.disjoint (by norm_num) (by norm_num)
      (memLp_one_iff_integrable.mpr hf) (memLp_one_iff_integrable.mpr hg)
    series_two := fun hf2 => badSeries_of_memLp f Q hQ.disjoint (by norm_num) (by norm_num)
      hf2 (goodPart_memLp_two f hf t ht Q hQ)
  }


theorem calderonZygmund_cube_geometry :
    CalderonZygmundDecompositionSpec.CubeGeometry := by
  intro d q
  exact ⟨cube_measurable q, cube_volume_pos q, cube_volume q,
    cube_subset_parent q, cube_parent_volume q⟩

theorem calderonZygmund_cube_grid : CalderonZygmundDecompositionSpec.CubeGrid := by
  exact ⟨fun _ q r => cube_nested_or_disjoint q r,
    fun _ k x => exists_cube_at_level k x⟩

theorem calderonZygmund_selection_bounds :
    CalderonZygmundDecompositionSpec.SelectionBounds := by
  intro d 𝕜 _ f hf t ht Q hQ
  exact ⟨selection_measure_bound f hf t ht Q hQ, selection_bad_one_bound f hf t Q hQ⟩

theorem calderonZygmund_pointwise_good : CalderonZygmundDecompositionSpec.PointwiseGood := by
  intro d 𝕜 _ f t ht Q hQ
  refine ⟨fun x hx => goodPart_outside f Q x hx, ?_, goodPart_ae_norm_le f t ht Q hQ⟩
  intro q hq x hx
  exact goodPart_inside f Q hQ.disjoint ⟨q, hq⟩ x hx

theorem calderonZygmund_single_bad_piece :
    CalderonZygmundDecompositionSpec.SingleBadPiece := by
  intro d 𝕜 _ f hf q
  have hfin := cube_volume_lt_top q
  exact ⟨badPiece_integrable f hf q hfin, badPiece_integral f q hfin,
    badPiece_support f q, badPiece_integral_norm_le f hf q,
    fun hf2 => badPiece_memLp f q hfin hf2⟩

/-- The two independently stated ingredients imply the full decomposition. -/
theorem calderonZygmund_decomposition_of_selection_and_assembly
    : CalderonZygmundDecompositionSpec.AssemblyReduction := by
  intro hs ha d hd 𝕜 _ f hf t ht
  obtain ⟨Q, hQ⟩ := hs d hd f hf t ht
  obtain ⟨g, hg⟩ := ha d f hf t ht Q hQ
  exact ⟨Q, g, hg⟩

/-- Maximal dyadic cubes exist by volume growth and have the a.e. exterior bound. -/
theorem calderonZygmund_maximal_selection :
    CalderonZygmundDecompositionSpec.MaximalSelection := by
  intro d hd 𝕜 _ f hf t ht
  exact selection_exists hd f hf t ht

/-- The complete Calderón–Zygmund decomposition, including both Lp series. -/
theorem calderonZygmund_decomposition :
    CalderonZygmundDecompositionSpec.DecompositionTheorem :=
  calderonZygmund_decomposition_of_selection_and_assembly
    calderonZygmund_maximal_selection calderonZygmund_assemble_selection

end ExpandedFA.SingularIntegrals
