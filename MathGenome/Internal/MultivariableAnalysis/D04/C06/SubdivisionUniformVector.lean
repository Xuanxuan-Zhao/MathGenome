import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.SubdivisionUniformVector
import MathGenome.Internal.MultivariableAnalysis.D04.C06.BoxAlgebra
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.D04.C01.OperatorEstimates

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.Darboux

abbrev VectorBounded := @Specs.D04.C06.SubdivisionUniformVector.Model.VectorBounded
abbrev VectorIntegrable := @Specs.D04.C06.SubdivisionUniformVector.Model.VectorIntegrable
abbrev vectorIntegral := @Specs.D04.C06.SubdivisionUniformVector.Model.vectorIntegral
abbrev vectorTaggedSum := @Specs.D04.C06.SubdivisionUniformVector.Model.vectorTaggedSum
abbrev HasVectorTaggedIntegral := @Specs.D04.C06.SubdivisionUniformVector.Model.HasVectorTaggedIntegral

variable {n k : ℕ} {Q : Box n} {f g : E n → ℝ}

theorem integrable_sub (hf : Integrable f Q) (hg : Integrable g Q) :
    Integrable (fun x => f x - g x) Q := by
  simpa only [neg_one_mul, ← sub_eq_add_neg] using integrable_add hf (integrable_smul (-1) hg)

theorem integral_sub (hf : Integrable f Q) (hg : Integrable g Q)
    (h : Integrable (fun x => f x - g x) Q) :
    integral (fun x => f x - g x) Q h = integral f Q hf - integral g Q hg := by
  have hn := integrable_smul (-1) hg
  have hh := integral_add hf hn (show Integrable (fun x => f x + -1 * g x) Q by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using h)
  rw [integral_smul] at hh
  simpa only [neg_one_mul, ← sub_eq_add_neg] using hh

theorem integral_sub_le_sup (hf : Integrable f Q) (hg : Integrable g Q) :
    |integral f Q hf - integral g Q hg| ≤
      content Q * sSup ((fun x => |f x - g x|) '' carrier Q) := by
  have hd := integrable_sub hf hg
  rw [← integral_sub hf hg hd]
  exact (integral_abs_bound hd (integrable_abs hd)).1.trans
    (integral_abs_bound hd (integrable_abs hd)).2

/-- A bound on the integrand difference controls the difference of integrals. -/
theorem integral_sub_le (hf : Integrable f Q) (hg : Integrable g Q) {M : ℝ}
    (hM : ∀ x ∈ carrier Q, |f x - g x| ≤ M) :
    |integral f Q hf - integral g Q hg| ≤ content Q * M := by
  have hd := integrable_sub hf hg
  have ha := integrable_abs hd
  have hu := integral_mono ha (integrable_const Q M) hM
  rw [integral_const] at hu
  rw [← integral_sub hf hg hd]
  exact (integral_abs_bound hd ha).1.trans (hu.trans_eq (mul_comm _ _))

/-- Uniform perturbations change a Darboux gap by at most twice volume times error. -/
theorem gap_perturbation (_hf : Bounded f Q) (hg : Bounded g Q) {M : ℝ}
    (hM : ∀ x ∈ carrier Q, |f x - g x| ≤ M) (P : Grid Q) :
    upperSum f P - lowerSum f P ≤ upperSum g P - lowerSum g P + 2 * M * content Q := by
  have hc (c : CellIndex P) : cellSupremum f P c - cellInfimum f P c ≤
      cellSupremum g P c - cellInfimum g P c + 2 * M := by
    apply cell_oscillation_le
    intro x hx y hy
    have hx' := abs_le.mp (hM x (cell_subset P c hx))
    have hy' := abs_le.mp (hM y (cell_subset P c hy))
    have hxg := le_cellSupremum g hg P c hx
    have hyg := cellInfimum_le g hg P c hy
    linarith
  change (∑ c, cellSupremum f P c * cellContent P c) -
    (∑ c, cellInfimum f P c * cellContent P c) ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, (cellSupremum g P c - cellInfimum g P c + 2 * M) * cellContent P c := by
      apply Finset.sum_le_sum
      intro c _
      rw [← sub_mul]
      exact mul_le_mul_of_nonneg_right (hc c) (cellContent_nonneg P c)
    _ = _ := by
      simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, content_partition]
      rfl

theorem uniform_limit (F : ℕ → E n → ℝ) (f : E n → ℝ)
    (hF : ∀ j, Integrable (F j) Q)
    (hu : TendstoUniformlyOn F f atTop (carrier Q)) :
    ∃ hf : Integrable f Q,
      Tendsto (fun j => integral (F j) Q (hF j)) atTop (𝓝 (integral f Q hf)) := by
  have hup : ∀ ε > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ x ∈ carrier Q, |f x - F j x| < ε := by
    intro ε hε
    have h := (Metric.tendstoUniformlyOn_iff.mp hu) ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    exact ⟨N, fun j hj x hx => by simpa only [Real.dist_eq] using hN j hj x hx⟩
  have hb : Bounded f Q := by
    obtain ⟨N, hN⟩ := hup 1 zero_lt_one
    obtain ⟨M, _, hM⟩ := exists_abs_bound (hF N).1
    apply bounded_of_abs_le (M := 1 + M)
    intro x hx
    have ht := abs_add_le (f x - F N x) (F N x)
    rw [sub_add_cancel] at ht
    linarith [hN N le_rfl x hx, hM x hx]
  have hf : Integrable f Q := by
    apply (integrable_iff_gap f Q hb).mpr
    intro ε hε
    let η := ε / (8 * (content Q + 1))
    have hden : 0 < 8 * (content Q + 1) := by nlinarith [content_nonneg Q]
    have hη : 0 < η := div_pos hε hden
    obtain ⟨N, hN⟩ := hup η hη
    obtain ⟨P, hP⟩ := (integrable_iff_gap (F N) Q (hF N).1).mp (hF N) (ε/2) (half_pos hε)
    have hg := gap_perturbation hb (hF N).1 (M := η) (fun x hx => (hN N le_rfl x hx).le) P
    have heq : η * (8 * (content Q + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
    exact ⟨P, by nlinarith [content_nonneg Q]⟩
  refine ⟨hf, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  let η := ε / (content Q + 1)
  have hd : 0 < content Q + 1 := by linarith [content_nonneg Q]
  have hη : 0 < η := div_pos hε hd
  obtain ⟨N, hN⟩ := hup η hη
  refine ⟨N, fun j hj => ?_⟩
  have he := integral_sub_le hf (hF j) (fun x hx => (hN j hj x hx).le)
  have heq : η * (content Q + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hd)
  rw [Real.dist_eq, abs_sub_comm]
  nlinarith [content_nonneg Q]

/-- A positive common lower bound for finitely many positive numbers, including
an empty index type. -/
theorem finite_positive_min {ι : Type*} [Fintype ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ δ > 0, ∀ i, δ ≤ d i := by
  classical
  let s := insert 1 (Finset.univ.image d)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  refine ⟨s.min' hs, ?_, fun i => Finset.min'_le s _ ?_⟩
  · apply (Finset.lt_min'_iff s hs).mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hd i
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem vector_bounded_iff (v : E n → E k) (Q : Box n) :
    VectorBounded v Q ↔ ∀ i : Fin k, Bounded (fun x => v x i) Q := by
  constructor
  · rintro ⟨M, hM⟩ i
    exact bounded_of_abs_le (M := M) fun x hx =>
      (PiLp.norm_apply_le (v x) i).trans (hM x hx)
  · intro h
    choose M hM0 hM using fun i => exists_abs_bound (h i)
    refine ⟨∑ i, M i, fun x hx => (norm_le_sum_abs (v x)).trans ?_⟩
    exact Finset.sum_le_sum fun i _ => hM i x hx

theorem vector_integral_coordinate (v : E n → E k) (Q : Box n)
    (hv : VectorIntegrable v Q) (i : Fin k) :
    vectorIntegral v Q hv i = integral (fun x => v x i) Q (hv i) := rfl

theorem vectorTaggedSum_coordinate (v : E n → E k) (P : Grid Q) (ξ : Tagging P)
    (i : Fin k) : vectorTaggedSum v P ξ i = taggedSum (fun x => v x i) P ξ := by
  change (PiLp.projₗ (𝕜 := ℝ) (β := fun _ : Fin k => ℝ) 2 i)
    (∑ c, cellContent P c • v (ξ c)) = _
  rw [map_sum]
  change (∑ c, cellContent P c * v (ξ c) i) = _
  change (∑ c, cellContent P c * v (ξ c) i) = ∑ c, v (ξ c) i * cellContent P c
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

theorem mesh_degenerate (hd : Degenerate Q) (P : Grid Q) : mesh P = 0 := by
  let _ := no_cells_of_degenerate hd P
  simp [mesh, Specs.D04.C06.DarbouxIntegral.Model.mesh]

theorem fine_grid_exists (Q : Box n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : Grid Q, mesh P < δ := by
  by_cases hd : Degenerate Q
  · obtain ⟨P⟩ := grid_exists Q
    exact ⟨P, by rw [mesh_degenerate hd]; exact hδ⟩
  · exact arbitrarily_fine Q (nondegenerate_of_not_degenerate hd) δ hδ

theorem tagged_forward_all (hf : Integrable f Q) : HasTaggedIntegral f Q (integral f Q hf) := by
  by_cases hd : Degenerate Q
  · intro ε hε
    refine ⟨1, zero_lt_one, fun P ξ _ => ?_⟩
    change |taggedSum f P ξ - lowerIntegral f Q| < ε
    rw [(degenerate_sums f hd P ξ).1, (degenerate_integrals f Q hd).1, sub_self, abs_zero]
    exact hε
  · exact tagged_forward f Q (nondegenerate_of_not_degenerate hd) hf

theorem integrable_of_taggedIntegral_all (hb : Bounded f Q) {I : ℝ}
    (hi : HasTaggedIntegral f Q I) : Integrable f Q := by
  by_cases hd : Degenerate Q
  · exact integrable_degenerate f Q hb hd
  · exact integrable_of_taggedIntegral f Q hb (nondegenerate_of_not_degenerate hd) I hi

theorem taggedIntegral_unique_all {I J : ℝ} (hI : HasTaggedIntegral f Q I)
    (hJ : HasTaggedIntegral f Q J) : I = J := by
  by_contra hne
  have hp : 0 < |I - J| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δI, hδI, hcI⟩ := hI (|I-J| / 2) (half_pos hp)
  obtain ⟨δJ, hδJ, hcJ⟩ := hJ (|I-J| / 2) (half_pos hp)
  obtain ⟨P, hP⟩ := fine_grid_exists Q (min δI δJ) (lt_min hδI hδJ)
  obtain ⟨ξ⟩ := tags_exist P
  have hi := hcI P ξ (hP.trans_le (min_le_left _ _))
  have hj := hcJ P ξ (hP.trans_le (min_le_right _ _))
  have ht := abs_sub_le I (taggedSum f P ξ) J
  rw [abs_sub_comm I (taggedSum f P ξ)] at ht
  linarith

/-- The norm tagged-sum limit is precisely the collection of scalar limits. -/
theorem vector_tagged_iff_coordinate (v : E n → E k) (I : E k) :
    HasVectorTaggedIntegral v Q I ↔
      ∀ i, HasTaggedIntegral (fun x => v x i) Q (I i) := by
  constructor
  · intro hv i ε hε
    obtain ⟨δ, hδ, ht⟩ := hv ε hε
    refine ⟨δ, hδ, fun P ξ hP => ?_⟩
    have he := PiLp.norm_apply_le (vectorTaggedSum v P ξ - I) i
    rw [PiLp.sub_apply, vectorTaggedSum_coordinate, Real.norm_eq_abs] at he
    exact he.trans_lt (ht P ξ hP)
  · intro hc ε hε
    let η := ε / ((k : ℝ) + 1)
    have hd : 0 < (k : ℝ) + 1 := by positivity
    have hη : 0 < η := div_pos hε hd
    choose d hdpos ht using fun i => hc i η hη
    obtain ⟨δ, hδ, hδd⟩ := finite_positive_min d hdpos
    refine ⟨δ, hδ, fun P ξ hP => ?_⟩
    calc
      ‖vectorTaggedSum v P ξ - I‖ ≤ ∑ i, |(vectorTaggedSum v P ξ - I) i| := norm_le_sum_abs _
      _ ≤ ∑ _i : Fin k, η := by
        apply Finset.sum_le_sum
        intro i _
        rw [PiLp.sub_apply, vectorTaggedSum_coordinate]
        exact (ht i P ξ (hP.trans_le (hδd i))).le
      _ = (k : ℝ) * η := by simp
      _ < ε := by
        have heq : η * ((k : ℝ) + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hd)
        nlinarith

theorem vector_tagged_criteria (v : E n → E k) (Q : Box n) (hb : VectorBounded v Q) :
    (VectorIntegrable v Q ↔ ∃ I, HasVectorTaggedIntegral v Q I) ∧
    (∀ hv : VectorIntegrable v Q, HasVectorTaggedIntegral v Q (vectorIntegral v Q hv)) ∧
    ∀ I, HasVectorTaggedIntegral v Q I →
      ∃ hv : VectorIntegrable v Q, I = vectorIntegral v Q hv := by
  have hforward (hv : VectorIntegrable v Q) :
      HasVectorTaggedIntegral v Q (vectorIntegral v Q hv) := by
    apply (vector_tagged_iff_coordinate v _).mpr
    intro i
    exact tagged_forward_all (hv i)
  have hback (I : E k) (hi : HasVectorTaggedIntegral v Q I) :
      ∃ hv : VectorIntegrable v Q, I = vectorIntegral v Q hv := by
    have hc := (vector_tagged_iff_coordinate v I).mp hi
    have hv : VectorIntegrable v Q := fun i =>
      integrable_of_taggedIntegral_all ((vector_bounded_iff v Q).mp hb i) (hc i)
    refine ⟨hv, ?_⟩
    ext i
    exact taggedIntegral_unique_all (hc i) (tagged_forward_all (hv i))
  exact ⟨⟨fun hv => ⟨_, hforward hv⟩, fun ⟨I, hI⟩ => (hback I hI).choose⟩,
    hforward, hback⟩

/-- Finitely many integrable functions admit one grid with every gap small. -/
theorem simultaneous_small_gaps {ι : Type*} (s : Finset ι) (u : ι → E n → ℝ)
    (hu : ∀ i ∈ s, Integrable (u i) Q) {η : ℝ} (hη : 0 < η) :
    ∃ P : Grid Q, ∀ i ∈ s, upperSum (u i) P - lowerSum (u i) P < η := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨P⟩ := grid_exists Q
    exact ⟨P, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨P, hP⟩ := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
    obtain ⟨R, hR⟩ := (integrable_iff_gap (u i) Q (hu i (Finset.mem_insert_self _ _)).1).mp
      (hu i (Finset.mem_insert_self _ _)) η hη
    obtain ⟨T, hTP, hTR⟩ := common_refinement P R
    refine ⟨T, fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with hji | hj
    · subst j
      have huT := upper_refinement (u i) (hu i (Finset.mem_insert_self _ _)).1 R T hTR
      have hlT := lower_refinement (u i) (hu i (Finset.mem_insert_self _ _)).1 R T hTR
      linarith
    · have huT := upper_refinement (u j) (hu j (Finset.mem_insert_of_mem hj)).1 P T hTP
      have hlT := lower_refinement (u j) (hu j (Finset.mem_insert_of_mem hj)).1 P T hTP
      linarith [hP j hj]

theorem integrable_norm {v : E n → E k} (hv : VectorIntegrable v Q) :
    Integrable (fun x => ‖v x‖) Q := by
  have hb := (vector_bounded_iff v Q).mpr (fun i => (hv i).1)
  obtain ⟨M, hM⟩ := hb
  have hn : Bounded (fun x => ‖v x‖) Q :=
    bounded_of_abs_le (M := M) fun x hx => by simpa only [abs_norm] using hM x hx
  apply (integrable_iff_gap _ Q hn).mpr
  intro ε hε
  let η := ε / ((k : ℝ) + 1)
  have hd : 0 < (k : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hε hd
  obtain ⟨P, hP⟩ := simultaneous_small_gaps Finset.univ (fun i x => v x i)
    (fun i _ => hv i) hη
  have hc (c : CellIndex P) : cellSupremum (fun x => ‖v x‖) P c -
      cellInfimum (fun x => ‖v x‖) P c ≤
      ∑ i, (cellSupremum (fun x => v x i) P c - cellInfimum (fun x => v x i) P c) := by
    apply cell_oscillation_le
    intro x hx y hy
    calc
      ‖v x‖ - ‖v y‖ ≤ ‖v x - v y‖ := norm_sub_norm_le _ _
      _ ≤ ∑ i, |(v x - v y) i| := norm_le_sum_abs _
      _ ≤ _ := Finset.sum_le_sum fun i _ => abs_sub_le_cell_oscillation (hv i).1 P c hx hy
  have hs : upperSum (fun x => ‖v x‖) P - lowerSum (fun x => ‖v x‖) P ≤
      ∑ i, (upperSum (fun x => v x i) P - lowerSum (fun x => v x i) P) := by
    change (∑ c, cellSupremum (fun x => ‖v x‖) P c * cellContent P c) -
      (∑ c, cellInfimum (fun x => ‖v x‖) P c * cellContent P c) ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ c, (∑ i, (cellSupremum (fun x => v x i) P c -
          cellInfimum (fun x => v x i) P c)) * cellContent P c := by
        apply Finset.sum_le_sum
        intro c _
        rw [← sub_mul]
        exact mul_le_mul_of_nonneg_right (hc c) (cellContent_nonneg P c)
      _ = _ := by
        simp only [Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
        congr 1 <;> exact Finset.sum_comm
  refine ⟨P, lt_of_le_of_lt hs ?_⟩
  calc
    _ ≤ ∑ _i : Fin k, η := Finset.sum_le_sum fun i _ => (hP i (Finset.mem_univ i)).le
    _ = (k : ℝ) * η := by simp
    _ < ε := by
      have heq : η * ((k : ℝ) + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hd)
      nlinarith

theorem vectorTaggedIntegral_unique {v : E n → E k} {I J : E k}
    (hI : HasVectorTaggedIntegral v Q I) (hJ : HasVectorTaggedIntegral v Q J) : I = J := by
  ext i
  exact taggedIntegral_unique_all ((vector_tagged_iff_coordinate v I).mp hI i)
    ((vector_tagged_iff_coordinate v J).mp hJ i)

theorem vectorTaggedSum_norm_le (v : E n → E k) (P : Grid Q) (ξ : Tagging P) :
    ‖vectorTaggedSum v P ξ‖ ≤ taggedSum (fun x => ‖v x‖) P ξ := by
  calc
    _ ≤ ∑ c, ‖cellContent P c • v (ξ c)‖ := norm_sum_le _ _
    _ = _ := by
      change (∑ c, ‖cellContent P c • v (ξ c)‖) =
        ∑ c, ‖v (ξ c)‖ * cellContent P c
      apply Finset.sum_congr rfl
      intro c _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cellContent_nonneg P c), mul_comm]

theorem vector_integral_norm_le {v : E n → E k} (hv : VectorIntegrable v Q)
    (hn : Integrable (fun x => ‖v x‖) Q) :
    ‖vectorIntegral v Q hv‖ ≤ integral (fun x => ‖v x‖) Q hn := by
  have hb : VectorBounded v Q := (vector_bounded_iff v Q).mpr (fun i => (hv i).1)
  have htv := (vector_tagged_criteria v Q hb).2.1 hv
  have htn := tagged_forward_all hn
  by_contra hnot
  have hp : 0 < ‖vectorIntegral v Q hv‖ - integral (fun x => ‖v x‖) Q hn :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let ε := (‖vectorIntegral v Q hv‖ - integral (fun x => ‖v x‖) Q hn) / 3
  have hε : 0 < ε := div_pos hp (by norm_num)
  obtain ⟨δv, hδv, hδv'⟩ := htv ε hε
  obtain ⟨δn, hδn, hδn'⟩ := htn ε hε
  obtain ⟨P, hP⟩ := fine_grid_exists Q (min δv δn) (lt_min hδv hδn)
  obtain ⟨ξ⟩ := tags_exist P
  have hvP := hδv' P ξ (hP.trans_le (min_le_left _ _))
  have hnP := (abs_lt.mp (hδn' P ξ (hP.trans_le (min_le_right _ _)))).2
  have hnorm := norm_sub_norm_le (vectorIntegral v Q hv) (vectorTaggedSum v P ξ)
  rw [norm_sub_rev] at hnorm
  have hs := vectorTaggedSum_norm_le v P ξ
  dsimp [ε] at hvP hnP
  linarith

theorem vectorTaggedSum_linear {m : ℕ} (A : E k →ₗ[ℝ] E m) (v : E n → E k)
    (P : Grid Q) (ξ : Tagging P) :
    vectorTaggedSum (fun x => A (v x)) P ξ = A (vectorTaggedSum v P ξ) := by
  change (∑ c, cellContent P c • A (v (ξ c))) = A (∑ c, cellContent P c • v (ξ c))
  rw [map_sum]
  simp only [map_smul]

theorem hasVectorTaggedIntegral_linear {m : ℕ} (A : E k →ₗ[ℝ] E m)
    {v : E n → E k} {I : E k} (hv : HasVectorTaggedIntegral v Q I) :
    HasVectorTaggedIntegral (fun x => A (v x)) Q (A I) := by
  intro ε hε
  have hA0 : 0 ≤ linearOperatorNorm A := (linear_norm_finite A).2
  have hd : 0 < linearOperatorNorm A + 1 := by linarith
  obtain ⟨δ, hδ, ht⟩ := hv (ε / (linearOperatorNorm A + 1)) (div_pos hε hd)
  refine ⟨δ, hδ, fun P ξ hP => ?_⟩
  change ‖vectorTaggedSum (fun x => A (v x)) P ξ - A I‖ < ε
  rw [vectorTaggedSum_linear, ← map_sub]
  have he := linear_apply_bound A (vectorTaggedSum v P ξ - I)
  have ht' := ht P ξ hP
  have heq : ε / (linearOperatorNorm A + 1) * (linearOperatorNorm A + 1) = ε :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hη := div_pos hε hd
  nlinarith [norm_nonneg (vectorTaggedSum v P ξ - I)]

theorem vectorBounded_linear {m : ℕ} (A : E k →ₗ[ℝ] E m)
    {v : E n → E k} (hb : VectorBounded v Q) : VectorBounded (fun x => A (v x)) Q := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨linearOperatorNorm A * M, fun x hx => (linear_apply_bound A _).trans
    (mul_le_mul_of_nonneg_left (hM x hx) (linear_norm_finite A).2)⟩

theorem vector_integrable_linear {n k m : ℕ} {Q : Box n} {v : E n → E k}
    (A : E k →ₗ[ℝ] E m) (hv : VectorIntegrable v Q) : VectorIntegrable (fun x => A (v x)) Q := by
  have hb := (vector_bounded_iff v Q).mpr (fun i => (hv i).1)
  exact (vector_tagged_criteria _ Q (vectorBounded_linear A hb)).1.mpr
    ⟨_, hasVectorTaggedIntegral_linear A ((vector_tagged_criteria v Q hb).2.1 hv)⟩

theorem vector_integral_linear {n k m : ℕ} {Q : Box n} {v : E n → E k}
    (A : E k →ₗ[ℝ] E m) (hv : VectorIntegrable v Q)
    (hA : VectorIntegrable (fun x => A (v x)) Q) :
    vectorIntegral (fun x => A (v x)) Q hA = A (vectorIntegral v Q hv) := by
  have hb := (vector_bounded_iff v Q).mpr (fun i => (hv i).1)
  exact vectorTaggedIntegral_unique
    ((vector_tagged_criteria _ Q (vectorBounded_linear A hb)).2.1 hA)
    (hasVectorTaggedIntegral_linear A ((vector_tagged_criteria v Q hb).2.1 hv))

theorem vector_degenerate (v : E n → E k) (hv : VectorIntegrable v Q)
    (hd : Degenerate Q) : vectorIntegral v Q hv = 0 := by
  ext i
  exact (degenerate_integrals (fun x => v x i) Q hd).1

theorem vector_zero_domain {k : ℕ} (Q : Box 0) (v : E 0 → E k) :
    ∃ hv : VectorIntegrable v Q, vectorIntegral v Q hv = v 0 := by
  refine ⟨fun i => (zero_dimension Q (fun x => v x i)).2.1, ?_⟩
  ext i
  exact (zero_dimension Q (fun x => v x i)).2.2.1

theorem vector_zero_target (Q : Box n) (v : E n → E 0) :
    ∃ hv : VectorIntegrable v Q, vectorIntegral v Q hv = 0 :=
  ⟨fun i => Fin.elim0 i, Subsingleton.elim _ _⟩

namespace Subdivision
open SingleVariableAnalysis.Riemann

/-- The consecutive sublist of a refining partition between two old endpoints. -/
def restrictPartition {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P) (c : Fin P.n) :
    Partition (P.point c.castSucc) (P.point c.succ) where
  n := (refinementIndex h c.succ).val - (refinementIndex h c.castSucc).val
  point j := R.point ⟨(refinementIndex h c.castSucc).val + j.val, by
    have he := refinementIndex_strictMono h (Fin.castSucc_lt_succ (i := c))
    have hu := (refinementIndex h c.succ).isLt
    have hj := j.isLt
    omega⟩
  strictMono := by
    intro i j hij
    apply R.strictMono
    change _ + i.val < _ + j.val
    exact Nat.add_lt_add_left hij _
  first := by
    apply Eq.trans _ (point_refinementIndex h c.castSucc)
    apply congrArg R.point
    apply Fin.ext
    exact Nat.add_zero _
  last := by
    apply Eq.trans _ (point_refinementIndex h c.succ)
    apply congrArg R.point
    apply Fin.ext
    have he := refinementIndex_strictMono h (Fin.castSucc_lt_succ (i := c))
    change _ + (_ - _) = _
    omega

def embedCell {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P) (c : Fin P.n)
    (j : Fin (restrictPartition h c).n) : Fin R.n :=
  ⟨(refinementIndex h c.castSucc).val + j.val, by
    have he := refinementIndex_strictMono h (Fin.castSucc_lt_succ (i := c))
    have hu := (refinementIndex h c.succ).isLt
    have hj := j.isLt
    change _ < _ - _ at hj
    omega⟩

theorem restrict_left {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P) (c : Fin P.n)
    (j : Fin (restrictPartition h c).n) :
    (restrictPartition h c).point j.castSucc = R.point (embedCell h c j).castSucc := rfl

theorem restrict_right {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P) (c : Fin P.n)
    (j : Fin (restrictPartition h c).n) :
    (restrictPartition h c).point j.succ = R.point (embedCell h c j).succ := by
  apply congrArg R.point
  apply Fin.ext
  change _ + (j.val + 1) = _ + j.val + 1
  omega

theorem embed_cell_subset {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P) (c : Fin P.n)
    (j : Fin (restrictPartition h c).n) : SingleVariableAnalysis.Riemann.cell R (embedCell h c j) ⊆ SingleVariableAnalysis.Riemann.cell P c := by
  have he : SingleVariableAnalysis.Riemann.cell R (embedCell h c j) = SingleVariableAnalysis.Riemann.cell (restrictPartition h c) j := by
    change Icc _ _ = Icc _ _
    rw [restrict_left, restrict_right]
  rw [he]
  exact cell_subset_interval _ j

/-- Each fine interval occurs in precisely one of the old consecutive blocks. -/
theorem embedCell_bijective {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P) :
    Function.Bijective (fun cj : Σ c : Fin P.n, Fin (restrictPartition h c).n =>
      embedCell h cj.1 cj.2) := by
  constructor
  · rintro ⟨c, j⟩ ⟨c', j'⟩ he
    change embedCell h c j = embedCell h c' j' at he
    have hc : c = c' := containing_interval_unique P R (embedCell h c j) c c'
      (embed_cell_subset h c j) (by rw [he]; exact embed_cell_subset h c' j')
    subst c'
    have hj : j = j' := by
      apply Fin.ext
      have hh := congrArg Fin.val he
      change (refinementIndex h c.castSucc).val + j.val =
        (refinementIndex h c.castSucc).val + j'.val at hh
      omega
    subst j'
    rfl
  · intro j
    obtain ⟨c, hc⟩ := Step.refinement_cell_contained P R h j
    have hl := (hc (show R.point j.castSucc ∈ SingleVariableAnalysis.Riemann.cell R j from
      ⟨le_rfl, (R.strictMono (Fin.castSucc_lt_succ (i := j))).le⟩)).1
    have hu := (hc (show R.point j.succ ∈ SingleVariableAnalysis.Riemann.cell R j from
      ⟨(R.strictMono (Fin.castSucc_lt_succ (i := j))).le, le_rfl⟩)).2
    rw [← point_refinementIndex h c.castSucc] at hl
    rw [← point_refinementIndex h c.succ] at hu
    have hl' := R.strictMono.le_iff_le.mp hl
    have hu' := R.strictMono.le_iff_le.mp hu
    let d : Fin (restrictPartition h c).n := ⟨j.val - (refinementIndex h c.castSucc).val, by
      change _ < _ - _
      change _ ≤ j.val at hl'
      change j.val + 1 ≤ _ at hu'
      omega⟩
    refine ⟨⟨c, d⟩, ?_⟩
    change embedCell h c d = j
    apply Fin.ext
    change (refinementIndex h c.castSucc).val + (j.val - (refinementIndex h c.castSucc).val) = j.val
    change _ ≤ j.val at hl'
    omega

def cellEquiv {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P) :
    (Σ c : Fin P.n, Fin (restrictPartition h c).n) ≃ Fin R.n :=
  Equiv.ofBijective _ (embedCell_bijective h)

/-- A restricted sublist retains exactly the refining cuts in the old cell. -/
theorem points_restrictPartition {a b : ℝ} {P R : Partition a b} (h : SingleVariableAnalysis.Riemann.Refines R P)
    (c : Fin P.n) (x : ℝ) :
    x ∈ points (restrictPartition h c) ↔ x ∈ points R ∧ x ∈ SingleVariableAnalysis.Riemann.cell P c := by
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
      (endpoints (restrictPartition h c)).2.2 _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)⟩
  · rintro ⟨hx, hl, hu⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [← point_refinementIndex h c.castSucc] at hl
    rw [← point_refinementIndex h c.succ] at hu
    have hl' := R.strictMono.le_iff_le.mp hl
    have hu' := R.strictMono.le_iff_le.mp hu
    let d : Fin ((restrictPartition h c).n + 1) :=
      ⟨j.val - (refinementIndex h c.castSucc).val, by
        change _ < _ - _ + 1
        change _ ≤ j.val at hl'
        change j.val ≤ _ at hu'
        omega⟩
    refine Finset.mem_image.mpr ⟨d, Finset.mem_univ _, ?_⟩
    apply congrArg R.point
    apply Fin.ext
    change _ + (j.val - _) = j.val
    change _ ≤ j.val at hl'
    omega

end Subdivision
namespace Subdivision

def restrictGrid {P R : Grid Q} (h : Refines R P) (c : CellIndex P) : Grid (cellBox P c) :=
  fun i => restrictPartition (h i) (c i)

def embedGridCell {P R : Grid Q} (h : Refines R P) (c : CellIndex P)
    (d : CellIndex (restrictGrid h c)) : CellIndex R := fun i => embedCell (h i) (c i) (d i)

def gridCellEquiv {P R : Grid Q} (h : Refines R P) :
    (Σ c : CellIndex P, CellIndex (restrictGrid h c)) ≃ CellIndex R := by
  apply Equiv.ofBijective (fun cd => embedGridCell h cd.1 cd.2)
  constructor
  · rintro ⟨c, d⟩ ⟨c', d'⟩ he
    have hc : c = c' := by
      funext i
      have hh : (⟨c i, d i⟩ : Σ j : Fin (P i).n, Fin (restrictPartition (h i) j).n) = ⟨c' i, d' i⟩ := by
        apply (cellEquiv (h i)).injective
        exact congrFun he i
      exact congrArg Sigma.fst hh
    subst c'
    have hd : d = d' := by
      funext i
      apply Fin.ext
      have hh := congrArg (fun z => (z i).val) he
      change (SingleVariableAnalysis.Riemann.refinementIndex (h i) (c i).castSucc).val + (d i).val =
        (SingleVariableAnalysis.Riemann.refinementIndex (h i) (c i).castSucc).val + (d' i).val at hh
      omega
    subst d'
    rfl
  · intro j
    let c : CellIndex P := fun i => ((cellEquiv (h i)).symm (j i)).1
    let d : CellIndex (restrictGrid h c) := fun i => ((cellEquiv (h i)).symm (j i)).2
    exact ⟨⟨c, d⟩, funext (fun i => (cellEquiv (h i)).apply_symm_apply (j i))⟩

theorem box_ext {A B : Box n} (hl : A.lower = B.lower) (hu : A.upper = B.upper) : A = B := by
  cases A
  cases B
  cases hl
  cases hu
  rfl

theorem cellBox_embed {P R : Grid Q} (h : Refines R P) (c : CellIndex P)
    (d : CellIndex (restrictGrid h c)) :
    cellBox (restrictGrid h c) d = cellBox R (embedGridCell h c d) := by
  apply box_ext
  · ext i
    exact restrict_left (h i) (c i) (d i)
  · ext i
    exact restrict_right (h i) (c i) (d i)

theorem grid_sum_split {P R : Grid Q} (h : Refines R P) (w : CellIndex R → ℝ) :
    ∑ j, w j = ∑ c, ∑ d : CellIndex (restrictGrid h c), w (embedGridCell h c d) := by
  rw [← (gridCellEquiv h).sum_comp w]
  exact Fintype.sum_sigma _

theorem lowerSum_split (f : E n → ℝ) {P R : Grid Q} (h : Refines R P) :
    lowerSum f R = ∑ c, lowerSum f (restrictGrid h c) := by
  change (∑ j, cellInfimum f R j * cellContent R j) = _
  rw [grid_sum_split h]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  change sInf (f '' carrier (cellBox R _)) * content (cellBox R _) =
    sInf (f '' carrier (cellBox (restrictGrid h c) d)) * content (cellBox (restrictGrid h c) d)
  rw [cellBox_embed h c d]

theorem upperSum_split (f : E n → ℝ) {P R : Grid Q} (h : Refines R P) :
    upperSum f R = ∑ c, upperSum f (restrictGrid h c) := by
  change (∑ j, cellSupremum f R j * cellContent R j) = _
  rw [grid_sum_split h]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  change sSup (f '' carrier (cellBox R _)) * content (cellBox R _) =
    sSup (f '' carrier (cellBox (restrictGrid h c) d)) * content (cellBox (restrictGrid h c) d)
  rw [cellBox_embed h c d]

theorem gap_split (f : E n → ℝ) {P R : Grid Q} (h : Refines R P) :
    upperSum f R - lowerSum f R =
      ∑ c, (upperSum f (restrictGrid h c) - lowerSum f (restrictGrid h c)) := by
  rw [upperSum_split f h, lowerSum_split f h, Finset.sum_sub_distrib]

/-- Insert all coordinate cuts from a finite family of grids on old cells. -/
theorem extend_cell_grids (P : Grid Q) (S : ∀ c : CellIndex P, Grid (cellBox P c)) :
    ∃ R : Grid Q, ∃ h : Refines R P, ∀ c, Refines (restrictGrid h c) (S c) := by
  classical
  let cuts (i : Fin n) := SingleVariableAnalysis.Riemann.points (P i) ∪
    Finset.univ.biUnion (fun c : CellIndex P => SingleVariableAnalysis.Riemann.points (S c i))
  have hlow (i : Fin n) : Q.lower i ∈ cuts i := Finset.mem_union_left _
    (SingleVariableAnalysis.Riemann.endpoints (P i)).1
  have hupp (i : Fin n) : Q.upper i ∈ cuts i := Finset.mem_union_left _
    (SingleVariableAnalysis.Riemann.endpoints (P i)).2.1
  have hbound (i : Fin n) : ∀ x ∈ cuts i, x ∈ Icc (Q.lower i) (Q.upper i) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (SingleVariableAnalysis.Riemann.endpoints (P i)).2.2 x hx
    · obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hx
      exact SingleVariableAnalysis.Riemann.cell_subset_interval (P i) (c i)
        ((SingleVariableAnalysis.Riemann.endpoints (S c i)).2.2 x hc)
  let R : Grid Q := fun i => SingleVariableAnalysis.Riemann.ofPoints (cuts i) (hlow i) (hupp i) (hbound i)
  have hR (i : Fin n) : SingleVariableAnalysis.Riemann.points (R i) = cuts i :=
    SingleVariableAnalysis.Riemann.points_ofPoints _ _ _ _
  have h : Refines R P := by
    intro i
    change SingleVariableAnalysis.Riemann.points (P i) ⊆ SingleVariableAnalysis.Riemann.points (R i)
    rw [hR]
    exact Finset.subset_union_left
  refine ⟨R, h, fun c i x hx => ?_⟩
  apply (points_restrictPartition (h i) (c i) x).mpr
  constructor
  · rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hx⟩)
  · exact (SingleVariableAnalysis.Riemann.endpoints (S c i)).2.2 x hx

end Subdivision
/-- Boundedness restricts to the actual closed cells, including their faces. -/
theorem bounded_cell (f : E n → ℝ) (hb : Bounded f Q) (P : Grid Q) (c : CellIndex P) :
    Bounded f (cellBox P c) := cell_image_bounded f hb P c

theorem subdivision_integrable (f : E n → ℝ) (Q : Box n) (hb : Bounded f Q) (P : Grid Q) :
    Integrable f Q ↔ ∀ c, Integrable f (cellBox P c) := by
  classical
  have hbc (c : CellIndex P) : Bounded f (cellBox P c) := bounded_cell f hb P c
  constructor
  · intro hf c
    apply (integrable_iff_gap f (cellBox P c) (hbc c)).mpr
    intro ε hε
    obtain ⟨R, hR⟩ := (integrable_iff_gap f Q hb).mp hf ε hε
    obtain ⟨T, hTP, hTR⟩ := common_refinement P R
    have hgap : upperSum f T - lowerSum f T < ε := by
      have hu := upper_refinement f hb R T hTR
      have hl := lower_refinement f hb R T hTR
      linarith
    refine ⟨Subdivision.restrictGrid hTP c, lt_of_le_of_lt ?_ hgap⟩
    rw [Subdivision.gap_split f hTP]
    apply Finset.single_le_sum _ (Finset.mem_univ c)
    intro d _
    exact sub_nonneg.mpr (same_grid_lower_le_upper f (hbc d) _)
  · intro hc
    apply (integrable_iff_gap f Q hb).mpr
    intro ε hε
    let η := ε / ((Fintype.card (CellIndex P) : ℝ) + 1)
    have hd : 0 < (Fintype.card (CellIndex P) : ℝ) + 1 := by positivity
    have hη : 0 < η := div_pos hε hd
    have hs (c : CellIndex P) : ∃ S : Grid (cellBox P c),
        upperSum f S - lowerSum f S < η :=
      (integrable_iff_gap f (cellBox P c) (hbc c)).mp (hc c) η hη
    choose S hS using hs
    obtain ⟨R, h, hRS⟩ := Subdivision.extend_cell_grids P S
    refine ⟨R, ?_⟩
    rw [Subdivision.gap_split f h]
    calc
      _ ≤ ∑ _c : CellIndex P, η := by
        apply Finset.sum_le_sum
        intro c _
        have hu := upper_refinement f (hbc c) (S c) (Subdivision.restrictGrid h c) (hRS c)
        have hl := lower_refinement f (hbc c) (S c) (Subdivision.restrictGrid h c) (hRS c)
        linarith [hS c]
      _ = (Fintype.card (CellIndex P) : ℝ) * η := by simp
      _ < ε := by
        have heq : η * ((Fintype.card (CellIndex P) : ℝ) + 1) = ε :=
          div_mul_cancel₀ _ (ne_of_gt hd)
        nlinarith

/-- Closed common faces carry no extra term in grid additivity. -/
theorem subdivision_integral (f : E n → ℝ) (Q : Box n) (P : Grid Q)
    (hf : Integrable f Q) (hc : ∀ c, Integrable f (cellBox P c)) :
    integral f Q hf = ∑ c, integral f (cellBox P c) (hc c) := by
  classical
  by_contra hne
  have hp : 0 < |integral f Q hf - ∑ c, integral f (cellBox P c) (hc c)| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨R, hR⟩ := (integrable_iff_gap f Q hf.1).mp hf _ hp
  obtain ⟨T, hTP, hTR⟩ := common_refinement P R
  have hgap : upperSum f T - lowerSum f T <
      |integral f Q hf - ∑ c, integral f (cellBox P c) (hc c)| := by
    have hu := upper_refinement f hf.1 R T hTR
    have hl := lower_refinement f hf.1 R T hTR
    linarith
  have hL : lowerSum f T ≤ ∑ c, integral f (cellBox P c) (hc c) := by
    rw [Subdivision.lowerSum_split f hTP]
    exact Finset.sum_le_sum fun c _ => (integral_bounds f _ (hc c) _).1
  have hU : (∑ c, integral f (cellBox P c) (hc c)) ≤ upperSum f T := by
    rw [Subdivision.upperSum_split f hTP]
    exact Finset.sum_le_sum fun c _ => (integral_bounds f _ (hc c) _).2
  have hI := integral_bounds f Q hf T
  have ha : |integral f Q hf - ∑ c, integral f (cellBox P c) (hc c)| ≤
      upperSum f T - lowerSum f T := abs_le.mpr ⟨by linarith [hI.1], by linarith [hI.2]⟩
  linarith

end D04.Darboux
