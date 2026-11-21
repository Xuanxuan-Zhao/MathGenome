import Mathlib.Data.Fin.Rev
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Oriented
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.TaggedEquivalence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.HeineCantor

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators Topology
open Set

/-- Prepending a positive cell to a strict partition. -/
def prependPartition {v w : ℝ} (u : ℝ) (huv : u < v) (Q : Partition v w) :
    Partition u w where
  n := Q.n + 1
  point := Fin.cases u Q.point
  strictMono := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (lt_irrefl _ hij)
      | succ j =>
        change u < Q.point j
        exact huv.trans_le (by simpa only [Q.first] using Q.strictMono.monotone (Fin.zero_le j))
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (by simp at hij)
      | succ j => exact Q.strictMono (Fin.succ_lt_succ_iff.mp hij)
  first := rfl
  last := by
    change Fin.cases u Q.point (Fin.last Q.n).succ = w
    exact Q.last

@[simp] theorem prepend_point_zero {v w : ℝ} (u : ℝ) (huv : u < v)
    (Q : Partition v w) : (prependPartition u huv Q).point 0 = u := rfl

@[simp] theorem prepend_point_succ {v w : ℝ} (u : ℝ) (huv : u < v)
    (Q : Partition v w) (i : Fin (Q.n + 1)) :
    (prependPartition u huv Q).point i.succ = Q.point i := rfl

/-- Weakly increasing endpoint lists can be compressed, retaining all positive
increments, every tag on those increments, and a bound for the mesh. -/
theorem compress_monotone_tagged {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ℝ → E) (n : ℕ) (y : Fin (n + 1) → ℝ) (hy : Monotone y)
    (z : Fin n → ℝ) (hz : ∀ i, z i ∈ Icc (y i.castSucc) (y i.succ))
    (D : ℝ) (hD : 0 ≤ D) (hstep : ∀ i : Fin n, y i.succ - y i.castSucc ≤ D) :
    ∃ (Q : Partition (y 0) (y (Fin.last n))) (ζ : Tagging Q),
      mesh Q ≤ D ∧ taggedSum Q ζ f =
        ∑ i : Fin n, (y i.succ - y i.castSucc) • f (z i) := by
  induction n with
  | zero =>
    refine ⟨emptyPartition (y 0), (tags_exist _).some, ?_, ?_⟩
    · rw [mesh_eq_zero_of_n_eq_zero (emptyPartition (y 0)) rfl]
      exact hD
    · change (∑ i : Fin 0, _) = (∑ i : Fin 0, _)
      simp
  | succ n ih =>
    obtain ⟨Q, ζ, hmesh, hsum⟩ := ih (fun i => y i.succ)
      (hy.comp (fun _ _ h => Fin.succ_le_succ_iff.mpr h))
      (fun i => z i.succ) (fun i => hz i.succ) (fun i => hstep i.succ)
    have h01 : y 0 ≤ y (0 : Fin (n+1)).succ := hy (Fin.zero_le _)
    rcases h01.eq_or_lt with heq | hlt
    · let R : Partition (y 0) (y (Fin.last (n+1))) :=
        ⟨Q.n, Q.point, Q.strictMono, Q.first.trans heq.symm, Q.last⟩
      refine ⟨R, ζ, hmesh, ?_⟩
      rw [Fin.sum_univ_succ]
      simpa only [Fin.castSucc_zero, heq, sub_self, zero_smul, zero_add,
        ← Fin.succ_castSucc, taggedSum, S.sumValue, S.lengthValue, R] using hsum
    · let R := prependPartition (y 0) hlt Q
      have hleft : cellLength R (0 : Fin (Q.n+1)) = y (0 : Fin (n+1)).succ - y 0 := by
        change Q.point 0 - y 0 = _
        rw [Q.first]
      have hright (i : Fin Q.n) : cellLength R i.succ = cellLength Q i := rfl
      let η : Tagging R := Fin.cases
        ⟨z 0, by simpa only [R, prependPartition, Fin.castSucc_zero, Fin.cases_zero,
          Fin.cases_succ, Q.first] using hz 0⟩
        (fun i => ⟨ζ i, (ζ i).property⟩)
      refine ⟨R, η, mesh_le R hD ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [hleft]
          exact hstep 0
        · rw [hright]
          exact (cellLength_le_mesh Q i).trans hmesh
      · change (∑ i : Fin (Q.n+1), cellLength R i • f (η i)) = _
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [η, Fin.cases_zero, Fin.cases_succ, hleft, hright, Fin.castSucc_zero]
        simpa only [← Fin.succ_castSucc, taggedSum, S.sumValue] using
          congrArg (fun x => (y (0 : Fin (n+1)).succ - y 0) • f (z 0) + x) hsum

/-- A fine-tagged limit also controls weakly increasing lists with zero cells. -/
theorem FineTaggedLimit.monotone_list {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {A B : ℝ} {I : E} (hf : FineTaggedLimit f A B I)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (y : Fin (n+1) → ℝ), Monotone y →
      y 0 = A → y (Fin.last n) = B →
      ∀ z : Fin n → ℝ, (∀ i, z i ∈ Icc (y i.castSucc) (y i.succ)) →
      ∀ D : ℝ, 0 ≤ D → D < δ → (∀ i : Fin n, y i.succ - y i.castSucc ≤ D) →
        ‖(∑ i : Fin n, (y i.succ - y i.castSucc) • f (z i)) - I‖ < ε := by
  obtain ⟨δ, hδ, hc⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n y hy hA hB z hz D hD hDδ hstep
  obtain ⟨Q, ζ, hmesh, hsum⟩ := compress_monotone_tagged f n y hy z hz D hD hstep
  subst A; subst B
  rw [← hsum]
  exact hc Q ζ (hmesh.trans_lt hDδ)


/-- Reversing a weakly decreasing list reverses its signed sum. -/
theorem FineTaggedLimit.antitone_list {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {A B : ℝ} {I : E} (hf : FineTaggedLimit f B A I)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (y : Fin (n+1) → ℝ), Antitone y →
      y 0 = A → y (Fin.last n) = B →
      ∀ z : Fin n → ℝ, (∀ i, z i ∈ Icc (y i.succ) (y i.castSucc)) →
      ∀ D : ℝ, 0 ≤ D → D < δ → (∀ i : Fin n, y i.castSucc - y i.succ ≤ D) →
        ‖(∑ i : Fin n, (y i.succ - y i.castSucc) • f (z i)) - (-I)‖ < ε := by
  obtain ⟨δ, hδ, hc⟩ := hf.monotone_list ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n y hy hA hB z hz D hD hDδ hstep
  have hr := hc n (fun i => y i.rev)
    (fun i j hij => hy (Fin.rev_le_rev.mpr hij))
    (by simpa using hB) (by simpa using hA)
    (fun i => z i.rev) (fun i => by simpa only [Fin.rev_castSucc, Fin.rev_succ] using hz i.rev) D hD hDδ
    (fun i => by simpa only [Fin.rev_castSucc, Fin.rev_succ] using hstep i.rev)
  have he : (∑ i : Fin n, (y i.succ.rev - y i.castSucc.rev) • f (z i.rev)) =
      -(∑ i : Fin n, (y i.succ - y i.castSucc) • f (z i)) := by
    simp only [Fin.rev_succ, Fin.rev_castSucc]
    calc
      _ = ∑ i : Fin n, -((y i.rev.succ - y i.rev.castSucc) • f (z i.rev)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← neg_sub (y i.rev.succ) (y i.rev.castSucc), neg_smul]
      _ = -(∑ i : Fin n, (y i.rev.succ - y i.rev.castSucc) • f (z i.rev)) :=
        Finset.sum_neg_distrib _
      _ = _ := by
        have hs := Equiv.sum_comp Fin.revPerm
          (fun i : Fin n => (y i.succ - y i.castSucc) • f (z i))
        exact congrArg Neg.neg hs
  rw [he] at hr
  calc
    _ = ‖-(∑ i : Fin n, (y i.succ - y i.castSucc) • f (z i)) - I‖ := by
      rw [← norm_neg ((∑ i : Fin n, (y i.succ - y i.castSucc) • f (z i)) - -I)]
      congr 1
      abel
    _ < ε := hr

abbrev C1OnInterval := Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution.C1OnInterval

theorem C1OnInterval.continuousOn {φ dφ : ℝ → ℝ} {a b : ℝ}
    (h : C1OnInterval φ dφ a b) : ContinuousOn φ (Icc a b) :=
  fun t ht => (h.2 t ht).continuousWithinAt

theorem C1OnInterval.hasDerivAt {φ dφ : ℝ → ℝ} {a b t : ℝ}
    (h : C1OnInterval φ dφ a b) (ht : t ∈ Ioo a b) : HasDerivAt φ (dφ t) t :=
  (h.2 t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Mean-value tags lie inside the original interval, including when its
endpoints are endpoints of the domain of C¹ data. -/
theorem C1OnInterval.mean_value {φ dφ : ℝ → ℝ} {a b u v : ℝ}
    (h : C1OnInterval φ dφ a b) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b)
    (huv : u < v) : ∃ c ∈ Icc u v, φ v - φ u = dφ c * (v-u) := by
  obtain ⟨c, hc, heq⟩ := SingleVariableAnalysis.lagrange_deriv φ u v huv
    (h.continuousOn.mono (Icc_subset_Icc hu.1 hv.2))
    (fun t ht => (h.hasDerivAt ⟨hu.1.trans_lt ht.1, ht.2.trans_le hv.2⟩).differentiableAt)
  refine ⟨c, ⟨hc.1.le, hc.2.le⟩, ?_⟩
  rw [(h.hasDerivAt ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩).deriv] at heq
  exact heq

/-- A positive bound for the derivative, with a uniform bound for secants. -/
theorem C1OnInterval.secant_bound {φ dφ : ℝ → ℝ} {a b : ℝ}
    (h : C1OnInterval φ dφ a b) :
    ∃ L > 0, (∀ t ∈ Icc a b, |dφ t| ≤ L) ∧
      ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → |φ v - φ u| ≤ L * (v-u) := by
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image h.1.norm
  let K := max L 0 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hb (t : ℝ) (ht : t ∈ Icc a b) : |dφ t| ≤ K := by
    have htL := hL (mem_image_of_mem (fun t => ‖dφ t‖) ht)
    simp only [Real.norm_eq_abs] at htL
    exact htL.trans (by dsimp [K]; linarith [le_max_left L 0])
  refine ⟨K, hK, hb, ?_⟩
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · simp
  · obtain ⟨c, hc, heq⟩ := h.mean_value hu hv huv
    rw [heq, abs_mul, abs_of_pos (sub_pos.mpr huv)]
    exact mul_le_mul_of_nonneg_right (hb c ⟨hu.1.trans hc.1, hc.2.trans hv.2⟩)
      (sub_nonneg.mpr huv.le)

/-- Uniform continuity of φ′ controls its difference from every cell's
mean slope. The statement is uniform in the partition and all its tags. -/
theorem C1OnInterval.cell_error {φ dφ : ℝ → ℝ} {a b : ℝ}
    (h : C1OnInterval φ dφ a b) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ (P : Partition a b) (ξ : Tagging P), mesh P < δ →
      ∀ i : Fin P.n,
        |cellLength P i * dφ (ξ i) - (φ (P.point i.succ) - φ (P.point i.castSucc))| ≤
          η * cellLength P i := by
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous h.1) η hη
  refine ⟨δ, hδ, ?_⟩
  intro P ξ hP i
  have hl := cell_subset_interval P i
  have hle := (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
  have hu : P.point i.castSucc ∈ Icc a b := hl ⟨le_rfl, hle⟩
  have hv : P.point i.succ ∈ Icc a b := hl ⟨hle, le_rfl⟩
  obtain ⟨c, hcCell, heq⟩ := h.mean_value hu hv (sub_pos.mp (cell_positive P i))
  have hdist : dist (ξ i : ℝ) c < δ := by
    rw [Real.dist_eq]
    have hd : |(ξ i : ℝ) - c| ≤ cellLength P i := abs_le.mpr
      ⟨by dsimp [cellLength, S.lengthValue]; linarith [(ξ i).property.1, hcCell.2],
       by dsimp [cellLength, S.lengthValue]; linarith [(ξ i).property.2, hcCell.1]⟩
    exact hd.trans_lt ((cellLength_le_mesh P i).trans_lt hP)
  have hd := (hc (ξ i) (hl (ξ i).property) c (hl hcCell) hdist).le
  rw [Real.dist_eq] at hd
  rw [heq]
  change |cellLength P i * dφ (ξ i) - dφ c * cellLength P i| ≤ _
  calc
    _ = |dφ (ξ i) - dφ c| * cellLength P i := by
      rw [show cellLength P i * dφ (ξ i) - dφ c * cellLength P i =
        (dφ (ξ i) - dφ c) * cellLength P i by ring,
        abs_mul, abs_of_pos (show 0 < cellLength P i from cell_positive P i)]
    _ ≤ η * cellLength P i := mul_le_mul_of_nonneg_right hd (cell_positive P i).le


/-- Stieltjes-style finite sum induced by the endpoint values of φ. -/
noncomputable def imageTaggedSum {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b : ℝ} (P : Partition a b) (ξ : Tagging P) (φ : ℝ → ℝ) (f : ℝ → E) : E :=
  ∑ i : Fin P.n, (φ (P.point i.succ) - φ (P.point i.castSucc)) • f (φ (ξ i))

/-- The sole analytic error in replacing derivatives by image increments. -/
theorem taggedSum_image_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (P : Partition a b) (ξ : Tagging P) (φ dφ : ℝ → ℝ) (f : ℝ → E)
    (M η : ℝ) (hη : 0 ≤ η)
    (hf : ∀ t ∈ Icc a b, ‖f (φ t)‖ ≤ M)
    (herr : ∀ i : Fin P.n,
      |cellLength P i * dφ (ξ i) - (φ (P.point i.succ) - φ (P.point i.castSucc))| ≤
        η * cellLength P i) :
    ‖taggedSum P ξ (fun t => dφ t • f (φ t)) - imageTaggedSum P ξ φ f‖ ≤
      η * M * (b-a) := by
  have he : taggedSum P ξ (fun t => dφ t • f (φ t)) - imageTaggedSum P ξ φ f =
      ∑ i : Fin P.n,
        (cellLength P i * dφ (ξ i) - (φ (P.point i.succ) - φ (P.point i.castSucc))) •
          f (φ (ξ i)) := by
    simp only [taggedSum, S.sumValue, imageTaggedSum, ← mul_smul, sub_smul,
      Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i : Fin P.n,
        ‖(cellLength P i * dφ (ξ i) - (φ (P.point i.succ) - φ (P.point i.castSucc))) •
          f (φ (ξ i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, (η * cellLength P i) * M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (herr i) (hf (ξ i) (cell_subset_interval P i (ξ i).property))
        (norm_nonneg _) (mul_nonneg hη (cell_positive P i).le)
    _ = η * M * (b-a) := by
      simp_rw [show ∀ i : Fin P.n, η * cellLength P i * M = η * M * cellLength P i
        from fun i => by ring]
      rw [← Finset.mul_sum, sum_cellLength]

/-- Once the image sums have a limit, the transformed ordinary sums have
that limit too. This implication requires no monotonicity of φ. -/
theorem fineTaggedLimit_of_image_sums {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ dφ : ℝ → ℝ} {f : ℝ → E} {a b : ℝ} {I : E}
    (hab : a ≤ b) (h : C1OnInterval φ dφ a b)
    (hf : ∃ M : ℝ, ∀ t ∈ Icc a b, ‖f (φ t)‖ ≤ M)
    (hi : ∀ ε > 0, ∃ δ > 0, ∀ (P : Partition a b) (ξ : Tagging P),
      mesh P < δ → ‖imageTaggedSum P ξ φ f - I‖ < ε) :
    FineTaggedLimit (fun t => dφ t • f (φ t)) a b I := by
  obtain ⟨M₀, hM₀⟩ := hf
  let M := max M₀ 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb (t : ℝ) (ht : t ∈ Icc a b) : ‖f (φ t)‖ ≤ M :=
    (hM₀ t ht).trans (by dsimp [M]; linarith [le_max_left M₀ 0])
  intro ε hε
  let η := ε / (4 * M * (b-a+1))
  have hlen : 0 < b-a+1 := by linarith
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ₁, hδ₁, hc₁⟩ := h.cell_error η hη
  obtain ⟨δ₂, hδ₂, hc₂⟩ := hi (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro P ξ hP
  have herr := taggedSum_image_error P ξ φ dφ f M η hη.le hb
    (hc₁ P ξ (hP.trans_le (min_le_left _ _)))
  have hsmall : η * M * (b-a) < ε / 2 := by
    have he : η * M * (b-a+1) = ε / 4 := by
      dsimp [η]
      field_simp
    nlinarith [mul_pos hη hM]
  have hiClose := hc₂ P ξ (hP.trans_le (min_le_right _ _))
  have hn := norm_add_le
    (taggedSum P ξ (fun t => dφ t • f (φ t)) - imageTaggedSum P ξ φ f)
    (imageTaggedSum P ξ φ f - I)
  rw [sub_add_sub_cancel] at hn
  exact hn.trans_lt (by linarith)

/-- The original all-tagged limit controls image sums for a nondecreasing
C¹ map. No inverse and no positive lower bound for φ′ is needed. -/
theorem image_sums_monotone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ dφ : ℝ → ℝ} {f : ℝ → E} {a b : ℝ} {I : E}
    (h : C1OnInterval φ dφ a b) (hm : MonotoneOn φ (Icc a b))
    (hf : FineTaggedLimit f (φ a) (φ b) I) :
    ∀ ε > 0, ∃ δ > 0, ∀ (P : Partition a b) (ξ : Tagging P),
      mesh P < δ → ‖imageTaggedSum P ξ φ f - I‖ < ε := by
  obtain ⟨L, hL, _, hsec⟩ := h.secant_bound
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hf.monotone_list ε hε
  refine ⟨δ / L, div_pos hδ hL, ?_⟩
  intro P ξ hP
  have hpoint (i : Fin (P.n+1)) : P.point i ∈ Icc a b :=
    (endpoints P).2.2 _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  apply hc P.n (fun i => φ (P.point i))
    (fun i j hij => hm (hpoint i) (hpoint j) (P.strictMono.monotone hij))
    (congrArg φ P.first) (congrArg φ P.last) (fun i => φ (ξ i))
    (fun i => ⟨hm (hpoint _) (cell_subset_interval P i (ξ i).property) (ξ i).property.1,
      hm (cell_subset_interval P i (ξ i).property) (hpoint _) (ξ i).property.2⟩)
    (L * mesh P) (mul_nonneg hL.le (mesh_nonneg P))
    (by have := (lt_div_iff₀ hL).mp hP; linarith)
  intro i
  exact (le_abs_self _).trans ((hsec _ (hpoint _) _ (hpoint _)
    (P.strictMono.monotone (Fin.castSucc_le_succ i))).trans
      (mul_le_mul_of_nonneg_left (cellLength_le_mesh P i) hL.le))

/-- The reversed image list gives the orientation sign for decreasing maps. -/
theorem image_sums_antitone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ dφ : ℝ → ℝ} {f : ℝ → E} {a b : ℝ} {I : E}
    (h : C1OnInterval φ dφ a b) (hm : AntitoneOn φ (Icc a b))
    (hf : FineTaggedLimit f (φ b) (φ a) I) :
    ∀ ε > 0, ∃ δ > 0, ∀ (P : Partition a b) (ξ : Tagging P),
      mesh P < δ → ‖imageTaggedSum P ξ φ f - (-I)‖ < ε := by
  obtain ⟨L, hL, _, hsec⟩ := h.secant_bound
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hf.antitone_list ε hε
  refine ⟨δ / L, div_pos hδ hL, ?_⟩
  intro P ξ hP
  have hpoint (i : Fin (P.n+1)) : P.point i ∈ Icc a b :=
    (endpoints P).2.2 _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  apply hc P.n (fun i => φ (P.point i))
    (fun i j hij => hm (hpoint i) (hpoint j) (P.strictMono.monotone hij))
    (congrArg φ P.first) (congrArg φ P.last) (fun i => φ (ξ i))
    (fun i => ⟨hm (cell_subset_interval P i (ξ i).property) (hpoint _) (ξ i).property.2,
      hm (hpoint _) (cell_subset_interval P i (ξ i).property) (ξ i).property.1⟩)
    (L * mesh P) (mul_nonneg hL.le (mesh_nonneg P))
    (by have := (lt_div_iff₀ hL).mp hP; linarith)
  intro i
  have hs : |φ (P.point i.castSucc) - φ (P.point i.succ)| ≤ L * cellLength P i := by
    simpa only [abs_sub_comm, cellLength, S.lengthValue] using
      (hsec _ (hpoint i.castSucc) _ (hpoint i.succ)
        (P.strictMono.monotone (Fin.castSucc_le_succ i)))
  exact (le_abs_self _).trans (hs.trans
    (mul_le_mul_of_nonneg_left (cellLength_le_mesh P i) hL.le))


/-- Non-strict monotonicity puts the full image in the endpoint hull. -/
theorem monotone_image_mem_hull {φ : ℝ → ℝ} {a b t : ℝ}
    (hm : MonotoneOn φ (Icc a b) ∨ AntitoneOn φ (Icc a b)) (ht : t ∈ Icc a b) :
    φ t ∈ Icc (min (φ a) (φ b)) (max (φ a) (φ b)) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hb : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
  rcases hm with hm | hm
  · exact ⟨(min_le_left _ _).trans (hm ha ht ht.1),
      (hm ht hb ht.2).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (hm ht hb ht.2),
      (hm ha ht ht.1).trans (le_max_left _ _)⟩

/-- Boundedness of the transformed product is proved independently of its
integrability, also on flat portions and singleton intervals. -/
theorem transformed_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ dφ : ℝ → ℝ} {f : ℝ → E} {a b : ℝ} (h : C1OnInterval φ dφ a b)
    (hf : ∃ M : ℝ, ∀ t ∈ Icc a b, ‖f (φ t)‖ ≤ M) :
    ∃ C : ℝ, ∀ t ∈ Icc a b, ‖dφ t • f (φ t)‖ ≤ C := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨L, _, hL, _⟩ := h.secant_bound
  refine ⟨L * max M 0, ?_⟩
  intro t ht
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hL t ht) ((hM t ht).trans (le_max_left _ _))
    (norm_nonneg _) (by linarith [hL t ht, abs_nonneg (dφ t)])

/-- Monotone C¹ substitution for the proper real Darboux integral. -/
theorem real_monotone_substitution :
    Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution.realMonotoneSubstitution := by
  intro φ dφ f a b hab h hm hf
  have hfb : ∃ M : ℝ, ∀ t ∈ Icc a b, ‖f (φ t)‖ ≤ M := by
    obtain ⟨M, hM⟩ := (RealIntegrable.bounded hf).abs_bound
    refine ⟨M, ?_⟩
    intro t ht
    simpa only [Real.norm_eq_abs] using hM (φ t) (monotone_image_mem_hull hm ht)
  have hgb : BoundedOnInterval (fun t => dφ t * f (φ t)) a b := by
    obtain ⟨M, hM⟩ := transformed_norm_bound h hfb
    exact boundedOnInterval_of_abs (fun t ht => by
      simpa only [smul_eq_mul, Real.norm_eq_abs] using hM t ht)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rcases hm with hm | hm
  · have hAB := hm ha hb hab
    have hf' : RealIntegrable f (φ a) (φ b) := by
      simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue, min_eq_left hAB,
        max_eq_right hAB] using hf
    have hfLim := (real_tagged_equivalence f hAB hf'.bounded _).mp ⟨hf', rfl⟩
    have hgLim := fineTaggedLimit_of_image_sums hab h hfb (image_sums_monotone h hm hfLim)
    obtain ⟨hg, hv⟩ := (real_tagged_equivalence _ hab hgb _).mpr hgLim
    exact ⟨hg, hv.trans (oriented_real_agreement f hAB hf hf').symm⟩
  · have hBA := hm ha hb hab
    have hf' : RealIntegrable f (φ b) (φ a) := by
      simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue, min_eq_right hBA,
        max_eq_left hBA] using hf
    have hfLim := (real_tagged_equivalence f hBA hf'.bounded _).mp ⟨hf', rfl⟩
    have hgLim := fineTaggedLimit_of_image_sums hab h hfb (image_sums_antitone h hm hfLim)
    obtain ⟨hg, hv⟩ := (real_tagged_equivalence _ hab hgb _).mpr hgLim
    have hfRev : OrientedRealIntegrable f (φ b) (φ a) := by
      simpa only [O.realIntegrableValue, min_eq_left hBA, max_eq_right hBA] using hf'
    refine ⟨hg, hv.trans ?_⟩
    exact (congrArg Neg.neg (oriented_real_agreement f hBA hfRev hf')).symm.trans
      (oriented_real_symmetry f (φ a) (φ b) hf hfRev).symm

/-- Monotone C¹ substitution for complex scalars, with real increments and
componentwise Darboux integration. -/
theorem complex_monotone_substitution :
    Specs.SingleVariableAnalysis.Ch09.MonotoneSubstitution.complexMonotoneSubstitution := by
  intro φ dφ f a b hab h hm hf
  have hfb : ∃ M : ℝ, ∀ t ∈ Icc a b, ‖f (φ t)‖ ≤ M := by
    obtain ⟨M, hM⟩ := ComplexIntegrable.norm_bound hf
    exact ⟨M, fun t ht => hM (φ t) (monotone_image_mem_hull hm ht)⟩
  have hgb : ∃ M : ℝ, ∀ t ∈ Icc a b, ‖(dφ t : ℂ) * f (φ t)‖ ≤ M := by
    simpa only [Complex.real_smul] using transformed_norm_bound h hfb
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  rcases hm with hm | hm
  · have hAB := hm ha hb hab
    have hf' : ComplexIntegrable f (φ a) (φ b) := by
      simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.complexIntegrableValue, min_eq_left hAB,
        max_eq_right hAB] using hf
    have hfLim := (complex_tagged_equivalence f hAB hf'.norm_bound _).mp ⟨hf', rfl⟩
    have hgLim := fineTaggedLimit_of_image_sums hab h hfb (image_sums_monotone h hm hfLim)
    have hgLim' : FineTaggedLimit (fun t => (dφ t : ℂ) * f (φ t)) a b
        (complexIntegral f hf') := by simpa only [Complex.real_smul] using hgLim
    obtain ⟨hg, hv⟩ := (complex_tagged_equivalence _ hab hgb _).mpr hgLim'
    exact ⟨hg, hv.trans (oriented_complex_agreement f hAB hf hf').symm⟩
  · have hBA := hm ha hb hab
    have hf' : ComplexIntegrable f (φ b) (φ a) := by
      simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.complexIntegrableValue, min_eq_right hBA,
        max_eq_left hBA] using hf
    have hfLim := (complex_tagged_equivalence f hBA hf'.norm_bound _).mp ⟨hf', rfl⟩
    have hgLim := fineTaggedLimit_of_image_sums hab h hfb (image_sums_antitone h hm hfLim)
    have hgLim' : FineTaggedLimit (fun t => (dφ t : ℂ) * f (φ t)) a b
        (-complexIntegral f hf') := by simpa only [Complex.real_smul] using hgLim
    obtain ⟨hg, hv⟩ := (complex_tagged_equivalence _ hab hgb _).mpr hgLim'
    have hfRev : OrientedComplexIntegrable f (φ b) (φ a) := by
      simpa only [O.complexIntegrableValue, min_eq_left hBA, max_eq_right hBA] using hf'
    refine ⟨hg, hv.trans ?_⟩
    exact (congrArg Neg.neg (oriented_complex_agreement f hBA hfRev hf')).symm.trans
      (oriented_complex_symmetry f (φ a) (φ b) hf hfRev).symm

end SingleVariableAnalysis.Riemann
