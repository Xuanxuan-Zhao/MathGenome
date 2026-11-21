import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.MonotoneReparameterization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.RectifiableStieltjes

noncomputable section
open Set
open scoped BigOperators ENNReal

namespace D12Complex.Stieltjes

/-- Variation is unchanged even when a monotone parameter map has plateaus. -/
theorem variation_monotone {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (γ : ℝ → ℂ) (φ : ℝ → ℝ) (hm : MonotoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) :
    totalVariation (γ ∘ φ) c d = totalVariation γ a b := by
  rw [totalVariation_eq_eVariationOn _ hcd, totalVariation_eq_eVariationOn _ hab,
    eVariationOn.comp_eq_of_monotoneOn γ φ hm, hi]

theorem variation_antitone {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (γ : ℝ → ℂ) (φ : ℝ → ℝ) (hm : AntitoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) :
    totalVariation (γ ∘ φ) c d = totalVariation γ a b := by
  rw [totalVariation_eq_eVariationOn _ hcd, totalVariation_eq_eVariationOn _ hab,
    eVariationOn.comp_eq_of_antitoneOn γ φ hm, hi]

/-- Inserting an endpoint splits variation, also when one piece is a singleton. -/
theorem totalVariation_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (γ : ℝ → ℂ) :
    totalVariation γ a b + totalVariation γ b c = totalVariation γ a c := by
  rw [totalVariation_eq_eVariationOn _ hab, totalVariation_eq_eVariationOn _ hbc,
    totalVariation_eq_eVariationOn _ (hab.trans hbc)]
  simpa only [univ_inter] using
    (eVariationOn.Icc_add_Icc γ (s := univ) hab hbc (mem_univ b))

theorem totalVariation_mono {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b) (γ : ℝ → ℂ) :
    totalVariation γ c d ≤ totalVariation γ a b := by
  rw [totalVariation_eq_eVariationOn _ hab, totalVariation_eq_eVariationOn _ hcd]
  exact eVariationOn.mono γ (Icc_subset_Icc hac hdb)

/-- The finite telescoping identity uses the actual endpoint values. -/
theorem sum_increments {n : ℕ} (v : Fin (n + 1) → ℂ) :
    ∑ i : Fin n, (v i.succ - v i.castSucc) = v (Fin.last n) - v 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.castSucc_succ]
    rw [ih (fun i => v i.succ)]
    simp only [Fin.succ_last, Fin.succ_zero_eq_one, Fin.castSucc_zero]
    abel

theorem taggedSum_const {a b : ℝ} (P : Partition a b) (t : Tags P)
    (γ : ℝ → ℂ) (w : ℂ) :
    taggedSum P t (fun _ => w) γ = w * (γ b - γ a) := by
  simp only [taggedSum, ← Finset.mul_sum]
  rw [sum_increments (fun i => γ (P.point i)), P.first, P.last]

theorem integral_const {a b : ℝ} (hab : a ≤ b) (γ : ℝ → ℂ) (w : ℂ) :
    integral a b (fun _ => w) γ = w * (γ b - γ a) := by
  apply integral_eq_of_hasIntegral hab
  intro ε hε
  refine ⟨1, zero_lt_one, fun P _ t => ?_⟩
  simp only [taggedSum_const, sub_self, norm_zero]
  exact hε

/-- The error on a cell is bounded by oscillation times variation on that cell. -/
theorem integral_cell_error {a b : ℝ} (hab : a ≤ b) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤)
    (w : ℂ) {η : ℝ} (hη : 0 ≤ η) (ho : ∀ x ∈ Icc a b, ‖w - u x‖ ≤ η) :
    ‖w * (γ b - γ a) - integral a b u γ‖ ≤ η * (totalVariation γ a b).toReal := by
  have he : integral a b (fun x => w - u x) γ =
      w * (γ b - γ a) - integral a b u γ := by
    have h := continuous_integrand_linearity hab (fun _ => w) u γ 1 (-1)
      continuousOn_const hu hγ
    simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg, integral_const hab γ w] using h
  rw [← he]
  exact (hasIntegral_integral hab _ γ (continuousOn_const.sub hu) hγ).norm_le
    hab hγ hη ho

/-- Tagged-sum error on a weakly increasing node list. Zero-length cells need
no deletion; both their variation and their integral are zero. -/
theorem sum_error_of_oscillation {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (t : Fin n → ℝ) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc (x 0) (x (Fin.last n))))
    (hγ : totalVariation γ (x 0) (x (Fin.last n)) < ⊤)
    {η : ℝ} (hη : 0 ≤ η)
    (ho : ∀ i : Fin n, ∀ z ∈ Icc (x i.castSucc) (x i.succ), ‖u (t i) - u z‖ ≤ η) :
    ‖(∑ i : Fin n, u (t i) * (γ (x i.succ) - γ (x i.castSucc))) -
      integral (x 0) (x (Fin.last n)) u γ‖ ≤
      η * (totalVariation γ (x 0) (x (Fin.last n))).toReal := by
  induction n with
  | zero => simp [integral_degenerate, totalVariation_degenerate]
  | succ n ih =>
    have h01 : x 0 ≤ x (Fin.succ 0) := hx (Fin.zero_le _)
    have h1N : x (Fin.succ 0) ≤ x (Fin.last (n+1)) := hx (Fin.le_last _)
    have h0N := h01.trans h1N
    have hγ₀ := lt_of_le_of_lt (totalVariation_mono h0N h01 le_rfl h1N γ) hγ
    have hγ₁ := lt_of_le_of_lt (totalVariation_mono h0N h1N h01 le_rfl γ) hγ
    have he₀ := integral_cell_error h01 u γ
      (hu.mono (Icc_subset_Icc le_rfl h1N)) hγ₀ (u (t 0)) hη (ho 0)
    have he₁ := ih (fun i => x i.succ) (hx.comp Fin.strictMono_succ.monotone)
      (fun i => t i.succ)
      (hu.mono (Icc_subset_Icc h01 le_rfl)) hγ₁
      (fun i z hz => ho i.succ z (by simpa only [Fin.castSucc_succ] using hz))
    have hV : (totalVariation γ (x 0) (x (Fin.succ 0))).toReal +
        (totalVariation γ (x (Fin.succ 0)) (x (Fin.last (n+1)))).toReal =
        (totalVariation γ (x 0) (x (Fin.last (n+1)))).toReal := by
      rw [← ENNReal.toReal_add (ne_of_lt hγ₀) (ne_of_lt hγ₁), totalVariation_add h01 h1N]
    rw [Fin.sum_univ_succ, integral_add_subinterval h01 h1N u γ hu hγ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ]
    calc
      _ = ‖(u (t 0) * (γ (x (Fin.succ 0)) - γ (x 0)) -
          integral (x 0) (x (Fin.succ 0)) u γ) +
        ((∑ i : Fin n, u (t i.succ) * (γ (x i.succ.succ) - γ (x i.castSucc.succ))) -
          integral (x (Fin.succ 0)) (x (Fin.last (n+1))) u γ)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ η * (totalVariation γ (x 0) (x (Fin.succ 0))).toReal +
          η * (totalVariation γ (x (Fin.succ 0)) (x (Fin.last (n+1)))).toReal :=
        add_le_add he₀ he₁
      _ = _ := by rw [← mul_add, hV]

/-- Fine weak partitions approximate the integral, including repeated nodes. -/
theorem weakSum_approx {a b : ℝ} (_hab : a ≤ b) (u γ : ℝ → ℂ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (x : Fin (n+1) → ℝ), Monotone x →
      x 0 = a → x (Fin.last n) = b → ∀ t : Fin n → ℝ,
      (∀ i, t i ∈ Icc (x i.castSucc) (x i.succ)) →
      (∀ i : Fin n, x i.succ - x i.castSucc < δ) →
      ‖(∑ i : Fin n, u (t i) * (γ (x i.succ) - γ (x i.castSucc))) -
        integral a b u γ‖ < ε := by
  let V := (totalVariation γ a b).toReal
  let η := ε / (V + 1)
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hu) η hη
  refine ⟨δ, hδ, fun n x hx ha hb t ht hmesh => ?_⟩
  have hmem (i : Fin (n+1)) : x i ∈ Icc a b := by
    constructor
    · rw [← ha]; exact hx (Fin.zero_le _)
    · rw [← hb]; exact hx (Fin.le_last _)
  have ho (i : Fin n) (z : ℝ) (hz : z ∈ Icc (x i.castSucc) (x i.succ)) :
      ‖u (t i) - u z‖ ≤ η := by
    have hi : Icc (x i.castSucc) (x i.succ) ⊆ Icc a b :=
      Icc_subset_Icc (hmem _).1 (hmem _).2
    simpa only [dist_eq_norm] using (hδu _ (hi (ht i)) _ (hi hz)
      ((Real.dist_le_of_mem_Icc (ht i) hz).trans_lt (hmesh i))).le
  have he := sum_error_of_oscillation x hx t u γ
    (by simpa only [ha, hb] using hu) (by simpa only [ha, hb] using hγ) hη.le ho
  simp only [ha, hb] at he
  apply he.trans_lt
  change η * V < ε
  have heq : η * (V + 1) = ε := div_mul_cancel₀ _ (by positivity)
  nlinarith

/-- Reversing the finite node and tag lists reverses every increment. -/
theorem sum_reverse {n : ℕ} (x : Fin (n+1) → ℝ) (t : Fin n → ℝ)
    (u γ : ℝ → ℂ) :
    (∑ i : Fin n, u (t i.rev) *
        (γ (x i.succ.rev) - γ (x i.castSucc.rev))) =
      -(∑ i : Fin n, u (t i) * (γ (x i.succ) - γ (x i.castSucc))) := by
  simp only [Fin.rev_succ, Fin.rev_castSucc]
  calc
    _ = ∑ i : Fin n, u (t i) * (γ (x i.castSucc) - γ (x i.succ)) :=
      Equiv.sum_comp (Fin.revPerm : Fin n ≃ Fin n) _
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A surjective monotone interval map has the specified endpoint values. -/
theorem monotone_endpoints {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (φ : ℝ → ℝ) (hm : MonotoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) : φ c = a ∧ φ d = b := by
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hd : d ∈ Icc c d := ⟨hcd, le_rfl⟩
  have hmap : MapsTo φ (Icc c d) (Icc a b) := fun x hx => hi ▸ mem_image_of_mem φ hx
  obtain ⟨x, hx, hxa⟩ := show a ∈ φ '' Icc c d from hi.symm ▸ left_mem_Icc.mpr hab
  obtain ⟨y, hy, hyb⟩ := show b ∈ φ '' Icc c d from hi.symm ▸ right_mem_Icc.mpr hab
  exact ⟨le_antisymm (hxa ▸ hm hc hx hx.1) (hmap hc).1,
    le_antisymm (hmap hd).2 (hyb ▸ hm hy hd hy.2)⟩

/-- Transfer the actual mesh limit through any continuous nondecreasing map. -/
theorem hasIntegral_comp_monotone {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (u γ : ℝ → ℂ) (φ : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤)
    (hc : ContinuousOn φ (Icc c d)) (hm : MonotoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) :
    HasIntegral c d (u ∘ φ) (γ ∘ φ) (integral a b u γ) := by
  obtain ⟨ha, hb⟩ := monotone_endpoints hab hcd φ hm hi
  intro ε hε
  obtain ⟨δ, hδ, hδsum⟩ := weakSum_approx hab u γ hu hγ hε
  obtain ⟨σ, hσ, hσφ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) δ hδ
  refine ⟨σ, hσ, fun P hP t => ?_⟩
  have hmem (i : Fin (P.n+1)) : P.point i ∈ Icc c d :=
    (SingleVariableAnalysis.Riemann.endpoints P).2.2 _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  apply hδsum P.n (fun i => φ (P.point i))
    (fun i j hij => hm (hmem i) (hmem j) (P.strictMono.monotone hij))
    (by simpa only [P.first] using ha) (by simpa only [P.last] using hb)
    (fun i => φ (t i))
  · intro i
    have ht := SingleVariableAnalysis.Stieltjes.tag_mem_interval P t i
    exact ⟨hm (hmem _) ht (t i).property.1, hm ht (hmem _) (t i).property.2⟩
  · intro i
    have hdist : dist (P.point i.succ) (P.point i.castSucc) < σ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i)))]
      exact (SingleVariableAnalysis.Riemann.cellLength_le_mesh P i).trans_lt hP
    have h := hσφ _ (hmem i.succ) _ (hmem i.castSucc) hdist
    rw [Real.dist_eq, abs_of_nonneg
      (sub_nonneg.mpr (hm (hmem _) (hmem _) (P.strictMono.monotone (Fin.castSucc_le_succ i))))] at h
    exact h

theorem integral_monotone {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (u γ : ℝ → ℂ) (φ : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤)
    (hc : ContinuousOn φ (Icc c d)) (hm : MonotoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) :
    integral c d (u ∘ φ) (γ ∘ φ) = integral a b u γ :=
  integral_eq_of_hasIntegral hcd (hasIntegral_comp_monotone hab hcd u γ φ hu hγ hc hm hi)

theorem antitone_endpoints {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (φ : ℝ → ℝ) (hm : AntitoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) : φ c = b ∧ φ d = a := by
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  have hd : d ∈ Icc c d := ⟨hcd, le_rfl⟩
  have hmap : MapsTo φ (Icc c d) (Icc a b) := fun x hx => hi ▸ mem_image_of_mem φ hx
  obtain ⟨x, hx, hxa⟩ := show a ∈ φ '' Icc c d from hi.symm ▸ left_mem_Icc.mpr hab
  obtain ⟨y, hy, hyb⟩ := show b ∈ φ '' Icc c d from hi.symm ▸ right_mem_Icc.mpr hab
  exact ⟨le_antisymm (hmap hc).2 (hyb ▸ hm hc hy hy.1),
    le_antisymm (hxa ▸ hm hx hd hx.2) (hmap hd).1⟩

/-- Decreasing parameter maps reverse the sign of the mesh-limit integral. -/
theorem hasIntegral_comp_antitone {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (u γ : ℝ → ℂ) (φ : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤)
    (hc : ContinuousOn φ (Icc c d)) (hm : AntitoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) :
    HasIntegral c d (u ∘ φ) (γ ∘ φ) (-integral a b u γ) := by
  obtain ⟨hb, ha⟩ := antitone_endpoints hab hcd φ hm hi
  intro ε hε
  obtain ⟨δ, hδ, hδsum⟩ := weakSum_approx hab u γ hu hγ hε
  obtain ⟨σ, hσ, hσφ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) δ hδ
  refine ⟨σ, hσ, fun P hP t => ?_⟩
  have hmem (i : Fin (P.n+1)) : P.point i ∈ Icc c d :=
    (SingleVariableAnalysis.Riemann.endpoints P).2.2 _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hsum := hδsum P.n (fun i => φ (P.point i.rev))
    (fun i j hij => hm (hmem j.rev) (hmem i.rev)
      (P.strictMono.monotone (Fin.rev_le_rev.mpr hij)))
    (by simpa only [Fin.rev_zero, P.last] using ha)
    (by simpa only [Fin.rev_last, P.first] using hb)
    (fun i => φ (t i.rev))
  have htags : ∀ i : Fin P.n, φ (t i.rev) ∈
      Icc (φ (P.point i.castSucc.rev)) (φ (P.point i.succ.rev)) := by
    intro i
    simp only [Fin.rev_castSucc, Fin.rev_succ]
    have ht := SingleVariableAnalysis.Stieltjes.tag_mem_interval P t i.rev
    exact ⟨hm ht (hmem _) (t i.rev).property.2,
      hm (hmem _) ht (t i.rev).property.1⟩
  have hmesh : ∀ i : Fin P.n, φ (P.point i.succ.rev) - φ (P.point i.castSucc.rev) < δ := by
    intro i
    simp only [Fin.rev_castSucc, Fin.rev_succ]
    have hdist : dist (P.point i.rev.castSucc) (P.point i.rev.succ) < σ := by
      rw [dist_comm, Real.dist_eq, abs_of_nonneg
        (sub_nonneg.mpr (P.strictMono.monotone (Fin.castSucc_le_succ i.rev)))]
      exact (SingleVariableAnalysis.Riemann.cellLength_le_mesh P i.rev).trans_lt hP
    have h := hσφ _ (hmem i.rev.castSucc) _ (hmem i.rev.succ) hdist
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
      (hm (hmem _) (hmem _) (P.strictMono.monotone (Fin.castSucc_le_succ i.rev))))] at h
    exact h
  have he := hsum htags hmesh
  rw [sum_reverse (fun i => φ (P.point i)) (fun i => φ (t i)) u γ] at he
  change ‖taggedSum P t (u ∘ φ) (γ ∘ φ) - -integral a b u γ‖ < ε
  have hn : ‖taggedSum P t (u ∘ φ) (γ ∘ φ) - -integral a b u γ‖ =
      ‖-(∑ i : Fin P.n, u (φ (t i)) *
        (γ (φ (P.point i.succ)) - γ (φ (P.point i.castSucc)))) - integral a b u γ‖ := by
    rw [← norm_neg (taggedSum P t (u ∘ φ) (γ ∘ φ) - -integral a b u γ)]
    congr 1
    simp only [taggedSum, Function.comp_apply]
    abel
  exact hn.symm ▸ he

theorem integral_antitone {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (u γ : ℝ → ℂ) (φ : ℝ → ℝ)
    (hu : ContinuousOn u (Icc a b)) (hγ : totalVariation γ a b < ⊤)
    (hc : ContinuousOn φ (Icc c d)) (hm : AntitoneOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc a b) :
    integral c d (u ∘ φ) (γ ∘ φ) = -integral a b u γ :=
  integral_eq_of_hasIntegral hcd (hasIntegral_comp_antitone hab hcd u γ φ hu hγ hc hm hi)

/-- The composed path has the same variation and the same contour integral. -/
theorem contour_monotone (γ : ComplexPath) (hγ : Rectifiable γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) {c d : ℝ} (hcd : c ≤ d) (φ : ℝ → ℝ)
    (hm : MonotoneOn φ (Icc c d)) (hc : ContinuousOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc γ.a γ.b) :
    let η := γ.reparameterize hcd φ hc hi
    polygonalLength η = polygonalLength γ ∧ Rectifiable η ∧
      contourIntegral η f = contourIntegral γ f := by
  change totalVariation (γ ∘ φ) c d = polygonalLength γ ∧
    totalVariation (γ ∘ φ) c d < ⊤ ∧
    integral c d ((f ∘ γ) ∘ φ) (γ ∘ φ) = contourIntegral γ f
  have hlen := variation_monotone γ.ordered hcd γ φ hm hi
  exact ⟨hlen, hlen ▸ hγ,
    integral_monotone γ.ordered hcd (f ∘ γ) γ φ
      (hf.comp γ.continuousOn (fun x hx => ⟨x,hx,rfl⟩)) hγ hc hm hi⟩

/-- Orientation reversal keeps variation and negates the contour integral. -/
theorem contour_antitone (γ : ComplexPath) (hγ : Rectifiable γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) {c d : ℝ} (hcd : c ≤ d) (φ : ℝ → ℝ)
    (hm : AntitoneOn φ (Icc c d)) (hc : ContinuousOn φ (Icc c d))
    (hi : φ '' Icc c d = Icc γ.a γ.b) :
    let η := γ.reparameterize hcd φ hc hi
    polygonalLength η = polygonalLength γ ∧ Rectifiable η ∧
      contourIntegral η f = -contourIntegral γ f := by
  change totalVariation (γ ∘ φ) c d = polygonalLength γ ∧
    totalVariation (γ ∘ φ) c d < ⊤ ∧
    integral c d ((f ∘ γ) ∘ φ) (γ ∘ φ) = -contourIntegral γ f
  have hlen := variation_antitone γ.ordered hcd γ φ hm hi
  exact ⟨hlen, hlen ▸ hγ,
    integral_antitone γ.ordered hcd (f ∘ γ) γ φ
      (hf.comp γ.continuousOn (fun x hx => ⟨x,hx,rfl⟩)) hγ hc hm hi⟩

end D12Complex.Stieltjes

namespace D12Complex.MonotoneReparameterization

abbrev reparameterize : Specs.D12Complex.Ch03.MonotoneReparameterization.reparameterize_type :=
  @_root_.D12Complex.ComplexPath.reparameterize

end D12Complex.MonotoneReparameterization
