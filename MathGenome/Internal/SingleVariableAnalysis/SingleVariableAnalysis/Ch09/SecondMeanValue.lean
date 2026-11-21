import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.SecondMeanValue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Accumulation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Monotone
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Products
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.SummationParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.IntermediateValues
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.ExtremeValues

/-! A Darboux proof of the normalized second mean value theorem.
Finite weighted increments approximate the integral with a mesh times total
variation error. Summation by parts bounds those increments by the range of
the continuous accumulation function. Jumps and actual endpoint values are
retained throughout. -/
noncomputable section
namespace SingleVariableAnalysis.Riemann.SecondMeanValue
open scoped BigOperators

/-- Every partition endpoint belongs to its full interval. -/
theorem point_mem {a b : ℝ} (P : Partition a b) (j : Fin (P.n + 1)) :
    P.point j ∈ Set.Icc a b :=
  ⟨by simpa only [P.first] using P.strictMono.monotone (Fin.zero_le j),
   by simpa only [P.last] using P.strictMono.monotone (Fin.le_last j)⟩

/-- The initial primitive, extended by zero outside its original interval.
Only its restriction to the interval will be used. -/
def initialIntegral {f : ℝ → ℝ} {a b : ℝ} (hf : RealIntegrable f a b) (x : ℝ) : ℝ :=
  if hx : x ∈ Set.Icc a b then realIntegral f (hf.subinterval le_rfl hx.1 hx.2) else 0

theorem initialIntegral_eq {f : ℝ → ℝ} {a b x : ℝ}
    (hf : RealIntegrable f a b) (hx : x ∈ Set.Icc a b)
    (hi : RealIntegrable f a x) : initialIntegral hf x = realIntegral f hi := by
  simp only [initialIntegral, dite_eq_left hx]

theorem initialIntegral_left {f : ℝ → ℝ} {a b : ℝ} (hf : RealIntegrable f a b) :
    initialIntegral hf a = 0 := by
  rw [initialIntegral_eq hf ⟨le_rfl, hf.ordered⟩ (realIntegrable_degenerate f a)]
  exact realIntegral_degenerate f a _

theorem initialIntegral_right {f : ℝ → ℝ} {a b : ℝ} (hf : RealIntegrable f a b) :
    initialIntegral hf b = realIntegral f hf := initialIntegral_eq hf ⟨hf.ordered, le_rfl⟩ hf

theorem initialIntegral_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hf : RealIntegrable f a b) :
    ContinuousOn (initialIntegral hf) (Set.Icc a b) := by
  obtain ⟨H, _, _, _, hcont⟩ := real_accumulation f hf
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hcont using 1
  ext x
  exact initialIntegral_eq hf x.property (H x)

/-- Additivity identifies a cell integral with an increment of the primitive. -/
theorem initialIntegral_sub {f : ℝ → ℝ} {a b x y : ℝ}
    (hf : RealIntegrable f a b) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hxy : x ≤ y) (hi : RealIntegrable f x y) :
    initialIntegral hf y - initialIntegral hf x = realIntegral f hi := by
  let hl := hf.subinterval le_rfl hx.1 hx.2
  let hr := hf.subinterval le_rfl hy.1 hy.2
  rw [initialIntegral_eq hf hx hl, initialIntegral_eq hf hy hr]
  have he := (real_split f hx.1 hxy hr.bounded).2 hr hl hi
  linarith

/-- Integrals over all cells add to the integral over the full interval. -/
theorem integral_sum_cells {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (P : Partition a b)
    (H : ∀ i : Fin P.n, RealIntegrable f (P.point i.castSucc) (P.point i.succ)) :
    (∑ i : Fin P.n, realIntegral f (H i)) = realIntegral f hf := by
  calc
    _ = ∑ i : Fin P.n, (initialIntegral hf (P.point i.succ) -
        initialIntegral hf (P.point i.castSucc)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (initialIntegral_sub hf (point_mem P _) (point_mem P _)
        (P.strictMono.monotone (Fin.castSucc_le_succ i)) (H i)).symm
    _ = _ := by rw [sum_cell_differences (fun j => initialIntegral hf (P.point j)), P.last, P.first,
      initialIntegral_left, initialIntegral_right, sub_zero]

/-- Finite Abel bounds, with no strictness or continuity assumption on weights. -/
theorem antitone_increment_bounds {n : ℕ} (G F : Fin (n + 1) → ℝ) {m M : ℝ}
    (hG : Antitone G) (hG0 : 0 ≤ G (Fin.last n)) (hF0 : F 0 = 0)
    (hF : ∀ j, m ≤ F j ∧ F j ≤ M) :
    m * G 0 ≤ (∑ i : Fin n, G i.castSucc * (F i.succ - F i.castSucc)) ∧
    (∑ i : Fin n, G i.castSucc * (F i.succ - F i.castSucc)) ≤ M * G 0 := by
  have hd (i : Fin n) : 0 ≤ G i.castSucc - G i.succ :=
    sub_nonneg.mpr (hG (Fin.castSucc_le_succ i))
  have hsum : (∑ i : Fin n, (G i.castSucc - G i.succ)) = G 0 - G (Fin.last n) := by
    have ht := sum_cell_differences G
    simp only [Finset.sum_sub_distrib] at ht ⊢
    linarith
  have he : (∑ i : Fin n, G i.castSucc * (F i.succ - F i.castSucc)) =
      G (Fin.last n) * F (Fin.last n) +
        ∑ i : Fin n, (G i.castSucc - G i.succ) * F i.succ := by
    have ht := sum_cell_differences (fun j => G j * F j)
    rw [hF0, mul_zero, sub_zero] at ht
    rw [← ht, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  constructor
  · calc
      m * G 0 = G (Fin.last n) * m +
          ∑ i : Fin n, (G i.castSucc - G i.succ) * m := by rw [← Finset.sum_mul, hsum]; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hF _).1 hG0)
        (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hF _).1 (hd i))
  · calc
      _ ≤ G (Fin.last n) * M +
          ∑ i : Fin n, (G i.castSucc - G i.succ) * M :=
        add_le_add (mul_le_mul_of_nonneg_left (hF _).2 hG0)
          (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hF _).2 (hd i))
      _ = M * G 0 := by rw [← Finset.sum_mul, hsum]; ring

/-- The reversed Abel bound uses terminal rather than initial increments. -/
theorem monotone_increment_bounds {n : ℕ} (G F : Fin (n + 1) → ℝ) {m M : ℝ}
    (hG : Monotone G) (hG0 : 0 ≤ G 0) (hFn : F (Fin.last n) = 0)
    (hF : ∀ j, m ≤ F j ∧ F j ≤ M) :
    m * G (Fin.last n) ≤ (∑ i : Fin n, G i.succ * (F i.castSucc - F i.succ)) ∧
    (∑ i : Fin n, G i.succ * (F i.castSucc - F i.succ)) ≤ M * G (Fin.last n) := by
  have hd (i : Fin n) : 0 ≤ G i.succ - G i.castSucc :=
    sub_nonneg.mpr (hG (Fin.castSucc_le_succ i))
  have hsum := sum_cell_differences G
  have he : (∑ i : Fin n, G i.succ * (F i.castSucc - F i.succ)) =
      G 0 * F 0 + ∑ i : Fin n, (G i.succ - G i.castSucc) * F i.castSucc := by
    have ht := sum_cell_differences (fun j => G j * F j)
    rw [hFn, mul_zero, zero_sub] at ht
    have heach : (∑ i : Fin n, G i.succ * (F i.castSucc - F i.succ)) -
        (∑ i : Fin n, (G i.succ - G i.castSucc) * F i.castSucc) =
        -(∑ i : Fin n, (G i.succ * F i.succ - G i.castSucc * F i.castSucc)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    linarith
  rw [he]
  constructor
  · calc
      m * G (Fin.last n) = G 0 * m +
          ∑ i : Fin n, (G i.succ - G i.castSucc) * m := by rw [← Finset.sum_mul, hsum]; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hF _).1 hG0)
        (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hF _).1 (hd i))
  · calc
      _ ≤ G 0 * M + ∑ i : Fin n, (G i.succ - G i.castSucc) * M :=
        add_le_add (mul_le_mul_of_nonneg_left (hF _).2 hG0)
          (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hF _).2 (hd i))
      _ = M * G (Fin.last n) := by rw [← Finset.sum_mul, hsum]; ring


/-- Each closed cell is a subinterval, with no changes to endpoint values. -/
theorem integrable_cell {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (P : Partition a b) (i : Fin P.n) :
    RealIntegrable f (P.point i.castSucc) (P.point i.succ) :=
  hf.subinterval (point_mem P _).1
    (P.strictMono.monotone (Fin.castSucc_le_succ i)) (point_mem P _).2

/-- Cellwise comparison of the weighted integral with weighted primitive
increments. The error tends to zero with mesh times total weight variation. -/
theorem weighted_integral_error {f g : ℝ → ℝ} {a b A : ℝ}
    (hf : RealIntegrable f a b) (hgf : RealIntegrable (fun x => g x * f x) a b)
    (hA : 0 ≤ A) (hbound : ∀ x ∈ Set.Icc a b, |f x| ≤ A)
    (P : Partition a b) (q D : Fin P.n → ℝ)
    (hD : ∀ i, 0 ≤ D i)
    (hclose : ∀ i, ∀ x ∈ cell P i, |g x - q i| ≤ D i) :
    |realIntegral _ hgf - ∑ i : Fin P.n, q i *
      (initialIntegral hf (P.point i.succ) - initialIntegral hf (P.point i.castSucc))| ≤
      A * mesh P * ∑ i : Fin P.n, D i := by
  let Hf := integrable_cell hf P
  let Hgf := integrable_cell hgf P
  have herr (i : Fin P.n) :
      |realIntegral _ (Hgf i) - q i * realIntegral f (Hf i)| ≤
        A * D i * cellLength P i := by
    obtain ⟨hscale, hscaleval⟩ := real_mul_value (Hf i) (-q i)
    obtain ⟨hdiff, hdiffval⟩ := real_add_value (Hgf i) hscale
    have he : realIntegral _ hdiff = realIntegral _ (Hgf i) - q i * realIntegral f (Hf i) := by
      rw [hdiffval, hscaleval]
      ring
    rw [← he, ← Real.norm_eq_abs]
    obtain ⟨hn, hnval, _⟩ := real_norm_estimate _ hdiff
    apply hnval.trans
    have hb : ∀ x ∈ cell P i, ‖g x * f x + -q i * f x‖ ≤ A * D i := by
      intro x hx
      calc
        _ = |(g x - q i) * f x| := by rw [Real.norm_eq_abs]; congr 1; ring
        _ = |f x| * |g x - q i| := by rw [abs_mul, mul_comm]
        _ ≤ _ := mul_le_mul (hbound x (cell_subset_interval P i hx))
          (hclose i x hx) (abs_nonneg _) hA
    exact (realIntegral_le_mul_bound hn hb).trans_eq (by dsimp [cellLength, S.lengthValue]; ring)
  have he : realIntegral _ hgf - ∑ i : Fin P.n, q i *
      (initialIntegral hf (P.point i.succ) - initialIntegral hf (P.point i.castSucc)) =
      ∑ i : Fin P.n, (realIntegral _ (Hgf i) - q i * realIntegral f (Hf i)) := by
    rw [Finset.sum_sub_distrib, integral_sum_cells hgf P Hgf]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [initialIntegral_sub hf (point_mem P _) (point_mem P _)
      (P.strictMono.monotone (Fin.castSucc_le_succ i)) (Hf i)]
  rw [he]
  calc
    _ ≤ ∑ i : Fin P.n, |realIntegral _ (Hgf i) - q i * realIntegral f (Hf i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n, A * D i * cellLength P i := Finset.sum_le_sum fun i _ => herr i
    _ ≤ ∑ i : Fin P.n, A * D i * mesh P := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (cellLength_le_mesh P i) (mul_nonneg hA (hD i))
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]; ring

/-- Left endpoint weights for an antitone function. -/
theorem antitone_integral_error {f g : ℝ → ℝ} {a b A : ℝ}
    (hf : RealIntegrable f a b) (hgf : RealIntegrable (fun x => g x * f x) a b)
    (hg : AntitoneOn g (Set.Icc a b))
    (hA : 0 ≤ A) (hbound : ∀ x ∈ Set.Icc a b, |f x| ≤ A) (P : Partition a b) :
    |realIntegral _ hgf - ∑ i : Fin P.n, g (P.point i.castSucc) *
      (initialIntegral hf (P.point i.succ) - initialIntegral hf (P.point i.castSucc))| ≤
      A * mesh P * (g a - g b) := by
  have hd (i : Fin P.n) : 0 ≤ g (P.point i.castSucc) - g (P.point i.succ) :=
    sub_nonneg.mpr (hg (point_mem P _) (point_mem P _)
      (P.strictMono.monotone (Fin.castSucc_le_succ i)))
  have ht := weighted_integral_error hf hgf hA hbound P
    (fun i => g (P.point i.castSucc))
    (fun i => g (P.point i.castSucc) - g (P.point i.succ)) hd (by
      intro i x hx
      have hl := hg (point_mem P _) (cell_subset_interval P i hx) hx.1
      have hr := hg (cell_subset_interval P i hx) (point_mem P _) hx.2
      rw [abs_of_nonpos (sub_nonpos.mpr hl)]
      linarith)
  have he : (∑ i : Fin P.n, (g (P.point i.castSucc) - g (P.point i.succ))) = g a - g b := by
    have hdif := sum_cell_differences (fun j => g (P.point j))
    rw [P.first, P.last] at hdif
    simp only [Finset.sum_sub_distrib] at hdif ⊢
    linarith
  rwa [he] at ht

/-- Right endpoint weights for a monotone function. -/
theorem monotone_integral_error {f g : ℝ → ℝ} {a b A : ℝ}
    (hf : RealIntegrable f a b) (hgf : RealIntegrable (fun x => g x * f x) a b)
    (hg : MonotoneOn g (Set.Icc a b))
    (hA : 0 ≤ A) (hbound : ∀ x ∈ Set.Icc a b, |f x| ≤ A) (P : Partition a b) :
    |realIntegral _ hgf - ∑ i : Fin P.n, g (P.point i.succ) *
      (initialIntegral hf (P.point i.succ) - initialIntegral hf (P.point i.castSucc))| ≤
      A * mesh P * (g b - g a) := by
  have hd (i : Fin P.n) : 0 ≤ g (P.point i.succ) - g (P.point i.castSucc) :=
    sub_nonneg.mpr (hg (point_mem P _) (point_mem P _)
      (P.strictMono.monotone (Fin.castSucc_le_succ i)))
  have ht := weighted_integral_error hf hgf hA hbound P
    (fun i => g (P.point i.succ))
    (fun i => g (P.point i.succ) - g (P.point i.castSucc)) hd (by
      intro i x hx
      have hl := hg (point_mem P _) (cell_subset_interval P i hx) hx.1
      have hr := hg (cell_subset_interval P i hx) (point_mem P _) hx.2
      rw [abs_of_nonpos (sub_nonpos.mpr hr)]
      linarith)
  have he := sum_cell_differences (fun j => g (P.point j))
  rw [P.first, P.last] at he
  rwa [he] at ht


/-- Bounds valid for arbitrarily fine approximations pass to the integral. -/
theorem bounds_of_fine_approximations {a b I L U C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (h : ∀ P : Partition a b, ∃ s : ℝ, L ≤ s ∧ s ≤ U ∧ |I - s| ≤ C * mesh P) :
    L ≤ I ∧ I ≤ U := by
  have happ (ε : ℝ) (hε : 0 < ε) : ∃ s : ℝ, L ≤ s ∧ s ≤ U ∧ |I - s| < ε := by
    obtain ⟨P, hP⟩ := exists_fine_partition hab (ε / (C + 1)) (by positivity)
    obtain ⟨s, hl, hu, hs⟩ := h P
    refine ⟨s, hl, hu, hs.trans_lt ?_⟩
    have ht := (lt_div_iff₀ (show 0 < C + 1 by positivity)).mp hP
    nlinarith [mesh_nonneg P]
  constructor
  · by_contra hn
    have hp : 0 < L - I := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨s, hl, _, hs⟩ := happ (L - I) hp
    linarith [(abs_lt.mp hs).1]
  · by_contra hn
    have hp : 0 < I - U := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨s, _, hu, hs⟩ := happ (I - U) hp
    linarith [(abs_lt.mp hs).2]

/-- The antitone weighted integral lies between the extreme initial integrals,
multiplied by the actual initial weight. -/
theorem antitone_integral_bounds {f g : ℝ → ℝ} {a b m M : ℝ}
    (hf : RealIntegrable f a b) (hgf : RealIntegrable (fun x => g x * f x) a b)
    (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hg : AntitoneOn g (Set.Icc a b))
    (hF : ∀ x ∈ Set.Icc a b, m ≤ initialIntegral hf x ∧ initialIntegral hf x ≤ M) :
    m * g a ≤ realIntegral _ hgf ∧ realIntegral _ hgf ≤ M * g a := by
  obtain ⟨A, hbound⟩ := hf.bounded.abs_bound
  have hA : 0 ≤ A := (abs_nonneg _).trans (hbound a ⟨le_rfl, hf.ordered⟩)
  have hvar : 0 ≤ g a - g b := sub_nonneg.mpr
    (hg ⟨le_rfl, hf.ordered⟩ ⟨hf.ordered, le_rfl⟩ hf.ordered)
  apply bounds_of_fine_approximations hf.ordered (mul_nonneg hA hvar)
  intro P
  let s := ∑ i : Fin P.n, g (P.point i.castSucc) *
    (initialIntegral hf (P.point i.succ) - initialIntegral hf (P.point i.castSucc))
  have hs := antitone_increment_bounds (fun j => g (P.point j))
    (fun j => initialIntegral hf (P.point j))
    (fun _ _ hij => hg (point_mem P _) (point_mem P _) (P.strictMono.monotone hij))
    (hg0 _ (point_mem P _)) (by rw [P.first, initialIntegral_left])
    (fun j => hF _ (point_mem P j))
  rw [P.first] at hs
  refine ⟨s, hs.1, hs.2, ?_⟩
  exact (antitone_integral_error hf hgf hg hA hbound P).trans_eq (by ring)

/-- The monotone weighted integral is bounded by the terminal primitive range. -/
theorem monotone_integral_bounds {f g : ℝ → ℝ} {a b m M : ℝ}
    (hf : RealIntegrable f a b) (hgf : RealIntegrable (fun x => g x * f x) a b)
    (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hg : MonotoneOn g (Set.Icc a b))
    (hF : ∀ x ∈ Set.Icc a b,
      m ≤ realIntegral f hf - initialIntegral hf x ∧ realIntegral f hf - initialIntegral hf x ≤ M) :
    m * g b ≤ realIntegral _ hgf ∧ realIntegral _ hgf ≤ M * g b := by
  obtain ⟨A, hbound⟩ := hf.bounded.abs_bound
  have hA : 0 ≤ A := (abs_nonneg _).trans (hbound a ⟨le_rfl, hf.ordered⟩)
  have hvar : 0 ≤ g b - g a := sub_nonneg.mpr
    (hg ⟨le_rfl, hf.ordered⟩ ⟨hf.ordered, le_rfl⟩ hf.ordered)
  apply bounds_of_fine_approximations hf.ordered (mul_nonneg hA hvar)
  intro P
  let s := ∑ i : Fin P.n, g (P.point i.succ) *
    (initialIntegral hf (P.point i.succ) - initialIntegral hf (P.point i.castSucc))
  have hs := monotone_increment_bounds (fun j => g (P.point j))
    (fun j => realIntegral f hf - initialIntegral hf (P.point j))
    (fun _ _ hij => hg (point_mem P _) (point_mem P _) (P.strictMono.monotone hij))
    (hg0 _ (point_mem P _)) (by rw [P.last, initialIntegral_right, sub_self])
    (fun j => hF _ (point_mem P j))
  rw [P.last] at hs
  have he : (∑ i : Fin P.n, g (P.point i.succ) *
      ((realIntegral f hf - initialIntegral hf (P.point i.castSucc)) -
        (realIntegral f hf - initialIntegral hf (P.point i.succ)))) = s := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hs
  refine ⟨s, hs.1, hs.2, ?_⟩
  exact (monotone_integral_error hf hgf hg hA hbound P).trans_eq (by ring)

/-- A continuous primitive attains every normalized value between its extrema,
with a separate argument when the normalizing factor vanishes. -/
theorem exists_normalized_value {F : ℝ → ℝ} {a b I c : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Set.Icc a b)) (hc : 0 ≤ c)
    (hI : ∀ m M : ℝ, (∀ x ∈ Set.Icc a b, m ≤ F x ∧ F x ≤ M) →
      m * c ≤ I ∧ I ≤ M * c) :
    ∃ ξ ∈ Set.Icc a b, I = c * F ξ := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab) hF
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hF
  have hrange (x : ℝ) (hx : x ∈ Set.Icc a b) : F u ≤ F x ∧ F x ≤ F v :=
    ⟨hmin hx, hmax hx⟩
  have hb := hI (F u) (F v) hrange
  rcases hc.eq_or_lt with hc | hc
  · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
    rw [← hc, mul_zero] at hb
    rw [← hc, zero_mul]
    linarith [hb.1, hb.2]
  · have hratio : I / c ∈ Set.Icc (F u) (F v) :=
      ⟨(le_div_iff₀ hc).mpr hb.1, (div_le_iff₀ hc).mpr hb.2⟩
    obtain ⟨ξ, hξ, he⟩ := (isPreconnected_Icc.intermediate_value hu hv hF) hratio
    refine ⟨ξ, hξ, ?_⟩
    have he' := (div_eq_iff hc.ne').mp he.symm
    exact he'.trans (mul_comm _ _)


end SecondMeanValue

/-- Bonnet's normalized theorem for proper Riemann integrals. All weights
are allowed to jump, and the coefficient is the assigned value at `a`. -/
theorem second_mean_value_antitone :
    Specs.SingleVariableAnalysis.Ch09.SecondMeanValue.antitoneWeight := by
  intro f g a b hf hg0 hg
  change RealIntegrable f a b at hf
  have hgb : BoundedOnInterval g a b := by
    refine ⟨⟨g b, ?_⟩, ⟨g a, ?_⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hg hx ⟨hf.ordered, le_rfl⟩ hx.2
    · rintro _ ⟨x, hx, rfl⟩
      exact hg ⟨le_rfl, hf.ordered⟩ hx hx.1
  have hgi : RealIntegrable g a b := real_monotone_integrable g hf.ordered hgb (Or.inr hg)
  have hgf : RealIntegrable (fun x => g x * f x) a b := real_product hgi hf
  obtain ⟨ξ, hξ, he⟩ := SecondMeanValue.exists_normalized_value hf.ordered
    (SecondMeanValue.initialIntegral_continuousOn hf) (hg0 a ⟨le_rfl, hf.ordered⟩)
    (fun _ _ hr => SecondMeanValue.antitone_integral_bounds hf hgf hg0 hg hr)
  let hξi := hf.subinterval le_rfl hξ.1 hξ.2
  refine ⟨hgi, hgf, ξ, hξ, hξi, ?_⟩
  exact he.trans (congrArg (fun y => g a * y) (SecondMeanValue.initialIntegral_eq hf hξ hξi))

/-- Reflected Bonnet theorem used in the Dirichlet--Jordan proof: a
nonnegative nondecreasing weight uses its final value and a terminal integral. -/
theorem second_mean_value_monotone :
    Specs.SingleVariableAnalysis.Ch09.SecondMeanValue.monotoneWeight := by
  intro f g a b hf hg0 hg
  change RealIntegrable f a b at hf
  have hgb : BoundedOnInterval g a b := by
    refine ⟨⟨g a, ?_⟩, ⟨g b, ?_⟩⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hg ⟨le_rfl, hf.ordered⟩ hx hx.1
    · rintro _ ⟨x, hx, rfl⟩
      exact hg hx ⟨hf.ordered, le_rfl⟩ hx.2
  have hgi : RealIntegrable g a b := real_monotone_integrable g hf.ordered hgb (Or.inl hg)
  have hgf : RealIntegrable (fun x => g x * f x) a b := real_product hgi hf
  have hc : ContinuousOn (fun x => realIntegral f hf - SecondMeanValue.initialIntegral hf x)
      (Set.Icc a b) := continuousOn_const.sub (SecondMeanValue.initialIntegral_continuousOn hf)
  obtain ⟨ξ, hξ, he⟩ := SecondMeanValue.exists_normalized_value hf.ordered hc
    (hg0 b ⟨hf.ordered, le_rfl⟩)
    (fun _ _ hr => SecondMeanValue.monotone_integral_bounds hf hgf hg0 hg hr)
  let hξi := hf.subinterval hξ.1 hξ.2 le_rfl
  refine ⟨hgi, hgf, ξ, hξ, hξi, ?_⟩
  have htail : realIntegral f hf - SecondMeanValue.initialIntegral hf ξ = realIntegral f hξi := by
    rw [← SecondMeanValue.initialIntegral_right hf]
    exact SecondMeanValue.initialIntegral_sub hf hξ ⟨hf.ordered, le_rfl⟩ hξ.2 hξi
  exact he.trans (congrArg (fun y => g b * y) htail)

end SingleVariableAnalysis.Riemann
