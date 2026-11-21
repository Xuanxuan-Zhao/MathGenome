import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.AccumulationParts
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Accumulation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.SummationParts

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators
open Set

/-- A continuous real function is Darboux integrable, by uniform continuity. -/
theorem realIntegrable_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) : RealIntegrable f a b := by
  have hb : BoundedOnInterval f a b :=
    ⟨(isCompact_Icc.image_of_continuousOn hf).bddBelow,
      (isCompact_Icc.image_of_continuousOn hf).bddAbove⟩
  apply (realIntegrable_iff_small_gap f hab hb).mpr
  intro ε hε
  let η := ε / (b - a + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  obtain ⟨P, hP⟩ := exists_fine_partition hab δ hδ
  have hcell (i : Fin P.n) : cellSupremum f P hb i - cellInfimum f P hb i ≤ η := by
    apply cell_oscillation_le_of_sub_le
    intro x hx y hy
    have hd : dist x y ≤ cellLength P i := by
      rw [Real.dist_eq, abs_le]
      dsimp [cell, D.cellValue] at hx hy
      dsimp [cellLength, S.lengthValue]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have ht := hc x (cell_subset_interval P i hx) y (cell_subset_interval P i hy)
      (hd.trans_lt ((cellLength_le_mesh P i).trans_lt hP))
    exact (le_abs_self _).trans (le_of_lt (by simpa [Real.dist_eq] using ht))
  refine ⟨P, ?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    mul_le_mul_of_nonneg_right (hcell i) (cell_positive P i).le
  rw [sum_cell_oscillation, ← Finset.mul_sum, sum_cellLength] at hs
  apply hs.trans_lt
  have he : η * (b - a + 1) = ε := by
    dsimp [η]; exact div_mul_cancel₀ _ (by linarith)
  nlinarith

/-- Equality on the interval transfers Darboux integrability and its value. -/
theorem realIntegral_congr_on {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hfg : ∀ x ∈ Icc a b, f x = g x) :
    ∃ hg : RealIntegrable g a b, realIntegral g hg = realIntegral f hf := by
  have hb : BoundedOnInterval g a b := by
    have he : g '' Icc a b = f '' Icc a b := Set.image_congr fun x hx => (hfg x hx).symm
    change BddBelow _ ∧ BddAbove _
    rw [he]
    exact hf.bounded
  apply (real_tagged_equivalence _ (RealIntegrable.ordered hf) hb _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ :=
    (real_tagged_equivalence _ (RealIntegrable.ordered hf) hf.bounded _).mp ⟨hf, rfl⟩ ε hε
  refine ⟨δ, hδ, fun P ξ hP => ?_⟩
  have he : taggedSum P ξ g = taggedSum P ξ f := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hfg (ξ i) (cell_subset_interval P i (ξ i).property)]
  change ‖taggedSum P ξ g - realIntegral f hf‖ < ε
  rw [he]
  exact hc P ξ hP

/-- Pointwise values of any accumulation representative are continuous on the interval. -/
theorem real_accumulation_continuous {f F : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b)
    (H : ∀ x : Icc a b, RealIntegrable f a x)
    (hF : ∀ x : Icc a b, F x = realIntegral f (H x)) :
    ContinuousOn F (Icc a b) := by
  obtain ⟨H₀, _, _, _, hc⟩ := real_accumulation f hf
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hc using 1
  funext x
  exact hF x

/-- Splitting identifies increments of an accumulation with the cell integral. -/
theorem real_accumulation_increment {f F : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b)
    (H : ∀ x : Icc a b, RealIntegrable f a x)
    (hF : ∀ x : Icc a b, F x = realIntegral f (H x))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u ≤ v)
    (h : RealIntegrable f u v) : F v - F u = realIntegral f h := by
  rw [hF ⟨v, hv⟩, hF ⟨u, hu⟩]
  have he := (real_split f hu.1 huv (H ⟨v, hv⟩).bounded).2 (H ⟨v, hv⟩) (H ⟨u, hu⟩) h
  linarith

/-- Integral norm bound with any pointwise majorant. -/
theorem abs_realIntegral_le {f : ℝ → ℝ} {a b M : ℝ}
    (hf : RealIntegrable f a b) (hb : ∀ x ∈ Icc a b, |f x| ≤ M) :
    |realIntegral f hf| ≤ (b - a) * M := by
  obtain ⟨hn, he, _⟩ := real_norm_estimate f hf
  exact (show |realIntegral f hf| ≤ realIntegral _ hn from he).trans
    (realIntegral_le_mul_bound hn (by simpa only [Real.norm_eq_abs] using hb))

/-- Point values of a partition stay inside its endpoints. -/
theorem partition_point_mem {a b : ℝ} (P : Partition a b) (i : Fin (P.n + 1)) :
    P.point i ∈ Icc a b :=
  (endpoints P).2.2 _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- Additivity on every finite partition, with arbitrary integrability witnesses. -/
theorem realIntegral_sum_cells {f : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (P : Partition a b)
    (h : ∀ i : Fin P.n, RealIntegrable f (P.point i.castSucc) (P.point i.succ)) :
    (∑ i : Fin P.n, realIntegral f (h i)) = realIntegral f hf := by
  let H (i : Fin (P.n + 1)) : RealIntegrable f a (P.point i) :=
    hf.subinterval le_rfl (partition_point_mem P i).1 (partition_point_mem P i).2
  have he (i : Fin P.n) : realIntegral f (h i) =
      realIntegral f (H i.succ) - realIntegral f (H i.castSucc) := by
    have hs := (real_split f (partition_point_mem P i.castSucc).1
      (P.strictMono.monotone (Fin.castSucc_le_succ i)) (H i.succ).bounded).2
      (H i.succ) (H i.castSucc) (h i)
    linarith
  simp_rw [he]
  change (∑ i : Fin P.n, ((fun j => realIntegral f (H j)) i.succ -
    (fun j => realIntegral f (H j)) i.castSucc)) = _
  rw [sum_cell_differences (fun j => realIntegral f (H j))]
  have hlast : realIntegral f (H (Fin.last P.n)) = realIntegral f hf := by
    generalize_proofs h₁
    revert h₁
    rw [P.last]
    intro h₁
    rfl
  have hz (v : ℝ) (hv : v = a) (hh : RealIntegrable f a v) : realIntegral f hh = 0 := by
    subst v
    exact realIntegral_degenerate f a hh
  have hfirst : realIntegral f (H 0) = 0 := hz _ P.first _
  rw [hlast, hfirst, sub_zero]

/-- Integral subtraction, for supplied witnesses. -/
theorem realIntegral_sub_eq {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b)
    (h : RealIntegrable (fun x => f x - g x) a b) :
    realIntegral _ h = realIntegral f hf - realIntegral g hg := by
  obtain ⟨hn, hen⟩ := real_mul_value hg (-1)
  obtain ⟨ha, hea⟩ := real_add_value hf hn
  simpa only [neg_one_mul, ← sub_eq_add_neg] using hea.trans (by rw [hen]; ring)

/-- A real derivative bound controls all secants, including interval endpoints. -/
theorem real_secant_bound {g g' : ℝ → ℝ} {a b N : ℝ}
    (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hN : ∀ x ∈ Icc a b, |g' x| ≤ N)
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    |g v - g u| ≤ N * |v - u| := by
  wlog huv : u ≤ v generalizing u v
  · simpa only [abs_sub_comm] using this hv hu (le_of_not_ge huv)
  rcases eq_or_lt_of_le huv with rfl | huv
  · simp
  obtain ⟨c, hc, he⟩ := SingleVariableAnalysis.lagrange_deriv g u v huv
    (hg.mono (Icc_subset_Icc hu.1 hv.2))
    (fun x hx => (hd x ⟨hu.1.trans_lt hx.1, hx.2.trans_le hv.2⟩).differentiableAt)
  rw [(hd c ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩).deriv] at he
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_right (hN c ⟨hu.1.trans hc.1.le, hc.2.le.trans hv.2⟩)
    (abs_nonneg _)

/-- A frozen endpoint multiplier changes a cell integral by a quadratic error. -/
theorem real_frozen_multiplier_error {f g : ℝ → ℝ} {u v M N : ℝ}
    (hf : RealIntegrable f u v) (hfg : RealIntegrable (fun x => f x * g x) u v)
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hb : ∀ x ∈ Icc u v, |f x| ≤ M)
    (hg : ∀ x ∈ Icc u v, |g x - g v| ≤ N * (v - u)) :
    |realIntegral _ hfg - g v * realIntegral f hf| ≤ M * N * (v - u)^2 := by
  obtain ⟨hconst, he⟩ := real_mul_value hf (g v)
  let herr := RealIntegrable.sub hfg hconst
  have hv := realIntegral_sub_eq hfg hconst herr
  rw [he] at hv
  rw [← hv]
  have hb' : ∀ x ∈ Icc u v, |f x * g x - g v * f x| ≤ M * (N * (v - u)) := by
    intro x hx
    rw [show f x * g x - g v * f x = f x * (g x - g v) by ring, abs_mul]
    exact mul_le_mul (hb x hx) (hg x hx) (abs_nonneg _) hM
  have hh := abs_realIntegral_le herr hb'
  nlinarith

/-- Integration by parts with an accumulation, for an integrable derivative.
The accumulation is never differentiated. -/
theorem real_accumulation_parts_of_derivative {f g g' F : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : ContinuousOn g (Icc a b))
    (hgp : RealIntegrable g' a b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (H : ∀ x : Icc a b, RealIntegrable f a x)
    (hF : ∀ x : Icc a b, F x = realIntegral f (H x)) :
    ∃ hfg : RealIntegrable (fun x => f x * g x) a b,
    ∃ hFg : RealIntegrable (fun x => F x * g' x) a b,
      realIntegral _ hfg = F b * g b - realIntegral _ hFg := by
  have hab := (RealIntegrable.ordered hf)
  have hFc := real_accumulation_continuous hf H hF
  let hfg : RealIntegrable (fun x => f x * g x) a b := real_product hf (realIntegrable_of_continuousOn hab hg)
  let hFg : RealIntegrable (fun x => F x * g' x) a b := real_product (realIntegrable_of_continuousOn hab hFc) hgp
  refine ⟨hfg, hFg, ?_⟩
  let M := sSup ((fun t => ‖f t‖) '' Icc a b)
  obtain ⟨hM, hbM⟩ := norm_supremum_bounds f hab hf.norm.bounded.2
  change 0 ≤ M at hM
  have hfM (x : ℝ) (hx : x ∈ Icc a b) : |f x| ≤ M := hbM x hx
  obtain ⟨N, hN⟩ := hgp.bounded.abs_bound
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN a ⟨le_rfl, hab⟩)
  have hFa : F a = 0 := (hF ⟨a, le_rfl, hab⟩).trans (realIntegral_degenerate f a _)
  have hFL (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
      |F y - F x| ≤ M * |y - x| := by
    obtain ⟨H₀, hb, _⟩ := real_accumulation f hf
    have ht := hb ⟨x, hx⟩ ⟨y, hy⟩
    rw [hF ⟨y, hy⟩, hF ⟨x, hx⟩]
    exact ht
  have hpartition (P : Partition a b) :
      ∃ ξ : Tagging P,
        |realIntegral _ hfg + taggedSum P ξ (fun x => F x * g' x) - F b * g b| ≤
          (2 * M * N * (b - a)) * mesh P := by
    have hcell (i : Fin P.n) :
        ∃ c ∈ Ioo (P.point i.castSucc) (P.point i.succ),
          g (P.point i.succ) - g (P.point i.castSucc) = g' c * cellLength P i := by
      obtain ⟨c, hc, he⟩ := SingleVariableAnalysis.lagrange_deriv g
        (P.point i.castSucc) (P.point i.succ)
        (P.strictMono (Fin.castSucc_lt_succ (i := i)))
        (hg.mono (Icc_subset_Icc (partition_point_mem P _).1 (partition_point_mem P _).2))
        (fun x hx => (hd x ⟨(partition_point_mem P _).1.trans_lt hx.1,
          hx.2.trans_le (partition_point_mem P _).2⟩).differentiableAt)
      refine ⟨c, hc, ?_⟩
      rw [(hd c ⟨(partition_point_mem P _).1.trans_lt hc.1,
        hc.2.trans_le (partition_point_mem P _).2⟩).deriv] at he
      exact he
    choose c hc he using hcell
    let ξ : Tagging P := fun i => ⟨c i, (hc i).1.le, (hc i).2.le⟩
    let hi (i : Fin P.n) : RealIntegrable f (P.point i.castSucc) (P.point i.succ) :=
      hf.subinterval (partition_point_mem P _).1
        (P.strictMono.monotone (Fin.castSucc_le_succ i)) (partition_point_mem P _).2
    let hgi (i : Fin P.n) : RealIntegrable (fun x => f x * g x)
        (P.point i.castSucc) (P.point i.succ) :=
      hfg.subinterval (partition_point_mem P _).1
        (P.strictMono.monotone (Fin.castSucc_le_succ i)) (partition_point_mem P _).2
    have hinc (i : Fin P.n) : F (P.point i.succ) - F (P.point i.castSucc) =
        realIntegral f (hi i) := real_accumulation_increment hf H hF
      (partition_point_mem P _) (partition_point_mem P _)
      (P.strictMono.monotone (Fin.castSucc_le_succ i)) (hi i)
    have herr (i : Fin P.n) :
        |realIntegral _ (hgi i) + cellLength P i * (F (ξ i) * g' (ξ i)) -
          (F (P.point i.succ) * g (P.point i.succ) -
            F (P.point i.castSucc) * g (P.point i.castSucc))| ≤
        2 * M * N * (cellLength P i)^2 := by
      have hdist : |(ξ i : ℝ) - P.point i.castSucc| ≤ cellLength P i := by
        rw [abs_of_nonneg (sub_nonneg.mpr (ξ i).property.1)]
        dsimp [cellLength, S.lengthValue]
        linarith [(ξ i).property.2]
      have hloc := real_frozen_multiplier_error (hi i) (hgi i) hM hN0
        (fun x hx => hfM x (cell_subset_interval P i hx)) (fun x hx => by
          have hx' := cell_subset_interval P i hx
          have hh := real_secant_bound hg hd hN (partition_point_mem P i.succ) hx'
          have hlen : |x - P.point i.succ| ≤ cellLength P i := by
            rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
            dsimp [cellLength, S.lengthValue]
            linarith [hx.1]
          exact hh.trans (mul_le_mul_of_nonneg_left hlen hN0))
      have hFdist := hFL (P.point i.castSucc) (ξ i)
        (partition_point_mem P _) (cell_subset_interval P i (ξ i).property)
      have hFbound := hFdist.trans (mul_le_mul_of_nonneg_left hdist hM)
      have hNbound := hN (ξ i) (cell_subset_interval P i (ξ i).property)
      have hprod : |(F (ξ i) - F (P.point i.castSucc)) * g' (ξ i) * cellLength P i| ≤
          M * N * (cellLength P i)^2 := by
        rw [abs_mul, abs_mul, abs_of_pos (cell_positive P i)]
        have ht := mul_le_mul hFbound hNbound (abs_nonneg _) (mul_nonneg hM (cell_positive P i).le)
        have ht' := mul_le_mul_of_nonneg_right ht (cell_positive P i).le
        nlinarith
      have hid : realIntegral _ (hgi i) + cellLength P i * (F (ξ i) * g' (ξ i)) -
          (F (P.point i.succ) * g (P.point i.succ) -
            F (P.point i.castSucc) * g (P.point i.castSucc)) =
          (realIntegral _ (hgi i) - g (P.point i.succ) * realIntegral f (hi i)) +
          (F (ξ i) - F (P.point i.castSucc)) * g' (ξ i) * cellLength P i := by
        rw [← hinc i]
        have he' : g (P.point i.succ) - g (P.point i.castSucc) =
            g' (ξ i) * cellLength P i := he i
        linear_combination -F (P.point i.castSucc) * he'
      change |_ - _ * _| ≤ M * N * (cellLength P i)^2 at hloc
      rw [hid]
      exact (abs_add_le _ _).trans (by nlinarith)
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => herr i
    have ht := Finset.abs_sum_le_sum_abs (s := Finset.univ)
      (f := fun i : Fin P.n => realIntegral _ (hgi i) + cellLength P i * (F (ξ i) * g' (ξ i)) -
        (F (P.point i.succ) * g (P.point i.succ) - F (P.point i.castSucc) * g (P.point i.castSucc)))
    have htel := sum_cell_differences (fun j => F (P.point j) * g (P.point j))
    have hidentity : (∑ i : Fin P.n, (realIntegral _ (hgi i) +
        cellLength P i * (F (ξ i) * g' (ξ i)) -
        (F (P.point i.succ) * g (P.point i.succ) -
          F (P.point i.castSucc) * g (P.point i.castSucc)))) =
        realIntegral _ hfg + taggedSum P ξ (fun x => F x * g' x) - F b * g b := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, realIntegral_sum_cells hfg P hgi,
        htel, P.last, P.first, hFa, zero_mul, sub_zero]
      rfl
    rw [hidentity] at ht
    refine ⟨ξ, (ht.trans hsum).trans ?_⟩
    calc
      _ ≤ ∑ i : Fin P.n, (2 * M * N * mesh P) * cellLength P i := by
        apply Finset.sum_le_sum
        intro i _
        have hs := mul_le_mul_of_nonneg_left (cellLength_le_mesh P i)
          (cell_positive P i).le
        nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * M * N by positivity)]
      _ = _ := by rw [← Finset.mul_sum, sum_cellLength]; ring
  by_contra hne
  let D := realIntegral _ hfg + realIntegral _ hFg - F b * g b
  have hD : 0 < |D| := abs_pos.mpr (by dsimp [D]; intro h; apply hne; linarith)
  let C := 2 * M * N * (b - a)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨δ, hδ, hclose⟩ :=
    (real_tagged_equivalence _ hab hFg.bounded _).mp ⟨hFg, rfl⟩ (|D| / 2) (half_pos hD)
  obtain ⟨P, hP⟩ := exists_fine_partition hab (min δ (|D| / (2 * (C + 1))))
    (lt_min hδ (by positivity))
  obtain ⟨ξ, herr⟩ := hpartition P
  have hc := hclose P ξ (hP.trans_le (min_le_left _ _))
  change |taggedSum P ξ (fun x => F x * g' x) - realIntegral _ hFg| < |D| / 2 at hc
  have hm := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp
    (hP.trans_le (min_le_right _ _))
  have htri : |D| ≤
      |realIntegral _ hfg + taggedSum P ξ (fun x => F x * g' x) - F b * g b| +
      |taggedSum P ξ (fun x => F x * g' x) - realIntegral _ hFg| := by
    convert norm_sub_le (realIntegral _ hfg + taggedSum P ξ (fun x => F x * g' x) - F b * g b)
      (taggedSum P ξ (fun x => F x * g' x) - realIntegral _ hFg) using 1 <;>
      simp only [Real.norm_eq_abs] <;> dsimp [D] <;> congr 1 <;> ring
  change _ ≤ C * mesh P at herr
  nlinarith [mesh_nonneg P]

/-- Real version of the proper accumulation parts formula. -/
theorem real_accumulation_parts :
    Specs.SingleVariableAnalysis.Ch10.AccumulationParts.realParts := by
  intro f g g' a b hf hg hgp hd
  obtain ⟨H, _⟩ := real_accumulation f hf
  obtain ⟨F, hF⟩ := SingleVariableAnalysis.exists_ambientExtension (Icc a b)
    (fun x => realIntegral f (H x))
  obtain ⟨hfg, hFg, he⟩ := real_accumulation_parts_of_derivative hf hg
    (realIntegrable_of_continuousOn (RealIntegrable.ordered hf) hgp) hd H hF
  exact ⟨H, F, hF, hfg, hFg, he⟩

/-- Integral addition, for supplied integrability witnesses. -/
theorem realIntegral_add_eq {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b)
    (h : RealIntegrable (fun x => f x + g x) a b) :
    realIntegral _ h = realIntegral f hf + realIntegral g hg :=
  (real_add_value hf hg).choose_spec

/-- The real component of an integral of a complex product. -/
theorem complexIntegral_mul_re_eq {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b)
    (h : ComplexIntegrable (fun x => f x * g x) a b) :
    (complexIntegral _ h).re =
      realIntegral (fun x => (f x).re * (g x).re) (real_product hf.1 hg.1) -
      realIntegral (fun x => (f x).im * (g x).im) (real_product hf.2 hg.2) := by
  rw [(complexIntegral_components _ h).1]
  exact realIntegral_sub_eq (real_product hf.1 hg.1) (real_product hf.2 hg.2) h.1

/-- The imaginary component of an integral of a complex product. -/
theorem complexIntegral_mul_im_eq {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b)
    (h : ComplexIntegrable (fun x => f x * g x) a b) :
    (complexIntegral _ h).im =
      realIntegral (fun x => (f x).re * (g x).im) (real_product hf.1 hg.2) +
      realIntegral (fun x => (f x).im * (g x).re) (real_product hf.2 hg.1) := by
  rw [(complexIntegral_components _ h).2]
  exact realIntegral_add_eq (real_product hf.1 hg.2) (real_product hf.2 hg.1) h.2

/-- The complex formula is the combination of four real formulas. In
particular there is no assertion of a common complex mean-value tag. -/
theorem complex_accumulation_parts :
    Specs.SingleVariableAnalysis.Ch10.AccumulationParts.complexParts := by
  intro f g g' a b hf hg hgp hd
  have hab := (RealIntegrable.ordered hf.1)
  obtain ⟨H, _, _, _, hcont⟩ := complex_accumulation f hf
  obtain ⟨F, hF⟩ := SingleVariableAnalysis.exists_ambientExtension (Icc a b)
    (fun x => complexIntegral f (H x))
  have hFc : ContinuousOn F (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hcont using 1
    funext x
    exact hF x
  have hFr (x : Icc a b) : (F x).re = realIntegral (fun t => (f t).re) (H x).1 := by
    rw [hF x]
    exact (complexIntegral_components f (H x)).1
  have hFi (x : Icc a b) : (F x).im = realIntegral (fun t => (f t).im) (H x).2 := by
    rw [hF x]
    exact (complexIntegral_components f (H x)).2
  have hgr := Complex.continuous_re.comp_continuousOn hg
  have hgi := Complex.continuous_im.comp_continuousOn hg
  have hgpr := realIntegrable_of_continuousOn hab (Complex.continuous_re.comp_continuousOn hgp)
  have hgpi := realIntegrable_of_continuousOn hab (Complex.continuous_im.comp_continuousOn hgp)
  have hdr (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun t => (g t).re) (g' x).re x :=
    ((SingleVariableAnalysis.complex_hasDerivAt_iff_components g (g' x) x).mp (hd x hx)).1
  have hdi (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun t => (g t).im) (g' x).im x :=
    ((SingleVariableAnalysis.complex_hasDerivAt_iff_components g (g' x) x).mp (hd x hx)).2
  obtain ⟨hrr, hRr, err⟩ := real_accumulation_parts_of_derivative (F := fun x => (F x).re) hf.1 hgr hgpr hdr
    (fun x => (H x).1) hFr
  obtain ⟨hii, hIi, eii⟩ := real_accumulation_parts_of_derivative (F := fun x => (F x).im) hf.2 hgi hgpi hdi
    (fun x => (H x).2) hFi
  obtain ⟨hri, hRi, eri⟩ := real_accumulation_parts_of_derivative (F := fun x => (F x).re) hf.1 hgi hgpi hdi
    (fun x => (H x).1) hFr
  obtain ⟨hir, hIr, eir⟩ := real_accumulation_parts_of_derivative (F := fun x => (F x).im) hf.2 hgr hgpr hdr
    (fun x => (H x).2) hFi
  simp only [Function.comp_def] at err eii eri eir
  have hgint : ComplexIntegrable g a b :=
    ⟨realIntegrable_of_continuousOn hab hgr, realIntegrable_of_continuousOn hab hgi⟩
  have hgpint : ComplexIntegrable g' a b := ⟨hgpr, hgpi⟩
  have hFint : ComplexIntegrable F a b :=
    ⟨realIntegrable_of_continuousOn hab (Complex.continuous_re.comp_continuousOn hFc),
      realIntegrable_of_continuousOn hab (Complex.continuous_im.comp_continuousOn hFc)⟩
  let hfg : ComplexIntegrable (fun x => f x * g x) a b := complex_product hf hgint
  let hFg : ComplexIntegrable (fun x => F x * g' x) a b := complex_product hFint hgpint
  refine ⟨H, F, hF, hfg, hFg, ?_⟩
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re]
    rw [complexIntegral_mul_re_eq hf hgint hfg, complexIntegral_mul_re_eq hFint hgpint hFg]
    linarith [err, eii]
  · simp only [Complex.sub_im, Complex.mul_im]
    rw [complexIntegral_mul_im_eq hf hgint hfg, complexIntegral_mul_im_eq hFint hgpint hFg]
    linarith [eri, eir]

end SingleVariableAnalysis.Riemann
