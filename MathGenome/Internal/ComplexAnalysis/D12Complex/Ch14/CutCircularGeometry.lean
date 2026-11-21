import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CutCircularGeometry
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.FiniteCircularArcs
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.DiskUnionBoundarySectors
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CircularCornerRounding
import Mathlib.Topology.Perfect
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators

/-! Actual fixed-cut geometry with explicit finite angular partitions. -/

noncomputable section
open Set Metric
open scoped Topology
namespace D12Complex.CircularCutGeometry

/-- The canonical cut is the literal finite closed-disk deletion. -/
theorem circularCut_eq_setDiff :
    Specs.D12Complex.Ch14.CutCircularGeometry.circularCut_eq_setDiff_type := rfl

lemma finite_positive_lower_bound {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, δ ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hδf⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    refine ⟨min (f a) δ, lt_min (hf a (Finset.mem_insert_self _ _)) hδ, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hδf b hb)

lemma uniform_finite_separation (s t : Finset ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, ∀ y ∈ t, x ≠ y → δ ≤ dist x y := by
  classical
  let u := (s ×ˢ t).filter (fun p => p.1 ≠ p.2)
  obtain ⟨δ, hδ, h⟩ := finite_positive_lower_bound u (fun p => dist p.1 p.2)
    (by intro p hp; exact dist_pos.mpr (Finset.mem_filter.mp hp).2)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  exact h (x,y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩)

lemma uniform_closedBall_in_open {D : Set ℂ} (hD : IsOpen D) (poles : Finset ℂ)
    (hpoles : (↑poles : Set ℂ) ⊆ D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ → ℝ, (∀ c ∈ poles, q c < δ) →
      ∀ c ∈ poles, closedBall c (q c) ⊆ D := by
  classical
  have hc : ∀ c ∈ poles, ∃ ε : ℝ, 0 < ε ∧ ball c ε ⊆ D := by
    intro c hc
    exact Metric.isOpen_iff.mp hD c (hpoles hc)
  choose ε hε hεD using hc
  obtain ⟨δ,hδ,hδε⟩ := finite_positive_lower_bound poles
    (fun c => if h : c ∈ poles then ε c h else 1)
    (by intro c hc; simpa only [dite_eq_left hc] using hε c hc)
  refine ⟨δ,hδ,?_⟩
  intro q hq c hc z hz
  apply hεD c hc
  change dist z c < ε c hc
  have hδc : δ ≤ ε c hc := by simpa only [dite_eq_left hc] using hδε c hc
  exact (mem_closedBall.mp hz).trans_lt ((hq c hc).trans_le hδc)

lemma uniform_disjoint_closedBalls (centers : Finset ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ → ℝ, (∀ c ∈ centers, q c < δ) →
      ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
        Disjoint (closedBall c (q c)) (closedBall d (q d)) := by
  obtain ⟨δ,hδ,hsep⟩ := uniform_finite_separation centers centers
  refine ⟨δ/3, by positivity, ?_⟩
  intro q hq c hc d hd hcd
  apply Metric.closedBall_disjoint_closedBall
  have hh := hsep c hc d hd hcd
  have hqc := hq c hc
  have hqd := hq d hd
  linarith

lemma uniform_spheres_avoid_finite_set (centers bad : Finset ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ → ℝ,
      (∀ c ∈ centers, 0 < q c ∧ q c < δ) →
      ∀ c ∈ centers, ∀ z ∈ bad, z ∉ sphere c (q c) := by
  obtain ⟨δ,hδ,hsep⟩ := uniform_finite_separation centers bad
  refine ⟨δ,hδ,?_⟩
  intro q hq c hc z hz hzc
  change dist z c = q c at hzc
  by_cases hcz : c = z
  · subst z
    simp only [dist_self] at hzc
    exact (ne_of_gt (hq c hc).1) hzc.symm
  · have hh := hsep c hc z hz hcz
    rw [dist_comm,hzc] at hh
    exact (not_lt_of_ge hh) (hq c hc).2

lemma uniform_circle_nontangency (centers s : Finset ℂ) (r : ℂ → ℝ)
    (hr : ∀ c ∈ s, 0 < r c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ → ℝ,
      (∀ x ∈ centers, 0 < q x ∧ q x < δ) →
      ∀ x ∈ centers, ∀ c ∈ s,
        dist x c ≠ q x + r c ∧ dist x c ≠ |q x - r c| := by
  classical
  let margin : ℂ × ℂ → ℝ := fun p =>
    if dist p.1 p.2 = r p.2 then r p.2 else |dist p.1 p.2 - r p.2|
  obtain ⟨δ,hδ,hm⟩ := finite_positive_lower_bound (centers ×ˢ s) margin (by
    rintro ⟨x,c⟩ hp
    have hc := (Finset.mem_product.mp hp).2
    dsimp [margin]
    split_ifs with h
    · exact hr c hc
    · exact abs_pos.mpr (sub_ne_zero.mpr h))
  refine ⟨δ,hδ,?_⟩
  intro q hq x hx c hc
  have hqm : q x < margin (x,c) := (hq x hx).2.trans_le
    (hm (x,c) (Finset.mem_product.mpr ⟨hx,hc⟩))
  have hqpos := (hq x hx).1
  have hrpos := hr c hc
  by_cases hinc : dist x c = r c
  · simp only [margin,hinc,ite_true] at hqm
    constructor
    · linarith
    · rw [abs_of_neg (by linarith : q x - r c < 0)]
      linarith
  · simp only [margin,hinc,ite_false] at hqm
    constructor
    · intro heq
      rw [heq,add_sub_cancel_right,abs_of_pos hqpos] at hqm
      exact (lt_irrefl _ hqm)
    · intro heq
      rcases le_total (r c) (q x) with hle | hle
      · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at heq
        rw [heq] at hqm
        have habs : |q x - r c - r c| ≤ q x := abs_le.mpr ⟨by linarith, by linarith⟩
        exact (not_lt_of_ge habs) hqm
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at heq
        rw [heq] at hqm
        have : -(q x - r c) - r c = -q x := by ring
        rw [this,abs_neg,abs_of_pos hqpos] at hqm
        exact (lt_irrefl _ hqm)

lemma uniform_only_incident_circle_intersections (centers s : Finset ℂ) (r : ℂ → ℝ)
    (hr : ∀ c ∈ s, 0 < r c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ → ℝ,
      (∀ x ∈ centers, q x < δ) →
      ∀ x ∈ centers, ∀ c ∈ s, ∀ z : ℂ,
        z ∈ sphere x (q x) → z ∈ sphere c (r c) → dist x c = r c := by
  classical
  let margin : ℂ × ℂ → ℝ := fun p =>
    if dist p.1 p.2 = r p.2 then r p.2 else |dist p.1 p.2 - r p.2|
  obtain ⟨δ,hδ,hm⟩ := finite_positive_lower_bound (centers ×ˢ s) margin (by
    rintro ⟨x,c⟩ hp
    have hc := (Finset.mem_product.mp hp).2
    dsimp [margin]
    split_ifs with h
    · exact hr c hc
    · exact abs_pos.mpr (sub_ne_zero.mpr h))
  refine ⟨δ,hδ,?_⟩
  intro q hq x hx c hc z hzx hzc
  by_contra hinc
  have hqm : q x < |dist x c - r c| := by
    have hh := (hq x hx).trans_le (hm (x,c) (Finset.mem_product.mpr ⟨hx,hc⟩))
    simpa only [margin,hinc,ite_false] using hh
  have hdist := abs_dist_sub_le x z c
  rw [mem_sphere] at hzx hzc
  rw [hzc,dist_comm x z,hzx] at hdist
  exact (not_lt_of_ge hdist) hqm

/-- The deletion radius threshold works for every small positive radius function,
without removing a further exceptional set of radii. -/
lemma uniform_deletion_geometry (s : Finset ℂ) (r : ℂ → ℝ)
    (hr : ∀ c ∈ s, 0 < r c) (poles centers : Finset ℂ)
    (hp : (↑poles : Set ℂ) ⊆ CircularExhaustion.diskUnion s r)
    (hpc : poles ⊆ centers) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ → ℝ,
      (∀ x ∈ centers, 0 < q x ∧ q x < δ) →
      (∀ c ∈ poles, closedBall c (q c) ⊆ CircularExhaustion.diskUnion s r) ∧
      (∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
        Disjoint (closedBall c (q c)) (closedBall d (q d))) ∧
      (∀ x ∈ centers, ∀ c ∈ s,
        dist x c ≠ q x + r c ∧ dist x c ≠ |q x - r c|) ∧
      (∀ x ∈ centers, ∀ z : ℂ,
        (∃ c ∈ s, ∃ d ∈ s, c ≠ d ∧ dist z c = r c ∧ dist z d = r d) →
        z ∉ sphere x (q x)) ∧
      (∀ x ∈ centers, ∀ c ∈ s, ∀ z : ℂ,
        z ∈ sphere x (q x) → z ∈ sphere c (r c) → dist x c = r c) ∧
      (∀ x ∈ centers, ∀ c ∈ s, ∀ z : ℂ,
        z ∈ sphere x (q x) → z ∈ sphere c (r c) →
        ((z - x) * star (z - c)).im ≠ 0) := by
  classical
  have hD : IsOpen (CircularExhaustion.diskUnion s r) :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  obtain ⟨δp,hδp,hpδ⟩ := uniform_closedBall_in_open hD poles hp
  obtain ⟨δs,hδs,hsδ⟩ := uniform_disjoint_closedBalls centers
  obtain ⟨δt,hδt,htδ⟩ := uniform_circle_nontangency centers s r hr
  let bad : Finset ℂ := (FiniteCircularArcs.finite_double_points s r).toFinset
  obtain ⟨δb,hδb,hbδ⟩ := uniform_spheres_avoid_finite_set centers bad
  obtain ⟨δi,hδi,hiδ⟩ := uniform_only_incident_circle_intersections centers s r hr
  let δ := min δp (min δs (min δt (min δb δi)))
  have hδ : 0 < δ := lt_min hδp (lt_min hδs (lt_min hδt (lt_min hδb hδi)))
  have hδp' : δ ≤ δp := min_le_left _ _
  have hδs' : δ ≤ δs := (min_le_right _ _).trans (min_le_left _ _)
  have hδt' : δ ≤ δt := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδb' : δ ≤ δb := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδi' : δ ≤ δi := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,hδ,?_⟩
  intro q hq
  have hqp : ∀ x ∈ poles, q x < δp := fun x hx => ((hq x (hpc hx)).2.trans_le hδp')
  have hqs : ∀ x ∈ centers, q x < δs := fun x hx => (hq x hx).2.trans_le hδs'
  have hqt : ∀ x ∈ centers, 0 < q x ∧ q x < δt := fun x hx =>
    ⟨(hq x hx).1,(hq x hx).2.trans_le hδt'⟩
  have hqb : ∀ x ∈ centers, 0 < q x ∧ q x < δb := fun x hx =>
    ⟨(hq x hx).1,(hq x hx).2.trans_le hδb'⟩
  have hqi : ∀ x ∈ centers, q x < δi := fun x hx => (hq x hx).2.trans_le hδi'
  have ht := htδ q hqt
  refine ⟨hpδ q hqp,hsδ q hqs,ht,?_,hiδ q hqi,?_⟩
  · intro x hx z hz
    exact hbδ q hqb x hx z (by simpa only [bad,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hz)
  · intro x hx c hc z hzx hzc
    apply FiniteCircularArcs.radial_cross_ne_zero ((hq x hx).1) (hr c hc)
      (by simpa only [mem_sphere,dist_eq_norm] using hzx)
      (by simpa only [mem_sphere,dist_eq_norm] using hzc)
    · simpa only [sub_sub_sub_cancel_left, ← dist_eq_norm,dist_comm] using (ht x hx c hc).1
    · simpa only [sub_sub_sub_cancel_left, ← dist_eq_norm,dist_comm] using (ht x hx c hc).2

end D12Complex.CircularCutGeometry


noncomputable section
open Set Metric
open scoped Topology ComplexConjugate
namespace D12Complex.CircularCutGeometry
open CircularExhaustion

lemma sectorChart_of_diskGeometry {D : Set ℂ} {p : ℂ} {θ : ℝ}
    (h : DiskUnionBoundarySectors.SectorChart D p θ) : SectorChart D p θ := by
  rcases h with ⟨U,V,f,g,hp,hpair,hzero,hd,hside⟩
  refine ⟨U,V,f,g,hp,hpair,hzero,hd,?_⟩
  intro z hz
  rw [hside z hz]
  constructor
  · rintro ⟨ρ,hρ,t,ht,htθ,he⟩
    exact ⟨ρ,t,hρ,ht,htθ,he⟩
  · rintro ⟨ρ,t,hρ,ht,htθ,he⟩
    exact ⟨ρ,hρ,t,ht,htθ,he⟩

lemma sectorChart_local {D E W : Set ℂ} {p : ℂ} {θ : ℝ}
    (h : SectorChart E p θ) (hW : IsOpen W) (hp : p ∈ W)
    (hlocal : ∀ z ∈ W, z ∈ D ↔ z ∈ E) : SectorChart D p θ := by
  obtain ⟨U,V,f,g,hpU,hpair,hzero,hd,hside⟩ := h
  have hnew := DiskUnionBoundarySectors.restrict_biholomorphicPair hpair
    (hpair.1.1.inter hW) (show U ∩ W ⊆ U from inter_subset_left)
  refine ⟨U ∩ W, V ∩ g ⁻¹' (U ∩ W), f,g,⟨hpU,hp⟩,hnew,hzero,hd,?_⟩
  intro z hz
  exact (hlocal z hz.2).trans (hside z hz.1)

lemma exterior_disk_sector_chart (c p : ℂ) (R : ℝ) (hR : 0 < R)
    (hp : dist p c = R) : SectorChart (closedBall c R)ᶜ p Real.pi := by
  let η := 2 * c - p
  have hpη : p ≠ η := by
    intro h
    have hpc : p = c := by dsimp [η] at h; linear_combination h / 2
    have : R = 0 := by simpa [hpc] using hp.symm
    linarith
  let f := fun z => Complex.I * (z - p) / (z - η)
  let g := fun w => (w * η - Complex.I * p) / (w - Complex.I)
  have hpair := DiskUnionBoundarySectors.rational_chart p η Complex.I hpη (by simp)
  refine ⟨{z | z ≠ η}, {w | w ≠ Complex.I}, f,g,hpη,hpair,by simp [f],?_,?_⟩
  · have hd := DiskUnionBoundarySectors.rational_chart_derivative p η Complex.I p hpη
    rw [hd.deriv]
    exact div_ne_zero (mul_ne_zero (by simp) (sub_ne_zero.mpr hpη))
      (pow_ne_zero _ (sub_ne_zero.mpr hpη))
  · intro z hz
    change z ∉ closedBall c R ↔ f z ∈ sector Real.pi
    have him : (f z).im = (‖z-c‖^2 - R^2) / ‖z - (2*c-p)‖^2 := by
      have hi := DiskUnionBoundarySectors.disk_rational_im c p z R hp hz
      have hn : f z = -(-Complex.I * (z-p) / (z-(2*c-p))) := by dsimp [f,η]; ring
      rw [hn, Complex.neg_im, hi]
      ring
    have hpolar : f z ∈ sector Real.pi ↔ 0 < (f z).im := by
      rw [DiskUnionBoundarySectors.upper_half_plane_iff_polar]
      constructor
      · rintro ⟨ρ,t,hρ,ht,htπ,he⟩; exact ⟨ρ,hρ,t,ht,htπ,he⟩
      · rintro ⟨ρ,hρ,t,ht,htπ,he⟩; exact ⟨ρ,t,hρ,ht,htπ,he⟩
    rw [hpolar,him]
    have hden : 0 < ‖z - (2*c-p)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
    rw [div_pos_iff_of_pos_right hden, mem_closedBall_iff_norm]
    constructor
    · intro h; have hlt := lt_of_not_ge h; nlinarith [norm_nonneg (z-c)]
    · intro h; exact not_le.mpr (by nlinarith [norm_nonneg (z-c)])

lemma ball_negative_side (c z : ℂ) {R : ℝ} (hR : 0 < R) :
    z ∈ ball c R ↔ (1 : ℝ) * (‖z-c‖^2-R^2) < 0 := by
  rw [mem_ball_iff_norm, one_mul]
  constructor <;> intro h <;> nlinarith [norm_nonneg (z-c)]

lemma exterior_negative_side (c z : ℂ) {R : ℝ} (hR : 0 < R) :
    z ∈ (closedBall c R)ᶜ ↔ (-1 : ℝ) * (‖z-c‖^2-R^2) < 0 := by
  rw [mem_compl_iff, mem_closedBall_iff_norm]
  constructor
  · intro h; have hlt := lt_of_not_ge h; nlinarith [norm_nonneg (z-c)]
  · intro h; exact not_le.mpr (by nlinarith [norm_nonneg (z-c)])

open private polar_im polar_coefficient from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.DiskUnionBoundarySectors

lemma intersection_halfplanes_sector {p : ℂ} (hp : p.im < 0) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ ∀ w : ℂ,
      (0 < w.im ∧ (p*w).im < 0) ↔ w ∈ sector θ := by
  let φ := -p.arg
  have hφ : 0 < φ := neg_pos.mpr (Complex.arg_neg_iff.mpr hp)
  have hφπ : φ < Real.pi := by dsimp [φ]; linarith [Complex.neg_pi_lt_arg p]
  have hpn : p ≠ 0 := by intro h; simp [h] at hp
  have hnp : 0 < ‖p‖ := norm_pos_iff.mpr hpn
  refine ⟨φ,hφ,hφπ,?_⟩
  intro w
  constructor
  · rintro ⟨hw,hpw⟩
    obtain ⟨ρ,hρ,t,ht,htπ,he⟩ := (DiskUnionBoundarySectors.upper_half_plane_iff_polar w).mp hw
    refine ⟨ρ,t,hρ,ht,?_,he⟩
    rw [he, polar_coefficient p ρ t φ rfl, polar_im] at hpw
    have hs : Real.sin (t-φ) < 0 := by nlinarith [mul_pos hnp hρ]
    by_contra h
    have hle : 0 ≤ t-φ := by linarith
    have hlt : t-φ < Real.pi := by linarith
    have : 0 ≤ Real.sin (t-φ) := Real.sin_nonneg_of_nonneg_of_le_pi hle hlt.le
    linarith
  · rintro ⟨ρ,t,hρ,ht,htφ,rfl⟩
    constructor
    · rw [polar_im]; exact mul_pos hρ (Real.sin_pos_of_pos_of_lt_pi ht (htφ.trans hφπ))
    · rw [polar_coefficient p ρ t φ rfl, polar_im]
      apply mul_neg_of_pos_of_neg (mul_pos hnp hρ)
      have hs := Real.sin_pos_of_pos_of_lt_pi (show 0 < φ-t by linarith)
        (show φ-t < Real.pi by linarith)
      rw [show t-φ = -(φ-t) by ring, Real.sin_neg]
      linarith

lemma straightening_exterior_side (ξ c K z : ℂ) (R : ℝ) (hR : 0 < R)
    (hξ : dist ξ c = R) (hK : 2 * ((ξ-c)*K).re = 1)
    (hz : 1 + K*(z-ξ) ≠ 0) :
    z ∈ (closedBall c R)ᶜ ↔
      (-Complex.I * conj (ξ-c) * ((z-ξ)/(1+K*(z-ξ)))).im < 0 := by
  have he : ‖z-c‖^2-R^2 = ‖z-ξ‖^2+2*(conj (ξ-c)*(z-ξ)).re := by
    have hnorm : ‖ξ-c‖^2 = R^2 := by rw [← dist_eq_norm,hξ]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.conj_re, Complex.conj_im] at hnorm ⊢
    nlinarith
  have hden : 0 < ‖1+K*(z-ξ)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hid := DiskUnionBoundarySectors.straightening_real_identity (ξ-c) K (z-ξ) hK
  rw [←he] at hid
  have him : (-Complex.I * conj (ξ-c) * ((z-ξ)/(1+K*(z-ξ)))).im =
      -(conj (ξ-c)*((z-ξ)/(1+K*(z-ξ)))).re := by rw [mul_assoc]; simp
  rw [him, mem_compl_iff, mem_closedBall_iff_norm]
  constructor
  · intro h
    have hlt : R < ‖z-c‖ := lt_of_not_ge h
    have : 0 < (‖z-c‖^2-R^2) / ‖1+K*(z-ξ)‖^2 :=
      div_pos (by nlinarith [norm_nonneg (z-c)]) hden
    linarith
  · intro h
    have : 0 < (‖z-c‖^2-R^2) / ‖1+K*(z-ξ)‖^2 := by linarith
    have ht := (div_pos_iff_of_pos_right hden).mp this
    exact not_le.mpr (by nlinarith [norm_nonneg (z-c)])

lemma straightening_intersection_chart {A : Set ℂ} {ξ K C p : ℂ}
    (hC : C ≠ 0) (hp : p.im < 0)
    (hside : ∀ z : ℂ, 1+K*(z-ξ) ≠ 0 →
      (z ∈ A ↔ 0 < (C*(z-ξ)/(1+K*(z-ξ))).im ∧
        (p*(C*(z-ξ)/(1+K*(z-ξ)))).im < 0)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ SectorChart A ξ θ := by
  obtain ⟨θ,hθ,hθπ,hpolar⟩ := intersection_halfplanes_sector hp
  refine ⟨θ,hθ,hθπ,{z | 1+K*(z-ξ) ≠ 0}, {w | C-K*w ≠ 0},
    (fun z => C*(z-ξ)/(1+K*(z-ξ))), (fun w => ξ+w/(C-K*w)),
    by simp, DiskUnionBoundarySectors.straightening_chart ξ K C hC,
    by simp, ?_, ?_⟩
  · have hd := DiskUnionBoundarySectors.straightening_chart_derivative ξ K C ξ (by simp)
    rw [hd.deriv]
    simpa using hC
  · intro z hz
    exact (hside z hz).trans (hpolar _)

lemma ratio_times_coordinate (a b σ h : ℂ) (ha : a ≠ 0) :
    (conj b / conj a) * (σ * conj a * h) = σ * conj b * h := by
  have hconj : conj a ≠ 0 := by simpa only [map_ne_zero] using ha
  field_simp

lemma signed_mixed_disk_sector_chart {c d ξ : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hξc : dist ξ c = R) (hξd : dist ξ d = S)
    (hdet : (ξ-c).re*(ξ-d).im-(ξ-c).im*(ξ-d).re ≠ 0) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧
      SectorChart (ball c R \ closedBall d S) ξ θ := by
  have ha : ξ-c ≠ 0 := by
    intro h
    have : dist ξ c = 0 := by simp [dist_eq_norm,h]
    linarith
  have hb : ξ-d ≠ 0 := by
    intro h
    have : dist ξ d = 0 := by simp [dist_eq_norm,h]
    linarith
  obtain ⟨K,hKa,hKb⟩ := DiskUnionBoundarySectors.simultaneous_straightening_coefficient hdet
  by_cases hpos : 0 < (ξ-c).re*(ξ-d).im-(ξ-c).im*(ξ-d).re
  · have hp : (conj (ξ-d)/conj (ξ-c)).im < 0 := by
      have hn : 0 < Complex.normSq (conj (ξ-c)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa only [map_ne_zero] using ha))
      simp only [Complex.div_im, Complex.conj_re, Complex.conj_im]
      rw [←sub_div]
      exact div_neg_of_neg_of_pos (by nlinarith) hn
    apply straightening_intersection_chart (ξ:=ξ) (K:=K)
      (C := -Complex.I*conj (ξ-c))
      (mul_ne_zero (by simp) (by simpa only [map_ne_zero] using ha)) hp
    intro z hz
    have hc := DiskUnionBoundarySectors.straightening_disk_side ξ c K z R hR hξc hKa hz
    have hd := straightening_exterior_side ξ d K z S hS hξd hKb hz
    have hr := ratio_times_coordinate (ξ-c) (ξ-d) (-Complex.I)
      ((z-ξ)/(1+K*(z-ξ))) ha
    rw [show -Complex.I*conj (ξ-c)*(z-ξ)/(1+K*(z-ξ)) =
      -Complex.I*conj (ξ-c)*((z-ξ)/(1+K*(z-ξ))) by ring,hr]
    exact and_congr hc hd
  · have hneg : 0 < (ξ-d).re*(ξ-c).im-(ξ-d).im*(ξ-c).re := by
      have := lt_of_le_of_ne (not_lt.mp hpos) hdet
      nlinarith
    have hp : (conj (ξ-c)/conj (ξ-d)).im < 0 := by
      have hn : 0 < Complex.normSq (conj (ξ-d)) := by
        rw [Complex.normSq_eq_norm_sq]
        exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa only [map_ne_zero] using hb))
      simp only [Complex.div_im, Complex.conj_re, Complex.conj_im]
      rw [←sub_div]
      exact div_neg_of_neg_of_pos (by nlinarith) hn
    apply straightening_intersection_chart (ξ:=ξ) (K:=K)
      (C := Complex.I*conj (ξ-d))
      (mul_ne_zero (by simp) (by simpa only [map_ne_zero] using hb)) hp
    intro z hz
    have hc := DiskUnionBoundarySectors.straightening_disk_side ξ c K z R hR hξc hKa hz
    have hd := straightening_exterior_side ξ d K z S hS hξd hKb hz
    have hr := ratio_times_coordinate (ξ-d) (ξ-c) Complex.I
      ((z-ξ)/(1+K*(z-ξ))) hb
    rw [show Complex.I*conj (ξ-d)*(z-ξ)/(1+K*(z-ξ)) =
      Complex.I*conj (ξ-d)*((z-ξ)/(1+K*(z-ξ))) by ring,hr]
    have hi (a : ℂ) : (Complex.I*conj a*((z-ξ)/(1+K*(z-ξ)))).im =
      -(-Complex.I*conj a*((z-ξ)/(1+K*(z-ξ)))).im := by
      rw [show Complex.I*conj a*((z-ξ)/(1+K*(z-ξ))) =
        -(-Complex.I*conj a*((z-ξ)/(1+K*(z-ξ)))) by ring,Complex.neg_im]
    rw [hi,hi]
    change (z ∈ ball c R ∧ z ∉ closedBall d S) ↔ _
    rw [hc,show z ∉ closedBall d S ↔ z ∈ (closedBall d S)ᶜ by rfl,hd]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

lemma mixed_disk_sector_chart {c d ξ : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hξc : dist ξ c = R) (hξd : dist ξ d = S)
    (hext : dist c d ≠ R+S) (hint : dist c d ≠ |R-S|) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2*Real.pi ∧
      SectorChart (ball c R \ closedBall d S) ξ θ := by
  obtain ⟨θ,hθ,hθπ,hchart⟩ := signed_mixed_disk_sector_chart hR hS hξc hξd
    (DiskUnionBoundarySectors.two_circle_transverse hR hS hξc hξd hext hint)
  exact ⟨θ,hθ,by linarith [Real.pi_pos],hchart⟩

lemma circularCut_local_retained {D : Set ℂ} {centers : Finset ℂ} {q : ℂ → ℝ} {p : ℂ}
    (hp : p ∉ ⋃ c ∈ centers, closedBall c (q c)) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut D centers q ↔ z ∈ D := by
  let W := (⋃ c ∈ centers, closedBall c (q c))ᶜ
  have hclosed : IsClosed (⋃ c ∈ centers, closedBall c (q c)) :=
    centers.finite_toSet.isClosed_biUnion (fun _ _ => isClosed_closedBall)
  refine ⟨W,hclosed.isOpen_compl,hp,?_⟩
  intro z hz
  exact and_iff_left hz

lemma circularCut_local_single_deletion {D : Set ℂ} {centers : Finset ℂ}
    {q : ℂ → ℝ} {p c : ℂ} (hc : c ∈ centers)
    (hother : ∀ d ∈ centers, d ≠ c → p ∉ closedBall d (q d)) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut D centers q ↔ z ∈ D \ closedBall c (q c) := by
  let W := (⋃ d ∈ centers.erase c, closedBall d (q d))ᶜ
  have hclosed : IsClosed (⋃ d ∈ centers.erase c, closedBall d (q d)) :=
    (centers.erase c).finite_toSet.isClosed_biUnion (fun _ _ => isClosed_closedBall)
  have hpW : p ∈ W := by
    intro h
    obtain ⟨d,hd,hdp⟩ := mem_iUnion₂.mp h
    exact hother d (Finset.mem_erase.mp hd).2 (Finset.mem_erase.mp hd).1 hdp
  refine ⟨W,hclosed.isOpen_compl,hpW,?_⟩
  intro z hz
  constructor
  · rintro ⟨hzD,hzn⟩
    exact ⟨hzD, fun hzC => hzn (mem_iUnion₂.mpr ⟨c,hc,hzC⟩)⟩
  · rintro ⟨hzD,hzC⟩
    refine ⟨hzD,?_⟩
    intro h
    obtain ⟨d,hd,hdz⟩ := mem_iUnion₂.mp h
    by_cases he : d = c
    · subst d; exact hzC hdz
    · exact hz (mem_iUnion₂.mpr ⟨d,Finset.mem_erase.mpr ⟨he,hd⟩,hdz⟩)

lemma circularCut_retained_sector {D : Set ℂ} {centers : Finset ℂ} {q : ℂ → ℝ}
    {p : ℂ} {θ : ℝ} (hchart : SectorChart D p θ)
    (hp : p ∉ ⋃ c ∈ centers, closedBall c (q c)) :
    SectorChart (circularCut D centers q) p θ := by
  obtain ⟨W,hW,hpW,hside⟩ := circularCut_local_retained (D:=D) hp
  exact sectorChart_local hchart hW hpW hside

lemma circularCut_deleting_sector {D : Set ℂ} {centers : Finset ℂ} {q : ℂ → ℝ}
    {p c : ℂ} (hD : IsOpen D) (hpD : p ∈ D) (hc : c ∈ centers) (hq : 0 < q c)
    (hp : dist p c = q c)
    (hother : ∀ d ∈ centers, d ≠ c → p ∉ closedBall d (q d)) :
    SectorChart (circularCut D centers q) p Real.pi := by
  obtain ⟨W,hW,hpW,hside⟩ := circularCut_local_single_deletion (D:=D) hc hother
  apply sectorChart_local (exterior_disk_sector_chart c p (q c) hq hp)
    (hW.inter hD) ⟨hpW,hpD⟩
  intro z hz
  exact (hside z hz.1).trans (and_iff_right hz.2)

lemma circularCut_deleting_negative_side {D : Set ℂ} {centers : Finset ℂ}
    {q : ℂ → ℝ} {p c : ℂ} (hD : IsOpen D) (hpD : p ∈ D) (hc : c ∈ centers)
    (hq : 0 < q c) (hother : ∀ d ∈ centers, d ≠ c → p ∉ closedBall d (q d)) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut D centers q ↔ (-1 : ℝ)*(‖z-c‖^2-(q c)^2) < 0 := by
  obtain ⟨W,hW,hpW,hside⟩ := circularCut_local_single_deletion (D:=D) hc hother
  refine ⟨W ∩ D,hW.inter hD,⟨hpW,hpD⟩,?_⟩
  intro z hz
  exact ((hside z hz.1).trans (and_iff_right hz.2)).trans (exterior_negative_side c z hq)

lemma circularCut_mixed_sector {D W₀ : Set ℂ} {centers : Finset ℂ}
    {q : ℂ → ℝ} {p a c : ℂ} {R : ℝ} (hW₀ : IsOpen W₀) (hpW₀ : p ∈ W₀)
    (hlocal : ∀ z ∈ W₀, z ∈ D ↔ z ∈ ball a R)
    (hc : c ∈ centers) (hR : 0 < R) (hq : 0 < q c)
    (hpR : dist p a = R) (hpq : dist p c = q c)
    (hext : dist a c ≠ R+q c) (hint : dist a c ≠ |R-q c|)
    (hother : ∀ d ∈ centers, d ≠ c → p ∉ closedBall d (q d)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2*Real.pi ∧
      SectorChart (circularCut D centers q) p θ := by
  obtain ⟨θ,hθ,hθ2,hchart⟩ := mixed_disk_sector_chart hR hq hpR hpq hext hint
  obtain ⟨W,hW,hpW,hside⟩ := circularCut_local_single_deletion (D:=D) hc hother
  refine ⟨θ,hθ,hθ2,sectorChart_local hchart (hW.inter hW₀) ⟨hpW,hpW₀⟩ ?_⟩
  intro z hz
  exact (hside z hz.1).trans (and_congr_left (fun _ => hlocal z hz.2))

lemma circularCut_retained_negative_side {D W₀ : Set ℂ} {centers : Finset ℂ}
    {q : ℂ → ℝ} {p a : ℂ} {R : ℝ} (hW₀ : IsOpen W₀) (hpW₀ : p ∈ W₀)
    (hlocal : ∀ z ∈ W₀, z ∈ D ↔ z ∈ ball a R) (hR : 0 < R)
    (hp : p ∉ ⋃ c ∈ centers, closedBall c (q c)) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut D centers q ↔ (1 : ℝ)*(‖z-a‖^2-R^2) < 0 := by
  obtain ⟨W,hW,hpW,hside⟩ := circularCut_local_retained (D:=D) hp
  refine ⟨W ∩ W₀,hW.inter hW₀,⟨hpW,hpW₀⟩,?_⟩
  intro z hz
  exact ((hside z hz.1).trans (hlocal z hz.2)).trans (ball_negative_side a z hR)

lemma diskUnion_local_single_circle {s : Finset ℂ} {r : ℂ → ℝ} {p : ℂ}
    (hp : p ∈ frontier (diskUnion s r))
    (hnotdouble : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      p ∉ sphere a (r a) ∩ sphere b (r b)) :
    ∃ a ∈ s, dist p a = r a ∧ ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ diskUnion s r ↔ z ∈ ball a (r a) := by
  have hp' : p ∈ frontier (DiskUnionBoundarySectors.diskUnion s r) := hp
  obtain ⟨a,ha,hpa⟩ := DiskUnionBoundarySectors.boundary_active s r hp'
  obtain ⟨ε,hε,havoid⟩ := DiskUnionBoundarySectors.inactive_disks_avoided s r hp'
  refine ⟨a,ha,hpa,ball p ε,isOpen_ball,mem_ball_self hε,?_⟩
  intro z hz
  constructor
  · intro h
    obtain ⟨b,hb,hzb⟩ := mem_iUnion₂.mp h
    by_cases he : b = a
    · simpa [he] using hzb
    · have hna : dist p b ≠ r b := by
        intro hpb
        exact hnotdouble a ha b hb (Ne.symm he) ⟨hpa,hpb⟩
      exact False.elim (havoid z hz b hb hna (ball_subset_closedBall hzb))
  · intro hza
    exact mem_iUnion₂.mpr ⟨a,ha,hza⟩

lemma circularCut_frontier_avoids_open_deletions {D : Set ℂ} {centers : Finset ℂ}
    {q : ℂ → ℝ} {p c : ℂ} (hp : p ∈ frontier (circularCut D centers q))
    (hc : c ∈ centers) : p ∉ ball c (q c) := by
  have hsub : circularCut D centers q ⊆ (ball c (q c))ᶜ := by
    intro z hz hzc
    exact hz.2 (mem_iUnion₂.mpr ⟨c,hc,ball_subset_closedBall hzc⟩)
  exact closure_minimal hsub isOpen_ball.isClosed_compl hp.1

lemma circularCut_frontier_cases {D : Set ℂ} {centers : Finset ℂ} {q : ℂ → ℝ}
    (hq : ∀ c ∈ centers, 0 < q c) {p : ℂ}
    (hp : p ∈ frontier (circularCut D centers q)) :
    p ∈ closure D ∧ (p ∈ frontier D ∨ ∃ c ∈ centers, p ∈ sphere c (q c)) := by
  have hpcl : p ∈ closure D := closure_mono sdiff_subset hp.1
  refine ⟨hpcl,?_⟩
  have hm := frontier_inter_subset D (⋃ c ∈ centers, closedBall c (q c))ᶜ hp
  rcases hm with hm | hm
  · exact Or.inl hm.1
  · have hpu : p ∈ frontier (⋃ c ∈ centers, closedBall c (q c)) := by
      simpa only [frontier_compl] using hm.2
    obtain ⟨c,hc,hpc⟩ := mem_iUnion₂.mp (centers.frontier_biUnion_subset
      (fun c => closedBall c (q c)) hpu)
    exact Or.inr ⟨c,hc,frontier_closedBall_subset_sphere hpc⟩

lemma circularCut_other_deletions_avoided {centers : Finset ℂ} {q : ℂ → ℝ}
    (hdisjoint : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {p c : ℂ} (hc : c ∈ centers) (hp : p ∈ sphere c (q c)) :
    ∀ d ∈ centers, d ≠ c → p ∉ closedBall d (q d) := by
  intro d hd hdc hpd
  exact Set.disjoint_left.mp (hdisjoint c hc d hd (Ne.symm hdc))
    (sphere_subset_closedBall hp) hpd

lemma finite_original_deleting_intersections (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hnontangent : ∀ x ∈ centers, ∀ a ∈ s,
      dist x a ≠ q x + r a ∧ dist x a ≠ |q x-r a|) :
    (⋃ a ∈ s, ⋃ c ∈ centers, sphere a (r a) ∩ sphere c (q c)).Finite := by
  apply s.finite_toSet.biUnion
  intro a ha
  apply centers.finite_toSet.biUnion
  intro c hc
  by_cases he : a = c
  · subst c
    have hneq : r a ≠ q a := by
      intro h
      have hn := (hnontangent a hc a ha).2
      simp [h] at hn
    have hempty : sphere a (r a) ∩ sphere a (q a) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hneq ((mem_sphere.mp hz.1).symm.trans (mem_sphere.mp hz.2))
    rw [hempty]
    exact Set.finite_empty
  · exact DiskUnionBoundarySectors.finite_circle_intersection a c (r a) (q c) he

lemma circularCut_boundarySectors (s centers corners : Finset ℂ) (r q : ℂ → ℝ)
    (hr : ∀ a ∈ s, 0 < r a) (hq : ∀ c ∈ centers, 0 < q c)
    (hcorners : corners ⊆ centers)
    (hsmooth : ∀ p ∈ frontier (diskUnion s r), p ∉ corners →
      SectorChart (diskUnion s r) p Real.pi)
    (hdisjoint : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    (hnontangent : ∀ x ∈ centers, ∀ a ∈ s,
      dist x a ≠ q x+r a ∧ dist x a ≠ |q x-r a|)
    (havoid : ∀ x ∈ centers, ∀ z : ℂ,
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ dist z a = r a ∧ dist z b = r b) →
        z ∉ sphere x (q x)) :
    BoundarySectors (circularCut (diskUnion s r) centers q) := by
  classical
  let K := circularCut (diskUnion s r) centers q
  let joins : Set ℂ := frontier K ∩ frontier (diskUnion s r) ∩
    (⋃ c ∈ centers, sphere c (q c))
  have hfinite : joins.Finite := by
    apply (finite_original_deleting_intersections s centers r q hnontangent).subset
    intro p hp
    obtain ⟨a,ha,hpa⟩ := DiskUnionBoundarySectors.boundary_active s r hp.1.2
    obtain ⟨c,hc,hpc⟩ := mem_iUnion₂.mp hp.2
    exact mem_iUnion₂.mpr ⟨a,ha,mem_iUnion₂.mpr ⟨c,hc,⟨hpa,hpc⟩⟩⟩
  let J := hfinite.toFinset
  have hJ : ∀ p : ℂ, p ∈ J ↔ p ∈ joins := by intro p; exact Set.Finite.mem_toFinset hfinite
  have hD : IsOpen (diskUnion s r) := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  refine ⟨J, ?_, ?_, ?_⟩
  · intro p hp
    exact ((hJ p).mp hp).1.1
  · intro p hpK hpJ
    obtain ⟨hpcl,hcases⟩ := circularCut_frontier_cases hq hpK
    by_cases hpsphere : ∃ c ∈ centers, p ∈ sphere c (q c)
    · obtain ⟨c,hc,hpc⟩ := hpsphere
      have hpD : p ∈ diskUnion s r := by
        by_contra hpnD
        have hpfront : p ∈ frontier (diskUnion s r) := ⟨hpcl, fun h => hpnD (interior_subset h)⟩
        exact hpJ ((hJ p).mpr ⟨⟨hpK,hpfront⟩,mem_iUnion₂.mpr ⟨c,hc,hpc⟩⟩)
      exact circularCut_deleting_sector hD hpD hc (hq c hc) (mem_sphere.mp hpc)
        (circularCut_other_deletions_avoided hdisjoint hc hpc)
    · have hpfront : p ∈ frontier (diskUnion s r) := hcases.resolve_right hpsphere
      have hpoutside : p ∉ ⋃ c ∈ centers, closedBall c (q c) := by
        intro h
        obtain ⟨c,hc,hpc⟩ := mem_iUnion₂.mp h
        have hle := mem_closedBall.mp hpc
        have hn := circularCut_frontier_avoids_open_deletions hpK hc
        have hge : q c ≤ dist p c := not_lt.mp hn
        exact hpsphere ⟨c,hc,le_antisymm hle hge⟩
      have hpnc : p ∉ corners := by
        intro hpc
        exact hpoutside (mem_iUnion₂.mpr ⟨p,hcorners hpc,mem_closedBall_self (hq p (hcorners hpc)).le⟩)
      exact circularCut_retained_sector (hsmooth p hpfront hpnc) hpoutside
  · intro p hpJ
    have hpjoins := (hJ p).mp hpJ
    obtain ⟨c,hc,hpc⟩ := mem_iUnion₂.mp hpjoins.2
    have hnotdouble : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
        p ∉ sphere a (r a) ∩ sphere b (r b) := by
      intro a ha b hb hab hpd
      exact havoid c hc p ⟨a,ha,b,hb,hab,hpd.1,hpd.2⟩ hpc
    obtain ⟨a,ha,hpa,W,hW,hpW,hlocal⟩ := diskUnion_local_single_circle hpjoins.1.2 hnotdouble
    have hn := hnontangent c hc a ha
    apply circularCut_mixed_sector hW hpW hlocal hc (hr a ha) (hq c hc) hpa
      (mem_sphere.mp hpc)
    · simpa only [dist_comm,add_comm] using hn.1
    · simpa only [dist_comm,abs_sub_comm] using hn.2
    · exact circularCut_other_deletions_avoided hdisjoint hc hpc

lemma circularCut_original_negative_side_at {s centers : Finset ℂ} {r q : ℂ → ℝ}
    (hr : ∀ a ∈ s, 0 < r a) (hq : ∀ c ∈ centers, 0 < q c)
    {p a : ℂ} (ha : a ∈ s)
    (hp : p ∈ frontier (circularCut (diskUnion s r) centers q))
    (hpa : p ∈ sphere a (r a))
    (hotherOriginal : ∀ b ∈ s, b ≠ a → p ∉ sphere b (r b))
    (hotherCut : ∀ c ∈ centers, p ∉ sphere c (q c)) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut (diskUnion s r) centers q ↔
        (1 : ℝ)*(‖z-a‖^2-(r a)^2) < 0 := by
  have hpoutside : p ∉ ⋃ c ∈ centers, closedBall c (q c) := by
    intro h
    obtain ⟨c,hc,hpc⟩ := mem_iUnion₂.mp h
    have hle := mem_closedBall.mp hpc
    have hge : q c ≤ dist p c := not_lt.mp (circularCut_frontier_avoids_open_deletions hp hc)
    exact hotherCut c hc (le_antisymm hle hge)
  have hpfront : p ∈ frontier (diskUnion s r) := by
    have hh := (circularCut_frontier_cases hq hp).2
    rcases hh with hh | ⟨c,hc,hpc⟩
    · exact hh
    · exact False.elim (hotherCut c hc hpc)
  have hnotdouble : ∀ c ∈ s, ∀ b ∈ s, c ≠ b →
      p ∉ sphere c (r c) ∩ sphere b (r b) := by
    intro c hc b hb hcb hpc
    by_cases hca : c = a
    · subst c
      exact hotherOriginal b hb (Ne.symm hcb) hpc.2
    · exact hotherOriginal c hc hca hpc.1
  obtain ⟨b,hb,hpb,W,hW,hpW,hlocal⟩ := diskUnion_local_single_circle hpfront hnotdouble
  have hba : b = a := by
    by_contra hne
    exact hotherOriginal b hb hne hpb
  subst b
  exact circularCut_retained_negative_side hW hpW hlocal (hr a ha) hpoutside

lemma circularCut_deleting_negative_side_at {D : Set ℂ} {centers : Finset ℂ}
    {q : ℂ → ℝ} (hD : IsOpen D)
    (hdisjoint : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {p c : ℂ} (hc : c ∈ centers) (hp : p ∈ sphere c (q c))
    (hpD : p ∈ D) (hq : 0 < q c) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut D centers q ↔ (-1 : ℝ)*(‖z-c‖^2-(q c)^2) < 0 := by
  exact circularCut_deleting_negative_side hD hpD hc hq
    (circularCut_other_deletions_avoided hdisjoint hc hp)

lemma circularCut_original_piece_point {s centers : Finset ℂ} {r q : ℂ → ℝ}
    (hr : ∀ a ∈ s, 0 < r a) (hq : ∀ c ∈ centers, 0 < q c)
    {p a : ℂ} (ha : a ∈ s)
    (hp : p ∈ frontier (circularCut (diskUnion s r) centers q))
    (hpa : p ∈ sphere a (r a))
    (hotherOriginal : ∀ b ∈ s, b ≠ a → p ∉ sphere b (r b))
    (hotherCut : ∀ c ∈ centers, p ∉ sphere c (q c)) :
    p ∈ frontier (diskUnion s r) ∧
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut (diskUnion s r) centers q ↔
        (1 : ℝ)*(‖z-a‖^2-(r a)^2) < 0 := by
  constructor
  · rcases (circularCut_frontier_cases hq hp).2 with hh | ⟨c,hc,hpc⟩
    · exact hh
    · exact False.elim (hotherCut c hc hpc)
  · exact circularCut_original_negative_side_at hr hq ha hp hpa hotherOriginal hotherCut

lemma circularCut_deleting_piece_point {s centers : Finset ℂ} {r q : ℂ → ℝ}
    (hq : ∀ c ∈ centers, 0 < q c)
    (hdisjoint : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {p c : ℂ} (hc : c ∈ centers)
    (hp : p ∈ frontier (circularCut (diskUnion s r) centers q))
    (hpc : p ∈ sphere c (q c))
    (hotherOriginal : ∀ a ∈ s, p ∉ sphere a (r a)) :
    p ∈ diskUnion s r ∧
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut (diskUnion s r) centers q ↔
        (-1 : ℝ)*(‖z-c‖^2-(q c)^2) < 0 := by
  have hpD : p ∈ diskUnion s r := by
    have hpcl := (circularCut_frontier_cases hq hp).1
    by_contra hpnD
    have hpfront : p ∈ frontier (diskUnion s r) := ⟨hpcl,fun h => hpnD (interior_subset h)⟩
    obtain ⟨a,ha,hpa⟩ := DiskUnionBoundarySectors.boundary_active s r hpfront
    exact hotherOriginal a ha hpa
  refine ⟨hpD,?_⟩
  exact circularCut_deleting_negative_side_at
    (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball)
    hdisjoint hc hpc hpD (hq c hc)

lemma closed_arc_subset_original_frontier {D : Set ℂ} {a : ℂ} {R α β : ℝ}
    (hαβ : α < β)
    (hopen : arcParam a R '' Ioo α β ⊆ frontier D) :
    arcParam a R '' Icc α β ⊆ frontier D := by
  have hcont : Continuous (arcParam a R) := by unfold arcParam; fun_prop
  have hclosure : arcParam a R '' closure (Ioo α β) ⊆ closure (arcParam a R '' Ioo α β) :=
    image_closure_subset_closure_image hcont
  rw [closure_Ioo hαβ.ne] at hclosure
  exact hclosure.trans (closure_minimal hopen isClosed_frontier)

/-- Circle arrays retain the literal source labels. -/
def cutLabelCenter {s centers : Finset ℂ} : (↥s ⊕ ↥centers) → ℂ
  | .inl a => a
  | .inr c => c

def cutLabelRadius {s centers : Finset ℂ} (r q : ℂ → ℝ) : (↥s ⊕ ↥centers) → ℝ
  | .inl a => r a
  | .inr c => q c

def cutLabelSign {s centers : Finset ℂ} : (↥s ⊕ ↥centers) → ℝ
  | .inl _ => 1
  | .inr _ => -1

lemma cutLabelRadius_positive {s centers : Finset ℂ} {r q : ℂ → ℝ}
    (hr : ∀ a ∈ s, 0 < r a) (hq : ∀ c ∈ centers, 0 < q c)
    (i : ↥s ⊕ ↥centers) : 0 < cutLabelRadius r q i := by
  cases i with
  | inl a => exact hr a a.property
  | inr c => exact hq c c.property

lemma cutLabel_circles_distinct {s centers : Finset ℂ} {r q : ℂ → ℝ}
    (hnontangent : ∀ x ∈ centers, ∀ a ∈ s,
      dist x a ≠ q x+r a ∧ dist x a ≠ |q x-r a|)
    {i j : ↥s ⊕ ↥centers} (hij : i ≠ j) :
    cutLabelCenter i ≠ cutLabelCenter j ∨ cutLabelRadius r q i ≠ cutLabelRadius r q j := by
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      left
      intro heq
      exact hij (congrArg Sum.inl (Subtype.ext heq))
    | inr c =>
      by_cases heq : (a : ℂ) = c
      · right
        intro hrad
        have hn := (hnontangent c c.property a a.property).2
        change r a = q c at hrad
        have hrad' : q a = r a := by simpa only [←heq] using hrad.symm
        exact hn (by simp only [←heq,dist_self,hrad',sub_self,abs_zero])
      · exact Or.inl heq
  | inr c =>
    cases j with
    | inl a =>
      by_cases heq : (c : ℂ) = a
      · right
        intro hrad
        have hn := (hnontangent c c.property a a.property).2
        change q c = r a at hrad
        have hrad' : q a = r a := by simpa only [heq] using hrad
        exact hn (by simp only [heq,dist_self,hrad',sub_self,abs_zero])
      · exact Or.inl heq
    | inr d =>
      left
      intro heq
      exact hij (congrArg Sum.inr (Subtype.ext heq))

lemma circularCut_frontier_subset_labelCircles {s centers : Finset ℂ} {r q : ℂ → ℝ}
    (hq : ∀ c ∈ centers, 0 < q c) :
    frontier (circularCut (diskUnion s r) centers q) ⊆
      ⋃ i : ↥s ⊕ ↥centers, sphere (cutLabelCenter i) (cutLabelRadius r q i) := by
  intro p hp
  rcases (circularCut_frontier_cases hq hp).2 with hD | ⟨c,hc,hpc⟩
  · obtain ⟨a,ha,hpa⟩ := DiskUnionBoundarySectors.boundary_active s r hD
    exact mem_iUnion.mpr ⟨Sum.inl ⟨a,ha⟩,hpa⟩
  · exact mem_iUnion.mpr ⟨Sum.inr ⟨c,hc⟩,hpc⟩

lemma cutLabel_piece_point {s centers : Finset ℂ} {r q : ℂ → ℝ}
    (hr : ∀ a ∈ s, 0 < r a) (hq : ∀ c ∈ centers, 0 < q c)
    (hdisjoint : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {p : ℂ} (i : ↥s ⊕ ↥centers)
    (hp : p ∈ frontier (circularCut (diskUnion s r) centers q))
    (hpi : p ∈ sphere (cutLabelCenter i) (cutLabelRadius r q i))
    (hother : ∀ j : ↥s ⊕ ↥centers, j ≠ i →
      p ∉ sphere (cutLabelCenter j) (cutLabelRadius r q j)) :
    (match i with | .inl _ => p ∈ frontier (diskUnion s r) | .inr _ => p ∈ diskUnion s r) ∧
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧
      ∀ z ∈ W, z ∈ circularCut (diskUnion s r) centers q ↔
        cutLabelSign i*(‖z-cutLabelCenter i‖^2-(cutLabelRadius r q i)^2) < 0 := by
  cases i with
  | inl a =>
    apply circularCut_original_piece_point hr hq a.property hp hpi
    · intro b hb hba
      apply hother (.inl ⟨b,hb⟩)
      intro he
      have he' : b = (a : ℂ) := by
        have hs := Sum.inl.inj he
        exact congrArg Subtype.val hs
      exact hba he'
    · intro c hc
      exact hother (.inr ⟨c,hc⟩) (by simp)
  | inr c =>
    apply circularCut_deleting_piece_point hq hdisjoint c.property hp hpi
    intro a ha
    exact hother (.inl ⟨a,ha⟩) (by simp)

end D12Complex.CircularCutGeometry


noncomputable section
open Set Metric MeasureTheory
open scoped Interval

namespace D12Complex.CircularCutGeometry

/-- Finite exceptional angular sets are null for one-dimensional Lebesgue measure. -/
theorem finite_angles_ae_avoided {E : Set ℝ} (hE : E.Finite) :
    ∀ᵐ t : ℝ ∂volume, t ∉ E := by
  rw [ae_iff]
  simpa only [not_not, ofPred_mem_eq] using hE.measure_zero volume

/-- Additivity over any finite collection of angular intervals. The set `inside`
may differ from their union at the finite set `E` and at the two global endpoints.
No periodicity, smoothness, or harmonicity is needed. -/
theorem finite_angular_interval_additivity {ι : Type*}
    (pieces : Finset ι) (start stop : ι → ℝ) (A B : ℝ) (hAB : A ≤ B)
    (inside E : Set ℝ) (hinside : MeasurableSet inside) (hE : E.Finite)
    (hbounds : ∀ i ∈ pieces, A ≤ start i ∧ start i < stop i ∧ stop i ≤ B)
    (hdisjoint : Set.Pairwise (↑pieces : Set ι)
      (fun i j => Disjoint (Ioo (start i) (stop i)) (Ioo (start j) (stop j))))
    (hcoverage : ∀ t ∈ Ioo A B, t ∉ E →
      (t ∈ inside ↔ ∃ i ∈ pieces, t ∈ Ioo (start i) (stop i)))
    (f : ℝ → ℝ)
    (hf : ∀ i ∈ pieces, IntervalIntegrable f volume (start i) (stop i)) :
    (∑ i ∈ pieces, ∫ t in start i..stop i, f t) =
      ∫ t in A..B, inside.indicator f t := by
  have hAE : Ioc A B ∩ inside =ᵐ[volume]
      ⋃ i ∈ pieces, Ioo (start i) (stop i) := by
    filter_upwards [finite_angles_ae_avoided (hE.union (Set.finite_singleton B))]
      with t ht
    have htE : t ∉ E := fun h => ht (Or.inl h)
    have htB : t ≠ B := fun h => ht (Or.inr h)
    apply propext
    change (t ∈ Ioc A B ∧ t ∈ inside) ↔ _
    constructor
    · rintro ⟨htAB, htinside⟩
      obtain ⟨i, hi, hti⟩ := (hcoverage t ⟨htAB.1, lt_of_le_of_ne htAB.2 htB⟩ htE).mp htinside
      exact mem_iUnion₂.mpr ⟨i, hi, hti⟩
    · intro htunion
      obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp htunion
      have hbi := hbounds i hi
      have htAB : t ∈ Ioo A B := ⟨hbi.1.trans_lt hti.1, hti.2.trans_le hbi.2.2⟩
      exact ⟨⟨htAB.1, htAB.2.le⟩,
        (hcoverage t htAB htE).mpr ⟨i, hi, hti⟩⟩
  rw [intervalIntegral.integral_of_le hAB, setIntegral_indicator hinside,
    setIntegral_congr_set hAE]
  rw [integral_biUnion_finset pieces (fun _ _ => measurableSet_Ioo) hdisjoint]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_of_le (hbounds i hi).2.1.le,
      integral_Ioc_eq_integral_Ioo]
  · intro i hi
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (hbounds i hi).2.1.le).mp
      (hf i hi)

/-- Consecutive pairs of a finite set of real breakpoints. -/
noncomputable def angularCells (E : Finset ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (E.product E).filter (fun p => p.1 < p.2 ∧
    ∀ e ∈ E, e ≤ p.1 ∨ p.2 ≤ e)

theorem mem_angularCells {E : Finset ℝ} {p : ℝ × ℝ} :
    p ∈ angularCells E ↔ p.1 ∈ E ∧ p.2 ∈ E ∧ p.1 < p.2 ∧
      ∀ e ∈ E, e ≤ p.1 ∨ p.2 ≤ e := by
  classical
  rcases p with ⟨x, y⟩
  simp only [angularCells, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product]
  tauto

theorem angularCells_avoid_breakpoints {E : Finset ℝ} {p : ℝ × ℝ}
    (hp : p ∈ angularCells E) {t : ℝ} (ht : t ∈ Ioo p.1 p.2) : t ∉ E := by
  intro htE
  rcases (mem_angularCells.mp hp).2.2.2 t htE with h | h
  · exact (not_le_of_gt ht.1) h
  · exact (not_le_of_gt ht.2) h

theorem angularCells_pairwise_disjoint (E : Finset ℝ) :
    Set.Pairwise (↑(angularCells E) : Set (ℝ × ℝ))
      (fun p q => Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2)) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.mpr
  intro t ht hu
  obtain ⟨hpx, hpy, hplt, hpadj⟩ := mem_angularCells.mp hp
  obtain ⟨hqx, hqy, hqlt, hqadj⟩ := mem_angularCells.mp hq
  have hqxpx : q.1 ≤ p.1 := by
    rcases hpadj q.1 hqx with h | h
    · exact h
    · exact False.elim ((not_le_of_gt ht.2) (h.trans hu.1.le))
  have hpxqx : p.1 ≤ q.1 := by
    rcases hqadj p.1 hpx with h | h
    · exact h
    · exact False.elim ((not_le_of_gt hu.2) (h.trans ht.1.le))
  have hpqy : p.2 ≤ q.2 := by
    rcases hpadj q.2 hqy with h | h
    · exact False.elim ((not_le_of_gt hu.2) (h.trans ht.1.le))
    · exact h
  have hqpy : q.2 ≤ p.2 := by
    rcases hqadj p.2 hpy with h | h
    · exact False.elim ((not_le_of_gt ht.2) (h.trans hu.1.le))
    · exact h
  exact hpq (Prod.ext (le_antisymm hpxqx hqxpx) (le_antisymm hpqy hqpy))

theorem angularCells_cover {E : Finset ℝ} {A B t : ℝ}
    (hA : A ∈ E) (hB : B ∈ E) (ht : t ∈ Ioo A B) (htE : t ∉ E) :
    ∃ p ∈ angularCells E, t ∈ Ioo p.1 p.2 := by
  classical
  let L := E.filter (fun e => e < t)
  let U := E.filter (fun e => t < e)
  have hL : L.Nonempty := ⟨A, Finset.mem_filter.mpr ⟨hA, ht.1⟩⟩
  have hU : U.Nonempty := ⟨B, Finset.mem_filter.mpr ⟨hB, ht.2⟩⟩
  let x := L.max' hL
  let y := U.min' hU
  have hx : x ∈ E ∧ x < t := Finset.mem_filter.mp (L.max'_mem hL)
  have hy : y ∈ E ∧ t < y := Finset.mem_filter.mp (U.min'_mem hU)
  refine ⟨(x, y), mem_angularCells.mpr ⟨hx.1, hy.1, hx.2.trans hy.2, ?_⟩,
    hx.2, hy.2⟩
  intro e he
  by_cases het : e < t
  · exact Or.inl (L.le_max' e (Finset.mem_filter.mpr ⟨he, het⟩))
  · right
    have hte : t < e := lt_of_le_of_ne (not_lt.mp het) (fun h => htE (h ▸ he))
    exact U.min'_le e (Finset.mem_filter.mpr ⟨he, hte⟩)

/-- Membership in a set is constant on a connected set avoiding its frontier. -/
theorem membership_constant_of_preconnected {X : Type*} [TopologicalSpace X]
    {C S : Set X} (hC : IsPreconnected C) (havoid : Disjoint C (frontier S)) :
    (∀ x ∈ C, x ∈ S) ∨ (∀ x ∈ C, x ∉ S) := by
  have hcover : C ⊆ interior S ∪ interior Sᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact Set.disjoint_left.mp havoid
  have hd : Disjoint (interior S) (interior Sᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hC.subset_or_subset isOpen_interior isOpen_interior hd hcover with h | h
  · exact Or.inl (fun x hx => interior_subset (h hx))
  · exact Or.inr (fun x hx => interior_subset (h hx))

/-- The midpoint test selects an entire adjacent cell when every boundary point
in the global open interval is a breakpoint. -/
theorem angularCell_membership_constant {E : Finset ℝ} {A B : ℝ}
    (hbound : ∀ e ∈ E, e ∈ Icc A B) (inside : Set ℝ)
    (hfrontier : frontier inside ∩ Ioo A B ⊆ (↑E : Set ℝ))
    {p : ℝ × ℝ} (hp : p ∈ angularCells E) :
    ∀ t ∈ Ioo p.1 p.2, (t ∈ inside ↔ (p.1 + p.2) / 2 ∈ inside) := by
  have hpm := mem_angularCells.mp hp
  have havoid : Disjoint (Ioo p.1 p.2) (frontier inside) := by
    apply Set.disjoint_left.mpr
    intro t ht htf
    have htAB : t ∈ Ioo A B :=
      ⟨(hbound p.1 hpm.1).1.trans_lt ht.1,
        ht.2.trans_le (hbound p.2 hpm.2.1).2⟩
    exact angularCells_avoid_breakpoints hp ht (hfrontier ⟨htf, htAB⟩)
  have hm : (p.1 + p.2) / 2 ∈ Ioo p.1 p.2 := by
    constructor <;> linarith [hpm.2.2.1]
  rcases membership_constant_of_preconnected isPreconnected_Ioo havoid with h | h
  · exact fun t ht => ⟨fun _ => h _ hm, fun _ => h t ht⟩
  · intro t ht
    exact iff_of_false (h t ht) (h _ hm)

/-- An adjacent cell is selected precisely when its midpoint belongs to `inside`. -/
noncomputable def selectedAngularCells (E : Finset ℝ) (inside : Set ℝ) :
    Finset (ℝ × ℝ) := by
  classical
  exact (angularCells E).filter (fun p => (p.1 + p.2) / 2 ∈ inside)

theorem mem_selectedAngularCells {E : Finset ℝ} {inside : Set ℝ} {p : ℝ × ℝ} :
    p ∈ selectedAngularCells E inside ↔
      p ∈ angularCells E ∧ (p.1 + p.2) / 2 ∈ inside := by
  classical
  exact Finset.mem_filter

theorem selectedAngularCells_bounds {E : Finset ℝ} {inside : Set ℝ} {A B : ℝ}
    (hbound : ∀ e ∈ E, e ∈ Icc A B) {p : ℝ × ℝ}
    (hp : p ∈ selectedAngularCells E inside) :
    A ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ B := by
  have hm := mem_angularCells.mp (mem_selectedAngularCells.mp hp).1
  exact ⟨(hbound p.1 hm.1).1, hm.2.2.1, (hbound p.2 hm.2.1).2⟩

theorem selectedAngularCells_pairwise_disjoint (E : Finset ℝ) (inside : Set ℝ) :
    Set.Pairwise (↑(selectedAngularCells E inside) : Set (ℝ × ℝ))
      (fun p q => Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2)) := by
  intro p hp q hq hpq
  exact angularCells_pairwise_disjoint E
    (mem_selectedAngularCells.mp hp).1 (mem_selectedAngularCells.mp hq).1 hpq

theorem selectedAngularCells_subset_inside {E : Finset ℝ} {A B : ℝ}
    (hbound : ∀ e ∈ E, e ∈ Icc A B) (inside : Set ℝ)
    (hfrontier : frontier inside ∩ Ioo A B ⊆ (↑E : Set ℝ))
    {p : ℝ × ℝ} (hp : p ∈ selectedAngularCells E inside) :
    Ioo p.1 p.2 ⊆ inside := by
  have hm := mem_selectedAngularCells.mp hp
  intro t ht
  exact (angularCell_membership_constant hbound inside hfrontier hm.1 t ht).mpr hm.2

theorem selectedAngularCells_coverage {E : Finset ℝ} {A B : ℝ}
    (hA : A ∈ E) (hB : B ∈ E) (hbound : ∀ e ∈ E, e ∈ Icc A B)
    (inside : Set ℝ) (hfrontier : frontier inside ∩ Ioo A B ⊆ (↑E : Set ℝ))
    {t : ℝ} (ht : t ∈ Ioo A B) (htE : t ∉ E) :
    t ∈ inside ↔ ∃ p ∈ selectedAngularCells E inside, t ∈ Ioo p.1 p.2 := by
  constructor
  · intro htinside
    obtain ⟨p, hp, htp⟩ := angularCells_cover hA hB ht htE
    exact ⟨p, mem_selectedAngularCells.mpr ⟨hp,
      (angularCell_membership_constant hbound inside hfrontier hp t htp).mp htinside⟩, htp⟩
  · rintro ⟨p, hp, htp⟩
    exact selectedAngularCells_subset_inside hbound inside hfrontier hp htp

/-- The explicit finite angular partition yields the zero-extension integral
formula, including empty selections and whole angular intervals. -/
theorem selectedAngularCells_integral {E : Finset ℝ} {A B : ℝ} (hAB : A ≤ B)
    (hA : A ∈ E) (hB : B ∈ E) (hbound : ∀ e ∈ E, e ∈ Icc A B)
    (inside : Set ℝ) (hinside : MeasurableSet inside)
    (hfrontier : frontier inside ∩ Ioo A B ⊆ (↑E : Set ℝ))
    (f : ℝ → ℝ)
    (hf : ∀ p ∈ selectedAngularCells E inside,
      IntervalIntegrable f volume p.1 p.2) :
    (∑ p ∈ selectedAngularCells E inside, ∫ t in p.1..p.2, f t) =
      ∫ t in A..B, inside.indicator f t := by
  exact finite_angular_interval_additivity (selectedAngularCells E inside)
    Prod.fst Prod.snd A B hAB inside (↑E : Set ℝ) hinside E.finite_toSet
    (fun _ hp => selectedAngularCells_bounds hbound hp)
    (selectedAngularCells_pairwise_disjoint E inside)
    (fun _ ht htE => selectedAngularCells_coverage hA hB hbound inside hfrontier ht htE)
    f hf

/-- A canonical finite breakpoint set containing all interior boundary angles
and both ends of the angular range. -/
noncomputable def angularBreakpoints (A B : ℝ) (inside : Set ℝ)
    (hfinite : (frontier inside ∩ Ioo A B).Finite) : Finset ℝ := by
  classical
  exact insert A (insert B hfinite.toFinset)

theorem angularBreakpoints_properties {A B : ℝ} (hAB : A ≤ B)
    (inside : Set ℝ) (hfinite : (frontier inside ∩ Ioo A B).Finite) :
    A ∈ angularBreakpoints A B inside hfinite ∧
    B ∈ angularBreakpoints A B inside hfinite ∧
    (∀ e ∈ angularBreakpoints A B inside hfinite, e ∈ Icc A B) ∧
    frontier inside ∩ Ioo A B ⊆ (↑(angularBreakpoints A B inside hfinite) : Set ℝ) := by
  classical
  refine ⟨by simp [angularBreakpoints], by simp [angularBreakpoints], ?_, ?_⟩
  · intro e he
    simp only [angularBreakpoints, Finset.mem_insert, Set.Finite.mem_toFinset] at he
    rcases he with rfl | rfl | he
    · exact ⟨le_rfl, hAB⟩
    · exact ⟨hAB, le_rfl⟩
    · exact ⟨he.2.1.le, he.2.2.le⟩
  · intro e he
    change e ∈ angularBreakpoints A B inside hfinite
    simp only [angularBreakpoints, Finset.mem_insert, Set.Finite.mem_toFinset]
    exact Or.inr (Or.inr he)

open CircularExhaustion

lemma arcParam_eq_circleMap (c : ℂ) (R : ℝ) : arcParam c R = circleMap c R := rfl

lemma arcParam_dist_center (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    dist (arcParam c R t) c = R := by
  exact mem_sphere.mp (circleMap_mem_sphere c hR t)

lemma continuous_arcParam (c : ℂ) (R : ℝ) : Continuous (arcParam c R) :=
  continuous_circleMap c R

lemma arcParam_injOn_zero_two_pi (c : ℂ) {R : ℝ} (hR : 0 < R) :
    InjOn (arcParam c R) (Ioo 0 (2 * Real.pi)) := by
  exact (injOn_circleMap_of_abs_sub_le' hR.ne' (by simp : 2 * Real.pi - 0 ≤
    2 * Real.pi)).mono Ioo_subset_Ico_self

/-- Even coincident centers cause no exceptional angular continuum: membership
in a concentric disk is constant on the whole test circle. -/
lemma finite_angular_frontier_ball (c d : ℂ) {R : ℝ} (hR : 0 < R) (S : ℝ) :
    (frontier ((arcParam c R) ⁻¹' ball d S) ∩ Ioo 0 (2 * Real.pi)).Finite := by
  by_cases hcd : c = d
  · subst d
    have heq : (arcParam c R) ⁻¹' ball c S = if R < S then univ else ∅ := by
      ext t
      simp only [mem_preimage, mem_ball, arcParam_dist_center c hR.le]
      split_ifs with h <;> simp [h]
    rw [heq]
    split_ifs <;> simp
  · have himage : ((arcParam c R) ''
        (frontier ((arcParam c R) ⁻¹' ball d S) ∩ Ioo 0 (2 * Real.pi))).Finite := by
      apply (D12Complex.FiniteCircularArcs.finite_circle_intersection c d R S hcd).subset
      rintro z ⟨t, ht, rfl⟩
      refine ⟨arcParam_dist_center c hR.le t, ?_⟩
      exact mem_sphere.mp (frontier_ball_subset_sphere
        ((continuous_arcParam c R).frontier_preimage_subset (ball d S) ht.1))
    exact himage.of_finite_image
      ((arcParam_injOn_zero_two_pi c hR).mono inter_subset_right)

/-- The angular part of any positive-radius circle inside an actual finite
union of disks has finite frontier in `(0, 2*pi)`. No general-position or
smallness assumption is used for this partition statement. -/
theorem finite_angular_frontier_diskUnion (s : Finset ℂ) (r : ℂ → ℝ)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (frontier ((arcParam c R) ⁻¹' diskUnion s r) ∩ Ioo 0 (2 * Real.pi)).Finite := by
  classical
  have hfinite : (⋃ d ∈ s,
      frontier ((arcParam c R) ⁻¹' ball d (r d)) ∩ Ioo 0 (2 * Real.pi)).Finite := by
    apply s.finite_toSet.biUnion
    intro d hd
    exact finite_angular_frontier_ball c d hR (r d)
  apply hfinite.subset
  intro t ht
  have heq : (arcParam c R) ⁻¹' diskUnion s r =
      ⋃ d ∈ s, (arcParam c R) ⁻¹' ball d (r d) := by
    simp only [diskUnion, preimage_iUnion]
  rw [heq] at ht
  obtain ⟨d, hd, htd⟩ := mem_iUnion₂.mp
    (s.frontier_biUnion_subset (fun d => (arcParam c R) ⁻¹' ball d (r d)) ht.1)
  exact mem_iUnion₂.mpr ⟨d, hd, htd, ht.2⟩

lemma measurableSet_angular_diskUnion (s : Finset ℂ) (r : ℂ → ℝ)
    (c : ℂ) (R : ℝ) : MeasurableSet ((arcParam c R) ⁻¹' diskUnion s r) :=
  ((diskUnion_open s r).preimage (continuous_arcParam c R)).measurableSet

/-- Exact deleting-circle angular partition and zero-extension additivity for an
arbitrary finite union of open disks. The finite set `E` contains all endpoints;
`pieces` consists of literal pairs of consecutive angles in `[0, 2*pi]`.
The integral statement applies, in particular, to every integrable periodic
angular function. -/
theorem diskUnion_circle_angular_partition (s : Finset ℂ) (r : ℂ → ℝ)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ (E : Finset ℝ) (pieces : Finset (ℝ × ℝ)),
      (∀ p ∈ pieces, p.1 ∈ E ∧ p.2 ∈ E ∧
        0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 2 * Real.pi) ∧
      Set.Pairwise (↑pieces : Set (ℝ × ℝ))
        (fun p q => Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2)) ∧
      (∀ p ∈ pieces, ∀ t ∈ Ioo p.1 p.2,
        arcParam c R t ∈ diskUnion s r) ∧
      (∀ t ∈ Ioo 0 (2 * Real.pi), t ∉ E →
        (arcParam c R t ∈ diskUnion s r ↔
          ∃ p ∈ pieces, t ∈ Ioo p.1 p.2)) ∧
      (∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 (2 * Real.pi) →
        (∑ p ∈ pieces, ∫ t in p.1..p.2, f t) =
          ∫ t in (0 : ℝ)..(2 * Real.pi),
            ((arcParam c R) ⁻¹' diskUnion s r).indicator f t) := by
  let inside := (arcParam c R) ⁻¹' diskUnion s r
  have hfinite : (frontier inside ∩ Ioo 0 (2 * Real.pi)).Finite :=
    finite_angular_frontier_diskUnion s r c hR
  let E := angularBreakpoints 0 (2 * Real.pi) inside hfinite
  let pieces := selectedAngularCells E inside
  have hAB : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  obtain ⟨hA, hB, hbound, hfrontier⟩ :=
    angularBreakpoints_properties hAB inside hfinite
  change 0 ∈ E at hA
  change 2 * Real.pi ∈ E at hB
  change ∀ e ∈ E, e ∈ Icc 0 (2 * Real.pi) at hbound
  change frontier inside ∩ Ioo 0 (2 * Real.pi) ⊆ (↑E : Set ℝ) at hfrontier
  refine ⟨E, pieces, ?_, selectedAngularCells_pairwise_disjoint E inside,
    ?_, ?_, ?_⟩
  · intro p hp
    have hm := mem_angularCells.mp (mem_selectedAngularCells.mp hp).1
    exact ⟨hm.1, hm.2.1, selectedAngularCells_bounds hbound hp⟩
  · intro p hp t ht
    exact selectedAngularCells_subset_inside hbound inside hfrontier hp ht
  · intro t ht htE
    exact selectedAngularCells_coverage hA hB hbound inside hfrontier ht htE
  · intro f hf
    apply selectedAngularCells_integral hAB hA hB hbound inside
      (measurableSet_angular_diskUnion s r c R) hfrontier f
    intro p hp
    have hb := selectedAngularCells_bounds hbound hp
    apply hf.mono_set
    rw [uIcc_of_le hb.2.1.le, uIcc_of_le hAB]
    exact Icc_subset_Icc hb.1 hb.2.2

/-- Distinct cells on the same injective parametrization have disjoint open
images. Cells on different curves have disjoint images once every intersection
parameter was inserted among their breakpoints. -/
theorem angularCells_open_images_disjoint
    {X ι : Type*} (curves : Finset ι) (γ : ι → ℝ → X)
    (endpoints : ι → Finset ℝ) (A B : ℝ)
    (hbound : ∀ i ∈ curves, ∀ e ∈ endpoints i, e ∈ Icc A B)
    (hinj : ∀ i ∈ curves, InjOn (γ i) (Ioo A B))
    (hcross : ∀ i ∈ curves, ∀ j ∈ curves, i ≠ j →
      ∀ t ∈ Ioo A B, γ i t ∈ range (γ j) → t ∈ endpoints i)
    {i j : ι} (hi : i ∈ curves) (hj : j ∈ curves)
    {p q : ℝ × ℝ} (hp : p ∈ angularCells (endpoints i))
    (hq : q ∈ angularCells (endpoints j)) (hne : (i, p) ≠ (j, q)) :
    Disjoint (γ i '' Ioo p.1 p.2) (γ j '' Ioo q.1 q.2) := by
  have hglobal : ∀ k ∈ curves, ∀ u ∈ angularCells (endpoints k),
      Ioo u.1 u.2 ⊆ Ioo A B := by
    intro k hk u hu t ht
    have hm := mem_angularCells.mp hu
    exact ⟨(hbound k hk u.1 hm.1).1.trans_lt ht.1,
      ht.2.trans_le (hbound k hk u.2 hm.2.1).2⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨t, htp, htz⟩ ⟨u, huq, huz⟩
  by_cases hij : i = j
  · subst j
    have htu : t = u := hinj i hi (hglobal i hi p hp htp)
      (hglobal i hi q hq huq) (htz.trans huz.symm)
    have hpq : p ≠ q := fun h => hne (by simp [h])
    exact Set.disjoint_left.mp (angularCells_pairwise_disjoint (endpoints i) hp hq hpq)
      htp (htu.symm ▸ huq)
  · exact angularCells_avoid_breakpoints hp htp
      (hcross i hi j hj hij t (hglobal i hi p hp htp) ⟨u, huz.trans htz.symm⟩)

/-- A finite relatively open remainder in a set without isolated points is
empty. The closed set `A` may be a finite union of closed arc images. -/
theorem eq_of_closed_subset_finite_sdiff_no_isolated
    {X : Type*} [TopologicalSpace X] [T1Space X] {F A : Set X}
    (hAF : A ⊆ F) (hA : IsClosed A) (hfinite : (F \ A).Finite)
    (hnoisolated : ∀ x ∈ F, x ∈ closure (F \ {x})) : A = F := by
  apply Subset.antisymm hAF
  intro x hx
  by_contra hxA
  let B := A ∪ ((F \ A) \ {x})
  have hB : IsClosed B := hA.union (hfinite.subset sdiff_subset).isClosed
  have hsub : F \ {x} ⊆ B := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · exact Or.inr ⟨⟨hy.1, hyA⟩, hy.2⟩
  have hxB : x ∈ B := hB.closure_eq ▸ closure_mono hsub (hnoisolated x hx)
  rcases hxB with h | h
  · exact hxA h
  · exact h.2 rfl

/-- Continuity and closedness add both endpoints of every positive-length arc. -/
theorem closed_arc_image_subset_of_open_arc_image_subset
    {X : Type*} [TopologicalSpace X] {γ : ℝ → X} (hγ : Continuous γ)
    {F : Set X} (hF : IsClosed F) {a b : ℝ} (hab : a < b)
    (hopen : γ '' Ioo a b ⊆ F) : γ '' Icc a b ⊆ F := by
  have hmap : MapsTo γ (Ioo a b) F := image_subset_iff.mp hopen
  have hc := hmap.closure hγ
  rw [closure_Ioo hab.ne, hF.closure_eq] at hc
  exact image_subset_iff.mpr hc

/-- Given finite parameter partitions on finitely many curves, every uncovered
point lies in the finite image of their endpoint sets. -/
theorem finite_uncovered_by_closed_arcs
    {X ι : Type*} [TopologicalSpace X]
    (curves : Finset ι) (γ : ι → ℝ → X) (endpoints : ι → Finset ℝ)
    (pieces : ι → Finset (ℝ × ℝ)) (A B : ℝ) (F : Set X)
    (hrep : ∀ z ∈ F, ∃ i ∈ curves, ∃ t ∈ Icc A B, γ i t = z)
    (hends : ∀ i ∈ curves, A ∈ endpoints i ∧ B ∈ endpoints i)
    (hcover : ∀ i ∈ curves, ∀ t ∈ Ioo A B, t ∉ endpoints i → γ i t ∈ F →
      ∃ p ∈ pieces i, t ∈ Ioo p.1 p.2) :
    (F \ ⋃ i ∈ curves, ⋃ p ∈ pieces i, γ i '' Icc p.1 p.2).Finite := by
  have hf : (⋃ i ∈ curves, γ i '' (↑(endpoints i) : Set ℝ)).Finite := by
    apply curves.finite_toSet.biUnion
    intro i hi
    exact (endpoints i).finite_toSet.image (γ i)
  apply hf.subset
  rintro z ⟨hzF, hznot⟩
  obtain ⟨i, hi, t, ht, rfl⟩ := hrep z hzF
  by_cases htE : t ∈ endpoints i
  · exact mem_iUnion₂.mpr ⟨i, hi, mem_image_of_mem (γ i) htE⟩
  · have htA : A < t := lt_of_le_of_ne ht.1 (fun h => htE (h ▸ (hends i hi).1))
    have htB : t < B := lt_of_le_of_ne ht.2 (fun h => htE (h.symm ▸ (hends i hi).2))
    obtain ⟨p, hp, htp⟩ := hcover i hi t ⟨htA, htB⟩ htE hzF
    exact False.elim (hznot (mem_iUnion₂.mpr ⟨i, hi,
      mem_iUnion₂.mpr ⟨p, hp, mem_image_of_mem (γ i) ⟨htp.1.le, htp.2.le⟩⟩⟩))

/-- Closed selected arc images cover the entire closed set once their open
images cover outside finite endpoint sets and the set has no isolated points.
This is the final finite-remainder step in the circular arrangement argument. -/
theorem closed_arcs_cover_of_finite_angular_partition
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (curves : Finset ι) (γ : ι → ℝ → X) (endpoints : ι → Finset ℝ)
    (pieces : ι → Finset (ℝ × ℝ)) (A B : ℝ) (F : Set X)
    (hγ : ∀ i ∈ curves, Continuous (γ i)) (hF : IsClosed F)
    (hrep : ∀ z ∈ F, ∃ i ∈ curves, ∃ t ∈ Icc A B, γ i t = z)
    (hends : ∀ i ∈ curves, A ∈ endpoints i ∧ B ∈ endpoints i)
    (hlength : ∀ i ∈ curves, ∀ p ∈ pieces i, p.1 < p.2)
    (hselected : ∀ i ∈ curves, ∀ p ∈ pieces i, γ i '' Ioo p.1 p.2 ⊆ F)
    (hcover : ∀ i ∈ curves, ∀ t ∈ Ioo A B, t ∉ endpoints i → γ i t ∈ F →
      ∃ p ∈ pieces i, t ∈ Ioo p.1 p.2)
    (hnoisolated : ∀ z ∈ F, z ∈ closure (F \ {z})) :
    F = ⋃ i ∈ curves, ⋃ p ∈ pieces i, γ i '' Icc p.1 p.2 := by
  have hclosed : IsClosed (⋃ i ∈ curves, ⋃ p ∈ pieces i,
      γ i '' Icc p.1 p.2) := by
    apply curves.finite_toSet.isClosed_biUnion
    intro i hi
    apply (pieces i).finite_toSet.isClosed_biUnion
    intro p hp
    exact (isCompact_Icc.image (hγ i hi)).isClosed
  have hsubset : (⋃ i ∈ curves, ⋃ p ∈ pieces i,
      γ i '' Icc p.1 p.2) ⊆ F := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨p, hp, hz⟩ := mem_iUnion₂.mp hz
    exact closed_arc_image_subset_of_open_arc_image_subset (hγ i hi) hF
      (hlength i hi p hp) (hselected i hi p hp) hz
  exact (eq_of_closed_subset_finite_sdiff_no_isolated hsubset hclosed
    (finite_uncovered_by_closed_arcs curves γ endpoints pieces A B F hrep hends hcover)
    hnoisolated).symm

/-- The preimages of intersections of distinct circles are finite in a closed
angular period, including both seam endpoints. Concentric unequal circles
have no common points. -/
lemma finite_circle_pair_angles (c d : ℂ) (R S : ℝ) (hR : 0 < R)
    (hneq : c ≠ d ∨ R ≠ S) :
    {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam c R t ∈ sphere d S}.Finite := by
  have hfinite : {z : ℂ | dist z c = R ∧ dist z d = S}.Finite := by
    rcases hneq with hcd | hRS
    · exact FiniteCircularArcs.finite_circle_intersection c d R S hcd
    · by_cases hcd : c = d
      · subst d
        have he : {z : ℂ | dist z c = R ∧ dist z c = S} = ∅ := by
          ext z
          simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
          rintro ⟨hzR,hzS⟩
          exact hRS (hzR.symm.trans hzS)
        rw [he]
        exact finite_empty
      · exact FiniteCircularArcs.finite_circle_intersection c d R S hcd
  have hinterior : {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam c R t ∈ sphere d S}.Finite := by
    apply Set.Finite.of_injOn (f := CircularExhaustion.arcParam c R)
      (t := {z : ℂ | dist z c = R ∧ dist z d = S}) ?_
      ((arcParam_injOn_zero_two_pi c hR).mono (fun _ ht => ht.1)) hfinite
    intro t ht
    exact ⟨arcParam_dist_center c hR.le t,mem_sphere.mp ht.2⟩
  apply (hinterior.union (Set.toFinite ({0,2 * Real.pi} : Set ℝ))).subset
  intro t ht
  by_cases h0 : t = 0
  · exact Or.inr (by simp [h0])
  by_cases hT : t = 2 * Real.pi
  · exact Or.inr (by simp [hT])
  · exact Or.inl ⟨⟨lt_of_le_of_ne ht.1.1 (Ne.symm h0),lt_of_le_of_ne ht.1.2 hT⟩,ht.2⟩

/-- A finite distinct-circle family with finite angular boundary data and no
isolated frontier points admits an exact finite disjoint closed-arc display.
All angular cells and endpoint sets are explicit finite constructions. -/
theorem finite_circle_display_from_angular_frontiers
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (R : ι → ℝ)
    (hR : ∀ i, 0 < R i)
    (hdistinct : ∀ i j, i ≠ j → c i ≠ c j ∨ R i ≠ R j)
    (F : Set ℂ) (hF : IsClosed F) (hcircles : F ⊆ ⋃ i, sphere (c i) (R i))
    (hnoisolated : ∀ z ∈ F, z ∈ closure (F \ {z}))
    (hfrontiers : ∀ i,
      (frontier ((arcParam (c i) (R i)) ⁻¹' F) ∩ Ioo 0 (2 * Real.pi)).Finite) :
    ∃ (endpoints : ι → Finset ℝ) (pieces : ι → Finset (ℝ × ℝ)),
      (∀ i, pieces i = selectedAngularCells (endpoints i)
        ((arcParam (c i) (R i)) ⁻¹' F)) ∧
      (∀ i, 0 ∈ endpoints i ∧ 2 * Real.pi ∈ endpoints i ∧
        ∀ e ∈ endpoints i, e ∈ Icc 0 (2 * Real.pi)) ∧
      (∀ i, ∀ p ∈ pieces i, p.1 ∈ endpoints i ∧ p.2 ∈ endpoints i ∧
        0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 2 * Real.pi) ∧
      (∀ i, ∀ p ∈ pieces i, arcParam (c i) (R i) '' Ioo p.1 p.2 ⊆ F) ∧
      F = (⋃ i, ⋃ p ∈ pieces i, arcParam (c i) (R i) '' Icc p.1 p.2) ∧
      (∀ i j, ∀ p ∈ pieces i, ∀ q ∈ pieces j, (i, p) ≠ (j, q) →
        Disjoint (arcParam (c i) (R i) '' Ioo p.1 p.2)
          (arcParam (c j) (R j) '' Ioo q.1 q.2)) ∧
      (∀ i, frontier ((arcParam (c i) (R i)) ⁻¹' F) ∩ Ioo 0 (2 * Real.pi) ⊆
        (↑(endpoints i) : Set ℝ)) ∧
      (∀ i j, i ≠ j → ∀ t ∈ Icc 0 (2 * Real.pi),
        arcParam (c i) (R i) t ∈ sphere (c j) (R j) → t ∈ endpoints i) ∧
      (∀ i, ∀ t ∈ Ioo 0 (2 * Real.pi), t ∉ endpoints i →
        (arcParam (c i) (R i) t ∈ F ↔ ∃ p ∈ pieces i, t ∈ Ioo p.1 p.2)) := by
  classical
  let inside : ι → Set ℝ := fun i => (arcParam (c i) (R i)) ⁻¹' F
  let crossings : ι → Set ℝ := fun i => ⋃ j ∈ Finset.univ.erase i,
    {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧ arcParam (c i) (R i) t ∈ sphere (c j) (R j)}
  have hcrossfinite : ∀ i, (crossings i).Finite := by
    intro i
    apply (Finset.univ.erase i).finite_toSet.biUnion
    intro j hj
    exact finite_circle_pair_angles (c i) (c j) (R i) (R j) (hR i)
      (hdistinct i j (Finset.mem_erase.mp hj).1.symm)
  let bad : ι → Set ℝ := fun i => (frontier (inside i) ∩ Ioo 0 (2 * Real.pi)) ∪ crossings i
  have hbadfinite : ∀ i, (bad i).Finite := fun i => (hfrontiers i).union (hcrossfinite i)
  let endpoints : ι → Finset ℝ := fun i => insert 0 (insert (2 * Real.pi) (hbadfinite i).toFinset)
  let pieces : ι → Finset (ℝ × ℝ) := fun i => selectedAngularCells (endpoints i) (inside i)
  have hends : ∀ i, 0 ∈ endpoints i ∧ 2 * Real.pi ∈ endpoints i := by
    intro i
    simp [endpoints]
  have hbounds : ∀ i, ∀ e ∈ endpoints i, e ∈ Icc 0 (2 * Real.pi) := by
    intro i e he
    simp only [endpoints, Finset.mem_insert, Set.Finite.mem_toFinset] at he
    rcases he with rfl | rfl | he
    · exact ⟨le_rfl, by positivity⟩
    · exact ⟨by positivity, le_rfl⟩
    · rcases he with he | he
      · exact ⟨he.2.1.le, he.2.2.le⟩
      · obtain ⟨j, hj, ht⟩ := mem_iUnion₂.mp he
        exact ht.1
  have hbadmem : ∀ i, bad i ⊆ (↑(endpoints i) : Set ℝ) := by
    intro i t ht
    change t ∈ endpoints i
    simp only [endpoints, Finset.mem_insert, Set.Finite.mem_toFinset]
    exact Or.inr (Or.inr ht)
  have hfrontier : ∀ i, frontier (inside i) ∩ Ioo 0 (2 * Real.pi) ⊆
      (↑(endpoints i) : Set ℝ) := fun i t ht => hbadmem i (Or.inl ht)
  have hcrossmem : ∀ i j, i ≠ j → ∀ t ∈ Icc 0 (2 * Real.pi),
      arcParam (c i) (R i) t ∈ sphere (c j) (R j) → t ∈ endpoints i := by
    intro i j hij t ht hz
    apply hbadmem i
    apply Or.inr
    exact mem_iUnion₂.mpr ⟨j,
      Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩, ht, hz⟩
  have hcoverage : ∀ i, ∀ t ∈ Ioo 0 (2 * Real.pi), t ∉ endpoints i →
      (t ∈ inside i ↔ ∃ p ∈ pieces i, t ∈ Ioo p.1 p.2) := by
    intro i t ht htE
    exact selectedAngularCells_coverage (hends i).1 (hends i).2
      (hbounds i) (inside i) (hfrontier i) ht htE
  have hpiecebound : ∀ i, ∀ p ∈ pieces i,
      0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 2 * Real.pi := by
    intro i p hp
    exact selectedAngularCells_bounds (hbounds i) hp
  have hselected : ∀ i, ∀ p ∈ pieces i, arcParam (c i) (R i) '' Ioo p.1 p.2 ⊆ F := by
    intro i p hp z hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact selectedAngularCells_subset_inside (hbounds i) (inside i) (hfrontier i) hp ht
  have hrep : ∀ z ∈ F, ∃ i ∈ (Finset.univ : Finset ι),
      ∃ t ∈ Icc 0 (2 * Real.pi), arcParam (c i) (R i) t = z := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcircles hz)
    have himage : z ∈ arcParam (c i) (R i) '' Ioc 0 (2 * Real.pi) := by
      have heq : arcParam (c i) (R i) '' Ioc 0 (2 * Real.pi) = sphere (c i) (R i) := by
        simpa only [arcParam_eq_circleMap, abs_of_pos (hR i)] using image_circleMap_Ioc (c i) (R i)
      exact heq.symm ▸ hi
    obtain ⟨t, ht, htz⟩ := himage
    exact ⟨i, Finset.mem_univ i, t, ⟨ht.1.le, ht.2⟩, htz⟩
  have hcoverall : F = ⋃ i, ⋃ p ∈ pieces i,
      arcParam (c i) (R i) '' Icc p.1 p.2 := by
    simpa only [Finset.mem_univ, iUnion_true] using
      closed_arcs_cover_of_finite_angular_partition Finset.univ
        (fun i => arcParam (c i) (R i)) endpoints pieces 0 (2 * Real.pi) F
        (fun i _ => continuous_arcParam (c i) (R i)) hF hrep
        (fun i _ => hends i) (fun i _ p hp => (hpiecebound i p hp).2.1)
        (fun i _ => hselected i)
        (fun i _ t ht htE htF => (hcoverage i t ht htE).mp htF) hnoisolated
  refine ⟨endpoints, pieces, fun _ => rfl, ?_, ?_, hselected, hcoverall, ?_,
    hfrontier, hcrossmem, hcoverage⟩
  · exact fun i => ⟨(hends i).1, (hends i).2, hbounds i⟩
  · intro i p hp
    have hm := mem_angularCells.mp (mem_selectedAngularCells.mp hp).1
    exact ⟨hm.1, hm.2.1, hpiecebound i p hp⟩
  · intro i j p hp q hq hne
    apply angularCells_open_images_disjoint Finset.univ
      (fun k => arcParam (c k) (R k)) endpoints 0 (2 * Real.pi)
      (fun k _ => hbounds k) (fun k _ => arcParam_injOn_zero_two_pi (c k) (hR k))
      ?_ (Finset.mem_univ i) (Finset.mem_univ j)
      (mem_selectedAngularCells.mp hp).1 (mem_selectedAngularCells.mp hq).1 hne
    intro k hk l hl hkl t ht htrange
    obtain ⟨u, hut⟩ := htrange
    apply hbadmem k
    apply Or.inr
    apply mem_iUnion₂.mpr
    refine ⟨l, Finset.mem_erase.mpr ⟨hkl.symm, Finset.mem_univ l⟩, ?_⟩
    refine ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
    rw [← hut]
    exact circleMap_mem_sphere (c l) (hR l).le u

end D12Complex.CircularCutGeometry


noncomputable section
open Set Metric MeasureTheory
open scoped Topology Interval
namespace D12Complex.CircularCutGeometry

lemma circularCut_isOpen {D : Set ℂ} (hD : IsOpen D)
    (centers : Finset ℂ) (q : ℂ → ℝ) : IsOpen (circularCut D centers q) := by
  exact hD.sdiff (centers.finite_toSet.isClosed_biUnion (fun _ _ => isClosed_closedBall))

lemma circularCut_isBounded {D : Set ℂ} (hD : Bornology.IsBounded D)
    (centers : Finset ℂ) (q : ℂ → ℝ) : Bornology.IsBounded (circularCut D centers q) :=
  hD.subset sdiff_subset

lemma circularCut_empty (D : Set ℂ) (q : ℂ → ℝ) : circularCut D ∅ q = D := by
  simp [circularCut]

lemma mem_circularCut {D : Set ℂ} {centers : Finset ℂ} {q : ℂ → ℝ} {z : ℂ} :
    z ∈ circularCut D centers q ↔ z ∈ D ∧ ∀ c ∈ centers, q c < dist z c := by
  simp [circularCut]

lemma circularCut_closure_exterior {D : Set ℂ} {centers : Finset ℂ} {q : ℂ → ℝ}
    {z : ℂ} (hz : z ∈ closure (circularCut D centers q)) :
    z ∈ closure D ∧ ∀ c ∈ centers, q c ≤ dist z c := by
  refine ⟨closure_mono sdiff_subset hz, ?_⟩
  intro c hc
  have hsub : circularCut D centers q ⊆ {w : ℂ | q c ≤ dist w c} := by
    intro w hw
    exact (mem_circularCut.mp hw).2 c hc |>.le
  have hclosed : IsClosed {w : ℂ | q c ≤ dist w c} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  exact closure_minimal hsub hclosed hz

lemma frontier_circularCut_subset (D : Set ℂ) (centers : Finset ℂ) (q : ℂ → ℝ) :
    frontier (circularCut D centers q) ⊆
      frontier D ∪ ⋃ c ∈ centers, sphere c (q c) := by
  intro z hz
  have h := frontier_inter_subset D (⋃ c ∈ centers, closedBall c (q c))ᶜ hz
  rcases h with h | h
  · exact Or.inl h.1
  · right
    have hfront : z ∈ frontier (⋃ c ∈ centers, closedBall c (q c)) := by
      simpa only [frontier_compl] using h.2
    obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp
      (centers.frontier_biUnion_subset (fun c => closedBall c (q c)) hfront)
    exact mem_iUnion₂.mpr ⟨c,hc,frontier_closedBall_subset_sphere hzc⟩

lemma frontier_circularCut_away {D : Set ℂ} {centers : Finset ℂ} {q : ℂ → ℝ}
    {z : ℂ} (hz : z ∉ ⋃ c ∈ centers, closedBall c (q c)) :
    z ∈ frontier (circularCut D centers q) ↔ z ∈ frontier D := by
  let W : Set ℂ := (⋃ c ∈ centers, closedBall c (q c))ᶜ
  have hW : IsOpen W := (centers.finite_toSet.isClosed_biUnion (fun _ _ => isClosed_closedBall)).isOpen_compl
  have heq := frontier_inter_open_inter (s := D) hW
  constructor
  · intro h
    have : z ∈ frontier (D ∩ W) ∩ W := ⟨h,hz⟩
    rw [heq] at this
    exact this.1
  · intro h
    have : z ∈ frontier D ∩ W := ⟨h,hz⟩
    rw [← heq] at this
    exact this.1

lemma circularCut_one_exterior (D : Set ℂ) (centers : Finset ℂ) (q : ℂ → ℝ)
    {c : ℂ} (hc : c ∈ centers) :
    circularCut D centers q = (closedBall c (q c))ᶜ ∩
      (D \ (⋃ d ∈ centers.erase c, closedBall d (q d))) := by
  classical
  ext z
  simp only [circularCut, mem_sdiff, mem_iUnion, mem_closedBall, not_exists,
    mem_inter_iff, mem_compl_iff, Finset.mem_erase]
  constructor
  · rintro ⟨hz,h⟩
    exact ⟨h c hc, hz, fun d hd => h d hd.2⟩
  · rintro ⟨hz,hD,h⟩
    refine ⟨hD, ?_⟩
    intro d hd
    by_cases hdc : d = c
    · simpa [hdc] using hz
    · exact h d ⟨hdc,hd⟩

lemma deleting_sphere_frontier {D : Set ℂ} (hD : IsOpen D)
    {centers : Finset ℂ} {q : ℂ → ℝ}
    (hd : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {c : ℂ} (hc : c ∈ centers) (hq : 0 < q c) :
    sphere c (q c) ∩ D ⊆ frontier (circularCut D centers q) := by
  classical
  intro z hz
  let W := D \ (⋃ d ∈ centers.erase c, closedBall d (q d))
  have hW : IsOpen W := hD.sdiff ((centers.erase c).finite_toSet.isClosed_biUnion
    (fun _ _ => isClosed_closedBall))
  have hzW : z ∈ W := by
    refine ⟨hz.2, ?_⟩
    intro hm
    obtain ⟨d,hdmem,hzd⟩ := mem_iUnion₂.mp hm
    exact Set.disjoint_left.mp (hd c hc d (Finset.mem_erase.mp hdmem).2
      (Finset.mem_erase.mp hdmem).1.symm) (sphere_subset_closedBall hz.1) hzd
  have hfront : z ∈ frontier (closedBall c (q c))ᶜ := by
    simpa only [frontier_compl, frontier_closedBall c hq.ne'] using hz.1
  have hh : z ∈ frontier ((closedBall c (q c))ᶜ) ∩ W := ⟨hfront,hzW⟩
  rw [← frontier_inter_open_inter hW] at hh
  rw [circularCut_one_exterior D centers q hc]
  exact hh.1

end D12Complex.CircularCutGeometry

noncomputable section
open Set Metric
open scoped Topology
namespace D12Complex.CircularCutGeometry

lemma arcParam_mem_sphere (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    CircularExhaustion.arcParam c R t ∈ sphere c R :=
  circleMap_mem_sphere c hR t

lemma arcParam_continuous (c : ℂ) (R : ℝ) :
    Continuous (CircularExhaustion.arcParam c R) :=
  FiniteCircularArcs.continuous_circle c R

lemma arcParam_injOn_period (c : ℂ) {R : ℝ} (hR : 0 < R) :
    InjOn (CircularExhaustion.arcParam c R) (Ioo 0 (2 * Real.pi)) := by
  exact (FiniteCircularArcs.circular_parametrization c R 0 (2 * Real.pi)
    hR (by positivity) (by linarith)).2.2

/-- The preimages of intersections of distinct circles are finite in a closed
angular period, including both seam endpoints. Concentric unequal circles
have no common points. -/
lemma finite_angular_circle_intersections (c d : ℂ) (R S : ℝ) (hR : 0 < R)
    (hneq : c ≠ d ∨ R ≠ S) :
    {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam c R t ∈ sphere d S}.Finite := by
  have hfinite : {z : ℂ | dist z c = R ∧ dist z d = S}.Finite := by
    rcases hneq with hcd | hRS
    · exact FiniteCircularArcs.finite_circle_intersection c d R S hcd
    · by_cases hcd : c = d
      · subst d
        have he : {z : ℂ | dist z c = R ∧ dist z c = S} = ∅ := by
          ext z
          simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]
          rintro ⟨hzR,hzS⟩
          exact hRS (hzR.symm.trans hzS)
        rw [he]
        exact finite_empty
      · exact FiniteCircularArcs.finite_circle_intersection c d R S hcd
  have hinterior : {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam c R t ∈ sphere d S}.Finite := by
    apply Set.Finite.of_injOn (f := CircularExhaustion.arcParam c R)
      (t := {z : ℂ | dist z c = R ∧ dist z d = S}) ?_
      ((arcParam_injOn_period c hR).mono (fun _ ht => ht.1)) hfinite
    intro t ht
    exact ⟨mem_sphere.mp (arcParam_mem_sphere c hR.le t),mem_sphere.mp ht.2⟩
  apply (hinterior.union (Set.toFinite ({0,2 * Real.pi} : Set ℝ))).subset
  intro t ht
  by_cases h0 : t = 0
  · exact Or.inr (by simp [h0])
  by_cases hT : t = 2 * Real.pi
  · exact Or.inr (by simp [hT])
  · exact Or.inl ⟨⟨lt_of_le_of_ne ht.1.1 (Ne.symm h0),lt_of_le_of_ne ht.1.2 hT⟩,ht.2⟩

lemma finite_frontier_inter {α : Type*} [TopologicalSpace α] {A B : Set α}
    (hA : (frontier A).Finite) (hB : (frontier B).Finite) :
    (frontier (A ∩ B)).Finite := by
  apply (hA.union hB).subset
  intro z hz
  rcases frontier_inter_subset A B hz with h | h
  · exact Or.inl h.1
  · exact Or.inr h.2

lemma finite_frontier_sdiff {α : Type*} [TopologicalSpace α] {A B : Set α}
    (hA : (frontier A).Finite) (hB : (frontier B).Finite) :
    (frontier (A \ B)).Finite := by
  rw [sdiff_eq_compl_inter,inter_comm]
  apply finite_frontier_inter hA
  simpa only [frontier_compl] using hB

lemma finite_frontier_biUnion {α ι : Type*} [TopologicalSpace α]
    (s : Finset ι) (A : ι → Set α) (hA : ∀ i ∈ s, (frontier (A i)).Finite) :
    (frontier (⋃ i ∈ s, A i)).Finite := by
  exact (s.finite_toSet.biUnion hA).subset (s.frontier_biUnion_subset A)

lemma finite_frontier_Ioo_period : (frontier (Ioo (0 : ℝ) (2 * Real.pi))).Finite := by
  rw [frontier_Ioo (by positivity : (0 : ℝ) < 2 * Real.pi)]
  exact Set.toFinite _

/-- A clipped continuous preimage has finite frontier once its crossings of
the target frontier in the closed period are finite. -/
lemma finite_frontier_clipped_preimage {A : Set ℂ} {c : ℂ} {R : ℝ}
    (hcross : {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam c R t ∈ frontier A}.Finite) :
    (frontier (Ioo 0 (2 * Real.pi) ∩
      CircularExhaustion.arcParam c R ⁻¹' A)).Finite := by
  apply (finite_frontier_Ioo_period.union hcross).subset
  intro t ht
  rcases frontier_inter_subset _ _ ht with h | h
  · exact Or.inl h.1
  · apply Or.inr
    refine ⟨?_,(arcParam_continuous c R).frontier_preimage_subset A h.2⟩
    simpa only [closure_Ioo (by positivity : (0 : ℝ) ≠ 2 * Real.pi)] using h.1

lemma finite_frontier_angular_ball (c d : ℂ) (R S : ℝ) (hR : 0 < R)
    (hneq : c ≠ d ∨ R ≠ S) :
    (frontier (Ioo 0 (2 * Real.pi) ∩
      CircularExhaustion.arcParam c R ⁻¹' ball d S)).Finite := by
  apply finite_frontier_clipped_preimage
  exact (finite_angular_circle_intersections c d R S hR hneq).subset
    (fun _ ht => ⟨ht.1,frontier_ball_subset_sphere ht.2⟩)

lemma finite_frontier_angular_closedBall (c d : ℂ) (R S : ℝ) (hR : 0 < R)
    (hneq : c ≠ d ∨ R ≠ S) :
    (frontier (Ioo 0 (2 * Real.pi) ∩
      CircularExhaustion.arcParam c R ⁻¹' closedBall d S)).Finite := by
  apply finite_frontier_clipped_preimage
  exact (finite_angular_circle_intersections c d R S hR hneq).subset
    (fun _ ht => ⟨ht.1,frontier_closedBall_subset_sphere ht.2⟩)

/-- The part of a deleting circle strictly inside the original disk union has
finite angular frontier, so a consecutive finite partition applies literally. -/
lemma finite_frontier_deleting_parameters (s : Finset ℂ) (r : ℂ → ℝ)
    (x : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hnt : ∀ c ∈ s, dist x c ≠ |Q - r c|) :
    (frontier {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam x Q t ∈ CircularExhaustion.diskUnion s r}).Finite := by
  have hneq : ∀ c ∈ s, x ≠ c ∨ Q ≠ r c := by
    intro c hc
    by_cases hxc : x = c
    · refine Or.inr ?_
      intro hQr
      apply hnt c hc
      simp [hxc,hQr]
    · exact Or.inl hxc
  have heq : {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam x Q t ∈ CircularExhaustion.diskUnion s r} =
      ⋃ c ∈ s, (Ioo 0 (2 * Real.pi) ∩ CircularExhaustion.arcParam x Q ⁻¹' ball c (r c)) := by
    ext t
    simp only [mem_ofPred_eq,CircularExhaustion.diskUnion,mem_iUnion,mem_inter_iff,mem_preimage]
    constructor
    · rintro ⟨ht,c,hc,hz⟩
      exact ⟨c,hc,ht,hz⟩
    · rintro ⟨c,hc,ht,hz⟩
      exact ⟨ht,c,hc,hz⟩
  rw [heq]
  exact finite_frontier_biUnion s _ (fun c hc => finite_frontier_angular_ball x c Q (r c) hQ (hneq c hc))

/-- On one original circle, discard the parts lying in another original disk
or in a closed deleting disk. The remaining angular set has finite frontier. -/
lemma finite_frontier_original_parameters (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (c : ℂ) (hR : 0 < r c)
    (hnt : ∀ x ∈ centers, dist x c ≠ |q x - r c|) :
    (frontier {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      (∀ d ∈ s.erase c, r d ≤ dist (CircularExhaustion.arcParam c (r c) t) d) ∧
      (∀ x ∈ centers, q x < dist (CircularExhaustion.arcParam c (r c) t) x)}).Finite := by
  classical
  let A := ⋃ d ∈ s.erase c,
    (Ioo 0 (2 * Real.pi) ∩ CircularExhaustion.arcParam c (r c) ⁻¹' ball d (r d))
  let B := ⋃ x ∈ centers,
    (Ioo 0 (2 * Real.pi) ∩ CircularExhaustion.arcParam c (r c) ⁻¹' closedBall x (q x))
  have hA : (frontier A).Finite := by
    apply finite_frontier_biUnion
    intro d hd
    exact finite_frontier_angular_ball c d (r c) (r d) hR
      (Or.inl (Finset.mem_erase.mp hd).1.symm)
  have hB : (frontier B).Finite := by
    apply finite_frontier_biUnion
    intro x hx
    apply finite_frontier_angular_closedBall c x (r c) (q x) hR
    by_cases hcx : c = x
    · refine Or.inr ?_
      intro heq
      apply hnt x hx
      rw [← heq, ← hcx,dist_self,sub_self,abs_zero]
    · exact Or.inl hcx
  have heq : {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      (∀ d ∈ s.erase c, r d ≤ dist (CircularExhaustion.arcParam c (r c) t) d) ∧
      (∀ x ∈ centers, q x < dist (CircularExhaustion.arcParam c (r c) t) x)} =
      (Ioo 0 (2 * Real.pi) \ A) \ B := by
    ext t
    simp only [mem_ofPred_eq,mem_sdiff,A,B,mem_iUnion,mem_inter_iff,mem_preimage,
      mem_ball,mem_closedBall,not_exists,not_and,not_lt,not_le]
    aesop
  rw [heq]
  exact finite_frontier_sdiff (finite_frontier_sdiff finite_frontier_Ioo_period hA) hB

end D12Complex.CircularCutGeometry

namespace D12Complex.CircularCutGeometry

/-- At a transverse circle crossing, both strict disk sides are literal
one-sided angular intervals. This supplies endpoint coverage by actual arcs. -/
lemma transverse_circle_angular_sides (c d : ℂ) (R S t : ℝ)
    (hS : 0 < S) (ht : dist (CircularExhaustion.arcParam c R t) d = S)
    (hcross : ((CircularExhaustion.arcParam c R t - c) *
      star (CircularExhaustion.arcParam c R t - d)).im ≠ 0) :
    let k := -2 * ((CircularExhaustion.arcParam c R t - c) *
      star (CircularExhaustion.arcParam c R t - d)).im
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, |u - t| < δ →
      (dist (CircularExhaustion.arcParam c R u) d < S ↔ k * (u - t) < 0) ∧
      (S < dist (CircularExhaustion.arcParam c R u) d ↔ 0 < k * (u - t)) := by
  dsimp only
  let f := fun u => Complex.normSq (CircularExhaustion.arcParam c R u - d) - S ^ 2
  let k := -2 * ((CircularExhaustion.arcParam c R t - c) *
    star (CircularExhaustion.arcParam c R t - d)).im
  have hderiv : HasDerivAt f k t := FiniteCircularArcs.circle_power_hasDerivAt c d R S t
  have hzero : f t = 0 := by
    dsimp [f]
    rw [Complex.normSq_eq_norm_sq,←dist_eq_norm,ht]
    ring
  have hk : k ≠ 0 := mul_ne_zero (by norm_num) hcross
  obtain ⟨δ₁,hδ₁,hside₁⟩ := FiniteCircularArcs.sign_near_simple_zero hderiv hzero hk
  obtain ⟨δ₂,hδ₂,hside₂⟩ := FiniteCircularArcs.sign_near_simple_zero hderiv.neg
    (by change -(f t) = 0; rw [hzero,neg_zero]) (neg_ne_zero.mpr hk)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_⟩
  intro u hu
  have hu₁ := hside₁ u (hu.trans_le (min_le_left _ _))
  have hu₂ := hside₂ u (hu.trans_le (min_le_right _ _))
  have hp₁ : dist (CircularExhaustion.arcParam c R u) d < S ↔ f u < 0 := by
    dsimp [f]
    rw [Complex.normSq_eq_norm_sq,←dist_eq_norm]
    have hd := dist_nonneg (x := CircularExhaustion.arcParam c R u) (y := d)
    constructor <;> intro h <;> nlinarith
  have hp₂ : S < dist (CircularExhaustion.arcParam c R u) d ↔ 0 < f u := by
    dsimp [f]
    rw [Complex.normSq_eq_norm_sq,←dist_eq_norm]
    have hd := dist_nonneg (x := CircularExhaustion.arcParam c R u) (y := d)
    constructor <;> intro h <;> nlinarith
  constructor
  · rw [hp₁,←not_le,←not_le]
    exact not_congr hu₁
  · rw [hp₂]
    have hh := not_congr hu₂
    simp only [not_le,neg_mul] at hh
    change -(f u) < 0 ↔ -(k * (u - t)) < 0 at hh
    simpa only [neg_lt_zero] using hh

end D12Complex.CircularCutGeometry
namespace D12Complex.CircularCutGeometry

lemma finite_frontier_of_eq_off_finite {S T E : Set ℝ}
    (hT : (frontier T).Finite) (hE : E.Finite)
    (heq : ∀ t ∉ E, t ∈ S ↔ t ∈ T) : (frontier S).Finite := by
  have hW : IsOpen Eᶜ := hE.isClosed.isOpen_compl
  have hlocal : S ∩ Eᶜ = T ∩ Eᶜ := by
    ext t
    simp only [mem_inter_iff,mem_compl_iff]
    constructor
    · exact fun h => ⟨(heq t h.2).mp h.1,h.2⟩
    · exact fun h => ⟨(heq t h.2).mpr h.1,h.2⟩
  apply (hT.union hE).subset
  intro t ht
  by_cases htE : t ∈ E
  · exact Or.inr htE
  · have hh : t ∈ frontier (S ∩ Eᶜ) ∩ Eᶜ := by
      rw [frontier_inter_open_inter hW]
      exact ⟨ht,htE⟩
    rw [hlocal,frontier_inter_open_inter hW] at hh
    exact Or.inl hh.1

/-- Off deleting-circle intersections, actual frontier membership on an original
circle is exactly the literal exposed-original and strict cut-exterior test. -/
lemma original_frontier_parameters_off_crossings (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hr : ∀ c ∈ s, 0 < r c) {c : ℂ} (hc : c ∈ s) (t : ℝ)
    (havoid : ∀ x ∈ centers,
      CircularExhaustion.arcParam c (r c) t ∉ sphere x (q x)) :
    CircularExhaustion.arcParam c (r c) t ∈
      frontier (circularCut (CircularExhaustion.diskUnion s r) centers q) ↔
      (∀ d ∈ s.erase c, r d ≤ dist (CircularExhaustion.arcParam c (r c) t) d) ∧
      (∀ x ∈ centers, q x < dist (CircularExhaustion.arcParam c (r c) t) x) := by
  classical
  let p := CircularExhaustion.arcParam c (r c) t
  have hp : dist p c = r c := mem_sphere.mp (arcParam_mem_sphere c (hr c hc).le t)
  have horig : p ∈ frontier (CircularExhaustion.diskUnion s r) ↔
      ∀ d ∈ s.erase c, r d ≤ dist p d := by
    change p ∈ frontier (FiniteCircularArcs.diskUnion s r) ↔ _
    rw [FiniteCircularArcs.mem_frontier_diskUnion s r hr p]
    constructor
    · exact fun h d hd => h.2 d (Finset.mem_erase.mp hd).2
    · intro h
      refine ⟨⟨c,hc,hp⟩,?_⟩
      intro d hd
      by_cases hdc : d = c
      · simpa only [hdc] using hp.ge
      · exact h d (Finset.mem_erase.mpr ⟨hdc,hd⟩)
  constructor
  · intro hcut
    have hcl := circularCut_closure_exterior hcut.1
    have hstrict : ∀ x ∈ centers, q x < dist p x := by
      intro x hx
      apply lt_of_le_of_ne (hcl.2 x hx)
      intro heq
      exact havoid x hx heq.symm
    have hout : p ∉ ⋃ x ∈ centers, closedBall x (q x) := by
      simpa only [mem_iUnion,mem_closedBall,not_exists,not_le] using hstrict
    exact ⟨horig.mp ((frontier_circularCut_away hout).mp hcut),hstrict⟩
  · rintro ⟨hor,hstrict⟩
    have hout : p ∉ ⋃ x ∈ centers, closedBall x (q x) := by
      simpa only [mem_iUnion,mem_closedBall,not_exists,not_le] using hstrict
    exact (frontier_circularCut_away hout).mpr (horig.mpr hor)

/-- Each original circle has only finitely many frontier changes for the actual
cut domain. Crossings are a finite modification of its literal exposed test. -/
lemma finite_frontier_actual_original_parameters (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hr : ∀ c ∈ s, 0 < r c) {c : ℂ} (hc : c ∈ s)
    (hnt : ∀ x ∈ centers, dist x c ≠ |q x - r c|) :
    (frontier {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam c (r c) t ∈
      frontier (circularCut (CircularExhaustion.diskUnion s r) centers q)}).Finite := by
  classical
  let E := ⋃ x ∈ centers,
    {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam c (r c) t ∈ sphere x (q x)}
  have hE : E.Finite := by
    apply centers.finite_toSet.biUnion
    intro x hx
    apply finite_angular_circle_intersections c x (r c) (q x) (hr c hc)
    by_cases hcx : c = x
    · refine Or.inr ?_
      intro heq
      apply hnt x hx
      rw [← heq,← hcx,dist_self,sub_self,abs_zero]
    · exact Or.inl hcx
  apply finite_frontier_of_eq_off_finite
    (finite_frontier_original_parameters s centers r q c (hr c hc) hnt) hE
  intro t htE
  by_cases ht : t ∈ Ioo 0 (2 * Real.pi)
  · have havoid : ∀ x ∈ centers,
        CircularExhaustion.arcParam c (r c) t ∉ sphere x (q x) := by
      intro x hx hxt
      apply htE
      exact mem_iUnion₂.mpr ⟨x,hx,⟨ht.1.le,ht.2.le⟩,hxt⟩
    simp only [mem_ofPred_eq,ht,true_and]
    exact original_frontier_parameters_off_crossings s centers r q hr hc t havoid
  · simp only [mem_ofPred_eq,ht,false_and]

end D12Complex.CircularCutGeometry

namespace D12Complex.CircularCutGeometry

lemma deleting_frontier_parameters_off_crossings (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hd : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {x : ℂ} (hx : x ∈ centers) (hQ : 0 < q x) (t : ℝ)
    (havoid : ∀ c ∈ s,
      CircularExhaustion.arcParam x (q x) t ∉ sphere c (r c)) :
    CircularExhaustion.arcParam x (q x) t ∈
      frontier (circularCut (CircularExhaustion.diskUnion s r) centers q) ↔
      CircularExhaustion.arcParam x (q x) t ∈ CircularExhaustion.diskUnion s r := by
  let p := CircularExhaustion.arcParam x (q x) t
  have hD : IsOpen (CircularExhaustion.diskUnion s r) := CircularExhaustion.diskUnion_open s r
  have hpsphere : p ∈ sphere x (q x) := arcParam_mem_sphere x hQ.le t
  constructor
  · intro hp
    have hpcl : p ∈ closure (CircularExhaustion.diskUnion s r) :=
      (circularCut_closure_exterior hp.1).1
    by_contra hpnot
    have hpfront : p ∈ frontier (CircularExhaustion.diskUnion s r) := by
      rw [hD.frontier_eq]
      exact ⟨hpcl,hpnot⟩
    obtain ⟨c,hc,hpc⟩ := mem_iUnion₂.mp
      (CircularExhaustion.frontier_diskUnion_subset_circles s r hpfront)
    exact havoid c hc hpc
  · intro hpD
    exact deleting_sphere_frontier hD hd hx hQ ⟨hpsphere,hpD⟩

lemma finite_frontier_actual_deleting_parameters (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hd : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {x : ℂ} (hx : x ∈ centers) (hQ : 0 < q x)
    (hnt : ∀ c ∈ s, dist x c ≠ |q x - r c|) :
    (frontier {t : ℝ | t ∈ Ioo 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam x (q x) t ∈
      frontier (circularCut (CircularExhaustion.diskUnion s r) centers q)}).Finite := by
  classical
  let E := ⋃ c ∈ s,
    {t : ℝ | t ∈ Icc 0 (2 * Real.pi) ∧
      CircularExhaustion.arcParam x (q x) t ∈ sphere c (r c)}
  have hE : E.Finite := by
    apply s.finite_toSet.biUnion
    intro c hc
    apply finite_angular_circle_intersections x c (q x) (r c) hQ
    by_cases hxc : x = c
    · refine Or.inr ?_
      intro heq
      apply hnt c hc
      rw [heq,hxc,dist_self,sub_self,abs_zero]
    · exact Or.inl hxc
  apply finite_frontier_of_eq_off_finite
    (finite_frontier_deleting_parameters s r x (q x) hQ hnt) hE
  intro t htE
  by_cases ht : t ∈ Ioo 0 (2 * Real.pi)
  · have havoid : ∀ c ∈ s,
        CircularExhaustion.arcParam x (q x) t ∉ sphere c (r c) := by
      intro c hc hct
      apply htE
      exact mem_iUnion₂.mpr ⟨c,hc,⟨ht.1.le,ht.2.le⟩,hct⟩
    simp only [mem_ofPred_eq,ht,true_and]
    exact deleting_frontier_parameters_off_crossings s centers r q hd hx hQ t havoid
  · simp only [mem_ofPred_eq,ht,false_and]

end D12Complex.CircularCutGeometry

namespace D12Complex.CircularCutGeometry

lemma finite_relative_frontier_of_clipped {S : Set ℝ}
    (hf : (frontier (Ioo 0 (2 * Real.pi) ∩ S)).Finite) :
    (frontier S ∩ Ioo 0 (2 * Real.pi)).Finite := by
  rw [← frontier_inter_open_inter isOpen_Ioo]
  apply Set.Finite.subset (s := frontier (S ∩ Ioo 0 (2 * Real.pi)))
  · simpa only [inter_comm] using hf
  · exact inter_subset_left

end D12Complex.CircularCutGeometry

namespace D12Complex.CircularCutGeometry

lemma finite_angular_frontier_actual_original (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hr : ∀ c ∈ s, 0 < r c) {c : ℂ} (hc : c ∈ s)
    (hnt : ∀ x ∈ centers, dist x c ≠ |q x - r c|) :
    (frontier (CircularExhaustion.arcParam c (r c) ⁻¹'
      frontier (circularCut (CircularExhaustion.diskUnion s r) centers q)) ∩
      Ioo 0 (2 * Real.pi)).Finite :=
  finite_relative_frontier_of_clipped
    (finite_frontier_actual_original_parameters s centers r q hr hc hnt)

lemma finite_angular_frontier_actual_deleting (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hd : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    {x : ℂ} (hx : x ∈ centers) (hQ : 0 < q x)
    (hnt : ∀ c ∈ s, dist x c ≠ |q x - r c|) :
    (frontier (CircularExhaustion.arcParam x (q x) ⁻¹'
      frontier (circularCut (CircularExhaustion.diskUnion s r) centers q)) ∩
      Ioo 0 (2 * Real.pi)).Finite :=
  finite_relative_frontier_of_clipped
    (finite_frontier_actual_deleting_parameters s centers r q hd hx hQ hnt)

end D12Complex.CircularCutGeometry


noncomputable section
open Set Metric
open scoped Topology
namespace D12Complex.CircularCutGeometry
open CircularExhaustion CircularCornerRounding

lemma positive_real_mem_frontier_sector {θ r : ℝ} (hθ : 0 < θ)
    (hθ' : θ < 2 * Real.pi) (hr : 0 < r) :
    (r : ℂ) ∈ frontier (sector θ) := by
  have hc : Continuous (fun t : ℝ => (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) := by
    fun_prop
  have hzero : (0 : ℝ) ∈ closure (Ioo 0 θ) := by
    rw [closure_Ioo hθ.ne]
    exact ⟨le_rfl,hθ.le⟩
  have hcl := mem_closure_image hc.continuousAt hzero
  have hsub : (fun t : ℝ => (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) '' Ioo 0 θ ⊆
      sector θ := by
    rintro z ⟨t,ht,rfl⟩
    exact ⟨r,t,hr,ht.1,ht.2,rfl⟩
  refine ⟨?_, ?_⟩
  · simpa using closure_mono hsub hcl
  · intro hi
    obtain ⟨s,t,hs,ht,htθ,he⟩ := interior_subset hi
    have hangle := angle_eq_of_polar_eq hs hr ⟨ht.le,htθ.le⟩ ⟨le_rfl,hθ.le⟩ hθ'
      (show (s : ℂ) * Complex.exp ((t : ℂ) * Complex.I) =
        (r : ℂ) * Complex.exp ((0 : ℂ) * Complex.I) by simpa using he.symm)
    linarith

lemma sectorChart_frontier_nonisolated {D : Set ℂ} {p : ℂ} {θ : ℝ}
    (h : SectorChart D p θ) (hθ : 0 < θ) (hθ' : θ < 2 * Real.pi) :
    p ∈ closure (frontier D \ {p}) := by
  obtain ⟨e,hp,he,hside,_,_⟩ := sectorChart_diffeomorph h
  have hz : (0 : ℂ) ∈ e.target := he ▸ e.map_source hp
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp e.open_target 0 hz
  have hzero : (0 : ℝ) ∈ closure (Ioo 0 ε) := by
    rw [closure_Ioo hε.ne]
    exact ⟨le_rfl,hε.le⟩
  have hc : ContinuousAt (fun r : ℝ => e.symm (r : ℂ)) 0 := by
    apply ContinuousAt.comp_of_eq (e.symm.continuousAt hz)
      Complex.continuous_ofReal.continuousAt
    exact Complex.ofReal_zero
  have hcl := mem_closure_image hc hzero
  have hsub : (fun r : ℝ => e.symm (r : ℂ)) '' Ioo 0 ε ⊆ frontier D \ {p} := by
    rintro z ⟨r,hr,rfl⟩
    have hrV : (r : ℂ) ∈ e.target := hball (by
      simpa only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hr.1] using hr.2)
    refine ⟨?_, ?_⟩
    · exact (hside.frontier.symm hrV).mpr
        (positive_real_mem_frontier_sector hθ hθ' hr.1)
    · intro hmem
      have hg : e.symm (r : ℂ) = p := Set.mem_singleton_iff.mp hmem
      have hx := congrArg e hg
      rw [e.right_inv hrV,he] at hx
      exact hr.1.ne' (Complex.ofReal_eq_zero.mp hx)
  have hg0 : e.symm (0 : ℂ) = p := by rw [← he]; exact e.left_inv hp
  simpa only [Complex.ofReal_zero, hg0] using closure_mono hsub hcl

end D12Complex.CircularCutGeometry


noncomputable section
open scoped BigOperators
namespace D12Complex.CircularCutGeometry

lemma sum_filter_fiber_equiv_sigma {L P M : Type*} [Fintype L] [DecidableEq L] [AddCommMonoid M]
    (pieces : L → Finset P)
    (e : Fin (Fintype.card (Σ l : L, ↥(pieces l))) ≃ (Σ l : L, ↥(pieces l)))
    (c : L) (g : L → P → M) :
    (∑ i ∈ Finset.univ.filter (fun i => (e i).1 = c),
      g (e i).1 (e i).2.val) = ∑ p ∈ pieces c, g c p := by
  classical
  rw [Finset.sum_filter]
  rw [e.sum_comp (fun p => if p.1 = c then g p.1 p.2.val else 0)]
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Fintype.sum_ite_eq']
  exact Finset.sum_coe_sort (pieces c) (g c)

end D12Complex.CircularCutGeometry


noncomputable section
open Set Metric MeasureTheory
open scoped Topology Interval
namespace D12Complex.CircularCutGeometry
open CircularExhaustion

lemma signed_circular_display_of_sectors (s centers : Finset ℂ) (r q : ℂ → ℝ)
    (hr : ∀ a ∈ s, 0 < r a) (hq : ∀ c ∈ centers, 0 < q c)
    (hd : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
      Disjoint (closedBall c (q c)) (closedBall d (q d)))
    (hnt : ∀ x ∈ centers, ∀ a ∈ s,
      dist x a ≠ q x+r a ∧ dist x a ≠ |q x-r a|)
    (hsectors : BoundarySectors (circularCut (diskUnion s r) centers q)) :
    SignedCircularDisplay (diskUnion s r)
      (circularCut (diskUnion s r) centers q) s r centers q := by
  classical
  let L := ↥s ⊕ ↥centers
  let K := circularCut (diskUnion s r) centers q
  have hno : ∀ z ∈ frontier K, z ∈ closure (frontier K \ {z}) := by
    obtain ⟨J,hJ,hs,hc⟩ := hsectors
    intro z hz
    by_cases hzJ : z ∈ J
    · obtain ⟨θ,hθ,hθ',hchart⟩ := hc z hzJ
      exact sectorChart_frontier_nonisolated hchart hθ hθ'
    · exact sectorChart_frontier_nonisolated (hs z hz hzJ) Real.pi_pos (by linarith [Real.pi_pos])
  have hfront : ∀ i : L,
      (frontier (arcParam (cutLabelCenter i) (cutLabelRadius r q i) ⁻¹' frontier K) ∩
        Ioo 0 (2*Real.pi)).Finite := by
    intro i
    cases i with
    | inl a =>
      exact finite_angular_frontier_actual_original s centers r q hr a.property
        (fun x hx => (hnt x hx a a.property).2)
    | inr c =>
      exact finite_angular_frontier_actual_deleting s centers r q hd c.property
        (hq c c.property) (fun a ha => (hnt c c.property a ha).2)
  obtain ⟨E,P,hP,hE,hbound,hinside,hcover,hdisjoint,hfrontier,hcross,hcoverage⟩ :=
    finite_circle_display_from_angular_frontiers
      (fun i : L => cutLabelCenter i) (cutLabelRadius r q)
      (cutLabelRadius_positive hr hq)
      (fun i j hij => cutLabel_circles_distinct hnt hij)
      (frontier K) isClosed_frontier (circularCut_frontier_subset_labelCircles hq) hno hfront
  have hpoint : ∀ (l : L) p, p ∈ P l → ∀ t ∈ Ioo p.1 p.2,
      (match l with
        | Sum.inl _ => arcParam (cutLabelCenter l) (cutLabelRadius r q l) t ∈ frontier (diskUnion s r)
        | Sum.inr _ => arcParam (cutLabelCenter l) (cutLabelRadius r q l) t ∈ diskUnion s r) ∧
      ∃ W : Set ℂ, IsOpen W ∧ arcParam (cutLabelCenter l) (cutLabelRadius r q l) t ∈ W ∧
        ∀ z ∈ W, z ∈ K ↔ cutLabelSign l *
          (‖z-cutLabelCenter l‖^2-(cutLabelRadius r q l)^2) < 0 := by
    intro l p hp t ht
    have hb := (hbound l p hp).2.2
    have htglobal : t ∈ Ioo 0 (2*Real.pi) :=
      ⟨hb.1.trans_lt ht.1,ht.2.trans_le hb.2.2⟩
    have hother : ∀ j : L, j ≠ l → arcParam (cutLabelCenter l) (cutLabelRadius r q l) t ∉
        sphere (cutLabelCenter j) (cutLabelRadius r q j) := by
      intro j hji hmem
      have hcell : p ∈ angularCells (E l) := by
        rw [hP l] at hp
        exact (mem_selectedAngularCells.mp hp).1
      exact angularCells_avoid_breakpoints hcell ht
        (hcross l j hji.symm t ⟨htglobal.1.le,htglobal.2.le⟩ hmem)
    have hh := cutLabel_piece_point hr hq hd l
      (hinside l p hp ⟨t,ht,rfl⟩)
      (circleMap_mem_sphere (cutLabelCenter l) (cutLabelRadius_positive hr hq l).le t) hother
    cases l <;> exact hh
  have hcell_mem : ∀ (l : L) (p : ℝ × ℝ), p ∈ P l → p ∈ angularCells (E l) := by
    intro l p hp
    rw [hP l] at hp
    exact (mem_selectedAngularCells.mp hp).1
  let T := Σ l : L, ↥(P l)
  let n := Fintype.card T
  let e : Fin n ≃ T := (Fintype.equivFin T).symm
  let C : Fin n → ℂ := fun i => cutLabelCenter (e i).1
  let R : Fin n → ℝ := fun i => cutLabelRadius r q (e i).1
  let A : Fin n → ℝ := fun i => (e i).2.val.1
  let B : Fin n → ℝ := fun i => (e i).2.val.2
  let S : Fin n → ℝ := fun i => cutLabelSign (e i).1
  let label : Fin n → L := fun i => (e i).1
  have hiP (i : Fin n) : (e i).2.val ∈ P (e i).1 := (e i).2.property
  have hbounds (i : Fin n) : 0 ≤ A i ∧ A i < B i ∧ B i ≤ 2*Real.pi :=
    (hbound (e i).1 (e i).2.val (hiP i)).2.2
  refine ⟨n,C,R,A,B,S,label,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨cutLabelRadius_positive hr hq (e i).1,hbounds i⟩
  · intro i
    change match (e i).1 with
      | Sum.inl a => C i = a ∧ R i = r a ∧ S i = 1 ∧
          arcParam (C i) (R i) '' Icc (A i) (B i) ⊆ frontier (diskUnion s r)
      | Sum.inr c => C i = c ∧ R i = q c ∧ S i = -1 ∧
          arcParam (C i) (R i) '' Ioo (A i) (B i) ⊆ diskUnion s r
    dsimp only [C,R,S,A,B]
    generalize he : e i = j
    rcases j with ⟨l,p,hp⟩
    cases l with
    | inl a =>
      refine ⟨rfl,rfl,rfl,?_⟩
      apply closed_arc_subset_original_frontier (hbound (.inl a) p hp).2.2.2.1
      rintro z ⟨t,ht,rfl⟩
      exact (hpoint (.inl a) p hp t ht).1
    | inr c =>
      refine ⟨rfl,rfl,rfl,?_⟩
      rintro z ⟨t,ht,rfl⟩
      exact (hpoint (.inr c) p hp t ht).1
  · apply Set.Subset.antisymm
    · intro z hz
      rw [hcover] at hz
      obtain ⟨l,hz⟩ := mem_iUnion.mp hz
      obtain ⟨p,hp,t,ht,heq⟩ := mem_iUnion₂.mp hz
      let j : T := ⟨l,⟨p,hp⟩⟩
      refine mem_iUnion.mpr ⟨e.symm j,?_⟩
      change z ∈ (fun v : T => arcParam (cutLabelCenter v.1) (cutLabelRadius r q v.1) ''
        Icc v.2.val.1 v.2.val.2) (e (e.symm j))
      rw [e.apply_symm_apply]
      exact ⟨t,ht,heq⟩
    · intro z hz
      obtain ⟨i,t,ht,heq⟩ := mem_iUnion.mp hz
      rw [hcover]
      exact mem_iUnion.mpr ⟨(e i).1,mem_iUnion₂.mpr
        ⟨(e i).2.val,hiP i,t,ht,heq⟩⟩
  · intro i j hij
    apply hdisjoint (e i).1 (e j).1 (e i).2.val (hiP i) (e j).2.val (hiP j)
    intro heq
    exact hij (e.injective (Sigma.subtype_ext (congrArg Prod.fst heq) (congrArg Prod.snd heq)))
  · intro i
    exact (arcParam_injOn_zero_two_pi (C i) (cutLabelRadius_positive hr hq (e i).1)).mono
      (Ioo_subset_Ioo (hbounds i).1 (hbounds i).2.2)
  · intro i t ht
    exact (hpoint (e i).1 (e i).2.val (hiP i) t ht).2
  · intro c
    refine ⟨measurableSet_angular_diskUnion s r c (q c), E (.inr c),?_,?_,?_,?_⟩
    · intro i hi
      have hh := hbound (e i).1 (e i).2.val (hiP i)
      change (e i).1 = Sum.inr c at hi
      simpa only [A,B,hi] using And.intro hh.1 hh.2.1
    · intro t ht htE
      have havoid : ∀ a ∈ s, arcParam c (q c) t ∉ sphere a (r a) := by
        intro a ha hta
        exact htE (hcross (.inr c) (.inl ⟨a,ha⟩) (by simp) t ⟨ht.1.le,ht.2.le⟩ hta)
      rw [← deleting_frontier_parameters_off_crossings s centers r q hd c.property
        (hq c c.property) t havoid]
      change arcParam (cutLabelCenter (Sum.inr c : L)) (cutLabelRadius r q (Sum.inr c : L)) t ∈ frontier K ↔ _
      rw [hcoverage (.inr c) t ht htE]
      constructor
      · rintro ⟨p,hp,htp⟩
        let j : T := ⟨Sum.inr c,⟨p,hp⟩⟩
        refine ⟨e.symm j,?_,?_⟩
        · simp only [label,e.apply_symm_apply,j]
        · change t ∈ (fun v : T => Ioo v.2.val.1 v.2.val.2) (e (e.symm j))
          rw [e.apply_symm_apply]
          exact htp
      · rintro ⟨i,hi,hti⟩
        refine ⟨(e i).2.val,?_,hti⟩
        change (e i).1 = Sum.inr c at hi
        simpa only [hi] using hiP i
    · intro i j hi hj hij
      have hid : (e i).1 = Sum.inr c := hi
      have hjd : (e j).1 = Sum.inr c := hj
      have hpi : (e i).2.val ∈ angularCells (E (.inr c)) := by
        exact Eq.mp (congrArg (fun ep : Finset ℝ => (e i).2.val ∈ angularCells ep)
          (congrArg E hid)) (hcell_mem (e i).1 (e i).2.val (hiP i))
      have hpj : (e j).2.val ∈ angularCells (E (.inr c)) := by
        exact Eq.mp (congrArg (fun ep : Finset ℝ => (e j).2.val ∈ angularCells ep)
          (congrArg E hjd)) (hcell_mem (e j).1 (e j).2.val (hiP j))
      apply angularCells_pairwise_disjoint (E (.inr c)) hpi hpj
      intro heq
      exact hij (e.injective (Sigma.subtype_ext (hid.trans hjd.symm) heq))
    · intro f _ hf _
      change (∑ i ∈ Finset.univ.filter (fun i => (e i).1 = Sum.inr c),
        ∫ t in (e i).2.val.1..(e i).2.val.2, f t) = _
      rw [sum_filter_fiber_equiv_sigma P e (Sum.inr c)
        (fun _ p => ∫ t in p.1..p.2, f t)]
      refine finite_angular_interval_additivity (P (.inr c)) Prod.fst Prod.snd
        0 (2*Real.pi) (by positivity)
        ((arcParam c (q c)) ⁻¹' diskUnion s r) (↑(E (.inr c)) : Set ℝ)
        (measurableSet_angular_diskUnion s r c (q c)) (E (.inr c)).finite_toSet
        (fun p hp => (hbound (.inr c) p hp).2.2) ?_ ?_ f ?_
      · intro p hp z hz hpz
        exact angularCells_pairwise_disjoint (E (.inr c))
          (hcell_mem (.inr c) p hp) (hcell_mem (.inr c) z hz) hpz
      · intro t ht htE
        have havoid : ∀ a ∈ s, arcParam c (q c) t ∉ sphere a (r a) := by
          intro a ha hta
          exact htE (hcross (.inr c) (.inl ⟨a,ha⟩) (by simp) t ⟨ht.1.le,ht.2.le⟩ hta)
        exact (deleting_frontier_parameters_off_crossings s centers r q hd c.property
          (hq c c.property) t havoid).symm.trans (hcoverage (.inr c) t ht htE)
      · intro p hp
        have hb := (hbound (.inr c) p hp).2.2
        apply hf.mono_set
        rw [uIcc_of_le hb.2.1.le,uIcc_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
        exact Icc_subset_Icc hb.1 hb.2.2

/-- The full all-small-radii fixed-cut geometry, with the literal signed
frontier partition and exact deleting-circle angular integrals. -/
theorem cut_circular_geometry :
    Specs.D12Complex.Ch14.CutCircularGeometry.cut_circular_geometry_type := by
  classical
  intro s r hG corners poles hcorners hsmooth hcornerCharts hpoles
  let centers := poles ∪ corners
  obtain ⟨δ,hδ,hδgeom⟩ := uniform_deletion_geometry s r hG.1 poles centers hpoles
    (by intro c hc; exact Finset.mem_union_left _ hc)
  refine ⟨δ,hδ,?_⟩
  intro q hq
  obtain ⟨hpole,hd,hnt,havoid,_,_⟩ := hδgeom q hq
  have hqpos : ∀ c ∈ centers, 0 < q c := fun c hc => (hq c hc).1
  have hsectors : BoundarySectors (circularCut (diskUnion s r) centers q) :=
    circularCut_boundarySectors s centers corners r q hG.1 hqpos
      (by intro c hc; exact Finset.mem_union_right _ hc) hsmooth hd hnt havoid
  have hdisplay := signed_circular_display_of_sectors s centers r q hG.1 hqpos hd hnt hsectors
  refine ⟨hpole,hd,?_⟩
  obtain ⟨J,hJ,hJsm,hJcorner⟩ := hsectors
  refine ⟨J,?_,hdisplay⟩
  refine ⟨circularCut_isOpen (diskUnion_open s r) centers q,?_,hJ,?_,hJsm,hJcorner⟩
  · exact circularCut_isBounded
      ((diskUnion_closure_compact s r).isBounded.subset subset_closure) centers q
  · obtain ⟨n,c,R,a,b,sign,label,hb,_,hfront,hdisj,_,_,_⟩ := hdisplay
    refine ⟨n,c,R,a,b,?_,hfront,hdisj⟩
    intro i
    have hi := hb i
    exact ⟨hi.1,hi.2.2.1,by linarith [hi.2.1,hi.2.2.2]⟩

end D12Complex.CircularCutGeometry
