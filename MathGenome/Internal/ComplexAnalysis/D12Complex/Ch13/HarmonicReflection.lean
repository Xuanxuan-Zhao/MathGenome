import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicReflection
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.DiskDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.BoundaryMaximum

noncomputable section
open scoped ComplexConjugate
open Complex Metric Set Filter InnerProductSpace Laplacian
open scoped Topology

namespace D12Complex.HarmonicReflection

def oddReflection : Specs.D12Complex.Ch13.HarmonicReflection.oddReflection_type :=
  Specs.D12Complex.Ch13.HarmonicReflection.oddReflection_value

lemma oddReflection_of_pos (u : ℂ → ℝ) {z : ℂ} (hz : 0 < z.im) :
    oddReflection u z = u z := by simp [oddReflection,
      Specs.D12Complex.Ch13.HarmonicReflection.oddReflection_value, hz]

lemma oddReflection_of_neg (u : ℂ → ℝ) {z : ℂ} (hz : z.im < 0) :
    oddReflection u z = -u (conj z) := by simp [oddReflection,
      Specs.D12Complex.Ch13.HarmonicReflection.oddReflection_value, hz, not_lt.mpr hz.le]

lemma oddReflection_of_zero (u : ℂ → ℝ) {z : ℂ} (hz : z.im = 0) :
    oddReflection u z = 0 := by simp [oddReflection,
      Specs.D12Complex.Ch13.HarmonicReflection.oddReflection_value, hz]

lemma oddReflection_conj (u : ℂ → ℝ) (z : ℂ) :
    oddReflection u (conj z) = -oddReflection u z := by
  rcases lt_trichotomy z.im 0 with hn | he | hp
  · rw [oddReflection_of_neg u hn, oddReflection_of_pos u (by simpa using hn)]
    simp
  · rw [oddReflection_of_zero u he,
      oddReflection_of_zero u (z := conj z) (by simp [he]), neg_zero]
  · rw [oddReflection_of_pos u hp, oddReflection_of_neg u (by simpa using hp)]
    simp

/-- Conjugation preserves the Laplacian: the two imaginary directions
both change sign in the second differential. -/
lemma laplacian_comp_conj (u : ℂ → ℝ) (z : ℂ) :
    Δ (u ∘ conj) z = Δ u (conj z) := by
  have hi := conjCLE.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ
    (x := z) (mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hi
  change iteratedFDeriv ℝ 2 (u ∘ conj) z = _ at hi
  have happ (v w : ℂ) : iteratedFDeriv ℝ 2 (u ∘ conj) z ![v, w] =
      iteratedFDeriv ℝ 2 u (conj z) ![conj v, conj w] := by
    rw [hi]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [laplacian_eq_iteratedFDeriv_complexPlane,
    laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  rw [happ, happ]
  simp [iteratedFDeriv_two_apply]

lemma harmonicOnNhd_comp_conj {U : Set ℂ} {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u U) : HarmonicOnNhd (u ∘ conj) (conj ⁻¹' U) := by
  intro z hz
  refine ⟨(hu _ hz).1.comp z conjCLE.contDiff.contDiffAt, ?_⟩
  have ht := continuous_conj.continuousAt.tendsto.eventually (hu _ hz).2
  filter_upwards [ht] with w hw
  change Δ (u ∘ conj) w = 0
  rw [laplacian_comp_conj]
  exact hw

lemma reflection_continuous_closedBall {R r : ℝ} {u : ℂ → ℝ}
    (hrR : r < R)
    (hc : ContinuousOn u {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im})
    (hzero : ∀ z : ℂ, ‖z‖ < R → z.im = 0 → u z = 0) :
    ContinuousOn (oddReflection u) (closedBall 0 r) := by
  let A := closedBall (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
  let B := closedBall (0 : ℂ) r ∩ {z : ℂ | z.im ≤ 0}
  have hA : ContinuousOn (oddReflection u) A := by
    apply (hc.mono (show A ⊆ {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im} from
      fun z hz => ⟨(by simpa using hz.1 : ‖z‖ ≤ r).trans_lt hrR, hz.2⟩)).congr
    intro z hz
    by_cases hp : 0 < z.im
    · exact oddReflection_of_pos u hp
    · have he : z.im = 0 := le_antisymm (le_of_not_gt hp) hz.2
      rw [oddReflection_of_zero u he, hzero z
        ((by simpa using hz.1 : ‖z‖ ≤ r).trans_lt hrR) he]
  have hB : ContinuousOn (oddReflection u) B := by
    have hmaps : MapsTo conj B {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im} := by
      intro z hz
      exact ⟨by simpa using (by simpa using hz.1 : ‖z‖ ≤ r).trans_lt hrR,
        by simpa using hz.2⟩
    apply ((hc.comp continuous_conj.continuousOn hmaps).neg).congr
    intro z hz
    by_cases hn : z.im < 0
    · exact oddReflection_of_neg u hn
    · have he : z.im = 0 := le_antisymm hz.2 (le_of_not_gt hn)
      change oddReflection u z = -u (conj z)
      rw [oddReflection_of_zero u he, hzero (conj z)
        (by simpa using (by simpa using hz.1 : ‖z‖ ≤ r).trans_lt hrR)
        (by simpa using he), neg_zero]
  have hcAB := hA.union_of_isClosed hB
    (isClosed_closedBall.inter (isClosed_le continuous_const continuous_im))
    (isClosed_closedBall.inter (isClosed_le continuous_im continuous_const))
  apply hcAB.mono
  intro z hz
  rcases le_total 0 z.im with hp | hn
  · exact Or.inl ⟨hz, hp⟩
  · exact Or.inr ⟨hz, hn⟩

/-- Boundary comparison on an arbitrary bounded open set. The common
continuous extension need only be specified on a set containing its closure. -/
lemma eqOn_of_boundary {U K : Set ℂ} {f g : ℂ → ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hf : HarmonicOn U f) (hg : HarmonicOn U g)
    (hUK : U ⊆ K) (hfront : frontier U ⊆ K)
    (hfc : ContinuousOn f K) (hgc : ContinuousOn g K)
    (hb : EqOn f g (frontier U)) : EqOn f g U := by
  let w := f - g
  have hw : HarmonicOn U w :=
    (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U w hU).mpr
      (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U f hU).mp hf).sub
        ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U g hU).mp hg))
  have hwc : ContinuousOn w K := hfc.sub hgc
  have hbd : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ z ∈ U, dist z ξ < δ → |w z| < ε := by
    intro ξ hξ ε hε
    obtain ⟨δ, hδ, hbound⟩ := Metric.continuousWithinAt_iff.mp (hwc ξ (hfront hξ)) ε hε
    refine ⟨δ, hδ, fun z hz hd => ?_⟩
    have he : w ξ = 0 := sub_eq_zero.mpr (hb hξ)
    simpa only [he, Real.dist_eq, sub_zero] using hbound (hUK hz) hd
  have hbup : BoundaryLimsupLE U w 0 := by
    intro ξ hξ ε hε
    obtain ⟨δ, hδ, hbδ⟩ := hbd ξ hξ ε hε
    exact ⟨δ, hδ, fun z hz hd => by
      simpa using (le_abs_self (w z)).trans (hbδ z hz hd).le⟩
  have hbdown : BoundaryLiminfGE U w 0 := by
    intro ξ hξ ε hε
    obtain ⟨δ, hδ, hbδ⟩ := hbd ξ hξ ε hε
    refine ⟨δ, hδ, fun z hz hd => ?_⟩
    have := (abs_lt.mp (hbδ z hz hd)).1
    linarith
  have hle := BoundaryMaximum.harmonic_boundary_maximum U w 0 hUb hw hbup
  have hge := BoundaryMaximum.harmonic_boundary_minimum U w 0 hUb hw hbdown
  intro z hz
  exact sub_eq_zero.mp (le_antisymm (hle z hz) (hge z hz))

lemma halfDisk_isOpen (r : ℝ) : IsOpen {z : ℂ | ‖z‖ < r ∧ 0 < z.im} :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const continuous_im)

lemma halfDisk_frontier {r : ℝ} {ξ : ℂ}
    (hξ : ξ ∈ frontier {z : ℂ | ‖z‖ < r ∧ 0 < z.im}) :
    (‖ξ‖ ≤ r ∧ 0 ≤ ξ.im) ∧ (‖ξ‖ = r ∨ ξ.im = 0) := by
  have hc := frontier_subset_closure hξ
  have hn : ‖ξ‖ ≤ r :=
    closure_minimal (s := {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
      (t := {z : ℂ | ‖z‖ ≤ r}) (fun _ hz => hz.1.le)
      (isClosed_le continuous_norm continuous_const) hc
  have hi : 0 ≤ ξ.im :=
    closure_minimal (s := {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
      (t := {z : ℂ | 0 ≤ z.im}) (fun _ hz => hz.2.le)
      (isClosed_le continuous_const continuous_im) hc
  refine ⟨⟨hn, hi⟩, ?_⟩
  have hnot : ¬ (‖ξ‖ < r ∧ 0 < ξ.im) :=
    (show ξ ∉ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} from
      ((halfDisk_isOpen r).frontier_eq ▸ hξ).2)
  by_cases hnr : ‖ξ‖ < r
  · exact Or.inr (le_antisymm (le_of_not_gt (fun h => hnot ⟨hnr, h⟩)) hi)
  · exact Or.inl (le_antisymm hn (le_of_not_gt hnr))

/-- On every smaller disk the odd reflection is the continuous Dirichlet
solution for its own boundary data. Uniqueness supplies oddness of that
solution before any smoothness across the diameter is claimed. -/
lemma harmonic_oddReflection_smaller {R r : ℝ} {u : ℂ → ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hu : HarmonicOn {z : ℂ | ‖z‖ < R ∧ 0 < z.im} u)
    (hc : ContinuousOn u {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im})
    (hzero : ∀ z : ℂ, ‖z‖ < R → z.im = 0 → u z = 0) :
    HarmonicOn (ball 0 r) (oddReflection u) := by
  let φ := oddReflection u
  let F := DiskDirichlet.closedPoissonIntegral r φ
  have hcφ : ContinuousOn φ (sphere 0 r) :=
    (reflection_continuous_closedBall hrR hc hzero).mono sphere_subset_closedBall
  obtain ⟨hFc, hFh, hFb, _⟩ := DiskDirichlet.closedPoissonIntegral_solution r φ hr hcφ
  change ContinuousOn F (closedBall 0 r) at hFc
  change HarmonicOn (ball 0 r) F at hFh
  change EqOn F φ (sphere 0 r) at hFb
  have hconjClosed : MapsTo conj (closedBall (0 : ℂ) r) (closedBall 0 r) :=
    fun z hz => by simpa using hz
  have hconjBall : MapsTo conj (ball (0 : ℂ) r) (ball 0 r) :=
    fun z hz => by simpa using hz
  have hFn : HarmonicOnNhd F (ball 0 r) :=
    (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hFh
  have hFch : HarmonicOn (ball 0 r) (fun z => -F (conj z)) :=
    (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mpr
      ((harmonicOnNhd_comp_conj hFn).mono hconjBall).neg
  have hFcc : ContinuousOn (fun z => -F (conj z)) (closedBall 0 r) :=
    (hFc.comp continuous_conj.continuousOn hconjClosed).neg
  have hFcb : EqOn (fun z => -F (conj z)) φ (sphere 0 r) := by
    intro z hz
    change -F (conj z) = φ z
    rw [hFb (by simpa using hz)]
    exact (congrArg Neg.neg (oddReflection_conj u z)).trans (neg_neg _)
  have hodd : ∀ z ∈ closedBall (0 : ℂ) r, -F (conj z) = F z :=
    DiskDirichlet.disk_dirichlet_unique r φ _ hr hcφ hFcc hFch hFcb
  have hFzero : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 → F z = 0 := by
    intro z hz hi
    have he : conj z = z := by apply Complex.ext <;> simp [hi]
    have := hodd z hz
    rw [he] at this
    linarith
  let U := {z : ℂ | ‖z‖ < r ∧ 0 < z.im}
  let K := closedBall (0 : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
  have hU : IsOpen U := halfDisk_isOpen r
  have hUR : U ⊆ {z : ℂ | ‖z‖ < R ∧ 0 < z.im} :=
    fun z hz => ⟨hz.1.trans hrR, hz.2⟩
  have hUB : U ⊆ ball (0 : ℂ) r := fun z hz => by simpa using hz.1
  have hUK : U ⊆ K := fun z hz => ⟨by simpa using hz.1.le, hz.2.le⟩
  have hfrontK : frontier U ⊆ K := fun z hz =>
    ⟨by simpa using (halfDisk_frontier hz).1.1, (halfDisk_frontier hz).1.2⟩
  have hKR : K ⊆ {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im} :=
    fun z hz => ⟨(by simpa using hz.1 : ‖z‖ ≤ r).trans_lt hrR, hz.2⟩
  have huU : HarmonicOn U u :=
    (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hU).mpr
      (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hu.1).mp hu).mono hUR)
  have hFU : HarmonicOn U F :=
    (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hU).mpr (hFn.mono hUB)
  have hb : EqOn F u (frontier U) := by
    intro z hz
    obtain ⟨⟨hn, hi⟩, hcases⟩ := halfDisk_frontier hz
    have hnR := hn.trans_lt hrR
    rcases hcases with hs | he
    · rw [hFb (by simpa using hs)]
      by_cases hp : 0 < z.im
      · exact oddReflection_of_pos u hp
      · have hi0 : z.im = 0 := le_antisymm (le_of_not_gt hp) hi
        change oddReflection u z = u z
        rw [oddReflection_of_zero u hi0, hzero z hnR hi0]
    · rw [hFzero z (by simpa using hn) he, hzero z hnR he]
  have hagree : EqOn F u U := eqOn_of_boundary hU
    (isBounded_ball.subset hUB) hFU huU hUK hfrontK
    (hFc.mono inter_subset_left) (hc.mono hKR) hb
  have heq : EqOn F φ (ball 0 r) := by
    intro z hz
    have hn : ‖z‖ < r := by simpa using hz
    rcases lt_trichotomy z.im 0 with hm | he | hp
    · change F z = oddReflection u z
      rw [oddReflection_of_neg u hm, ← hagree (show conj z ∈ U from
        ⟨by simpa using hn, by simpa using hm⟩)]
      exact (hodd z (ball_subset_closedBall hz)).symm
    · change F z = oddReflection u z
      rw [oddReflection_of_zero u he, hFzero z (ball_subset_closedBall hz) he]
    · exact (hagree ⟨hn, hp⟩).trans (oddReflection_of_pos u hp).symm
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mpr
  intro z hz
  exact (harmonicAt_congr_nhds (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz))).mp
    (hFn z hz)

theorem harmonic_oddReflection :
    Specs.D12Complex.Ch13.HarmonicReflection.harmonic_oddReflection_type := by
  intro R u hR hu hc hzero
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mpr
  intro z hz
  have hn : ‖z‖ < R := by simpa using hz
  obtain ⟨r, hzr, hrR⟩ := exists_between hn
  have hr : 0 < r := (norm_nonneg z).trans_lt hzr
  exact ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp
    (harmonic_oddReflection_smaller hr hrR hu hc hzero)) z (by simpa using hzr)

/-- Transport the proved reflection theorem by an arbitrary complex similarity.
Its inverse and the explicit reflection formula are verified here. -/
theorem harmonic_oddReflection_affine :
    Specs.D12Complex.Ch13.HarmonicReflection.harmonic_oddReflection_affine_type := by
  intro a c R u hc hR hu hcont hzero
  let A : ℂ → ℂ := fun w => a + c * w
  let T : ℂ → ℂ := fun z => (z - a) / c
  have hTA (w : ℂ) : T (A w) = w := by simp [T, A, hc]
  have hAT (z : ℂ) : A (T z) = z := by
    dsimp [A, T]
    rw [mul_div_cancel₀ _ hc]
    ring
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hTc : Continuous T := by dsimp [T]; fun_prop
  have hAh : HolomorphicOn {z : ℂ | ‖z‖ < R ∧ 0 < z.im} A :=
    ⟨halfDisk_isOpen R, fun z _ => by dsimp [A]; fun_prop⟩
  have hmaps : MapsTo A {z : ℂ | ‖z‖ < R ∧ 0 < z.im}
      {z : ℂ | ‖(z-a)/c‖ < R ∧ 0 < ((z-a)/c).im} := by
    intro z hz
    change ‖T (A z)‖ < R ∧ 0 < (T (A z)).im
    rw [hTA]
    exact hz
  have hup : HarmonicOn {z : ℂ | ‖z‖ < R ∧ 0 < z.im} (u ∘ A) :=
    HarmonicFoundation.harmonicOn_comp_holomorphic _ _ u A hu hAh hmaps
  have hcup : ContinuousOn (u ∘ A) {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im} := by
    apply hcont.comp hAc.continuousOn
    intro z hz
    change ‖T (A z)‖ < R ∧ 0 ≤ (T (A z)).im
    rw [hTA]
    exact hz
  have hzeroUp : ∀ z : ℂ, ‖z‖ < R → z.im = 0 → (u ∘ A) z = 0 := by
    intro z hz hi
    apply hzero (A z)
    · change ‖T (A z)‖ < R
      rwa [hTA]
    · change (T (A z)).im = 0
      rwa [hTA]
  have hreflection : HarmonicOn (ball 0 R) (oddReflection (u ∘ A)) :=
    harmonic_oddReflection R (u ∘ A) hR hup hcup hzeroUp
  have hV : IsOpen {z : ℂ | ‖T z‖ < R} :=
    isOpen_lt hTc.norm continuous_const
  have hTh : HolomorphicOn {z : ℂ | ‖T z‖ < R} T :=
    ⟨hV, fun z _ => by dsimp [T]; fun_prop⟩
  have hresult := HarmonicFoundation.harmonicOn_comp_holomorphic
    (ball 0 R) {z : ℂ | ‖T z‖ < R} (oddReflection (u ∘ A)) T
    hreflection hTh (fun z hz => by simpa using hz)
  have heq : (oddReflection (u ∘ A) ∘ T) =
      (fun z => if 0 < (T z).im then u z
        else if (T z).im < 0 then -u (A (conj (T z))) else 0) := by
    ext z
    simp only [Function.comp_apply, oddReflection,
      Specs.D12Complex.Ch13.HarmonicReflection.oddReflection_value, hAT]
  rw [heq] at hresult
  exact hresult

end D12Complex.HarmonicReflection
