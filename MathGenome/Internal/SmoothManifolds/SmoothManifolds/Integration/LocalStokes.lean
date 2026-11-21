import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.LocalStokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Atlases
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Topology

namespace SmoothManifolds.LocalStokesResults
open ModelData LocalStokesData MeasureTheory Set Filter

/-- A compactly supported C¹ scalar field has zero integral of every
constant-direction derivative. Integrability follows from compact support of
the derivative; integration by parts against 1 then gives the identity. -/
theorem integral_directional_derivative {n : ℕ} (f : Euclidean n → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) (v : Euclidean n) :
    Integrable (fun x => fderiv ℝ f x v) ∧ (∫ x, fderiv ℝ f x v) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x v) :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  refine ⟨hi, ?_⟩
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Euclidean n => (1 : ℝ)) (g := f) (v := v)
    (by simp)
    (by simpa using hi)
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ => differentiableAt_const 1)
    (fun x _ => hf.differentiable (by simp) x)
  simpa using h

/-- The full-space part, directly on genuine alternating covectors. -/
theorem fullSpaceStokes_proof :
    Specs.SmoothManifolds.Integration.LocalStokes.fullSpaceStokesType := by
  intro n ω hω hs
  let f (i : Fin (n+1)) (x : Euclidean (n+1)) := ω x (i.removeNth (frame (n+1)))
  have hf (i : Fin (n+1)) : ContDiff ℝ 1 (f i) :=
    (ContinuousAlternatingMap.apply ℝ (Euclidean (n+1)) ℝ (i.removeNth (frame (n+1)))).contDiff.comp hω
  have hfs (i : Fin (n+1)) : HasCompactSupport (f i) := by
    exact hs.comp_left (g := fun A : (Euclidean (n+1)) [⋀^Fin n]→L[ℝ] ℝ =>
      A (i.removeNth (frame (n+1)))) (by simp)
  have hd (x : Euclidean (n+1)) : bulkCoefficient ω x =
      ∑ i : Fin (n+1), (-1 : ℝ)^i.val * fderiv ℝ (f i) x (frame (n+1) i) := by
    simpa [bulkCoefficient, f, zsmul_eq_mul] using
      extDeriv_apply (hω.differentiable (by simp) x) (frame (n+1))
  have hi (i : Fin (n+1)) := integral_directional_derivative (f i) (hf i) (hfs i)
    (frame (n+1) i)
  have hInt (i : Fin (n+1)) :
      Integrable (fun x => (-1 : ℝ)^i.val * fderiv ℝ (f i) x (frame (n+1) i)) :=
    (hi i).1.const_mul _
  constructor
  · change Integrable (fun x => bulkCoefficient ω x)
    simp_rw [hd]
    exact integrable_finsetSum _ (fun i _ => hInt i)
  · simp_rw [hd]
    rw [integral_finsetSum _ (fun i _ => hInt i)]
    simp [integral_const_mul, (hi _).2]

/-- Multiplication of the restricted-form sign and the outward-first frame
sign gives the negative last coefficient, including the endpoint case. -/
theorem boundarySign_proof :
    Specs.SmoothManifolds.Integration.LocalStokes.boundarySignType := by
  intro n ω x
  have hframe : (Fin.last n).removeNth (frame (n+1)) =
      fun j => frame (n+1) j.castSucc := by
    funext j
    simp [Fin.removeNth, Fin.succAbove_last]
  simp only [boundaryCoefficient, signedOmittedCoefficient, Fin.val_last, hframe, pow_succ]
  ring

/-- Local ambient Cʳ extensions imply the usual within-set Cʳ predicate.
No extension on the whole ambient space is assumed. -/
theorem localExtensions_contDiffOn {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set (Euclidean n)}
    {f : Euclidean n → F} {r : ℕ∞}
    (hf : LocallyContDiffOn r s (fun x => f x.val)) : ContDiffOn ℝ r f s := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, he⟩ := hf ⟨x, hx⟩
  apply ((hg.contDiffAt (hU.mem_nhds hxU)).contDiffWithinAt).congr_of_eventuallyEq_of_mem
    (s := s) _ hx
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hxU)] with y hy hyU
  exact (he ⟨y, hy⟩ hyU).symm

/-- A relative compact support has a compact ambient image, on which all
nonzero values in the model are supported. -/
theorem relative_support_image {n : ℕ} {F : Type*} [Zero F]
    (s : Set (Euclidean n)) (f : Euclidean n → F)
    (hs : HasCompactSupport (fun x : s => f x.val)) :
    ∃ K : Set (Euclidean n), IsCompact K ∧ K ⊆ s ∧
      ∀ x ∈ s, x ∉ K → f x = 0 := by
  refine ⟨Subtype.val '' tsupport (fun x : s => f x.val),
    hs.image continuous_subtype_val, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · intro x hx hxK
    by_contra hn
    exact hxK ⟨⟨x, hx⟩, subset_tsupport _ hn, rfl⟩

/-- Outside a compact relative support the within-set derivative vanishes.
This uses a relative zero germ, so also applies at the true boundary. -/
theorem fderivWithin_zero_off_compact {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {s K : Set (Euclidean n)}
    (hK : IsCompact K) (f : Euclidean n → F)
    (hz : ∀ x ∈ s, x ∉ K → f x = 0) {x : Euclidean n}
    (hx : x ∈ s) (hxK : x ∉ K) : fderivWithin ℝ f s x = 0 := by
  have he : f =ᶠ[𝓝[s] x] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hK.isClosed.isOpen_compl.mem_nhds hxK)] with y hy hyK
    exact hz y hy hyK
  rw [he.fderivWithin_eq_of_mem hx]
  simp

/-- Divergence theorem on the closed half-space, for scalar components.
The only compactness assumption is on a relative support in the model. -/
theorem halfSpace_divergence {n : ℕ}
    (f : Fin (n+1) → Euclidean (n+1) → ℝ)
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (halfSpaceSet (n+1)))
    (K : Set (Euclidean (n+1))) (hK : IsCompact K)
    (hKH : K ⊆ halfSpaceSet (n+1))
    (hz : ∀ i x, x ∈ halfSpaceSet (n+1) → x ∉ K → f i x = 0) :
    IntegrableOn (fun x => ∑ i, fderivWithin ℝ (f i) (halfSpaceSet (n+1)) x
      (frame (n+1) i)) (halfSpaceSet (n+1)) ∧
    Integrable (fun y => f (Fin.last n) ((Fin.last n).insertNth 0 y)) ∧
    (∫ x in halfSpaceSet (n+1), ∑ i,
      fderivWithin ℝ (f i) (halfSpaceSet (n+1)) x (frame (n+1) i)) =
      - ∫ y, f (Fin.last n) ((Fin.last n).insertNth 0 y) := by
  classical
  let H := halfSpaceSet (n+1)
  have hHc : IsClosed H := isClosed_le continuous_const (continuous_apply (Fin.last n))
  have hud : UniqueDiffOn ℝ H := uniqueDiffOn_halfSpaceSet (n+1)
  let D (i : Fin (n+1)) := fderivWithin ℝ (f i) H
  let d (x : Euclidean (n+1)) := ∑ i, D i x (frame (n+1) i)
  have hdcont : ContinuousOn d H := by
    exact continuousOn_finsetSum _ (fun i _ =>
      ((hf i).continuousOn_fderivWithin hud (by norm_num)).clm_apply continuousOn_const)
  have hd0 (x : Euclidean (n+1)) (hx : x ∈ H) (hxK : x ∉ K) : d x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    dsimp only [D]
    rw [fderivWithin_zero_off_compact hK (f i) (hz i) hx hxK]
    rfl
  have hdi : IntegrableOn d H :=
    ((hdcont.mono hKH).integrableOn_compact hK).of_forall_sdiff_eq_zero hHc.measurableSet
      (fun x hx => hd0 x hx.1 hx.2)
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_ball_lt 0 0
  have hbnd (x : Euclidean (n+1)) (hx : x ∈ K) (i : Fin (n+1)) : |x i| < R := by
    exact (norm_le_pi_norm x i).trans_lt (by simpa using hR hx)
  let a : Euclidean (n+1) := fun i => if i = Fin.last n then 0 else -R
  let b : Euclidean (n+1) := fun _ => R
  let B := Icc a b
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    split_ifs <;> linarith
  have hBH : B ⊆ H := by
    intro x hx
    have h := hx.1 (Fin.last n)
    simpa [a, H, halfSpaceSet] using h
  have hKB : K ⊆ B := by
    intro x hx
    constructor
    · intro i
      dsimp [a]
      split_ifs with hi
      · subst i
        exact hKH hx
      · exact (abs_lt.mp (hbnd x hx i)).1.le
    · intro i
      exact (abs_lt.mp (hbnd x hx i)).2.le
  have hdeq : (∫ x in H, d x) = ∫ x in B, d x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hHc.measurableSet hBH
      (fun x hx => hd0 x hx.1 (fun h => hx.2 (hKB h)))
  have hdf (x : Euclidean (n+1))
      (hx : x ∈ (pi univ fun i => Ioo (a i) (b i)) \ (∅ : Set (Euclidean (n+1))))
      (i : Fin (n+1)) : HasFDerivAt (f i) (D i x) x := by
    have hxlast : 0 < x (Fin.last n) := by
      simpa [a] using (hx.1 (Fin.last n) (mem_univ _)).1
    have hnhds : H ∈ 𝓝 x :=
      mem_of_superset ((isOpen_lt continuous_const (continuous_apply (Fin.last n))).mem_nhds
        hxlast) (fun y hy => by exact (le_of_lt hy : 0 ≤ y (Fin.last n)))
    dsimp only [D]
    rw [fderivWithin_of_mem_nhds hnhds]
    exact ((hf i).differentiableOn (by norm_num) x (le_of_lt hxlast)).differentiableAt
      hnhds |>.hasFDerivAt
  have hbox := integral_divergence_of_hasFDerivAt_off_countable' a b hab f D ∅ countable_empty
    (fun i => (hf i).continuousOn.mono hBH) hdf (hdi.mono_set hBH)
  have hfront (i : Fin (n+1)) (x : Euclidean n)
      (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      f i (i.insertNth (b i) x) = 0 := by
    apply hz i
    · apply hBH
      constructor <;> intro j <;> refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · simp only [Fin.insertNth_apply_same]; exact hab i
      · simpa using hx.1 k
      · simp
      · simpa using hx.2 k
    · intro hm
      have ht := (abs_lt.mp (hbnd _ hm i)).2
      simp [b] at ht
  have hback (i : Fin (n+1)) (hi : i ≠ Fin.last n) (x : Euclidean n)
      (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
      f i (i.insertNth (a i) x) = 0 := by
    apply hz i
    · apply hBH
      constructor <;> intro j <;> refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · simp
      · simpa using hx.1 k
      · simp only [Fin.insertNth_apply_same]; exact hab i
      · simpa using hx.2 k
    · intro hm
      have ht := (abs_lt.mp (hbnd _ hm i)).1
      simp [a, hi] at ht
  let face := Icc (a ∘ (Fin.last n).succAbove) (b ∘ (Fin.last n).succAbove)
  let tr (x : Euclidean n) := f (Fin.last n) ((Fin.last n).insertNth 0 x)
  have htr0 (x : Euclidean n) (hx : x ∉ face) : tr x = 0 := by
    apply hz (Fin.last n)
    · simp [halfSpaceSet]
    · intro hm
      apply hx
      constructor <;> intro j
      · have ht := (abs_lt.mp (hbnd _ hm j.castSucc)).1.le
        simpa [a, Fin.succAbove_last] using ht
      · have ht := (abs_lt.mp (hbnd _ hm j.castSucc)).2.le
        simpa [b, Fin.succAbove_last] using ht
  have htrcont : ContinuousOn tr face := by
    apply (hf (Fin.last n)).continuousOn.comp
      (continuous_const.finInsertNth (Fin.last n) continuous_id).continuousOn
    intro x _
    simp [halfSpaceSet]
  have htri : Integrable tr :=
    (htrcont.integrableOn_compact isCompact_Icc).integrable_of_forall_notMem_eq_zero htr0
  have htreq : (∫ x in face, tr x) = ∫ x, tr x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero htr0
  refine ⟨hdi, htri, ?_⟩
  change (∫ x in H, d x) = - ∫ x, tr x
  rw [hdeq]
  change (∫ x in Icc a b, ∑ i, D i x (Pi.single i 1)) = - ∫ x, tr x
  rw [hbox, Finset.sum_eq_single (Fin.last n)]
  · rw [setIntegral_eq_zero_of_forall_eq_zero (hfront (Fin.last n))]
    simpa [a, tr, face] using congrArg Neg.neg htreq
  · intro i _ hi
    rw [setIntegral_eq_zero_of_forall_eq_zero (hfront i),
      setIntegral_eq_zero_of_forall_eq_zero (hback i hi)]
    simp
  · simp

/-- The relative half-space result on actual alternating form fields. -/
theorem halfSpaceStokes_proof :
    Specs.SmoothManifolds.Integration.LocalStokes.halfSpaceStokesType := by
  intro n ω hlocal hs
  classical
  let H := halfSpaceSet (n+1)
  have hω : ContDiffOn ℝ 1 ω H := localExtensions_contDiffOn hlocal
  have hud : UniqueDiffOn ℝ H := uniqueDiffOn_halfSpaceSet (n+1)
  let g (i : Fin (n+1)) (x : Euclidean (n+1)) := ω x (i.removeNth (frame (n+1)))
  let f (i : Fin (n+1)) := signedOmittedCoefficient ω i
  have hg (i : Fin (n+1)) : ContDiffOn ℝ 1 (g i) H :=
    (ContinuousAlternatingMap.apply ℝ (Euclidean (n+1)) ℝ
      (i.removeNth (frame (n+1)))).contDiff.comp_contDiffOn hω
  have hf (i : Fin (n+1)) : ContDiffOn ℝ 1 (f i) H :=
    contDiffOn_const.mul (hg i)
  obtain ⟨K, hK, hKH, hz⟩ := relative_support_image H ω hs
  have hzero (i : Fin (n+1)) (x : Euclidean (n+1)) (hx : x ∈ H) (hxK : x ∉ K) :
      f i x = 0 := by
    simp [f, signedOmittedCoefficient, hz x hx hxK]
  obtain ⟨hdi, htri, hstokes⟩ := halfSpace_divergence f hf K hK hKH hzero
  have hd (x : Euclidean (n+1)) (hx : x ∈ H) : halfSpaceBulkCoefficient ω x =
      ∑ i, fderivWithin ℝ (f i) H x (frame (n+1) i) := by
    rw [halfSpaceBulkCoefficient,
      extDerivWithin_apply (hω.differentiableOn (by norm_num) x hx) (hud x hx)]
    apply Finset.sum_congr rfl
    intro i _
    change ((-1 : ℤ)^i.val) • fderivWithin ℝ (g i) H x (frame (n+1) i) =
      fderivWithin ℝ (fun y => (-1 : ℝ)^i.val * g i y) H x (frame (n+1) i)
    rw [fderivWithin_const_mul (hud x hx) ((hg i).differentiableOn (by norm_num) x hx)]
    simp [zsmul_eq_mul]
  have htrace (y : Euclidean n) : boundaryCoefficient ω y =
      - f (Fin.last n) ((Fin.last n).insertNth 0 y) := boundarySign_proof n ω y
  refine ⟨?_, ?_, ?_⟩
  · exact hdi.congr_fun (fun x hx => (hd x hx).symm) (by
      exact (isClosed_le continuous_const (continuous_apply (Fin.last n))).measurableSet)
  · have he : boundaryCoefficient ω =
        fun y => - f (Fin.last n) ((Fin.last n).insertNth 0 y) := funext htrace
    rw [he]
    exact htri.neg
  · calc
      (∫ x in H, halfSpaceBulkCoefficient ω x) =
          ∫ x in H, ∑ i, fderivWithin ℝ (f i) H x (frame (n+1) i) :=
        setIntegral_congr_fun
          (isClosed_le continuous_const (continuous_apply (Fin.last n))).measurableSet hd
      _ = - ∫ y, f (Fin.last n) ((Fin.last n).insertNth 0 y) := hstokes
      _ = ∫ y, boundaryCoefficient ω y := by
        simp_rw [htrace]
        rw [integral_neg]

/-- In dimension one the outward-first boundary integral is minus evaluation
at the left endpoint. The empty product Lebesgue measure has mass one. -/
theorem left_endpoint_integral (ω : CoordinateForm 1 0) :
    (∫ y : Euclidean 0, boundaryCoefficient ω y) = - ω 0 (fun i => Fin.elim0 i) := by
  have he (y : Euclidean 0) : boundaryCoefficient ω y = - ω 0 (fun i => Fin.elim0 i) := by
    have hy : (Fin.last 0).insertNth (0 : ℝ) y = (0 : Euclidean 1) := by
      funext i
      fin_cases i
      simp
    have hempty : (fun j : Fin 0 => frame 1 j.castSucc) =
        (fun i : Fin 0 => (Fin.elim0 i : Euclidean 1)) := Subsingleton.elim _ _
    change (-1 : ℝ)^1 * ω ((Fin.last 0).insertNth 0 y)
      (fun j : Fin 0 => frame 1 j.castSucc) = _
    rw [hy, hempty]
    ring
  have hvol : (volume : Measure (Euclidean 0)) = Measure.dirac (0 : Euclidean 0) :=
    Measure.volume_pi_eq_dirac (0 : Euclidean 0)
  rw [hvol]
  simpa using he 0

/-- Local Stokes in every positive dimension, with compact support relative to
its model and the outward-first boundary sign. -/
theorem local_stokes :
    Specs.SmoothManifolds.Integration.LocalStokes.local_stokesType :=
  ⟨fullSpaceStokes_proof, halfSpaceStokes_proof, boundarySign_proof⟩

end SmoothManifolds.LocalStokesResults
