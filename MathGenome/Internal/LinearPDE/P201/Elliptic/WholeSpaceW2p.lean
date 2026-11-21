import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WholeSpaceW2p
import MathGenome.Internal.FourierSobolev.P102.U3.RieszTransforms
import MathGenome.Internal.FourierSobolev.P102.U3.SchwartzFourier
import MathGenome.Internal.FourierSobolev.P102.U4.TestSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ContDiff FourierTransform ENNReal
namespace P201.Elliptic.WholeSpaceW2p
open P201Specs.Elliptic.WholeSpaceW2p

lemma schwartzHessian_apply {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ)
    (i j : Fin n) (x : P201.Space n) :
    schwartzHessian u i j x = HessianEntry (u : P201.Space n → ℂ) i j x := by
  rw [schwartzHessian, P102.U3.coordinatePartial_apply]
  symm
  have h := P102.U4.multiPartial_ofFn (u.smooth ⊤) ![i, j] x
  simpa [List.ofFn_succ, ← Multiset.cons_coe, Multiset.coe_singleton, HessianEntry, P201Specs.multiPartial,
    P102.U3.coordinateVector, P102.U4.coordinateVector, Function.comp_def] using h

lemma negativeLaplacianSchwartz_apply {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ)
    (x : P201.Space n) :
    negativeLaplacianSchwartz u x = -P201Specs.laplacian (u : P201.Space n → ℂ) x := by
  simp [negativeLaplacianSchwartz, schwartzHessian_apply, P201Specs.laplacian,
    P201Specs.laplacian, HessianEntry]

theorem schwartzBridge : P201Specs.Elliptic.WholeSpaceW2p.SchwartzBridgeStatement := by
  intro n u
  exact ⟨schwartzHessian_apply u, negativeLaplacianSchwartz_apply u⟩

lemma fourier_hessian {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ)
    (i j : Fin n) (ξ : P201.Space n) :
    (𝓕 (schwartzHessian u i j)) ξ =
      -(2 * Real.pi : ℂ)^2 * (ξ i : ℂ) * (ξ j : ℂ) * (𝓕 u) ξ := by
  change P102.U3.fourier n (P102.U3.coordinatePartial ![i, j] u) ξ = _
  rw [P102.U3.fourier_partial, P102.U3.polynomialMul_apply]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one]
  change _ = _ * _ * _ * P102.U3.fourier n u ξ
  calc
    _ = (2 * Real.pi : ℂ)^2 * Complex.I^2 * (ξ i : ℂ) * (ξ j : ℂ) *
        P102.U3.fourier n u ξ := by ring
    _ = _ := by rw [Complex.I_sq]; ring

lemma fourier_negativeLaplacian {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ)
    (ξ : P201.Space n) :
    (𝓕 (negativeLaplacianSchwartz u)) ξ =
      (2 * Real.pi : ℂ)^2 * (‖ξ‖ : ℂ)^2 * (𝓕 u) ξ := by
  change P102.U3.fourier n (-∑ i : Fin n, schwartzHessian u i i) ξ = _
  simp only [map_neg, map_sum, neg_apply, sum_apply]
  change -(∑ i : Fin n, (𝓕 (schwartzHessian u i i)) ξ) = _
  simp_rw [fourier_hessian]
  have hn : (‖ξ‖ : ℂ)^2 = ∑ i : Fin n, (ξ i : ℂ)^2 := by
    exact_mod_cast EuclideanSpace.real_norm_sq_eq ξ
  rw [hn, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change -(-(2 * Real.pi : ℂ)^2 * (ξ i : ℂ) * (ξ i : ℂ) * (𝓕 u) ξ) = _
  ring

lemma fourierL2_schwartz_ae {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ) :
    (P102.Specs.U3.Riesz.F2 n (u.toLp 2) : P201.Space n → ℂ) =ᵐ[volume]
      (𝓕 u : SchwartzMap (P201.Space n) ℂ) := by
  change (𝓕 (u.toLp 2) : MeasureTheory.Lp ℂ 2 volume) =ᵐ[volume] _
  rw [SchwartzMap.toLp_fourier_eq]
  exact (𝓕 u).coeFn_toLp 2

theorem l2Representation : P201Specs.Elliptic.WholeSpaceW2p.L2RepresentationStatement := by
  intro n hn u i j
  apply (P102.Specs.U3.Riesz.F2 n).injective
  apply MeasureTheory.Lp.ext
  have hi := P102.U3.RieszTransforms.canonical_multiplier hn i 0
    (P102.U3.Riesz.rieszL2 j ((negativeLaplacianSchwartz u).toLp 2))
  have hj := P102.U3.RieszTransforms.canonical_multiplier hn j 0
    ((negativeLaplacianSchwartz u).toLp 2)
  filter_upwards [hi, hj, fourierL2_schwartz_ae (negativeLaplacianSchwartz u),
    fourierL2_schwartz_ae (schwartzHessian u i j)] with ξ hiξ hjξ hlξ hhξ
  rw [hiξ, hjξ, hlξ, hhξ, fourier_negativeLaplacian, fourier_hessian]
  by_cases hξ : ξ = 0
  · simp [P102.Specs.U3.Riesz.symbolAtOrigin, hξ]
  · have hnorm : (‖ξ‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hξ
    simp only [P102.Specs.U3.Riesz.symbolAtOrigin, ite_eq_right hξ,
      P102.Specs.U3.Riesz.symbolValue, Complex.ofReal_div]
    field_simp
    ring_nf
    simp [Complex.I_sq]

theorem lpRepresentation : P201Specs.Elliptic.WholeSpaceW2p.LpRepresentationStatement := by
  intro n hn p R hR u i j
  let f := negativeLaplacianSchwartz u
  let g : P201.Space n → ℂ := P102.U3.Riesz.rieszL2 j (f.toLp 2)
  have hj := hR j f (f.memLp p.val) (f.memLp 2)
  have hgp : MemLp g p.val volume :=
    (memLp_congr_ae hj).mp (MeasureTheory.Lp.memLp (R j (f.toLp p.val)))
  have hg2 : MemLp g 2 volume := MeasureTheory.Lp.memLp _
  have hjp : hgp.toLp g = R j (f.toLp p.val) := by
    apply MeasureTheory.Lp.ext
    exact hgp.coeFn_toLp.trans hj.symm
  have hj2 : hg2.toLp g = P102.U3.Riesz.rieszL2 j (f.toLp 2) :=
    MeasureTheory.Lp.toLp_coeFn _ _
  have hi := hR i g hgp hg2
  rw [hjp, hj2] at hi
  change (R i (R j (f.toLp p.val)) : P201.Space n → ℂ) =ᵐ[volume]
    (P102.U3.Riesz.rieszL2 i (P102.U3.Riesz.rieszL2 j (f.toLp 2)) : P201.Space n → ℂ) at hi
  rw [l2Representation n hn u i j] at hi
  apply MeasureTheory.Lp.ext
  exact hi.trans (((schwartzHessian u i j).coeFn_toLp 2).trans
    ((schwartzHessian u i j).coeFn_toLp p.val).symm)

lemma rieszLp_exists {n : ℕ} (hn : 1 ≤ n) (p : P102.U2.CZLpData.Exponent) :
    ∃ R : Fin n → P102.U2.CZLpData.StrongOperator n p,
      ∀ i, P102.U2.CZLpData.Agrees (P102.U3.Riesz.rieszL2 i) p (R i) := by
  have hex (i : Fin n) : ∃ R : P102.U2.CZLpData.StrongOperator n p,
      P102.U2.CZLpData.Agrees (P102.U3.Riesz.rieszL2 i) p R := by
    obtain ⟨T, S, R, C₁, C, hm, _hT, _hcompat, _hweak, _huniq,
      _hnorm, hagree, _hpair, _hend, _hconv, _hunique⟩ :=
      P102.U3.RieszTransforms.full_theorem n hn i
    have hT : T = P102.U3.Riesz.rieszL2 i :=
      P102.U3.Riesz.multiplier_unique n hn i 0 0 T (P102.U3.Riesz.rieszL2 i)
        (hm 0) (P102.U3.RieszTransforms.canonical_multiplier hn i 0)
    exact ⟨R p, hT ▸ hagree p⟩
  exact Classical.axiomOfChoice hex

lemma schwartz_hessian_memLp {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ)
    (p : ℝ≥0∞) (i j : Fin n) : MemLp (HessianEntry (u : P201.Space n → ℂ) i j) p volume := by
  have he : (schwartzHessian u i j : P201.Space n → ℂ) = HessianEntry (u : P201.Space n → ℂ) i j :=
    funext (schwartzHessian_apply u i j)
  rw [← he]
  exact (schwartzHessian u i j).memLp p

lemma schwartz_laplacian_memLp {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ)
    (p : ℝ≥0∞) : MemLp (P201Specs.laplacian (u : P201.Space n → ℂ)) p volume := by
  have he : (negativeLaplacianSchwartz u : P201.Space n → ℂ) =
      -P201Specs.laplacian (u : P201.Space n → ℂ) := funext (negativeLaplacianSchwartz_apply u)
  have h := (negativeLaplacianSchwartz u).memLp p
  rw [he] at h
  exact (memLp_neg_iff).mp h

lemma negativeLaplacianSchwartz_norm {n : ℕ} (u : SchwartzMap (P201.Space n) ℂ)
    (p : ℝ≥0∞) : ‖(negativeLaplacianSchwartz u).toLp p‖ =
      (eLpNorm (P201Specs.laplacian (u : P201.Space n → ℂ)) p volume).toReal := by
  rw [SchwartzMap.norm_toLp]
  have he : (negativeLaplacianSchwartz u : P201.Space n → ℂ) =
      -P201Specs.laplacian (u : P201.Space n → ℂ) := funext (negativeLaplacianSchwartz_apply u)
  rw [he, eLpNorm_neg]

lemma schwartz_estimate {n : ℕ} (hn : 1 ≤ n) (p : P102.U2.CZLpData.Exponent) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SchwartzMap (P201.Space n) ℂ),
      hessianLpNorm p.val (u : P201.Space n → ℂ) ≤
        C * (eLpNorm (P201Specs.laplacian (u : P201.Space n → ℂ)) p.val volume).toReal := by
  obtain ⟨R, hR⟩ := rieszLp_exists hn p
  refine ⟨∑ i : Fin n, ∑ j : Fin n, ‖R i‖ * ‖R j‖, by positivity, ?_⟩
  intro u
  have hentry (i j : Fin n) : ‖(schwartzHessian u i j).toLp p.val‖ ≤
      (‖R i‖ * ‖R j‖) * ‖(negativeLaplacianSchwartz u).toLp p.val‖ := by
    rw [← lpRepresentation n hn p R hR u i j]
    exact ((R i).le_opNorm _).trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left ((R j).le_opNorm _)
        (norm_nonneg (R i)))
  have he : hessianLpNorm p.val (u : P201.Space n → ℂ) =
      ∑ i : Fin n, ∑ j : Fin n, ‖(schwartzHessian u i j).toLp p.val‖ := by
    unfold hessianLpNorm
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [SchwartzMap.norm_toLp]
    congr 2
    exact (funext (schwartzHessian_apply u i j)).symm
  rw [he, ← negativeLaplacianSchwartz_norm u p.val, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _ => hentry i j)

theorem complexEstimate : P201Specs.Elliptic.WholeSpaceW2p.ComplexEstimateStatement := by
  intro n hn p hp
  let q : P102.U2.CZLpData.Exponent :=
    ⟨ENNReal.ofReal p, by simpa using (ENNReal.ofReal_lt_ofReal_iff (lt_trans zero_lt_one hp)).mpr hp,
      ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC, hbound⟩ := schwartz_estimate hn q
  refine ⟨C, hC, ?_⟩
  intro u hu hc
  let v : SchwartzMap (P201.Space n) ℂ := hc.toSchwartzMap (hu.of_le (by simp))
  exact ⟨schwartz_hessian_memLp v q.val, schwartz_laplacian_memLp v q.val, hbound v⟩

lemma partialWord_ofReal {n : ℕ} {u : P201.Space n → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (l : List (Fin n)) :
    P102.U4.partialWord (fun x => (u x : ℂ)) l =
      fun x => ((P102.U4.partialWord (𝕜 := ℝ) u l x : ℝ) : ℂ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    simp only [P102.U4.partialWord, ih]
    have hd := (P102.U4.partialWord_contDiff hu l).differentiable (by simp) x
    have he := (Complex.ofRealCLM.hasFDerivAt).comp x hd.hasFDerivAt
    change fderiv ℝ (Complex.ofRealCLM ∘ P102.U4.partialWord u l) x _ = _
    rw [he.fderiv]
    rfl

lemma multiPartial_ofReal {n : ℕ} {u : P201.Space n → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (α : P201.MultiIndex n) (x : P201.Space n) :
    P201Specs.multiPartial (fun y => (u y : ℂ)) α x = ((P201Specs.multiPartial (𝕜 := ℝ) u α x : ℝ) : ℂ) :=
  congrFun (partialWord_ofReal hu (α.sort (· ≤ ·))) x

lemma laplacian_ofReal {n : ℕ} {u : P201.Space n → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : P201.Space n) :
    P201Specs.laplacian (fun y => (u y : ℂ)) x = ((P201Specs.laplacian (𝕜 := ℝ) u x : ℝ) : ℂ) := by
  simp only [P201Specs.laplacian, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => multiPartial_ofReal hu _ x)

lemma eLpNorm_complexify {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : ℝ≥0∞) (f : α → ℝ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => (f x : ℂ)) p μ = eLpNorm f p μ := by
  apply eLpNorm_congr_norm_ae (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hf) hf
  exact Filter.Eventually.of_forall (fun x => Complex.norm_real (f x))

theorem realEstimate : P201Specs.Elliptic.WholeSpaceW2p.RealEstimateStatement := by
  intro n hn p hp
  obtain ⟨C, hC, hbound⟩ := complexEstimate n hn p hp
  refine ⟨C, hC, ?_⟩
  intro u hu hc
  let v : P201.Space n → ℂ := fun x => (u x : ℂ)
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := Complex.ofRealCLM.contDiff.comp hu
  have hvc : HasCompactSupport v := hc.comp_left (g := ((↑) : ℝ → ℂ)) rfl
  obtain ⟨hh, hl, hb⟩ := hbound v hv hvc
  have he (i j : Fin n) : HessianEntry v i j =
      fun x => ((HessianEntry (𝕜 := ℝ) u i j x : ℝ) : ℂ) := funext (multiPartial_ofReal hu _)
  have hel : P201Specs.laplacian v = fun x => ((P201Specs.laplacian (𝕜 := ℝ) u x : ℝ) : ℂ) :=
    funext (laplacian_ofReal hu)
  have hhr (i j : Fin n) : MemLp (HessianEntry u i j) (ENNReal.ofReal p) volume := by
    have h := Complex.reCLM.comp_memLp' (hh i j)
    change MemLp (fun x => (HessianEntry v i j x).re) (ENNReal.ofReal p) volume at h
    simpa only [he, Complex.ofReal_re] using h
  have hlr : MemLp (P201Specs.laplacian u) (ENNReal.ofReal p) volume := by
    have h := Complex.reCLM.comp_memLp' hl
    change MemLp (fun x => (P201Specs.laplacian v x).re) (ENNReal.ofReal p) volume at h
    have heR : (fun x => (P201Specs.laplacian v x).re) = P201Specs.laplacian u := by
      funext x
      exact (congrArg Complex.re (congrFun hel x)).trans (Complex.ofReal_re _)
    rw [heR] at h
    exact h
  refine ⟨hhr, hlr, ?_⟩
  have hnorm : hessianLpNorm (ENNReal.ofReal p) v = hessianLpNorm (ENNReal.ofReal p) u := by
    unfold hessianLpNorm
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [he, eLpNorm_complexify volume _ _ (hhr i j).aestronglyMeasurable]
  rw [hnorm, hel, eLpNorm_complexify volume _ _ hlr.aestronglyMeasurable] at hb
  exact hb

/-- The component-sum estimate controls the usual Frobenius Lᵖ norm. -/
lemma hessian_memLp_and_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : P201.Space n → 𝕜) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hh : ∀ i j : Fin n, MemLp (HessianEntry u i j) p volume) :
    MemLp (hessian u) p volume ∧
      (eLpNorm (hessian u) p volume).toReal ≤ hessianLpNorm p u := by
  let piece (ij : Fin n × Fin n) : P201.Space n → EuclideanSpace 𝕜 (Fin n × Fin n) :=
    fun x => HessianEntry u ij.1 ij.2 x • EuclideanSpace.single ij (1 : 𝕜)
  have hpiece (ij : Fin n × Fin n) : MemLp (piece ij) p volume :=
    ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (EuclideanSpace.single ij (1 : 𝕜))).comp_memLp'
      (hh ij.1 ij.2)
  have he : hessian u = ∑ ij : Fin n × Fin n, piece ij := by
    funext x
    apply PiLp.ext
    intro ij
    simp [hessian, piece, Pi.single_apply, mul_ite]
  have hm : MemLp (hessian u) p volume := by
    rw [he]
    exact memLp_finsetSum' Finset.univ (fun ij _ => hpiece ij)
  refine ⟨hm, ?_⟩
  have hnorm (ij : Fin n × Fin n) : eLpNorm (piece ij) p volume =
      eLpNorm (HessianEntry u ij.1 ij.2) p volume := by
    apply eLpNorm_congr_norm_ae (hpiece ij).aestronglyMeasurable (hh ij.1 ij.2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by simp [piece, norm_smul, PiLp.norm_single])
  change lpNorm (hessian u) p volume ≤ _
  rw [he]
  calc
    _ ≤ ∑ ij : Fin n × Fin n, lpNorm (piece ij) p volume :=
      lpNorm_sum_le (fun ij _ => hpiece ij) hp
    _ = hessianLpNorm p u := by
      simp only [← toReal_eLpNorm, hnorm, Fintype.sum_prod_type, hessianLpNorm]

theorem frobeniusEstimate : P201Specs.Elliptic.WholeSpaceW2p.FrobeniusEstimateStatement := by
  intro n hn p hp
  obtain ⟨C, hC, hbound⟩ := realEstimate n hn p hp
  refine ⟨C, hC, ?_⟩
  intro u hu hc
  obtain ⟨hh, hl, hb⟩ := hbound u hu hc
  have hq : 1 ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨hm, hnorm⟩ := hessian_memLp_and_norm_le u _ hq hh
  exact ⟨hm, hl, hnorm.trans hb⟩

end P201.Elliptic.WholeSpaceW2p
