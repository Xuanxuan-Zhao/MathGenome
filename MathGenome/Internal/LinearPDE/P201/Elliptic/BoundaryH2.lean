import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.BoundaryH2
import MathGenome.Internal.LinearPDE.P201.Elliptic.InteriorH2
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Affine
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatZeroTrace
import MathGenome.Internal.FourierSobolev.P102.U4.Rademacher
import MathGenome.Internal.FourierSobolev.P102.U4.BiLipschitzPullback

/-! Local boundary H² regularity for C¹,¹ domains. The proof establishes
the Sobolev coordinate bridge, tangential difference estimates and normal
derivative recovery, including dimension one.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped InnerProductSpace NNReal ENNReal Topology
namespace P201.BoundaryH2

abbrev conjugateCoefficient : P201Specs.BoundaryH2.conjugateCoefficientType :=
  @P201Specs.BoundaryH2.conjugateCoefficient

theorem conjugatePairing : P201Specs.BoundaryH2.conjugatePairingStatement := by
  intro n J A ξ ζ
  change inner ℝ (J (A (ContinuousLinearMap.adjoint J ξ))) ζ = _
  exact (ContinuousLinearMap.adjoint_inner_right J _ _).symm

theorem conjugateNorm : P201Specs.BoundaryH2.conjugateNormStatement := by
  intro n J A
  calc
    ‖P201Specs.BoundaryH2.conjugateCoefficient J A‖ ≤
        ‖J‖ * (‖A‖ * ‖ContinuousLinearMap.adjoint J‖) :=
      (J.opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_left (A.opNorm_comp_le _) (norm_nonneg _))
    _ = ‖J‖ ^ 2 * ‖A‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      ring

theorem conjugateSymmetry : P201Specs.BoundaryH2.conjugateSymmetryStatement := by
  intro n J A hA ξ ζ
  rw [conjugatePairing, hA]
  change inner ℝ (ContinuousLinearMap.adjoint J ξ)
    (A (ContinuousLinearMap.adjoint J ζ)) =
      inner ℝ ξ (J (A (ContinuousLinearMap.adjoint J ζ)))
  exact ContinuousLinearMap.adjoint_inner_left J _ _

theorem inverseAdjointBound : P201Specs.BoundaryH2.inverseAdjointBoundStatement := by
  intro n J E h ξ
  have hi : ContinuousLinearMap.adjoint E (ContinuousLinearMap.adjoint J ξ) = ξ := by
    have ha := congrArg (fun T : Space n →L[ℝ] Space n =>
      ContinuousLinearMap.adjoint T) h
    simpa only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using congrArg (fun T => T ξ) ha
  calc
    ‖ξ‖ = ‖ContinuousLinearMap.adjoint E (ContinuousLinearMap.adjoint J ξ)‖ :=
      congrArg norm hi.symm
    _ ≤ ‖ContinuousLinearMap.adjoint E‖ * ‖ContinuousLinearMap.adjoint J ξ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]

theorem conjugateDifference : P201Specs.BoundaryH2.conjugateDifferenceStatement := by
  intro n J K A D N M hN hM hJ hK hA hD
  have hs : P201Specs.BoundaryH2.conjugateCoefficient J A -
      P201Specs.BoundaryH2.conjugateCoefficient K D =
      (J - K).comp (A.comp (ContinuousLinearMap.adjoint J)) +
      K.comp ((A - D).comp (ContinuousLinearMap.adjoint J)) +
      K.comp (D.comp (ContinuousLinearMap.adjoint (J - K))) := by
    ext ξ
    simp only [P201Specs.BoundaryH2.conjugateCoefficient,
      ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_sub]
    abel
  have hb (P Q R : Space n →L[ℝ] Space n) :
      ‖P.comp (Q.comp R)‖ ≤ ‖P‖ * ‖Q‖ * ‖R‖ :=
    (P.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
      (Q.opNorm_comp_le _) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)
  rw [hs]
  calc
    _ ≤ ‖(J - K).comp (A.comp (ContinuousLinearMap.adjoint J))‖ +
        ‖K.comp ((A - D).comp (ContinuousLinearMap.adjoint J))‖ +
        ‖K.comp (D.comp (ContinuousLinearMap.adjoint (J - K)))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖J - K‖ * ‖A‖ * ‖ContinuousLinearMap.adjoint J‖ +
        ‖K‖ * ‖A - D‖ * ‖ContinuousLinearMap.adjoint J‖ +
        ‖K‖ * ‖D‖ * ‖ContinuousLinearMap.adjoint (J - K)‖ :=
      add_le_add (add_le_add (hb _ _ _) (hb _ _ _)) (hb _ _ _)
    _ = ‖J - K‖ * ‖A‖ * ‖J‖ + ‖K‖ * ‖A - D‖ * ‖J‖ +
        ‖K‖ * ‖D‖ * ‖J - K‖ := by simp only [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖J - K‖ * M * N + N * ‖A - D‖ * N + N * M * ‖J - K‖ := by
      gcongr
    _ = _ := by ring

theorem conjugateLipschitz : P201Specs.BoundaryH2.conjugateLipschitzStatement := by
  intro n S J A N M LJ LA hJ hA hLJ hLA
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm]
  calc
    _ ≤ 2 * N * M * ‖J x - J y‖ + N ^ 2 * ‖A x - A y‖ :=
      conjugateDifference (J x) (J y) (A x) (A y) N M
        N.coe_nonneg M.coe_nonneg (hJ x hx) (hJ y hy) (hA x hx) (hA y hy)
    _ ≤ 2 * N * M * (LJ * dist x y) + N ^ 2 * (LA * dist x y) := by
      gcongr
      · exact hLJ.norm_sub_le hx hy
      · exact hLA.norm_sub_le hx hy
    _ = _ := by push_cast; ring

theorem conjugateEllipticity :
    P201Specs.BoundaryH2.conjugateEllipticityStatement := by
  intro n J A theta K htheta hK hA hJ ξ
  rw [conjugatePairing]
  have hs : ‖ξ‖ ^ 2 ≤ K ^ 2 * ‖ContinuousLinearMap.adjoint J ξ‖ ^ 2 := by
    have h := sq_le_sq₀ (norm_nonneg ξ)
      (mul_nonneg hK.le (norm_nonneg _)) |>.mpr (hJ ξ)
    simpa only [mul_pow] using h
  calc
    theta / K ^ 2 * ‖ξ‖ ^ 2 ≤
        theta / K ^ 2 * (K ^ 2 * ‖ContinuousLinearMap.adjoint J ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg htheta.le (sq_nonneg K))
    _ = theta * ‖ContinuousLinearMap.adjoint J ξ‖ ^ 2 := by
      field_simp
    _ ≤ _ := hA _

theorem normalCoefficient : P201Specs.BoundaryH2.normalCoefficientStatement := by
  intro m B theta hB
  have h := hB (coordinate (m + 1) (Fin.last m))
  simpa only [P102.U4.DifferenceQuotient.norm_coordinateVector,
    one_pow, mul_one] using h

theorem h2Restriction : P201Specs.BoundaryH2.h2RestrictionStatement := by
  intro n V U hUV v g B hB hg hgB
  let u := InteriorH2.restrictLp hUV (hUnderlying V 1 v)
  let d : Fin n → Lp ℝ U 2 := fun j =>
    InteriorH2.restrictLp hUV (hFirstDerivative v j)
  have hd (j : Fin n) : distributionDerivative {j} (regularDistribution U u) =
      regularDistribution U (d j) := by
    dsimp only [u, d]
    rw [InteriorH2.regular_restrictLp, InteriorH2.regular_restrictLp]
    apply P102.U4.DifferenceQuotient.weak_derivative_restrict hUV
      (P102.U4.domainLp_locallyIntegrable V 2 _)
      (P102.U4.domainLp_locallyIntegrable V 2 _)
    exact hilbertDerivativeDistribution V 1 v ⟨{j}, by simp⟩
  have hdg (j k : Fin n) : distributionDerivative {k} (regularDistribution U (d j)) =
      regularDistribution U (g j k) := by
    dsimp only [d]
    rw [InteriorH2.regular_restrictLp]
    exact hg j k
  have hcoord (α : P102.U4.SobolevIndex n 1) :
      ‖P102.U4.sobolevDerivative ((hToW ℝ V 1) v) α‖ ≤ ‖v‖ := by
    change ‖v.val α‖ ≤ ‖v.val‖
    exact PiLp.norm_apply_le _ _
  have hu : ‖u‖ ≤ ‖v‖ := (InteriorH2.restrictLp_norm_le hUV _).trans (hcoord _)
  have hdn (j : Fin n) : ‖d j‖ ≤ ‖v‖ :=
    (InteriorH2.restrictLp_norm_le hUV _).trans (hcoord ⟨{j}, by simp⟩)
  obtain ⟨w, hw, hnorm⟩ := InteriorH2.h2FromWeakDerivatives U u d g (‖v‖ + B) hd hdg
    (hu.trans (le_add_of_nonneg_right hB))
    (fun j => (hdn j).trans (le_add_of_nonneg_right hB))
    (fun j k => (hgB j k).trans (le_add_of_nonneg_left (norm_nonneg v)))
  refine ⟨w, ?_, hnorm⟩
  rw [hw]
  exact InteriorH2.restrictLp_ae hUV _

theorem directionalProduct : P201Specs.BoundaryH2.directionalProductStatement := by
  intro n U j a da u du ha hda hu hdu hea heu hau hder
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  obtain ⟨f, haf, hf⟩ := (P102.U4.acl_characterization n hn ℝ U j a da ha hda).mp hea
  obtain ⟨g, hug, hg⟩ := (P102.U4.acl_characterization n hn ℝ U j u du hu hdu).mp heu
  apply P102.U4.acl_converse n hn ℝ U j _ _ hau hder
  refine ⟨fun x => f x * g x, haf.mul hug, ?_⟩
  filter_upwards [hf, hg, P102.U4.ACL.ae_on_fibers j haf,
    P102.U4.ACL.ae_on_fibers j hug] with z hfz hgz haz huz
  refine ⟨?_, ?_⟩
  · intro c d hcd
    exact (hfz.1 c d hcd).mul (hgz.1 c d hcd)
  · filter_upwards [hfz.2, hgz.2, haz, huz] with t hft hgt hat hut
    rw [hat, hut]
    convert hft.mul hgt using 1 <;> ring

/-- The actual scalar Lipschitz representative has the expected derivative on
almost every coordinate line. No smoothness beyond Lipschitz is used. -/
private lemma lipschitz_scalar_on_lines {n : ℕ} (U : Domain n) (j : Fin n)
    (a : Space n → ℝ) {L : ℝ≥0} (hL : LipschitzOnWith L a U) :
    ∀ᵐ z : P102.U4.ACL.Transverse j ∂volume,
      P102.U4.ACL.LocallyAC (fun t => a (P102.U4.ACL.line j z t))
        (P102.U4.ACL.fiber U j z) ∧
      ∀ᵐ t ∂volume.restrict (P102.U4.ACL.fiber U j z),
        HasDerivAt (fun s => a (P102.U4.ACL.line j z s))
          (fderiv ℝ a (P102.U4.ACL.line j z t) (coordinate n j)) t := by
  have hd : ∀ᵐ x ∂domainMeasure U, DifferentiableAt ℝ a x := by
    filter_upwards [hL.ae_differentiableWithinAt U.isOpen.measurableSet,
      ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
    exact hx.differentiableAt (U.isOpen.mem_nhds hxU)
  filter_upwards [P102.U4.ACL.ae_on_fibers j hd] with z hz
  refine ⟨?_, ?_⟩
  · intro c d hcd
    exact (hL.comp (P102.U4.acl_line_lipschitz j z).lipschitzOnWith hcd).absolutelyContinuousOnInterval
  · filter_upwards [hz] with t ht
    exact ht.hasFDerivAt.comp_hasDerivAt t (P102.U4.ACL.line_hasDerivAt j z t)

private lemma reciprocal_lipschitz {n : ℕ} (U : Domain n) (b : Space n → ℝ)
    {L : ℝ≥0} {theta : ℝ} (htheta : 0 < theta)
    (hL : LipschitzOnWith L b U) (hb : ∀ x ∈ U, theta ≤ b x) :
    LipschitzOnWith (L * ⟨theta⁻¹ ^ 2, sq_nonneg _⟩)
      (fun x => (b x)⁻¹) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx0 : 0 < b x := htheta.trans_le (hb x hx)
  have hy0 : 0 < b y := htheta.trans_le (hb y hy)
  rw [Real.dist_eq, inv_sub_inv' hx0.ne' hy0.ne', abs_mul, abs_mul,
    abs_inv, abs_inv, abs_of_pos hx0, abs_of_pos hy0]
  calc
    (b x)⁻¹ * |b y - b x| * (b y)⁻¹ ≤
        theta⁻¹ * ((L : ℝ) * dist x y) * theta⁻¹ := by
      gcongr
      · exact hb x hx
      · simpa only [Real.dist_eq, abs_sub_comm] using hL.dist_le_mul x hx y hy
      · exact hb y hy
    _ = _ := by change _ = ((L : ℝ) * theta⁻¹ ^ 2) * dist x y; ring

theorem normalRecovery : P201Specs.BoundaryH2.normalRecoveryStatement := by
  intro n U j b M L theta htheta hL hb hM v R heq
  let μ := domainMeasure U
  let db : Space n → ℝ := fun x => fderiv ℝ b x (coordinate n j)
  have hbm : AEStronglyMeasurable b μ :=
    hL.continuousOn.aestronglyMeasurable U.isOpen.measurableSet
  have hdbm : AEStronglyMeasurable db μ := by
    exact ((ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).continuous.measurable.comp
      (measurable_fderiv ℝ b)).aestronglyMeasurable
  have hdbb : ∀ᵐ x ∂μ, |db x| ≤ (L : ℝ) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    change ‖fderiv ℝ b x (coordinate n j)‖ ≤ (L : ℝ)
    calc
      _ ≤ ‖fderiv ℝ b x‖ * ‖coordinate n j‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * 1 := by
        rw [P102.U4.DifferenceQuotient.norm_coordinateVector]
        exact mul_le_mul_of_nonneg_right
          (norm_fderiv_le_of_lipschitzOn ℝ (U.isOpen.mem_nhds hx) hL) zero_le_one
      _ = _ := mul_one _
  have hbM : ∀ᵐ x ∂μ, |b x| ≤ (M : ℝ) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact hM x hx
  have hqm := InteriorH2.scalarMultiply_memLp v b hbm hbM
  let q : Lp ℝ U 2 := hqm.toLp (fun x => b x * v x)
  have hq : (q : Space n → ℝ) =ᵐ[μ] (fun x => b x * v x) := hqm.coeFn_toLp
  have hkv := InteriorH2.scalarMultiply_memLp v db hdbm hdbb
  let kv : Lp ℝ U 2 := hkv.toLp (fun x => db x * v x)
  have hkvEq : (kv : Space n → ℝ) =ᵐ[μ] (fun x => db x * v x) := hkv.coeFn_toLp
  let s : Lp ℝ U 2 := R - kv
  let a : Space n → ℝ := fun x => (b x)⁻¹
  have haL := reciprocal_lipschitz U b htheta hL hb
  have ham : AEStronglyMeasurable a μ :=
    haL.continuousOn.aestronglyMeasurable U.isOpen.measurableSet
  have hab : ∀ᵐ x ∂μ, |a x| ≤ theta⁻¹ := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    dsimp only [a]
    rw [abs_inv, abs_of_pos (htheta.trans_le (hb x hx))]
    exact (inv_le_inv₀ (htheta.trans_le (hb x hx)) htheta).mpr (hb x hx)
  have hdm := InteriorH2.scalarMultiply_memLp s a ham hab
  let d : Lp ℝ U 2 := hdm.toLp (fun x => a x * s x)
  have hd : (d : Space n → ℝ) =ᵐ[μ] (fun x =>
      (R x - db x * v x) / b x) := by
    filter_upwards [hdm.coeFn_toLp, Lp.coeFn_sub R kv, hkvEq] with x hx hs hk
    change d x = a x * s x at hx
    change s x = R x - kv x at hs
    rw [hx, hs, hk]
    dsimp only [a]
    ring
  have hnorm : ‖d‖ ≤ theta⁻¹ * (‖R‖ + (L : ℝ) * ‖v‖) := by
    calc
      ‖d‖ ≤ theta⁻¹ * ‖s‖ := InteriorH2.scalarMultiply_norm_le s a ham hab
      _ ≤ theta⁻¹ * (‖R‖ + ‖kv‖) := by
        exact mul_le_mul_of_nonneg_left (norm_sub_le R kv) (inv_nonneg.mpr htheta.le)
      _ ≤ _ := by
        gcongr
        exact InteriorH2.scalarMultiply_norm_le v db hdbm hdbb
  have hqD : distributionDerivative {j} (regularDistribution U q) =
      regularDistribution U R := by
    have hreg : regularDistribution U (q : Space n → ℝ) =
        regularDistribution U (fun x => b x * v x) :=
      (P102.U4.regular_injectivity n ℝ U _ _
        (P102.U4.domainLp_locallyIntegrable U 2 q)
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          (hqm.locallyIntegrable (by norm_num)))).mpr hq
    rw [hreg]
    exact heq
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  obtain ⟨f, hqf, hf⟩ := (P102.U4.acl_characterization n hn ℝ U j q R
    (P102.U4.domainLp_locallyIntegrable U 2 q)
    (P102.U4.domainLp_locallyIntegrable U 2 R)).mp hqD
  have hvf : (v : Space n → ℝ) =ᵐ[μ] (fun x => a x * f x) := by
    filter_upwards [hq, hqf, ae_restrict_mem U.isOpen.measurableSet] with x hx hxf hxU
    dsimp only [a]
    rw [← hxf, hx, ← mul_assoc, inv_mul_cancel₀ (htheta.trans_le (hb x hxU)).ne', one_mul]
  refine ⟨d, ?_, hd, hnorm⟩
  apply P102.U4.acl_converse n hn ℝ U j v d
    (P102.U4.domainLp_locallyIntegrable U 2 v)
    (P102.U4.domainLp_locallyIntegrable U 2 d)
  refine ⟨fun x => a x * f x, hvf, ?_⟩
  filter_upwards [hf, lipschitz_scalar_on_lines U j b hL,
    P102.U4.ACL.ae_on_fibers j hq,
    P102.U4.ACL.ae_on_fibers j hqf,
    P102.U4.ACL.ae_on_fibers j hd,
    P102.U4.ACL.ae_on_fibers j (ae_restrict_mem U.isOpen.measurableSet)]
    with z hfz hbz hqz hqfz hdz hUz
  refine ⟨?_, ?_⟩
  · intro c e hce
    have haAC : AbsolutelyContinuousOnInterval
        (fun t => a (P102.U4.ACL.line j z t)) c e :=
      (haL.comp (P102.U4.acl_line_lipschitz j z).lipschitzOnWith hce).absolutelyContinuousOnInterval
    exact haAC.mul (hfz.1 c e hce)
  · filter_upwards [hfz.2, hbz.2, hqz, hqfz, hdz, hUz] with t hft hbt hqt hqft hdt htU
    let x := P102.U4.ACL.line j z t
    have hx0 : b x ≠ 0 := (htheta.trans_le (hb x htU)).ne'
    have hat : HasDerivAt (fun s => a (P102.U4.ACL.line j z s))
        (-(db x) / (b x) ^ 2) t := hbt.inv hx0
    have hprod := hat.mul hft
    convert hprod using 1
    rw [hdt, ← hqft, hqt]
    dsimp only [a, db, x]
    field_simp <;> ring

private lemma matrix_entry_bound {n : ℕ} (T : Space n →L[ℝ] Space n)
    (i j : Fin n) : |T (coordinate n j) i| ≤ ‖T‖ := by
  calc
    _ ≤ ‖T (coordinate n j)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖coordinate n j‖ := T.le_opNorm _
    _ = _ := by rw [P102.U4.DifferenceQuotient.norm_coordinateVector, mul_one]

private lemma matrix_entry_lipschitz {n : ℕ} (U : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (i j : Fin n) {L : ℝ≥0}
    (hL : LipschitzOnWith L A U) :
    LipschitzOnWith L (fun x => A x (coordinate n j) i) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  calc
    _ = |(A x - A y) (coordinate n j) i| := rfl
    _ ≤ ‖A x - A y‖ := matrix_entry_bound _ i j
    _ ≤ _ := hL.norm_sub_le hx hy

private lemma one_dimensional_vector (z : Space 1) : z = z 0 • coordinate 1 0 := by
  ext i
  fin_cases i
  simp [P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]

private lemma one_dimensional_energy (A : Space 1 →L[ℝ] Space 1)
    (z t : Space 1) : inner ℝ (A z) t = A (coordinate 1 0) 0 * z 0 * t 0 := by
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_one, RCLike.inner_apply, conj_trivial]
  conv_lhs => arg 2; arg 1; rw [one_dimensional_vector z]
  simp only [map_smul, smul_eq_mul, PiLp.smul_apply]
  ring

theorem dimensionOneEstimate : P201Specs.BoundaryH2.dimensionOneEstimateStatement := by
  intro U M L theta htheta
  let K : ℝ := 1 + theta⁻¹ * (1 + (L : ℝ))
  let N : ℝ := Fintype.card (P102.U4.SobolevIndex 1 2)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨P102.U4.zeroSobolevIndex 1 2⟩
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨N * K, mul_pos hN hK, ?_⟩
  intro A hA v f heq
  let b : Space 1 → ℝ := fun x => A x (coordinate 1 0) 0
  have hbL : LipschitzOnWith L b U := matrix_entry_lipschitz U A 0 0 hA.2.1
  have hbp : ∀ x ∈ U, theta ≤ b x := by
    intro x hx
    have h := hA.2.2 x hx (coordinate 1 0)
    rw [P102.U4.DifferenceQuotient.norm_coordinateVector, one_pow, mul_one] at h
    simpa only [b, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.inner_basisFun_real] using h
  have hbM : ∀ x ∈ U, |b x| ≤ (M : ℝ) := fun x hx =>
    (matrix_entry_bound (A x) 0 0).trans (hA.1 x hx)
  have hbm : AEStronglyMeasurable b (domainMeasure U) :=
    hbL.continuousOn.aestronglyMeasurable U.isOpen.measurableSet
  have hbMv : ∀ᵐ x ∂domainMeasure U, |b x| ≤ (M : ℝ) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact hbM x hx
  have hq := InteriorH2.scalarMultiply_memLp (hFirstDerivative v 0) b hbm hbMv
  have hqLI : LocallyIntegrableOn (fun x => b x * hFirstDerivative v 0 x) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hq.locallyIntegrable (by norm_num))
  have hfluxD : distributionDerivative {(0 : Fin 1)}
      (regularDistribution U (fun x => b x * hFirstDerivative v 0 x)) =
      regularDistribution U (-f) := by
    apply (P102.U4.ACL.weak_iff_test_identity 0 hqLI
      (P102.U4.domainLp_locallyIntegrable U 2 (-f))).mpr
    intro φ
    have h := heq φ
    have hleft : (∫ x in U, inner ℝ (A x (hGradient v x)) (gradient φ x)) =
        ∫ x, P102.U4.testPartialWord U [0] φ x * (b x * hFirstDerivative v 0 x) := by
      calc
        _ = ∫ x in U, (b x * hFirstDerivative v 0 x) *
            P102.U4.testPartialWord U [0] φ x := by
          apply integral_congr_ae
          filter_upwards [InteriorH2.hGradient_ae v] with x hx
          rw [one_dimensional_energy, hx]
          rfl
        _ = ∫ x, (b x * hFirstDerivative v 0 x) *
            P102.U4.testPartialWord U [0] φ x := P102.U4.setIntegral_mul_test U _ _
        _ = _ := by congr 1; funext x; ring
    have hright : (∫ x in U, f x * φ x) = ∫ x, φ x * f x := by
      rw [P102.U4.setIntegral_mul_test]
      congr 1
      funext x
      exact mul_comm _ _
    have hneg : (∫ x, φ x * (-f) x) = -(∫ x, φ x * f x) := by
      have hnegpoint : ∀ᵐ x ∂domainMeasure U, (-f) x * φ x = -(f x * φ x) := by
        filter_upwards [Lp.coeFn_neg f] with x hx
        simp only [hx, Pi.neg_apply, neg_mul]
      have hnegset : (∫ x in U, (-f) x * φ x) = -(∫ x in U, f x * φ x) := by
        rw [integral_congr_ae hnegpoint, integral_neg]
      rw [P102.U4.setIntegral_mul_test, P102.U4.setIntegral_mul_test] at hnegset
      calc
        _ = ∫ x, (-f) x * φ x := integral_congr_ae (Filter.Eventually.of_forall
          fun x => mul_comm _ _)
        _ = -(∫ x, f x * φ x) := hnegset
        _ = _ := congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall
          fun x => mul_comm _ _))
    rw [hneg, ← hright, ← h, hleft]
  obtain ⟨d, hd, _, hdB⟩ := normalRecovery U 0 b M L theta htheta hbL hbp hbM
    (hFirstDerivative v 0) (-f) hfluxD
  have hg (j k : Fin 1) : distributionDerivative {k}
      (regularDistribution U (hFirstDerivative v j)) = regularDistribution U d := by
    fin_cases j
    fin_cases k
    exact hd
  have hv0 : ‖hUnderlying U 1 v‖ ≤ ‖v‖ := PiLp.norm_apply_le _ _
  have hv1 (j : Fin 1) : ‖hFirstDerivative v j‖ ≤ ‖v‖ :=
    InteriorH2.firstDerivative_norm_le U v j
  have hd_bound : ‖d‖ ≤ K * (‖v‖ + ‖f‖) := by
    apply hdB.trans
    rw [norm_neg]
    have ht : 0 ≤ theta⁻¹ := inv_nonneg.mpr htheta.le
    calc
      _ ≤ theta⁻¹ * (‖f‖ + (L : ℝ) * ‖v‖) := by gcongr; exact hv1 0
      _ ≤ theta⁻¹ * ((1 + (L : ℝ)) * (‖v‖ + ‖f‖)) := by
        apply mul_le_mul_of_nonneg_left _ ht
        nlinarith [norm_nonneg v, mul_nonneg L.coe_nonneg (norm_nonneg f)]
      _ ≤ K * (‖v‖ + ‖f‖) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (by positivity)
  have hv_bound : ‖v‖ ≤ K * (‖v‖ + ‖f‖) := by
    have hK1 : 1 ≤ K := by
      dsimp only [K]
      exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr htheta.le) (by positivity))
    calc
      ‖v‖ ≤ ‖v‖ + ‖f‖ := le_add_of_nonneg_right (norm_nonneg _)
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hK1
  obtain ⟨w, hw, hnorm⟩ := InteriorH2.h2FromWeakDerivatives U (hUnderlying U 1 v)
    (hFirstDerivative v) (fun _ _ => d) (K * (‖v‖ + ‖f‖))
    (fun j => hilbertDerivativeDistribution U 1 v ⟨{j}, by simp⟩) hg
    (hv0.trans hv_bound) (fun j => (hv1 j).trans hv_bound) (fun _ _ => hd_bound)
  exact ⟨w, hw, by simpa only [mul_assoc, N] using hnorm⟩

theorem directionalLipschitzMultiplier :
    P201Specs.BoundaryH2.directionalLipschitzMultiplierStatement := by
  intro n U j a M L hL hM v dv hv
  let μ := domainMeasure U
  let da : Space n → ℝ := fun x => fderiv ℝ a x (coordinate n j)
  have ham : AEStronglyMeasurable a μ :=
    hL.continuousOn.aestronglyMeasurable U.isOpen.measurableSet
  have hdam : AEStronglyMeasurable da μ :=
    ((ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).continuous.measurable.comp
      (measurable_fderiv ℝ a)).aestronglyMeasurable
  have hdaB : ∀ᵐ x ∂μ, |da x| ≤ (L : ℝ) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    calc
      _ ≤ ‖fderiv ℝ a x‖ * ‖coordinate n j‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ a x‖ := by
        rw [P102.U4.DifferenceQuotient.norm_coordinateVector, mul_one]
      _ ≤ _ := norm_fderiv_le_of_lipschitzOn ℝ (U.isOpen.mem_nhds hx) hL
  have haB : ∀ᵐ x ∂μ, |a x| ≤ (M : ℝ) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact hM x hx
  have hdaTop : MemLp da ∞ μ := memLp_top_of_bound hdam L hdaB
  have hdaLI : LocallyIntegrableOn da U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdaTop.locallyIntegrable le_top)
  have haLI : LocallyIntegrableOn a U volume :=
    hL.continuousOn.locallyIntegrableOn U.isOpen.measurableSet
  have haD : distributionDerivative {j} (regularDistribution U a) =
      regularDistribution U da := by
    apply P102.U4.acl_converse n (Nat.zero_lt_of_lt j.isLt) ℝ U j a da haLI hdaLI
    exact ⟨a, Filter.EventuallyEq.rfl, lipschitz_scalar_on_lines U j a hL⟩
  have hwm := InteriorH2.scalarMultiply_memLp v a ham haB
  have hd1m := InteriorH2.scalarMultiply_memLp dv a ham haB
  have hd2m := InteriorH2.scalarMultiply_memLp v da hdam hdaB
  have hdm := hd1m.add hd2m
  let w : Lp ℝ U 2 := hwm.toLp (fun x => a x * v x)
  let d : Lp ℝ U 2 := hdm.toLp (fun x => a x * dv x + da x * v x)
  have hw : (w : Space n → ℝ) =ᵐ[μ] (fun x => a x * v x) := hwm.coeFn_toLp
  have hd : (d : Space n → ℝ) =ᵐ[μ]
      (fun x => a x * dv x + da x * v x) := hdm.coeFn_toLp
  have hprodLI : LocallyIntegrableOn (fun x => a x * v x) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hwm.locallyIntegrable (by norm_num))
  have hderLI : LocallyIntegrableOn (fun x => a x * dv x + da x * v x) U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdm.locallyIntegrable (by norm_num))
  have heq := directionalProduct U j a da v dv haLI hdaLI
    (P102.U4.domainLp_locallyIntegrable U 2 v)
    (P102.U4.domainLp_locallyIntegrable U 2 dv) haD hv hprodLI hderLI
  have hwreg : regularDistribution U w =
      regularDistribution U (fun x => a x * v x) :=
    (P102.U4.regular_injectivity n ℝ U _ _
      (P102.U4.domainLp_locallyIntegrable U 2 w) hprodLI).mpr hw
  have hdreg : regularDistribution U d =
      regularDistribution U (fun x => a x * dv x + da x * v x) :=
    (P102.U4.regular_injectivity n ℝ U _ _
      (P102.U4.domainLp_locallyIntegrable U 2 d) hderLI).mpr hd
  refine ⟨w, d, hw, hd, ?_, InteriorH2.scalarMultiply_norm_le v a ham haB, ?_⟩
  · change distributionDerivative {j} (regularDistribution U w) = regularDistribution U d
    rw [hwreg, hdreg]
    exact heq
  · let z1 : Lp ℝ U 2 := hd1m.toLp (fun x => a x * dv x)
    let z2 : Lp ℝ U 2 := hd2m.toLp (fun x => da x * v x)
    have hz1 : (z1 : Space n → ℝ) =ᵐ[μ] (fun x => a x * dv x) := hd1m.coeFn_toLp
    have hz2 : (z2 : Space n → ℝ) =ᵐ[μ] (fun x => da x * v x) := hd2m.coeFn_toLp
    have he : d = z1 + z2 := by
      apply Lp.ext
      filter_upwards [hd, Lp.coeFn_add z1 z2, hz1, hz2] with x hx hadd h1 h2
      change d x = (z1 + z2) x
      rw [hx, hadd]
      change _ = z1 x + z2 x
      rw [h1, h2]
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add
      (InteriorH2.scalarMultiply_norm_le dv a ham haB)
      (InteriorH2.scalarMultiply_norm_le v da hdam hdaB))

private lemma hilbert_to_sum_bound {n : ℕ} (U : Domain n) (k : ℕ) (v : H ℝ U k) :
    ‖(hToW ℝ U k) v‖ ≤ (Fintype.card (P102.U4.SobolevIndex n k) : ℝ) * ‖v‖ := by
  rw [P102.U4.sobolev_norm U k 2]
  calc
    _ ≤ ∑ _α : P102.U4.SobolevIndex n k, ‖v‖ := by
      apply Finset.sum_le_sum
      intro α _
      change ‖v.val α‖ ≤ ‖v.val‖
      exact PiLp.norm_apply_le _ _
    _ = _ := by simp

private lemma sum_to_hilbert_bound {n : ℕ} (U : Domain n) (k : ℕ) (v : W ℝ U k 2) :
    ‖(hToW ℝ U k).symm v‖ ≤ ‖v‖ := by
  let w : H ℝ U k := (hToW ℝ U k).symm v
  have hs : ‖w‖ ^ 2 ≤ (∑ α : P102.U4.SobolevIndex n k, ‖w.val α‖) ^ 2 := by
    rw [fullHilbertNorm U k w]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun α _ => norm_nonneg _)
  have hn := (sq_le_sq₀ (norm_nonneg w)
    (Finset.sum_nonneg (fun α _ => norm_nonneg _))).mp hs
  have he : (∑ α : P102.U4.SobolevIndex n k, ‖w.val α‖) = ‖v‖ := by
    rw [P102.U4.sobolev_norm U k 2]
    rfl
  exact hn.trans_eq he

theorem coordinateH1Pullback : P201Specs.BoundaryH2.coordinateH1PullbackStatement := by
  intro n hn U V L M F
  obtain ⟨S, hS, hSd, hSnorm⟩ := P102.U4.bilipschitz_sobolevPullback n hn ℝ U V L M F 2
  let T : H ℝ U 1 →L[ℝ] H ℝ V 1 :=
    (hToW ℝ V 1).symm.toContinuousLinearMap.comp
      (S.comp (hToW ℝ U 1).toContinuousLinearMap)
  have hnorm (u : H ℝ U 1) : ‖T u‖ ≤
      ((Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) *
        P102.U4.pullbackSobolevBound n 2 L M) * ‖u‖ := by
    have hpos : 0 ≤ P102.U4.pullbackSobolevBound n 2 L M := by
      dsimp [P102.U4.pullbackSobolevBound, P102.U4.pullbackLpBound]
      positivity
    calc
      ‖T u‖ ≤ ‖S ((hToW ℝ U 1) u)‖ := sum_to_hilbert_bound V 1 _
      _ ≤ ‖S‖ * ‖(hToW ℝ U 1) u‖ := S.le_opNorm _
      _ ≤ P102.U4.pullbackSobolevBound n 2 L M *
          ((Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) * ‖u‖) :=
        mul_le_mul hSnorm (hilbert_to_sum_bound U 1 u) (norm_nonneg _) hpos
      _ = _ := by ring
  refine ⟨T, ?_, ?_, ContinuousLinearMap.opNorm_le_bound _ (by
    dsimp [P102.U4.pullbackSobolevBound, P102.U4.pullbackLpBound]; positivity) hnorm⟩
  · intro u
    change (P102.U4.sobolevUnderlying ((hToW ℝ V 1) ((hToW ℝ V 1).symm
      (S ((hToW ℝ U 1) u)))) : Space n → ℝ) =ᵐ[domainMeasure V] _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hS ((hToW ℝ U 1) u)
  · intro u j
    change (P102.U4.firstWeakDerivative ((hToW ℝ V 1) ((hToW ℝ V 1).symm
      (S ((hToW ℝ U 1) u)))) j : Space n → ℝ) =ᵐ[domainMeasure V] _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hSd ((hToW ℝ U 1) u) j

private lemma h1_norm_from_bounds {n : ℕ} (U : Domain n) (v : H ℝ U 1)
    (B : ℝ) (hu : ‖hUnderlying U 1 v‖ ≤ B)
    (hd : ∀ j, ‖hFirstDerivative v j‖ ≤ B) : ‖v‖ ≤ (1 + (n : ℝ)) * B := by
  have hn : ‖v‖ ≤ ‖(hToW ℝ U 1) v‖ := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      sum_to_hilbert_bound U 1 ((hToW ℝ U 1) v)
  calc
    ‖v‖ ≤ ‖(hToW ℝ U 1) v‖ := hn
    _ = ‖hUnderlying U 1 v‖ + ∑ j : Fin n, ‖hFirstDerivative v j‖ :=
      P102.U4.BiLipschitzPullback.sobolev_firstOrder_norm U 2 _
    _ ≤ B + ∑ _j : Fin n, B := add_le_add hu (Finset.sum_le_sum (fun j _ => hd j))
    _ = _ := by simp; ring

private lemma h1_lipschitz_multiplier {n : ℕ} (U : Domain n) (a : Space n → ℝ)
    (M L : ℝ≥0) (hL : LipschitzOnWith L a U) (hM : ∀ x ∈ U, |a x| ≤ M)
    (v : H ℝ U 1) :
    ∃ w : H ℝ U 1,
      (hUnderlying U 1 w : Space n → ℝ) =ᵐ[domainMeasure U]
        (fun x => a x * hUnderlying U 1 v x) ∧
      ‖w‖ ≤ (1 + (n : ℝ)) * ((M : ℝ) + L) * ‖v‖ := by
  have ham : AEStronglyMeasurable a (domainMeasure U) :=
    hL.continuousOn.aestronglyMeasurable U.isOpen.measurableSet
  have haB : ∀ᵐ x ∂domainMeasure U, |a x| ≤ (M : ℝ) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact hM x hx
  have hwm := InteriorH2.scalarMultiply_memLp (hUnderlying U 1 v) a ham haB
  let w0 : Lp ℝ U 2 := hwm.toLp (fun x => a x * hUnderlying U 1 v x)
  have hw0 : (w0 : Space n → ℝ) =ᵐ[domainMeasure U]
      (fun x => a x * hUnderlying U 1 v x) := hwm.coeFn_toLp
  have hj (j : Fin n) := directionalLipschitzMultiplier U j a M L hL hM
    (hUnderlying U 1 v) (hFirstDerivative v j)
    (hilbertDerivativeDistribution U 1 v ⟨{j}, by simp⟩)
  choose wj dj hwj hdj hDj hnwj hndj using hj
  have hweak (j : Fin n) : distributionDerivative {j} (regularDistribution U w0) =
      regularDistribution U (dj j) := by
    have he : w0 = wj j := Lp.ext (hw0.trans (hwj j).symm)
    rw [he]
    exact hDj j
  obtain ⟨w, hw, hwd⟩ := InteriorH2.h1FromWeakDerivatives U w0 dj hweak
  have huNorm : ‖hUnderlying U 1 v‖ ≤ ‖v‖ := PiLp.norm_apply_le _ _
  have hw0norm : ‖w0‖ ≤ ((M : ℝ) + L) * ‖v‖ := by
    calc
      _ ≤ (M : ℝ) * ‖hUnderlying U 1 v‖ :=
        InteriorH2.scalarMultiply_norm_le (hUnderlying U 1 v) a ham haB
      _ ≤ (M : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_left huNorm M.coe_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right L.coe_nonneg) (norm_nonneg _)
  have hdNorm (j : Fin n) : ‖dj j‖ ≤ ((M : ℝ) + L) * ‖v‖ := by
    calc
      _ ≤ (M : ℝ) * ‖hFirstDerivative v j‖ + (L : ℝ) * ‖hUnderlying U 1 v‖ := hndj j
      _ ≤ (M : ℝ) * ‖v‖ + (L : ℝ) * ‖v‖ := by
        gcongr
        exact InteriorH2.firstDerivative_norm_le U v j
      _ = _ := by ring
  refine ⟨w, by simpa only [hw] using hw0, ?_⟩
  have hbound := h1_norm_from_bounds U w (((M : ℝ) + L) * ‖v‖)
    (by simpa only [hw] using hw0norm) (fun j => by simpa only [hwd] using hdNorm j)
  simpa only [mul_assoc] using hbound

private lemma h2_first_order_classes {n : ℕ} (U : Domain n) (u : H ℝ U 2) :
    ∃ (v : H ℝ U 1) (d : Fin n → H ℝ U 1),
      hUnderlying U 1 v = hUnderlying U 2 u ∧
      (∀ j, hUnderlying U 1 (d j) = hFirstDerivative v j) ∧
      ‖v‖ ≤ (1 + (n : ℝ)) * ‖u‖ ∧
      ∀ j, ‖d j‖ ≤ (1 + (n : ℝ)) * ‖u‖ := by
  let u0 := hUnderlying U 2 u
  let u1 : Fin n → Lp ℝ U 2 := fun j => u.val ⟨{j}, by simp⟩
  let u2 : Fin n → Fin n → Lp ℝ U 2 := fun j k => u.val ⟨{j, k}, by simp⟩
  have h1 (j : Fin n) : distributionDerivative {j} (regularDistribution U u0) =
      regularDistribution U (u1 j) := hilbertDerivativeDistribution U 2 u ⟨{j}, by simp⟩
  have h2 (j k : Fin n) : distributionDerivative {k} (regularDistribution U (u1 j)) =
      regularDistribution U (u2 j k) := by
    rw [← h1 j]
    change P102.U4.distributionPartial {k} (P102.U4.distributionPartial {j} _) = _
    rw [← P102.U4.derivative_add n ℝ U]
    have hs : ({k} + {j} : MultiIndex n) = {j, k} := by simp [add_comm]
    rw [hs]
    exact hilbertDerivativeDistribution U 2 u ⟨{j, k}, by simp⟩
  obtain ⟨v, hv, hvd⟩ := InteriorH2.h1FromWeakDerivatives U u0 u1 h1
  have hd (j : Fin n) := InteriorH2.h1FromWeakDerivatives U (u1 j) (u2 j) (h2 j)
  choose d hd0 hd1 using hd
  refine ⟨v, d, hv, fun j => (hd0 j).trans (hvd j).symm, ?_, ?_⟩
  · apply h1_norm_from_bounds U v ‖u‖
    · rw [hv]
      exact PiLp.norm_apply_le _ _
    · intro j
      rw [hvd j]
      exact PiLp.norm_apply_le _ _
  · intro j
    apply h1_norm_from_bounds U (d j) ‖u‖
    · rw [hd0 j]
      exact PiLp.norm_apply_le _ _
    · intro k
      rw [hd1 j k]
      exact PiLp.norm_apply_le _ _

theorem coordinateH2Pullback : P201Specs.BoundaryH2.coordinateH2PullbackStatement := by
  intro n hn U V L M Hder F hDF
  obtain ⟨T, hTu, hTd, hTnorm⟩ := coordinateH1Pullback hn U V L M F
  let N : ℝ := 1 + (n : ℝ)
  let K : ℝ := 1 + (Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) *
    P102.U4.pullbackSobolevBound n 2 L M
  have hK : 0 < K := by
    dsimp [K, P102.U4.pullbackSobolevBound, P102.U4.pullbackLpBound]
    positivity
  have hN : 0 < N := by dsimp only [N]; positivity
  have hTK : ‖T‖ ≤ K := hTnorm.trans (le_add_of_nonneg_left zero_le_one)
  let D : ℝ := N * ((L : ℝ) + Hder) * K * N
  let B : ℝ := K * N + (n : ℝ) * D
  let C : ℝ := 1 + (Fintype.card (P102.U4.SobolevIndex n 2) : ℝ) * B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u
  obtain ⟨v, d, hv, hd, hvnorm, hdnorm⟩ := h2_first_order_classes U u
  let a : Fin n → Fin n → Space n → ℝ := fun i j x =>
    fderiv ℝ F.toFun x (coordinate n i) j
  have haLip (i j : Fin n) : LipschitzOnWith Hder (a i j) V :=
    matrix_entry_lipschitz V (fderiv ℝ F.toFun) j i hDF
  have haB (i j : Fin n) : ∀ x ∈ V, |a i j x| ≤ (L : ℝ) := by
    intro x hx
    exact (matrix_entry_bound _ j i).trans
      (norm_fderiv_le_of_lipschitzOn ℝ (V.isOpen.mem_nhds hx) F.lipschitz)
  have hp (i j : Fin n) := h1_lipschitz_multiplier V (a i j) L Hder
    (haLip i j) (haB i j) (T (d j))
  choose p hpu hpnorm using hp
  let z : Fin n → H ℝ V 1 := fun i => ∑ j : Fin n, p i j
  have hyNorm (j : Fin n) : ‖T (d j)‖ ≤ K * N * ‖u‖ := by
    calc
      _ ≤ ‖T‖ * ‖d j‖ := T.le_opNorm _
      _ ≤ K * (N * ‖u‖) := mul_le_mul hTK (hdnorm j) (norm_nonneg _) hK.le
      _ = _ := (mul_assoc _ _ _).symm
  have hpNorm (i j : Fin n) : ‖p i j‖ ≤ D * ‖u‖ := by
    calc
      _ ≤ N * ((L : ℝ) + Hder) * ‖T (d j)‖ := hpnorm i j
      _ ≤ N * ((L : ℝ) + Hder) * (K * N * ‖u‖) := by
        gcongr
        exact hyNorm j
      _ = _ := by dsimp only [D]; ring
  have hzNorm (i : Fin n) : ‖z i‖ ≤ (n : ℝ) * D * ‖u‖ := by
    calc
      _ ≤ ∑ j : Fin n, ‖p i j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, D * ‖u‖ := Finset.sum_le_sum (fun j _ => hpNorm i j)
      _ = _ := by simp; ring
  have hzu (i : Fin n) : hUnderlying V 1 (z i) = hFirstDerivative (T v) i := by
    have hpi (j : Fin n) : (hUnderlying V 1 (p i j) : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => a i j x * hFirstDerivative v j (F.toFun x)) := by
      filter_upwards [hpu i j, hTu (d j)] with x hx hy
      rw [hx, hy, hd j]
    have hzsum : hUnderlying V 1 (z i) = ∑ j : Fin n, hUnderlying V 1 (p i j) :=
      map_sum (hUnderlying V 1) _ _
    rw [hzsum]
    apply Lp.ext
    filter_upwards [MeasureTheory.Lp.coeFn_fun_finsetSum Finset.univ (fun j => hUnderlying V 1 (p i j)),
      (ae_all_iff.mpr hpi), hTd v i] with x hsum hpx hchain
    rw [hsum, hchain]
    exact Finset.sum_congr rfl (fun j _ => hpx j)
  let g : Fin n → Fin n → Lp ℝ V 2 := fun i k => hFirstDerivative (z i) k
  have hg (i k : Fin n) : distributionDerivative {k}
      (regularDistribution V (hFirstDerivative (T v) i)) = regularDistribution V (g i k) := by
    rw [← hzu i]
    exact hilbertDerivativeDistribution V 1 (z i) ⟨{k}, by simp⟩
  have hvT : ‖T v‖ ≤ K * N * ‖u‖ := by
    calc
      _ ≤ ‖T‖ * ‖v‖ := T.le_opNorm _
      _ ≤ K * (N * ‖u‖) := mul_le_mul hTK hvnorm (norm_nonneg _) hK.le
      _ = _ := (mul_assoc _ _ _).symm
  have hvB : ‖T v‖ ≤ B * ‖u‖ := hvT.trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (norm_nonneg _))
  have hgB (i k : Fin n) : ‖g i k‖ ≤ B * ‖u‖ := by
    calc
      _ ≤ ‖z i‖ := InteriorH2.firstDerivative_norm_le V (z i) k
      _ ≤ (n : ℝ) * D * ‖u‖ := hzNorm i
      _ ≤ B * ‖u‖ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by positivity)) (norm_nonneg _)
  have hv0 : ‖hUnderlying V 1 (T v)‖ ≤ B * ‖u‖ :=
    (PiLp.norm_apply_le _ _).trans hvB
  have hv1 (j : Fin n) : ‖hFirstDerivative (T v) j‖ ≤ B * ‖u‖ :=
    (InteriorH2.firstDerivative_norm_le V (T v) j).trans hvB
  obtain ⟨w, hw, hwnorm⟩ := InteriorH2.h2FromWeakDerivatives V (hUnderlying V 1 (T v))
    (hFirstDerivative (T v)) g (B * ‖u‖)
    (fun j => hilbertDerivativeDistribution V 1 (T v) ⟨{j}, by simp⟩) hg hv0 hv1 hgB
  refine ⟨w, ?_, ?_⟩
  · change (hUnderlying V 2 w : Space n → ℝ) =ᵐ[domainMeasure V] _
    rw [hw]
    simpa only [hv] using hTu v
  · apply hwnorm.trans
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)


/-- Restriction of a full H¹ class to any smaller open set, including one
whose closure reaches the boundary of the larger set. -/
theorem h1Restriction {n : ℕ} (V U : Domain n) (hUV : U ≤ V) (v : H ℝ V 1) :
    ∃ w : H ℝ U 1,
      (hUnderlying U 1 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
      (∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure U]
        hFirstDerivative v j) ∧ ‖w‖ ≤ (1 + (n : ℝ)) * ‖v‖ := by
  let u := InteriorH2.restrictLp hUV (hUnderlying V 1 v)
  let d : Fin n → Lp ℝ U 2 := fun j => InteriorH2.restrictLp hUV (hFirstDerivative v j)
  have hd (j : Fin n) : distributionDerivative {j} (regularDistribution U u) =
      regularDistribution U (d j) := by
    dsimp only [u, d]
    rw [InteriorH2.regular_restrictLp, InteriorH2.regular_restrictLp]
    apply P102.U4.DifferenceQuotient.weak_derivative_restrict hUV
      (P102.U4.domainLp_locallyIntegrable V 2 _)
      (P102.U4.domainLp_locallyIntegrable V 2 _)
    exact hilbertDerivativeDistribution V 1 v ⟨{j}, by simp⟩
  obtain ⟨w, hw, hwd⟩ := InteriorH2.h1FromWeakDerivatives U u d hd
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [hw]
    exact InteriorH2.restrictLp_ae hUV _
  · intro j
    rw [hwd]
    exact InteriorH2.restrictLp_ae hUV _
  · apply h1_norm_from_bounds U w ‖v‖
    · rw [hw]
      exact (InteriorH2.restrictLp_norm_le hUV _).trans (PiLp.norm_apply_le _ _)
    · intro j
      rw [hwd]
      exact (InteriorH2.restrictLp_norm_le hUV _).trans
        (InteriorH2.firstDerivative_norm_le V v j)

/-- Restriction of the actual weak equation requires no compact containment. -/
theorem weakEquationRestriction {n : ℕ} (V U : Domain n) (hUV : U ≤ V)
    (A : Space n → Space n →L[ℝ] Space n) (v : H ℝ V 1) (w : H ℝ U 1)
    (f g : Space n → ℝ)
    (hd : ∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure U]
      hFirstDerivative v j)
    (hfg : g =ᵐ[domainMeasure U] f)
    (heq : P201Specs.InteriorH2.WeakEquation V A v f) :
    P201Specs.InteriorH2.WeakEquation U A w g := by
  have hgrad : (hGradient w : Space n → Space n) =ᵐ[domainMeasure U] hGradient v := by
    filter_upwards [InteriorH2.hGradient_ae w,
      ae_restrict_of_ae_restrict_of_subset hUV (InteriorH2.hGradient_ae v),
      ae_all_iff.mpr hd] with x hw hv hx
    rw [hw, hv]
    ext j
    exact hx j
  intro φ
  let ψ : Test ℝ V := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hUV⟩
  have hgzero (x : Space n) (hx : x ∉ U) : gradient φ x = 0 := by
    have hxt : x ∉ tsupport φ := fun h => hx (φ.tsupport_subset h)
    change WithLp.toLp 2 (fun j => fderiv ℝ φ x (coordinate n j)) = 0
    rw [fderiv_of_notMem_tsupport ℝ hxt]
    rfl
  have hleft : (∫ x in V, inner ℝ (A x (hGradient v x)) (gradient ψ x)) =
      ∫ x in U, inner ℝ (A x (hGradient v x)) (gradient φ x) := by
    change (∫ x in V, inner ℝ (A x (hGradient v x)) (gradient φ x)) = _
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero V.isOpen.measurableSet hUV
    intro x hx
    rw [hgzero x hx.2, inner_zero_right]
  have hright : (∫ x in V, f x * ψ x) = ∫ x in U, f x * φ x := by
    change (∫ x in V, f x * φ x) = _
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero V.isOpen.measurableSet hUV
    intro x hx
    rw [φ.zero_on_compl hx.2, Pi.zero_apply, mul_zero]
  calc
    _ = ∫ x in U, inner ℝ (A x (hGradient v x)) (gradient φ x) := by
      apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      rw [hx]
    _ = ∫ x in V, inner ℝ (A x (hGradient v x)) (gradient ψ x) := hleft.symm
    _ = ∫ x in V, f x * ψ x := heq ψ
    _ = ∫ x in U, f x * φ x := hright
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      rw [hx]


/-- The endpoint case of the source boundary estimate, with genuine local
outer norms. No boundary regularity is needed in dimension one. -/
theorem localBoundaryEstimateOne : P201Specs.BoundaryH2.localBoundaryEstimateOneStatement := by
  intro Ω p M L theta htheta
  let V := P201Specs.BoundaryH2.neighborhood Ω p 2
  let U := P201Specs.BoundaryH2.neighborhood Ω p 1
  have hVΩ : V ≤ Ω := fun _ hx => hx.1
  have hUV : U ≤ V := by
    intro x hx
    exact ⟨hx.1, (lt_trans hx.2 (by norm_num : (1 : ℝ) < 2))⟩
  obtain ⟨C, hC, hreg⟩ := dimensionOneEstimate U M L theta htheta
  refine ⟨2, 1, 2 * C, by norm_num, by norm_num, mul_pos (by norm_num) hC, ?_⟩
  intro A hA u f heq
  obtain ⟨v, hv, hvd, _⟩ := h1Restriction Ω V hVΩ u.val
  let g := InteriorH2.restrictLp hVΩ f
  have hg : (g : Space 1 → ℝ) =ᵐ[domainMeasure V] f :=
    InteriorH2.restrictLp_ae hVΩ f
  have hveq := weakEquationRestriction Ω V hVΩ A u.val v f g hvd hg heq
  obtain ⟨vU, hvU, hvUd, hvUn⟩ := h1Restriction V U hUV v
  let gU := InteriorH2.restrictLp hUV g
  have hgU : (gU : Space 1 → ℝ) =ᵐ[domainMeasure U] g :=
    InteriorH2.restrictLp_ae hUV g
  have hUeq := weakEquationRestriction V U hUV A v vU g gU hvUd hgU hveq
  have hAU : P201Specs.InteriorH2.CoefficientBounds U A M L theta :=
    ⟨fun x hx => hA.1 x (hVΩ (hUV hx)), hA.2.1.mono (hUV.trans hVΩ),
      fun x hx => hA.2.2 x (hVΩ (hUV hx))⟩
  obtain ⟨w, hw, hwn⟩ := hreg A hAU vU gU hUeq
  refine ⟨v, g, w, hv, hg, ?_, ?_⟩
  · rw [hw]
    exact hvU.trans (ae_restrict_of_ae_restrict_of_subset hUV hv)
  · calc
      ‖w‖ ≤ C * (‖vU‖ + ‖gU‖) := hwn
      _ ≤ C * ((1 + (1 : ℝ)) * ‖v‖ + ‖g‖) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (by simpa only [Nat.cast_one] using hvUn)
            (InteriorH2.restrictLp_norm_le hUV g)) hC.le
      _ ≤ (2 * C) * (‖v‖ + ‖g‖) := by
        nlinarith [mul_nonneg hC.le (norm_nonneg g)]

/-- A common directional quotient bound constructs the L² derivative on an
arbitrary open restriction, including a set meeting the boundary of V. -/
theorem derivativeFromBoundaryQuotients {n : ℕ} (hn : 0 < n)
    (U V : Domain n) (hUV : U ≤ V) (u : Lp ℝ V 2) (j : Fin n) (B : ℝ≥0)
    (hb : ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
      MemLp (differenceQuotient u j h) 2 (domainMeasure U) ∧
      eLpNorm (differenceQuotient u j h) 2 (domainMeasure U) ≤ B) :
    ∃ d : Lp ℝ U 2,
      distributionDerivative {j} (regularDistribution U u) =
        regularDistribution U d ∧ ‖d‖ ≤ B := by
  obtain ⟨W, hW⟩ := P102.U4.DifferenceQuotient.exists_exhaustion U
  have hWU (i : ℕ) : W i ≤ U := subset_closure.trans (hW.2.1 i).2
  have hbW (i : ℕ) : P102.U4.DifferenceQuotient.HasBound U (W i) j 2 u B := by
    obtain ⟨δ, hδ, hquot⟩ := hb
    obtain ⟨ε, hε, hK⟩ := (hW.2.1 i).1.exists_cthickening_subset_open
      U.isOpen (hW.2.1 i).2
    refine ⟨min δ ε, lt_min hδ hε, fun h hh hsmall => ?_⟩
    obtain ⟨hm, hnq⟩ := hquot h hh (hsmall.trans_le (min_le_left _ _))
    refine ⟨?_, hm.mono_measure (Measure.restrict_mono (hWU i) le_rfl), ?_⟩
    · intro x hx
      apply hK
      apply Metric.mem_cthickening_of_dist_le _ x ε _ (subset_closure hx)
      simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul,
        P102.U4.DifferenceQuotient.norm_coordinateVector, mul_one, Real.norm_eq_abs]
        using (hsmall.trans_le (min_le_right _ _)).le
    · exact (eLpNorm_mono_measure _ (Measure.restrict_mono (hWU i) le_rfl)).trans hnq
  have huloc : P102.U4.DifferenceQuotient.LocallyMemLp U 2 u := by
    intro Z hZ
    exact (Lp.memLp u).mono_measure
      (Measure.restrict_mono ((subset_closure.trans hZ.2).trans hUV) le_rfl)
  obtain ⟨d, hdloc, hdm, hder, hdn⟩ :=
    P102.U4.difference_quotient_converse_global n hn ℝ U j 2
      (by norm_num) (by norm_num) u W B huloc hW hbW
  refine ⟨hdm.toLp d, ?_, ?_⟩
  · exact hder.trans ((P102.U4.regular_injectivity n ℝ U d (hdm.toLp d)
      hdloc (P102.U4.domainLp_locallyIntegrable U 2 _)).mpr (MemLp.coeFn_toLp hdm).symm)
  · rw [Lp.norm_toLp]
    exact_mod_cast ENNReal.toReal_mono ENNReal.coe_ne_top hdn

/-- A whole-space H¹ class vanishing below the flat face restricts to H¹₀
of the half-space. This uses the actual closure definition, including m = 0. -/
theorem zeroBelow_mem_hZero {m : ℕ}
    (z : H ℝ (⊤ : Domain (m + 1)) 1)
    (hz : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (v : H ℝ (P102.Trace.halfSpace m) 1)
    (hv : (hUnderlying (P102.Trace.halfSpace m) 1 v : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure (P102.Trace.halfSpace m)] hUnderlying ⊤ 1 z) :
    v ∈ P201Specs.hZeroSubmodule ℝ (P102.Trace.halfSpace m) := by
  let U := P102.Trace.halfSpace m
  let zw := hToW ℝ ⊤ 1 z
  let vw := hToW ℝ U 1 v
  have hback : P102.Trace.restrictWholeSobolev U zw = vw := by
    apply P102.U4.sobolevUnderlying_injective U 1 2
    apply Lp.ext
    exact (P102.Trace.restrictWholeLp_ae U (P102.U4.sobolevUnderlying zw)).trans hv.symm
  rw [hZeroClosureBridge ℝ U]
  change vw ∈ closure (P102.U4.smoothSobolevSubmodule ℝ U 1 2 : Set _)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨φ, w, hrep, herr⟩ := P102.Trace.halfSpace_approximation_of_wholeSpace
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) zw hz hε
  let wU := P102.Trace.restrictWholeSobolev U w
  have hwφ : P102.U4.sobolevUnderlying wU = P102.U4.testToDomainLp U 2 φ := by
    apply Lp.ext
    have hφ0 := hrep (P102.U4.zeroSobolevIndex (m + 1) 1)
    simp only [P102.U4.zeroSobolevIndex, P102.U4.multiPartial,
      Multiset.sort_zero, P102.U4.partialWord] at hφ0
    exact ((P102.Trace.restrictWholeLp_ae U (P102.U4.sobolevUnderlying w)).trans
      (ae_restrict_of_ae hφ0)).trans (P102.U4.testToDomainLp_ae U 2 φ).symm
  refine ⟨wU, ⟨φ, hwφ.symm⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, ← hback]
  exact (P102.Trace.restrictWholeSobolev_norm_sub_le U w zw).trans_lt herr

/-- Tangential quotients of a whole-space zero extension are admissible H¹₀
half-space tests, including their actual weak derivatives. -/
theorem tangentialQuotientTest {m : ℕ}
    (z : H ℝ (⊤ : Domain (m + 1)) 1)
    (hz : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) :
    ∃ t : H10 ℝ (P102.Trace.halfSpace m),
      (hZeroUnderlying (P102.Trace.halfSpace m) t : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)]
          differenceQuotient (hUnderlying ⊤ 1 z) k h ∧
      ∀ j, (hFirstDerivative t.val j : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)]
          differenceQuotient (hFirstDerivative z j) k h := by
  have hcoord : coordinate (m + 1) k (Fin.last m) = 0 := by
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, Ne.symm hk]
  have hheight (x : Space (m + 1)) :
      (x + h • coordinate (m + 1) k) (Fin.last m) = x (Fin.last m) := by
    change x (Fin.last m) + h * coordinate (m + 1) k (Fin.last m) = _
    rw [hcoord, mul_zero, add_zero]
  obtain ⟨q, hq, _hqd⟩ := InteriorH2.h1Quotient ⊤ ⊤ le_top k h
    (fun _ _ => mem_univ _) z
  have hq' : (hUnderlying ⊤ 1 q : Space (m + 1) → ℝ) =ᵐ[volume]
      differenceQuotient (hUnderlying ⊤ 1 z) k h := by
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using hq
  have hzshift := (measurePreserving_add_right volume (h • coordinate (m + 1) k)).quasiMeasurePreserving.ae hz
  have hqbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 q x = 0 := by
    filter_upwards [hq', hz, hzshift] with x hx hxz hxs hxneg
    rw [hx]
    change h⁻¹ • (hUnderlying ⊤ 1 z (x + h • coordinate (m + 1) k) -
      hUnderlying ⊤ 1 z x) = 0
    rw [hxz hxneg, hxs (by rw [hheight]; exact hxneg), sub_self, smul_zero]
  obtain ⟨t, ht, htd⟩ := InteriorH2.h1Quotient (P102.Trace.halfSpace m) ⊤
    le_top k h (fun _ _ => mem_univ _) z
  have hqU : (hUnderlying ⊤ 1 q : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure (P102.Trace.halfSpace m)]
        differenceQuotient (hUnderlying ⊤ 1 z) k h := ae_restrict_of_ae hq'
  have htq : (hUnderlying (P102.Trace.halfSpace m) 1 t : Space (m + 1) → ℝ)
      =ᵐ[domainMeasure (P102.Trace.halfSpace m)] hUnderlying ⊤ 1 q :=
    ht.trans hqU.symm
  exact ⟨⟨t, zeroBelow_mem_hZero q hqbelow t htq⟩, ht, htd⟩

/-- Discrete energy testing across the flat boundary. The test may reach the
flat face because its whole-space representative vanishes below that face. -/
theorem halfSpace_discrete_energy_identity {m : ℕ}
    (F : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure (P102.Trace.halfSpace m)))
    (f : Lp ℝ (P102.Trace.halfSpace m) 2)
    (heq : ∀ φ : Test ℝ (P102.Trace.halfSpace m),
      (∫ x in P102.Trace.halfSpace m, inner ℝ (F x) (gradient φ x)) =
        ∫ x in P102.Trace.halfSpace m, f x * φ x)
    (z : H ℝ (⊤ : Domain (m + 1)) 1)
    (hzbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) (hh : h ≠ 0) :
    (∑ j : Fin (m + 1), ∫ x,
      differenceQuotient (P102.U4.lpZeroExtension (P102.Trace.halfSpace m) 2
        (InteriorH2.fluxCoordinate F j)) k h x * hFirstDerivative z j x) =
      -(∫ x in P102.Trace.halfSpace m,
        f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
  let V := P102.Trace.halfSpace m
  have hn : 1 ≤ m + 1 := by omega
  obtain ⟨t, ht, htd⟩ := tangentialQuotientTest z hzbelow k hk (-h)
  have htest (φ : Test ℝ V) (w : H10 ℝ V)
      (hw : hZeroUnderlying V w = P102.U4.testToDomainLp V 2 φ) :
      negativeDivergenceDistribution V F φ = pivot V f w := by
    rw [InteriorTesting.negativeDivergenceDistribution_pairing, pivotPairing, hw]
    change (∫ x in V, inner ℝ (F x) (gradient φ x)) = _
    rw [heq φ]
    apply integral_congr_ae
    filter_upwards [P102.U4.testToDomainLp_ae V 2 φ] with x hx
    rw [hx]
  have henergy := InteriorTesting.energyTesting hn V F (pivot V f) htest t
  rw [pivotPairing] at henergy
  have hcoord (j : Fin (m + 1)) :
      (∫ x, differenceQuotient (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j)) k h x *
        hFirstDerivative z j x) =
      -(∫ x in V, InteriorH2.fluxCoordinate F j x * hFirstDerivative t.val j x) := by
    have hF : MemLp (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j) : Space (m + 1) → ℝ)
        2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (MeasureTheory.Lp.memLp (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j)))
    have hz : MemLp (hFirstDerivative z j : Space (m + 1) → ℝ) 2 volume := by
      simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ]
        using (MeasureTheory.Lp.memLp (hFirstDerivative z j))
    have hzT : MemLp (fun x => hFirstDerivative z j (x - h • coordinate (m + 1) k)) 2 volume :=
      hz.comp_measurePreserving (measurePreserving_sub_right volume _)
    rw [discreteIntegrationByPartsWholeSpace hn _ _ k h hh
      (hF.integrable_mul hz) (hF.integrable_mul hzT)]
    rw [P102.U4.integral_lpZeroExtension_mul V 2]
    congr 1
    apply integral_congr_ae
    filter_upwards [htd j] with x hx
    rw [hx]
  change (∑ j : Fin (m + 1), ∫ x,
    differenceQuotient (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j)) k h x *
      hFirstDerivative z j x) =
    -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x)
  simp_rw [hcoord]
  rw [Finset.sum_neg_distrib, ← InteriorH2.fluxFunctional_eq_sum, InteriorTesting.fluxFunctional_integral,
    henergy]
  congr 1
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx]

private def regularLpLinear {n : ℕ} (U : Domain n) :
    Lp ℝ U 2 →ₗ[ℝ] Distribution ℝ U where
  toFun u := regularDistribution U u
  map_add' u v := by
    ext φ
    simp only [P102.U4.regularLp_pairing U 2,
      ContinuousLinearMap.map_add, add_apply]
  map_smul' r u := by
    ext φ
    simp only [P102.U4.regularLp_pairing U 2,
      ContinuousLinearMap.map_smul, smul_apply, RingHom.id_apply]

private lemma derivative_sum {n : ℕ} (U : Domain n) (j : Fin n)
    {ι : Type*} (s : Finset ι) (D : ι → Distribution ℝ U) :
    distributionDerivative {j} (∑ a ∈ s, D a) =
      ∑ a ∈ s, distributionDerivative {j} (D a) := by
  ext φ
  simp [P102.U4.distributionPartial]

private lemma vector_coordinate_expansion {n : ℕ} (z : Space n) :
    z = ∑ j : Fin n, z j • coordinate n j := by
  ext i
  simp [P102.U4.coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single, Pi.single_apply]

private lemma matrix_component_expansion {n : ℕ} (A : Space n →L[ℝ] Space n)
    (z : Space n) (i : Fin n) :
    A z i = ∑ j : Fin n, A (coordinate n j) i * z j := by
  conv_lhs => arg 1; rw [vector_coordinate_expansion z]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The weak PDE in terms of the actual L² matrix flux products. -/
theorem weakEquation_matrixFlux {n : ℕ} (U : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (v : H ℝ U 1) (f : Lp ℝ U 2)
    (hA : ContinuousOn A U) {M : ℝ} (hM : ∀ x ∈ U, ‖A x‖ ≤ M)
    (heq : P201Specs.InteriorH2.WeakEquation U A v f)
    (q : Fin n → Fin n → Lp ℝ U 2)
    (hq : ∀ i j, (q i j : Space n → ℝ) =ᵐ[domainMeasure U]
      (fun x => A x (coordinate n j) i * hFirstDerivative v j x)) :
    -(∑ i : Fin n, ∑ j : Fin n,
      distributionDerivative {i} (regularDistribution U (q i j))) =
        regularDistribution U f := by
  let hm := InteriorH2.flux_memLp U A (hGradient v) hA hM
  let F : MeasureTheory.Lp (Space n) 2 (domainMeasure U) := hm.toLp _
  have hF : (F : Space n → Space n) =ᵐ[domainMeasure U]
      (fun x => A x (hGradient v x)) := hm.coeFn_toLp
  have hdiv : negativeDivergenceDistribution U F = regularDistribution U f := by
    ext φ
    rw [InteriorTesting.negativeDivergenceDistribution_pairing,
      P102.U4.regularLp_pairing U 2, P102.U4.lpTestPairing_eq_integral]
    change (∫ x in U, inner ℝ (F x) (gradient φ x)) = _
    rw [← heq φ]
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    rw [hx]
  have hFi (i : Fin n) : regularDistribution U (fun x => F x i) =
      regularLpLinear U (∑ j, q i j) := by
    apply (P102.U4.regular_injectivity n ℝ U _ _
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        (((Lp.memLp F).eval_piLp i).locallyIntegrable (by norm_num)))
      (P102.U4.domainLp_locallyIntegrable U 2 _)).mpr
    filter_upwards [hF, InteriorH2.hGradient_ae v,
      ae_all_iff.mpr (fun j => hq i j),
      MeasureTheory.Lp.coeFn_fun_finsetSum Finset.univ (fun j => q i j)]
      with x hx hgrad hqx hsum
    rw [hsum, hx, matrix_component_expansion]
    apply Finset.sum_congr rfl
    intro j _
    rw [hqx j]
    rw [hgrad]
  change -(∑ i : Fin n, distributionDerivative {i}
    (regularDistribution U (fun x => F x i))) = _ at hdiv
  simp_rw [hFi, map_sum, derivative_sum] at hdiv
  exact hdiv

/-- Recover the normal derivative and reconstruct H² after every other second
weak derivative has been obtained. The hypotheses are only intermediate
L² derivative identities, without a boundary extension or regularity certificate. -/
theorem normalAssembly {m : ℕ} (U : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (M L : ℝ≥0) (theta : ℝ) (htheta : 0 < theta)
    (hA : P201Specs.InteriorH2.CoefficientBounds U A M L theta)
    (v : H ℝ U 1) (f : Lp ℝ U 2)
    (heq : P201Specs.InteriorH2.WeakEquation U A v f)
    (g : Fin (m + 1) → Fin (m + 1) → Lp ℝ U 2) (K : ℝ) (hK : 0 ≤ K)
    (hg : ∀ j i, (i, j) ≠ (Fin.last m, Fin.last m) →
      distributionDerivative {i} (regularDistribution U (hFirstDerivative v j)) =
        regularDistribution U (g j i))
    (hgB : ∀ j i, (i, j) ≠ (Fin.last m, Fin.last m) → ‖g j i‖ ≤ K) :
    ∃ w : H ℝ U 2, hUnderlying U 2 w = hUnderlying U 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex (m + 1) 2) : ℝ) *
        (‖v‖ + K + theta⁻¹ * (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
          ((M : ℝ) * K + (L : ℝ) * ‖v‖) + (L : ℝ) * ‖v‖)) := by
  classical
  let e : Fin (m + 1) := Fin.last m
  let a (i j : Fin (m + 1)) (x : Space (m + 1)) : ℝ := A x (coordinate (m + 1) j) i
  have haL (i j : Fin (m + 1)) : LipschitzOnWith L (a i j) U :=
    matrix_entry_lipschitz U A i j hA.2.1
  have haM (i j : Fin (m + 1)) : ∀ x ∈ U, |a i j x| ≤ (M : ℝ) :=
    fun x hx => (matrix_entry_bound (A x) i j).trans (hA.1 x hx)
  have ham (i j : Fin (m + 1)) : AEStronglyMeasurable (a i j) (domainMeasure U) :=
    (haL i j).continuousOn.aestronglyMeasurable U.isOpen.measurableSet
  have haB (i j : Fin (m + 1)) : ∀ᵐ x ∂domainMeasure U, |a i j x| ≤ (M : ℝ) := by
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact haM i j x hx
  let qm (i j : Fin (m + 1)) :=
    InteriorH2.scalarMultiply_memLp (hFirstDerivative v j) (a i j) (ham i j) (haB i j)
  let q (i j : Fin (m + 1)) : Lp ℝ U 2 :=
    (qm i j).toLp (fun x => a i j x * hFirstDerivative v j x)
  have hq (i j : Fin (m + 1)) : (q i j : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
      (fun x => a i j x * hFirstDerivative v j x) := (qm i j).coeFn_toLp
  have hdExists (p : Fin (m + 1) × Fin (m + 1)) (hp : p ≠ (e, e)) :
      ∃ d : Lp ℝ U 2,
        distributionDerivative {p.1} (regularDistribution U (q p.1 p.2)) =
          regularDistribution U d ∧ ‖d‖ ≤ (M : ℝ) * K + (L : ℝ) * ‖v‖ := by
    obtain ⟨q', d, hq', _, hd, _, hdB⟩ := directionalLipschitzMultiplier U p.1
      (a p.1 p.2) M L (haL _ _) (haM _ _) (hFirstDerivative v p.2) (g p.2 p.1)
      (hg _ _ hp)
    have hqq : q p.1 p.2 = q' := Lp.ext ((hq _ _).trans hq'.symm)
    refine ⟨d, hqq ▸ hd, hdB.trans ?_⟩
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hgB _ _ hp) M.coe_nonneg)
      (mul_le_mul_of_nonneg_left (InteriorH2.firstDerivative_norm_le U v p.2) L.coe_nonneg)
  let d (p : Fin (m + 1) × Fin (m + 1)) : Lp ℝ U 2 :=
    if hp : p = (e, e) then 0 else (hdExists p hp).choose
  have hd (p : Fin (m + 1) × Fin (m + 1)) (hp : p ≠ (e, e)) :
      distributionDerivative {p.1} (regularDistribution U (q p.1 p.2)) =
        regularDistribution U (d p) ∧ ‖d p‖ ≤ (M : ℝ) * K + (L : ℝ) * ‖v‖ := by
    simpa only [d, dite_eq_right hp] using (hdExists p hp).choose_spec
  let s : Finset (Fin (m + 1) × Fin (m + 1)) := Finset.univ.erase (e, e)
  let R : Lp ℝ U 2 := -f - ∑ p ∈ s, d p
  have hnormal : distributionDerivative {e} (regularDistribution U (q e e)) =
      regularDistribution U R := by
    have h := weakEquation_matrixFlux U A v f hA.2.1.continuousOn hA.1 heq q hq
    have hs : (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        distributionDerivative {i} (regularDistribution U (q i j))) =
        distributionDerivative {e} (regularDistribution U (q e e)) +
          ∑ p ∈ s, distributionDerivative {p.1} (regularDistribution U (q p.1 p.2)) := by
      rw [← Fintype.sum_prod_type']
      exact (Finset.add_sum_erase Finset.univ
        (fun p : Fin (m + 1) × Fin (m + 1) =>
          distributionDerivative {p.1} (regularDistribution U (q p.1 p.2)))
        (Finset.mem_univ (e, e))).symm
    rw [hs] at h
    have hsd : (∑ p ∈ s, distributionDerivative {p.1}
        (regularDistribution U (q p.1 p.2))) =
        ∑ p ∈ s, regularDistribution U (d p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (hd p (Finset.mem_erase.mp hp).1).1
    rw [hsd] at h
    change _ = regularLpLinear U (-f - ∑ p ∈ s, d p)
    rw [map_sub, map_neg, map_sum]
    change _ = -regularDistribution U f - ∑ p ∈ s, regularDistribution U (d p)
    rw [← h]
    abel
  have hbpos : ∀ x ∈ U, theta ≤ a e e x := by
    intro x hx
    have h := hA.2.2 x hx (coordinate (m + 1) e)
    rw [P102.U4.DifferenceQuotient.norm_coordinateVector, one_pow, mul_one] at h
    simpa only [a, P102.U4.coordinateVector, EuclideanSpace.inner_basisFun_real] using h
  have hnormal' : distributionDerivative {e} (regularDistribution U
      (fun x => a e e x * hFirstDerivative v e x)) = regularDistribution U R := by
    have hreg : regularDistribution U (q e e) = regularDistribution U
        (fun x => a e e x * hFirstDerivative v e x) :=
      (P102.U4.regular_injectivity (m + 1) ℝ U _ _
        (P102.U4.domainLp_locallyIntegrable U 2 _)
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((qm e e).locallyIntegrable (by norm_num)))).mpr (hq e e)
    rw [← hreg]
    exact hnormal
  obtain ⟨z, hz, _, hzB⟩ := normalRecovery U e (a e e) M L theta htheta
    (haL e e) hbpos (haM e e) (hFirstDerivative v e) R hnormal'
  have hRB : ‖R‖ ≤ ‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
      ((M : ℝ) * K + (L : ℝ) * ‖v‖) := by
    calc
      _ ≤ ‖f‖ + ‖∑ p ∈ s, d p‖ := by
        simpa only [R, norm_neg] using norm_sub_le (-f) (∑ p ∈ s, d p)
      _ ≤ ‖f‖ + ∑ p ∈ s, ‖d p‖ := add_le_add le_rfl (norm_sum_le _ _)
      _ ≤ ‖f‖ + ∑ _p ∈ s, ((M : ℝ) * K + (L : ℝ) * ‖v‖) := by
        gcongr with p hp
        exact (hd p (Finset.mem_erase.mp hp).1).2
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        gcongr
        have hc : s.card ≤ (m + 1) * (m + 1) := by
          exact (Finset.card_erase_le).trans_eq (by simp)
        exact_mod_cast (by simpa only [pow_two] using hc : s.card ≤ (m + 1) ^ 2)
  let B : ℝ := ‖v‖ + K + theta⁻¹ * (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
    ((M : ℝ) * K + (L : ℝ) * ‖v‖) + (L : ℝ) * ‖v‖)
  have htB : 0 ≤ theta⁻¹ * (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
      ((M : ℝ) * K + (L : ℝ) * ‖v‖) + (L : ℝ) * ‖v‖) := by positivity
  have hBv : ‖v‖ ≤ B := by dsimp only [B]; linarith
  have hBg : K ≤ B := by dsimp only [B]; linarith [norm_nonneg v]
  have hzNorm : ‖z‖ ≤ B := by
    apply hzB.trans
    calc
      _ ≤ theta⁻¹ * (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
          ((M : ℝ) * K + (L : ℝ) * ‖v‖) + (L : ℝ) * ‖v‖) := by
        gcongr
        exact InteriorH2.firstDerivative_norm_le U v e
      _ ≤ B := by dsimp only [B]; linarith [norm_nonneg v]
  let G (j i : Fin (m + 1)) : Lp ℝ U 2 := if (i, j) = (e, e) then z else g j i
  have hG (j i : Fin (m + 1)) : distributionDerivative {i}
      (regularDistribution U (hFirstDerivative v j)) = regularDistribution U (G j i) := by
    by_cases h : (i, j) = (e, e)
    · have hi : i = e := congrArg Prod.fst h
      have hj : j = e := congrArg Prod.snd h
      simpa [G, hi, hj] using hz
    · simpa only [G, ite_eq_right h] using hg j i h
  have hGB (j i : Fin (m + 1)) : ‖G j i‖ ≤ B := by
    by_cases h : (i, j) = (e, e)
    · simpa only [G, ite_eq_left h] using hzNorm
    · exact (by simpa only [G, ite_eq_right h] using hgB j i h : ‖G j i‖ ≤ K) |>.trans hBg
  obtain ⟨w, hw, hwB⟩ := InteriorH2.h2FromWeakDerivatives U (hUnderlying U 1 v)
    (hFirstDerivative v) G B
    (fun j => hilbertDerivativeDistribution U 1 v ⟨{j}, by simp⟩) hG
    ((PiLp.norm_apply_le _ _).trans hBv)
    (fun j => (InteriorH2.firstDerivative_norm_le U v j).trans hBv) hGB
  exact ⟨w, hw, hwB⟩


/-- Tangential second derivatives provide all mixed derivatives by distribution
commutation. The weak equation then recovers the last normal derivative. -/
theorem h2FromTangentialDerivatives {m : ℕ} (U : Domain (m + 1))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (M L : ℝ≥0) (theta : ℝ) (htheta : 0 < theta)
    (hA : P201Specs.InteriorH2.CoefficientBounds U A M L theta)
    (v : H ℝ U 1) (f : Lp ℝ U 2)
    (heq : P201Specs.InteriorH2.WeakEquation U A v f)
    (g : Fin (m + 1) → Fin (m + 1) → Lp ℝ U 2) (B : ℝ≥0)
    (hg : ∀ j k, k ≠ Fin.last m →
      distributionDerivative {k} (regularDistribution U (hFirstDerivative v j)) =
        regularDistribution U (g j k))
    (hgB : ∀ j k, k ≠ Fin.last m → ‖g j k‖ ≤ B) :
    ∃ w : H ℝ U 2, hUnderlying U 2 w = hUnderlying U 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex (m + 1) 2) : ℝ) *
        (‖v‖ + B + theta⁻¹ * (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 *
          ((M : ℝ) * B + (L : ℝ) * ‖v‖) + (L : ℝ) * ‖v‖)) := by
  classical
  let e : Fin (m + 1) := Fin.last m
  let G (j i : Fin (m + 1)) : Lp ℝ U 2 := if i = e then g i j else g j i
  have hcomm (j i : Fin (m + 1)) :
      distributionDerivative {i} (regularDistribution U (hFirstDerivative v j)) =
        distributionDerivative {j} (regularDistribution U (hFirstDerivative v i)) := by
    have hd (k : Fin (m + 1)) : distributionDerivative {k}
        (regularDistribution U (hUnderlying U 1 v)) =
          regularDistribution U (hFirstDerivative v k) :=
      hilbertDerivativeDistribution U 1 v ⟨{k}, by simp⟩
    calc
      _ = distributionDerivative {i} (distributionDerivative {j}
          (regularDistribution U (hUnderlying U 1 v))) := by rw [hd j]
      _ = distributionDerivative {j} (distributionDerivative {i}
          (regularDistribution U (hUnderlying U 1 v))) :=
        P102.U4.derivative_coordinateCommutation (m + 1) ℝ U i j _
      _ = _ := by rw [hd i]
  have hG (j i : Fin (m + 1)) (hp : (i, j) ≠ (e, e)) :
      distributionDerivative {i} (regularDistribution U (hFirstDerivative v j)) =
        regularDistribution U (G j i) := by
    by_cases hi : i = e
    · have hj : j ≠ e := fun hj => hp (Prod.ext hi hj)
      simpa only [G, ite_eq_left hi] using (hcomm j i).trans (hg i j hj)
    · simpa only [G, ite_eq_right hi] using hg j i hi
  have hGB (j i : Fin (m + 1)) (hp : (i, j) ≠ (e, e)) : ‖G j i‖ ≤ B := by
    by_cases hi : i = e
    · have hj : j ≠ e := fun hj => hp (Prod.ext hi hj)
      simpa only [G, ite_eq_left hi] using hgB i j hj
    · simpa only [G, ite_eq_right hi] using hgB j i hi
  exact normalAssembly U A M L theta htheta hA v f heq G B B.coe_nonneg hG hGB

/-- Uniform tangential quotients imply H², without relative compactness of
U in V. Their common bound is converted to actual L² derivatives on U. -/
theorem h2FromTangentialQuotients {m : ℕ} (U V : Domain (m + 1)) (hUV : U ≤ V)
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (M L : ℝ≥0) (theta : ℝ) (htheta : 0 < theta)
    (hA : P201Specs.InteriorH2.CoefficientBounds V A M L theta)
    (v : H ℝ V 1) (f : Lp ℝ V 2)
    (heq : P201Specs.InteriorH2.WeakEquation V A v f) (B : ℝ≥0)
    (hb : ∀ j k : Fin (m + 1), k ≠ Fin.last m →
      ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
        MemLp (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ∧
        eLpNorm (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ≤ B) :
    ∃ w : H ℝ U 2,
      (hUnderlying U 2 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex (m + 1) 2) : ℝ) *
        ((1 + ((m + 1 : ℕ) : ℝ)) * ‖v‖ + B + theta⁻¹ *
          (‖f‖ + ((m + 1 : ℕ) : ℝ) ^ 2 * ((M : ℝ) * B +
            (L : ℝ) * ((1 + ((m + 1 : ℕ) : ℝ)) * ‖v‖)) +
            (L : ℝ) * ((1 + ((m + 1 : ℕ) : ℝ)) * ‖v‖))) := by
  classical
  obtain ⟨vU, hvU, hvUd, hvUn⟩ := h1Restriction V U hUV v
  let fU : Lp ℝ U 2 := InteriorH2.restrictLp hUV f
  have hfU : (fU : Space (m + 1) → ℝ) =ᵐ[domainMeasure U] f :=
    InteriorH2.restrictLp_ae hUV f
  have hfUn : ‖fU‖ ≤ ‖f‖ := InteriorH2.restrictLp_norm_le hUV f
  have hUeq : P201Specs.InteriorH2.WeakEquation U A vU fU :=
    weakEquationRestriction V U hUV A v vU f fU hvUd hfU heq
  have hAU : P201Specs.InteriorH2.CoefficientBounds U A M L theta :=
    ⟨(fun x hx => hA.1 x (hUV hx)), hA.2.1.mono hUV,
      (fun x hx => hA.2.2 x (hUV hx))⟩
  have hder (j k : Fin (m + 1)) (hk : k ≠ Fin.last m) :
      ∃ d : Lp ℝ U 2,
        distributionDerivative {k} (regularDistribution U (hFirstDerivative vU j)) =
          regularDistribution U d ∧ ‖d‖ ≤ B := by
    obtain ⟨d, hd, hdB⟩ := derivativeFromBoundaryQuotients (by omega) U V hUV
      (hFirstDerivative v j) k B (hb j k hk)
    have he : hFirstDerivative vU j = InteriorH2.restrictLp hUV (hFirstDerivative v j) :=
      Lp.ext ((hvUd j).trans (InteriorH2.restrictLp_ae hUV _).symm)
    refine ⟨d, ?_, hdB⟩
    rw [he, InteriorH2.regular_restrictLp]
    exact hd
  let g (j k : Fin (m + 1)) : Lp ℝ U 2 :=
    if hk : k = Fin.last m then 0 else (hder j k hk).choose
  have hg (j k : Fin (m + 1)) (hk : k ≠ Fin.last m) :
      distributionDerivative {k} (regularDistribution U (hFirstDerivative vU j)) =
        regularDistribution U (g j k) ∧ ‖g j k‖ ≤ B := by
    simpa only [g, dite_eq_right hk] using (hder j k hk).choose_spec
  obtain ⟨w, hw, hwn⟩ := h2FromTangentialDerivatives U A M L theta htheta hAU vU fU hUeq
    g B (fun j k hk => (hg j k hk).1) (fun j k hk => (hg j k hk).2)
  refine ⟨w, ?_, hwn.trans ?_⟩
  · rw [hw]
    exact hvU
  · gcongr

lemma chart_inverse_differential {n : ℕ} (U V : Domain n) (LF LG : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V LF LG)
    (hF : DifferentiableOn ℝ F.toFun V) (hG : DifferentiableOn ℝ F.invFun U)
    (y : Space n) (hy : y ∈ V) :
    (fderiv ℝ F.invFun (F.toFun y)).comp (fderiv ℝ F.toFun y) =
      ContinuousLinearMap.id ℝ (Space n) := by
  have hdF := (hF.differentiableAt
    (V.isOpen.mem_nhds hy)).hasFDerivAt
  have hdG := (hG.differentiableAt
    (U.isOpen.mem_nhds (F.mapsTo hy))).hasFDerivAt
  have hid : (fun x => F.invFun (F.toFun x)) =ᶠ[nhds y] (fun x => x) := by
    filter_upwards [V.isOpen.mem_nhds hy] with x hx
    exact F.left_inv x hx
  exact (hdG.comp y hdF).unique ((hasFDerivAt_id y).congr_of_eventuallyEq hid)

lemma coordinateCoefficientBounds {n : ℕ} (U V : Domain n) (LF LG HG : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V LF LG)
    (hF : DifferentiableOn ℝ F.toFun V) (hG : DifferentiableOn ℝ F.invFun U)
    (hDG : LipschitzOnWith HG (fderiv ℝ F.invFun) U)
    (A : Space n → Space n →L[ℝ] Space n) (M LA : ℝ≥0) (theta : ℝ)
    (htheta : 0 < theta) (hA : P201Specs.InteriorH2.CoefficientBounds U A M LA theta) :
    P201Specs.InteriorH2.CoefficientBounds V
      (fun y => conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y)))
      (LG ^ 2 * M)
      (2 * LG * M * (HG * LF) + LG ^ 2 * (LA * LF))
      (theta / (max 1 (LF : ℝ)) ^ 2) := by
  let J : Space n → Space n →L[ℝ] Space n := fun y => fderiv ℝ F.invFun (F.toFun y)
  have hJ (y : Space n) (hy : y ∈ V) : ‖J y‖ ≤ (LG : ℝ) :=
    norm_fderiv_le_of_lipschitzOn ℝ (U.isOpen.mem_nhds (F.mapsTo hy)) F.inv_lipschitz
  have hAJ (y : Space n) (hy : y ∈ V) : ‖A (F.toFun y)‖ ≤ (M : ℝ) :=
    hA.1 _ (F.mapsTo hy)
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    calc
      _ ≤ ‖J y‖ ^ 2 * ‖A (F.toFun y)‖ := conjugateNorm _ _
      _ ≤ (LG : ℝ) ^ 2 * (M : ℝ) := by
        gcongr
        · exact hJ y hy
        · exact hAJ y hy
      _ = _ := by push_cast; rfl
  · exact conjugateLipschitz V J (fun y => A (F.toFun y)) LG M (HG * LF) (LA * LF)
      hJ hAJ (hDG.comp F.lipschitz F.mapsTo) (hA.2.1.comp F.lipschitz F.mapsTo)
  · intro y hy ξ
    apply conjugateEllipticity (J y) (A (F.toFun y)) theta (max 1 (LF : ℝ))
      htheta (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (hA.2.2 _ (F.mapsTo hy)) _ ξ
    intro ζ
    have h := inverseAdjointBound (J y) (fderiv ℝ F.toFun y)
      (chart_inverse_differential U V LF LG F hF hG y hy) ζ
    exact h.trans (mul_le_mul_of_nonneg_right
      ((norm_fderiv_le_of_lipschitzOn ℝ (V.isOpen.mem_nhds hy) F.lipschitz).trans
        (le_max_right _ _)) (norm_nonneg _))


/-- Multiplying a whole-space zero extension by an ambient smooth cutoff
produces an actual local H¹₀ test, even where the cutoff meets the flat face. -/
theorem flatLocalized_mem_hZero {m : ℕ} (U : Domain (m + 1))
    (χ : Test ℝ (⊤ : Domain (m + 1)))
    (hχU : tsupport χ ∩ (P102.Trace.halfSpace m : Set (Space (m + 1))) ⊆ U)
    (z : H ℝ (⊤ : Domain (m + 1)) 1)
    (hz : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (v : H ℝ U 1)
    (hv : (hUnderlying U 1 v : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
      (fun x => χ x * hUnderlying ⊤ 1 z x)) :
    v ∈ P201Specs.hZeroSubmodule ℝ U := by
  let zw := hToW ℝ ⊤ 1 z
  let vw := hToW ℝ U 1 v
  obtain ⟨M, hM⟩ := P102.Trace.Ordinary.exists_wholeSobolevCutoffCLM
    (𝕜 := ℝ) (k := 1) 2 χ χ.contDiff χ.hasCompactSupport
  have hback : P102.Trace.restrictWholeSobolev U (M zw) = vw := by
    apply P102.U4.sobolevUnderlying_injective U 1 2
    apply Lp.ext
    exact ((P102.Trace.restrictWholeLp_ae U (P102.U4.sobolevUnderlying (M zw))).trans
      (ae_restrict_of_ae (hM zw))).trans hv.symm
  rw [hZeroClosureBridge ℝ U]
  change vw ∈ closure (P102.U4.smoothSobolevSubmodule ℝ U 1 2 : Set _)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨φ, w, hrep, herr⟩ := P102.Trace.halfSpace_approximation_of_wholeSpace
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) zw hz
    (div_pos hε (by positivity : 0 < ‖M‖ + 1))
  let ψ : Test ℝ U := ⟨fun x => χ x * φ x, χ.contDiff.mul φ.contDiff,
    χ.hasCompactSupport.mul_right, fun x hx =>
      hχU ⟨tsupport_mul_subset_left hx,
        φ.tsupport_subset (tsupport_mul_subset_right hx)⟩⟩
  let wU := P102.Trace.restrictWholeSobolev U (M w)
  have hwφ : P102.U4.sobolevUnderlying wU = P102.U4.testToDomainLp U 2 ψ := by
    apply Lp.ext
    have hφ0 := hrep (P102.U4.zeroSobolevIndex (m + 1) 1)
    simp only [P102.U4.zeroSobolevIndex, P102.U4.multiPartial,
      Multiset.sort_zero, P102.U4.partialWord] at hφ0
    filter_upwards [P102.Trace.restrictWholeLp_ae U (P102.U4.sobolevUnderlying (M w)),
      ae_restrict_of_ae (hM w), ae_restrict_of_ae hφ0,
      P102.U4.testToDomainLp_ae U 2 ψ] with x hx hm hφ hψ
    have hval : χ x • P102.U4.sobolevUnderlying w x = ψ x := by
      change χ x * P102.U4.sobolevUnderlying w x = χ x * φ x
      congr 1
    exact hx.trans (hm.trans (hval.trans hψ.symm))
  refine ⟨wU, ⟨ψ, hwφ.symm⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, ← hback]
  calc
    ‖P102.Trace.restrictWholeSobolev U (M w) -
        P102.Trace.restrictWholeSobolev U (M zw)‖ ≤ ‖M w - M zw‖ :=
      P102.Trace.restrictWholeSobolev_norm_sub_le U (M w) (M zw)
    _ ≤ ‖M‖ * ‖w - zw‖ := by
      rw [← M.map_sub]
      exact M.le_opNorm _
    _ ≤ (‖M‖ + 1) * ‖w - zw‖ := by nlinarith [norm_nonneg (w - zw)]
    _ < (‖M‖ + 1) * (ε / (‖M‖ + 1)) :=
      mul_lt_mul_of_pos_left herr (by positivity)
    _ = ε := mul_div_cancel₀ ε (by positivity : (‖M‖ + 1) ≠ 0)

/-- An admissible tangential quotient test localized away from the artificial
faces; the compact support container is allowed to meet the flat face. -/
theorem localTangentialQuotientTest {m : ℕ} (W U : Domain (m + 1))
    (hWU : (W : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ U)
    (z : H ℝ (⊤ : Domain (m + 1)) 1) (K : Compacts (Space (m + 1)))
    (hKW : (K : Set (Space (m + 1))) ⊆ W)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (hz : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ)
    (ha : ∀ x ∈ K, x - h • coordinate (m + 1) k ∈ W) :
    ∃ t : H10 ℝ U,
      (hZeroUnderlying U t : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
        differenceQuotient (hUnderlying ⊤ 1 z) k h ∧
      ∀ j, (hFirstDerivative t.val j : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
        differenceQuotient (hFirstDerivative z j) k h := by
  let a := h • coordinate (m + 1) k
  let K' : Compacts (Space (m + 1)) :=
    ⟨(K : Set (Space (m + 1))) ∪ (fun x => x - a) '' (K : Set (Space (m + 1))),
      K.isCompact.union (K.isCompact.image (by fun_prop))⟩
  have hK'W : (K' : Set (Space (m + 1))) ⊆ W := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hKW hx
    · exact ha y hy
  obtain ⟨q, hq, _hqd⟩ := InteriorH2.h1Quotient ⊤ ⊤ le_top k h
    (fun _ _ => mem_univ _) z
  have hq' : (hUnderlying ⊤ 1 q : Space (m + 1) → ℝ) =ᵐ[volume]
      differenceQuotient (hUnderlying ⊤ 1 z) k h := by
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using hq
  have hcoord : coordinate (m + 1) k (Fin.last m) = 0 := by
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, Ne.symm hk]
  have hheight (x : Space (m + 1)) :
      (x + a) (Fin.last m) = x (Fin.last m) := by
    change x (Fin.last m) + h * coordinate (m + 1) k (Fin.last m) = _
    rw [hcoord, mul_zero, add_zero]
  have hzshift := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hz
  have hqbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 q x = 0 := by
    filter_upwards [hq', hz, hzshift] with x hx hxz hxs hxneg
    rw [hx]
    change h⁻¹ • (hUnderlying ⊤ 1 z (x + a) - hUnderlying ⊤ 1 z x) = 0
    rw [hxz hxneg, hxs (by rw [hheight]; exact hxneg), sub_self, smul_zero]
  have hKshift := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hK
  have hqoff : ∀ᵐ x ∂volume, x ∉ K' → hUnderlying ⊤ 1 q x = 0 := by
    filter_upwards [hq', hK, hKshift] with x hx hxK hxS hxnot
    have hxK' : x ∉ K := fun hx => hxnot (Or.inl hx)
    have hxaK : x + a ∉ K := by
      intro hxa
      exact hxnot (Or.inr ⟨x + a, hxa, add_sub_cancel_right x a⟩)
    rw [hx]
    change h⁻¹ • (hUnderlying ⊤ 1 z (x + a) - hUnderlying ⊤ 1 z x) = 0
    rw [hxK hxK', hxS hxaK, sub_self, smul_zero]
  obtain ⟨χ, _, N, hK'N, _, hχone⟩ := P102.U4.cutoff (m + 1) W K' hK'W
  let η : Test ℝ (⊤ : Domain (m + 1)) :=
    ⟨χ, χ.contDiff, χ.hasCompactSupport, subset_univ _⟩
  have hηU : tsupport η ∩ (P102.Trace.halfSpace m : Set (Space (m + 1))) ⊆ U := by
    rintro x ⟨hxχ, hxH⟩
    exact hWU ⟨χ.tsupport_subset hxχ, hxH⟩
  have hηq : (hUnderlying ⊤ 1 q : Space (m + 1) → ℝ) =ᵐ[volume]
      (fun x => η x * hUnderlying ⊤ 1 q x) := by
    filter_upwards [hqoff] with x hx
    by_cases hxK : x ∈ K'
    · change _ = χ x * _
      rw [hχone x (hK'N hxK), one_mul]
    · rw [hx hxK, mul_zero]
  obtain ⟨t, ht, htd⟩ := InteriorH2.h1Quotient U ⊤ le_top k h
    (fun _ _ => mem_univ _) z
  have hqU : (hUnderlying ⊤ 1 q : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
      differenceQuotient (hUnderlying ⊤ 1 z) k h := ae_restrict_of_ae hq'
  have hηqU : (hUnderlying ⊤ 1 q : Space (m + 1) → ℝ) =ᵐ[domainMeasure U]
      (fun x => η x * hUnderlying ⊤ 1 q x) := ae_restrict_of_ae hηq
  exact ⟨⟨t, flatLocalized_mem_hZero U η hηU q hqbelow t
    ((ht.trans hqU.symm).trans hηqU)⟩, ht, htd⟩

/-- The actual local discrete energy identity. Smooth tests and the weak
equation are imposed only on the chart's upper-side open set V. -/
theorem localBoundary_discrete_energy_identity {m : ℕ}
    (W V : Domain (m + 1))
    (hWV : (W : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (F : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure V))
    (f : Lp ℝ V 2)
    (heq : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x)
    (z : H ℝ (⊤ : Domain (m + 1)) 1) (K : Compacts (Space (m + 1)))
    (hKW : (K : Set (Space (m + 1))) ⊆ W)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (hzbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ K, x + h • coordinate (m + 1) k ∈ W) :
    (∑ j : Fin (m + 1), ∫ x,
      differenceQuotient (P102.U4.lpZeroExtension V 2
        (InteriorH2.fluxCoordinate F j)) k h x * hFirstDerivative z j x) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
  have hn : 1 ≤ m + 1 := by omega
  obtain ⟨t, ht, htd⟩ := localTangentialQuotientTest W V hWV z K hKW hK
    hzbelow k hk (-h) (by
      intro x hx
      simpa only [neg_smul, sub_neg_eq_add] using ha x hx)
  have htest (φ : Test ℝ V) (w : H10 ℝ V)
      (hw : hZeroUnderlying V w = P102.U4.testToDomainLp V 2 φ) :
      negativeDivergenceDistribution V F φ = pivot V f w := by
    rw [InteriorTesting.negativeDivergenceDistribution_pairing, pivotPairing, hw]
    change (∫ x in V, inner ℝ (F x) (gradient φ x)) = _
    rw [heq φ]
    apply integral_congr_ae
    filter_upwards [P102.U4.testToDomainLp_ae V 2 φ] with x hx
    rw [hx]
  have henergy := InteriorTesting.energyTesting hn V F (pivot V f) htest t
  rw [pivotPairing] at henergy
  have hcoord (j : Fin (m + 1)) :
      (∫ x, differenceQuotient (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j)) k h x *
        hFirstDerivative z j x) =
      -(∫ x in V, InteriorH2.fluxCoordinate F j x * hFirstDerivative t.val j x) := by
    have hF : MemLp (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j) : Space (m + 1) → ℝ)
        2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        (MeasureTheory.Lp.memLp (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j)))
    have hz : MemLp (hFirstDerivative z j : Space (m + 1) → ℝ) 2 volume := by
      simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top, Measure.restrict_univ]
        using (MeasureTheory.Lp.memLp (hFirstDerivative z j))
    have hzT : MemLp (fun x => hFirstDerivative z j (x - h • coordinate (m + 1) k)) 2 volume :=
      hz.comp_measurePreserving (measurePreserving_sub_right volume _)
    rw [discreteIntegrationByPartsWholeSpace hn _ _ k h hh
      (hF.integrable_mul hz) (hF.integrable_mul hzT)]
    rw [P102.U4.integral_lpZeroExtension_mul V 2]
    congr 1
    apply integral_congr_ae
    filter_upwards [htd j] with x hx
    rw [hx]
  change (∑ j : Fin (m + 1), ∫ x,
    differenceQuotient (P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j)) k h x *
      hFirstDerivative z j x) =
    -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x)
  simp_rw [hcoord]
  rw [Finset.sum_neg_distrib, ← InteriorH2.fluxFunctional_eq_sum, InteriorTesting.fluxFunctional_integral,
    henergy]
  congr 1
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx]

end P201.BoundaryH2

namespace P201.BoundaryH2

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def graphShear (P : E →L[ℝ] F) (ν : E) (φ : F → ℝ) (x : E) : E :=
  x + φ (P x) • ν

def graphShearDifferential (P : E →L[ℝ] F) (ν : E) (D : F →L[ℝ] ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E + (D.comp P).smulRight ν

lemma hasFDerivAt_graphShear (P : E →L[ℝ] F) (ν : E) (φ : F → ℝ)
    (x : E) (hφ : DifferentiableAt ℝ φ (P x)) :
    HasFDerivAt (graphShear P ν φ)
      (graphShearDifferential P ν (fderiv ℝ φ (P x))) x := by
  exact (hasFDerivAt_id x).add ((hφ.hasFDerivAt.comp x P.hasFDerivAt).smul_const ν)

lemma fderiv_graphShear (P : E →L[ℝ] F) (ν : E) (φ : F → ℝ)
    (x : E) (hφ : DifferentiableAt ℝ φ (P x)) :
    fderiv ℝ (graphShear P ν φ) x =
      graphShearDifferential P ν (fderiv ℝ φ (P x)) :=
  (hasFDerivAt_graphShear P ν φ x hφ).fderiv

lemma graphShearDifferential_inverse (P : E →L[ℝ] F) (ν : E) (hν : P ν = 0)
    (D : F →L[ℝ] ℝ) :
    (graphShearDifferential P ν (-D)).comp (graphShearDifferential P ν D) =
      ContinuousLinearMap.id ℝ E := by
  ext x
  simp [graphShearDifferential, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, hν]

lemma graphShear_inverse (P : E →L[ℝ] F) (ν : E) (hν : P ν = 0)
    (φ : F → ℝ) (x : E) :
    graphShear P ν (fun y => -φ y) (graphShear P ν φ x) = x := by
  simp [graphShear, map_add, map_smul, hν]

lemma lipschitz_graphShearDifferential (P : E →L[ℝ] F) (ν : E)
    (D : F → F →L[ℝ] ℝ) (S : Set F) (H : ℝ≥0)
    (hD : LipschitzOnWith H D S) :
    LipschitzOnWith (H * ‖P‖₊ ^ 2 * ‖ν‖₊)
      (fun x => graphShearDifferential P ν (D (P x))) (P ⁻¹' S) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm]
  have he : graphShearDifferential P ν (D (P x)) - graphShearDifferential P ν (D (P y)) =
      ((D (P x) - D (P y)).comp P).smulRight ν := by
    ext z
    simp [graphShearDifferential, sub_smul]
  rw [he]
  calc
    _ ≤ ‖(D (P x) - D (P y)).comp P‖ * ‖ν‖ := le_of_eq (ContinuousLinearMap.norm_smulRight_apply _ _)
    _ ≤ (‖D (P x) - D (P y)‖ * ‖P‖) * ‖ν‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((H : ℝ) * ‖P x - P y‖ * ‖P‖) * ‖ν‖ := by
      gcongr
      simpa only [dist_eq_norm] using hD.dist_le_mul (P x) hx (P y) hy
    _ ≤ ((H : ℝ) * (‖P‖ * ‖x-y‖) * ‖P‖) * ‖ν‖ := by
      gcongr
      simpa only [map_sub] using P.le_opNorm (x-y)
    _ = _ := by push_cast; rw [dist_eq_norm]; ring

end P201.BoundaryH2
namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry

/-- The graph shear differential is locally Lipschitz under exactly C¹,¹ data. -/
lemma fderiv_graphShear_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F) (ν : E) (φ : F → ℝ) (S : Set F) (H : ℝ≥0)
    (hd : ∀ y ∈ S, DifferentiableAt ℝ φ y)
    (hL : LipschitzOnWith H (fderiv ℝ φ) S) :
    LipschitzOnWith (H * ‖P‖₊ ^ 2 * ‖ν‖₊)
      (fderiv ℝ (graphShear P ν φ)) (P ⁻¹' S) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [fderiv_graphShear P ν φ x (hd _ hx), fderiv_graphShear P ν φ y (hd _ hy)]
  exact (lipschitz_graphShearDifferential P ν (fderiv ℝ φ) S H hL).dist_le_mul x hx y hy

lemma shear_eq_graphShear {m : ℕ} (φ : Space m → ℝ) :
    shear φ = graphShear horizontal (WithLp.toLp 2 (0, (1:ℝ))) φ := by
  funext x
  apply (WithLp.equiv 2 (Space m × ℝ)).injective
  ext <;> simp [shear, graphShear, horizontal, add_comm]

lemma hasFDerivAt_shear {m : ℕ} (φ : Space m → ℝ) (x : Ambient m)
    (hφ : DifferentiableAt ℝ φ x.ofLp.1) :
    HasFDerivAt (shear φ)
      (graphShearDifferential horizontal (WithLp.toLp 2 (0, (1:ℝ)))
        (fderiv ℝ φ x.ofLp.1)) x := by
  rw [shear_eq_graphShear]
  exact hasFDerivAt_graphShear _ _ _ _ hφ

lemma fderiv_shear_lipschitz {m : ℕ} (φ : Space m → ℝ) (S : Set (Space m))
    (H : ℝ≥0) (hd : ∀ y ∈ S, DifferentiableAt ℝ φ y)
    (hL : LipschitzOnWith H (fderiv ℝ φ) S) :
    LipschitzOnWith (H * ‖(horizontal : Ambient m →L[ℝ] Space m)‖₊ ^ 2 *
      ‖(WithLp.toLp 2 (0, (1:ℝ)) : Ambient m)‖₊) (fderiv ℝ (shear φ)) (strip S) := by
  rw [shear_eq_graphShear]
  exact fderiv_graphShear_lipschitz _ _ _ _ _ hd hL

lemma shear_differential_inverse {m : ℕ} (D : Space m →L[ℝ] ℝ) :
    (graphShearDifferential horizontal (WithLp.toLp 2 (0, (1:ℝ))) (-D)).comp
      (graphShearDifferential horizontal (WithLp.toLp 2 (0, (1:ℝ))) D) =
    ContinuousLinearMap.id ℝ (Ambient m) :=
  graphShearDifferential_inverse _ _ (by rfl) D

end P201.BoundaryH2
namespace P201.BoundaryH2
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma lipschitz_sandwich (A : F →L[ℝ] G) (B : E →L[ℝ] F)
    (D : E → F →L[ℝ] F) (S : Set E) (H : ℝ≥0) (hD : LipschitzOnWith H D S) :
    LipschitzOnWith (‖A‖₊ * H * ‖B‖₊) (fun x => A.comp ((D x).comp B)) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm]
  have he : A.comp ((D x).comp B) - A.comp ((D y).comp B) =
      A.comp ((D x - D y).comp B) := by ext z; simp
  rw [he]
  calc
    _ ≤ ‖A‖ * ‖(D x - D y).comp B‖ := A.opNorm_comp_le _
    _ ≤ ‖A‖ * (‖D x - D y‖ * ‖B‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (((H : ℝ) * dist x y) * ‖B‖) := by
      gcongr
      simpa only [dist_eq_norm] using hD.dist_le_mul x hx y hy
    _ = _ := by push_cast; ring

open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

lemma physicalChartMap_fderiv_lipschitz {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (Ω : Opens (Space (m+1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (H : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith H (fderiv ℝ C.graphFunction) (ball C.center C.radius)) :
    ∃ Hder : ℝ≥0, LipschitzOnWith Hder
      (fderiv ℝ (physicalChartMap e q Ω C).toFun)
      (flatChartOpen q C.center C.radius C.height) := by
  let A : Ambient m →L[ℝ] Space (m+1) := e.toContinuousLinearMap.comp
    C.frame.toAffineIsometry.toContinuousAffineMap.contLinear
  let B : Space (m+1) →L[ℝ] Ambient m := q.symm.toContinuousLinearMap
  let S := (flatChartOpen q C.center C.radius C.height : Set (Space (m+1)))
  let D := fun z : Ambient m => fderiv ℝ (shear C.graphFunction) z
  have hdiff : ∀ y ∈ ball C.center C.radius,
      DifferentiableAt ℝ C.graphFunction y := by
    intro y hy
    exact (hC.differentiableOn (by simp) y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  have hD := fderiv_shear_lipschitz C.graphFunction (ball C.center C.radius) H hdiff hL
  have hmap : MapsTo B S (strip (ball C.center C.radius)) := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hx
    change (q.symm (q z)).ofLp.1 ∈ ball C.center C.radius
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hz.1
  have hDB := hD.comp B.lipschitzWith.lipschitzOnWith hmap
  have hf (x : Space (m+1)) (hx : x ∈ S) :
      fderiv ℝ (physicalChartMap e q Ω C).toFun x = A.comp ((D (B x)).comp B) := by
    have hshear := hasFDerivAt_shear C.graphFunction (B x) (hdiff _ (hmap hx))
    have h := e.toContinuousLinearMap.hasFDerivAt.comp x
      (C.frame.toAffineIsometry.toContinuousAffineMap.hasFDerivAt.comp x
        (hshear.comp x B.hasFDerivAt))
    change HasFDerivAt (physicalChartMap e q Ω C).toFun _ x at h
    rw [h.fderiv]
    dsimp only [A, D]
    rw [hshear.fderiv]
    ext z
    rfl
  let Hder := ‖A‖₊ * (H * ‖(horizontal : Ambient m →L[ℝ] Space m)‖₊ ^ 2 *
    ‖(WithLp.toLp 2 (0, (1:ℝ)) : Ambient m)‖₊ * ‖B‖₊) * ‖B‖₊
  refine ⟨Hder, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  rw [hf x hx, hf y hy]
  exact (lipschitz_sandwich A B (fun x => D (B x)) S _ hDB).dist_le_mul x hx y hy
end P201.BoundaryH2
namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

lemma hasFDerivAt_unshear {m : ℕ} (φ : Space m → ℝ) (x : Ambient m)
    (hφ : DifferentiableAt ℝ φ x.ofLp.1) :
    HasFDerivAt (unshear φ)
      (graphShearDifferential horizontal (WithLp.toLp 2 (0, (1:ℝ)))
        (-fderiv ℝ φ x.ofLp.1)) x := by
  rw [unshear_eq_shear_neg, shear_eq_graphShear]
  exact (hasFDerivAt_id x).add ((hφ.hasFDerivAt.neg.comp x horizontal.hasFDerivAt).smul_const _)

lemma fderiv_unshear_lipschitz {m : ℕ} (φ : Space m → ℝ) (S : Set (Space m))
    (H : ℝ≥0) (hd : ∀ y ∈ S, DifferentiableAt ℝ φ y)
    (hL : LipschitzOnWith H (fderiv ℝ φ) S) :
    LipschitzOnWith (H * ‖(horizontal : Ambient m →L[ℝ] Space m)‖₊ ^ 2 *
      ‖(WithLp.toLp 2 (0, (1:ℝ)) : Ambient m)‖₊) (fderiv ℝ (unshear φ)) (strip S) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [(hasFDerivAt_unshear φ x (hd _ hx)).fderiv, (hasFDerivAt_unshear φ y (hd _ hy)).fderiv]
  exact (lipschitz_graphShearDifferential horizontal (WithLp.toLp 2 (0,(1:ℝ)))
    (fun z => -fderiv ℝ φ z) S H hL.neg).dist_le_mul x hx y hy

lemma physicalChartMap_inverse_fderiv_lipschitz {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (Ω : Opens (Space (m+1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (H : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith H (fderiv ℝ C.graphFunction) (ball C.center C.radius)) :
    ∃ Hder : ℝ≥0, LipschitzOnWith Hder
      (fderiv ℝ (physicalChartMap e q Ω C).invFun)
      (physicalChartOpen e Ω C) := by
  let A : Ambient m →L[ℝ] Space (m+1) := q.toContinuousLinearMap
  let B : Space (m+1) →L[ℝ] Ambient m :=
    C.frame.symm.toAffineIsometry.toContinuousAffineMap.contLinear.comp e.symm.toContinuousLinearMap
  let b : Space (m+1) → Ambient m := fun x => C.frame.symm (e.symm x)
  let S := (physicalChartOpen e Ω C : Set (Space (m+1)))
  let D := fun z : Ambient m => fderiv ℝ (unshear C.graphFunction) z
  have hdiff : ∀ y ∈ ball C.center C.radius,
      DifferentiableAt ℝ C.graphFunction y := by
    intro y hy
    exact (hC.differentiableOn (by simp) y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  have hD := fderiv_unshear_lipschitz C.graphFunction (ball C.center C.radius) H hdiff hL
  have hmap : MapsTo b S (strip (ball C.center C.radius)) := by
    intro x hx
    obtain ⟨u,⟨v,⟨w,hw,rfl⟩,rfl⟩,rfl⟩ := hx.2
    change (C.frame.symm (e.symm (e (C.frame (shear C.graphFunction w))))).ofLp.1 ∈
      ball C.center C.radius
    simpa only [LinearIsometryEquiv.symm_apply_apply, AffineIsometryEquiv.symm_apply_apply,
      shear, WithLp.ofLp_toLp] using hw.1
  have hblip : LipschitzWith 1 b := by
    simpa only [b, Function.comp_def, one_mul] using C.frame.symm.isometry.lipschitzWith.comp e.symm.isometry.lipschitzWith
  have hDB := hD.comp hblip.lipschitzOnWith hmap
  have hf (x : Space (m+1)) (hx : x ∈ S) :
      fderiv ℝ (physicalChartMap e q Ω C).invFun x = A.comp ((D (b x)).comp B) := by
    have hunshear := hasFDerivAt_unshear C.graphFunction (b x) (hdiff _ (hmap hx))
    have h := q.toContinuousLinearMap.hasFDerivAt.comp x
      (hunshear.comp x (C.frame.symm.toAffineIsometry.toContinuousAffineMap.hasFDerivAt.comp x
        e.symm.toContinuousLinearMap.hasFDerivAt))
    change HasFDerivAt (physicalChartMap e q Ω C).invFun _ x at h
    rw [h.fderiv]
    dsimp only [A, D]
    rw [hunshear.fderiv]
  let Hder := ‖A‖₊ * (H * ‖(horizontal : Ambient m →L[ℝ] Space m)‖₊ ^ 2 *
    ‖(WithLp.toLp 2 (0, (1:ℝ)) : Ambient m)‖₊ * 1) * ‖B‖₊
  refine ⟨Hder, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  rw [hf x hx, hf y hy]
  exact (lipschitz_sandwich A B (fun x => D (b x)) S _ hDB).dist_le_mul x hx y hy
end P201.BoundaryH2
namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

lemma physicalGraphH2Transport {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] P201.Space (m+1)) (Ω : P201.Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (Hder : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius)) :
    ∃ (Cpull Cpush : ℝ), 0 < Cpull ∧ 0 < Cpush ∧
      (∀ u : P201.H ℝ (physicalChartOpen e Ω C) 2,
        ∃ w : P201.H ℝ (flatChartOpen q C.center C.radius C.height) 2,
          (P201.hUnderlying _ 2 w : P201.Space (m+1) → ℝ) =ᵐ[P201.domainMeasure (flatChartOpen q C.center C.radius C.height)]
            (fun x => P201.hUnderlying _ 2 u ((physicalChartMap e q Ω C).toFun x)) ∧
          ‖w‖ ≤ Cpull * ‖u‖) ∧
      (∀ w : P201.H ℝ (flatChartOpen q C.center C.radius C.height) 2,
        ∃ u : P201.H ℝ (physicalChartOpen e Ω C) 2,
          (P201.hUnderlying _ 2 u : P201.Space (m+1) → ℝ) =ᵐ[P201.domainMeasure (physicalChartOpen e Ω C)]
            (fun x => P201.hUnderlying _ 2 w ((physicalChartMap e q Ω C).invFun x)) ∧
          ‖u‖ ≤ Cpush * ‖w‖) := by
  let F := physicalChartMap e q Ω C
  let G : BiLipschitzChart (flatChartOpen q C.center C.radius C.height)
      (physicalChartOpen e Ω C) (shearConstant C.constant) (shearConstant C.constant) :=
    { toFun := F.invFun
      invFun := F.toFun
      mapsTo := F.inv_mapsTo
      inv_mapsTo := F.mapsTo
      left_inv := F.right_inv
      right_inv := F.left_inv
      lipschitz := F.inv_lipschitz
      inv_lipschitz := F.lipschitz }
  obtain ⟨Hf,hf⟩ := physicalChartMap_fderiv_lipschitz e q Ω C Hder hC hL
  obtain ⟨Hg,hg⟩ := physicalChartMap_inverse_fderiv_lipschitz e q Ω C Hder hC hL
  obtain ⟨Cpull,hCpull,hpull⟩ := coordinateH2Pullback (Nat.succ_pos m) _ _ _ _ Hf F hf
  obtain ⟨Cpush,hCpush,hpush⟩ := coordinateH2Pullback (Nat.succ_pos m) _ _ _ _ Hg G hg
  exact ⟨Cpull,Cpush,hCpull,hCpush,hpull,hpush⟩
end P201.BoundaryH2

namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary
lemma physicalChartMap_differentiable {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (Ω : Opens (Space (m+1)))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius)) :
    (∀ x ∈ flatChartOpen q C.center C.radius C.height,
      DifferentiableAt ℝ (physicalChartMap e q Ω C).toFun x) ∧
    (∀ x ∈ physicalChartOpen e Ω C,
      DifferentiableAt ℝ (physicalChartMap e q Ω C).invFun x) := by
  have hdiff : ∀ y ∈ ball C.center C.radius,
      DifferentiableAt ℝ C.graphFunction y := by
    intro y hy
    exact (hC.differentiableOn (by simp) y hy).differentiableAt (isOpen_ball.mem_nhds hy)
  constructor
  · intro x hx
    have hbase : (q.symm x).ofLp.1 ∈ ball C.center C.radius := by
      obtain ⟨z,hz,rfl⟩ := hx
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hz.1
    have hs := hasFDerivAt_shear C.graphFunction (q.symm x) (hdiff _ hbase)
    have h := e.toContinuousLinearMap.hasFDerivAt.comp x
      (C.frame.toAffineIsometry.toContinuousAffineMap.hasFDerivAt.comp x
        (hs.comp x q.symm.toContinuousLinearMap.hasFDerivAt))
    exact h.differentiableAt
  · intro x hx
    have hbase : (C.frame.symm (e.symm x)).ofLp.1 ∈ ball C.center C.radius := by
      obtain ⟨u,⟨v,⟨w,hw,rfl⟩,rfl⟩,rfl⟩ := hx.2
      simpa only [LinearIsometryEquiv.symm_apply_apply, AffineIsometryEquiv.symm_apply_apply,
        shear, WithLp.ofLp_toLp] using hw.1
    have hs := hasFDerivAt_unshear C.graphFunction (C.frame.symm (e.symm x)) (hdiff _ hbase)
    have h := q.toContinuousLinearMap.hasFDerivAt.comp x
      (hs.comp x (C.frame.symm.toAffineIsometry.toContinuousAffineMap.hasFDerivAt.comp x
        e.symm.toContinuousLinearMap.hasFDerivAt))
    exact h.differentiableAt
end P201.BoundaryH2

namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

set_option maxHeartbeats 1000000 in
lemma flattenH10Supported {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] P201.Space (m+1)) (Ω : P201.Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (K : Compacts (P201.Space (m+1))) (hK : (K : Set (P201.Space (m+1))) ⊆ fullPhysicalChartOpen e C) :
    ∃ Cflat : ℝ, 0 < Cflat ∧
      ∀ u : P201.H10 ℝ Ω,
      (∀ᵐ x ∂P201.domainMeasure Ω, x ∉ K → P201.hZeroUnderlying Ω u x = 0) →
      ∃ w : P201.H10 ℝ (P102.Trace.halfSpace m),
        P102.Trace.FlatZeroTraceExpected.HasFlatZeroExtension
          (P201.hToW ℝ (P102.Trace.halfSpace m) 1 w.val) ∧
        (P201.hZeroUnderlying (P102.Trace.halfSpace m) w : P201.Space (m+1) → ℝ)
          =ᵐ[P201.domainMeasure (flatChartOpen (flatCoordinates m) C.center C.radius C.height)]
          (fun x => P201.hZeroUnderlying Ω u ((physicalChartMap e (flatCoordinates m) Ω C).toFun x)) ∧
        (∀ᵐ x ∂P201.domainMeasure (P102.Trace.halfSpace m),
          x ∉ fullChartPullbackCompact e (flatCoordinates m) C K hK →
            P201.hZeroUnderlying (P102.Trace.halfSpace m) w x = 0) ∧
        ‖w‖ ≤ Cflat * ‖u‖ := by
  letI : SeminormedAddCommGroup (sobolevSupportedSubmodule (k := 1) ℝ Ω 2 K) :=
    (sobolevSupportedSubmodule (k := 1) ℝ Ω 2 K).seminormedAddCommGroup
  letI : NormedSpace ℝ (sobolevSupportedSubmodule (k := 1) ℝ Ω 2 K) :=
    (sobolevSupportedSubmodule (k := 1) ℝ Ω 2 K).normedSpace
  let Q : sobolevSupportedSubmodule (k := 1) ℝ Ω 2 K →L[ℝ] P102.Trace.HalfSobolev m ℝ 2 :=
    flattenHalfSupportedCLM (𝕜 := ℝ) e Ω C 2 K hK
  let A := (P201.hToW ℝ (P102.Trace.halfSpace m) 1).symm.toContinuousLinearMap
  let B := (P201.hToW ℝ Ω 1).toContinuousLinearMap
  let Cflat := 1 + ‖A‖ * ‖Q‖ * ‖B‖
  have hCflat : 0 < Cflat := by dsimp only [Cflat]; positivity
  refine ⟨Cflat,hCflat,?_⟩
  intro u hsupport
  let z : sobolevSupportedSubmodule (k := 1) ℝ Ω 2 K :=
    ⟨(P201.hToW ℝ Ω 1) u.val, hsupport⟩
  have hu0 : (P201.hToW ℝ Ω 1) u.val ∈ sobolevZeroSubmodule ℝ Ω 1 2 := by
    exact Eq.mp (congrArg (fun S : Submodule ℝ (P201.H ℝ Ω 1) => u.val ∈ S)
      (P201.hZeroClosureBridge ℝ Ω)) u.property
  have hu : P102.Trace.Ordinary.HasZeroExtension z.val :=
    hasZeroExtension_of_mem_sobolevZero z.val hu0
  let w0 : P201.H ℝ (P102.Trace.halfSpace m) 1 := A (Q z)
  have hw0 : (P201.hToW ℝ (P102.Trace.halfSpace m) 1) w0 = Q z :=
    ContinuousLinearEquiv.apply_symm_apply _ _
  have hwzero : w0 ∈ P201Specs.hZeroSubmodule ℝ (P102.Trace.halfSpace m) := by
    rw [P201.hZeroClosureBridge ℝ (P102.Trace.halfSpace m)]
    change (P201.hToW ℝ (P102.Trace.halfSpace m) 1) w0 ∈
      sobolevZeroSubmodule ℝ (P102.Trace.halfSpace m) 1 2
    rw [hw0]
    exact flattenHalfSupportedCLM_mem_sobolevZero_of_zeroExtension e Ω C 2 K hK (by norm_num) z hu
  let w : P201.H10 ℝ (P102.Trace.halfSpace m) := ⟨w0,hwzero⟩
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · change P102.Trace.FlatZeroTraceExpected.HasFlatZeroExtension
      ((P201.hToW ℝ (P102.Trace.halfSpace m) 1) w0)
    rw [hw0]
    exact flattenHalfSupportedCLM_hasFlatZeroExtension e Ω C 2 K hK z hu
  · change (sobolevUnderlying ((P201.hToW ℝ (P102.Trace.halfSpace m) 1) w0) : _ → ℝ)
      =ᵐ[_] _
    rw [hw0]
    have hhalf := flattenHalfSupportedCLM_underlying_ae e Ω C 2 K hK z
    have hle : (flatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (P201.Space (m+1))) ⊆
        P102.Trace.halfSpace m := by
      rw [← flatPositiveOpen_flatCoordinates m]
      exact flatChartOpen_le_flatPositive _ _ _ _
    have hhalf' := ae_restrict_of_ae_restrict_of_subset hle hhalf
    filter_upwards [hhalf', flattenCylinderSupportedCLM_underlying_ae e (flatCoordinates m) Ω C 2 K z,
      ae_restrict_mem (flatChartOpen (flatCoordinates m) C.center C.radius C.height).isOpen.measurableSet]
      with x hx hy hxF
    exact hx.trans ((indicator_of_mem hxF _).trans hy)
  · change ∀ᵐ x ∂P201.domainMeasure (P102.Trace.halfSpace m),
      x ∉ fullChartPullbackCompact e (flatCoordinates m) C K hK →
        sobolevUnderlying ((P201.hToW ℝ (P102.Trace.halfSpace m) 1) w0) x = 0
    rw [hw0]
    exact flattenHalfSupportedCLM_zero_off_compact e Ω C 2 K hK z
  · have hQz := Q.le_opNorm z
    have hnorm : ‖w‖ ≤ ‖A‖ * ‖Q‖ * ‖B‖ * ‖u‖ := by
      calc
        ‖w‖ ≤ ‖A‖ * ‖Q z‖ := A.le_opNorm _
        _ ≤ ‖A‖ * (‖Q‖ * ‖z‖) := mul_le_mul_of_nonneg_left hQz (norm_nonneg A)
        _ ≤ ‖A‖ * (‖Q‖ * (‖B‖ * ‖u‖)) := by
          gcongr
          exact B.le_opNorm u.val
        _ = _ := by ring
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
end P201.BoundaryH2

namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary
lemma physicalGraphCoefficientBounds {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (Hder : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius))
    (M LA : ℝ≥0) (theta : ℝ) (htheta : 0 < theta) :
    ∃ (M' L' : ℝ≥0) (theta' : ℝ), 0 < theta' ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      P201Specs.InteriorH2.CoefficientBounds (physicalChartOpen e Ω C) A M LA theta →
      P201Specs.InteriorH2.CoefficientBounds (flatChartOpen q C.center C.radius C.height)
        (fun y => conjugateCoefficient
          (fderiv ℝ (physicalChartMap e q Ω C).invFun ((physicalChartMap e q Ω C).toFun y))
          (A ((physicalChartMap e q Ω C).toFun y))) M' L' theta' ∧
      (P201Specs.BoundaryH2.SymmetricOn (physicalChartOpen e Ω C) A →
        P201Specs.BoundaryH2.SymmetricOn (flatChartOpen q C.center C.radius C.height)
          (fun y => conjugateCoefficient
            (fderiv ℝ (physicalChartMap e q Ω C).invFun ((physicalChartMap e q Ω C).toFun y))
            (A ((physicalChartMap e q Ω C).toFun y)))) := by
  let F := physicalChartMap e q Ω C
  let s := shearConstant C.constant
  obtain ⟨HG, hDG⟩ := physicalChartMap_inverse_fderiv_lipschitz e q Ω C Hder hC hL
  have hdiff := physicalChartMap_differentiable e q Ω C hC
  let theta' := theta / (max 1 (s : ℝ)) ^ 2
  have ht : 0 < theta' := div_pos htheta (sq_pos_of_pos
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  refine ⟨s ^ 2 * M, 2 * s * M * (HG * s) + s ^ 2 * (LA * s), theta', ht, ?_⟩
  intro A hA
  constructor
  · exact coordinateCoefficientBounds _ _ s s HG F
      (fun x hx => (hdiff.1 x hx).differentiableWithinAt)
      (fun x hx => (hdiff.2 x hx).differentiableWithinAt) hDG A M LA theta htheta hA
  · intro hsym y hy ξ ζ
    exact conjugateSymmetry _ _ (hsym _ (F.mapsTo hy)) ξ ζ

end P201.BoundaryH2

namespace P201.BoundaryH2
open Filter
open scoped Topology

private lemma adjoint_apply_coordinate {n : ℕ} (T : Space n →L[ℝ] Space n)
    (z : Space n) (j : Fin n) :
    ContinuousLinearMap.adjoint T z j =
      ∑ i : Fin n, T (coordinate n j) i * z i := by
  calc
    _ = inner ℝ (ContinuousLinearMap.adjoint T z) (coordinate n j) := by
      exact (EuclideanSpace.inner_basisFun_real (Fin n) _ j).symm
    _ = inner ℝ z (T (coordinate n j)) := T.adjoint_inner_left _ _
    _ = _ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

private lemma hGradient_chain {n : ℕ} (U V : Domain n) (L M : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V L M) (u : H ℝ U 1) (w : H ℝ V 1)
    (hd : ∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun x => ∑ i : Fin n, fderiv ℝ F.toFun x (coordinate n j) i *
        hFirstDerivative u i (F.toFun x))) :
    (hGradient w : Space n → Space n) =ᵐ[domainMeasure V]
      (fun x => ContinuousLinearMap.adjoint (fderiv ℝ F.toFun x) (hGradient u (F.toFun x))) := by
  filter_upwards [InteriorH2.hGradient_ae w,
    F.ae_comp (InteriorH2.hGradient_ae u), ae_all_iff.mpr hd] with x hx hxu hdx
  rw [hx]
  ext j
  rw [adjoint_apply_coordinate, hxu]
  exact hdx j

private lemma inverse_derivative_ae {n : ℕ} (U V : Domain n) (L M : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V L M) :
    ∀ᵐ y ∂domainMeasure V,
      (fderiv ℝ F.toFun y).comp (fderiv ℝ F.invFun (F.toFun y)) =
        ContinuousLinearMap.id ℝ (Space n) := by
  have hdF : ∀ᵐ y ∂domainMeasure V, DifferentiableAt ℝ F.toFun y := by
    filter_upwards [F.lipschitz.ae_differentiableWithinAt V.isOpen.measurableSet,
      ae_restrict_mem V.isOpen.measurableSet] with y hy hyV
    exact hy.differentiableAt (V.isOpen.mem_nhds hyV)
  have hdG : ∀ᵐ x ∂domainMeasure U, DifferentiableAt ℝ F.invFun x := by
    filter_upwards [F.inv_lipschitz.ae_differentiableWithinAt U.isOpen.measurableSet,
      ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
    exact hx.differentiableAt (U.isOpen.mem_nhds hxU)
  filter_upwards [hdF, F.ae_comp hdG, ae_restrict_mem V.isOpen.measurableSet]
    with y hyF hyG hyV
  have hid : (fun x => F.toFun (F.invFun x)) =ᶠ[𝓝 (F.toFun y)] id := by
    filter_upwards [U.isOpen.mem_nhds (F.mapsTo hyV)] with x hx
    exact F.right_inv x hx
  have hF : HasFDerivAt F.toFun (fderiv ℝ F.toFun y) (F.invFun (F.toFun y)) := by
    rw [F.left_inv y hyV]
    exact hyF.hasFDerivAt
  have hcomp := hF.comp (F.toFun y) hyG.hasFDerivAt
  have hc : HasFDerivAt id
      ((fderiv ℝ F.toFun y).comp (fderiv ℝ F.invFun (F.toFun y))) (F.toFun y) :=
    hcomp.congr_of_eventuallyEq hid.symm
  exact hc.unique (hasFDerivAt_id (F.toFun y))

/-- The actual weak divergence equation under a volume-preserving bi-Lipschitz
coordinate map. All Sobolev pullbacks and admissible physical tests are derived;
no transformed PDE or regularity certificate is assumed. -/
theorem weakEquation_coordinatePullback {n : ℕ} (hn : 0 < n)
    (U V : Domain n) (LF LG : ℝ≥0) (F : P102.U4.BiLipschitzChart U V LF LG)
    (hvol : Measure.map F.toFun (domainMeasure V) = domainMeasure U)
    (A : Space n → Space n →L[ℝ] Space n)
    (hA : ContinuousOn A U) {M : ℝ} (hM : ∀ x ∈ U, ‖A x‖ ≤ M)
    (u : H ℝ U 1) (f : Lp ℝ U 2)
    (heq : P201Specs.InteriorH2.WeakEquation U A u f) :
    ∃ (w : H ℝ V 1) (g : Lp ℝ V 2),
      (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun y => hUnderlying U 1 u (F.toFun y)) ∧
      (g : Space n → ℝ) =ᵐ[domainMeasure V] (fun y => f (F.toFun y)) ∧
      P201Specs.InteriorH2.WeakEquation V
        (fun y => conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y))) w g ∧
      ‖w‖ ≤ ((Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) *
        P102.U4.pullbackSobolevBound n 2 LF LG) * ‖u‖ ∧
      ‖g‖ ≤ P102.U4.pullbackLpBound n 2 LG * ‖f‖ := by
  obtain ⟨T, hT, hTd, hTnorm⟩ := coordinateH1Pullback hn U V LF LG F
  obtain ⟨S, hS, hSd, _⟩ := coordinateH1Pullback hn V U LG LF F.symm
  let w := T u
  let g : Lp ℝ V 2 := F.lpPullback ℝ 2 f
  have hg : (g : Space n → ℝ) =ᵐ[domainMeasure V] (fun y => f (F.toFun y)) :=
    F.lpPullback_ae ℝ 2 f
  have hwgrad := hGradient_chain U V LF LG F u w (hTd u)
  refine ⟨w, g, hT u, hg, ?_, ?_, ?_⟩
  rotate_left
  · exact (T.le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _))
  · exact F.lpPullbackLinear_norm_le ℝ 2 f
  intro φ
  obtain ⟨φH, hφH⟩ := InteriorTesting.exists_test_class V φ
  let z : H ℝ U 1 := S φH.val
  have hz : (hUnderlying U 1 z : Space n → ℝ) =ᵐ[domainMeasure U]
      (fun x => φ (F.invFun x)) := by
    have hφ : (hUnderlying V 1 φH.val : Space n → ℝ) =ᵐ[domainMeasure V] φ := by
      have hφUnderlying : hUnderlying V 1 φH.val = P102.U4.testToDomainLp V 2 φ := hφH
      rw [hφUnderlying]
      exact P102.U4.testToDomainLp_ae V 2 φ
    exact (hS φH.val).trans (F.symm.ae_comp hφ)
  have hzgrad : (hGradient z : Space n → Space n) =ᵐ[domainMeasure U]
      (fun x => ContinuousLinearMap.adjoint (fderiv ℝ F.invFun x) (gradient φ (F.invFun x))) := by
    have hφgrad := InteriorTesting.smooth_gradient_ae V φH.val φ hφH
    exact (hGradient_chain V U LG LF F.symm φH.val z (hSd φH.val)).trans
      (by
        filter_upwards [F.symm.ae_comp hφgrad] with x hx
        exact congrArg (ContinuousLinearMap.adjoint (fderiv ℝ F.invFun x)) hx)
  let K : Compacts (Space n) := ⟨F.toFun '' tsupport φ,
    φ.hasCompactSupport.image_of_continuousOn (F.lipschitz.continuousOn.mono φ.tsupport_subset)⟩
  have hKU : (K : Set (Space n)) ⊆ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact F.mapsTo (φ.tsupport_subset hy)
  have hzK : P102.U4.HasCompactSupportIn (hUnderlying U 1 z) := by
    refine ⟨K, hKU, ?_⟩
    filter_upwards [hz, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU hxK
    rw [hx]
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    apply hxK
    exact ⟨F.invFun x, hxs, F.right_inv x hxU⟩
  let z0 : H10 ℝ U := ⟨z, InteriorH2.compactSupport_mem_hZero U z hzK⟩
  have henergy := InteriorH2.weakEquation_energy hn U A u f hA hM heq z0
  have hfluxmeas : AEStronglyMeasurable (fun x =>
      inner ℝ (A x (hGradient u x)) (hGradient z x)) (domainMeasure U) :=
    (InteriorH2.flux_memLp U A (hGradient u) hA hM).aestronglyMeasurable.inner
      (Lp.memLp (hGradient z)).aestronglyMeasurable
  have hsourcemeas : AEStronglyMeasurable (fun x =>
      f x * hUnderlying U 1 z x) (domainMeasure U) :=
    (Lp.memLp f).aestronglyMeasurable.mul (Lp.memLp (hUnderlying U 1 z)).aestronglyMeasurable
  have hchangeL : (∫ x in U, inner ℝ (A x (hGradient u x)) (hGradient z x)) =
      ∫ y in V, inner ℝ (A (F.toFun y) (hGradient u (F.toFun y))) (hGradient z (F.toFun y)) := by
    have hm : AEStronglyMeasurable (fun x =>
        inner ℝ (A x (hGradient u x)) (hGradient z x))
        (Measure.map F.toFun (domainMeasure V)) := by rwa [hvol]
    have h := integral_map F.aemeasurable hm
    rw [hvol] at h
    exact h
  have hchangeR : (∫ x in U, f x * hUnderlying U 1 z x) =
      ∫ y in V, f (F.toFun y) * hUnderlying U 1 z (F.toFun y) := by
    have hm : AEStronglyMeasurable (fun x => f x * hUnderlying U 1 z x)
        (Measure.map F.toFun (domainMeasure V)) := by rwa [hvol]
    have h := integral_map F.aemeasurable hm
    rw [hvol] at h
    exact h
  have hpair : (∫ y in V,
      inner ℝ (conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y)) (hGradient w y))
        (gradient φ y)) =
      ∫ y in V, inner ℝ (A (F.toFun y) (hGradient u (F.toFun y))) (hGradient z (F.toFun y)) := by
    apply integral_congr_ae
    filter_upwards [hwgrad, inverse_derivative_ae U V LF LG F,
      F.ae_comp hzgrad, ae_restrict_mem V.isOpen.measurableSet] with y hyw hyinv hyz hyV
    rw [conjugatePairing]
    have hrecovery : ContinuousLinearMap.adjoint (fderiv ℝ F.invFun (F.toFun y)) (hGradient w y) =
        hGradient u (F.toFun y) := by
      rw [hyw]
      change ((ContinuousLinearMap.adjoint (fderiv ℝ F.invFun (F.toFun y))).comp
        (ContinuousLinearMap.adjoint (fderiv ℝ F.toFun y))) (hGradient u (F.toFun y)) = _
      rw [← ContinuousLinearMap.adjoint_comp, hyinv, ContinuousLinearMap.adjoint_id,
        ContinuousLinearMap.id_apply]
    rw [hrecovery, hyz, F.left_inv y hyV]
  have hsource : (∫ y in V, g y * φ y) =
      ∫ y in V, f (F.toFun y) * hUnderlying U 1 z (F.toFun y) := by
    apply integral_congr_ae
    filter_upwards [hg, F.ae_comp hz, ae_restrict_mem V.isOpen.measurableSet] with y hyg hyz hyV
    rw [hyg, hyz, F.left_inv y hyV]
  exact hpair.trans (hchangeL.symm.trans (henergy.trans (hchangeR.trans hsource.symm)))

private lemma linearIsometry_volume_image {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    (e : E ≃ₗᵢ[ℝ] G) (S : Set E) : volume (e '' S) = volume S := by
  have h := e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding (e '' S)
  simpa only [Set.preimage_image_eq _ e.injective] using h.symm

private lemma affineIsometry_measurePreserving {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ᵃⁱ[ℝ] E) : MeasurePreserving e volume volume := by
  have h := (measurePreserving_add_right volume (e 0)).comp e.linearIsometryEquiv.measurePreserving
  convert h using 1
  funext x
  simpa only [vadd_eq_add, add_zero, Function.comp_apply] using e.map_vadd 0 x

private lemma affineIsometry_volume_image {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ᵃⁱ[ℝ] E) (S : Set E) : volume (e '' S) = volume S := by
  have h := (affineIsometry_measurePreserving e).measure_preimage_emb
    e.toHomeomorph.measurableEmbedding (e '' S)
  simpa only [Set.preimage_image_eq _ e.injective] using h.symm

/-- The graph-flattening inverse has Jacobian of absolute value one, expressed
as equality of actual volumes on all subsets of the physical chart. -/
theorem physicalChartMap_inverse_volume {m : ℕ}
    (e q : P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Domain (m + 1))
    (C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient m)))
    (S : Set (Space (m + 1))) (hS : S ⊆ P102.Trace.Ordinary.physicalChartOpen e Ω C) :
    volume ((P102.Trace.Ordinary.physicalChartMap e q Ω C).invFun '' S) = volume S := by
  let T : Set (P102.U4.GraphPieces.Ambient m) := C.frame.symm '' (e.symm '' S)
  have hT : T ⊆ P102.Sobolev.Geometry.strip (Metric.ball C.center C.radius) := by
    rintro _ ⟨y, ⟨x, hxS, rfl⟩, rfl⟩
    obtain ⟨u, ⟨v, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩ := (hS hxS).2
    simpa only [LinearIsometryEquiv.symm_apply_apply,
      AffineIsometryEquiv.symm_apply_apply, P102.Sobolev.Geometry.strip, mem_ofPred_eq,
      P102.Sobolev.Geometry.shear, WithLp.ofLp_toLp] using hw.1
  calc
    _ = volume (q '' (P102.Sobolev.Geometry.unshear C.graphFunction '' T)) := by
      simp only [T, Set.image_image]
      rfl
    _ = volume (P102.Sobolev.Geometry.unshear C.graphFunction '' T) :=
      linearIsometry_volume_image q _
    _ = volume T := (P102.Sobolev.Geometry.shear_volume m _ _ _ C.graph_lipschitz T hT).2
    _ = volume (e.symm '' S) := affineIsometry_volume_image C.frame.symm _
    _ = volume S := linearIsometry_volume_image e.symm _

/-- The determinant-one graph map transports exactly the restricted Euclidean
volume of the flat chart to that of the physical chart. -/
theorem physicalChartMap_map_volume {m : ℕ}
    (e q : P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Domain (m + 1))
    (C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient m))) :
    Measure.map (P102.Trace.Ordinary.physicalChartMap e q Ω C).toFun
      (domainMeasure (P102.Trace.Ordinary.flatChartOpen q C.center C.radius C.height)) =
        domainMeasure (P102.Trace.Ordinary.physicalChartOpen e Ω C) := by
  let F := P102.Trace.Ordinary.physicalChartMap e q Ω C
  apply Measure.ext
  intro E hE
  change (Measure.map F.toFun (volume.restrict
    (P102.Trace.Ordinary.flatChartOpen q C.center C.radius C.height : Set _))) E =
      (volume.restrict (P102.Trace.Ordinary.physicalChartOpen e Ω C : Set _)) E
  rw [Measure.map_apply_of_aemeasurable F.aemeasurable hE,
    Measure.restrict_apply' (P102.Trace.Ordinary.flatChartOpen q C.center C.radius C.height).isOpen.measurableSet,
    Measure.restrict_apply hE]
  rw [inter_comm (F.toFun ⁻¹' E), F.preimage_eq_inverse_image]
  rw [physicalChartMap_inverse_volume e q Ω C _ inter_subset_left]
  rw [inter_comm]

/-- The manuscript's actual graph chart transforms the weak equation, source,
and H¹ function with quantitative norm bounds. No extra regularity of the
ambient graph representative outside its base ball is needed. -/
theorem physicalGraphWeakEquation {m : ℕ}
    (e q : P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Domain (m + 1))
    (C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient m)))
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (hA : ContinuousOn A (P102.Trace.Ordinary.physicalChartOpen e Ω C))
    {M : ℝ} (hM : ∀ x ∈ P102.Trace.Ordinary.physicalChartOpen e Ω C, ‖A x‖ ≤ M)
    (u : H ℝ (P102.Trace.Ordinary.physicalChartOpen e Ω C) 1)
    (f : Lp ℝ (P102.Trace.Ordinary.physicalChartOpen e Ω C) 2)
    (heq : P201Specs.InteriorH2.WeakEquation
      (P102.Trace.Ordinary.physicalChartOpen e Ω C) A u f) :
    let F := P102.Trace.Ordinary.physicalChartMap e q Ω C
    let U := P102.Trace.Ordinary.physicalChartOpen e Ω C
    let V := P102.Trace.Ordinary.flatChartOpen q C.center C.radius C.height
    ∃ (w : H ℝ V 1) (g : Lp ℝ V 2),
      (hUnderlying V 1 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure V]
        (fun y => hUnderlying U 1 u (F.toFun y)) ∧
      (g : Space (m + 1) → ℝ) =ᵐ[domainMeasure V] (fun y => f (F.toFun y)) ∧
      P201Specs.InteriorH2.WeakEquation V
        (fun y => conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y))) w g ∧
      ‖w‖ ≤ ((Fintype.card (P102.U4.SobolevIndex (m + 1) 1) : ℝ) *
        P102.U4.pullbackSobolevBound (m + 1) 2 (P102.Sobolev.Geometry.shearConstant C.constant)
          (P102.Sobolev.Geometry.shearConstant C.constant)) * ‖u‖ ∧
      ‖g‖ ≤ P102.U4.pullbackLpBound (m + 1) 2
        (P102.Sobolev.Geometry.shearConstant C.constant) * ‖f‖ := by
  exact weakEquation_coordinatePullback (by omega) _ _ _ _ _
    (physicalChartMap_map_volume e q Ω C) A hA hM u f heq

end P201.BoundaryH2

namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

lemma selectBoundaryChartNeighborhood {m : ℕ} (Ω : P201.Domain (m+1))
    (hΩ : P201.HasC11Boundary Ω) (p : P201.Space (m+1))
    (hp : p ∈ frontier (Ω : Set (P201.Space (m+1)))) :
    ∃ (C : BoundaryChart (geometricOpen (P201.graphFrame m) Ω : Set (Ambient m)))
      (Hder : ℝ≥0) (R r : ℝ) (χ : P201.Test ℝ (⊤ : P201.Domain (m+1))),
      (P201.graphFrame m) (C.frame (graph C.graphFunction C.center)) = p ∧
      ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius) ∧
      LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius) ∧
      0 < r ∧ r < R ∧
      ball p R ⊆ fullPhysicalChartOpen (P201.graphFrame m) C ∧
      P201Specs.BoundaryH2.neighborhood Ω p R ≤ physicalChartOpen (P201.graphFrame m) Ω C ∧
      tsupport χ ⊆ ball p R ∧
      (∀ x ∈ ball p r, χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) := by
  let e := P201.graphFrame m
  have hpG : e.symm p ∈ frontier (geometricOpen e Ω : Set (Ambient m)) := by
    change e.symm p ∈ frontier (e ⁻¹' (Ω : Set (P201.Space (m+1))))
    have hpf : e.symm p ∈ e.toHomeomorph ⁻¹' frontier (Ω : Set (P201.Space (m+1))) := by
      change e (e.symm p) ∈ frontier (Ω : Set (P201.Space (m+1)))
      simpa using hp
    rw [e.toHomeomorph.preimage_frontier] at hpf
    exact hpf
  obtain ⟨C,hcenter,hC,Hder,hLip⟩ := hΩ (e.symm p) hpG
  have hphysical : e (C.frame (graph C.graphFunction C.center)) = p := by
    simpa using congrArg e hcenter
  have hpfull : p ∈ fullPhysicalChartOpen e C := by
    rw [← hphysical]
    refine ⟨C.frame (graph C.graphFunction C.center), ?_, rfl⟩
    refine ⟨graph C.graphFunction C.center, ?_, rfl⟩
    refine ⟨WithLp.toLp 2 (C.center, (0:ℝ)), ?_, ?_⟩
    · exact ⟨by simpa using C.radius_pos, by simpa using (neg_lt_zero.mpr C.height_pos), C.height_pos⟩
    · simp [shear, graph]
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp (fullPhysicalChartOpen e C).isOpen p hpfull
  let r := R/4
  let b : ContDiffBump p :=
    { rIn := r
      rOut := R/2
      rIn_pos := by dsimp only [r]; positivity
      rIn_lt_rOut := by dsimp only [r]; linarith }
  let χ : P201.Test ℝ (⊤ : P201.Domain (m+1)) :=
    ⟨b,b.contDiff,b.hasCompactSupport,subset_univ _⟩
  refine ⟨C,Hder,R,r,χ,hphysical,hC,hLip,by dsimp only [r]; positivity,
    by dsimp only [r]; linarith,hball,?_,?_,?_,?_⟩
  · intro x hx
    exact ⟨hx.1, hball hx.2⟩
  · change tsupport b ⊆ ball p R
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by dsimp only [b]; linarith)
  · intro x hx
    exact b.one_of_mem_closedBall (ball_subset_closedBall hx)
  · intro x
    exact ⟨b.nonneg,b.le_one⟩
end P201.BoundaryH2

namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

lemma selectNestedFlatCutoff {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] P201.Space (m+1)) (Ω : P201.Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p : P201.Space (m+1))
    (hcenter : e (C.frame (graph C.graphFunction C.center)) = p)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hchart : ball p ρ ⊆ fullPhysicalChartOpen e C) :
    let y0 := flatCoordinates m (WithLp.toLp 2 (C.center,(0:ℝ)))
    ∃ (a s : ℝ) (η : P201.Test ℝ (⊤ : P201.Domain (m+1))),
      0 < a ∧ 0 < s ∧ s < ρ ∧
      ball y0 (2*a) ⊆ (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (P201.Space (m+1))) ∩
        (fullChartMap e (flatCoordinates m) C).toFun ⁻¹' ball p ρ ∧
      tsupport η ⊆ ball y0 (2*a) ∧
      tsupport η ⊆ closedBall y0 (3*a/2) ∧
      (∀ y ∈ ball y0 a, η y = 1) ∧
      (∀ y, 0 ≤ η y ∧ η y ≤ 1) ∧
      (∀ x ∈ P201Specs.BoundaryH2.neighborhood Ω p s,
        (physicalChartMap e (flatCoordinates m) Ω C).invFun x ∈
          ball y0 a ∩ (P102.Trace.halfSpace m : Set (P201.Space (m+1)))) := by
  dsimp only
  let q := flatCoordinates m
  let y0 := q (WithLp.toLp 2 (C.center,(0:ℝ)))
  let F := fullChartMap e q C
  have hy0 : y0 ∈ fullFlatChartOpen q C.center C.radius C.height := by
    refine ⟨WithLp.toLp 2 (C.center,(0:ℝ)),?_,rfl⟩
    exact ⟨by simpa using C.radius_pos, by simpa using (neg_lt_zero.mpr C.height_pos), C.height_pos⟩
  have hp : p ∈ fullPhysicalChartOpen e C := hchart (mem_ball_self hρ)
  have hFy0 : F.toFun y0 = p := (physicalChartMap_boundary e q Ω C C.center).trans hcenter
  have hFp : F.invFun p = y0 := by
    rw [← hcenter]
    exact physicalChartMap_inverse_boundary e q Ω C C.center
  have hfc : ContinuousAt F.toFun y0 :=
    F.lipschitz.continuousOn.continuousAt ((fullFlatChartOpen q C.center C.radius C.height).isOpen.mem_nhds hy0)
  have hNflat : (fullFlatChartOpen q C.center C.radius C.height : Set (P201.Space (m+1))) ∩
      F.toFun ⁻¹' ball p ρ ∈ 𝓝 y0 := by
    apply Filter.inter_mem ((fullFlatChartOpen q C.center C.radius C.height).isOpen.mem_nhds hy0)
    exact hfc.preimage_mem_nhds (by rw [hFy0]; exact Metric.ball_mem_nhds _ hρ)
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp hNflat
  let a := d/4
  have ha : 0 < a := by dsimp only [a]; positivity
  have hgc : ContinuousAt F.invFun p :=
    F.inv_lipschitz.continuousOn.continuousAt ((fullPhysicalChartOpen e C).isOpen.mem_nhds hp)
  have hNphys : F.invFun ⁻¹' ball y0 a ∈ 𝓝 p :=
    hgc.preimage_mem_nhds (by rw [hFp]; exact Metric.ball_mem_nhds _ ha)
  obtain ⟨t,ht,htsub⟩ := Metric.mem_nhds_iff.mp hNphys
  let s := min t ρ/2
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsρ : s < ρ := by
    dsimp only [s]
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) (half_lt_self hρ)
  have hst : s ≤ t := by
    dsimp only [s]
    exact (half_le_self (le_of_lt (lt_min ht hρ))).trans (min_le_left _ _)
  let b : ContDiffBump y0 :=
    { rIn := a
      rOut := 3*a/2
      rIn_pos := ha
      rIn_lt_rOut := by linarith }
  let η : P201.Test ℝ (⊤ : P201.Domain (m+1)) :=
    ⟨b,b.contDiff,b.hasCompactSupport,subset_univ _⟩
  refine ⟨a,s,η,ha,hs,hsρ,?_,?_,?_,?_,?_,?_⟩
  · apply (ball_subset_ball (show 2*a ≤ d by dsimp only [a]; linarith)).trans hdsub
  · change tsupport b ⊆ ball y0 (2*a)
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by dsimp only [b]; linarith)
  · change tsupport b ⊆ closedBall y0 (3*a/2)
    rw [b.tsupport_eq]
  · intro y hy
    exact b.one_of_mem_closedBall (ball_subset_closedBall hy)
  · intro y
    exact ⟨b.nonneg,b.le_one⟩
  · intro x hx
    have hxρ : x ∈ ball p ρ := ball_subset_ball hsρ.le hx.2
    have hxC : x ∈ physicalChartOpen e Ω C := ⟨hx.1,hchart hxρ⟩
    refine ⟨htsub (ball_subset_ball hst hx.2), ?_⟩
    rw [← flatPositiveOpen_flatCoordinates m]
    exact flatChartOpen_le_flatPositive q C.center C.radius C.height
      ((physicalChartMap e q Ω C).inv_mapsTo hxC)
end P201.BoundaryH2

namespace P201.BoundaryH2
open InteriorH2 P201Specs.InteriorH2
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem boundaryWeightedFluxIntegral {n : ℕ} (W V : Domain n) (hWV : W ≤ V)
    (η : Space n → ℝ) (geta : Space n → Space n)
    (A : Space n → Space n →L[ℝ] Space n)
    (g F : MeasureTheory.Lp (Space n) 2 (domainMeasure V))
    (hF : (F : Space n → Space n) =ᵐ[domainMeasure V] (fun x => A x (g x)))
    (z : H ℝ (⊤ : Domain n) 1) (q : Space n → ℝ) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (hgz : (hGradient z : Space n → Space n) =ᵐ[domainMeasure W]
      (fun x => η x ^ 2 • (h⁻¹ • (g (x + h • coordinate n k) - g x)) +
        (2 * η x * q x) • geta x))
    (hzoff : ∀ᵐ x ∂volume, x ∉ W → hGradient z x = 0) :
    (∫ x, inner ℝ
      (h⁻¹ • (((V : Set (Space n)).indicator (F : Space n → Space n))
          (x + h • coordinate n k) -
        ((V : Set (Space n)).indicator (F : Space n → Space n)) x)) (hGradient z x)) =
      ∫ x in W, inner ℝ
        (A (x + h • coordinate n k) (η x • (h⁻¹ • (g (x + h • coordinate n k) - g x))) +
          η x • ((h⁻¹ • (A (x + h • coordinate n k) - A x)) (g x)))
        (η x • (h⁻¹ • (g (x + h • coordinate n k) - g x)) +
          (2 * q x) • geta x) := by
  let a := h • coordinate n k
  have hI : ((V : Set (Space n)).indicator (F : Space n → Space n))
      =ᵐ[domainMeasure V] (fun x => A x (g x)) := by
    filter_upwards [hF, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
    rw [indicator_of_mem hxV]
    exact hx
  have hI0 := (ae_restrict_iff' W.isOpen.measurableSet).mp
    (ae_restrict_of_ae_restrict_of_subset hWV hI)
  have hIt := (ae_restrict_iff' W.isOpen.measurableSet).mp
    (InteriorH2.ae_eq_translate_local hI a (by
      rintro _ ⟨x, hx, rfl⟩
      exact ha x hx))
  have hgz' := (ae_restrict_iff' W.isOpen.measurableSet).mp hgz
  rw [← integral_indicator W.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards [hgz', hzoff, hI0, hIt] with x hx hz h0 ht
  by_cases hxW : x ∈ W
  · rw [indicator_of_mem hxW, hx hxW, h0 hxW, ht hxW]
    exact InteriorH2.weighted_flux_pairing (A x) (A (x+a)) (g x) (g (x+a))
      (geta x) (η x) (q x) h
  · rw [hz hxW, inner_zero_right, indicator_of_notMem hxW]

/-- Vector form of the actual chart-local tangential energy identity. -/
theorem localBoundary_discrete_energy_identity_vector {m : ℕ}
    (W V : Domain (m + 1))
    (hWV : (W : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (F : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure V))
    (f : Lp ℝ V 2)
    (heq : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x)
    (z : H ℝ (⊤ : Domain (m + 1)) 1) (K : Compacts (Space (m + 1)))
    (hKW : (K : Set (Space (m + 1))) ⊆ W)
    (hK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 z x = 0)
    (hzbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) (hh : h ≠ 0)
    (ha : ∀ x ∈ K, x + h • coordinate (m + 1) k ∈ W) :
    (∫ x, inner ℝ
      (h⁻¹ • (((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1)))
          (x + h • coordinate (m + 1) k) -
        ((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1))) x))
      (hGradient z x)) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
  let a := h • coordinate (m + 1) k
  let E (j : Fin (m + 1)) := P102.U4.lpZeroExtension V 2 (InteriorH2.fluxCoordinate F j)
  have hE (j : Fin (m + 1)) : MemLp (E j : Space (m + 1) → ℝ) 2 volume := by
    simpa only [E, Opens.coe_top, Measure.restrict_univ] using (Lp.memLp (E j))
  have hq (j : Fin (m + 1)) : MemLp (differenceQuotient (E j) k h) 2 volume := by
    have ht := (hE j).comp_measurePreserving (measurePreserving_add_right volume a)
    convert (ht.sub (hE j)).const_smul h⁻¹ using 1 <;> rfl
  have hd (j : Fin (m + 1)) : MemLp (hFirstDerivative z j : Space (m + 1) → ℝ) 2 volume := by
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using (Lp.memLp (hFirstDerivative z j))
  have hi (j : Fin (m + 1)) : Integrable
      (fun x => differenceQuotient (E j) k h x * hFirstDerivative z j x) volume :=
    (hq j).integrable_mul (hd j)
  have hcoord (j : Fin (m + 1)) := InteriorH2.fluxCoordinate_zeroExtension_ae V F j
  have hcoordT (j : Fin (m + 1)) :=
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (hcoord j)
  have hg : (hGradient z : Space (m + 1) → Space (m + 1)) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun j => hFirstDerivative z j x)) := by
    have hg0 : (hGradient z : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure (⊤ : Domain (m + 1))]
        (fun x => WithLp.toLp 2 (fun j => hFirstDerivative z j x)) := MemLp.coeFn_toLp _
    simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
      Measure.restrict_univ] using hg0
  have he : (fun x => inner ℝ
      (h⁻¹ • (((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1))) (x + a) -
        ((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1))) x))
      (hGradient z x)) =ᵐ[volume]
        (fun x => ∑ j : Fin (m + 1),
          differenceQuotient (E j) k h x * hFirstDerivative z j x) := by
    filter_upwards [hg, ae_all_iff.mpr hcoord, ae_all_iff.mpr hcoordT]
      with x hx hxF hxFT
    rw [hx]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
    congr 1
    change h⁻¹ * ((((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1))) (x+a)) j -
        (((V : Set (Space (m + 1))).indicator (F : Space (m + 1) → Space (m + 1))) x) j) =
      h⁻¹ * (E j (x+a) - E j x)
    rw [← hxF j, ← hxFT j]
  calc
    _ = ∫ x, ∑ j : Fin (m + 1),
        differenceQuotient (E j) k h x * hFirstDerivative z j x := integral_congr_ae he
    _ = ∑ j : Fin (m + 1), ∫ x,
        differenceQuotient (E j) k h x * hFirstDerivative z j x :=
      integral_finsetSum _ (fun j _ => hi j)
    _ = _ := localBoundary_discrete_energy_identity W V hWV F f heq z K hKW hK hzbelow k hk h hh ha




theorem boundaryGradientQuotient_step_bound {m : ℕ}
    (S W V O : Domain (m + 1)) [IsFiniteMeasure (domainMeasure S)]
    (hSW : S ≤ W) (hWV : W ≤ V)
    (hOV : (O : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (η : Test ℝ (⊤ : Domain (m + 1)))
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηO : tsupport η ⊆ O)
    (hηS : tsupport η ∩ (P102.Trace.halfSpace m : Set (Space (m + 1))) ⊆ S)
    (G M L Cz : ℝ≥0) (theta : ℝ) (ht : 0 < theta)
    (hG : ∀ x, ‖gradient η x‖ ≤ G)
    (A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1))
    (hA : CoefficientBounds V A M L theta)
    (v : H ℝ V 1) (f : Lp ℝ V 2) (heq : WeakEquation V A v f)
    (Z : H ℝ (⊤ : Domain (m + 1)) 1)
    (hZgrad : (hGradient Z : Space (m + 1) → Space (m + 1))
      =ᵐ[domainMeasure W] hGradient v)
    (hZzero : ∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
      hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0)
    (hZn : ‖Z‖ ≤ Cz * ‖v‖)
    (k : Fin (m + 1)) (hk : k ≠ Fin.last m) (h : ℝ) (hh : h ≠ 0)
    (hdint : Integrable (hFirstDerivative Z k : Space (m + 1) → ℝ) volume)
    (haS : ∀ x ∈ S, x + h • coordinate (m + 1) k ∈ W)
    (haO : ∀ x ∈ tsupport η, x + h • coordinate (m + 1) k ∈ O) :
    ∃ p : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure S),
      ((p : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S] fun x =>
        η x • (h⁻¹ • (hGradient v (x + h • coordinate (m + 1) k) - hGradient v x))) ∧
      ‖p‖ ≤ (1 + 2 * (1 + L + 2 * M * G + 2 * L * G + 2 * G) / theta) *
        ((1 + Cz) * ‖v‖ + ‖f‖) := by
  have hSV : S ≤ V := hSW.trans hWV
  have haSV : ∀ x ∈ S, x + h • coordinate (m + 1) k ∈ V :=
    fun x hx => hWV (haS x hx)
  let a := h • coordinate (m + 1) k
  have hcoord : coordinate (m + 1) k (Fin.last m) = 0 := by
    simp [coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply, Ne.symm hk]
  have hheight (x : Space (m + 1)) : (x + a) (Fin.last m) = x (Fin.last m) := by
    change x (Fin.last m) + h * coordinate (m + 1) k (Fin.last m) = _
    rw [hcoord, mul_zero, add_zero]
  have hHshift (x : Space (m + 1)) :
      x + a ∈ P102.Trace.halfSpace m ↔ x ∈ P102.Trace.halfSpace m := by
    change 0 < (x + a) (Fin.last m) ↔ 0 < x (Fin.last m)
    rw [hheight]
  have hZzeroT := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae hZzero
  obtain ⟨qH, hq, hqd⟩ := h1Quotient S ⊤ le_top k h (fun _ _ => mem_univ _) Z
  obtain ⟨hmq, _hqb⟩ := wholeSpace_quotient_bound Z k h hh hdint
  have hqn : ‖hUnderlying S 1 qH‖ ≤ ‖Z‖ := by
    calc
      _ = (eLpNorm (differenceQuotient (hUnderlying ⊤ 1 Z) k h) 2 (domainMeasure S)).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae hq]
      _ ≤ (eLpNorm (differenceQuotient (hUnderlying ⊤ 1 Z) k h) 2 volume).toReal :=
        ENNReal.toReal_mono hmq.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)
      _ ≤ ‖hFirstDerivative Z k‖ := wholeSpace_quotient_bound_toReal Z k h hh hdint
      _ ≤ ‖Z‖ := firstDerivative_norm_le ⊤ Z k
  have hgradS : (hGradient Z : Space (m + 1) → Space (m + 1))
      =ᵐ[domainMeasure S] hGradient v := ae_restrict_of_ae_restrict_of_subset hSW hZgrad
  have hgradT : (fun x => hGradient Z (x+a)) =ᵐ[domainMeasure S]
      (fun x => hGradient v (x+a)) := ae_eq_translate_local hZgrad a (by
        rintro _ ⟨x, hx, rfl⟩
        exact haS x hx)
  have hdqZ : (hGradient qH : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
      (fun x => h⁻¹ • (hGradient Z (x+a) - hGradient Z x)) := by
    have hto : (hGradient qH : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
        (fun x => WithLp.toLp 2 (fun j => differenceQuotient (hFirstDerivative Z j) k h x)) := by
      filter_upwards [hGradient_ae qH, ae_all_iff.mpr hqd] with x hx hd
      rw [hx]
      apply PiLp.ext
      intro j
      exact hd j
    exact hto.trans (hGradient_quotient_ae S ⊤ le_top Z k h (fun _ _ => mem_univ _)).symm
  have hdq : (hGradient qH : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
      (fun x => h⁻¹ • (hGradient v (x+a) - hGradient v x)) := by
    filter_upwards [hdqZ, hgradS, hgradT] with x hx h0 hT
    rw [hx, h0, hT]
  let hg := (Lp.memLp (hGradient v)).mono_measure (Measure.restrict_mono hSV le_rfl)
  let g : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure S) := hg.toLp _
  have hga : (g : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S] hGradient v := hg.coeFn_toLp
  have hgn : ‖g‖ ≤ ‖v‖ + ‖Z‖ := by
    have hgn0 : ‖g‖ ≤ ‖v‖ := by
      calc
        _ = (eLpNorm (hGradient v) 2 (domainMeasure S)).toReal := Lp.norm_toLp _ _
        _ ≤ ‖hGradient v‖ := by
          rw [Lp.norm_def]
          exact ENNReal.toReal_mono (Lp.memLp (hGradient v)).eLpNorm_ne_top
            (eLpNorm_mono_measure _ (Measure.restrict_mono hSV le_rfl))
        _ ≤ ‖v‖ := hGradient_norm_le v
    linarith [norm_nonneg Z]
  have hqnY : ‖hUnderlying S 1 qH‖ ≤ ‖v‖ + ‖Z‖ := by linarith [norm_nonneg v]
  have hηa : AEStronglyMeasurable η (domainMeasure S) := η.contDiff.continuous.aestronglyMeasurable
  have hη1 : ∀ x, |η x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (hη x).1]
    exact (hη x).2
  have hcgeta : Continuous (gradient η) := by
    change Continuous (fun x => WithLp.toLp 2 (fun j : Fin (m + 1) => fderiv ℝ η x (coordinate (m + 1) j)))
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact (η.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨hB, hD, hBM, hDL, hell⟩ := translated_coefficient_data S V hSV A M L theta hA k h hh haSV
  obtain ⟨p, b, r, e, hp, hb, hr, he, hel, hbn, hrn, hen⟩ :=
    construct_energy_fields g (hGradient qH) (hUnderlying S 1 qH) η (gradient η)
      (fun x => A (x+a)) (fun x => h⁻¹ • (A (x+a) - A x))
      hηa hcgeta.aestronglyMeasurable hB hD M.coe_nonneg L.coe_nonneg G.coe_nonneg
      (Filter.Eventually.of_forall hη1) (Filter.Eventually.of_forall hG)
      hBM hDL hell hgn hqnY
  have hpv : (p : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
      (fun x => η x • (h⁻¹ • (hGradient v (x+a) - hGradient v x))) := by
    filter_upwards [hp, hdq] with x hx hdx
    rw [hx, hdx]
  have hrv : (r : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
      (fun x => η x • (h⁻¹ • (A (x+a) - A x)) (hGradient v x)) := by
    filter_upwards [hr, hga] with x hx hgx
    rw [hx, hgx]
  have hev : (e : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
      (fun x => (2 * differenceQuotient (hUnderlying ⊤ 1 Z) k h x) • gradient η x) := by
    filter_upwards [he, hq] with x hx hqx
    rw [hx, hqx]
  obtain ⟨z, hz0, hzd, hK⟩ := localizedQuotient ⊤ ⊤ le_top η k h
    (fun _ _ => mem_univ _) Z
  have hgzZ := hGradient_localizedQuotient_ae ⊤ ⊤ le_top η Z z k h
    (fun _ _ => mem_univ _) hzd
  have hgz : (hGradient z : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
      (fun x => η x ^ 2 • (h⁻¹ • (hGradient v (x+a) - hGradient v x)) +
        (2 * η x * differenceQuotient (hUnderlying ⊤ 1 Z) k h x) • gradient η x) := by
    filter_upwards [ae_restrict_of_ae hgzZ, hgradS, hgradT] with x hx h0 hT
    rw [hx, h0, hT]
  have hzbelow : ∀ᵐ x ∂volume, x (Fin.last m) < 0 → hUnderlying ⊤ 1 z x = 0 := by
    filter_upwards [hz0, hZzero, hZzeroT] with x hx h0 hT hxneg
    have hxH : x ∉ P102.Trace.halfSpace m := by
      change ¬0 < x (Fin.last m)
      linarith
    have hxTH : x+a ∉ P102.Trace.halfSpace m := by rw [hHshift]; exact hxH
    rw [hx]
    change η x ^ 2 * (h⁻¹ • (hUnderlying ⊤ 1 Z (x+a) - hUnderlying ⊤ 1 Z x)) = 0
    rw [(h0 hxH).1, (hT hxTH).1, sub_self, smul_zero, mul_zero]
  have hzoff : ∀ᵐ x ∂volume, x ∉ S → hGradient z x = 0 := by
    filter_upwards [hgzZ, hZzero, hZzeroT] with x hx h0 hT hxS
    by_cases hxH : x ∈ P102.Trace.halfSpace m
    · have hηx : η x = 0 := by
        by_contra hne
        exact hxS (hηS ⟨subset_tsupport _ hne, hxH⟩)
      rw [hx, hηx]
      simp
    · have hxTH : x+a ∉ P102.Trace.halfSpace m := by rw [hHshift]; exact hxH
      rw [hx, (h0 hxH).2, (hT hxTH).2]
      change η x ^ 2 • (h⁻¹ • (0 - 0)) +
        (2 * η x * (h⁻¹ • (hUnderlying ⊤ 1 Z (x+a) - hUnderlying ⊤ 1 Z x))) • gradient η x = 0
      rw [(h0 hxH).1, (hT hxTH).1]
      simp
  have hgfields : (hGradient z : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure S]
      (fun x => η x • (p + e) x) := by
    filter_upwards [hgz, hpv, hev, Lp.coeFn_add p e] with x hx hpx hex hpe
    rw [hx, hpe, Pi.add_apply, hpx, hex]
    simp only [smul_add, smul_smul, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hgradz := hGradient_ae z
  simp only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
    Measure.restrict_univ] at hgradz
  have hzDoff : ∀ᵐ x ∂volume, x ∉ S → hFirstDerivative z k x = 0 := by
    filter_upwards [hgradz, hzoff] with x hx hzS hxS
    exact congrArg (fun ξ : Space (m + 1) => ξ k) (hx.symm.trans (hzS hxS))
  have hsource := localized_source_bound S V z p e η hη1 hgfields k (-h)
    (neg_ne_zero.mpr hh) hzDoff f
  have hsource' : |∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x| ≤
      ‖f‖ * (‖p‖ + 2 * G * (‖v‖ + ‖Z‖)) :=
    hsource.trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg f))
  let hmF := flux_memLp V A (hGradient v) hA.2.1.continuousOn hA.1
  let F : MeasureTheory.Lp (Space (m + 1)) 2 (domainMeasure V) := hmF.toLp _
  have hF : (F : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure V]
      (fun x => A x (hGradient v x)) := hmF.coeFn_toLp
  have htest : ∀ φ : Test ℝ V,
      (∫ x in V, inner ℝ (F x) (gradient φ x)) = ∫ x in V, f x * φ x := by
    intro φ
    refine (integral_congr_ae ?_).trans (heq φ)
    filter_upwards [hF] with x hx
    rw [hx]
  let K : Compacts (Space (m + 1)) := ⟨tsupport η, η.hasCompactSupport⟩
  have hidentity := localBoundary_discrete_energy_identity_vector O V hOV F f htest z K
    hηO hK hzbelow k hk h hh haO
  have hweighted := boundaryWeightedFluxIntegral S V hSV η (gradient η) A
    (hGradient v) F hF z (differenceQuotient (hUnderlying ⊤ 1 Z) k h) k h haSV hgz hzoff
  have hinner : inner ℝ (b + r) (p + e) =
      -(∫ x in V, f x * differenceQuotient (hUnderlying ⊤ 1 z) k (-h) x) := by
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (hweighted.symm.trans hidentity)
    filter_upwards [Lp.coeFn_add b r, Lp.coeFn_add p e, hpv, hb, hrv, hev]
      with x hbr hpe hpx hbx hrx hex
    rw [hbr, hpe, Pi.add_apply, Pi.add_apply, hbx, hrx, hpx, hex]
  have henergy : |inner ℝ (b + r) (p + e)| ≤ ‖f‖ * (‖p‖ + 2 * G * (‖v‖ + ‖Z‖)) := by
    rw [hinner, abs_neg]
    exact hsource'
  refine ⟨p, hpv, ?_⟩
  have hpbound := energy_absorption_abstract p b r e M.coe_nonneg L.coe_nonneg G.coe_nonneg
    (add_nonneg (norm_nonneg v) (norm_nonneg Z)) (norm_nonneg f) ht hel hbn hrn hen henergy
  refine hpbound.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  nlinarith [hZn]


lemma boundaryScalarQuotient {n : ℕ} {U W V : Domain n}
    (hUW : U ≤ W) (hWV : W ≤ V) (η : Space n → ℝ)
    (hηU : ∀ x ∈ U, η x = 1) (v : H ℝ V 1) (k : Fin n) (h : ℝ)
    (ha : ∀ x ∈ W, x + h • coordinate n k ∈ V)
    (p : MeasureTheory.Lp (Space n) 2 (domainMeasure W))
    (hp : (p : Space n → Space n) =ᵐ[domainMeasure W]
      (fun x => η x • (h⁻¹ • (hGradient v (x + h • coordinate n k) - hGradient v x))))
    (j : Fin n) :
    MemLp (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ∧
      eLpNorm (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ≤ ‖p‖₊ := by
  have hg := hGradient_quotient_ae W V hWV v k h ha
  have hs : StronglyMeasurable (differenceQuotient (hFirstDerivative v j) k h) := by
    change StronglyMeasurable (fun x => h⁻¹ •
      (hFirstDerivative v j (x + h • coordinate n k) - hFirstDerivative v j x))
    exact (((Lp.stronglyMeasurable (hFirstDerivative v j)).comp_measurable
      (measurable_id.add_const (h • coordinate n k))).sub
      (Lp.stronglyMeasurable (hFirstDerivative v j))).const_smul h⁻¹
  have hb : ∀ᵐ x ∂domainMeasure U,
      ‖differenceQuotient (hFirstDerivative v j) k h x‖ ≤ ‖p x‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUW hp,
      ae_restrict_of_ae_restrict_of_subset hUW hg,
      ae_restrict_mem U.isOpen.measurableSet] with x hx hxg hxU
    rw [hηU x hxU, one_smul, hxg] at hx
    rw [hx]
    exact PiLp.norm_apply_le (WithLp.toLp 2 (fun i =>
      differenceQuotient (hFirstDerivative v i) k h x)) j
  have hbp : ∀ᵐ x ∂domainMeasure U,
      ‖differenceQuotient (hFirstDerivative v j) k h x‖ ≤ 1 * ‖p x‖ := by
    simpa only [one_mul] using hb
  refine ⟨((Lp.memLp p).mono_measure (Measure.restrict_mono hUW le_rfl)).of_le_mul
    hs.aestronglyMeasurable hbp, ?_⟩
  calc
    _ ≤ eLpNorm p 2 (domainMeasure U) := eLpNorm_mono_ae hs.aestronglyMeasurable hb
    _ ≤ eLpNorm p 2 (domainMeasure W) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono hUW le_rfl)
    _ = ‖p‖₊ := by rw [← Lp.enorm_def, enorm_eq_nnnorm]


/-- The local flat H² estimate with explicit geometric buffers and an actual
controlled H¹ zero extension. Neither tangential nor normal second derivatives
are assumed. The constant is fixed before coefficients, data and extension. -/
theorem flatBoundaryEstimate_with_extension {m : ℕ}
    (U S W V O : Domain (m + 1)) [IsFiniteMeasure (domainMeasure S)]
    (hUS : U ≤ S) (hSW : S ≤ W) (hWV : W ≤ V)
    (hOV : (O : Set (Space (m + 1))) ∩ P102.Trace.halfSpace m ⊆ V)
    (η : Test ℝ (⊤ : Domain (m + 1)))
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηO : tsupport η ⊆ O)
    (hηS : tsupport η ∩ (P102.Trace.halfSpace m : Set (Space (m + 1))) ⊆ S)
    (hηU : ∀ x ∈ U, η x = 1)
    (G M L Cz : ℝ≥0) (theta : ℝ) (ht : 0 < theta)
    (hG : ∀ x, ‖gradient η x‖ ≤ G)
    (δ : ℝ) (hδ : 0 < δ)
    (haS : ∀ (k : Fin (m + 1)), k ≠ Fin.last m →
      ∀ h : ℝ, |h| < δ → ∀ x ∈ S, x + h • coordinate (m + 1) k ∈ W)
    (haO : ∀ (k : Fin (m + 1)), k ≠ Fin.last m →
      ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport η, x + h • coordinate (m + 1) k ∈ O) :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      CoefficientBounds V A M L theta →
      ∀ (v : H ℝ V 1) (f : Lp ℝ V 2), WeakEquation V A v f →
      ∀ Z : H ℝ (⊤ : Domain (m + 1)) 1,
      ((hGradient Z : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure W] hGradient v) →
      (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
        hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) →
      ‖Z‖ ≤ Cz * ‖v‖ →
      (∀ k : Fin (m + 1), k ≠ Fin.last m →
        Integrable (hFirstDerivative Z k : Space (m + 1) → ℝ) volume) →
      ∃ w : H ℝ U 2,
        (hUnderlying U 2 w : Space (m + 1) → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
        ‖w‖ ≤ C * (‖v‖ + ‖f‖) := by
  let K : ℝ≥0 := ⟨1 + 2 * (1 + L + 2 * M * G + 2 * L * G + 2 * G) / theta, by positivity⟩
  let Q : ℝ≥0 := K * (1 + Cz)
  let d : ℝ := ((m + 1 : ℕ) : ℝ)
  let N : ℝ := Fintype.card (P102.U4.SobolevIndex (m + 1) 2)
  let C : ℝ := 1 + N * ((1 + d) + Q + theta⁻¹ *
    (1 + d ^ 2 * ((M : ℝ) * Q + (L : ℝ) * (1 + d)) + (L : ℝ) * (1 + d)))
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun A hA v f heq Z hZgrad hZzero hZn hdint => ?_⟩
  let B : ℝ≥0 := Q * (‖v‖₊ + ‖f‖₊)
  have hSV : S ≤ V := hSW.trans hWV
  have hUV : U ≤ V := hUS.trans hSV
  have hb (j k : Fin (m + 1)) (hk : k ≠ Fin.last m) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < |h| → |h| < ε →
        MemLp (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ∧
        eLpNorm (differenceQuotient (hFirstDerivative v j) k h) 2 (domainMeasure U) ≤ B := by
    refine ⟨δ, hδ, fun h hh hsmall => ?_⟩
    obtain ⟨p, hp, hpn⟩ := boundaryGradientQuotient_step_bound S W V O hSW hWV hOV η hη hηO hηS
      G M L Cz theta ht hG A hA v f heq Z hZgrad hZzero hZn k hk h
      (abs_pos.mp hh) (hdint k hk) (haS k hk h hsmall) (haO k hk h hsmall)
    obtain ⟨hm, hn⟩ := boundaryScalarQuotient hUS hSV η hηU v k h
      (fun x hx => hWV (haS k hk h hsmall x hx)) p hp j
    have hpnB : ‖p‖ ≤ (B : ℝ) := by
      calc
        ‖p‖ ≤ (K : ℝ) * ((1 + Cz) * ‖v‖ + ‖f‖) := hpn
        _ ≤ (K : ℝ) * ((1 + Cz) * (‖v‖ + ‖f‖)) := by
          gcongr
          nlinarith [norm_nonneg f, Cz.coe_nonneg]
        _ = (B : ℝ) := by simp only [B, Q, NNReal.coe_mul, NNReal.coe_add,
          NNReal.coe_one, coe_nnnorm]; ring
    refine ⟨hm, hn.trans ?_⟩
    exact_mod_cast hpnB
  obtain ⟨w, hw, hwn⟩ := h2FromTangentialQuotients U V hUV A M L theta ht hA v f heq B hb
  refine ⟨w, hw, hwn.trans ?_⟩
  have hB : (B : ℝ) = (Q : ℝ) * (‖v‖ + ‖f‖) := by
    simp only [B, NNReal.coe_mul, NNReal.coe_add, coe_nnnorm]
  change N * ((1 + d) * ‖v‖ + B + theta⁻¹ *
    (‖f‖ + d ^ 2 * ((M : ℝ) * B + (L : ℝ) * ((1 + d) * ‖v‖)) +
      (L : ℝ) * ((1 + d) * ‖v‖))) ≤ C * (‖v‖ + ‖f‖)
  rw [hB]
  calc
    _ ≤ N * ((1 + d) * (‖v‖ + ‖f‖) + (Q : ℝ) * (‖v‖ + ‖f‖) + theta⁻¹ *
        ((‖v‖ + ‖f‖) + d ^ 2 * ((M : ℝ) * ((Q : ℝ) * (‖v‖ + ‖f‖)) +
          (L : ℝ) * ((1 + d) * (‖v‖ + ‖f‖))) +
          (L : ℝ) * ((1 + d) * (‖v‖ + ‖f‖)))) := by
      gcongr <;> linarith [norm_nonneg v, norm_nonneg f]
    _ ≤ C * (‖v‖ + ‖f‖) := by
      dsimp only [C]
      nlinarith [norm_nonneg v, norm_nonneg f]

end P201.BoundaryH2

namespace P201.BoundaryH2
open Filter
open scoped Topology ContDiff

private lemma h1_lipschitz_multiplier_map {n : ℕ} (V : Domain n) (a : Space n → ℝ)
    (M L : ℝ≥0) (haL : LipschitzOnWith L a V) (haM : ∀ x ∈ V, |a x| ≤ M) :
    ∃ T : H ℝ V 1 →L[ℝ] H ℝ V 1,
      (∀ u, (hUnderlying V 1 (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => a x * hUnderlying V 1 u x)) ∧
      ‖T‖ ≤ (1 + (n : ℝ)) * ((M : ℝ) + L) := by
  classical
  choose v hv hvnorm using h1_lipschitz_multiplier V a M L haL haM
  have ham : AEStronglyMeasurable a (domainMeasure V) :=
    haL.continuousOn.aestronglyMeasurable V.isOpen.measurableSet
  have haB : ∀ᵐ x ∂domainMeasure V, ‖a x‖ ≤ (M : ℝ) := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact haM x hx
  let R : Lp ℝ V 2 →L[ℝ] Lp ℝ V 2 := P102.U4.realMultiplier V 2 a M ham haB
  have hR (u : H ℝ V 1) : hUnderlying V 1 (v u) = R (hUnderlying V 1 u) := by
    apply Lp.ext
    exact (hv u).trans (P102.U4.realMultiplier_ae V 2 a M ham haB (hUnderlying V 1 u)).symm
  let S : H ℝ V 1 →ₗ[ℝ] H ℝ V 1 :=
    { toFun := v
      map_add' := fun u w => by
        apply hilbertUnderlyingInjective V 1
        rw [map_add, hR, hR, hR, map_add, map_add]
      map_smul' := fun r u => by
        apply hilbertUnderlyingInjective V 1
        rw [map_smul, hR, hR, map_smul, map_smul]
        rfl }
  let T := S.mkContinuous ((1 + (n : ℝ)) * ((M : ℝ) + L)) hvnorm
  refine ⟨T, hv, LinearMap.mkContinuous_norm_le _ (by positivity) _⟩

/-- A bounded Lipschitz multiplier preserves the actual H¹₀ closure on every
open set. The proof first constructs a continuous H¹ multiplier and then uses
compact smooth test density; no boundary regularity is required. -/
theorem hZeroLipschitzMultiplier {n : ℕ} (V : Domain n) (a : Space n → ℝ)
    (M L : ℝ≥0) (haL : LipschitzOnWith L a V) (haM : ∀ x ∈ V, |a x| ≤ M) :
    ∃ T : H10 ℝ V →L[ℝ] H10 ℝ V,
      (∀ u, (hZeroUnderlying V (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => a x * hZeroUnderlying V u x)) ∧
      (∀ u j, (hFirstDerivative (T u).val j : Space n → ℝ) =ᵐ[domainMeasure V]
        (fun x => a x * hFirstDerivative u.val j x +
          fderiv ℝ a x (coordinate n j) * hZeroUnderlying V u x)) ∧
      ∀ u, ‖T u‖ ≤ ((1 + (n : ℝ)) * ((M : ℝ) + L)) * ‖u‖ := by
  obtain ⟨T, hT, hTn⟩ := h1_lipschitz_multiplier_map V a M L haL haM
  let D : Submodule ℝ (H ℝ V 1) :=
    (P102.U4.smoothSobolevSubmodule ℝ V 1 2).comap (hToW ℝ V 1).toLinearMap
  have hclosed : IsClosed (P201Specs.hZeroSubmodule ℝ V : Set (H ℝ V 1)) :=
    Submodule.isClosed_topologicalClosure D
  have htest : D ≤ (P201Specs.hZeroSubmodule ℝ V).comap T.toLinearMap := by
    intro v hv
    obtain ⟨φ, hφ⟩ := hv
    have hvφ : (hUnderlying V 1 v : Space n → ℝ) =ᵐ[domainMeasure V] φ := by
      have he : hUnderlying V 1 v = P102.U4.testToDomainLp V 2 φ := hφ.symm
      rw [he]
      exact P102.U4.testToDomainLp_ae V 2 φ
    apply InteriorH2.compactSupport_mem_hZero V (T v)
    refine ⟨⟨tsupport φ, φ.hasCompactSupport⟩, φ.tsupport_subset, ?_⟩
    filter_upwards [hT v, hvφ] with x hx hxv hxK
    rw [hx, hxv, image_eq_zero_of_notMem_tsupport hxK, mul_zero]
  have hpres : ∀ v ∈ P201Specs.hZeroSubmodule ℝ V, T v ∈ P201Specs.hZeroSubmodule ℝ V :=
    D.topologicalClosure_minimal htest (hclosed.preimage T.continuous)
  let T0 : H10 ℝ V →L[ℝ] H10 ℝ V := T.restrict hpres
  refine ⟨T0, fun u => hT u.val, ?_, ?_⟩
  · intro u j
    obtain ⟨w, d, hw, hd, hD, _, _⟩ := directionalLipschitzMultiplier V j a M L haL haM
      (hZeroUnderlying V u) (hFirstDerivative u.val j)
      (hilbertDerivativeDistribution V 1 u.val ⟨{j}, by simp⟩)
    have he : hUnderlying V 1 (T u.val) = w := Lp.ext ((hT u.val).trans hw.symm)
    have hder : hFirstDerivative (T u.val) j = d := by
      apply P102.U4.regularLp_injective V 2
      change regularDistribution V (hFirstDerivative (T u.val) j) = regularDistribution V d
      have hbase : distributionDerivative {j}
          (regularDistribution V (hUnderlying V 1 (T u.val))) =
            regularDistribution V (hFirstDerivative (T u.val) j) :=
        hilbertDerivativeDistribution V 1 (T u.val) ⟨{j}, by simp⟩
      rw [← hbase, he]
      exact hD
    change (hFirstDerivative (T u.val) j : Space n → ℝ) =ᵐ[domainMeasure V] _
    rw [hder]
    exact hd
  · intro u
    exact (T.le_opNorm u.val).trans
      (mul_le_mul_of_nonneg_right hTn (norm_nonneg _))

/-- An ambient smooth compact cutoff acts continuously on the canonical H¹₀
space, with actual representatives, product-rule derivatives and support. -/
theorem hZeroSmoothCutoff {n : ℕ} (V : Domain n) (χ : Space n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : H10 ℝ V →L[ℝ] H10 ℝ V,
      ∀ u,
        (hZeroUnderlying V (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hZeroUnderlying V u x) ∧
        (∀ j, (hFirstDerivative (T u).val j : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hFirstDerivative u.val j x +
            fderiv ℝ χ x (coordinate n j) * hZeroUnderlying V u x)) ∧
        (∀ᵐ x ∂domainMeasure V, x ∉ tsupport χ → hZeroUnderlying V (T u) x = 0) ∧
        ‖T u‖ ≤ C * ‖u‖ := by
  obtain ⟨c0, hc0⟩ := hc.exists_bound_of_continuous hχ.continuous
  obtain ⟨c1, hc1⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  let M : ℝ≥0 := ⟨max c0 0, le_max_right _ _⟩
  let L : ℝ≥0 := ⟨max c1 0, le_max_right _ _⟩
  have hM : ∀ x ∈ V, |χ x| ≤ (M : ℝ) := fun x _ => (hc0 x).trans (le_max_left _ _)
  have hL : LipschitzWith L χ := lipschitzWith_of_nnnorm_fderiv_le
    (hχ.differentiable (by simp)) (fun x => by
      exact_mod_cast ((hc1 x).trans (le_max_left c1 0) : ‖fderiv ℝ χ x‖ ≤ (L : ℝ)))
  obtain ⟨T, hT, hTd, hTn⟩ := hZeroLipschitzMultiplier V χ M L hL.lipschitzOnWith hM
  let C : ℝ := 1 + (1 + (n : ℝ)) * ((M : ℝ) + L)
  refine ⟨C, by dsimp only [C]; positivity, T, fun u => ⟨hT u, hTd u, ?_, ?_⟩⟩
  · filter_upwards [hT u] with x hx hxK
    rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul]
  · exact (hTn u).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))

/-- A cutoff product can be estimated using only the H¹ norm on an open
neighborhood of the cutoff support, even when that neighborhood meets ∂V.
Only scalar L² zero extensions are used in this comparison. -/
theorem h1CutoffLocalBound {n : ℕ} (V U : Domain n) (hUV : U ≤ V)
    (χ : Space n → ℝ) (hχ : Continuous χ) (M L : ℝ≥0)
    (hχM : ∀ x ∈ V, |χ x| ≤ M)
    (hχD : ∀ x ∈ V, ‖fderiv ℝ χ x‖ ≤ L)
    (hχU : tsupport χ ∩ (V : Set (Space n)) ⊆ U)
    (u w : H ℝ V 1) (v : H ℝ U 1)
    (hv : (hUnderlying U 1 v : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 u)
    (hvd : ∀ j, (hFirstDerivative v j : Space n → ℝ) =ᵐ[domainMeasure U] hFirstDerivative u j)
    (hw : (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun x => χ x * hUnderlying V 1 u x))
    (hwd : ∀ j, (hFirstDerivative w j : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun x => χ x * hFirstDerivative u j x +
        fderiv ℝ χ x (coordinate n j) * hUnderlying V 1 u x)) :
    ‖w‖ ≤ ((1 + (n : ℝ)) * ((M : ℝ) + L)) * ‖v‖ := by
  have hext (a : Lp ℝ U 2) : ∃ b : Lp ℝ V 2,
      (b : Space n → ℝ) =ᵐ[domainMeasure V] (U : Set (Space n)).indicator a ∧ ‖b‖ ≤ ‖a‖ := by
    let b := InteriorH2.restrictLp (show V ≤ (⊤ : Domain n) from le_top) (P102.U4.lpZeroExtension U 2 a)
    refine ⟨b, ?_, (InteriorH2.restrictLp_norm_le le_top _).trans_eq (P102.U4.lpZeroExtension_norm U 2 a)⟩
    exact (InteriorH2.restrictLp_ae le_top _).trans (ae_restrict_of_ae (P102.U4.lpZeroExtension_ae U 2 a))
  obtain ⟨v0, hv0, hv0n⟩ := hext (hUnderlying U 1 v)
  choose vd hvd0 hvdn using fun j => hext (hFirstDerivative v j)
  have hvOn : ∀ᵐ x ∂domainMeasure V, x ∈ U → hUnderlying U 1 v x = hUnderlying V 1 u x :=
    ae_restrict_of_ae ((ae_restrict_iff' U.isOpen.measurableSet).mp hv)
  have hvdOn (j : Fin n) : ∀ᵐ x ∂domainMeasure V,
      x ∈ U → hFirstDerivative v j x = hFirstDerivative u j x :=
    ae_restrict_of_ae ((ae_restrict_iff' U.isOpen.measurableSet).mp (hvd j))
  have hχm : AEStronglyMeasurable χ (domainMeasure V) := hχ.aestronglyMeasurable
  have hχB : ∀ᵐ x ∂domainMeasure V, |χ x| ≤ (M : ℝ) := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact hχM x hx
  let da (j : Fin n) (x : Space n) := fderiv ℝ χ x (coordinate n j)
  have hdam (j : Fin n) : AEStronglyMeasurable (da j) (domainMeasure V) :=
    ((ContinuousLinearMap.apply ℝ ℝ (coordinate n j)).continuous.measurable.comp
      (measurable_fderiv ℝ χ)).aestronglyMeasurable
  have hdaB (j : Fin n) : ∀ᵐ x ∂domainMeasure V, |da j x| ≤ (L : ℝ) := by
    filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    change ‖fderiv ℝ χ x (coordinate n j)‖ ≤ (L : ℝ)
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by
      rw [P102.U4.DifferenceQuotient.norm_coordinateVector, mul_one]
      exact hχD x hx)
  let am := InteriorH2.scalarMultiply_memLp v0 χ hχm hχB
  let a : Lp ℝ V 2 := am.toLp (fun x => χ x * v0 x)
  have hwa : hUnderlying V 1 w = a := by
    apply Lp.ext
    filter_upwards [hw, am.coeFn_toLp, hv0, hvOn,
      ae_restrict_mem V.isOpen.measurableSet] with x hx hax hvx hvUx hxV
    change hUnderlying V 1 w x = a x
    change a x = χ x * v0 x at hax
    rw [hx, hax]
    by_cases hxχ : x ∈ tsupport χ
    · have hxU := hχU ⟨hxχ, hxV⟩
      rw [hvx, indicator_of_mem hxU, hvUx hxU]
    · rw [image_eq_zero_of_notMem_tsupport hxχ, zero_mul, zero_mul]
  have hv0B : ‖v0‖ ≤ ‖v‖ := hv0n.trans (PiLp.norm_apply_le _ _)
  have hvdB (j : Fin n) : ‖vd j‖ ≤ ‖v‖ :=
    (hvdn j).trans (InteriorH2.firstDerivative_norm_le U v j)
  have hwB : ‖hUnderlying V 1 w‖ ≤ ((M : ℝ) + L) * ‖v‖ := by
    rw [hwa]
    calc
      _ ≤ (M : ℝ) * ‖v0‖ := InteriorH2.scalarMultiply_norm_le v0 χ hχm hχB
      _ ≤ (M : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_left hv0B M.coe_nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right L.coe_nonneg) (norm_nonneg _)
  have hwdB (j : Fin n) : ‖hFirstDerivative w j‖ ≤ ((M : ℝ) + L) * ‖v‖ := by
    let bm := InteriorH2.scalarMultiply_memLp (vd j) χ hχm hχB
    let cm := InteriorH2.scalarMultiply_memLp v0 (da j) (hdam j) (hdaB j)
    let b : Lp ℝ V 2 := bm.toLp (fun x => χ x * vd j x)
    let c : Lp ℝ V 2 := cm.toLp (fun x => da j x * v0 x)
    have he : hFirstDerivative w j = b + c := by
      apply Lp.ext
      filter_upwards [hwd j, Lp.coeFn_add b c, bm.coeFn_toLp, cm.coeFn_toLp,
        hv0, hvd0 j, hvOn, hvdOn j, ae_restrict_mem V.isOpen.measurableSet]
        with x hx hsum hbx hcx hvx hvdx hvUx hvdUx hxV
      change hFirstDerivative w j x = (b + c) x
      change b x = χ x * vd j x at hbx
      change c x = da j x * v0 x at hcx
      rw [hx, hsum, Pi.add_apply, hbx, hcx]
      by_cases hxχ : x ∈ tsupport χ
      · have hxU := hχU ⟨hxχ, hxV⟩
        rw [hvx, hvdx, indicator_of_mem hxU, indicator_of_mem hxU, hvUx hxU, hvdUx hxU]
      · dsimp only [da]
        rw [image_eq_zero_of_notMem_tsupport hxχ, fderiv_of_notMem_tsupport ℝ hxχ]
        simp
    rw [he]
    calc
      _ ≤ ‖b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (M : ℝ) * ‖vd j‖ + (L : ℝ) * ‖v0‖ := add_le_add
        (InteriorH2.scalarMultiply_norm_le (vd j) χ hχm hχB)
        (InteriorH2.scalarMultiply_norm_le v0 (da j) (hdam j) (hdaB j))
      _ ≤ (M : ℝ) * ‖v‖ + (L : ℝ) * ‖v‖ := add_le_add
        (mul_le_mul_of_nonneg_left (hvdB j) M.coe_nonneg)
        (mul_le_mul_of_nonneg_left hv0B L.coe_nonneg)
      _ = _ := by ring
  simpa only [mul_assoc] using h1_norm_from_bounds V w (((M : ℝ) + L) * ‖v‖) hwB hwdB

/-- The cutoff constant is local: it controls χu using any actual outer H¹
restriction containing the cutoff support inside V. This supports boundary
neighborhood estimates with small outer balls, rather than the global H¹ norm. -/
theorem hZeroSmoothCutoffLocal {n : ℕ} (V : Domain n) (χ : Space n → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : H10 ℝ V →L[ℝ] H10 ℝ V,
      (∀ u,
        (hZeroUnderlying V (T u) : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hZeroUnderlying V u x) ∧
        (∀ j, (hFirstDerivative (T u).val j : Space n → ℝ) =ᵐ[domainMeasure V]
          (fun x => χ x * hFirstDerivative u.val j x +
            fderiv ℝ χ x (coordinate n j) * hZeroUnderlying V u x)) ∧
        (∀ᵐ x ∂domainMeasure V, x ∉ tsupport χ → hZeroUnderlying V (T u) x = 0)) ∧
      ∀ (U : Domain n), U ≤ V → tsupport χ ∩ (V : Set (Space n)) ⊆ U →
        ∀ (u : H10 ℝ V) (v : H ℝ U 1),
        (hUnderlying U 1 v : Space n → ℝ) =ᵐ[domainMeasure U] hZeroUnderlying V u →
        (∀ j, (hFirstDerivative v j : Space n → ℝ) =ᵐ[domainMeasure U] hFirstDerivative u.val j) →
        ‖T u‖ ≤ C * ‖v‖ := by
  obtain ⟨c0, hc0⟩ := hc.exists_bound_of_continuous hχ.continuous
  obtain ⟨c1, hc1⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  let M : ℝ≥0 := ⟨max c0 0, le_max_right _ _⟩
  let L : ℝ≥0 := ⟨max c1 0, le_max_right _ _⟩
  have hM : ∀ x ∈ V, |χ x| ≤ (M : ℝ) := fun x _ => (hc0 x).trans (le_max_left _ _)
  have hD : ∀ x ∈ V, ‖fderiv ℝ χ x‖ ≤ (L : ℝ) := fun x _ => (hc1 x).trans (le_max_left _ _)
  have hL : LipschitzWith L χ := lipschitzWith_of_nnnorm_fderiv_le
    (hχ.differentiable (by simp)) (fun x => by
      exact_mod_cast ((hc1 x).trans (le_max_left c1 0) : ‖fderiv ℝ χ x‖ ≤ (L : ℝ)))
  obtain ⟨T, hT, hTd, _⟩ := hZeroLipschitzMultiplier V χ M L hL.lipschitzOnWith hM
  let C : ℝ := 1 + (1 + (n : ℝ)) * ((M : ℝ) + L)
  refine ⟨C, by dsimp only [C]; positivity, T, ?_, ?_⟩
  · intro u
    refine ⟨hT u, hTd u, ?_⟩
    filter_upwards [hT u] with x hx hxK
    rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul]
  · intro U hUV hχU u v hv hvd
    exact (h1CutoffLocalBound V U hUV χ hχ.continuous M L hM hD hχU
      u.val (T u).val v hv hvd (hT u) (hTd u)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))

end P201.BoundaryH2

namespace P201.BoundaryH2
set_option backward.isDefEq.respectTransparency false
theorem h10ZeroExtension {n : ℕ} (V : Domain n) (w : H10 ℝ V) :
    ∃ Z : H ℝ (⊤ : Domain n) 1,
      hUnderlying ⊤ 1 Z = P102.U4.lpZeroExtension V 2 (hZeroUnderlying V w) ∧
      (∀ j, hFirstDerivative Z j = P102.U4.lpZeroExtension V 2 (hFirstDerivative w.val j)) ∧
      ‖Z‖ = ‖w‖ := by
  have hw0 : (hToW ℝ V 1) w.val ∈ P102.U4.sobolevZeroSubmodule ℝ V 1 2 := by
    exact Eq.mp (congrArg (fun S : Submodule ℝ (H ℝ V 1) => w.val ∈ S)
      (hZeroClosureBridge ℝ V)) w.property
  let v0 : P102.U4.SobolevZero ℝ V 1 2 := ⟨hToW ℝ V 1 w.val, hw0⟩
  obtain ⟨E, hEu, hEd, _⟩ := P102.U4.zeroExtension_operator (𝕜 := ℝ) V 1 2 (by norm_num)
  let Z : H ℝ (⊤ : Domain n) 1 := (hToW ℝ ⊤ 1).symm (E v0)
  have hZW : (hToW ℝ ⊤ 1) Z = E v0 := ContinuousLinearEquiv.apply_symm_apply _ _
  refine ⟨Z, ?_, ?_, ?_⟩
  · change P102.U4.sobolevUnderlying ((hToW ℝ ⊤ 1) Z) = _
    rw [hZW]
    exact hEu v0
  · intro j
    change P102.U4.sobolevDerivative ((hToW ℝ ⊤ 1) Z) ⟨{j}, by simp⟩ = _
    rw [hZW]
    exact hEd v0 _
  · apply (sq_eq_sq₀ (norm_nonneg Z) (norm_nonneg w)).mp
    rw [fullHilbertNorm ⊤ 1 Z]
    change _ = ‖w.val‖ ^ 2
    rw [fullHilbertNorm V 1 w.val, hZW]
    apply Finset.sum_congr rfl
    intro α _
    rw [hEd, P102.U4.lpZeroExtension_norm]

/-- Exact gradient representative of the canonical zero extension. -/
theorem h10ZeroExtension_gradient {n : ℕ} (V : Domain n) (w : H10 ℝ V)
    (Z : H ℝ (⊤ : Domain n) 1)
    (hZd : ∀ j, hFirstDerivative Z j = P102.U4.lpZeroExtension V 2 (hFirstDerivative w.val j)) :
    (hGradient Z : Space n → Space n) =ᵐ[volume]
      (V : Set (Space n)).indicator (hGradient w.val) := by
  have hZg := InteriorH2.hGradient_ae Z
  simp only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
    Measure.restrict_univ] at hZg
  have hwg := (ae_restrict_iff' V.isOpen.measurableSet).mp (InteriorH2.hGradient_ae w.val)
  have hdz (j : Fin n) : (hFirstDerivative Z j : Space n → ℝ) =ᵐ[volume]
      (V : Set (Space n)).indicator (hFirstDerivative w.val j) := by
    rw [hZd j]
    exact P102.U4.lpZeroExtension_ae V 2 _
  filter_upwards [hZg, hwg, ae_all_iff.mpr hdz] with x hz hw hd
  rw [hz]
  by_cases hxV : x ∈ V
  · rw [indicator_of_mem hxV, hw hxV]
    apply PiLp.ext
    intro j
    exact (hd j).trans (indicator_of_mem hxV _)
  · rw [indicator_of_notMem hxV]
    apply PiLp.ext
    intro j
    exact (hd j).trans (indicator_of_notMem hxV _)

/-- Zero-extension support may meet the genuine boundary. Compact essential
support of the original class suffices for L¹ first derivatives of its extension. -/
theorem zeroExtension_derivative_integrable {n : ℕ} (V : Domain n) (w : H10 ℝ V)
    (K : Compacts (Space n))
    (hK : ∀ᵐ x ∂domainMeasure V, x ∉ K → hZeroUnderlying V w x = 0)
    (Z : H ℝ (⊤ : Domain n) 1)
    (hZu : hUnderlying ⊤ 1 Z = P102.U4.lpZeroExtension V 2 (hZeroUnderlying V w)) :
    ∀ j, Integrable (hFirstDerivative Z j : Space n → ℝ) volume := by
  have hZK : ∀ᵐ x ∂volume, x ∉ K → hUnderlying ⊤ 1 Z x = 0 := by
    rw [hZu]
    exact P102.Trace.Ordinary.lpZeroExtension_zero_off_compact (hZeroUnderlying V w) K hK
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_ball (0 : Space n)
  let B : Domain n := ⟨ball (0 : Space n) r, isOpen_ball⟩
  let : IsFiniteMeasure (domainMeasure B) := isFiniteMeasure_restrict.mpr
    (Metric.isBounded_ball.measure_lt_top.ne)
  intro j
  have hZD : ∀ᵐ x ∂volume, x ∉ K → hFirstDerivative Z j x = 0 := by
    have hK' : ∀ᵐ x ∂volume.restrict ((⊤ : Domain n) : Set (Space n)),
        x ∉ K → P102.U4.sobolevUnderlying ((hToW ℝ ⊤ 1) Z) x = 0 := by
      change ∀ᵐ x ∂volume.restrict ((⊤ : Domain n) : Set (Space n)),
        x ∉ K → hUnderlying ⊤ 1 Z x = 0
      simpa only [Opens.coe_top, Measure.restrict_univ] using hZK
    have hD := P102.U4.sobolevDerivative_zero_off_compact ⊤ 1 2
      ((hToW ℝ ⊤ 1) Z) K hK' ⟨{j}, by simp⟩
    simpa only [Opens.coe_top, Measure.restrict_univ] using hD
  apply InteriorH2.wholeSpace_integrable_of_zero_off B (hFirstDerivative Z j)
  filter_upwards [hZD] with x hx hxB
  exact hx (fun hxK => hxB (hr hxK))

/-- All concrete extension inputs needed by the local flat estimate. -/
theorem halfSpaceZeroExtension {m : ℕ} (w : H10 ℝ (P102.Trace.halfSpace m))
    (K : Compacts (Space (m + 1)))
    (hK : ∀ᵐ x ∂domainMeasure (P102.Trace.halfSpace m),
      x ∉ K → hZeroUnderlying (P102.Trace.halfSpace m) w x = 0) :
    ∃ Z : H ℝ (⊤ : Domain (m + 1)) 1,
      (hUnderlying ⊤ 1 Z : Space (m + 1) → ℝ)
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)] hZeroUnderlying (P102.Trace.halfSpace m) w ∧
      (hGradient Z : Space (m + 1) → Space (m + 1))
        =ᵐ[domainMeasure (P102.Trace.halfSpace m)] hGradient w.val ∧
      (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
        hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) ∧
      ‖Z‖ = ‖w‖ ∧
      (∀ j, Integrable (hFirstDerivative Z j : Space (m + 1) → ℝ) volume) := by
  let V := P102.Trace.halfSpace m
  obtain ⟨Z, hZu, hZd, hZn⟩ := h10ZeroExtension V w
  have hZg := h10ZeroExtension_gradient V w Z hZd
  have hZuAe : (hUnderlying ⊤ 1 Z : Space (m + 1) → ℝ) =ᵐ[volume]
      (V : Set (Space (m + 1))).indicator (hZeroUnderlying V w) := by
    rw [hZu]
    exact P102.U4.lpZeroExtension_ae V 2 _
  refine ⟨Z, ?_, ?_, ?_, hZn, zeroExtension_derivative_integrable V w K hK Z hZu⟩
  · filter_upwards [ae_restrict_of_ae hZuAe, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
    exact hx.trans (indicator_of_mem hxV _)
  · filter_upwards [ae_restrict_of_ae hZg, ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
    exact hx.trans (indicator_of_mem hxV _)
  · filter_upwards [hZuAe, hZg] with x hu hg hxV
    exact ⟨hu.trans (indicator_of_notMem hxV _), hg.trans (indicator_of_notMem hxV _)⟩

/-- Local a.e. equality of H¹ representatives identifies their actual weak
gradients, including on open neighborhoods that reach the boundary. -/
theorem h1Gradient_congr_on {n : ℕ} (U V W : Domain n)
    (hUV : U ≤ V) (hUW : U ≤ W) (v : H ℝ V 1) (w : H ℝ W 1)
    (hvw : (hUnderlying V 1 v : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying W 1 w) :
    (hGradient v : Space n → Space n) =ᵐ[domainMeasure U] hGradient w := by
  obtain ⟨vU, hvU, hvUd, _⟩ := h1Restriction V U hUV v
  obtain ⟨wU, hwU, hwUd, _⟩ := h1Restriction W U hUW w
  have heq : vU = wU := hilbertUnderlyingInjective U 1
    (Lp.ext (hvU.trans (hvw.trans hwU.symm)))
  have hd (j : Fin n) : (hFirstDerivative v j : Space n → ℝ) =ᵐ[domainMeasure U]
      hFirstDerivative w j := by
    rw [heq] at hvUd
    exact (hvUd j).symm.trans (hwUd j)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hUV (InteriorH2.hGradient_ae v),
    ae_restrict_of_ae_restrict_of_subset hUW (InteriorH2.hGradient_ae w),
    ae_all_iff.mpr hd] with x hv hw hx
  rw [hv, hw]
  apply PiLp.ext
  intro j
  exact hx j

end P201.BoundaryH2

namespace P201.BoundaryH2
lemma coordinateH1InverseBound {n : ℕ} (hn : 0 < n)
    (U V : Domain n) (LF LG : ℝ≥0) (F : P102.U4.BiLipschitzChart U V LF LG)
    (u : H ℝ U 1) (w : H ℝ V 1)
    (hw : (hUnderlying V 1 w : Space n → ℝ) =ᵐ[domainMeasure V]
      (fun y => hUnderlying U 1 u (F.toFun y))) :
    ‖u‖ ≤ ((Fintype.card (P102.U4.SobolevIndex n 1) : ℝ) *
      P102.U4.pullbackSobolevBound n 2 LG LF) * ‖w‖ := by
  obtain ⟨S, hS, _, hSn⟩ := coordinateH1Pullback hn V U LG LF F.symm
  have heq : S w = u := by
    apply hilbertUnderlyingInjective U 1
    apply Lp.ext
    filter_upwards [hS w, F.symm.ae_comp hw, ae_restrict_mem U.isOpen.measurableSet]
      with x hx hwx hxU
    rw [hx, hwx]
    change hUnderlying U 1 u (F.toFun (F.invFun x)) = _
    rw [F.right_inv x hxU]
  calc
    ‖u‖ = ‖S w‖ := congrArg norm heq.symm
    _ ≤ ‖S‖ * ‖w‖ := S.le_opNorm w
    _ ≤ _ := mul_le_mul_of_nonneg_right hSn (norm_nonneg _)

end P201.BoundaryH2

namespace P201.BoundaryH2

lemma h2OpenRestriction {n : ℕ} (V U : Domain n) (hUV : U ≤ V) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H ℝ V 2,
      ∃ w : H ℝ U 2,
        (hUnderlying U 2 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 2 u ∧
        ‖w‖ ≤ C * ‖u‖ := by
  let N := 1 + (n : ℝ)
  let K : ℝ := Fintype.card (P102.U4.SobolevIndex n 2)
  let C := 1 + 2*K*N
  have hN : 0 < N := by dsimp only [N]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u
  obtain ⟨v,d,hv,hd,hvn,hdn⟩ := h2_first_order_classes V u
  let g : Fin n → Fin n → Lp ℝ U 2 := fun j k =>
    InteriorH2.restrictLp hUV (hFirstDerivative (d j) k)
  have hg (j k : Fin n) : distributionDerivative {k}
      (regularDistribution U (hFirstDerivative v j)) = regularDistribution U (g j k) := by
    dsimp only [g]
    rw [InteriorH2.regular_restrictLp, ← hd j]
    exact P102.U4.DifferenceQuotient.weak_derivative_restrict hUV
      (P102.U4.domainLp_locallyIntegrable V 2 _)
      (P102.U4.domainLp_locallyIntegrable V 2 _)
      (hilbertDerivativeDistribution V 1 (d j) ⟨{k},by simp⟩)
  have hgn (j k : Fin n) : ‖g j k‖ ≤ N * ‖u‖ :=
    (InteriorH2.restrictLp_norm_le hUV _).trans
      ((InteriorH2.firstDerivative_norm_le V (d j) k).trans (hdn j))
  obtain ⟨w,hw,hwn⟩ := h2Restriction V U hUV v g (N*‖u‖) (by positivity) hg hgn
  refine ⟨w,?_,?_⟩
  · rw [hv] at hw
    exact hw
  · calc
      ‖w‖ ≤ K * (‖v‖ + N*‖u‖) := hwn
      _ ≤ K * (N*‖u‖ + N*‖u‖) := by gcongr
      _ ≤ C * ‖u‖ := by dsimp only [C]; nlinarith [norm_nonneg u]
end P201.BoundaryH2
namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

lemma physicalGraphH2RestrictionToOpen {m : ℕ}
    (e q : Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (Ω : Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m))) (Hder : ℝ≥0)
    (hC : ContDiffOn ℝ 1 C.graphFunction (ball C.center C.radius))
    (hL : LipschitzOnWith Hder (fderiv ℝ C.graphFunction) (ball C.center C.radius))
    (U : Domain (m+1)) (hU : U ≤ physicalChartOpen e Ω C)
    (V : Domain (m+1))
    (hpre : (physicalChartMap e q Ω C).preimageOpen U ≤ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ w : H ℝ V 2,
      ∃ u : H ℝ U 2,
        (hUnderlying U 2 u : Space (m+1) → ℝ) =ᵐ[domainMeasure U]
          (fun x => hUnderlying V 2 w ((physicalChartMap e q Ω C).invFun x)) ∧
        ‖u‖ ≤ K * ‖w‖ := by
  let F := physicalChartMap e q Ω C
  let F' := F.restrict U hU
  let G : BiLipschitzChart (F.preimageOpen U) U
      (shearConstant C.constant) (shearConstant C.constant) :=
    { toFun := F'.invFun
      invFun := F'.toFun
      mapsTo := F'.inv_mapsTo
      inv_mapsTo := F'.mapsTo
      left_inv := F'.right_inv
      right_inv := F'.left_inv
      lipschitz := F'.inv_lipschitz
      inv_lipschitz := F'.lipschitz }
  obtain ⟨HG,hG⟩ := physicalChartMap_inverse_fderiv_lipschitz e q Ω C Hder hC hL
  obtain ⟨Kpush,hKpush,hpush⟩ := coordinateH2Pullback (Nat.succ_pos m) _ _ _ _ HG G (hG.mono hU)
  obtain ⟨Kres,hKres,hres⟩ := h2OpenRestriction V (F.preimageOpen U) hpre
  refine ⟨Kpush*Kres,mul_pos hKpush hKres,?_⟩
  intro w
  obtain ⟨wr,hwr,hwrn⟩ := hres w
  obtain ⟨u,hu,hun⟩ := hpush wr
  refine ⟨u,hu.trans (G.ae_comp hwr),?_⟩
  calc
    ‖u‖ ≤ Kpush * ‖wr‖ := hun
    _ ≤ Kpush * (Kres * ‖w‖) := mul_le_mul_of_nonneg_left hwrn hKpush.le
    _ = _ := (mul_assoc _ _ _).symm
end P201.BoundaryH2

namespace P201.BoundaryH2
/-- A volume-preserving coordinate chart remains exactly volume preserving
on every open physical restriction and its actual coordinate preimage. -/
theorem coordinateVolume_restrict {n : ℕ} (U V : Domain n) (LF LG : ℝ≥0)
    (F : P102.U4.BiLipschitzChart U V LF LG)
    (hvol : Measure.map F.toFun (domainMeasure V) = domainMeasure U)
    (P : Domain n) (hPU : P ≤ U) :
    Measure.map (F.restrict P hPU).toFun (domainMeasure (F.preimageOpen P)) =
      domainMeasure P := by
  change Measure.map F.toFun (domainMeasure (F.preimageOpen P)) = domainMeasure P
  have hmeasure : domainMeasure (F.preimageOpen P) =
      (domainMeasure V).restrict (F.toFun ⁻¹' (P : Set (Space n))) := by
    change volume.restrict ((V : Set (Space n)) ∩ F.toFun ⁻¹' (P : Set (Space n))) =
      (volume.restrict (V : Set (Space n))).restrict (F.toFun ⁻¹' (P : Set (Space n)))
    rw [Measure.restrict_restrict' V.isOpen.measurableSet, inter_comm]
  rw [hmeasure, ← Measure.restrict_map_of_aemeasurable F.aemeasurable P.isOpen.measurableSet,
    hvol]
  exact Measure.restrict_restrict_of_subset hPU


end P201.BoundaryH2

namespace P201.BoundaryH2
set_option maxHeartbeats 1000000
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary
open Filter
open scoped Topology ContDiff

/-- Localize an original H¹₀ function in a physical boundary chart, flatten it,
and extend by zero across the flat face. The extension agrees with the original
pullback wherever χ=1, and its norm uses only the given outer H¹ restriction. -/
theorem localizedCoordinateZeroExtension {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1)) (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (K : Compacts (Space (m + 1))) (hK : (K : Set (Space (m + 1))) ⊆ fullPhysicalChartOpen e C)
    (χ : Space (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχK : tsupport χ ⊆ K)
    (O : Domain (m + 1)) (hOΩ : O ≤ Ω)
    (hχO : tsupport χ ∩ (Ω : Set (Space (m + 1))) ⊆ O)
    (W : Domain (m + 1))
    (hWF : W ≤ flatChartOpen (flatCoordinates m) C.center C.radius C.height)
    (hOne : ∀ y ∈ W, χ ((physicalChartMap e (flatCoordinates m) Ω C).toFun y) = 1) :
    ∃ Cext : ℝ, 0 < Cext ∧
      ∀ (u : H10 ℝ Ω) (v : H ℝ O 1),
      (hUnderlying O 1 v : Space (m + 1) → ℝ) =ᵐ[domainMeasure O] hZeroUnderlying Ω u →
      (∀ j, (hFirstDerivative v j : Space (m + 1) → ℝ) =ᵐ[domainMeasure O] hFirstDerivative u.val j) →
      ∃ Z : H ℝ (⊤ : Domain (m + 1)) 1,
        (hUnderlying ⊤ 1 Z : Space (m + 1) → ℝ) =ᵐ[domainMeasure W]
          (fun y => hZeroUnderlying Ω u ((physicalChartMap e (flatCoordinates m) Ω C).toFun y)) ∧
        (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
          hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) ∧
        (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
          ∀ j, hFirstDerivative Z j x = 0) ∧
        (∀ j, Integrable (hFirstDerivative Z j : Space (m + 1) → ℝ) volume) ∧
        (∀ᵐ x ∂volume, x ∉ fullChartPullbackCompact e (flatCoordinates m) C K hK →
          hUnderlying ⊤ 1 Z x = 0) ∧
        ‖Z‖ ≤ Cext * ‖v‖ := by
  obtain ⟨Cχ, hCχ, T, hT, hTloc⟩ := hZeroSmoothCutoffLocal Ω χ hχ hc
  obtain ⟨Cflat, hCflat, hflat⟩ := flattenH10Supported e Ω C K hK
  refine ⟨Cflat * Cχ, mul_pos hCflat hCχ, ?_⟩
  intro u v hv hvd
  have hcutK : ∀ᵐ x ∂domainMeasure Ω, x ∉ K → hZeroUnderlying Ω (T u) x = 0 := by
    filter_upwards [(hT u).2.2] with x hx hxK
    exact hx (fun hxχ => hxK (hχK hxχ))
  obtain ⟨w, _, hw, hwK, hwn⟩ := hflat (T u) hcutK
  let Kflat := fullChartPullbackCompact e (flatCoordinates m) C K hK
  obtain ⟨Z, hZu, _, hZoff, hZn, hZint⟩ := halfSpaceZeroExtension w Kflat hwK
  have hWH : W ≤ P102.Trace.halfSpace m := by
    intro x hx
    rw [← flatPositiveOpen_flatCoordinates m]
    exact flatChartOpen_le_flatPositive _ _ _ _ (hWF hx)
  have hphysΩ : physicalChartOpen e Ω C ≤ Ω := inter_subset_left
  have hcutF := (physicalChartMap e (flatCoordinates m) Ω C).ae_comp
    (ae_restrict_of_ae_restrict_of_subset hphysΩ (hT u).1)
  refine ⟨Z, ?_, hZoff, ?_, hZint, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hWH hZu,
      ae_restrict_of_ae_restrict_of_subset hWF hw,
      ae_restrict_of_ae_restrict_of_subset hWF hcutF,
      ae_restrict_mem W.isOpen.measurableSet] with y hyZ hyw hycut hyW
    rw [hyZ, hyw, hycut, hOne y hyW, one_mul]
  · have hg : (hGradient Z : Space (m + 1) → Space (m + 1)) =ᵐ[volume]
        (fun x => WithLp.toLp 2 (fun j => hFirstDerivative Z j x)) := by
      simpa only [domainMeasure, P201Specs.domainMeasure, Opens.coe_top,
        Measure.restrict_univ] using InteriorH2.hGradient_ae Z
    filter_upwards [hZoff, hg] with x hx hxg hxH
    intro j
    have he := congrArg (fun z : Space (m + 1) => z j) (hx hxH).2
    rw [hxg] at he
    exact he
  · have huOn := (ae_restrict_iff' (P102.Trace.halfSpace m).isOpen.measurableSet).mp hZu
    have hwOn := (ae_restrict_iff' (P102.Trace.halfSpace m).isOpen.measurableSet).mp hwK
    filter_upwards [hZoff, huOn, hwOn] with x hx hxu hxw hxK
    by_cases hxH : x ∈ P102.Trace.halfSpace m
    · rw [hxu hxH]
      exact hxw hxH hxK
    · exact (hx hxH).1
  · calc
      ‖Z‖ = ‖w‖ := hZn
      _ ≤ Cflat * ‖T u‖ := hwn
      _ ≤ Cflat * (Cχ * ‖v‖) := mul_le_mul_of_nonneg_left
        (hTloc O hOΩ hχO u v hv hvd) hCflat.le
      _ = (Cflat * Cχ) * ‖v‖ := (mul_assoc _ _ _).symm

end P201.BoundaryH2

namespace P201.BoundaryH2

lemma translate_ball_buffer {n : ℕ} (c x : Space n) (r R δ : ℝ)
    (hr : r + δ ≤ R) (hx : x ∈ ball c r) (k : Fin n) (h : ℝ) (hh : |h| < δ) :
    x + h • coordinate n k ∈ ball c R := by
  rw [mem_ball_iff_norm]
  have hn : ‖x + h • coordinate n k - c‖ ≤ ‖x-c‖ + |h| := by
    calc
      _ = ‖(x-c) + h • coordinate n k‖ := by congr 1; abel
      _ ≤ ‖x-c‖ + ‖h • coordinate n k‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul,Real.norm_eq_abs,P102.U4.DifferenceQuotient.norm_coordinateVector,mul_one]
  have hxn := mem_ball_iff_norm.mp hx
  linarith

lemma translate_closedBall_buffer {n : ℕ} (c x : Space n) (r R δ : ℝ)
    (hr : r + δ ≤ R) (hx : x ∈ closedBall c r) (k : Fin n) (h : ℝ) (hh : |h| < δ) :
    x + h • coordinate n k ∈ ball c R := by
  rw [mem_ball_iff_norm]
  have hn : ‖x + h • coordinate n k - c‖ ≤ ‖x-c‖ + |h| := by
    calc
      _ = ‖(x-c) + h • coordinate n k‖ := by congr 1; abel
      _ ≤ ‖x-c‖ + ‖h • coordinate n k‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul,Real.norm_eq_abs,P102.U4.DifferenceQuotient.norm_coordinateVector,mul_one]
  have hxn := mem_closedBall_iff_norm.mp hx
  linarith

lemma tangential_translate_halfSpace {m : ℕ} (x : Space (m+1))
    (hx : x ∈ P102.Trace.halfSpace m) (k : Fin (m+1)) (hk : k ≠ Fin.last m) (h : ℝ) :
    x + h • coordinate (m+1) k ∈ P102.Trace.halfSpace m := by
  have hc : coordinate (m+1) k (Fin.last m) = 0 := by
    simp [coordinate,P201Specs.coordinate,P102.U4.coordinateVector,
      EuclideanSpace.basisFun_apply,Ne.symm hk]
  change 0 < x (Fin.last m) + h * coordinate (m+1) k (Fin.last m)
  rw [hc,mul_zero,add_zero]
  exact hx

lemma flat_preimage_ball_subset {m : ℕ}
    (e : P102.U4.GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (Ω : Domain (m+1))
    (C : P102.Sobolev.Geometry.BoundaryChart
      (P102.Sobolev.Extension.geometricOpen e Ω : Set (P102.U4.GraphPieces.Ambient m)))
    (P : Domain (m+1))
    (hP : P ≤ P102.Trace.Ordinary.physicalChartOpen e Ω C)
    (y0 : Space (m+1)) (a : ℝ)
    (hN : ∀ x ∈ P, (P102.Trace.Ordinary.physicalChartMap e
      (P102.Trace.Ordinary.flatCoordinates m) Ω C).invFun x ∈
        ball y0 a ∩ (P102.Trace.halfSpace m : Set (Space (m+1)))) :
    (P102.Trace.Ordinary.physicalChartMap e (P102.Trace.Ordinary.flatCoordinates m) Ω C).preimageOpen P ≤
      (P102.Trace.halfSpace m ⊓ (⟨ball y0 a,isOpen_ball⟩ : Domain (m+1))) := by
  let F := P102.Trace.Ordinary.physicalChartMap e (P102.Trace.Ordinary.flatCoordinates m) Ω C
  intro y hy
  have hn := hN (F.toFun y) hy.2
  rw [F.left_inv y hy.1] at hn
  exact ⟨hn.2,hn.1⟩
end P201.BoundaryH2
namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary

lemma flat_ball_subset_preimage_neighborhood {m : ℕ}
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m+1)) (Ω : Domain (m+1))
    (C : BoundaryChart (geometricOpen e Ω : Set (Ambient m)))
    (p y0 : Space (m+1)) (ρ a : ℝ)
    (hball : ball y0 (2*a) ⊆
      (fullFlatChartOpen (flatCoordinates m) C.center C.radius C.height : Set (Space (m+1))) ∩
        (fullChartMap e (flatCoordinates m) C).toFun ⁻¹' ball p ρ) :
    (P102.Trace.halfSpace m ⊓ (⟨ball y0 (2*a),isOpen_ball⟩ : Domain (m+1))) ≤
      (physicalChartMap e (flatCoordinates m) Ω C).preimageOpen
        (P201Specs.BoundaryH2.neighborhood Ω p ρ) := by
  intro y hy
  have hf := hball hy.2
  have hyflat : y ∈ flatChartOpen (flatCoordinates m) C.center C.radius C.height := by
    apply flatPositive_inter_full_subset_flat (flatCoordinates m) C.center C.radius C.height
    exact ⟨(flatPositiveOpen_flatCoordinates m).symm ▸ hy.1,hf.1⟩
  exact ⟨hyflat, (physicalChartMap e (flatCoordinates m) Ω C).mapsTo hyflat |>.1, hf.2⟩

lemma flat_ball_buffers {m : ℕ} (y0 : Space (m+1)) (a : ℝ) (ha : 0 < a)
    (V : Domain (m+1))
    (hV : (P102.Trace.halfSpace m ⊓ (⟨ball y0 (2*a),isOpen_ball⟩ : Domain (m+1))) ≤ V)
    (η : Test ℝ (⊤ : Domain (m+1)))
    (hηsupp : tsupport η ⊆ closedBall y0 (3*a/2))
    (hηone : ∀ y ∈ ball y0 a, η y = 1) :
    let U : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 a,isOpen_ball⟩
    let S : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 (7*a/4),isOpen_ball⟩
    let W : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 (2*a),isOpen_ball⟩
    let O : Domain (m+1) := ⟨ball y0 (2*a),isOpen_ball⟩
    U ≤ S ∧ S ≤ W ∧ W ≤ V ∧
      (O : Set (Space (m+1))) ∩ P102.Trace.halfSpace m ⊆ V ∧
      tsupport η ⊆ O ∧ tsupport η ∩ (P102.Trace.halfSpace m : Set (Space (m+1))) ⊆ S ∧
      (∀ y ∈ U, η y = 1) ∧
      (∀ k : Fin (m+1), k ≠ Fin.last m → ∀ h : ℝ, |h| < a/4 →
        ∀ x ∈ S, x + h • coordinate (m+1) k ∈ W) ∧
      (∀ k : Fin (m+1), k ≠ Fin.last m → ∀ h : ℝ, |h| < a/4 →
        ∀ x ∈ tsupport η, x + h • coordinate (m+1) k ∈ O) := by
  dsimp only
  refine ⟨?_,?_,hV,?_,?_,?_,?_,?_,?_⟩
  · exact fun x hx => ⟨hx.1,ball_subset_ball (by linarith) hx.2⟩
  · exact fun x hx => ⟨hx.1,ball_subset_ball (by linarith) hx.2⟩
  · exact fun x hx => hV ⟨hx.2,hx.1⟩
  · exact hηsupp.trans (closedBall_subset_ball (by linarith))
  · exact fun x hx => ⟨hx.2, closedBall_subset_ball (by linarith) (hηsupp hx.1)⟩
  · exact fun x hx => hηone x hx.2
  · intro k hk h hh x hx
    exact ⟨tangential_translate_halfSpace x hx.1 k hk h,
      translate_ball_buffer y0 x (7*a/4) (2*a) (a/4) (by linarith) hx.2 k h hh⟩
  · intro k hk h hh x hx
    exact translate_closedBall_buffer y0 x (3*a/2) (2*a) (a/4) (by linarith) (hηsupp hx) k h hh
end P201.BoundaryH2
namespace P201.BoundaryH2

lemma test_gradient_bounded {n : ℕ} (η : Test ℝ (⊤ : Domain n)) :
    ∃ G : ℝ≥0, ∀ x, ‖gradient η x‖ ≤ G := by
  have hc : Continuous (gradient η) := by
    change Continuous (fun x => WithLp.toLp 2 (fun j : Fin n => fderiv ℝ η x (coordinate n j)))
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro j
    exact (η.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : Function.support (gradient η) ⊆ tsupport η := by
    intro x hx
    by_contra hxt
    apply hx
    change WithLp.toLp 2 (fun j : Fin n => fderiv ℝ η x (coordinate n j)) = 0
    rw [fderiv_of_notMem_tsupport ℝ hxt]
    rfl
  have hcs : HasCompactSupport (gradient η) :=
    η.hasCompactSupport.of_isClosed_subset isClosed_closure (closure_minimal hs (isClosed_tsupport η))
  obtain ⟨G,hG⟩ := hcs.exists_bound_of_continuous hc
  refine ⟨⟨max G 0,le_max_right _ _⟩,fun x => (hG x).trans (le_max_left _ _)⟩

/-- The flat boundary estimate on actual nested half balls. All translation
buffers, finite measure and the cutoff-gradient bound are derived. -/
lemma flatBallBoundaryEstimate {m : ℕ} (y0 : Space (m+1)) (a : ℝ) (ha : 0 < a)
    (V : Domain (m+1))
    (hOV : ball y0 (2*a) ∩ (P102.Trace.halfSpace m : Set (Space (m+1))) ⊆ V)
    (η : Test ℝ (⊤ : Domain (m+1)))
    (hη : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hηsupp : tsupport η ⊆ closedBall y0 (3*a/2))
    (hηone : ∀ y ∈ ball y0 a, η y = 1)
    (M L Cz : ℝ≥0) (theta : ℝ) (ht : 0 < theta) :
    let U : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 a,isOpen_ball⟩
    let W : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 (2*a),isOpen_ball⟩
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Space (m+1) → Space (m+1) →L[ℝ] Space (m+1),
      P201Specs.InteriorH2.CoefficientBounds V A M L theta →
      ∀ (v : H ℝ V 1) (f : Lp ℝ V 2), P201Specs.InteriorH2.WeakEquation V A v f →
      ∀ Z : H ℝ (⊤ : Domain (m+1)) 1,
      ((hGradient Z : Space (m+1) → Space (m+1)) =ᵐ[domainMeasure W] hGradient v) →
      (∀ᵐ x ∂volume, x ∉ P102.Trace.halfSpace m →
        hUnderlying ⊤ 1 Z x = 0 ∧ hGradient Z x = 0) →
      ‖Z‖ ≤ Cz * ‖v‖ →
      (∀ k : Fin (m+1), k ≠ Fin.last m →
        Integrable (hFirstDerivative Z k : Space (m+1) → ℝ) volume) →
      ∃ w : H ℝ U 2,
        (hUnderlying U 2 w : Space (m+1) → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
        ‖w‖ ≤ C * (‖v‖ + ‖f‖) := by
  dsimp only
  let U : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 a,isOpen_ball⟩
  let S : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 (7*a/4),isOpen_ball⟩
  let W : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 (2*a),isOpen_ball⟩
  let O : Domain (m+1) := ⟨ball y0 (2*a),isOpen_ball⟩
  have hWV : W ≤ V := fun x hx => hOV ⟨hx.2,hx.1⟩
  obtain ⟨hUS,hSW,hWV,hOV',hηO,hηS,hηU,haS,haO⟩ :=
    flat_ball_buffers y0 a ha V hWV η hηsupp hηone
  have hSB : Bornology.IsBounded (S : Set (Space (m+1))) :=
    Metric.isBounded_ball.subset (show (S : Set (Space (m+1))) ⊆ ball y0 (7*a/4) from fun x hx => hx.2)
  letI : IsFiniteMeasure (domainMeasure S) :=
    isFiniteMeasure_restrict.mpr hSB.measure_lt_top.ne
  obtain ⟨G,hG⟩ := test_gradient_bounded η
  exact flatBoundaryEstimate_with_extension U S W V O hUS hSW hWV hOV' η hη hηO hηS hηU
    G M L Cz theta ht hG (a/4) (by positivity) haS haO
end P201.BoundaryH2

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false
namespace P201.BoundaryH2
open P102.U4 P102.U4.GraphPieces
open P102.Sobolev.Geometry P102.Sobolev.Extension P102.Trace.Ordinary
open P201Specs.InteriorH2

/-- Local boundary H² regularity on a smaller physical ball, with control by
the genuine outer H¹ and L² restrictions. Includes dimension one. -/
theorem localBoundaryEstimate : P201Specs.BoundaryH2.localBoundaryEstimateStatement := by
  intro m Ω hbounded hC11 p hp M L theta ht
  obtain ⟨C,Hder,R,r0,χ,hcenter,hC,hDL,hr0,hr0R,hRchart,hPchart,hχsupp,hχone,hχrange⟩ :=
    selectBoundaryChartNeighborhood Ω hC11 p hp
  have hR : 0 < R := hr0.trans hr0R
  let e := graphFrame m
  let q := flatCoordinates m
  let F0 := physicalChartMap e q Ω C
  let P := P201Specs.BoundaryH2.neighborhood Ω p R
  have hPΩ : P ≤ Ω := inter_subset_left
  have hr0chart : ball p r0 ⊆ fullPhysicalChartOpen e C :=
    (ball_subset_ball hr0R.le).trans hRchart
  obtain ⟨a,s,η,ha,hs,hsr0,hBall,hηsupp,hηclosed,hηone,hηrange,hsmall⟩ :=
    selectNestedFlatCutoff e Ω C p hcenter r0 hr0 hr0chart
  let y0 := q (WithLp.toLp 2 (C.center,(0:ℝ)))
  let U : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 a,isOpen_ball⟩
  let W : Domain (m+1) := P102.Trace.halfSpace m ⊓ ⟨ball y0 (2*a),isOpen_ball⟩
  let Ps := P201Specs.BoundaryH2.neighborhood Ω p s
  have hsR : s < R := hsr0.trans hr0R
  have hPsP : Ps ≤ P := fun x hx => ⟨hx.1,ball_subset_ball hsR.le hx.2⟩
  have hPschart : Ps ≤ physicalChartOpen e Ω C := hPsP.trans hPchart
  let F := F0.restrict P hPchart
  let V := F0.preimageOpen P
  have hWV : W ≤ V := by
    apply flat_ball_subset_preimage_neighborhood e Ω C p y0 R a
    intro y hy
    have hyold := hBall hy
    refine ⟨hyold.1,?_⟩
    change dist ((fullChartMap e q C).toFun y) p < R
    exact (show dist ((fullChartMap e q C).toFun y) p < r0 from hyold.2).trans hr0R
  have hWF : W ≤ flatChartOpen q C.center C.radius C.height := fun y hy => (hWV hy).1
  have hOne : ∀ y ∈ W, χ (F0.toFun y) = 1 := fun y hy => hχone _ (hBall hy.2).2
  let K : Compacts (Space (m+1)) := ⟨tsupport χ,χ.hasCompactSupport⟩
  have hKchart : (K : Set (Space (m+1))) ⊆ fullPhysicalChartOpen e C := hχsupp.trans hRchart
  have hχP : tsupport χ ∩ (Ω : Set (Space (m+1))) ⊆ P := fun x hx => ⟨hx.2,hχsupp hx.1⟩
  obtain ⟨Cext,hCext,hExt⟩ := localizedCoordinateZeroExtension e Ω C K hKchart χ χ.contDiff
    χ.hasCompactSupport (subset_rfl) P hPΩ hχP W hWF hOne
  have hpre : F0.preimageOpen Ps ≤ U :=
    flat_preimage_ball_subset e Ω C Ps hPschart y0 a hsmall
  obtain ⟨Cpush,hCpush,hPush⟩ := physicalGraphH2RestrictionToOpen e q Ω C Hder hC hDL
    Ps hPschart U hpre
  obtain ⟨M',L',theta',ht',hCoef⟩ := physicalGraphCoefficientBounds e q Ω C Hder hC hDL M L theta ht
  let Kh : ℝ := (Fintype.card (P102.U4.SobolevIndex (m+1) 1) : ℝ) *
    P102.U4.pullbackSobolevBound (m+1) 2 (shearConstant C.constant) (shearConstant C.constant)
  let Kf : ℝ := P102.U4.pullbackLpBound (m+1) 2 (shearConstant C.constant)
  have hKh : 0 ≤ Kh := by
    dsimp [Kh,P102.U4.pullbackSobolevBound,P102.U4.pullbackLpBound]; positivity
  have hKf : 0 ≤ Kf := by dsimp [Kf,P102.U4.pullbackLpBound]; positivity
  let Cz : ℝ≥0 := ⟨Cext*Kh,mul_nonneg hCext.le hKh⟩
  have hOV : ball y0 (2*a) ∩ (P102.Trace.halfSpace m : Set (Space (m+1))) ⊆ V :=
    fun y hy => hWV ⟨hy.2,hy.1⟩
  obtain ⟨Cflat,hCflat,hFlat⟩ := flatBallBoundaryEstimate y0 a ha V hOV η hηrange hηclosed hηone
    M' L' Cz theta' ht'
  let Ctotal := 1 + Cpush*Cflat*(Kh+Kf)
  have hCtotal : 0 < Ctotal := by dsimp only [Ctotal]; positivity
  refine ⟨R,s,Ctotal,hs,hsR,hCtotal,?_⟩
  intro A hA hSym u f heq
  have hAphys : CoefficientBounds (physicalChartOpen e Ω C) A M L theta :=
    ⟨fun x hx => hA.1 x hx.1,hA.2.1.mono inter_subset_left,
      fun x hx => hA.2.2 x hx.1⟩
  have hAP : CoefficientBounds P A M L theta :=
    ⟨fun x hx => hA.1 x hx.1,hA.2.1.mono hPΩ,fun x hx => hA.2.2 x hx.1⟩
  have hBF := (hCoef A hAphys).1
  have hBV : CoefficientBounds V
      (fun y => conjugateCoefficient (fderiv ℝ F.invFun (F.toFun y)) (A (F.toFun y))) M' L' theta' :=
    ⟨fun y hy => hBF.1 y hy.1,hBF.2.1.mono inter_subset_left,
      fun y hy => hBF.2.2 y hy.1⟩
  obtain ⟨v,hv,hvd,hvn⟩ := h1Restriction Ω P hPΩ u.val
  let g := InteriorH2.restrictLp hPΩ f
  have hg : (g : Space (m+1) → ℝ) =ᵐ[domainMeasure P] f := InteriorH2.restrictLp_ae hPΩ f
  have heqP : WeakEquation P A v g := weakEquationRestriction Ω P hPΩ A u.val v f g hvd hg heq
  have hvol := coordinateVolume_restrict _ _ _ _ F0 (physicalChartMap_map_volume e q Ω C) P hPchart
  obtain ⟨vf,gf,hvf,hgf,heqF,hvfn,hgfn⟩ := weakEquation_coordinatePullback (Nat.succ_pos m)
    P V _ _ F hvol A hAP.2.1.continuousOn hAP.1 v g heqP
  obtain ⟨Z,hZu,hZzero,hZcoord,hZint,hZsupp,hZn⟩ := hExt u v hv hvd
  have hflatOrig : (hUnderlying V 1 vf : Space (m+1) → ℝ) =ᵐ[domainMeasure V]
      (fun y => hZeroUnderlying Ω u (F0.toFun y)) := hvf.trans (F.ae_comp hv)
  have hZv : (hUnderlying ⊤ 1 Z : Space (m+1) → ℝ) =ᵐ[domainMeasure W] hUnderlying V 1 vf :=
    by
      filter_upwards [hZu,ae_restrict_of_ae_restrict_of_subset hWV hflatOrig] with y hyZ hyv
      exact hyZ.trans hyv.symm
  have hZgrad := h1Gradient_congr_on W ⊤ V le_top hWV Z vf hZv
  have hInv : ‖v‖ ≤ Kh * ‖vf‖ := coordinateH1InverseBound (Nat.succ_pos m) P V _ _ F v vf hvf
  have hZn' : ‖Z‖ ≤ Cz * ‖vf‖ := by
    calc
      _ ≤ Cext * ‖v‖ := hZn
      _ ≤ Cext * (Kh * ‖vf‖) := mul_le_mul_of_nonneg_left hInv hCext.le
      _ = _ := (mul_assoc _ _ _).symm
  obtain ⟨wf,hwf,hwfn⟩ := hFlat _ hBV vf gf heqF Z hZgrad hZzero hZn' (fun k hk => hZint k)
  obtain ⟨ws,hws,hwsn⟩ := hPush wf
  refine ⟨v,g,ws,hv,hg,?_,?_⟩
  · let Fs := F0.restrict Ps hPschart
    have hpreV : F0.preimageOpen Ps ≤ V := fun y hy => ⟨hy.1,hPsP hy.2⟩
    have hc1 := Fs.symm.ae_comp (ae_restrict_of_ae_restrict_of_subset hpre hwf)
    have hc2 := Fs.symm.ae_comp (ae_restrict_of_ae_restrict_of_subset hpreV hvf)
    have hvsmall := ae_restrict_of_ae_restrict_of_subset hPsP hv
    filter_upwards [hws,hc1,hc2,hvsmall,ae_restrict_mem Ps.isOpen.measurableSet]
      with x hx h1 h2 h3 hxPs
    change hUnderlying U 2 wf (F0.invFun x) = hUnderlying V 1 vf (F0.invFun x) at h1
    change hUnderlying V 1 vf (F0.invFun x) = hUnderlying P 1 v (F0.toFun (F0.invFun x)) at h2
    calc
      hUnderlying Ps 2 ws x = hUnderlying U 2 wf (F0.invFun x) := hx
      _ = hUnderlying V 1 vf (F0.invFun x) := h1
      _ = hUnderlying P 1 v (F0.toFun (F0.invFun x)) := h2
      _ = hUnderlying P 1 v x := by rw [F0.right_inv x (hPschart hxPs)]
      _ = _ := h3
  · calc
      ‖ws‖ ≤ Cpush * ‖wf‖ := hwsn
      _ ≤ Cpush * (Cflat * (‖vf‖ + ‖gf‖)) := mul_le_mul_of_nonneg_left hwfn hCpush.le
      _ ≤ Cpush * (Cflat * (Kh*‖v‖ + Kf*‖g‖)) := by gcongr
      _ ≤ Cpush * (Cflat * ((Kh+Kf)*(‖v‖+‖g‖))) := by
        apply mul_le_mul_of_nonneg_left _ hCpush.le
        apply mul_le_mul_of_nonneg_left _ hCflat.le
        nlinarith [mul_nonneg hKh (norm_nonneg g),mul_nonneg hKf (norm_nonneg v)]
      _ = (Cpush*Cflat*(Kh+Kf))*(‖v‖+‖g‖) := by ring
      _ ≤ Ctotal * (‖v‖+‖g‖) := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left zero_le_one) (add_nonneg (norm_nonneg v) (norm_nonneg g))
end P201.BoundaryH2
