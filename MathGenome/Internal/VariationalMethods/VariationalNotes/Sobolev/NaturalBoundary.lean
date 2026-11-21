import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.NaturalBoundary
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.DominatedEulerLagrange
import MathGenome.Internal.MultivariableAnalysis.D04.C12.RegularDomainGeometryAndJordanMeasurability
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Extend

import MathGenome.Internal.MultivariableAnalysis.D04.C12.GaussDivergenceTheorem
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Piecewise
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace ContDiff Topology

namespace VariationalNotes.Sobolev.NaturalBoundary

/-- An interior test is an allowed ambient test. -/
theorem smoothNearClosure_of_test {d m : ℕ} {Ω : Opens (Domain d)}
    (φ : VectorTest Ω m) : SmoothNearClosure Ω (φ : Domain d → Vector m) := by
  exact ⟨univ, isOpen_univ, subset_univ _, φ.contDiff.contDiffOn⟩

/-- The two Jacobian conventions are identical on compactly supported tests. -/
theorem jacobian_test {d m : ℕ} {Ω : Opens (Domain d)} (φ : VectorTest Ω m) :
    jacobian (φ : Domain d → Vector m) = EulerLagrange.testGradient φ := by
  funext x
  apply PiLp.ext
  intro ij
  simp [jacobian, EulerLagrange.testGradient,
    (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]

/-- Match ambient-test and compact-test weak pairings without changing norms. -/
theorem density_test {d m : ℕ} {Ω : Opens (Domain d)}
    (A : Domain d → Vector m) (P : Domain d → Gradient m d) (φ : VectorTest Ω m) :
    density A P (φ : Domain d → Vector m) = EulerLagrange.weakDensity A P φ := by
  funext x
  change ⟪A x, φ x⟫_ℝ + frobenius (P x) (jacobian (φ : Domain d → Vector m) x) = _
  rw [jacobian_test]
  rfl

/-- One-sided C¹ regularity implies ordinary C¹ regularity in the interior. -/
theorem C1UpToClosure.contDiffOn {d m : ℕ} {Ω : Opens (Domain d)}
    {P : Domain d → Gradient m d} (hP : C1UpToClosure Ω P) :
    ContDiffOn ℝ 1 P Ω := by
  obtain ⟨_, L, hL, hd⟩ := hP
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) Ω.isOpen).mpr
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,
    by simp, contDiffOn_zero.mpr ?_⟩
  exact (hL.mono subset_closure).congr fun x hx => (hd x hx).fderiv

/-- Each matrix entry is C¹, with its genuine Euclidean coordinate map. -/
theorem contDiffOn_entry {d m : ℕ} {Ω : Opens (Domain d)}
    {P : Domain d → Gradient m d} (hP : ContDiffOn ℝ 1 P Ω)
    (i : Fin m) (j : Fin d) : ContDiffOn ℝ 1 (fun x => P x (i,j)) Ω := by
  let L : Gradient m d →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m × Fin d => ℝ) (i,j)
  exact L.contDiff.comp_contDiffOn hP

/-- Interior continuity of an individual classical partial derivative. -/
theorem continuousOn_partial {d : ℕ} {Ω : Opens (Domain d)} {f : Domain d → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω) (j : Fin d) :
    ContinuousOn (fun x => fderiv ℝ f x (P102.U4.coordinateVector d j)) Ω :=
  ((hf.fderiv_of_isOpen Ω.isOpen (m := 0) (by simp)).clm_apply
    contDiffOn_const).continuousOn

/-- Scalar integration by parts identifies a classical and distributional derivative. -/
theorem lineDeriv_ofFun {d : ℕ} (Ω : Opens (Domain d)) {f : Domain d → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω) (j : Fin d) :
    Distribution.lineDerivCLM (P102.U4.coordinateVector d j)
      (Distribution.ofFun Ω f volume ⊤) =
    Distribution.ofFun Ω (fun x => fderiv ℝ f x (P102.U4.coordinateVector d j)) volume ⊤ := by
  have hi : LocallyIntegrableOn f Ω volume :=
    hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hdi : LocallyIntegrableOn (fun x => fderiv ℝ f x (P102.U4.coordinateVector d j)) Ω volume :=
    (continuousOn_partial hf j).locallyIntegrableOn Ω.isOpen.measurableSet
  ext ψ
  rw [Distribution.lineDerivCLM_apply, Distribution.ofFun_apply hi,
    Distribution.ofFun_apply hdi]
  change -(∫ x, (TestFunction.lineDerivCLM ℝ (P102.U4.coordinateVector d j) ψ :
    P102.U4.TestSpace ℝ Ω) x * f x) =
    ∫ x, ψ x * fderiv ℝ f x (P102.U4.coordinateVector d j)
  rw [P102.U4.integral_test_mul_partial Ω hf j ψ]
  rfl

/-- The classical row divergence is continuous in the interior. -/
theorem continuousOn_divergence {d m : ℕ} {Ω : Opens (Domain d)}
    {P : Domain d → Gradient m d} (hP : ContDiffOn ℝ 1 P Ω) :
    ContinuousOn (divergence P) Ω := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact continuousOn_finsetSum _ (fun j _ => continuousOn_partial (contDiffOn_entry hP i j) j)

/-- The upstream row distribution is the classical row divergence for C¹ fields. -/
theorem rowDivergence_eq_classical {d m : ℕ} (Ω : Opens (Domain d))
    {P : Domain d → Gradient m d} (hP : ContDiffOn ℝ 1 P Ω) (i : Fin m) :
    EulerLagrange.rowDivergence Ω P i =
      Distribution.ofFun Ω (fun x => divergence P x i) volume ⊤ := by
  have hdi (j : Fin d) : LocallyIntegrableOn
      (fun x => fderiv ℝ (fun y => P y (i,j)) x (P102.U4.coordinateVector d j)) Ω volume := (continuousOn_partial (contDiffOn_entry hP i j) j).locallyIntegrableOn
    Ω.isOpen.measurableSet
  have hq : LocallyIntegrableOn (fun x => divergence P x i) Ω volume := ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).comp_continuousOn
    (continuousOn_divergence hP)).locallyIntegrableOn Ω.isOpen.measurableSet
  simp only [EulerLagrange.rowDivergence, lineDeriv_ofFun Ω (contDiffOn_entry hP i _)]
  ext ψ
  rw [Distribution.ofFun_apply hq]
  simp only [sum_apply, Distribution.ofFun_apply (hdi _), smul_eq_mul]
  change (∑ j, ∫ x, ψ x * fderiv ℝ (fun y => P y (i,j)) x (P102.U4.coordinateVector d j)) =
    ∫ x, ψ x * ∑ j, fderiv ℝ (fun y => P y (i,j)) x (P102.U4.coordinateVector d j)
  simp_rw [Finset.mul_sum]
  exact (integral_finsetSum _ (fun j _ => ψ.integrable_smul (hdi j))).symm

/-- Ambient stationarity forces the pointwise interior Euler–Lagrange equation. -/
theorem interior_equation : Expected.InteriorEquation := by
  intro d m Ω A P hA hP hs
  have hPc := hP.contDiffOn
  have hAi (i : Fin m) : LocallyIntegrableOn (fun x => A x i) Ω volume := ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).comp_continuousOn
    hA).locallyIntegrableOn Ω.isOpen.measurableSet
  have hPi (i : Fin m) (j : Fin d) : LocallyIntegrableOn (fun x => P x (i,j)) Ω volume := (contDiffOn_entry hPc i j).continuousOn.locallyIntegrableOn
    Ω.isOpen.measurableSet
  have hw : ∀ φ : VectorTest Ω m,
      (∫ x, EulerLagrange.weakDensity A P φ x ∂domainMeasure Ω) = 0 := by
    intro φ
    have ht := (hs φ (smoothNearClosure_of_test φ)).2
    rwa [density_test] at ht
  have he := (EulerLagrange.distributional_euler_lagrange Ω A P hAi hPi).mp hw
  exact EulerLagrange.pointwise_euler_lagrange Ω A P (divergence P) hA
    (continuousOn_divergence hPc) he (rowDivergence_eq_classical Ω hPc)

/-- No regularity is necessary for an a.e. zero boundary trace. -/
theorem zero_trace_pairing : Expected.ZeroTracePairing := by
  intro d m Ω hΩ P t ht
  have he : (fun x => ⟪normalFlux hΩ P x, t x⟫_ℝ) =ᵐ[boundaryMeasure Ω] 0 := by
    filter_upwards [ht] with x hx
    simp only [Pi.zero_apply] at hx
    simp [hx]
  exact ⟨(integrable_zero _ _ _).congr he.symm, (integral_congr_ae he).trans (by simp)⟩

/-- In particular, the classical zero boundary value kills the boundary pairing. -/
theorem zero_boundary_pairing : Expected.ZeroBoundaryPairing := by
  intro d m Ω hΩ P φ hφ
  apply (zero_trace_pairing Ω hΩ P (fun x => φ x) _).2
  exact Filter.Eventually.of_forall fun x => hφ x x.property

/-- Constant fields satisfy the source's one-sided boundary regularity. -/
theorem c1UpToClosure_const {d m : ℕ} (Ω : Opens (Domain d)) (M : Gradient m d) :
    C1UpToClosure Ω (fun _ => M) := by
  refine ⟨continuousOn_const, fun _ => 0, continuousOn_const, ?_⟩
  intro x _
  exact hasFDerivAt_const M x

/-- The identity matrix field gives the fixed-boundary contrast on every
regular domain. At an actual boundary point its normal flux is a unit vector. -/
theorem fixed_boundary_contrast : Expected.FixedBoundaryContrast := by
  intro d Ω hΩ
  classical
  let M : Gradient d d := WithLp.toLp 2 (fun ij => if ij.1 = ij.2 then 1 else 0)
  let P : Domain d → Gradient d d := fun _ => M
  refine ⟨P, contDiff_const, c1UpToClosure_const Ω M, ?_, ?_, ?_⟩
  · intro x
    apply PiLp.ext
    intro i
    simp [divergence, P]
  · intro φ hφ
    exact zero_boundary_pairing Ω hΩ P φ hφ
  · intro x
    have he : normalFlux hΩ P x =
        Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hΩ x := by
      apply PiLp.ext
      intro i
      simp [normalFlux, P, M]
    rw [he]
    have hn := D04.ClassicalRegularDomains.outwardNormal_unit hΩ x
    intro hz
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn

/-- The geometric normal is continuous on the actual boundary. Its chosen
local defining function can be replaced by one fixed defining function near
any given point, so no continuity of the choices is required. -/
theorem continuous_outwardNormal {d : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) :
    Continuous (Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hΩ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U, ρ, hpU, hρ⟩ := hΩ.defining p p.property
  have hd : ContinuousOn (fderiv ℝ ρ) U :=
    (hρ.regular.fderiv_of_isOpen hρ.isOpen (m := 0) (by simp)).continuousOn
  have hg : ContinuousOn (_root_.gradient ρ) U :=
    (InnerProductSpace.toDual ℝ (Domain d)).symm.continuous.comp_continuousOn hd
  have hg0 : _root_.gradient ρ p ≠ 0 := D04.ClassicalRegularDomains.gradient_ne_zero
    (hρ.nonzero p hpU ((hρ.zero_level p hpU).mp p.property))
  have hc : ContinuousAt
      (fun x => ‖_root_.gradient ρ x‖⁻¹ • _root_.gradient ρ x) (p : Domain d) :=
    ((hg p hpU).continuousAt (hρ.isOpen.mem_nhds hpU)).norm.inv₀
      (norm_ne_zero_iff.mpr hg0) |>.smul
        ((hg p hpU).continuousAt (hρ.isOpen.mem_nhds hpU))
  have he : Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hΩ =ᶠ[𝓝 p]
      (fun x : frontier (Ω : Set (Domain d)) =>
        ‖_root_.gradient ρ x‖⁻¹ • _root_.gradient ρ x) := by
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (hρ.isOpen.mem_nhds hpU)] with x hx
    exact D04.ClassicalRegularDomains.outwardNormal_formula hΩ x hρ hx
  exact (hc.comp continuous_subtype_val.continuousAt).congr he.symm

/-- A continuous matrix field on the closure has continuous normal flux on
the boundary. -/
theorem continuous_normalFlux {d m : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) {P : Domain d → Gradient m d}
    (hP : ContinuousOn P (closure (Ω : Set (Domain d)))) :
    Continuous (normalFlux hΩ P) := by
  have hp : Continuous (fun x : frontier (Ω : Set (Domain d)) => P x) :=
    hP.comp_continuous continuous_subtype_val (fun x => frontier_subset_closure x.property)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_finsetSum _ fun j _ =>
    ((PiLp.continuous_apply 2 (fun _ : Fin m × Fin d => ℝ) (i,j)).comp hp).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp
        (continuous_outwardNormal hΩ))

/-- Every ambient neighborhood of a boundary point has positive
codimension-one Hausdorff measure on the boundary. The proof uses the local
inverse coordinates and the fact that Lipschitz maps preserve null sets;
it includes zero-dimensional boundary charts. -/
theorem hausdorff_frontier_inter_open_ne_zero_succ {d : ℕ}
    {Ω : Opens (Domain (d+1))} (hΩ : RegularDomain Ω)
    (p : frontier (Ω : Set (Domain (d+1))))
    {V : Set (Domain (d+1))} (hV : IsOpen V) (hpV : (p : Domain (d+1)) ∈ V) :
    Measure.hausdorffMeasure (d : ℝ) (frontier (Ω : Set (Domain (d+1))) ∩ V) ≠ 0 := by
  obtain ⟨U, ρ, hpU, hρ⟩ := hΩ.defining p p.property
  obtain ⟨C⟩ := D04.RegularDomainGeometry.boundary_coordinates hρ ⟨p.property, hpU⟩
  obtain ⟨hX, hY, hpX, hFpY, hXU, hbij, hgmap, hleft, hright, _⟩ := C.inverse
  obtain ⟨K, t, ht, hLip⟩ :=
    (C.forward_regular.contDiffAt (hX.mem_nhds hpX)).exists_lipschitzOnWith
  obtain ⟨W, hWt, hW, hpW⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hV.mem_nhds hpV) (Filter.inter_mem (hX.mem_nhds hpX) ht))
  have hWV : W ⊆ V := fun x hx => (hWt hx).1
  have hWX : W ⊆ C.X := fun x hx => (hWt hx).2.1
  have hWt' : W ⊆ t := fun x hx => (hWt hx).2.2
  let L : Domain (d+1) ≃L[ℝ] Domain d × Domain 1 := EuclideanSpace.finAddEquivProd
  let I : Domain d → Domain (d+1) := fun a => L.symm (a, 0)
  let Q : Domain (d+1) →L[ℝ] Domain d :=
    (ContinuousLinearMap.fst ℝ (Domain d) (Domain 1)).comp L.toContinuousLinearMap
  have hlast (x : Domain (d+1)) : (L x).2 0 = x (Fin.last d) := by
    rfl
  have hIlast (a : Domain d) : I a (Fin.last d) = 0 := by
    rw [← hlast]
    simp [I]
  have hIp : I (L (C.F p)).1 = C.F p := by
    apply L.injective
    simp only [I, L.apply_symm_apply]
    refine Prod.ext (by rfl) ?_
    apply PiLp.ext
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [hlast, C.final_coordinate, (hρ.zero_level p hpU).mp p.property,
      neg_zero, PiLp.zero_apply]
  have hI : Continuous I := L.symm.continuous.comp (continuous_id.prodMk continuous_const)
  let B : Set (Domain d) := I ⁻¹' (C.Y ∩ C.g ⁻¹' W)
  have hB : IsOpen B :=
    ((C.backward_regular.continuousOn.isOpen_inter_preimage hY hW)).preimage hI
  have hqB : (L (C.F p)).1 ∈ B := by
    change I (L (C.F p)).1 ∈ C.Y ∩ C.g ⁻¹' W
    rw [hIp]
    exact ⟨hFpY, by simpa only [mem_preimage, hleft hpX] using hpW⟩
  have hBpos : Measure.hausdorffMeasure (d : ℝ) B ≠ 0 := by
    exact hB.measure_ne_zero (Measure.hausdorffMeasure (d : ℝ)) ⟨_, hqB⟩
  let S : Set (Domain (d+1)) := frontier (Ω : Set (Domain (d+1))) ∩ W
  have hsub : B ⊆ (Q ∘ C.F) '' S := by
    intro a ha
    have ha' : I a ∈ C.Y ∧ C.g (I a) ∈ W := ha
    have hgX := hgmap ha'.1
    have hgb : C.g (I a) ∈ frontier (Ω : Set (Domain (d+1))) := by
      apply (hρ.zero_level _ (hXU hgX)).mpr
      have hh := C.final_coordinate (C.g (I a))
      rw [hright ha'.1, hIlast] at hh
      linarith
    refine ⟨C.g (I a), ⟨hgb, ha'.2⟩, ?_⟩
    simp [hright ha'.1, Q, I]
  have hQLip : LipschitzOnWith (‖Q‖₊ * K) (Q ∘ C.F) S :=
    Q.lipschitzWith.comp_lipschitzOnWith (hLip.mono (fun x hx => hWt' hx.2))
  intro hz
  have hSz : Measure.hausdorffMeasure (d : ℝ) S = 0 :=
    measure_mono_null (inter_subset_inter_right _ hWV) hz
  have himz : Measure.hausdorffMeasure (d : ℝ) ((Q ∘ C.F) '' S) = 0 := by
    apply le_antisymm _ (zero_le)
    exact (hQLip.hausdorffMeasure_image_le (Nat.cast_nonneg d)).trans (by rw [hSz, mul_zero])
  exact hBpos (measure_mono_null hsub himz)

/-- The normalized surface measure charges every relative boundary
neighborhood, including in ambient dimension one. -/
theorem boundaryMeasure_preimage_open_ne_zero {d : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) (p : frontier (Ω : Set (Domain d)))
    {V : Set (Domain d)} (hV : IsOpen V) (hpV : (p : Domain d) ∈ V) :
    boundaryMeasure Ω (Subtype.val ⁻¹' V) ≠ 0 := by
  have hh : Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)
      (frontier (Ω : Set (Domain d)) ∩ V) ≠ 0 := by
    cases d with
    | zero => have := hΩ.dimension; omega
    | succ n => exact hausdorff_frontier_inter_open_ne_zero_succ hΩ p hV hpV
  have he : Measure.euclideanHausdorffMeasure (d - 1)
      (frontier (Ω : Set (Domain d)) ∩ V) ≠ 0 := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def]
    exact mul_ne_zero (by exact_mod_cast
      Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero (d - 1)) hh
  intro hz
  apply he
  have hz' := Measure.measure_image_eq_zero_of_comap_eq_zero
    (Subtype.val : frontier (Ω : Set (Domain d)) → Domain d)
    (Measure.euclideanHausdorffMeasure (d - 1)) Subtype.val_injective
    (fun s hs => ((MeasurableEmbedding.subtype_coe measurableSet_frontier).measurableSet_image' hs).nullMeasurableSet) hz
  simpa only [image_preimage_eq_inter_range, Subtype.range_val, inter_comm] using hz'

/-- On convex open sets the continuous one-sided derivative field is an
actual derivative within the closure. This is the boundary differentiability
step needed before reflecting a flattened flux. -/
theorem C1UpToClosure.derivativeWithin_closure_of_convex {d m : ℕ}
    {Ω : Opens (Domain d)} {P : Domain d → Gradient m d}
    (hP : C1UpToClosure Ω P) (hconv : Convex ℝ (Ω : Set (Domain d))) :
    ∃ L : Domain d → (Domain d →L[ℝ] Gradient m d),
      ContinuousOn L (closure (Ω : Set (Domain d))) ∧
      ∀ x ∈ closure (Ω : Set (Domain d)),
        HasFDerivWithinAt P (L x) (closure (Ω : Set (Domain d))) x := by
  obtain ⟨hPc, L, hL, hder⟩ := hP
  refine ⟨L, hL, ?_⟩
  intro x hx
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hder y hy).differentiableAt.differentiableWithinAt) hconv Ω.isOpen
    (fun y hy => (hPc y hy).mono subset_closure)
  have he : fderiv ℝ P =ᶠ[𝓝[(Ω : Set (Domain d))] x] L := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hder y hy).fderiv
  exact ((hL x hx).mono subset_closure).congr' he.symm

/-- In the flattened convex case the original one-sided regularity therefore
implies C¹ regularity within the closed domain, without assuming an extension. -/
theorem C1UpToClosure.contDiffOn_closure_of_convex {d m : ℕ}
    {Ω : Opens (Domain d)} {P : Domain d → Gradient m d}
    (hP : C1UpToClosure Ω P) (hconv : Convex ℝ (Ω : Set (Domain d))) :
    ContDiffOn ℝ 1 P (closure (Ω : Set (Domain d))) := by
  obtain ⟨L, hL, hder⟩ := hP.derivativeWithin_closure_of_convex hconv
  apply (contDiffOn_succ_iff_hasFDerivWithinAt (n := 0) (by simp)).mpr
  intro x hx
  refine ⟨closure (Ω : Set (Domain d)), ?_, by simp, L, hder, contDiffOn_zero.mpr hL⟩
  rw [insert_eq_of_mem hx]
  exact self_mem_nhdsWithin

/-- The first derivatives of an ambient smooth test are continuous on the
closure even though its representative is arbitrary far from the domain. -/
theorem continuousOn_jacobian {d m : ℕ} {Ω : Opens (Domain d)}
    {φ : Domain d → Vector m} (hφ : SmoothNearClosure Ω φ) :
    ContinuousOn (jacobian φ) (closure (Ω : Set (Domain d))) := by
  obtain ⟨U, hU, hclU, hφ⟩ := hφ
  have hd := (hφ.fderiv_of_isOpen hU (m := 0) (by simp)).continuousOn.mono hclU
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m × Fin d => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro ij
  exact (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) ij.1).comp_continuousOn
    (hd.clm_apply continuousOn_const)

/-- A continuous extension of the derivative field supplies a continuous
representative of the row divergence on the closure. -/
theorem exists_continuous_divergence_extension {d m : ℕ} {Ω : Opens (Domain d)}
    {P : Domain d → Gradient m d} (hP : C1UpToClosure Ω P) :
    ∃ q : Domain d → Vector m,
      ContinuousOn q (closure (Ω : Set (Domain d))) ∧ EqOn q (divergence P) Ω := by
  obtain ⟨_, L, hL, hder⟩ := hP
  let q : Domain d → Vector m := fun x => WithLp.toLp 2 (fun i =>
    ∑ j : Fin d, (L x (P102.U4.coordinateVector d j)) (i,j))
  refine ⟨q, ?_, ?_⟩
  · apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    exact continuousOn_finsetSum _ fun j _ =>
      (PiLp.continuous_apply 2 (fun _ : Fin m × Fin d => ℝ) (i,j)).comp_continuousOn
        (hL.clm_apply continuousOn_const)
  · intro x hx
    apply PiLp.ext
    intro i
    change (∑ j : Fin d, (L x (P102.U4.coordinateVector d j)) (i,j)) = _
    apply Finset.sum_congr rfl
    intro j _
    let pr : Gradient m d →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin m × Fin d => ℝ) (i,j)
    have hh : HasFDerivAt (fun y => P y (i,j)) (pr.comp (L x)) x :=
      pr.hasFDerivAt.comp x (hder x hx)
    rw [hh.fderiv]
    rfl

/-- The volume term in Green's formula is integrable under precisely the
one-sided C¹ convention. No ambient extension of the flux is used here. -/
theorem integrable_green_density {d m : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) {P : Domain d → Gradient m d} (hP : C1UpToClosure Ω P)
    {φ : Domain d → Vector m} (hφ : SmoothNearClosure Ω φ) :
    Integrable (density (divergence P) P φ) (domainMeasure Ω) := by
  obtain ⟨q, hq, hqeq⟩ := exists_continuous_divergence_extension hP
  obtain ⟨U, hU, hclU, hφreg⟩ := hφ
  have hφcl : ContinuousOn φ (closure (Ω : Set (Domain d))) :=
    hφreg.continuousOn.mono hclU
  have hj : ContinuousOn (jacobian φ) (closure (Ω : Set (Domain d))) :=
    continuousOn_jacobian ⟨U, hU, hclU, hφreg⟩
  have hc : ContinuousOn (density q P φ) (closure (Ω : Set (Domain d))) :=
    (hq.inner hφcl).add (hP.1.inner hj)
  have hi := (hc.integrableOn_compact (μ := volume) hΩ.bounded.isCompact_closure).mono_set subset_closure
  apply hi.congr
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  simp only [density, hqeq hx]

/-- Boundary coordinates also give locally finite Hausdorff measure:
a small boundary patch is contained in a Lipschitz image of a compact
parameter ball. -/
theorem exists_boundary_neighborhood_hausdorff_lt_top {d : ℕ}
    {Ω : Opens (Domain (d+1))} (hΩ : RegularDomain Ω)
    (p : frontier (Ω : Set (Domain (d+1)))) :
    ∃ W : Set (Domain (d+1)), IsOpen W ∧ (p : Domain (d+1)) ∈ W ∧
      Measure.hausdorffMeasure (d : ℝ) (frontier (Ω : Set (Domain (d+1))) ∩ W) < ⊤ := by
  obtain ⟨U, ρ, hpU, hρ⟩ := hΩ.defining p p.property
  obtain ⟨C⟩ := D04.RegularDomainGeometry.boundary_coordinates hρ ⟨p.property, hpU⟩
  obtain ⟨hX, hY, hpX, hFpY, hXU, _, hgmap, hleft, hright, _, _, ⟨Kg, hgLip⟩, _⟩ := C.inverse
  let L : Domain (d+1) ≃L[ℝ] Domain d × Domain 1 := EuclideanSpace.finAddEquivProd
  let I : Domain d →L[ℝ] Domain (d+1) := L.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Domain d) (Domain 1))
  let Q : Domain (d+1) →L[ℝ] Domain d :=
    (ContinuousLinearMap.fst ℝ (Domain d) (Domain 1)).comp L.toContinuousLinearMap
  have hlast (x : Domain (d+1)) : (L x).2 0 = x (Fin.last d) := rfl
  have hflat (x : Domain (d+1)) (hx : x ∈ C.X)
      (hxb : x ∈ frontier (Ω : Set (Domain (d+1)))) : I (Q (C.F x)) = C.F x := by
    apply L.injective
    change L (L.symm ((L (C.F x)).1, 0)) = L (C.F x)
    rw [L.apply_symm_apply]
    refine Prod.ext (by rfl) ?_
    apply PiLp.ext
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [hlast, C.final_coordinate, (hρ.zero_level x (hXU hx)).mp hxb,
      neg_zero, PiLp.zero_apply]
  let a : Domain d := Q (C.F p)
  have hIa : I a = C.F p := hflat p hpX p.property
  have haY : a ∈ I ⁻¹' C.Y := by
    change I a ∈ C.Y
    rw [hIa]
    exact hFpY
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((hY.preimage I.continuous).mem_nhds haY)
  let K : Set (Domain d) := Metric.closedBall a (r/2)
  have hIK : MapsTo I K C.Y := fun b hb => hball
    ((Metric.closedBall_subset_ball (half_lt_self hr)) hb)
  let W : Set (Domain (d+1)) := C.X ∩ (fun x => Q (C.F x)) ⁻¹' Metric.ball a (r/2)
  have hW : IsOpen W := (Q.continuous.comp_continuousOn C.forward_regular.continuousOn).isOpen_inter_preimage hX Metric.isOpen_ball
  have hpW : (p : Domain (d+1)) ∈ W :=
    ⟨hpX, Metric.mem_ball_self (half_pos hr)⟩
  refine ⟨W, hW, hpW, ?_⟩
  have hsub : frontier (Ω : Set (Domain (d+1))) ∩ W ⊆ (C.g ∘ I) '' K := by
    intro x hx
    refine ⟨Q (C.F x), Metric.ball_subset_closedBall hx.2.2, ?_⟩
    change C.g (I (Q (C.F x))) = x
    rw [hflat x hx.2.1 hx.1, hleft hx.2.1]
  have hcomp : LipschitzOnWith (Kg * ‖I‖₊) (C.g ∘ I) K :=
    hgLip.comp I.lipschitzWith.lipschitzOnWith hIK
  have hbound := hcomp.hausdorffMeasure_image_le (Nat.cast_nonneg d)
  rw [ENNReal.rpow_natCast] at hbound
  apply (measure_mono hsub).trans_lt
  apply hbound.trans_lt
  exact ENNReal.mul_lt_top (by exact ENNReal.pow_lt_top (by exact ENNReal.coe_lt_top))
    (isCompact_closedBall a (r/2)).measure_lt_top

/-- A bounded C¹ boundary has finite normalized surface measure. -/
theorem boundaryMeasure_univ_lt_top {d : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) : boundaryMeasure Ω univ < ⊤ := by
  have hh : Measure.hausdorffMeasure ((d - 1 : ℕ) : ℝ)
      (frontier (Ω : Set (Domain d))) < ⊤ := by
    cases d with
    | zero => have := hΩ.dimension; omega
    | succ n =>
      classical
      choose W hW hpW hfinite using
        exists_boundary_neighborhood_hausdorff_lt_top hΩ
      have hcompact : IsCompact (frontier (Ω : Set (Domain (n+1)))) :=
        hΩ.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
      obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover W hW (by
        intro x hx
        exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpW ⟨x, hx⟩⟩)
      have hsub : frontier (Ω : Set (Domain (n+1))) ⊆
          ⋃ p ∈ s, frontier (Ω : Set (Domain (n+1))) ∩ W p := by
        intro x hx
        obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
        exact mem_iUnion₂.mpr ⟨p, hp, hx, hxp⟩
      exact (measure_mono hsub).trans_lt
        (measure_biUnion_lt_top s.finite_toSet (fun p _ => hfinite p))
  rw [boundaryMeasure, comap_subtype_coe_apply measurableSet_frontier,
    image_univ, Subtype.range_val, Measure.euclideanHausdorffMeasure_def,
    Measure.smul_apply, ENNReal.smul_def]
  exact ENNReal.mul_lt_top (by simp) hh

/-- Continuous boundary pairings are integrable for all permitted tests. -/
theorem integrable_boundary_pairing {d m : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) {P : Domain d → Gradient m d}
    (hP : ContinuousOn P (closure (Ω : Set (Domain d))))
    {φ : Domain d → Vector m} (hφ : SmoothNearClosure Ω φ) :
    Integrable (fun x => ⟪normalFlux hΩ P x, φ x⟫_ℝ) (boundaryMeasure Ω) := by
  let : IsFiniteMeasure (boundaryMeasure Ω) := ⟨boundaryMeasure_univ_lt_top hΩ⟩
  have hcompact : IsCompact (frontier (Ω : Set (Domain d))) :=
    hΩ.bounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain d))) := isCompact_iff_compactSpace.mp hcompact
  obtain ⟨U, _, hclU, hφ⟩ := hφ
  have hcφ : Continuous (fun x : frontier (Ω : Set (Domain d)) => φ x) :=
    (hφ.continuousOn.mono hclU).comp_continuous continuous_subtype_val
      (fun x => frontier_subset_closure x.property)
  exact ((continuous_normalFlux hΩ hP).inner hcφ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Ambient smooth tests detect a continuous normal flux pointwise. -/
theorem boundary_detection : Expected.BoundaryDetection := by
  intro d m Ω hΩ P hP htest p
  by_contra hp
  let g := normalFlux hΩ P
  have hc : Continuous g := continuous_normalFlux hΩ hP
  have hpos : 0 < ⟪g p, g p⟫_ℝ := real_inner_self_pos.mpr hp
  have ho : IsOpen {x : frontier (Ω : Set (Domain d)) | 0 < ⟪g x, g p⟫_ℝ} :=
    isOpen_lt continuous_const (hc.inner continuous_const)
  obtain ⟨O, hO, hEq⟩ := isOpen_induced_iff.mp ho
  have hpO : (p : Domain d) ∈ O := by
    change p ∈ (Subtype.val ⁻¹' O : Set (frontier (Ω : Set (Domain d))))
    rw [hEq]
    exact hpos
  obtain ⟨χ, hχsm, _, hχrange, ⟨W, hW, hpW, hχone⟩, _, hχsupp⟩ :=
    D04.EuclideanSmoothCutoffs.exists_smooth_cutoff
      {(p : Domain d)} O isCompact_singleton hO (singleton_subset_iff.mpr hpO)
  let φ : Domain d → Vector m := fun x => χ x • g p
  have hφ : SmoothNearClosure Ω φ :=
    ⟨univ, isOpen_univ, subset_univ _, (hχsm.smul contDiff_const).contDiffOn⟩
  obtain ⟨hi, hz⟩ := htest φ hφ
  have hnonneg : ∀ x : frontier (Ω : Set (Domain d)), 0 ≤ ⟪g x, φ x⟫_ℝ := by
    intro x
    change 0 ≤ ⟪g x, χ x • g p⟫_ℝ
    rw [inner_smul_right]
    by_cases hχzero : χ x = 0
    · simp [hχzero]
    · have hxO : (x : Domain d) ∈ O := hχsupp (subset_tsupport χ hχzero)
      have hxpos : 0 < ⟪g x, g p⟫_ℝ := by
        have hx : x ∈ (Subtype.val ⁻¹' O : Set (frontier (Ω : Set (Domain d)))) := hxO
        rw [hEq] at hx
        exact hx
      exact mul_nonneg (hχrange x).1 hxpos.le
  have hae : (fun x => ⟪g x, φ x⟫_ℝ) =ᵐ[boundaryMeasure Ω] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hz
  have hmeasure : boundaryMeasure Ω
      {x : frontier (Ω : Set (Domain d)) | ⟪g x, φ x⟫_ℝ ≠ 0} = 0 := by
    exact ae_iff.mp hae
  apply boundaryMeasure_preimage_open_ne_zero hΩ p hW (hpW (mem_singleton _))
  apply measure_mono_null _ hmeasure
  intro x hx
  have hχx : χ x = 1 := hχone hx
  have hxO : (x : Domain d) ∈ O := hχsupp
    (subset_tsupport χ (by change χ x ≠ 0; rw [hχx]; exact one_ne_zero))
  have hxpos : 0 < ⟪g x, g p⟫_ℝ := by
    have hx' : x ∈ (Subtype.val ⁻¹' O : Set (frontier (Ω : Set (Domain d)))) := hxO
    rw [hEq] at hx'
    exact hx'
  change ⟪g x, χ x • g p⟫_ℝ ≠ 0
  simpa only [hχx, one_smul] using hxpos.ne'


/-- Equality of state coefficients in Ω gives equality of the actual densities
almost everywhere for the restricted Lebesgue measure. -/
theorem density_congr_on {d m : ℕ} (Ω : Opens (Domain d))
    {A B : Domain d → Vector m} (P : Domain d → Gradient m d)
    (φ : Domain d → Vector m) (hAB : ∀ x ∈ Ω, A x = B x) :
    density A P φ =ᵐ[domainMeasure Ω] density B P φ := by
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  simp only [density, hAB x hx]


end VariationalNotes.Sobolev.NaturalBoundary

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace VariationalNotes.Sobolev.NaturalBoundary.C1Reflection
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def lower : Set (E × ℝ) := {x | x.2 ≤ 0}
def upper : Set (E × ℝ) := {x | 0 ≤ x.2}

def reflect (a : ℝ) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod ((-a) • ContinuousLinearMap.snd ℝ E ℝ)

@[simp] lemma reflect_apply (a : ℝ) (x : E × ℝ) :
    reflect a x = (x.1, -a * x.2) := rfl

lemma reflect_fixed {x : E × ℝ} (hx : x.2 = 0) (a : ℝ) : reflect a x = x := by
  ext <;> simp [hx]

lemma reflect_combination (L : (E × ℝ) →L[ℝ] F) :
    (3 : ℝ) • (L.comp (reflect 1)) - (2 : ℝ) • (L.comp (reflect 2)) = L := by
  apply ContinuousLinearMap.ext
  intro x
  change (3 : ℝ) • L (x.1, -1 * x.2) - (2 : ℝ) • L (x.1, -2 * x.2) = L x
  rw [← map_smul, ← map_smul, ← map_sub]
  congr 1
  apply Prod.ext
  · change (3 : ℝ) • x.1 - (2 : ℝ) • x.1 = x.1
    module
  · change (3 : ℝ) * (-1 * x.2) - (2 : ℝ) * (-2 * x.2) = x.2
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma union_halfspaces : (lower : Set (E × ℝ)) ∪ upper = univ := by
  ext x
  simp only [lower, upper, mem_union, mem_ofPred_eq, mem_univ, iff_true]
  exact le_total _ _

omit [NormedSpace ℝ E] in
lemma isClosed_lower : IsClosed (lower : Set (E × ℝ)) :=
  isClosed_le continuous_snd continuous_const
omit [NormedSpace ℝ E] in
lemma isClosed_upper : IsClosed (upper : Set (E × ℝ)) :=
  isClosed_le continuous_const continuous_snd

def extend (f : (E × ℝ) → F) (x : E × ℝ) : F :=
  if x.2 ≤ 0 then f x else (3 : ℝ) • f (reflect 1 x) - (2 : ℝ) • f (reflect 2 x)

def extendDeriv (L : (E × ℝ) → (E × ℝ) →L[ℝ] F) (x : E × ℝ) :
    (E × ℝ) →L[ℝ] F :=
  if x.2 ≤ 0 then L x else
    (3 : ℝ) • (L (reflect 1 x)).comp (reflect 1) -
      (2 : ℝ) • (L (reflect 2 x)).comp (reflect 2)

lemma extend_eq_lower (f : (E × ℝ) → F) {x : E × ℝ} (hx : x ∈ lower) :
    extend f x = f x := ite_eq_left hx

lemma extend_eq_upper (f : (E × ℝ) → F) {x : E × ℝ} (hx : x ∈ upper) :
    extend f x = (3 : ℝ) • f (reflect 1 x) - (2 : ℝ) • f (reflect 2 x) := by
  by_cases h : x.2 ≤ 0
  · have hz : x.2 = 0 := le_antisymm h hx
    simp [extend, h, reflect_fixed hz]
    module
  · exact ite_eq_right h

lemma extendDeriv_eq_upper (L : (E × ℝ) → (E × ℝ) →L[ℝ] F)
    {x : E × ℝ} (hx : x ∈ upper) :
    extendDeriv L x = (3 : ℝ) • (L (reflect 1 x)).comp (reflect 1) -
      (2 : ℝ) • (L (reflect 2 x)).comp (reflect 2) := by
  by_cases h : x.2 ≤ 0
  · have hz : x.2 = 0 := le_antisymm h hx
    simp [extendDeriv, h, reflect_fixed hz, reflect_combination]
  · exact ite_eq_right h

lemma hasFDerivWithinAt_upper (f : (E × ℝ) → F)
    (L : (E × ℝ) → (E × ℝ) →L[ℝ] F) {x : E × ℝ}
    (hx : x ∈ upper)
    (h1 : HasFDerivWithinAt f (L (reflect 1 x)) lower (reflect 1 x))
    (h2 : HasFDerivWithinAt f (L (reflect 2 x)) lower (reflect 2 x)) :
    HasFDerivWithinAt (extend f) (extendDeriv L x) upper x := by
  have hr (a : ℝ) (ha : 0 ≤ a) : MapsTo (reflect a) (upper : Set (E × ℝ)) lower := by
    intro y hy
    change -a * y.2 ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hy
  rw [extendDeriv_eq_upper L hx]
  exact (((h1.comp x (reflect (E := E) 1).hasFDerivAt.hasFDerivWithinAt (hr 1 (by norm_num))).const_smul (3 : ℝ)).sub
    ((h2.comp x (reflect (E := E) 2).hasFDerivAt.hasFDerivWithinAt (hr 2 (by norm_num))).const_smul (2 : ℝ))).congr'
    (fun y hy => extend_eq_upper f hy) hx

lemma hasFDerivAt_boundary (f : (E × ℝ) → F)
    (L : (E × ℝ) →L[ℝ] F) {x : E × ℝ} (hx : x.2 = 0)
    (hf : HasFDerivWithinAt f L lower x) :
    HasFDerivAt (extend f) L x := by
  have hlo : HasFDerivWithinAt (extend f) L lower x :=
    hf.congr' (fun y hy => extend_eq_lower f hy) (by exact hx.le)
  have hup := hasFDerivWithinAt_upper f (fun _ => L) (x := x) (by exact hx.ge)
    (by simpa [reflect_fixed hx] using hf) (by simpa [reflect_fixed hx] using hf)
  simp only [extendDeriv, hx, le_refl, ↓reduceIte] at hup
  have hu := hlo.union hup
  rwa [union_halfspaces, hasFDerivWithinAt_univ] at hu

lemma continuous_extendDeriv
    (L : (E × ℝ) → (E × ℝ) →L[ℝ] F)
    (hL : ContinuousOn L lower) : Continuous (extendDeriv L) := by
  have hr (a : ℝ) (ha : 0 ≤ a) : MapsTo (reflect a) (upper : Set (E × ℝ)) lower := by
    intro y hy
    change -a * y.2 ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hy
  have hlo : ContinuousOn (extendDeriv L) lower :=
    hL.congr (fun y hy => by simp [extendDeriv, show y.2 ≤ 0 from hy])
  have hup : ContinuousOn (extendDeriv L) upper := by
    apply ContinuousOn.congr
      (((hL.comp (reflect 1).continuous.continuousOn (hr 1 (by norm_num))).clm_comp
        continuousOn_const).const_smul (3 : ℝ) |>.sub
      (((hL.comp (reflect 2).continuous.continuousOn (hr 2 (by norm_num))).clm_comp
        continuousOn_const).const_smul (2 : ℝ)))
    intro y hy
    exact extendDeriv_eq_upper L hy
  have hh := hlo.union_of_isClosed hup isClosed_lower isClosed_upper
  rwa [union_halfspaces, continuousOn_univ] at hh

lemma hasFDerivAt_extend (f : (E × ℝ) → F)
    (L : (E × ℝ) → (E × ℝ) →L[ℝ] F)
    (hf : ∀ x ∈ lower, HasFDerivWithinAt f (L x) lower x) (x : E × ℝ) :
    HasFDerivAt (extend f) (extendDeriv L x) x := by
  have hlo : HasFDerivWithinAt (extend f) (extendDeriv L x) lower x := by
    by_cases hx : x ∈ lower
    · simpa [extendDeriv, show x.2 ≤ 0 from hx] using
        (hf x hx).congr' (fun y hy => extend_eq_lower f hy) hx
    · apply HasFDerivWithinAt.of_notMem_closure
      rwa [isClosed_lower.closure_eq]
  have hup : HasFDerivWithinAt (extend f) (extendDeriv L x) upper x := by
    by_cases hx : x ∈ upper
    · apply hasFDerivWithinAt_upper f L hx
      · apply hf
        change -1 * x.2 ≤ 0
        nlinarith [show 0 ≤ x.2 from hx]
      · apply hf
        change -2 * x.2 ≤ 0
        nlinarith [show 0 ≤ x.2 from hx]
    · apply HasFDerivWithinAt.of_notMem_closure
      rwa [isClosed_upper.closure_eq]
  have hu := hlo.union hup
  rwa [union_halfspaces, hasFDerivWithinAt_univ] at hu

lemma contDiff_extend (f : (E × ℝ) → F)
    (L : (E × ℝ) → (E × ℝ) →L[ℝ] F)
    (hL : ContinuousOn L lower)
    (hf : ∀ x ∈ lower, HasFDerivWithinAt f (L x) lower x) :
    ContDiff ℝ 1 (extend f) := by
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨extendDeriv L, continuous_extendDeriv L hL, hasFDerivAt_extend f L hf⟩

/-- Neighborhood on which both reflected sample points remain in `U`. -/
def extensionRegion (U : Set (E × ℝ)) : Set (E × ℝ) :=
  U ∩ (reflect 1 ⁻¹' U) ∩ (reflect 2 ⁻¹' U)

lemma isOpen_extensionRegion {U : Set (E × ℝ)} (hU : IsOpen U) :
    IsOpen (extensionRegion U) :=
  (hU.inter (hU.preimage (reflect 1).continuous)).inter
    (hU.preimage (reflect 2).continuous)

lemma mem_extensionRegion_boundary {U : Set (E × ℝ)} {x : E × ℝ}
    (hx : x ∈ U) (hz : x.2 = 0) : x ∈ extensionRegion U := by
  exact ⟨⟨hx, by simpa [reflect_fixed hz] using hx⟩,
    by simpa [reflect_fixed hz] using hx⟩

lemma continuousOn_extendDeriv
    (L : (E × ℝ) → (E × ℝ) →L[ℝ] F) {U : Set (E × ℝ)}
    (hL : ContinuousOn L (lower ∩ U)) :
    ContinuousOn (extendDeriv L) (extensionRegion U) := by
  have hr (a : ℝ) (ha : 0 ≤ a) : MapsTo (reflect a) (upper : Set (E × ℝ)) lower := by
    intro y hy
    change -a * y.2 ≤ 0
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hy
  have hcomp : ContinuousOn
      (fun x => (3 : ℝ) • (L (reflect 1 x)).comp (reflect 1) -
        (2 : ℝ) • (L (reflect 2 x)).comp (reflect 2)) (extensionRegion U ∩ upper) := by
    have hm1 : MapsTo (reflect 1) (extensionRegion U ∩ upper) (lower ∩ U) := by
      intro y hy
      exact ⟨hr 1 (by norm_num) hy.2, hy.1.1.2⟩
    have hm2 : MapsTo (reflect 2) (extensionRegion U ∩ upper) (lower ∩ U) := by
      intro y hy
      exact ⟨hr 2 (by norm_num) hy.2, hy.1.2⟩
    exact (((hL.comp (reflect 1).continuous.continuousOn hm1).clm_comp
      continuousOn_const).const_smul (3 : ℝ)).sub
      (((hL.comp (reflect 2).continuous.continuousOn hm2).clm_comp
        continuousOn_const).const_smul (2 : ℝ))
  have hclosure : closure (lower : Set (E × ℝ))ᶜ ⊆ upper := by
    apply closure_minimal _ isClosed_upper
    intro y hy
    change ¬ y.2 ≤ 0 at hy
    exact le_of_lt (lt_of_not_ge hy)
  apply ContinuousOn.if
  · intro y hy
    change y ∈ extensionRegion U ∩ frontier (lower : Set (E × ℝ)) at hy
    have hlo : y ∈ lower := by
      simpa only [isClosed_lower.closure_eq] using frontier_subset_closure hy.2
    have hup : y ∈ upper := hclosure (frontier_subset_closure
      (by simpa only [frontier_compl] using hy.2))
    have hz : y.2 = 0 := le_antisymm hlo hup
    simp [reflect_fixed hz, reflect_combination]
  · apply hL.mono
    intro y hy
    change y ∈ extensionRegion U ∩ closure (lower : Set (E × ℝ)) at hy
    exact ⟨by simpa only [isClosed_lower.closure_eq] using hy.2, hy.1.1.1⟩
  · exact hcomp.mono (fun y hy => ⟨hy.1, hclosure hy.2⟩)

lemma hasFDerivAt_extend_local (f : (E × ℝ) → F)
    (L : (E × ℝ) → (E × ℝ) →L[ℝ] F) {U : Set (E × ℝ)} (hU : IsOpen U)
    (hf : ∀ x ∈ lower ∩ U, HasFDerivWithinAt f (L x) (lower ∩ U) x)
    {x : E × ℝ} (hx : x ∈ extensionRegion U) :
    HasFDerivAt (extend f) (extendDeriv L x) x := by
  have hd {y : E × ℝ} (hy : y ∈ lower ∩ U) :
      HasFDerivWithinAt f (L y) lower y :=
    (hasFDerivWithinAt_inter (hU.mem_nhds hy.2)).mp (hf y hy)
  have hlo : HasFDerivWithinAt (extend f) (extendDeriv L x) lower x := by
    by_cases hh : x ∈ lower
    · simpa [extendDeriv, show x.2 ≤ 0 from hh] using
        (hd ⟨hh, hx.1.1⟩).congr' (fun y hy => extend_eq_lower f hy) hh
    · apply HasFDerivWithinAt.of_notMem_closure
      rwa [isClosed_lower.closure_eq]
  have hup : HasFDerivWithinAt (extend f) (extendDeriv L x) upper x := by
    by_cases hh : x ∈ upper
    · apply hasFDerivWithinAt_upper f L hh
      · apply hd
        refine ⟨?_, hx.1.2⟩
        change -1 * x.2 ≤ 0
        nlinarith [show 0 ≤ x.2 from hh]
      · apply hd
        refine ⟨?_, hx.2⟩
        change -2 * x.2 ≤ 0
        nlinarith [show 0 ≤ x.2 from hh]
    · apply HasFDerivWithinAt.of_notMem_closure
      rwa [isClosed_upper.closure_eq]
  have hu := hlo.union hup
  rwa [union_halfspaces, hasFDerivWithinAt_univ] at hu

lemma contDiffOn_extend (f : (E × ℝ) → F)
    (L : (E × ℝ) → (E × ℝ) →L[ℝ] F) {U : Set (E × ℝ)} (hU : IsOpen U)
    (hL : ContinuousOn L (lower ∩ U))
    (hf : ∀ x ∈ lower ∩ U, HasFDerivWithinAt f (L x) (lower ∩ U) x) :
    ContDiffOn ℝ 1 (extend f) (extensionRegion U) := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (isOpen_extensionRegion hU).uniqueDiffOn (n := (0 : ℕ∞ω))).mpr
  refine ⟨by simp, extendDeriv L, contDiffOn_zero.mpr (continuousOn_extendDeriv L hL), ?_⟩
  intro x hx
  exact (hasFDerivAt_extend_local f L hU hf hx).hasFDerivWithinAt

lemma uniqueDiffOn_lower : UniqueDiffOn ℝ (lower : Set (E × ℝ)) := by
  simpa only [lower, univ_prod, Iic, Set.preimage, mem_ofPred_eq] using
    (uniqueDiffOn_univ (𝕜 := ℝ) (E := E)).prod (uniqueDiffOn_Iic (0 : ℝ))

lemma contDiffOn_extend_of_contDiffOn (f : (E × ℝ) → F)
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f (lower ∩ U)) :
    ContDiffOn ℝ 1 (extend f) (extensionRegion U) := by
  apply contDiffOn_extend f (fderivWithin ℝ f (lower ∩ U)) hU
  · exact hf.continuousOn_fderivWithin (uniqueDiffOn_lower.inter hU) (by rfl)
  · intro x hx
    exact (hf.differentiableOn_one x hx).hasFDerivWithinAt

lemma contDiffAt_extend_boundary (f : (E × ℝ) → F)
    {U : Set (E × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f (lower ∩ U)) {x : E × ℝ}
    (hx : x ∈ U) (hz : x.2 = 0) : ContDiffAt ℝ 1 (extend f) x :=
  (contDiffOn_extend_of_contDiffOn f hU hf).contDiffAt
    ((isOpen_extensionRegion hU).mem_nhds (mem_extensionRegion_boundary hx hz))

end VariationalNotes.Sobolev.NaturalBoundary.C1Reflection

noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace ContDiff Topology
namespace VariationalNotes.Sobolev.NaturalBoundary

/-- Pulling a one-sided C¹ field back to a convex open parameter patch
makes its continuous jet a genuine derivative on the closed patch. -/
theorem C1UpToClosure.exists_pullback_jet {d m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens (Domain d)} {P : Domain d → Gradient m d}
    (hP : C1UpToClosure Ω P) {s U : Set E}
    (hs : IsOpen s) (hconv : Convex ℝ s) (hU : IsOpen U) (hclU : closure s ⊆ U)
    {g : E → Domain d} (hg : ContDiffOn ℝ 1 g U)
    (hmap : MapsTo g s Ω) (hmapcl : MapsTo g (closure s) (closure (Ω : Set (Domain d)))) :
    ∃ J : E → (E →L[ℝ] Gradient m d),
      ContinuousOn J (closure s) ∧
      ∀ y ∈ closure s, HasFDerivWithinAt (P ∘ g) (J y) (closure s) y := by
  obtain ⟨hc, L, hL, hder⟩ := hP
  let J : E → (E →L[ℝ] Gradient m d) :=
    fun y => (L (g y)).comp (fderiv ℝ g y)
  have hcpg : ContinuousOn (P ∘ g) (closure s) :=
    hc.comp (hg.continuousOn.mono hclU) hmapcl
  have hJ : ContinuousOn J (closure s) :=
    (hL.comp (hg.continuousOn.mono hclU) hmapcl).clm_comp
      ((hg.fderiv_of_isOpen hU (m := 0) (by simp)).continuousOn.mono hclU)
  have hd (y : E) (hy : y ∈ s) : HasFDerivAt (P ∘ g) (J y) y :=
    (hder (g y) (hmap hy)).comp y
      ((hg.contDiffAt (hU.mem_nhds (hclU (subset_closure hy)))).differentiableAt one_ne_zero).hasFDerivAt
  have hdcl (y : E) (hy : y ∈ closure s) :
      HasFDerivWithinAt (P ∘ g) (J y) (closure s) y := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt) hconv hs
      (fun z hz => (hcpg z hz).mono subset_closure)
    have he : fderiv ℝ (P ∘ g) =ᶠ[𝓝[s] y] J := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hd z hz).fderiv
    exact ((hJ y hy).mono subset_closure).congr' he.symm
  exact ⟨J, hJ, hdcl⟩
end VariationalNotes.Sobolev.NaturalBoundary

noncomputable section
open Set TopologicalSpace Filter
open scoped ContDiff Topology
namespace VariationalNotes.Sobolev.NaturalBoundary

theorem closure_lowerHalfSpace {E : Type*} [TopologicalSpace E] :
    closure {y : E × ℝ | y.2 < 0} = {y : E × ℝ | y.2 ≤ 0} := by
  change closure (Prod.snd ⁻¹' Iio (0 : ℝ)) = Prod.snd ⁻¹' Iic (0 : ℝ)
  rw [← isOpenMap_snd.preimage_closure_eq_closure_preimage continuous_snd, closure_Iio]

/-- On a parameter ball inside the inverse chart, the one-sided flux has a
continuous jet which is differentiable within the closed half-ball. -/
theorem C1UpToClosure.exists_halfBall_pullback_jet {d m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens (Domain d)} {P : Domain d → Gradient m d}
    (hP : C1UpToClosure Ω P) {U : Set (E × ℝ)} (hU : IsOpen U)
    {a : E × ℝ} {r : ℝ} (hball : Metric.closedBall a r ⊆ U)
    {g : E × ℝ → Domain d} (hg : ContDiffOn ℝ 1 g U)
    (hmap : MapsTo g (U ∩ {y | y.2 < 0}) Ω)
    (hmapcl : MapsTo g (U ∩ {y | y.2 ≤ 0}) (closure (Ω : Set (Domain d)))) :
    ∃ J : E × ℝ → (E × ℝ →L[ℝ] Gradient m d),
      ContinuousOn J (Metric.ball a r ∩ {y | y.2 ≤ 0}) ∧
      ∀ y ∈ Metric.ball a r ∩ {y | y.2 ≤ 0},
        HasFDerivWithinAt (P ∘ g) (J y)
          (Metric.ball a r ∩ {y | y.2 ≤ 0}) y := by
  let s : Set (E × ℝ) := Metric.ball a r ∩ {y | y.2 < 0}
  have hs : IsOpen s := Metric.isOpen_ball.inter (isOpen_lt continuous_snd continuous_const)
  have hconv : Convex ℝ s := (convex_ball a r).inter
    ((convex_Iio (0 : ℝ)).linear_preimage (LinearMap.snd ℝ E ℝ))
  have hclball : closure s ⊆ Metric.closedBall a r :=
    (closure_mono inter_subset_left).trans (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall)
  have hclside : closure s ⊆ {y | y.2 ≤ 0} := by
    simpa only [closure_lowerHalfSpace] using closure_mono (s := s) (t := {y | y.2 < 0}) inter_subset_right
  have hclU : closure s ⊆ U := hclball.trans hball
  have hssub : Metric.ball a r ∩ {y | y.2 ≤ 0} ⊆ closure s := by
    rw [← closure_lowerHalfSpace]
    exact Metric.isOpen_ball.inter_closure
  obtain ⟨J, hJ, hder⟩ := hP.exists_pullback_jet hs hconv hU hclU hg
    (fun y hy => hmap ⟨hball (Metric.ball_subset_closedBall hy.1), hy.2⟩)
    (fun y hy => hmapcl ⟨hclU hy, hclside hy⟩)
  refine ⟨J, hJ.mono hssub, ?_⟩
  intro y hy
  exact (hder y (hssub hy)).mono hssub

end VariationalNotes.Sobolev.NaturalBoundary

namespace VariationalNotes.Sobolev.NaturalBoundary
open Set Filter TopologicalSpace
open scoped ContDiff Topology

/-- A one-sided C¹ field admits an ambient C¹ extension locally on each
boundary chart. Reflection is performed in flat coordinates and preserves
both tangential and normal first derivatives. -/
theorem C1UpToClosure.locally_extendible {d m : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) {P : Domain d → Gradient m d} (hP : C1UpToClosure Ω P) :
    D04.ClassicalRegularDomains.LocallyCrExtendible 1
      (closure (Ω : Set (Domain d))) P := by
  intro p hp
  by_cases hpi : p ∈ Ω
  · exact ⟨Ω, P, Ω.isOpen, hpi, hP.contDiffOn, fun _ _ => rfl⟩
  have hpb : p ∈ frontier (Ω : Set (Domain d)) := by
    rw [frontier, Ω.isOpen.interior_eq]
    exact ⟨hp, hpi⟩
  cases d with
  | zero => have := hΩ.dimension; omega
  | succ n =>
    obtain ⟨U, ρ, hpU, hρ⟩ := hΩ.defining p hpb
    obtain ⟨C⟩ := D04.RegularDomainGeometry.boundary_coordinates hρ ⟨hpb, hpU⟩
    obtain ⟨hX, hY, hpX, hFpY, hXU, _, hgmap, hleft, hright, _⟩ := C.inverse
    let L : Domain (n+1) ≃L[ℝ] Domain n × Domain 1 := EuclideanSpace.finAddEquivProd
    let e : Domain (n+1) ≃L[ℝ] Domain n × ℝ :=
      L.trans ((ContinuousLinearEquiv.refl ℝ (Domain n)).prodCongr
        (D04.RegularDomainGeometry.scalarCoordinate.trans (ContinuousLinearEquiv.neg ℝ)))
    have heval (z : Domain (n+1)) : (e z).2 = -z (Fin.last n) := by rfl
    have hlast (y : Domain n × ℝ) : e.symm y (Fin.last n) = -y.2 := by
      have he := congrArg Prod.snd (e.apply_symm_apply y)
      rw [heval] at he
      linarith
    let B : Set (Domain n × ℝ) := e.symm ⁻¹' C.Y
    have hB : IsOpen B := hY.preimage e.symm.continuous
    let a : Domain n × ℝ := e (C.F p)
    have haB : a ∈ B := by simpa only [B, a, mem_preimage, e.symm_apply_apply] using hFpY
    have ha0 : a.2 = 0 := by
      rw [heval, C.final_coordinate, (hρ.zero_level p hpU).mp hpb]
      simp
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hB.mem_nhds haB)
    let g : Domain n × ℝ → Domain (n+1) := C.g ∘ e.symm
    have hg : ContDiffOn ℝ 1 g B :=
      C.backward_regular.comp e.symm.contDiff.contDiffOn (fun _ hy => hy)
    have hρg (y : Domain n × ℝ) (hy : y ∈ B) : ρ (g y) = y.2 := by
      have he := C.final_coordinate (C.g (e.symm y))
      rw [hright hy, hlast] at he
      dsimp [g]
      linarith
    have hmap : MapsTo g (B ∩ {y | y.2 < 0}) Ω := by
      intro y hy
      apply (hρ.negative (g y) (hXU (hgmap hy.1))).mpr
      rw [hρg y hy.1]
      exact hy.2
    have hmapcl : MapsTo g (B ∩ {y | y.2 ≤ 0})
        (closure (Ω : Set (Domain (n+1)))) := by
      intro y hy
      apply (D04.RegularDomainGeometry.closure_iff_nonpos Ω.isOpen hρ
        (hXU (hgmap hy.1))).mpr
      change ρ (g y) ≤ 0
      rw [hρg y hy.1]
      exact hy.2
    obtain ⟨J, hJ, hder⟩ := hP.exists_halfBall_pullback_jet hB hball hg hmap hmapcl
    have hJ' : ContinuousOn J (C1Reflection.lower ∩ Metric.ball a r) := by
      simpa only [C1Reflection.lower, inter_comm] using hJ
    have hder' : ∀ y ∈ C1Reflection.lower ∩ Metric.ball a r,
        HasFDerivWithinAt (P ∘ g) (J y) (C1Reflection.lower ∩ Metric.ball a r) y := by
      simpa only [C1Reflection.lower, inter_comm] using hder
    let R := C1Reflection.extensionRegion (Metric.ball a r)
    have hR : IsOpen R := C1Reflection.isOpen_extensionRegion Metric.isOpen_ball
    have haR : a ∈ R := C1Reflection.mem_extensionRegion_boundary (Metric.mem_ball_self hr) ha0
    have hext : ContDiffOn ℝ 1 (C1Reflection.extend (P ∘ g)) R :=
      C1Reflection.contDiffOn_extend _ J Metric.isOpen_ball hJ' hder'
    let V : Set (Domain (n+1)) := C.X ∩ (fun x => e (C.F x)) ⁻¹' R
    have hV : IsOpen V :=
      (e.continuous.comp_continuousOn C.forward_regular.continuousOn).isOpen_inter_preimage hX hR
    refine ⟨V, (C1Reflection.extend (P ∘ g)) ∘ (fun x => e (C.F x)),
      hV, ⟨hpX, haR⟩, ?_, ?_⟩
    · exact hext.comp ((e.contDiff.comp_contDiffOn C.forward_regular).mono inter_subset_left)
        (fun _ hx => hx.2)
    · intro x hx
      have hxnonpos : ρ x ≤ 0 :=
        (D04.RegularDomainGeometry.closure_iff_nonpos Ω.isOpen hρ (hXU hx.2.1)).mp hx.1
      have hxlow : e (C.F x) ∈ C1Reflection.lower := by
        change (e (C.F x)).2 ≤ 0
        rw [heval, C.final_coordinate]
        simpa using hxnonpos
      change C1Reflection.extend (P ∘ g) (e (C.F x)) = P x
      rw [C1Reflection.extend_eq_lower _ hxlow]
      simp only [Function.comp_apply, g, e.symm_apply_apply, hleft hx.2.1]

/-- A bounded regular domain turns the local one-sided reflection extensions
into a single global C¹ extension without changing the flux on the closure. -/
theorem C1UpToClosure.exists_extension {d m : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) {P : Domain d → Gradient m d} (hP : C1UpToClosure Ω P) :
    ∃ Q : Domain d → Gradient m d,
      ContDiff ℝ 1 Q ∧ EqOn Q P (closure (Ω : Set (Domain d))) := by
  exact D04.ClassicalRegularDomains.closure_extension 1 (by simp) hΩ P
    (hP.locally_extendible hΩ)

end VariationalNotes.Sobolev.NaturalBoundary

noncomputable section
open Set Filter MeasureTheory Topology
open scoped BigOperators ContDiff
namespace VariationalNotes.Sobolev.NaturalBoundary.ChartDensity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model
open Specs.D04.C15.DirectedSubstitution.Model
open Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model

lemma proper_coefficient_bridge {k : ℕ} {S : Set (E k)} (f : S → ℝ)
    (hf : ProperIntegrable f) :
    MeasureTheory.Integrable (zeroExtension f) volume ∧
    coefficientIntegral f = ∫ x, zeroExtension f x := by
  obtain ⟨Q, hQ, _⟩ := hf.2
  obtain ⟨hi, hv⟩ := D04.DirectedSubstitution.proper_on_box hf Q hQ
  have he : (Specs.D04.C06.DarbouxIntegral.Model.carrier Q).indicator (zeroExtension f) = zeroExtension f := by
    funext x
    by_cases hx : x ∈ Specs.D04.C06.DarbouxIntegral.Model.carrier Q
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      symm
      apply Function.notMem_support.mp
      exact fun h => hx (D04.JordanRegions.encloses_subset hQ h)
  obtain ⟨_, hL, heq⟩ := D04.MeasureBridge.box_bridge (zeroExtension f) Q hi
  rw [he] at hL
  refine ⟨hL, hv.trans ?_⟩
  rw [heq, ← integral_indicator (D04.MeasureBridge.measurableSet_carrier Q), he]

lemma coefficient_nonneg {k : ℕ} {S : Set (E k)} (f : S → ℝ)
    (hf : ProperIntegrable f) (hn : ∀ x, 0 ≤ f x) : 0 ≤ coefficientIntegral f := by
  rw [(proper_coefficient_bridge f hf).2]
  apply integral_nonneg
  intro x
  change 0 ≤ zeroExtension f x
  by_cases hx : x ∈ S
  · simpa only [D04.JordanRegions.zeroExtension_apply f ⟨x,hx⟩] using hn ⟨x,hx⟩
  · simp [Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]

lemma coefficient_zero_of_nonneg {k : ℕ} {S : Set (E k)} (hS : IsOpen S)
    (f : S → ℝ) (hc : Continuous f) (hf : ProperIntegrable f)
    (hn : ∀ x, 0 ≤ f x) (hz : coefficientIntegral f = 0) : ∀ x, f x = 0 := by
  obtain ⟨hi, he⟩ := proper_coefficient_bridge f hf
  have hn' : ∀ x, 0 ≤ zeroExtension f x := by
    intro x
    by_cases hx : x ∈ S
    · simpa only [D04.JordanRegions.zeroExtension_apply f ⟨x,hx⟩] using hn ⟨x,hx⟩
    · simp [Specs.D04.C06.JordanRegions.Model.zeroExtension, hx]
  have hae : zeroExtension f =ᵐ[MeasureTheory.volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hn' hi).mp (he.symm.trans hz)
  have hc' : ContinuousOn (zeroExtension f) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hc using 1
    funext x
    exact D04.JordanRegions.zeroExtension_apply f x
  have hpoint := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) hS hc' continuousOn_const
  intro x
  simpa only [D04.JordanRegions.zeroExtension_apply f x, Pi.zero_apply] using hpoint x.property

lemma source_open_of_boundaryless {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 k M) (hB : intrinsicBoundary 1 k M = ∅)
    (c : EmbeddedChart 1 k n M) : IsOpen c.source := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  apply D04.EmbeddedChart.source_mem_nhds c hu
  intro hb
  have hmem := (D04.chart_intrinsicBoundary c hM.1 hM.2.1 u hu).mpr hb
  rw [hB] at hmem
  exact hmem

lemma nonnegative_density_zero {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 k M) (hB : intrinsicBoundary 1 k M = ∅)
    (ρ : M → ℝ) (hI : HasDensityIntegral (d := k) ρ 0)
    (hn : ∀ x, 0 ≤ ρ x) : ∀ x, ρ x = 0 := by
  obtain ⟨P⟩ := hI.2.2.1
  have hp (i : Fin P.count) : ∀ u, 0 ≤ localizedDensityCoefficient ρ (P.chart i) (P.weight i) u := by
    intro u
    exact mul_nonneg (P.partition.2.1 i (chartPoint (P.chart i) u))
      (mul_nonneg (hn _) (D04MetricDensity.chartDensity_positive (P.chart i) hM.1 u u.property).le)
  have hpi (i : Fin P.count) : 0 ≤ coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i)) :=
    coefficient_nonneg _ ((hI.2.2.2 P).1 i) (hp i)
  have hzero (i : Fin P.count) : coefficientIntegral (localizedDensityCoefficient ρ (P.chart i) (P.weight i)) = 0 := by
    have hsum : ∑ j, coefficientIntegral (localizedDensityCoefficient ρ (P.chart j) (P.weight j)) = 0 :=
      (hI.2.2.2 P).2
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hpi j)).mp hsum i (Finset.mem_univ _)
  have hpoint (i : Fin P.count) : ∀ u, localizedDensityCoefficient ρ (P.chart i) (P.weight i) u = 0 :=
    coefficient_zero_of_nonneg (source_open_of_boundaryless hM hB (P.chart i)) _
      (D04.ManifoldIntegral.density_coefficients_integrable hM ρ hI.1 P i).1
      ((hI.2.2.2 P).1 i) (hp i) (hzero i)
  intro x
  by_contra hx
  have hxs : x ∈ tsupport ρ := subset_tsupport ρ hx
  obtain ⟨V, _, hKV, hsum⟩ := P.partition.2.2.2.1
  have hpos : ∃ i, 0 < P.weight i x := by
    have hsumpos : 0 < ∑ i, P.weight i x := by rw [hsum x (hKV hxs)]; norm_num
    exact Finset.sum_pos_iff_of_nonneg (fun i _ => P.partition.2.1 i x) |>.mp hsumpos |>.imp fun i hi => hi.2
  obtain ⟨i, hi⟩ := hpos
  have hxa : (x : E n) ∈ (P.chart i).ambient :=
    (P.partition.2.2.1 i).2 (subset_tsupport (fun y : M => P.weight i y) hi.ne')
  let u : (P.chart i).source := ⟨(P.chart i).invFun x, (P.chart i).map_target ⟨x.property,hxa⟩⟩
  have hux : (P.chart i).toFun u = x := (P.chart i).right_inv x ⟨x.property,hxa⟩
  have hcx : chartPoint (P.chart i) u = x := Subtype.ext hux
  have hp0 := hpoint i u
  change P.weight i ((P.chart i).toFun u) * (ρ (chartPoint (P.chart i) u) * chartDensity (P.chart i) u) = 0 at hp0
  rw [hux, hcx] at hp0
  exact (mul_ne_zero hi.ne' (mul_ne_zero hx
    (D04MetricDensity.chartDensity_positive (P.chart i) hM.1 u u.property).ne')) hp0

lemma density_value_eq_zero {k n : ℕ} {M : Set (E n)} (ρ : M → ℝ)
    {I : ℝ} (hI : HasDensityIntegral (d := k) ρ I) (hρ : ∀ x, ρ x = 0) : I = 0 := by
  obtain ⟨P⟩ := hI.2.2.1
  rw [← (hI.2.2.2 P).2]
  apply Finset.sum_eq_zero
  intro i _
  have he : localizedDensityCoefficient ρ (P.chart i) (P.weight i) = 0 := by
    funext u
    simp [localizedDensityCoefficient, densityCoefficient, hρ]
  rw [(proper_coefficient_bridge _ ((hI.2.2.2 P).1 i)).2, he]
  have hz : zeroExtension (0 : (P.chart i).source → ℝ) = 0 := by
    funext x
    simp [Specs.D04.C06.JordanRegions.Model.zeroExtension]
  rw [hz]
  simp

lemma ambient_smooth_tests_detect {k n m : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold 1 k M) (hB : intrinsicBoundary 1 k M = ∅)
    (g : M → E m) (hg : Continuous g)
    (htest : ∀ φ : E n → E m, ContDiff ℝ ∞ φ →
      HasDensityIntegral (d := k) (fun x => inner ℝ (g x) (φ x)) 0) :
    ∀ p, g p = 0 := by
  intro p
  by_contra hp
  have hpos : 0 < inner ℝ (g p) (g p) := real_inner_self_pos.mpr hp
  have ho : IsOpen {x : M | 0 < inner ℝ (g x) (g p)} :=
    isOpen_lt continuous_const (hg.inner continuous_const)
  obtain ⟨O, hO, hEq⟩ := isOpen_induced_iff.mp ho
  have hpO : (p : E n) ∈ O := by
    change p ∈ (Subtype.val ⁻¹' O : Set M)
    rw [hEq]
    exact hpos
  obtain ⟨χ, hχsm, _, hχrange, ⟨W, hW, hpW, hχone⟩, _, hχsupp⟩ :=
    D04.EuclideanSmoothCutoffs.exists_smooth_cutoff
      {(p : E n)} O isCompact_singleton hO (singleton_subset_iff.mpr hpO)
  let φ : E n → E m := fun x => χ x • g p
  have hi := htest φ (hχsm.smul contDiff_const)
  have hn : ∀ x : M, 0 ≤ inner ℝ (g x) (φ x) := by
    intro x
    change 0 ≤ inner ℝ (g x) (χ x • g p)
    rw [inner_smul_right]
    by_cases hz : χ x = 0
    · simp [hz]
    · have hxO : (x : E n) ∈ O := hχsupp (subset_tsupport χ hz)
      have hxpos : 0 < inner ℝ (g x) (g p) := by
        have hx : x ∈ (Subtype.val ⁻¹' O : Set M) := hxO
        rw [hEq] at hx
        exact hx
      exact mul_nonneg (hχrange x).1 hxpos.le
  have hz := nonnegative_density_zero hM hB _ hi hn p
  have hχp : χ p = 1 := hχone (hpW (mem_singleton _))
  change inner ℝ (g p) (χ p • g p) = 0 at hz
  rw [hχp, one_smul] at hz
  exact hpos.ne' hz

end VariationalNotes.Sobolev.NaturalBoundary.ChartDensity

noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped InnerProductSpace ContDiff Topology
namespace VariationalNotes.Sobolev.NaturalBoundary
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model

lemma divergence_congr_on {d m : ℕ} (Ω : Opens (Domain d))
    {P Q : Domain d → Gradient m d} (hPQ : EqOn P Q Ω) :
    EqOn (NaturalBoundary.divergence P) (NaturalBoundary.divergence Q) Ω := by
  intro x hx
  apply PiLp.ext
  intro i
  change (∑ j, fderiv ℝ (fun y => P y (i,j)) x (P102.U4.coordinateVector d j)) = _
  apply Finset.sum_congr rfl
  intro j _
  have h : (fun y => P y (i,j)) =ᶠ[𝓝 x] (fun y => Q y (i,j)) := by
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    rw [hPQ hy]
  rw [h.fderiv_eq]

lemma density_extension_congr {d m : ℕ} (Ω : Opens (Domain d))
    {P Q : Domain d → Gradient m d}
    (hPQ : EqOn P Q (closure (Ω : Set (Domain d)))) (φ : Domain d → Vector m) :
    density (NaturalBoundary.divergence P) P φ =ᵐ[domainMeasure Ω]
      density (NaturalBoundary.divergence Q) Q φ := by
  have hd := divergence_congr_on Ω (hPQ.mono subset_closure)
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  simp only [density, hd hx, hPQ (subset_closure hx)]

lemma normalFlux_extension_congr {d m : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) {P Q : Domain d → Gradient m d}
    (hPQ : EqOn P Q (closure (Ω : Set (Domain d)))) :
    NaturalBoundary.normalFlux hΩ P = NaturalBoundary.normalFlux hΩ Q := by
  funext x
  simp only [NaturalBoundary.normalFlux, hPQ (frontier_subset_closure x.property)]

lemma frontier_boundaryless {d : ℕ} {Ω : Opens (Domain d)}
    (hΩ : RegularDomain Ω) :
    IsEmbeddedManifold 1 (d-1) (frontier (Ω : Set (Domain d))) ∧
      intrinsicBoundary 1 (d-1) (frontier (Ω : Set (Domain d))) = ∅ := by
  cases d with
  | zero => have := hΩ.dimension; omega
  | succ d =>
    obtain ⟨_, hM⟩ := D04.RegularDomainGeometry.closure_manifold hΩ
    have hb := D04.RegularDomainGeometry.intrinsic_boundary hΩ
    have h := D04.boundaryless_iff.mp (D04.intrinsic_boundary_manifold hM)
    simpa only [hb, Nat.add_sub_cancel] using h

lemma natural_boundary_equivalence_of_chart_green
    (hgreen : ∀ {d m : ℕ} (Ω : Opens (Domain d)) (hΩ : RegularDomain Ω)
      (P : Domain d → Gradient m d), C1UpToClosure Ω P →
      ∀ φ : Domain d → Vector m, SmoothNearClosure Ω φ →
        HasDensityIntegral (d := d-1) (fun x =>
          ⟪NaturalBoundary.normalFlux hΩ P x, φ x⟫_ℝ)
          (∫ x, density (NaturalBoundary.divergence P) P φ x ∂domainMeasure Ω)) :
    Expected.NaturalBoundaryEquivalence := by
  intro d m Ω _hm hΩ A P hA hP
  constructor
  · intro hs
    have hi := interior_equation Ω A P hA hP hs
    refine ⟨hi, ?_⟩
    obtain ⟨hM,hB⟩ := frontier_boundaryless hΩ
    apply ChartDensity.ambient_smooth_tests_detect hM hB
      (NaturalBoundary.normalFlux hΩ P) (continuous_normalFlux hΩ hP.1)
    intro φ hφ
    have hφnear : SmoothNearClosure Ω φ :=
      ⟨univ,isOpen_univ,subset_univ _,hφ.contDiffOn⟩
    have hG := hgreen Ω hΩ P hP φ hφnear
    have hz : (∫ x, density (NaturalBoundary.divergence P) P φ x ∂domainMeasure Ω) = 0 := by
      rw [← integral_congr_ae (density_congr_on Ω P φ hi)]
      exact (hs φ hφnear).2
    rwa [hz] at hG
  · rintro ⟨hi,hn⟩ φ hφ
    have hG := hgreen Ω hΩ P hP φ hφ
    have hz := ChartDensity.density_value_eq_zero _ hG (by
      intro x
      simp [hn x])
    have he := density_congr_on Ω P φ hi
    refine ⟨(integrable_green_density hΩ hP hφ).congr he.symm, ?_⟩
    rw [integral_congr_ae he]
    exact hz
end VariationalNotes.Sobolev.NaturalBoundary

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ContDiff InnerProductSpace
namespace VariationalNotes.Sobolev.NaturalBoundary.ProductGauss
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open VariationalNotes.Sobolev VariationalNotes.Sobolev.NaturalBoundary

abbrev pairedField {d m : ℕ} (P : Domain d → Gradient m d)
    (φ : Domain d → Vector m) : Domain d → Domain d :=
  fun x => WithLp.toLp 2 (fun j => ∑ i : Fin m, P x (i,j) * φ x i)

lemma contDiffOn_pairedField {d m : ℕ} {U : Set (Domain d)}
    {P : Domain d → Gradient m d} {φ : Domain d → Vector m}
    (hP : ContDiffOn ℝ 1 P U) (hφ : ContDiffOn ℝ 1 φ U) :
    ContDiffOn ℝ 1 (pairedField P φ) U := by
  apply (contDiffOn_piLp 2).mpr
  intro j
  change ContDiffOn ℝ 1 (fun x => ∑ i : Fin m, P x (i,j) * φ x i) U
  exact ContDiffOn.sum (fun i _ => ((contDiffOn_piLp 2).mp hP (i,j)).mul
    ((contDiffOn_piLp 2).mp hφ i))

lemma classical_divergence_coordinates {d : ℕ} {F : Domain d → Domain d}
    {x : Domain d} (hF : DifferentiableAt ℝ F x) :
    Specs.D04.C11.EuclideanVectorOperators.Model.divergence F x =
      ∑ j : Fin d, fderiv ℝ (fun y => F y j) x (P102.U4.coordinateVector d j) := by
  change D04.divergence F x = _
  rw [D04.divergence_eq_jacobian_trace]
  apply Finset.sum_congr rfl
  intro j _
  change Specs.D04.C01.EuclideanInterfaces.Model.matrixOfLinearMap
    (fderiv ℝ F x).toLinearMap j j = _
  change D04.matrixOfLinearMap (fderiv ℝ F x).toLinearMap j j = _
  rw [D04.matrixOfLinearMap_apply]
  have h := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j).hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => F y j) x = _ at h
  change (fderiv ℝ F x (P102.U4.coordinateVector d j)) j = _
  rw [h]
  rfl

lemma divergence_pairedField {d m : ℕ} {U : Set (Domain d)} (hU : IsOpen U)
    {P : Domain d → Gradient m d} {φ : Domain d → Vector m}
    (hP : ContDiffOn ℝ 1 P U) (hφ : ContDiffOn ℝ 1 φ U)
    {x : Domain d} (hx : x ∈ U) :
    Specs.D04.C11.EuclideanVectorOperators.Model.divergence (pairedField P φ) x =
      density (divergence P) P φ x := by
  have hdP := (hP.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdφ := (hφ.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdPe (i : Fin m) (j : Fin d) : DifferentiableAt ℝ (fun y => P y (i,j)) x :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m × Fin d => ℝ) (i,j)).hasFDerivAt.comp x hdP.hasFDerivAt).differentiableAt
  have hdφe (i : Fin m) : DifferentiableAt ℝ (fun y => φ y i) x :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt.comp x hdφ.hasFDerivAt).differentiableAt
  have hφe (i : Fin m) : fderiv ℝ (fun y => φ y i) x =
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).comp (fderiv ℝ φ x) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt.comp x hdφ.hasFDerivAt).fderiv
  rw [classical_divergence_coordinates
    (((contDiffOn_pairedField hP hφ).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero)]
  have hcoord (j : Fin d) :
      fderiv ℝ (fun y => pairedField P φ y j) x (P102.U4.coordinateVector d j) =
        ∑ i : Fin m, (fderiv ℝ (fun y => P y (i,j)) x (P102.U4.coordinateVector d j) * φ x i +
          P x (i,j) * (fderiv ℝ φ x (P102.U4.coordinateVector d j)) i) := by
    change fderiv ℝ (fun y => ∑ i : Fin m, P y (i,j) * φ y i) x _ = _
    rw [fderiv_fun_sum (A := fun i y => P y (i,j) * φ y i) (fun i _ => (hdPe i j).mul (hdφe i))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hmul := ((hdPe i j).hasFDerivAt.mul (hdφe i).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => P y (i,j) * φ y i) x = _ at hmul
    rw [hmul, hφe]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply, smul_eq_mul]
    ring
  simp_rw [hcoord]
  rw [Finset.sum_comm]
  unfold density
  rw [frobenius_eq_sum]
  simp only [divergence, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply,
    conj_trivial, jacobian]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma normalFlux_pairedField {n m : ℕ} {Ω : Opens (Domain (n+1))} (hΩ : RegularDomain Ω)
    (P : Domain (n+1) → Gradient m (n+1)) (φ : Domain (n+1) → Vector m)
    (x : frontier (Ω : Set (Domain (n+1)))) :
    Specs.D04.C12.GaussDivergenceTheorem.Model.normalFlux (pairedField P φ)
      (Specs.D04.C12.ClassicalRegularDomains.Model.outwardNormal hΩ) x =
      ⟪normalFlux hΩ P x, φ x⟫_ℝ := by
  simp only [Specs.D04.C12.GaussDivergenceTheorem.Model.normalFlux, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, pairedField, normalFlux, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma gauss_density {n m : ℕ} (Ω : Opens (Domain (n+1))) (hΩ : RegularDomain Ω)
    {P : Domain (n+1) → Gradient m (n+1)} {φ : Domain (n+1) → Vector m}
    (hP : ContDiff ℝ 1 P) (hφ : SmoothNearClosure Ω φ) :
    Specs.D04.C12.GaussDivergenceTheorem.Model.HasDensityIntegral (d := n)
      (fun x : frontier (Ω : Set (Domain (n+1))) => ⟪normalFlux hΩ P x, φ x⟫_ℝ)
      (∫ x, density (divergence P) P φ x ∂domainMeasure Ω) := by
  obtain ⟨U, hU, hclU, hφU⟩ := hφ
  have hF := contDiffOn_pairedField hP.contDiffOn (hφU.of_le (by simp))
  obtain ⟨hi, hI⟩ := D04.Gauss.gauss hΩ U (pairedField P φ)
    hU hclU ((D04.crOn_iff_contDiffOn 1 U _ hU).mpr hF)
  obtain ⟨_, heq⟩ := D04.MeasureBridge.region_bridge_ambient
    (Specs.D04.C11.EuclideanVectorOperators.Model.divergence (pairedField P φ)) Ω.isOpen.measurableSet hi
  have hvol : (∫ x in (Ω : Set (Domain (n+1))),
      Specs.D04.C11.EuclideanVectorOperators.Model.divergence (pairedField P φ) x) =
      ∫ x, density (divergence P) P φ x ∂domainMeasure Ω := by
    apply setIntegral_congr_fun Ω.isOpen.measurableSet
    intro x hx
    exact divergence_pairedField hU hP.contDiffOn (hφU.of_le (by simp)) (hclU (subset_closure hx))
  change Specs.D04.C06.JordanRegions.Model.regionIntegral _ = _ at heq
  rw [heq, hvol] at hI
  convert hI using 1
  funext x
  exact (normalFlux_pairedField hΩ P φ x).symm
end VariationalNotes.Sobolev.NaturalBoundary.ProductGauss

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace ContDiff Topology
namespace VariationalNotes.Sobolev.NaturalBoundary
open Specs.D04.C12.GaussDivergenceTheorem.Model

lemma chart_green_identity {d m : ℕ} (Ω : Opens (Domain d)) (hΩ : RegularDomain Ω)
    (P : Domain d → Gradient m d) (hP : C1UpToClosure Ω P)
    (φ : Domain d → Vector m) (hφ : SmoothNearClosure Ω φ) :
    HasDensityIntegral (d := d-1) (fun x =>
      ⟪NaturalBoundary.normalFlux hΩ P x, φ x⟫_ℝ)
      (∫ x, density (NaturalBoundary.divergence P) P φ x ∂domainMeasure Ω) := by
  obtain ⟨Q,hQ,hQP⟩ := hP.exists_extension hΩ
  cases d with
  | zero => have := hΩ.dimension; omega
  | succ n =>
    have hG := ProductGauss.gauss_density Ω hΩ hQ hφ
    have hvol := integral_congr_ae (density_extension_congr Ω hQP φ)
    have hnormal := normalFlux_extension_congr hΩ hQP
    rw [hvol, hnormal] at hG
    exact hG

/-- Stationarity for all ambient smooth tests is equivalent to the interior
equation and the vanishing outward normal flux, with the original one-sided
C¹ regularity on the flux. -/
theorem natural_boundary_equivalence : Expected.NaturalBoundaryEquivalence :=
  natural_boundary_equivalence_of_chart_green chart_green_identity

end VariationalNotes.Sobolev.NaturalBoundary
