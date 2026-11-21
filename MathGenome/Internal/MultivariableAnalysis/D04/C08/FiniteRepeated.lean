import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.FiniteRepeated
import MathGenome.Internal.MultivariableAnalysis.D04.C08.ProperDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C03.FactorialBridge
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04.FiniteRepeated
open JordanRegions ProperContinuity ProperDerivative

/-- A coordinate identification used only to transport the already constructed
Riemann integral to other finite-dimensional targets. -/
private def coordinatesEquiv (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] : Y ≃L[ℝ] E (Module.finrank ℝ Y) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [E])

private def integral {n : ℕ} {S : Set (E n)} {Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (f : S → Y) : Y :=
  (coordinatesEquiv Y).symm (vectorRegionIntegral (fun x => coordinatesEquiv Y (f x)))

private def Integrable {n : ℕ} {S : Set (E n)} {Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (f : S → Y) : Prop :=
  VectorRegionIntegrable (fun x => coordinatesEquiv Y (f x))

private lemma integral_linear {n : ℕ} {S : Set (E n)} {Y Z : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (f : S → Y) (L : Y →L[ℝ] Z) (hf : Integrable f) :
    Integrable (fun x => L (f x)) ∧ integral (fun x => L (f x)) = L (integral f) := by
  let A := ((coordinatesEquiv Z).toContinuousLinearMap.comp L).comp
    (coordinatesEquiv Y).symm.toContinuousLinearMap
  have h := vector_integral_linear (fun x => coordinatesEquiv Y (f x)) A.toLinearMap hf
  have he : (fun x => A (coordinatesEquiv Y (f x))) =
      (fun x => coordinatesEquiv Z (L (f x))) := by
    funext x
    simp [A]
  change VectorRegionIntegrable (fun x => A (coordinatesEquiv Y (f x))) ∧
    vectorRegionIntegral (fun x => A (coordinatesEquiv Y (f x))) =
      A (vectorRegionIntegral (fun x => coordinatesEquiv Y (f x))) at h
  rw [he] at h
  refine ⟨h.1, ?_⟩
  unfold integral
  rw [h.2]
  simp [A]

private lemma integral_euclidean {n k : ℕ} {S : Set (E n)}
    (f : S → E k) (hf : Integrable f) :
    VectorRegionIntegrable f ∧ integral f = vectorRegionIntegral f := by
  have h := vector_integral_linear (fun x => coordinatesEquiv (E k) (f x))
    (coordinatesEquiv (E k)).symm.toLinearMap hf
  change VectorRegionIntegrable (fun x => (coordinatesEquiv (E k)).symm
    (coordinatesEquiv (E k) (f x))) ∧ _ at h
  simpa [integral] using h.imp_right Eq.symm

private lemma integral_continuous {n m : ℕ} {S : Set (E n)} {P : Set (E m)}
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (hS : Jordan S) (f : closure S → E m → Y)
    (hf : Continuous (fun z : closure S × P => f z.1 z.2)) :
    (∀ p ∈ P, Integrable (fun x : S => f ⟨x, subset_closure x.property⟩ p)) ∧
    ContinuousOn (fun p => integral (fun x : S => f ⟨x, subset_closure x.property⟩ p)) P := by
  have h := joint_continuity hS (fun z : closure S × P => coordinatesEquiv Y (f z.1 z.2))
    ((coordinatesEquiv Y).continuous.comp hf)
  refine ⟨fun p hp => h.1 ⟨p,hp⟩, ?_⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact (coordinatesEquiv Y).symm.continuous.comp h.2

private lemma integral_hasFDerivAt {n m : ℕ} {S : Set (E n)} {P : Set (E m)}
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (hS : Jordan S) (hP : IsOpen P) (f : closure S → E m → Y)
    (A : closure S → E m → E m →L[ℝ] Y)
    (hf : Continuous (fun z : closure S × P => f z.1 z.2))
    (hA : Continuous (fun z : closure S × P => A z.1 z.2))
    (hd : ∀ x : S, ∀ p ∈ P, HasFDerivAt (f ⟨x, subset_closure x.property⟩)
      (A ⟨x, subset_closure x.property⟩ p) p) (p : E m) (hp : p ∈ P) :
    HasFDerivAt (fun q => integral (fun x : S => f ⟨x, subset_closure x.property⟩ q))
      (integral (fun x : S => A ⟨x, subset_closure x.property⟩ p)) p := by
  let e := coordinatesEquiv Y
  let B := fun x q => e.toContinuousLinearMap.comp (A x q)
  have hB : Continuous (fun z : closure S × P => B z.1 z.2) :=
    ((ContinuousLinearMap.compL ℝ (E m) Y (E (Module.finrank ℝ Y)))
      e.toContinuousLinearMap).continuous.comp hA
  have H := continuous_parameter_derivative hS hP
    (fun x q => e (f x q)) B (e.continuous.comp hf) hB
    (fun x q hq => e.hasFDerivAt.comp q (hd x q hq))
  have hD := e.symm.hasFDerivAt.comp p (H.2.2.2 p hp).1
  apply hD.congr_fderiv
  ext v
  have hAi := (integral_continuous hS A hA).1 p hp
  have he := integral_linear (fun x : S => A ⟨x, subset_closure x.property⟩ p)
    (ContinuousLinearMap.apply ℝ Y v) hAi
  have heq : integral (fun x : S => A ⟨x, subset_closure x.property⟩ p v) =
      (integral (fun x : S => A ⟨x, subset_closure x.property⟩ p)) v := he.2
  rw [← heq]
  change e.symm (operatorRegionIntegral (fun x : S => B ⟨x, subset_closure x.property⟩ p) v) =
    e.symm (vectorRegionIntegral (fun x : S => e (A ⟨x, subset_closure x.property⟩ p v)))
  congr 1
  have hi : OperatorRegionIntegrable (fun x : S => B ⟨x, subset_closure x.property⟩ p) := by
    refine ⟨jordan_bounded hS, fun i => ?_⟩
    exact (joint_continuity hS (fun z : closure S × P => B z.1 z.2 (standardBasis m i))
      (continuous_clm_apply.mp hB _)).1 ⟨p,hp⟩
  exact (integral_apply _ hi v).2

private instance tensorFiniteDimensional (m k j : ℕ) :
    FiniteDimensional ℝ (Differential (E m) (E k) j) :=
  FiniteDimensional.of_injective (differentialCoefficients j).toLinearMap
    differentialCoefficients_injective

/-- All finite orders, including the continuity case and the empty tuple. -/
theorem finite_repeated : Specs.D04.C08.FiniteRepeated.finite_repeatedType := by
  intro n m k S P hS hP r f T hex hcont hext
  let F := fun p => vectorRegionIntegral (fun x => f x p)
  let G : E m → FormalMultilinearSeries ℝ (E m) (E k) :=
    fun p j => integral (fun x : S => T j ⟨x, subset_closure x.property⟩ p)
  have hTi (j : ℕ) (hj : j ≤ r) (p : E m) (hp : p ∈ P) :
      Integrable (fun x : S => T j ⟨x, subset_closure x.property⟩ p) :=
    (integral_continuous hS (T j) (hcont j hj)).1 p hp
  have hcalc (j : ℕ) (hj : j ≤ r) (p : E m) (hp : p ∈ P) (v : Fin j → E m) :
      VectorRegionIntegrable (fun x => higherDifferential j (f x) p v) ∧
      G p j v = vectorRegionIntegral (fun x => higherDifferential j (f x) p v) := by
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E m) (E k) v
    have hl := integral_linear (fun x : S => T j ⟨x, subset_closure x.property⟩ p)
      L (hTi j hj p hp)
    have hv := integral_euclidean _ hl.1
    have he : (fun x : S => L (T j ⟨x, subset_closure x.property⟩ p)) =
        (fun x => higherDifferential j (f x) p v) := by
      funext x
      exact congrArg (fun A => A v) (hext j hj x p hp)
    rw [he] at hl hv
    exact ⟨hv.1, hl.2.symm.trans hv.2⟩
  have hzero (p : E m) (hp : p ∈ P) : (G p 0).curry0 = F p := by
    change G p 0 (fun _ => 0) = F p
    simpa [F, higherDifferential, Specs.D04.C03.HigherInterfaces.Model.higherDifferential]
      using (hcalc 0 (Nat.zero_le r) p hp (fun _ => 0)).2
  have hderiv (j : ℕ) (hj : j < r) (p : E m) (hp : p ∈ P) :
      HasFDerivAt (fun q => G q j) (G p (j+1)).curryLeft p := by
    let c := (differentialSuccEquiv (E m) (E k) j).symm.toContinuousLinearMap
    have hA : Continuous (fun z : closure S × P => c (T (j+1) z.1 z.2)) :=
      c.continuous.comp (hcont (j+1) (by omega))
    have hd (x : S) (q : E m) (hq : q ∈ P) :
        HasFDerivAt (T j ⟨x, subset_closure x.property⟩)
          (c (T (j+1) ⟨x, subset_closure x.property⟩ q)) q := by
      have h := timesDifferentiableAt_hasFDerivAt j P (f x) q
        (FactorialBridge.timesDifferentiableAt_of_le P (f x) q (hex x q hq) (by omega))
      have heq : c (higherDifferential (j+1) (f x) q) =
          c (T (j+1) ⟨x, subset_closure x.property⟩ q) :=
        congrArg c (hext (j+1) (by omega) x q hq).symm
      apply (h.congr_fderiv heq).congr_of_eventuallyEq
      filter_upwards [hP.mem_nhds hq] with u hu
      exact hext j (by omega) x u hu
    have hD := integral_hasFDerivAt hS hP (T j)
      (fun x q => c (T (j+1) x q)) (hcont j (by omega)) hA hd p hp
    have hL := integral_linear
      (Y := Differential (E m) (E k) (j+1))
      (Z := E m →L[ℝ] Differential (E m) (E k) j)
      (fun x : S => T (j+1) ⟨x, subset_closure x.property⟩ p)
      c (hTi (j+1) (by omega) p hp)
    exact hD.congr_fderiv hL.2
  have hseries : HasFTaylorSeriesUpToOn (r : ℕ∞ω) F G P := by
    refine ⟨hzero, ?_, ?_⟩
    · intro j hj p hp
      exact (hderiv j (by exact_mod_cast hj) p hp).hasFDerivWithinAt
    · intro j hj
      exact (integral_continuous hS (T j) (hcont j (by exact_mod_cast hj))).2
  have hCr : CrOn r P F := (crOn_iff_contDiffOn r P F hP).mpr hseries.contDiffOn
  have hG (j : ℕ) (hj : j ≤ r) (p : E m) (hp : p ∈ P) :
      G p j = higherDifferential j F p := by
    exact (hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hj)
      hP.uniqueDiffOn hp).trans (iteratedFDerivWithin_of_isOpen j hP hp)
  refine ⟨?_, hCr, ?_, ?_⟩
  · intro p hp
    exact (hcalc 0 (Nat.zero_le r) p hp (fun i => Fin.elim0 i)).1
  · intro j hj p hp v
    exact ⟨(hcalc j hj p hp v).1,
      (congrArg (fun A => A v) (hG j hj p hp)).symm.trans (hcalc j hj p hp v).2⟩
  · intro α hα p hp
    let j := multiIndexDegree α
    have hj : j ≤ r := hα
    have hF := FactorialBridge.timesDifferentiableAt_of_le P F p
      (crOn_timesDifferentiableAt r P F hP hCr p hp) hj
    have hx (x : S) := FactorialBridge.timesDifferentiableAt_of_le P (f x) p
      (hex x p hp) hj
    have hw : (multiIndexWord α).length = j := multiIndexWord_length α
    let v : Fin j → E m := fun i =>
      standardBasis m ((multiIndexWord α).get (Fin.cast hw.symm i))
    have hpart (g : E m → E k) (hg : TimesDifferentiableAt j P g p) :
        multiIndexPartial α g p = higherDifferential j g p v := by
      rw [← tensorMultiIndex_higherDifferential P g p hg α rfl]
      simp only [tensorMultiIndex, Specs.D04.C03.FactorialBridge.Model.tensorMultiIndex,
        dite_eq_left hw]
      rfl
    have he : (fun x => multiIndexPartial α (f x) p) =
        (fun x => higherDifferential j (f x) p v) := funext (fun x => hpart (f x) (hx x))
    change VectorRegionIntegrable (fun x => multiIndexPartial α (f x) p) ∧
      multiIndexPartial α F p = vectorRegionIntegral (fun x => multiIndexPartial α (f x) p)
    rw [he]
    exact ⟨(hcalc j hj p hp v).1, (hpart F hF).trans
      ((congrArg (fun A => A v) (hG j hj p hp)).symm.trans (hcalc j hj p hp v).2)⟩

end D04.FiniteRepeated
