import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellsChainsAndIntegrals
import MathGenome.Internal.MultivariableAnalysis.D04.C13.PullbackCalculus
import MathGenome.Internal.MultivariableAnalysis.D04.C06.ExceptionalSets
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped BigOperators Classical ContDiff
namespace D04.Cells
abbrev cubeBox := Specs.D04.C15.CellsChainsAndIntegrals.Model.cubeBox
abbrev cube := Specs.D04.C15.CellsChainsAndIntegrals.Model.cube
abbrev Cell := Specs.D04.C15.CellsChainsAndIntegrals.Model.Cell
abbrev cellExtension := @Specs.D04.C15.CellsChainsAndIntegrals.Model.cellExtension
abbrev extensionDomain := @Specs.D04.C15.CellsChainsAndIntegrals.Model.extensionDomain
abbrev faceInsertion := @Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion
abbrev cellFace := @Specs.D04.C15.CellsChainsAndIntegrals.Model.cellFace
abbrev cellCoefficient := @Specs.D04.C15.CellsChainsAndIntegrals.Model.cellCoefficient
abbrev cellIntegral := @Specs.D04.C15.CellsChainsAndIntegrals.Model.cellIntegral
abbrev Chain := @Specs.D04.C15.CellsChainsAndIntegrals.Model.Chain
abbrev chainIntegral := @Specs.D04.C15.CellsChainsAndIntegrals.Model.chainIntegral
abbrev cellBoundary := @Specs.D04.C15.CellsChainsAndIntegrals.Model.cellBoundary
abbrev chainBoundarySucc := @Specs.D04.C15.CellsChainsAndIntegrals.Model.chainBoundarySucc
abbrev chainBoundary := @Specs.D04.C15.CellsChainsAndIntegrals.Model.chainBoundary
abbrev pointCell := Specs.D04.C15.CellsChainsAndIntegrals.Model.pointCell
open Specs.D04.C15.CellsChainsAndIntegrals.Model (extension_spec)

@[simp] theorem mem_cube {k : ℕ} (x : E k) : x ∈ cube k ↔ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := Iff.rfl
@[simp] theorem zero_mem_cube (k : ℕ) : (0 : E k) ∈ cube k := by
  intro i
  exact ⟨le_rfl, zero_le_one⟩

@[ext] theorem cell_ext {r k n} {O : Set (E n)} {c d : Cell r k O}
    (h : ∀ x, c.toFun x = d.toFun x) : c = d := by
  cases c
  cases d
  congr
  exact funext h

theorem extension_on_cube {r k n} {O : Set (E n)} (c : Cell r k O) (x : cube k) :
    cellExtension c x = (c.toFun x).val := (extension_spec c).2.2.2 x

theorem extension_C1 {r k n} {O : Set (E n)} (c : Cell r k O) :
    ContDiffOn ℝ 1 (cellExtension c) (extensionDomain c) :=
  (extension_spec c).2.2.1.of_le (by exact_mod_cast c.positive)

theorem cellCoefficient_continuous {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega) :
    ContinuousOn (cellCoefficient c omega) (cube k) := by
  have hf : ContinuousOn (cellExtension c) (cube k) :=
    (extension_C1 c).continuousOn.mono (extension_spec c).2.1
  have hmap : MapsTo (cellExtension c) (cube k) O := by
    intro x hx
    rw [extension_on_cube c ⟨x,hx⟩]
    exact (c.toFun ⟨x,hx⟩).property
  have hd : ContinuousOn (totalDerivative (cellExtension c)) (cube k) :=
    ((extension_C1 c).continuousOn_fderiv_of_isOpen (extension_spec c).1 le_rfl).mono
      (extension_spec c).2.1
  change ContinuousOn (fun x => omega (cellExtension c x)
    (fun j => totalDerivative (cellExtension c) x (standardBasis k j))) (cube k)
  simp_rw [formField_evaluation]
  apply continuousOn_finsetSum
  intro I _
  apply ContinuousOn.mul
  · exact (h.2 I).comp hf hmap
  · have hv : ∀ j : Fin k, CrOn 0 (extensionDomain c)
        (fun x => totalDerivative (cellExtension c) x (standardBasis k j)) :=
        fun j => ((extension_C1 c).continuousOn_fderiv_of_isOpen
          (extension_spec c).1 le_rfl).clm_apply continuousOn_const
    exact (crOn_multilinear 0 k (fun _ => E n) (dx (standardBasis n) I).toMultilinearMap
      (extensionDomain c) _ (extension_spec c).1 hv).mono (extension_spec c).2.1

theorem cellCoefficient_integrable {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega) :
    Darboux.Integrable (cellCoefficient c omega) (cubeBox k) := by
  cases k with
  | zero => exact (Darboux.zero_dimension _ _).2.1
  | succ k =>
      exact ExceptionalSets.integrable_continuous (Nat.succ_pos _) _ _
        (cellCoefficient_continuous c omega h)

theorem cellIntegral_eq_riemann {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega) :
    cellIntegral c omega = Darboux.integral (cellCoefficient c omega) (cubeBox k)
      (cellCoefficient_integrable c omega h) := rfl

@[simp] theorem faceInsertion_same {k} (i : Fin (k+1)) (ε : Bool) (x : E k) :
    faceInsertion i ε x i = if ε then 1 else 0 := by
  change Fin.insertNth (α := fun _ => ℝ) i _ _ i = _
  exact Fin.insertNth_apply_same _ _ _
@[simp] theorem faceInsertion_other {k} (i : Fin (k+1)) (ε : Bool) (x : E k) (j : Fin k) :
    faceInsertion i ε x (i.succAbove j) = x j := by
  change Fin.insertNth (α := fun _ => ℝ) i _ _ (i.succAbove j) = _
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem cellFace_apply {r k n} {O : Set (E n)} (c : Cell r (k+1) O)
    (i : Fin (k+1)) (ε : Bool) (x : cube k) :
    (cellFace c i ε).toFun x = c.toFun
      ⟨faceInsertion i ε x, Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i ε x.property⟩ := rfl

@[simp] theorem chainIntegral_single {r k n} {O : Set (E n)} (omega : FormField n k)
    (c : Cell r k O) (a : ℤ) :
    chainIntegral omega (Finsupp.single c a) = a • cellIntegral c omega := by
  simp [chainIntegral, Specs.D04.C15.CellsChainsAndIntegrals.Model.chainIntegral]

theorem chainIntegral_sum {r k n} {O : Set (E n)} (omega : FormField n k)
    (C : Chain r k O) :
    chainIntegral omega C = C.sum (fun c a => a • cellIntegral c omega) := rfl

@[simp] theorem boundary_single {r k n} {O : Set (E n)} (c : Cell r (k+1) O) (a : ℤ) :
    chainBoundarySucc (Finsupp.single c a) = a • cellBoundary c := by
  simp [chainBoundarySucc, Specs.D04.C15.CellsChainsAndIntegrals.Model.chainBoundarySucc]

@[simp] theorem boundary_zero_chain {r n} {O : Set (E n)} (C : Chain r 0 O) :
    chainBoundary 0 C = 0 := rfl

theorem cellIntegral_zero_degree {r n} {O : Set (E n)} (c : Cell r 0 O) (f : E n → ℝ) :
    cellIntegral c (fun y => scalarCovector (f y)) = f (c.toFun ⟨0, zero_mem_cube 0⟩) := by
  change Darboux.lowerIntegral _ _ = _
  rw [(Darboux.zero_dimension _ _).2.2.1]
  change f (cellExtension c 0) = _
  rw [extension_on_cube c ⟨0, zero_mem_cube 0⟩]

theorem pointCell_inverse {r n} {O : Set (E n)} (c : Cell r 0 O) :
    pointCell r O c.open_target c.positive (c.toFun ⟨0, zero_mem_cube 0⟩) = c := by
  apply cell_ext
  intro x
  change c.toFun ⟨0, zero_mem_cube 0⟩ = c.toFun x
  congr 1
  exact Subsingleton.elim _ _

/-- Even at a corner of the cube the derivative of an extension is determined
by its values on the cube. This includes the zero-dimensional cube. -/
theorem cube_uniqueDiff (k : ℕ) : UniqueDiffOn ℝ (cube k) := by
  have he : cube k = (coordinates k).toContinuousLinearEquiv ⁻¹'
      (Set.pi univ (fun _ : Fin k => Icc (0 : ℝ) 1)) := by
    ext x
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_true_left]
    rfl
  rw [he]
  exact (coordinates k).toContinuousLinearEquiv.uniqueDiffOn_preimage_iff.mpr
    (UniqueDiffOn.univ_pi (fun _ => uniqueDiffOn_Icc zero_lt_one))

theorem extension_derivative_unique {r k n} {O : Set (E n)} (c : Cell r k O)
    (f : E k → E n) (U : Set (E k)) (hU : IsOpen U) (hsub : cube k ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (heq : ∀ x : cube k, f x = (c.toFun x).val)
    (x : cube k) : totalDerivative (cellExtension c) x = totalDerivative f x := by
  have hce : DifferentiableAt ℝ (cellExtension c) x :=
    ((extension_C1 c).differentiableOn (by norm_num)).differentiableAt
      ((extension_spec c).1.mem_nhds ((extension_spec c).2.1 x.property))
  have hfe : DifferentiableAt ℝ f x :=
    (hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds (hsub x.property))
  have he : EqOn (cellExtension c) f (cube k) :=
    fun y hy => (extension_on_cube c ⟨y,hy⟩).trans (heq ⟨y,hy⟩).symm
  change fderiv ℝ (cellExtension c) x = fderiv ℝ f x
  rw [← hce.fderivWithin (cube_uniqueDiff k x x.property),
    ← hfe.fderivWithin (cube_uniqueDiff k x x.property)]
  exact fderivWithin_congr he (he x.property)

theorem cellCoefficient_extension_independent {r k n} {O : Set (E n)} (c : Cell r k O)
    (f : E k → E n) (U : Set (E k)) (hU : IsOpen U) (hsub : cube k ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (heq : ∀ x : cube k, f x = (c.toFun x).val)
    (omega : FormField n k) (x : cube k) :
    cellCoefficient c omega x = pullback f omega x (fun j => standardBasis k j) := by
  change omega (cellExtension c x) (fun j => totalDerivative (cellExtension c) x (standardBasis k j)) =
    omega (f x) (fun j => totalDerivative f x (standardBasis k j))
  rw [extension_derivative_unique c f U hU hsub hf heq x]
  rw [extension_on_cube c x, heq x]

/-- The scalar in the integral is exactly the coefficient of the normalized
coordinate volume form, not a metric density or an absolute Jacobian. -/
theorem cell_pullback_top {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (x : E k) :
    pullback (cellExtension c) omega x = cellCoefficient c omega x • volumeForm k := by
  have hv : volumeForm k = (standardBasis k).det := by
    ext v
    rw [volumeForm_apply, Module.Basis.det_apply]
    congr 1
  rw [hv]
  exact (pullback (cellExtension c) omega x).eq_smul_basis_det (standardBasis k)

theorem lowerIntegral_congr {k : ℕ} {Q : Darboux.Box k} {f g : E k → ℝ}
    (h : EqOn f g (Darboux.carrier Q)) : Darboux.lowerIntegral f Q = Darboux.lowerIntegral g Q := by
  have hi (P : Darboux.Grid Q) (j : Darboux.CellIndex P) :
      f '' Darboux.cell P j = g '' Darboux.cell P j :=
    Set.image_congr (fun x hx => h (Darboux.cell_subset P j hx))
  unfold Darboux.lowerIntegral Specs.D04.C06.DarbouxIntegral.Model.lowerIntegral
  congr 2
  funext P
  unfold Specs.D04.C06.DarbouxIntegral.Model.lowerSum
  apply Finset.sum_congr rfl
  intro j _
  simp only [Specs.D04.C06.DarbouxIntegral.Model.cellInfimum, hi]

theorem cellIntegral_extension_independent {r k n} {O : Set (E n)} (c : Cell r k O)
    (f : E k → E n) (U : Set (E k)) (hU : IsOpen U) (hsub : cube k ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (heq : ∀ x : cube k, f x = (c.toFun x).val)
    (omega : FormField n k) :
    cellIntegral c omega = Darboux.lowerIntegral
      (fun x => pullback f omega x (fun j => standardBasis k j)) (cubeBox k) := by
  apply lowerIntegral_congr
  intro x hx
  exact cellCoefficient_extension_independent c f U hU hsub hf heq omega ⟨x,hx⟩

/-- Existence and the value of the proper Riemann integral are simultaneous. -/
theorem cellIntegral_exists {r k n} {O : Set (E n)} (c : Cell r k O)
    (omega : FormField n k) (h : IsCrForm (some 0) O omega) :
    ∃ hi : Darboux.Integrable (cellCoefficient c omega) (cubeBox k),
      cellIntegral c omega = Darboux.integral (cellCoefficient c omega) (cubeBox k) hi :=
  ⟨cellCoefficient_integrable c omega h, rfl⟩

theorem chainIntegral_add {r k n} {O : Set (E n)} (omega : FormField n k)
    (C D : Chain r k O) : chainIntegral omega (C + D) = chainIntegral omega C + chainIntegral omega D :=
  (chainIntegral omega).map_add C D

theorem chainBoundary_add {r k n} {O : Set (E n)} (C D : Chain r k O) :
    chainBoundary k (C + D) = chainBoundary k C + chainBoundary k D :=
  (chainBoundary k).map_add C D

/-- The extension can also be taken to have values in the original open target. -/
theorem extension_into_target {r k n} {O : Set (E n)} (c : Cell r k O) :
    ∃ U : Set (E k), IsOpen U ∧ cube k ⊆ U ∧
      ContDiffOn ℝ (r : ℕ∞ω) (cellExtension c) U ∧ MapsTo (cellExtension c) U O := by
  refine ⟨extensionDomain c ∩ cellExtension c ⁻¹' O,
    (extension_C1 c).continuousOn.isOpen_inter_preimage (extension_spec c).1 c.open_target,
    ?_, (extension_spec c).2.2.1.mono inter_subset_left, fun _ hx => hx.2⟩
  intro x hx
  refine ⟨(extension_spec c).2.1 hx, ?_⟩
  change cellExtension c x ∈ O
  rw [extension_on_cube c ⟨x,hx⟩]
  exact (c.toFun ⟨x,hx⟩).property

end D04.Cells
