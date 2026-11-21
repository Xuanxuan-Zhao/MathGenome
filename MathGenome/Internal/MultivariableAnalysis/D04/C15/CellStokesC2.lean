import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.CellStokesC2
import MathGenome.Internal.MultivariableAnalysis.D04.C15.BoundarySquaredAndFaceSigns
import MathGenome.Internal.MultivariableAnalysis.D04.C13.DifferentialIdentities
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxFubini
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped BigOperators Classical
namespace D04.Cells
open Specs.D04.C15.CellsChainsAndIntegrals.Model (extension_spec faceInsertion_contDiff)

/-- Restrict the chosen extension to an open neighborhood mapping into any
specified open neighborhood of the cell image. -/
theorem extension_into_neighborhood {r k n} {O : Set (E n)} (c : Cell r k O)
    (V : Set (E n)) (hV : IsOpen V)
    (hcV : ∀ x : cube k, (c.toFun x).val ∈ V) :
    ∃ U : Set (E k), IsOpen U ∧ cube k ⊆ U ∧
      ContDiffOn ℝ (r : WithTop ℕ∞) (cellExtension c) U ∧ MapsTo (cellExtension c) U V := by
  refine ⟨extensionDomain c ∩ cellExtension c ⁻¹' V,
    (extension_C1 c).continuousOn.isOpen_inter_preimage (extension_spec c).1 hV,
    ?_, (extension_spec c).2.2.1.mono inter_subset_left, fun _ hx => hx.2⟩
  intro x hx
  refine ⟨(extension_spec c).2.1 hx, ?_⟩
  change cellExtension c x ∈ V
  rw [extension_on_cube c ⟨x,hx⟩]
  exact hcV ⟨x,hx⟩

/-- Integrating over the formal boundary is exactly the alternating face sum. -/
theorem boundaryIntegral_eq_sum {r k n} {O : Set (E n)} (c : Cell r (k+1) O)
    (ω : FormField n k) :
    chainIntegral ω (cellBoundary c) =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
        (cellIntegral (cellFace c i true) ω - cellIntegral (cellFace c i false) ω) := by
  unfold cellBoundary Specs.D04.C15.CellsChainsAndIntegrals.Model.cellBoundary
  simp only [map_sum, map_zsmul, map_sub, chainIntegral_single, one_zsmul]
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The integrand in a face integral can be computed with the extension of
the original cell rather than the independently chosen face extension. -/
theorem cellFace_integral_pullback {r k n} {O : Set (E n)} (c : Cell r (k+1) O)
    (ω : FormField n k) (i : Fin (k+1)) (ε : Bool) :
    cellIntegral (cellFace c i ε) ω = Darboux.lowerIntegral
      (fun x => pullback (faceInsertion i ε) (pullback (cellExtension c) ω) x
        (fun j => standardBasis k j)) (cubeBox k) := by
  let U := faceInsertion i ε ⁻¹' extensionDomain c
  have hU : IsOpen U := (extension_spec c).1.preimage
    (faceInsertion_contDiff i ε).continuous
  have hcU : cube k ⊆ U := fun _ hx =>
    (extension_spec c).2.1 (Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i ε hx)
  have hf : ContDiffOn ℝ 1 (cellExtension c ∘ faceInsertion i ε) U :=
    (extension_C1 c).comp ((faceInsertion_contDiff i ε).of_le (by norm_num)).contDiffOn (fun _ hx => hx)
  rw [cellIntegral_extension_independent (cellFace c i ε)
    (cellExtension c ∘ faceInsertion i ε) U hU hcU hf (fun x => by
      exact extension_on_cube c
        ⟨faceInsertion i ε x, Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i ε x.property⟩)]
  apply lowerIntegral_congr
  intro x hx
  have he := pullback_comp U (extensionDomain c) univ
    (faceInsertion i ε) (cellExtension c) ω x (fun _ hy => hy)
    (fun _ _ => mem_univ _) (hcU hx)
    ((crOn_iff_contDiffOn 1 U (faceInsertion i ε) hU).mpr
      ((faceInsertion_contDiff i ε).of_le (by norm_num)).contDiffOn).1
    ((crOn_iff_contDiffOn 1 (extensionDomain c) (cellExtension c) (extension_spec c).1).mpr
      (extension_C1 c)).1
  exact congrArg (fun A => A (fun j => standardBasis k j)) he

/-- The C² naturality theorem identifies the bulk coefficient with the
exterior derivative of the C¹ pulled-back form on an actual neighborhood. -/
theorem cell_bulk_naturality {k n} {O : Set (E n)} (c : Cell 2 (k+1) O)
    (V : Set (E n)) (ω : FormField n k) (hω : IsCrForm (some 1) V ω)
    (hcV : ∀ x : cube (k+1), (c.toFun x).val ∈ V) :
    ∃ U : Set (E (k+1)), IsOpen U ∧ cube (k+1) ⊆ U ∧
      IsCrForm (some 1) U (pullback (cellExtension c) ω) ∧
      cellIntegral c (exteriorDerivative ω) = Darboux.lowerIntegral
        (fun x => exteriorDerivative (pullback (cellExtension c) ω) x
          (fun j => standardBasis (k+1) j)) (cubeBox (k+1)) := by
  obtain ⟨U,hU,hsub,hc,hmap⟩ := extension_into_neighborhood c V hω.1 hcV
  have hc' : CrOn 2 U (cellExtension c) :=
    (crOn_iff_contDiffOn 2 U (cellExtension c) hU).mpr hc
  refine ⟨U,hU,hsub,pullback_C1 U V _ _ hU hmap hc' hω, ?_⟩
  apply lowerIntegral_congr
  intro x hx
  exact (congrArg (fun A => A (fun j => standardBasis (k+1) j))
    (exteriorDerivative_pullback U V _ _ hU hmap hc' hω x (hsub hx))).symm

/-- Transport of degree also transports the ordered list of one-covectors. -/
theorem wedgeList_cast {n a b : ℕ} (h : a = b)
    (f : Fin a → Module.Dual ℝ (E n)) :
    castCovector h (wedgeList a f) =
      wedgeList b (fun i => f (Fin.cast h.symm i)) := by
  subst b
  rfl

/-- Wedge with a one-covector is the determinant with that covector first. -/
theorem prepend_wedgeList {n k : ℕ} (l : Module.Dual ℝ (E n))
    (f : Fin k → Module.Dual ℝ (E n)) :
    prependCovector (linearCovector l) (wedgeList k f) =
      wedgeList (k+1) (Fin.cons l f) := by
  unfold prependCovector
  rw [wedge_eq_library, linearCovector_eq_toForm, wedgeList_eq_toForm,
    ← D05.M15.ExteriorPairing.AlternatingForms.multiplication_elementary]
  have hw : Specs.D05.M15.ExteriorPairing.AlternatingForms.wedge
      (exteriorPower.ιMulti ℝ 1 (fun _ => l)) (exteriorPower.ιMulti ℝ k f) =
      exteriorPower.ιMulti ℝ (1+k) (Fin.append (fun _ : Fin 1 => l) f) := by
    apply Subtype.ext
    exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _
  rw [hw, ← wedgeList_eq_toForm, wedgeList_cast]
  congr 1
  funext i
  simp only [Fin.append_left_eq_cons, Function.comp_apply, Fin.cast_cast]
  rfl

/-- Laplace expansion of a normalized coordinate exterior term. -/
theorem prepend_dx_apply {n k : ℕ} (j : Fin n) (I : MultiIndex n k)
    (v : Fin (k+1) → E n) :
    prependCovector (coordinateOneForm n j) (dx (standardBasis n) I) v =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val * v i j *
        dx (standardBasis n) I (fun b => v (i.succAbove b)) := by
  rw [← coordinate_wedge (standardBasis n) I]
  change prependCovector (linearCovector ((standardBasis n).coord j)) _ v = _
  rw [prepend_wedgeList, wedgeList_apply, Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [wedgeList_apply]
  rfl

/-- The coordinate formula of d on the ordered standard basis, with omitted
vectors kept in increasing order. -/
theorem exteriorDerivative_basis {k : ℕ} (U : Set (E (k+1)))
    (η : FormField (k+1) k) (hη : IsCrForm (some 1) U η)
    (x : E (k+1)) (hx : x ∈ U) :
    exteriorDerivative η x (fun j => standardBasis (k+1) j) =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
        scalarPartialDerivative (fun y => η y
          (fun b => standardBasis (k+1) (i.succAbove b))) x i := by
  have hterm (I : MultiIndex (k+1) k) (j : Fin (k+1)) :
      prependCovector (coordinateOneForm (k+1) j) (dx (standardBasis (k+1)) I)
        (fun a => standardBasis (k+1) a) =
      (-1 : ℝ)^j.val * dx (standardBasis (k+1)) I
        (fun b => standardBasis (k+1) (j.succAbove b)) := by
    rw [prepend_dx_apply]
    simp [standardBasis_apply]
  simp only [exteriorDerivative_expansion, sum_apply, smul_apply, smul_eq_mul, hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have heval : (fun y => η y (fun b => standardBasis (k+1) (i.succAbove b))) =
      fun y => ∑ I : MultiIndex (k+1) k,
        coefficient (standardBasis (k+1)) (η y) I *
        dx (standardBasis (k+1)) I (fun b => standardBasis (k+1) (i.succAbove b)) :=
    funext (fun y => formField_evaluation η y _)
  rw [heval, scalarPartialDerivative_sum_mul_const _ _ x
    (isCrForm_coefficient_differentiableAt U η hη x hx) i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

/-- Newton–Leibniz expressed in the same proper Darboux integral as cells. -/
theorem cube_interval_ftc (F : ℝ → ℝ) (g : E 1 → ℝ)
    (hF : ContinuousOn F (Icc 0 1))
    (hg : ContinuousOn g (cube 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt F (g (Darboux.scalarPoint t)) t) :
    Darboux.lowerIntegral g (cubeBox 1) = F 1 - F 0 := by
  have hbox : cubeBox 1 = Darboux.intervalBox 0 1 zero_le_one := by
    apply Darboux.Subdivision.box_ext <;> apply PiLp.ext <;> intro i <;> rfl
  have hi : Darboux.Integrable g (cubeBox 1) :=
    ExceptionalSets.integrable_continuous (by norm_num) _ _ hg
  rw [hbox] at hi ⊢
  obtain ⟨hs,he⟩ := (Darboux.scalar_integral g 0 1 zero_le_one).2 hi
  exact he.trans (SingleVariableAnalysis.Riemann.real_ftc_second F
    (fun t => g (Darboux.scalarPoint t)) 0 1 zero_le_one hF hd hs)

/-- A coordinate line with the other coordinates fixed in their original order. -/
def coordinateLine {k : ℕ} (i : Fin (k+1)) (x : E k) (t : ℝ) : E (k+1) :=
  faceInsertion i false x + t • standardBasis (k+1) i

@[simp] theorem coordinateLine_same {k : ℕ} (i : Fin (k+1)) (x : E k) (t : ℝ) :
    coordinateLine i x t i = t := by
  simp [coordinateLine, standardBasis_apply]

@[simp] theorem coordinateLine_other {k : ℕ} (i : Fin (k+1)) (x : E k)
    (t : ℝ) (j : Fin k) : coordinateLine i x t (i.succAbove j) = x j := by
  simp [coordinateLine, standardBasis_apply, Fin.succAbove_ne]

@[simp] theorem coordinateLine_endpoint {k : ℕ} (i : Fin (k+1)) (x : E k) (ε : Bool) :
    coordinateLine i x (if ε then 1 else 0) = faceInsertion i ε x := by
  apply PiLp.ext
  intro j
  refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp

theorem coordinateLine_mem {k : ℕ} (i : Fin (k+1)) {x : E k} (hx : x ∈ cube k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : coordinateLine i x t ∈ cube (k+1) := by
  change ∀ j, 0 ≤ coordinateLine i x t j ∧ coordinateLine i x t j ≤ 1
  change ∀ a, 0 ≤ x a ∧ x a ≤ 1 at hx
  intro j
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · simpa using ht
  · simpa using hx a

/-- The coordinate split used by Fubini, with the selected coordinate last
as a block but with the remaining coordinates still in increasing order. -/
def coordinateBlockEquiv {k : ℕ} (i : Fin (k+1)) : Fin k ⊕ Fin 1 ≃ Fin (k+1) where
  toFun := Sum.elim i.succAbove (fun _ => i)
  invFun j := ((finSuccEquiv' i) j).elim (Sum.inr 0) Sum.inl
  left_inv j := by
    cases j with
    | inl j => simp [finSuccEquiv'_succAbove]
    | inr j => have hj : j = 0 := Subsingleton.elim _ _
               subst j
               simp [finSuccEquiv'_at]
  right_inv j := by
    refine Fin.succAboveCases i ?_ (fun a => ?_) j
    · simp [finSuccEquiv'_at]
    · simp [finSuccEquiv'_succAbove]

open Specs.D04.C06.DarbouxFubini.Model (blockPoint blockBox)

theorem blockPoint_eq_coordinateLine {k : ℕ} (i : Fin (k+1)) (x : E k) (y : E 1) :
    blockPoint (coordinateBlockEquiv i) x y = coordinateLine i x (y 0) := by
  apply PiLp.ext
  intro j
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · simp [coordinateBlockEquiv, finSuccEquiv'_at]
  · simp [coordinateBlockEquiv, finSuccEquiv'_succAbove]

theorem blockBox_cube {k : ℕ} (i : Fin (k+1)) :
    blockBox (coordinateBlockEquiv i) (cubeBox k) (cubeBox 1) = cubeBox (k+1) := by
  apply Darboux.Subdivision.box_ext <;> apply PiLp.ext <;> intro j
  · change blockPoint (coordinateBlockEquiv i) 0 0 j = 0
    rw [blockPoint_eq_coordinateLine]
    refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp
  · change blockPoint (coordinateBlockEquiv i)
      (WithLp.toLp 2 (fun _ => 1)) (WithLp.toLp 2 (fun _ => 1)) j = 1
    rw [blockPoint_eq_coordinateLine]
    refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp

/-- C¹ gives a continuous genuine coordinate derivative on the open domain. -/
theorem coordinatePartial_continuous {n : ℕ} (U : Set (E n)) (hU : IsOpen U)
    (f : E n → ℝ) (hf : CrOn 1 U f) (i : Fin n) :
    ContinuousOn (fun z => scalarPartialDerivative f z i) U := by
  have hd : ContinuousOn (fun z => totalDerivative f z (standardBasis n i)) U :=
    hf.2.clm_apply continuousOn_const
  apply hd.congr
  intro z hz
  exact scalarPartialDerivative_eq_fderiv f z
    ((totalDifferentiableAt_iff_differentiableAt U f z hU hz).mp (hf.1 z hz)) i

/-- Continuous functions have the proper cube integral, also in dimension zero. -/
theorem integrable_cube_of_continuous {k : ℕ} (g : E k → ℝ)
    (hg : ContinuousOn g (cube k)) : Darboux.Integrable g (cubeBox k) := by
  cases k with
  | zero => exact (Darboux.zero_dimension _ _).2.1
  | succ k => exact ExceptionalSets.integrable_continuous (Nat.succ_pos _) _ _ hg

/-- The canonical cell integrand is properly Riemann integrable for a form
continuous on any open neighborhood of the image, even when that neighborhood
is smaller than the cell's originally declared target. -/
theorem cellCoefficient_integrable_neighborhood {r k n} {O : Set (E n)}
    (c : Cell r k O) (V : Set (E n)) (ω : FormField n k)
    (hω : IsCrForm (some 0) V ω)
    (hcV : ∀ x : cube k, (c.toFun x).val ∈ V) :
    Darboux.Integrable (cellCoefficient c ω) (cubeBox k) := by
  obtain ⟨U,hU,hsub,hf,hmap⟩ := extension_into_neighborhood c V hω.1 hcV
  have hf1 : ContDiffOn ℝ 1 (cellExtension c) U :=
    hf.of_le (by exact_mod_cast c.positive)
  have heval := isCrForm_evaluation 0 U V (cellExtension c) ω
    (fun j x => totalDerivative (cellExtension c) x (standardBasis k j))
    hU hmap hf1.continuousOn hω
    (fun j => (hf1.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
  exact integrable_cube_of_continuous _ (heval.mono hsub)

/-- Fubini and the scalar FTC, for one selected coordinate of a C¹ function. -/
theorem cube_coordinate_ftc {k : ℕ} (U : Set (E (k+1))) (hU : IsOpen U)
    (hsub : cube (k+1) ⊆ U) (f : E (k+1) → ℝ) (hf : CrOn 1 U f)
    (i : Fin (k+1)) :
    Darboux.lowerIntegral (fun z => scalarPartialDerivative f z i) (cubeBox (k+1)) =
      Darboux.lowerIntegral (fun x => f (faceInsertion i true x) - f (faceInsertion i false x))
        (cubeBox k) := by
  let g : E (k+1) → ℝ := fun z => scalarPartialDerivative f z i
  have hg : ContinuousOn g (cube (k+1)) :=
    (coordinatePartial_continuous U hU f hf i).mono hsub
  have hi := integrable_cube_of_continuous g hg
  have hb : Darboux.Integrable g (blockBox (coordinateBlockEquiv i) (cubeBox k) (cubeBox 1)) := by
    simpa only [blockBox_cube] using hi
  have hslice (x : E k) (hx : x ∈ cube k) :
      Darboux.lowerIntegral (fun y => g (blockPoint (coordinateBlockEquiv i) x y)) (cubeBox 1) =
        f (faceInsertion i true x) - f (faceInsertion i false x) := by
    have hline : Continuous (coordinateLine i x) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hlineU : MapsTo (coordinateLine i x) (Icc 0 1) U :=
      fun _ ht => hsub (coordinateLine_mem i hx ht)
    have hfc : ContinuousOn f U := ((crOn_iff_contDiffOn 1 U f hU).mp hf).continuousOn
    apply cube_interval_ftc (fun t => f (coordinateLine i x t))
      (fun y => g (blockPoint (coordinateBlockEquiv i) x y))
      (hfc.comp hline.continuousOn hlineU) ?_ ?_ |>.trans ?_
    · simp_rw [blockPoint_eq_coordinateLine]
      apply hg.comp
      · exact (continuous_const.add
          ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).smul continuous_const)).continuousOn
      · intro y hy
        exact coordinateLine_mem i hx (hy 0)
    · intro t ht
      have hz := hlineU (Ioo_subset_Icc_self ht)
      have hd := (totalDifferentiableAt_iff_differentiableAt U f _ hU hz).mp (hf.1 _ hz)
      have hl : HasDerivAt (coordinateLine i x) (standardBasis (k+1) i) t := by
        convert! (hasDerivAt_const t (faceInsertion i false x)).add
          ((hasDerivAt_id t).smul_const (standardBasis (k+1) i)) using 1
        simp
      have hd' := hd.hasFDerivAt.comp_hasDerivAt t hl
      rw [blockPoint_eq_coordinateLine]
      change HasDerivAt (fun t => f (coordinateLine i x t))
        (scalarPartialDerivative f (coordinateLine i x t) i) t
      rw [scalarPartialDerivative_eq_fderiv f _ hd i]
      convert! hd' using 1
    · have h1 : coordinateLine i x 1 = faceInsertion i true x := by
        simpa using coordinateLine_endpoint i x true
      have h0 : coordinateLine i x 0 = faceInsertion i false x := by
        simpa using coordinateLine_endpoint i x false
      rw [h1,h0]
  have hsint (x : E k) (hx : x ∈ cube k) :
      Darboux.Integrable (fun y => g (blockPoint (coordinateBlockEquiv i) x y)) (cubeBox 1) := by
    apply integrable_cube_of_continuous
    simp_rw [blockPoint_eq_coordinateLine]
    apply hg.comp
    · exact (continuous_const.add
        ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).smul continuous_const)).continuousOn
    · intro y hy
      exact coordinateLine_mem i hx (hy 0)
  obtain ⟨hout,he⟩ := Darboux.Fubini.block_fubini (coordinateBlockEquiv i) hb
    (fun x => f (faceInsertion i true x) - f (faceInsertion i false x))
    (fun x hx => (hslice x hx).le)
    (fun x hx => by
      rw [← hslice x hx]
      exact (hsint x hx).2.le)
  change _ = Darboux.lowerIntegral _ _ at he
  simpa only [blockBox_cube, g, Darboux.integral,
    Specs.D04.C06.DarbouxIntegral.Model.integral] using he.symm

/-- Finite linearity of the lower integral when all summands are integrable. -/
theorem lowerIntegral_sum {m : ℕ} {ι : Type} [Fintype ι]
    (Q : Darboux.Box m) (f : ι → E m → ℝ)
    (hf : ∀ i, Darboux.Integrable (f i) Q) :
    Darboux.lowerIntegral (fun x => ∑ i, f i x) Q =
      ∑ i, Darboux.lowerIntegral (f i) Q := by
  classical
  have hs := Darboux.integrable_sum (n := m) (Q := Q) Finset.univ f (fun i _ => hf i)
  have he := Darboux.integral_sum (n := m) (Q := Q) Finset.univ f (fun i _ => hf i) hs
  simpa only [Finset.mem_univ, ↓reduceDIte, Darboux.integral,
    Specs.D04.C06.DarbouxIntegral.Model.integral] using he

theorem lowerIntegral_smul {m : ℕ} {Q : Darboux.Box m} {f : E m → ℝ}
    (a : ℝ) (hf : Darboux.Integrable f Q) :
    Darboux.lowerIntegral (fun x => a * f x) Q = a * Darboux.lowerIntegral f Q :=
  Darboux.integral_smul a hf (Darboux.integrable_smul a hf)

theorem lowerIntegral_sub {m : ℕ} {Q : Darboux.Box m} {f g : E m → ℝ}
    (hf : Darboux.Integrable f Q) (hg : Darboux.Integrable g Q) :
    Darboux.lowerIntegral (fun x => f x - g x) Q =
      Darboux.lowerIntegral f Q - Darboux.lowerIntegral g Q :=
  Darboux.integral_sub hf hg (Darboux.integrable_sub hf hg)

/-- Stokes on the parameter cube, proved by the ordered coordinate calculation.
All functions are C¹ on the specified open neighborhood; no compact support
or hypotheses about the rank of a parametrization enter this calculation. -/
theorem cube_stokes (k : ℕ) (U : Set (E (k+1))) (η : FormField (k+1) k)
    (hη : IsCrForm (some 1) U η) (hsub : cube (k+1) ⊆ U) :
    Darboux.lowerIntegral
      (fun x => exteriorDerivative η x (fun j => standardBasis (k+1) j))
      (cubeBox (k+1)) =
    ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
      (Darboux.lowerIntegral (fun x => pullback (faceInsertion i true) η x
        (fun j => standardBasis k j)) (cubeBox k) -
       Darboux.lowerIntegral (fun x => pullback (faceInsertion i false) η x
        (fun j => standardBasis k j)) (cubeBox k)) := by
  let b (i : Fin (k+1)) (y : E (k+1)) :=
    η y (fun j => standardBasis (k+1) (i.succAbove j))
  have hb (i : Fin (k+1)) : CrOn 1 U (b i) := by
    exact isCrForm_evaluation 1 U U id η
      (fun j _ => standardBasis (k+1) (i.succAbove j)) hη.1 (fun _ hx => hx)
      ((crOn_iff_contDiffOn 1 U id hη.1).mpr contDiffOn_id) hη
      (fun _ => (crOn_iff_contDiffOn 1 U _ hη.1).mpr contDiffOn_const)
  have hp (i : Fin (k+1)) :
      Darboux.Integrable (fun x => scalarPartialDerivative (b i) x i) (cubeBox (k+1)) :=
    integrable_cube_of_continuous _
      ((coordinatePartial_continuous U hη.1 (b i) (hb i) i).mono hsub)
  have hface (i : Fin (k+1)) (ε : Bool) :
      (fun x => pullback (faceInsertion i ε) η x (fun j => standardBasis k j)) =
        fun x => b i (faceInsertion i ε x) := by
    funext x
    simp only [pullback_apply, faceInsertion_derivative]
    rfl
  have hfi (i : Fin (k+1)) (ε : Bool) :
      Darboux.Integrable (fun x => b i (faceInsertion i ε x)) (cubeBox k) := by
    apply integrable_cube_of_continuous
    exact (((crOn_iff_contDiffOn 1 U (b i) hη.1).mp (hb i)).continuousOn).comp
      (faceInsertion_contDiff i ε).continuous.continuousOn
      (fun _ hx => hsub (Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i ε hx))
  calc
    _ = Darboux.lowerIntegral (fun x => ∑ i : Fin (k+1),
          (-1 : ℝ)^i.val * scalarPartialDerivative (b i) x i) (cubeBox (k+1)) := by
      apply lowerIntegral_congr
      intro x hx
      exact exteriorDerivative_basis U η hη x (hsub hx)
    _ = ∑ i : Fin (k+1), Darboux.lowerIntegral
          (fun x => (-1 : ℝ)^i.val * scalarPartialDerivative (b i) x i) (cubeBox (k+1)) :=
      lowerIntegral_sum _ _ (fun i => Darboux.integrable_smul _ (hp i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lowerIntegral_smul _ (hp i), cube_coordinate_ftc U hη.1 hsub (b i) (hb i) i,
        lowerIntegral_sub (hfi i true) (hfi i false), hface, hface]

/-- An arbitrary-cell theorem follows from the C¹ coordinate cube identity.
This reduction has no geometric hypotheses on the cell. -/
theorem cell_stokes_of_cube
    (hcube : ∀ (k : ℕ) (U : Set (E (k+1))) (η : FormField (k+1) k),
      IsCrForm (some 1) U η → cube (k+1) ⊆ U →
      Darboux.lowerIntegral
        (fun x => exteriorDerivative η x (fun j => standardBasis (k+1) j))
        (cubeBox (k+1)) =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
        (Darboux.lowerIntegral (fun x => pullback (faceInsertion i true) η x
          (fun j => standardBasis k j)) (cubeBox k) -
         Darboux.lowerIntegral (fun x => pullback (faceInsertion i false) η x
          (fun j => standardBasis k j)) (cubeBox k))) :
    Specs.D04.C15.CellStokesC2.cell_stokesType := by
  intro k n O c V ω hω hcV
  obtain ⟨U,hU,hsub,hη,he⟩ := cell_bulk_naturality c V ω hω hcV
  change cellIntegral c (exteriorDerivative ω) = chainIntegral ω (cellBoundary c)
  rw [he, hcube k U (pullback (cellExtension c) ω) hη hsub,
    boundaryIntegral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cellFace_integral_pullback, cellFace_integral_pullback]

/-- Linearity proves the full finite-chain assertion once the cell assertion
is available, using only cells actually occurring in the finite support. -/
theorem chain_stokes_of_cell
    (hcell : Specs.D04.C15.CellStokesC2.cell_stokesType) :
    Specs.D04.C15.CellStokesC2.chain_stokesType := by
  intro k n O C V ω hω hCV
  classical
  rw [← C.sum_single]
  simp only [map_finsuppSum, boundary_single, map_zsmul, chainIntegral_single]
  apply Finset.sum_congr rfl
  intro c hc
  change C c • cellIntegral c (exteriorDerivative ω) = _
  exact congrArg (fun t : ℝ => C c • t) (hcell c V ω hω (hCV c hc))

/-- Stokes on every C² cell, with the form defined on any open neighborhood
of its image. The parameter k=0 is the endpoint fundamental theorem. -/
theorem cell_stokes : Specs.D04.C15.CellStokesC2.cell_stokesType :=
  cell_stokes_of_cube cube_stokes

/-- Stokes on every finite integer chain of C² cells. -/
theorem chain_stokes : Specs.D04.C15.CellStokesC2.chain_stokesType :=
  chain_stokes_of_cell cell_stokes

end D04.Cells
