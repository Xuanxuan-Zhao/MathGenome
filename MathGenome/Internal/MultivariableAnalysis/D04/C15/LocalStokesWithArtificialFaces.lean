import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.LocalStokesWithArtificialFaces
import MathGenome.Internal.MultivariableAnalysis.D04.C15.CellStokesC1
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OutwardFirstBoundaryOrientation
import MathGenome.Internal.MultivariableAnalysis.D04.C14.FiniteCompactPartition

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped BigOperators Classical
namespace D04.LocalStokes
open Cells
open Specs.D04.C15.LocalStokesWithArtificialFaces
open Model

/-- Vanishing is imposed only on the actual face coefficient. -/
theorem face_integral_zero {r k n} {O : Set (E n)} (c : Cell r (k+1) O)
    (ω : FormField n k) (i : Fin (k+1)) (ε : Bool) (h : FaceZero c ω i ε) :
    cellIntegral (cellFace c i ε) ω = 0 := by
  rw [C1.face_integral_eq_evaluation]
  calc
    _ = Darboux.lowerIntegral (fun _ => 0) (cubeBox k) := lowerIntegral_congr h
    _ = 0 := by simpa using (Darboux.constant_integrals (cubeBox k) 0).1

/-- Cancellation of every artificial face, with no rank assumption. -/
theorem cell_interior : cell_interiorType := by
  intro k n O c V ω hω hV hf
  rw [cell_stokes_c1 c V ω hω hV, boundaryIntegral_eq_sum]
  simp only [face_integral_zero c ω _ _ (hf _ _), sub_self, mul_zero, Finset.sum_const_zero]

/-- Exactly one lower face survives; its exponent is the dimension k+1. -/
theorem cell_halfspace : cell_halfspaceType := by
  intro k n O c V ω hω hV hf
  rw [cell_stokes_c1 c V ω hω hV, boundaryIntegral_eq_sum]
  rw [Finset.sum_eq_single (Fin.last k)]
  · rw [face_integral_zero c ω _ true (hf _ true (Or.inr rfl))]
    simp only [Fin.val_last, zero_sub, pow_succ]
    ring
  · intro i _ hi
    rw [face_integral_zero c ω i true (hf i true (Or.inr rfl)),
      face_integral_zero c ω i false (hf i false (Or.inl hi))]
    ring
  · simp

/-- Multiplication by the bulk chart sign supplies the boundary chart sign. -/
theorem signed_cell_halfspace : signed_cell_halfspaceType := by
  intro k n O c V ω hω hV hf σ
  rw [cell_halfspace c V ω hω hV hf, mul_assoc]

/-- The stored cell extension can be replaced by the actual chart map
on the whole cube, for every input tuple. -/
theorem rectangleChartCell_pullback {k n p : ℕ} (Q : Darboux.Box k)
    (φ : E k → E n) (W : Set (E k)) (hW : IsOpen W)
    (hQ : Darboux.carrier Q ⊆ W) (hφ : ContDiffOn ℝ 1 φ W)
    (omega : FormField n p) {x : E k} (hx : x ∈ cube k) (v : Fin p → E k) :
    pullback (cellExtension (rectangleChartCell Q φ W hW hQ hφ)) omega x v =
      pullback (φ ∘ rectangleMap Q) omega x v := by
  exact C1.pullback_extension_eq _ _ _
    (hW.preimage (rectangleMap_C1 Q).continuous)
    (fun _ ht => hQ (rectangleMap_mem Q ht))
    (hφ.comp (rectangleMap_C1 Q).contDiffOn (fun _ ht => ht))
    (fun _ => rfl) omega ⟨x, hx⟩ v

/-- Pointwise functoriality here uses only first derivatives of the chart. -/
theorem rectangle_pullback_comp {k n p : ℕ} (Q : Darboux.Box k)
    (φ : E k → E n) (W : Set (E k)) (hW : IsOpen W)
    (hQ : Darboux.carrier Q ⊆ W) (hφ : ContDiffOn ℝ 1 φ W)
    (omega : FormField n p) {x : E k} (hx : x ∈ cube k) (v : Fin p → E k) :
    pullback (φ ∘ rectangleMap Q) omega x v =
      pullback (rectangleMap Q) (pullback φ omega) x v := by
  simp only [pullback_apply]
  have hdφ : DifferentiableAt ℝ φ (rectangleMap Q x) :=
    (hφ.differentiableOn (by norm_num)).differentiableAt
      (hW.mem_nhds (hQ (rectangleMap_mem Q hx)))
  change (omega (φ (rectangleMap Q x))
    (fun i => fderiv ℝ (φ ∘ rectangleMap Q) x (v i))) =
    omega (φ (rectangleMap Q x))
      (fun i => fderiv ℝ φ (rectangleMap Q x) (fderiv ℝ (rectangleMap Q) x (v i)))
  rw [fderiv_comp x hdφ ((rectangleMap_C1 Q).differentiable (by norm_num) x)]
  rfl

/-- The geometric endpoint of a rectangle face, in its original coordinate. -/
theorem rectangle_face_coordinate {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) (eps : Bool) (x : E k) :
    rectangleMap Q (faceInsertion i eps x) i =
      if eps then Q.upper i else Q.lower i := by
  simp only [rectangleMap, faceInsertion_same]
  cases eps <;> simp

/-- Every artificial face is disjoint from the smaller half-open box.
No claim that the original irregular domain is itself a rectangle is used. -/
theorem artificial_face_outside {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) (eps : Bool) (h : i ≠ Fin.last k ∨ eps = true) (x : E k) :
    rectangleMap Q (faceInsertion i eps x) ∉ halfBoxInterior Q := by
  intro hy
  by_cases hi : i = Fin.last k
  · subst i
    have he : eps = true := h.resolve_left (not_not.mpr rfl)
    subst eps
    have ht := hy.2.2
    rw [rectangle_face_coordinate] at ht
    exact lt_irrefl _ ht
  · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    have ht := hy.1 j
    rw [rectangle_face_coordinate] at ht
    cases eps
    · exact lt_irrefl _ ht.1
    · exact lt_irrefl _ ht.2

/-- Support control on the pulled-back form kills artificial coefficients,
although the ambient form may be nonzero off the chart image. -/
theorem rectangle_artificial_faces {k n : ℕ} (Q : Darboux.Box (k+1))
    (φ : E (k+1) → E n) (W : Set (E (k+1))) (hW : IsOpen W)
    (hQ : Darboux.carrier Q ⊆ W) (hφ : ContDiffOn ℝ 1 φ W)
    (omega : FormField n k)
    (hs : Function.support (pullback φ omega) ∩ Darboux.carrier Q ⊆ halfBoxInterior Q) :
    ∀ i eps, (i ≠ Fin.last k ∨ eps = true) →
      FaceZero (rectangleChartCell Q φ W hW hQ hφ) omega i eps := by
  intro i eps hi x hx
  have ht := Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i eps hx
  rw [rectangleChartCell_pullback Q φ W hW hQ hφ omega ht,
    rectangle_pullback_comp Q φ W hW hQ hφ omega ht]
  have hz : pullback φ omega (rectangleMap Q (faceInsertion i eps x)) = 0 := by
    by_contra hn
    exact artificial_face_outside Q i eps hi x (hs ⟨hn, rectangleMap_mem Q ht⟩)
  simp only [pullback_apply, hz, zero_apply]

/-- Zero extension across the artificial boundary is C¹ coefficientwise.
Compactness is relative to U; its image is a compact ambient subset of U. -/
theorem extendForm_C1 : extendForm_C1Type := by
  intro n p U η hη hK
  let K := Subtype.val '' tsupport (fun x : U => η x)
  have hKc : IsCompact K := hK.image continuous_subtype_val
  have hKU : K ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hs : Function.support (extendForm U η) ⊆ K := by
    intro x hx
    have hxU : x ∈ U := by
      by_contra hn
      exact hx (by simp [extendForm, Set.indicator_of_notMem hn])
    refine ⟨⟨x, hxU⟩, subset_tsupport _ ?_, rfl⟩
    simpa only [Function.mem_support, extendForm, Set.indicator_of_mem hxU] using hx
  refine ⟨isOpen_univ, fun I => ?_⟩
  apply (crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr
  apply ContDiff.contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · have he : (fun y => coefficient (standardBasis n) (extendForm U η y) I) =ᶠ[𝓝 x]
        (fun y => coefficient (standardBasis n) (η y) I) := by
      filter_upwards [hη.1.mem_nhds hx] with y hy
      simp [extendForm, hy]
    exact (((crOn_iff_contDiffOn 1 U _ hη.1).mp (hη.2 I)).contDiffAt
      (hη.1.mem_nhds hx)).congr_of_eventuallyEq he
  · have hxK : x ∉ K := fun h => hx (hKU h)
    have he : (fun y => coefficient (standardBasis n) (extendForm U η y) I) =ᶠ[𝓝 x]
        (fun _ => 0) := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      have hz : extendForm U η y = 0 := Function.notMem_support.mp (fun h => hy (hs h))
      simp [hz, coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- A smooth weight supported in W regularizes the arbitrary representative
outside W, since the product vanishes on a neighborhood of every such point. -/
theorem cutoff_form_C1 {n p : ℕ} (W : Set (E n)) (eta : FormField n p)
    (heta : IsCrForm (some 1) W eta) (f : E n → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : tsupport f ⊆ W) :
    IsCrForm (some 1) univ (fun x => f x • eta x) := by
  refine ⟨isOpen_univ, fun I => ?_⟩
  apply (crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr
  apply ContDiff.contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · change ContDiffAt ℝ 1
      (fun y => f y * coefficient (standardBasis n) (eta y) I) x
    exact hf.contDiffAt.mul (((crOn_iff_contDiffOn 1 W _ heta.1).mp (heta.2 I)).contDiffAt
      (heta.1.mem_nhds (hs hx)))
  · have he : (fun y => coefficient (standardBasis n) (f y • eta y) I) =ᶠ[𝓝 x]
        (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy, coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient]
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- Local C¹ extensions are glued using finitely many genuine smooth
cutoffs. The only sum-to-one requirement is near the compact relative support. -/
theorem compact_relative_extension : compact_relative_extensionType := by
  intro n p S U eta hU hlocal hcompact
  let K := Subtype.val '' tsupport (fun x : ↥(U ∩ S) => eta x)
  have hK : IsCompact K := hcompact.image continuous_subtype_val
  have hKS : K ⊆ U ∩ S := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hloc (x : K) : ∃ (W : Set (E n)) (theta : FormField n p),
      x.val ∈ W ∧ W ⊆ U ∧ IsCrForm (some 1) W theta ∧
      EqOn theta eta (W ∩ S) := by
    obtain ⟨V, theta, hx, ht, he⟩ := hlocal x (hKS x.property)
    let W := V ∩ U
    have hW : IsOpen W := ht.1.inter hU
    refine ⟨W, theta, ⟨hx, (hKS x.property).1⟩, inter_subset_right, ⟨hW, ?_⟩, ?_⟩
    · intro I
      exact (crOn_iff_contDiffOn 1 W _ hW).mpr
        (((crOn_iff_contDiffOn 1 V _ ht.1).mp (ht.2 I)).mono inter_subset_left)
    · intro y hy
      exact he ⟨hy.1.1, hy.1.2, hy.2⟩
  choose W theta hxW hWU ht he using hloc
  have hbumps (x : K) : ∃ (rho : E n → ℝ) (A : Set (E n)),
      ContDiff ℝ (⊤ : ℕ∞) rho ∧ (∀ y, 0 ≤ rho y) ∧
      IsOpen A ∧ x.val ∈ A ∧ EqOn rho (fun _ => 1) A ∧ tsupport rho ⊆ W x := by
    obtain ⟨rho, hr⟩ := EuclideanSmoothCutoffs.exists_smooth_cutoff
      {x.val} (W x) isCompact_singleton (ht x).1 (singleton_subset_iff.mpr (hxW x))
    obtain ⟨A, hA, hxA, hone⟩ := hr.2.2.2.1
    exact ⟨rho, A, hr.1, fun y => (hr.2.2.1 y).1, hA,
      hxA (mem_singleton _), hone, hr.2.2.2.2.2⟩
  choose rho A hrsm hrnon hA hxA hone hsup using hbumps
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover A hA (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let rho' := fun i => rho (e i).val
  obtain ⟨f, hfsm, hfnon, hfsup, _, hfone⟩ := FiniteCompactPartition.normalize_bumps
    rho' (fun i => hrsm (e i).val) (fun i => hrnon (e i).val)
  have hfW (i : Fin (Fintype.card s)) : tsupport (f i) ⊆ W (e i).val :=
    (hfsup id i).trans (hsup (e i).val)
  have hsum (x : E n) (hx : x ∈ K) : ∑ i, f i x = 1 := by
    apply hfone
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
    obtain ⟨i, hi⟩ := e.surjective ⟨j, hj⟩
    have hrone : rho' i x = 1 := by
      change rho (e i).val x = 1
      rw [hi]
      exact hone j hxj
    calc
      1 = rho' i x := hrone.symm
      _ ≤ ∑ j, rho' j x := Finset.single_le_sum
        (fun j _ => hrnon (e j).val x) (Finset.mem_univ _)
  let g : FormField n p := fun x => ∑ i, f i x • theta (e i).val x
  have hg : IsCrForm (some 1) univ g := by
    have htC i := cutoff_form_C1 (W (e i).val) (theta (e i).val) (ht (e i).val)
      (f i) ((hfsm i).of_le (by norm_num)) (hfW i)
    refine ⟨isOpen_univ, fun I => ?_⟩
    apply (crOn_iff_contDiffOn 1 univ _ isOpen_univ).mpr
    have hexp : (fun x => coefficient (standardBasis n) (g x) I) =
        fun x => ∑ i, coefficient (standardBasis n) (f i x • theta (e i).val x) I := by
      funext x
      simp only [g, coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient,
        sum_apply]
    change ContDiffOn ℝ 1 (fun x => coefficient (standardBasis n) (g x) I) univ
    rw [hexp]
    exact ContDiffOn.sum fun i _ => (crOn_iff_contDiffOn 1 univ _ isOpen_univ).mp ((htC i).2 I)
  refine ⟨g, hg, ?_⟩
  intro x hxS
  have heval (i : Fin (Fintype.card s)) :
      f i x • theta (e i).val x = f i x • extendForm U eta x := by
    by_cases hx : f i x = 0
    · simp [hx]
    · have hxW' := hfW i (subset_tsupport _ hx)
      rw [he (e i).val ⟨hxW', hxS⟩]
      simp [extendForm, hWU (e i).val hxW']
  change (∑ i, f i x • theta (e i).val x) = _
  simp_rw [heval]
  rw [← Finset.sum_smul]
  by_cases hxU : x ∈ U
  · by_cases hxeta : eta x = 0
    · simp [extendForm, hxU, hxeta]
    · have hxK : x ∈ K :=
        ⟨⟨x, hxU, hxS⟩, subset_tsupport _ hxeta, rfl⟩
      rw [hsum x hxK, one_smul]
  · simp [extendForm, hxU]

/-- The C¹ ambient theorem on a localized chart rectangle. -/
theorem ambient_rectangle : ambient_rectangleType := by
  intro k n Q phi W hW hQ hphi V omega homega hmap hs sigma
  exact signed_cell_halfspace (rectangleChartCell Q phi W hW hQ hphi) V omega homega
    (fun x => hmap (rectangleMap_mem Q x.property))
    (rectangle_artificial_faces Q phi W hW hQ hphi omega hs) sigma

@[simp] theorem rectangleFacePoint_same {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) (eps : Bool) (x : E k) :
    rectangleFacePoint Q i eps x i = if eps then Q.upper i else Q.lower i := by
  simpa only [rectangleFacePoint] using
    (Fin.insertNth_apply_same (α := fun _ => ℝ) i (if eps then Q.upper i else Q.lower i) (fun j => x j))

@[simp] theorem rectangleFacePoint_other {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) (eps : Bool) (x : E k) (j : Fin k) :
    rectangleFacePoint Q i eps x (i.succAbove j) = x j := by
  simpa only [rectangleFacePoint] using
    (Fin.insertNth_apply_succAbove (α := fun _ => ℝ) i (if eps then Q.upper i else Q.lower i) (fun j => x j) j)

/-- Coordinate-line membership in the actual, possibly asymmetric rectangle. -/
theorem coordinateLine_mem_rectangle {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) {x : E k} (hx : x ∈ Darboux.carrier (rectangleFaceBox Q i))
    {t : ℝ} (ht : t ∈ Icc (Q.lower i) (Q.upper i)) :
    coordinateLine i x t ∈ Darboux.carrier Q := by
  intro j
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · simpa using ht
  · simpa only [coordinateLine_other, rectangleFaceBox] using hx a

@[simp] theorem coordinateLine_rectangle_endpoint {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) (x : E k) (eps : Bool) :
    coordinateLine i x (if eps then Q.upper i else Q.lower i) =
      rectangleFacePoint Q i eps x := by
  apply PiLp.ext
  intro j
  refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp

open Specs.D04.C06.DarbouxFubini.Model (blockPoint blockBox)

theorem rectangle_blockBox {k : ℕ} (Q : Darboux.Box (k+1)) (i : Fin (k+1)) :
    blockBox (coordinateBlockEquiv i) (rectangleFaceBox Q i)
      (Darboux.intervalBox (Q.lower i) (Q.upper i) (Q.ordered i)) = Q := by
  apply Darboux.Subdivision.box_ext <;> apply PiLp.ext <;> intro j
  · change blockPoint (coordinateBlockEquiv i) _ _ j = _
    rw [blockPoint_eq_coordinateLine]
    refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp [rectangleFaceBox, Darboux.intervalBox,
      Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
      Specs.D04.C06.DarbouxIntegral.Model.scalarPoint]
  · change blockPoint (coordinateBlockEquiv i) _ _ j = _
    rw [blockPoint_eq_coordinateLine]
    refine Fin.succAboveCases i ?_ (fun a => ?_) j <;> simp [rectangleFaceBox, Darboux.intervalBox,
      Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
      Specs.D04.C06.DarbouxIntegral.Model.scalarPoint]

theorem integrable_rectangle_of_continuous {k : ℕ} (Q : Darboux.Box k)
    (g : E k → ℝ) (hg : ContinuousOn g (Darboux.carrier Q)) : Darboux.Integrable g Q := by
  cases k with
  | zero => exact (Darboux.zero_dimension _ _).2.1
  | succ k => exact ExceptionalSets.integrable_continuous (Nat.succ_pos _) _ _ hg

/-- The one-dimensional FTC in the established proper Riemann integral. -/
theorem rectangle_interval_ftc (a b : ℝ) (hab : a ≤ b) (F : ℝ → ℝ) (g : E 1 → ℝ)
    (hF : ContinuousOn F (Icc a b))
    (hg : ContinuousOn g (Darboux.carrier (Darboux.intervalBox a b hab)))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt F (g (Darboux.scalarPoint t)) t) :
    Darboux.lowerIntegral g (Darboux.intervalBox a b hab) = F b - F a := by
  have hi := integrable_rectangle_of_continuous _ g hg
  obtain ⟨hs, he⟩ := (Darboux.scalar_integral g a b hab).2 hi
  exact he.trans (SingleVariableAnalysis.Riemann.real_ftc_second F
    (fun t => g (Darboux.scalarPoint t)) a b hab hF hd hs)

/-- Fubini followed by FTC along one coordinate, with all remaining
coordinates in their original order. -/
theorem rectangle_coordinate_ftc {k : ℕ} (Q : Darboux.Box (k+1))
    (U : Set (E (k+1))) (hU : IsOpen U) (hsub : Darboux.carrier Q ⊆ U)
    (f : E (k+1) → ℝ) (hf : CrOn 1 U f) (i : Fin (k+1)) :
    Darboux.lowerIntegral (fun z => scalarPartialDerivative f z i) Q =
      Darboux.lowerIntegral (fun x => f (rectangleFacePoint Q i true x) -
        f (rectangleFacePoint Q i false x)) (rectangleFaceBox Q i) := by
  let A := rectangleFaceBox Q i
  let B := Darboux.intervalBox (Q.lower i) (Q.upper i) (Q.ordered i)
  let g : E (k+1) → ℝ := fun z => scalarPartialDerivative f z i
  have hg : ContinuousOn g (Darboux.carrier Q) :=
    (coordinatePartial_continuous U hU f hf i).mono hsub
  have hi := integrable_rectangle_of_continuous Q g hg
  have hb : Darboux.Integrable g (blockBox (coordinateBlockEquiv i) A B) := by
    simpa only [A, B, rectangle_blockBox] using hi
  have hslice (x : E k) (hx : x ∈ Darboux.carrier A) :
      Darboux.lowerIntegral (fun y => g (blockPoint (coordinateBlockEquiv i) x y)) B =
        f (rectangleFacePoint Q i true x) - f (rectangleFacePoint Q i false x) := by
    have hline : Continuous (coordinateLine i x) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hlineU : MapsTo (coordinateLine i x) (Icc (Q.lower i) (Q.upper i)) U :=
      fun _ ht => hsub (coordinateLine_mem_rectangle Q i hx ht)
    have hfc : ContinuousOn f U := ((crOn_iff_contDiffOn 1 U f hU).mp hf).continuousOn
    apply rectangle_interval_ftc (Q.lower i) (Q.upper i) (Q.ordered i)
      (fun t => f (coordinateLine i x t))
      (fun y => g (blockPoint (coordinateBlockEquiv i) x y))
      (hfc.comp hline.continuousOn hlineU) ?_ ?_ |>.trans ?_
    · simp_rw [blockPoint_eq_coordinateLine]
      apply hg.comp
      · exact (continuous_const.add
          ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).smul continuous_const)).continuousOn
      · intro y hy
        exact coordinateLine_mem_rectangle Q i hx (hy 0)
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
    · have h1 : coordinateLine i x (Q.upper i) = rectangleFacePoint Q i true x := by
        simpa using coordinateLine_rectangle_endpoint Q i x true
      have h0 : coordinateLine i x (Q.lower i) = rectangleFacePoint Q i false x := by
        simpa using coordinateLine_rectangle_endpoint Q i x false
      rw [h1, h0]
  have hsint (x : E k) (hx : x ∈ Darboux.carrier A) :
      Darboux.Integrable (fun y => g (blockPoint (coordinateBlockEquiv i) x y)) B := by
    apply integrable_rectangle_of_continuous
    simp_rw [blockPoint_eq_coordinateLine]
    apply hg.comp
    · exact (continuous_const.add
        ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).smul continuous_const)).continuousOn
    · intro y hy
      exact coordinateLine_mem_rectangle Q i hx (hy 0)
  obtain ⟨_, he⟩ := Darboux.Fubini.block_fubini (coordinateBlockEquiv i) hb
    (fun x => f (rectangleFacePoint Q i true x) - f (rectangleFacePoint Q i false x))
    (fun x hx => (hslice x hx).le)
    (fun x hx => by rw [← hslice x hx]; exact (hsint x hx).2.le)
  change _ = Darboux.lowerIntegral _ _ at he
  simpa only [A, B, rectangle_blockBox, g, Darboux.integral,
    Specs.D04.C06.DarbouxIntegral.Model.integral] using he.symm

/-- Stokes in actual rectangle coordinates, not merely on a renamed cube. -/
theorem rectangle_stokes : rectangle_stokesType := by
  intro k Q U eta heta hsub
  let b (i : Fin (k+1)) (y : E (k+1)) :=
    eta y (fun j => standardBasis (k+1) (i.succAbove j))
  have hb (i : Fin (k+1)) : CrOn 1 U (b i) :=
    isCrForm_evaluation 1 U U id eta
      (fun j _ => standardBasis (k+1) (i.succAbove j)) heta.1 (fun _ hx => hx)
      ((crOn_iff_contDiffOn 1 U id heta.1).mpr contDiffOn_id) heta
      (fun _ => (crOn_iff_contDiffOn 1 U _ heta.1).mpr contDiffOn_const)
  have hp (i : Fin (k+1)) :
      Darboux.Integrable (fun x => scalarPartialDerivative (b i) x i) Q :=
    integrable_rectangle_of_continuous Q _
      ((coordinatePartial_continuous U heta.1 (b i) (hb i) i).mono hsub)
  have hfc (i : Fin (k+1)) (eps : Bool) : Continuous (rectangleFacePoint Q i eps) := by
    have he : rectangleFacePoint Q i eps = fun x =>
        faceInsertion i false x + (if eps then Q.upper i else Q.lower i) • standardBasis (k+1) i := by
      funext x
      exact (coordinateLine_rectangle_endpoint Q i x eps).symm
    rw [he]
    exact (Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_contDiff i false).continuous.add
      continuous_const
  have hfm (i : Fin (k+1)) (eps : Bool) :
      MapsTo (rectangleFacePoint Q i eps) (Darboux.carrier (rectangleFaceBox Q i)) U := by
    intro x hx
    apply hsub
    rw [← coordinateLine_rectangle_endpoint]
    apply coordinateLine_mem_rectangle Q i hx
    cases eps
    · exact ⟨le_rfl, Q.ordered i⟩
    · exact ⟨Q.ordered i, le_rfl⟩
  have hfi (i : Fin (k+1)) (eps : Bool) :
      Darboux.Integrable (fun x => b i (rectangleFacePoint Q i eps x)) (rectangleFaceBox Q i) :=
    integrable_rectangle_of_continuous _ _
      ((((crOn_iff_contDiffOn 1 U (b i) heta.1).mp (hb i)).continuousOn).comp
        (hfc i eps).continuousOn (hfm i eps))
  change Darboux.lowerIntegral _ Q = _
  calc
    _ = Darboux.lowerIntegral (fun x => ∑ i : Fin (k+1),
          (-1 : ℝ)^i.val * scalarPartialDerivative (b i) x i) Q := by
      apply lowerIntegral_congr
      intro x hx
      exact exteriorDerivative_basis U eta heta x (hsub hx)
    _ = ∑ i : Fin (k+1), Darboux.lowerIntegral
          (fun x => (-1 : ℝ)^i.val * scalarPartialDerivative (b i) x i) Q :=
      lowerIntegral_sum _ _ (fun i => Darboux.integrable_smul _ (hp i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [lowerIntegral_smul _ (hp i), rectangle_coordinate_ftc Q U heta.1 hsub (b i) (hb i) i,
        lowerIntegral_sub (hfi i true) (hfi i false)]
      rfl

/-- Vanishing of the whole form implies vanishing of its surviving face
coefficient; this includes evaluation on a zero-dimensional face. -/
theorem coordinateFaceIntegral_zero {k : ℕ} (Q : Darboux.Box (k+1))
    (eta : FormField (k+1) k) (i : Fin (k+1)) (eps : Bool)
    (h : ∀ x ∈ Darboux.carrier (rectangleFaceBox Q i), eta (rectangleFacePoint Q i eps x) = 0) :
    coordinateFaceIntegral Q eta i eps = 0 := by
  change Darboux.lowerIntegral _ _ = _
  calc
    _ = Darboux.lowerIntegral (fun _ => 0) (rectangleFaceBox Q i) := by
      apply lowerIntegral_congr
      intro x hx
      change eta (rectangleFacePoint Q i eps x)
        (fun j => standardBasis (k+1) (i.succAbove j)) = 0
      rw [h x hx]
      rfl
    _ = 0 := by simpa using (Darboux.constant_integrals (rectangleFaceBox Q i) 0).1

/-- Full rectangle membership of every geometric face point. -/
theorem rectangleFacePoint_mem {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) (eps : Bool) {x : E k}
    (hx : x ∈ Darboux.carrier (rectangleFaceBox Q i)) :
    rectangleFacePoint Q i eps x ∈ Darboux.carrier Q := by
  rw [← coordinateLine_rectangle_endpoint]
  apply coordinateLine_mem_rectangle Q i hx
  cases eps
  · exact ⟨le_rfl, Q.ordered i⟩
  · exact ⟨Q.ordered i, le_rfl⟩

/-- Coefficient cancellation in an interior rectangle. -/
theorem coordinate_interior {k : ℕ} (Q : Darboux.Box (k+1))
    (U : Set (E (k+1))) (eta : FormField (k+1) k)
    (heta : IsCrForm (some 1) U eta) (hQ : Darboux.carrier Q ⊆ U)
    (hs : Function.support eta ∩ Darboux.carrier Q ⊆ boxInterior Q) :
    coordinateIntegral Q (exteriorDerivative eta) = 0 := by
  have hz (i : Fin (k+1)) (eps : Bool) : coordinateFaceIntegral Q eta i eps = 0 := by
    apply coordinateFaceIntegral_zero
    intro x hx
    by_contra hn
    have hp := hs ⟨hn, rectangleFacePoint_mem Q i eps hx⟩
    have hi := hp i
    rw [rectangleFacePoint_same] at hi
    cases eps
    · exact lt_irrefl _ hi.1
    · exact lt_irrefl _ hi.2
  rw [rectangle_stokes Q U eta heta hQ]
  simp only [hz, sub_self, mul_zero, Finset.sum_const_zero]

/-- Coefficient cancellation at the flat bottom: the remaining sign is
(-1)^(k+1), the outward-first sign for the actual dimension k+1. -/
theorem coordinate_halfspace {k : ℕ} (Q : Darboux.Box (k+1))
    (U : Set (E (k+1))) (eta : FormField (k+1) k)
    (heta : IsCrForm (some 1) U eta) (hQ : Darboux.carrier Q ⊆ U)
    (hs : Function.support eta ∩ Darboux.carrier Q ⊆ halfBoxInterior Q) :
    coordinateIntegral Q (exteriorDerivative eta) =
      (-1 : ℝ)^(k+1) * coordinateFaceIntegral Q eta (Fin.last k) false := by
  have hz (i : Fin (k+1)) (eps : Bool) (h : i ≠ Fin.last k ∨ eps = true) :
      coordinateFaceIntegral Q eta i eps = 0 := by
    apply coordinateFaceIntegral_zero
    intro x hx
    by_contra hn
    have hp := hs ⟨hn, rectangleFacePoint_mem Q i eps hx⟩
    by_cases hi : i = Fin.last k
    · subst i
      have he : eps = true := h.resolve_left (not_not.mpr rfl)
      subst eps
      have ht := hp.2.2
      rw [rectangleFacePoint_same] at ht
      exact lt_irrefl _ ht
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      have ht := hp.1 j
      rw [rectangleFacePoint_same] at ht
      cases eps
      · exact lt_irrefl _ ht.1
      · exact lt_irrefl _ ht.2
  rw [rectangle_stokes Q U eta heta hQ, Finset.sum_eq_single (Fin.last k)]
  · rw [hz _ true (Or.inr rfl)]
    simp only [Fin.val_last, zero_sub, pow_succ]
    ring
  · intro i _ hi
    rw [hz i true (Or.inr rfl), hz i false (Or.inl hi)]
    ring
  · simp

/-- Compact support stays compact after extension by zero, without any
continuity assumption on the target space of alternating covectors. -/
theorem extendForm_compact {n p : ℕ} (U : Set (E n)) (eta : FormField n p)
    (hc : IsCompact (tsupport (fun x : U => eta x))) :
    IsCompact (tsupport (extendForm U eta)) := by
  let K := Subtype.val '' tsupport (fun x : U => eta x)
  have hK : IsCompact K := hc.image continuous_subtype_val
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_cases hxU : x ∈ U
  · refine ⟨⟨x, hxU⟩, subset_tsupport _ ?_, rfl⟩
    simpa only [Function.mem_support, extendForm, Set.indicator_of_mem hxU] using hx
  · exact False.elim (hx (by simp [extendForm, hxU]))

/-- A compact subset can be enclosed strictly in a nondegenerate rectangle;
this assertion is made after zero extension, not inside an irregular chart. -/
theorem enclose_compact {n : ℕ} (K : Set (E n)) (hK : IsCompact K) :
    ∃ Q : Darboux.Box n, Darboux.Nondegenerate Q ∧ K ⊆ boxInterior Q := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_lt
  let Q := centeredBox (0 : E n) R hR.le
  refine ⟨Q, ?_, ?_⟩
  · intro i
    dsimp [Q, centeredBox]
    linarith
  · intro x hx i
    have hi : |x i| < R := (show |x i| ≤ ‖x‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans_lt (hb x hx)
    simpa only [Q, centeredBox, PiLp.zero_apply, zero_sub, zero_add] using abs_lt.mp hi

/-- The same enclosure relative to H has lower last coordinate zero, while
all side and upper artificial faces are strictly separated from K. -/
theorem enclose_compact_halfspace {k : ℕ} (K : Set (E (k+1))) (hK : IsCompact K)
    (hKH : K ⊆ halfSpace (k+1)) :
    ∃ Q : Darboux.Box (k+1), Darboux.Nondegenerate Q ∧
      Q.lower (Fin.last k) = 0 ∧ K ⊆ halfBoxInterior Q := by
  obtain ⟨R, hR, hb⟩ := hK.isBounded.exists_pos_norm_lt
  let Q := halfCenteredBox (0 : E (k+1)) R hR.le rfl
  have hlast : Q.lower (Fin.last k) = 0 := by simp [Q, halfCenteredBox]
  refine ⟨Q, ?_, hlast, ?_⟩
  · intro i
    by_cases hi : i = Fin.last k
    · subst i; simpa [Q, halfCenteredBox] using hR
    · simp only [Q, halfCenteredBox, hi, ite_false, PiLp.zero_apply, zero_sub, zero_add]
      linarith
  · intro x hx
    have hi (i : Fin (k+1)) : |x i| < R := (show |x i| ≤ ‖x‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i).trans_lt (hb x hx)
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simpa only [Q, halfCenteredBox, Fin.castSucc_ne_last, ite_false,
        PiLp.zero_apply, zero_sub, zero_add] using abs_lt.mp (hi j.castSucc)
    · rw [hlast]; exact hKH hx
    · simpa only [Q, halfCenteredBox, PiLp.zero_apply, zero_add] using (abs_lt.mp (hi (Fin.last k))).2

/-- Every fixed evaluation of a continuous form is continuous. -/
theorem form_evaluation_continuous {n p : ℕ} (U : Set (E n)) (eta : FormField n p)
    (heta : IsCrForm (some 0) U eta) (v : Fin p → E n) :
    ContinuousOn (fun x => eta x v) U := by
  simp_rw [formField_evaluation]
  apply continuousOn_finsetSum
  intro I _
  exact (heta.2 I).mul continuousOn_const

theorem form_C0 {n p : ℕ} (U : Set (E n)) (eta : FormField n p)
    (heta : IsCrForm (some 1) U eta) : IsCrForm (some 0) U eta :=
  ⟨heta.1, fun I => ((crOn_iff_contDiffOn 1 U _ heta.1).mp (heta.2 I)).continuousOn⟩

theorem derivative_integrable {k : ℕ} (Q : Darboux.Box (k+1))
    (eta : FormField (k+1) k) (heta : IsCrForm (some 1) univ eta) :
    Darboux.Integrable (fun x => exteriorDerivative eta x (fun j => standardBasis (k+1) j)) Q :=
  integrable_rectangle_of_continuous Q _
    ((form_evaluation_continuous univ (exteriorDerivative eta)
      (exteriorDerivative_continuous univ eta heta) _).mono (subset_univ _))

/-- The full compactly supported coordinate interior assertion. -/
theorem compact_interior : compact_interiorType := by
  intro k U eta heta hc
  have he := extendForm_C1 U eta heta hc
  have hce := extendForm_compact U eta hc
  refine ⟨he, enclose_compact _ hce, ?_⟩
  intro Q hQ
  exact ⟨derivative_integrable Q _ he,
    coordinate_interior Q univ _ he (subset_univ _)
      (fun x hx => hQ (subset_tsupport _ hx.1))⟩

/-- Global continuity of the geometric face parametrization. -/
theorem rectangleFacePoint_continuous {k : ℕ} (Q : Darboux.Box (k+1))
    (i : Fin (k+1)) (eps : Bool) : Continuous (rectangleFacePoint Q i eps) := by
  have he : rectangleFacePoint Q i eps = fun x =>
      faceInsertion i false x + (if eps then Q.upper i else Q.lower i) • standardBasis (k+1) i := by
    funext x
    exact (coordinateLine_rectangle_endpoint Q i x eps).symm
  rw [he]
  exact (Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_contDiff i false).continuous.add
    continuous_const

/-- Norm control for the local rectangle refinement. -/
theorem norm_sub_le_of_centeredBox {n : ℕ} (p : E n) (delta : ℝ) (hd : 0 ≤ delta)
    {x : E n} (hx : x ∈ Darboux.carrier (centeredBox p delta hd)) :
    ‖x - p‖ ≤ Real.sqrt (n : ℝ) * delta := by
  apply (norm_le_sqrt_mul_maxNorm (x-p)).trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [maxNorm_eq_coordinate_norm]
  apply (pi_norm_le_iff_of_nonneg hd).mpr
  intro i
  change |x i - p i| ≤ delta
  rw [abs_le]
  have hi := hx i
  dsimp [centeredBox] at hi
  exact ⟨by linarith [hi.1, hi.2], by linarith [hi.1, hi.2]⟩

/-- A small closed centered rectangle fits inside any specified open set. -/
theorem small_centeredBox {n : ℕ} (U : Set (E n)) (hU : IsOpen U) (p : E n) (hp : p ∈ U) :
    ∃ (delta : ℝ) (hd : 0 < delta), Darboux.carrier (centeredBox p delta hd.le) ⊆ U := by
  obtain ⟨eps, heps, hb⟩ := Metric.isOpen_iff.mp hU p hp
  let delta := eps / (2 * (Real.sqrt (n : ℝ) + 1))
  have hden : 0 < 2 * (Real.sqrt (n : ℝ) + 1) := by positivity
  have hd : 0 < delta := div_pos heps hden
  have heq : 2 * (Real.sqrt (n : ℝ) + 1) * delta = eps := by
    dsimp [delta]
    field_simp
  refine ⟨delta, hd, ?_⟩
  intro x hx
  apply hb
  rw [Metric.mem_ball, dist_eq_norm]
  exact (norm_sub_le_of_centeredBox p delta hd.le hx).trans_lt (by nlinarith [Real.sqrt_nonneg (n : ℝ)])

/-- Refinement is chosen before the support weights, using nested boxes. -/
theorem interior_rectangles : interior_rectanglesType := by
  intro n U hU p hp
  obtain ⟨delta, hd, hbox⟩ := small_centeredBox U hU p hp
  refine ⟨delta, hd, hbox, ?_, ?_⟩
  · intro i
    dsimp [centeredBox]
    exact ⟨by linarith, by linarith⟩
  · intro x hx i
    have hi := hx i
    dsimp [centeredBox] at hi ⊢
    exact ⟨by linarith [hi.1, hi.2], by linarith [hi.1, hi.2]⟩

/-- The boundary version retains the flat bottom and keeps every other
face separated, even for dimension one. -/
theorem boundary_rectangles : boundary_rectanglesType := by
  intro k U hU p hp hp0
  obtain ⟨delta, hd, hbox⟩ := small_centeredBox U hU p hp
  refine ⟨delta, hd, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨hbox ?_, ?_⟩
    · intro i
      have hi := hx i
      by_cases hi' : i = Fin.last k
      · subst i
        simp only [halfCenteredBox, ite_true, hp0, zero_add] at hi
        dsimp [centeredBox]
        rw [hp0]
        exact ⟨by linarith [hi.1], by simpa only [zero_add] using hi.2⟩
      · simpa only [halfCenteredBox, hi', ite_false, centeredBox] using hi
    · change 0 ≤ x (Fin.last k)
      have hi := (hx (Fin.last k)).1
      simpa only [halfCenteredBox, ite_true] using hi
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      simp only [halfCenteredBox, Fin.castSucc_ne_last, ite_false]
      exact ⟨by linarith, by linarith⟩
    · simp only [halfCenteredBox, ite_true, hp0, le_refl]
    · simp only [halfCenteredBox, hp0, zero_add]
      linarith
  · intro x hx
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi := hx i.castSucc
      simp only [halfCenteredBox, Fin.castSucc_ne_last, ite_false] at hi ⊢
      exact ⟨by linarith [hi.1, hi.2], by linarith [hi.1, hi.2]⟩
    · simpa only [halfCenteredBox, ite_true] using (hx (Fin.last k)).1
    · have hi := (hx (Fin.last k)).2
      dsimp [halfCenteredBox] at hi ⊢
      linarith

/-- Unique differentiation on the inward half-space identifies the full
first derivatives of any two C¹ extensions, including at its flat boundary. -/
theorem halfspace_extension_independent : halfspace_extension_independentType := by
  intro k p eta theta heta htheta H heq x hx
  have hud : UniqueDiffWithinAt ℝ H x := parameterSpace_uniqueDiff (k+1) true x hx
  change exteriorDerivative eta x = exteriorDerivative theta x
  rw [exteriorDerivative_formula, exteriorDerivative_formula]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  have hdeta := isCrForm_coefficient_differentiableAt univ eta heta x (mem_univ _) I
  have hdtheta := isCrForm_coefficient_differentiableAt univ theta htheta x (mem_univ _) I
  have hcoeff : EqOn (fun y => coefficient (standardBasis (k+1)) (eta y) I)
      (fun y => coefficient (standardBasis (k+1)) (theta y) I) H := by
    intro y hy
    exact congrArg (fun a => coefficient (standardBasis (k+1)) a I) (heq hy)
  have hd : fderiv ℝ (fun y => coefficient (standardBasis (k+1)) (eta y) I) x =
      fderiv ℝ (fun y => coefficient (standardBasis (k+1)) (theta y) I) x := by
    rw [← hdeta.fderivWithin hud, ← hdtheta.fderivWithin hud]
    exact fderivWithin_congr hcoeff (hcoeff hx)
  rw [scalarPartialDerivative_eq_fderiv _ _ hdeta,
    scalarPartialDerivative_eq_fderiv _ _ hdtheta, hd]

/-- Every coordinate of the affine derivative has its actual side length. -/
theorem rectangleMap_derivative_apply {k : ℕ} (Q : Darboux.Box k)
    (x v : E k) (j : Fin k) :
    (fderiv ℝ (rectangleMap Q) x v) j = (Q.upper j - Q.lower j) * v j := by
  have hr := ((rectangleMap_C1 Q).differentiable (by norm_num) x).hasFDerivAt
  have hcoord : HasFDerivAt (fun y : E k => rectangleMap Q y j)
      ((Q.upper j - Q.lower j) • (EuclideanSpace.proj j : E k →L[ℝ] ℝ)) x := by
    exact (((EuclideanSpace.proj j : E k →L[ℝ] ℝ)).hasFDerivAt.const_mul (Q.upper j - Q.lower j)).const_add (Q.lower j)
  have hc := (EuclideanSpace.proj j : E k →L[ℝ] ℝ).hasFDerivAt.comp x hr
  have he := congrArg (fun A => A v) (hc.unique hcoord)
  exact he

theorem rectangleMap_derivative_basis {k : ℕ} (Q : Darboux.Box k)
    (x : E k) (i : Fin k) :
    fderiv ℝ (rectangleMap Q) x (standardBasis k i) =
      (Q.upper i - Q.lower i) • standardBasis k i := by
  apply PiLp.ext
  intro j
  rw [rectangleMap_derivative_apply]
  by_cases hij : i = j
  · subst j; simp
  · simp [standardBasis_apply, Ne.symm hij]

/-- Explicit bulk Jacobian bridge for the rescaled C¹ chart cell. -/
theorem rectangle_bulk_coefficient : rectangle_bulk_coefficientType := by
  intro k n Q phi W hW hQ hphi eta x hx
  change pullback (cellExtension _) eta x (fun j => standardBasis k j) = _
  rw [rectangleChartCell_pullback Q phi W hW hQ hphi eta hx,
    rectangle_pullback_comp Q phi W hW hQ hphi eta hx]
  change pullback phi eta (rectangleMap Q x)
    (fun j => fderiv ℝ (rectangleMap Q) x (standardBasis k j)) = _
  simp_rw [rectangleMap_derivative_basis]
  exact (pullback phi eta (rectangleMap Q x)).map_smul_univ
    (fun j => Q.upper j - Q.lower j) (fun j => standardBasis k j)

/-- Explicit face Jacobian bridge; omitted coordinates retain their order. -/
theorem rectangle_face_coefficient : rectangle_face_coefficientType := by
  intro k n Q phi W hW hQ hphi eta i eps x hx
  have ht := Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i eps hx
  rw [rectangleChartCell_pullback Q phi W hW hQ hphi eta ht,
    rectangle_pullback_comp Q phi W hW hQ hphi eta ht]
  change pullback phi eta (rectangleMap Q (faceInsertion i eps x))
    (fun j => fderiv ℝ (rectangleMap Q) (faceInsertion i eps x)
      (standardBasis (k+1) (i.succAbove j))) = _
  simp_rw [rectangleMap_derivative_basis]
  exact (pullback phi eta (rectangleMap Q (faceInsertion i eps x))).map_smul_univ
    (fun j => Q.upper (i.succAbove j) - Q.lower (i.succAbove j))
    (fun j => standardBasis (k+1) (i.succAbove j))

/-- The ambient interior calculation, controlled by support on the chart. -/
theorem ambient_interior_rectangle : ambient_interior_rectangleType := by
  intro k n Q phi W hW hQ hphi V eta heta hmap hs
  apply cell_interior (rectangleChartCell Q phi W hW hQ hphi) V eta heta
    (fun x => hmap (rectangleMap_mem Q x.property))
  intro i eps x hx
  have ht := Specs.D04.C15.CellsChainsAndIntegrals.Model.faceInsertion_mem i eps hx
  rw [rectangleChartCell_pullback Q phi W hW hQ hphi eta ht,
    rectangle_pullback_comp Q phi W hW hQ hphi eta ht]
  have hz : pullback phi eta (rectangleMap Q (faceInsertion i eps x)) = 0 := by
    by_contra hn
    have hi := hs ⟨hn, rectangleMap_mem Q ht⟩ i
    rw [rectangle_face_coordinate] at hi
    cases eps
    · exact lt_irrefl _ hi.1
    · exact lt_irrefl _ hi.2
  simp only [pullback_apply, hz, zero_apply]

/-- The algebraic sign is attached to the actual outward-first tuple. -/
theorem outward_chart_factor : outward_chart_factorType := by
  intro k sigma
  exact congrArg (fun a : ℝ => sigma * a)
    (D04BoundaryOrientation.outward_first_standard_determinant k)

/-- In dimension one the lower face is a signed point, not an empty
orientation-basis convention. A negative bulk chart sign makes it positive. -/
theorem signed_point : signed_pointType := by
  intro Q eta heta hbot hs sigma
  have hface : coordinateFaceIntegral Q eta (Fin.last 0) false =
      eta (WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ))) (fun j => Fin.elim0 j) := by
    change Darboux.lowerIntegral _ _ = _
    rw [(Darboux.zero_dimension _ _).2.2.1]
    have hp : rectangleFacePoint Q (Fin.last 0) false (0 : E 0) =
        WithLp.toLp 2 (fun _ : Fin 1 => (0 : ℝ)) := by
      apply PiLp.ext
      intro j
      have hj : j = Fin.last 0 := Fin.ext (by omega)
      subst j
      simpa only [rectangleFacePoint_same, Bool.false_eq_true, ite_false] using hbot
    rw [hp]
    congr 1
    funext j
    exact Fin.elim0 j
  change sigma * coordinateIntegral Q (exteriorDerivative eta) = _
  rw [coordinate_halfspace Q univ eta heta (subset_univ _) hs, hface]
  simp

/-- Exterior differentiation is local for the actual directional-derivative
selectors, without assuming regularity away from the point. -/
theorem exteriorDerivative_congr_eventuallyEq {n p : ℕ} (eta theta : FormField n p)
    (x : E n) (he : eta =ᶠ[𝓝 x] theta) :
    exteriorDerivative eta x = exteriorDerivative theta x := by
  rw [exteriorDerivative_formula, exteriorDerivative_formula]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change deriv (fun t : ℝ => coefficient (standardBasis n) (eta (x + t • standardBasis n j)) I) 0 =
    deriv (fun t : ℝ => coefficient (standardBasis n) (theta (x + t • standardBasis n j)) I) 0
  apply Filter.EventuallyEq.deriv_eq
  have hl : Tendsto (fun t : ℝ => x + t • standardBasis n j) (𝓝 0) (𝓝 x) := by
    have hcl : Continuous (fun t : ℝ => x + t • standardBasis n j) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have ht := hcl.tendsto 0
    change Tendsto (fun t : ℝ => x + t • standardBasis n j) (𝓝 0)
      (𝓝 (x + (0 : ℝ) • standardBasis n j)) at ht
    simpa only [zero_smul, add_zero] using ht
  exact (he.comp_tendsto hl).mono fun t ht => congrArg (fun a => coefficient (standardBasis n) a I) ht

theorem exteriorDerivative_support {n p : ℕ} (eta : FormField n p) :
    Function.support (exteriorDerivative eta) ⊆ tsupport eta := by
  intro x hx
  by_contra hn
  have he : eta =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  have hz := exteriorDerivative_congr_eventuallyEq eta (fun _ => 0) x he
  rw [exteriorDerivative_const] at hz
  exact hx hz

theorem extendForm_tsupport_subset {n p : ℕ} (U : Set (E n)) (eta : FormField n p)
    (hc : IsCompact (tsupport (fun x : U => eta x))) :
    tsupport (extendForm U eta) ⊆ Subtype.val '' tsupport (fun x : U => eta x) := by
  apply closure_minimal _ (hc.image continuous_subtype_val).isClosed
  intro x hx
  by_cases hxU : x ∈ U
  · refine ⟨⟨x, hxU⟩, subset_tsupport _ ?_, rfl⟩
    simpa only [Function.mem_support, extendForm, Set.indicator_of_mem hxU] using hx
  · exact False.elim (hx (by simp [extendForm, hxU]))

/-- The compact interior formula differentiates precisely the original
coefficients on U and extends their derivatives by zero. -/
theorem extendForm_exteriorDerivative : extendForm_exteriorDerivativeType := by
  intro n p U eta heta hc
  funext x
  by_cases hxU : x ∈ U
  · have he : extendForm U eta =ᶠ[𝓝 x] eta := by
      filter_upwards [heta.1.mem_nhds hxU] with y hy
      simp only [extendForm, Set.indicator_of_mem hy]
    have hd := exteriorDerivative_congr_eventuallyEq (extendForm U eta) eta x he
    simpa only [extendForm, Set.indicator_of_mem hxU] using hd
  · have hs : tsupport (extendForm U eta) ⊆ U := by
      intro y hy
      obtain ⟨z, _, hz⟩ := extendForm_tsupport_subset U eta hc hy
      exact hz ▸ z.property
    have hz : exteriorDerivative (extendForm U eta) x = 0 := by
      by_contra hn
      exact hxU (hs (exteriorDerivative_support _ hn))
    simpa only [extendForm, Set.indicator_of_notMem hxU] using hz

/-- The inward half-space determines all derivative coordinates at the
boundary, so zero relative support also forces zero derivative there. -/
theorem relative_derivative_support : relative_derivative_supportType := by
  intro k p theta ht K hK H hs x hx
  by_contra hxK
  have hud : UniqueDiffWithinAt ℝ H x := parameterSpace_uniqueDiff (k+1) true x hx.2
  have hd (I : MultiIndex (k+1) p) :
      fderiv ℝ (fun y => coefficient (standardBasis (k+1)) (theta y) I) x = 0 := by
    have he : (fun y => coefficient (standardBasis (k+1)) (theta y) I) =ᶠ[𝓝[H] x]
        (fun _ => 0) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hK.isOpen_compl.mem_nhds hxK)] with y hyH hyK
      have hz : theta y = 0 := by
        by_contra hn
        exact hyK (hs ⟨hn, hyH⟩)
      simp [hz, coefficient, Specs.D04.C13.NormalizedFormsAndWedge.Model.coefficient]
    rw [← (isCrForm_coefficient_differentiableAt univ theta ht x (mem_univ _) I).fderivWithin hud,
      he.fderivWithin_eq_of_mem hx.2]
    exact fderivWithin_const_apply 0
  have hz : exteriorDerivative theta x = 0 := by
    rw [exteriorDerivative_formula]
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro j _
    rw [scalarPartialDerivative_eq_fderiv _ _
      (isCrForm_coefficient_differentiableAt univ theta ht x (mem_univ _) I), hd I]
    simp
  exact hx.1 hz

/-- The complete relative half-space assertion. The arbitrary representative
eta is replaced by an actual C¹ extension theta, whose existence is proved. -/
theorem compact_halfspace : compact_halfspaceType := by
  intro k U eta hU H hlocal hc K
  obtain ⟨theta, ht, he⟩ := compact_relative_extension H U eta hU hlocal hc
  have hK : IsCompact K := hc.image continuous_subtype_val
  have hKH : K ⊆ H := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property.2
  have hsTheta : Function.support theta ∩ H ⊆ K := by
    intro x hx
    have heq := he hx.2
    have hxU : x ∈ U := by
      by_contra hn
      exact hx.1 (heq.trans (by simp [extendForm, hn]))
    have hxeta : eta x ≠ 0 := by
      intro hz
      exact hx.1 (heq.trans (by simp [extendForm, hxU, hz]))
    exact ⟨⟨x, hxU, hx.2⟩, subset_tsupport _ hxeta, rfl⟩
  refine ⟨theta, ht, he, relative_derivative_support theta ht K hK.isClosed hsTheta,
    enclose_compact_halfspace K hK hKH, ?_⟩
  intro Q hbot hs
  have hQH : Darboux.carrier Q ⊆ H := by
    intro x hx
    change 0 ≤ x (Fin.last k)
    rw [← hbot]
    exact (hx (Fin.last k)).1
  have hsupport : Function.support theta ∩ Darboux.carrier Q ⊆ halfBoxInterior Q :=
    fun _ hx => hs (hsTheta ⟨hx.1, hQH hx.2⟩)
  refine ⟨derivative_integrable Q theta ht, ?_, ?_⟩
  · apply integrable_rectangle_of_continuous
    exact (form_evaluation_continuous univ theta (form_C0 univ theta ht) _).comp
      (rectangleFacePoint_continuous Q (Fin.last k) false).continuousOn (fun _ _ => mem_univ _)
  · intro sigma
    rw [coordinate_halfspace Q univ theta ht (subset_univ _) hsupport, mul_assoc]

/-- The compact interior theorem in the canonical open-domain Riemann
integral, with no replacement of the original coefficients. -/
theorem compact_interior_openIntegral : compact_interior_openIntegralType := by
  intro k U eta heta hc
  let f : U → ℝ := fun x => exteriorDerivative eta x (fun j => standardBasis (k+1) j)
  let g : E (k+1) → ℝ := fun x => exteriorDerivative (extendForm U eta) x
    (fun j => standardBasis (k+1) j)
  have he : JordanRegions.zeroExtension f = g := by
    funext x
    have hd := congrFun (extendForm_exteriorDerivative U eta heta hc) x
    by_cases hx : x ∈ U
    · simpa only [JordanRegions.zeroExtension,
        Specs.D04.C06.JordanRegions.Model.zeroExtension, f, g, dite_eq_left hx,
        extendForm, Set.indicator_of_mem hx] using
          congrArg (fun a => a (fun j => standardBasis (k+1) j)) hd.symm
    · have hz : exteriorDerivative (extendForm U eta) x = 0 := by
        simpa only [extendForm, Set.indicator_of_notMem hx] using hd
      simp [JordanRegions.zeroExtension, Specs.D04.C06.JordanRegions.Model.zeroExtension,
        hx, g, hz]
  have hs : Function.support g ⊆ tsupport (extendForm U eta) := by
    intro x hx
    apply exteriorDerivative_support (extendForm U eta)
    intro hz
    exact hx (by simp [g, hz])
  have hce := extendForm_compact U eta hc
  obtain ⟨Q, _, hQ⟩ := enclose_compact _ hce
  have henc : JordanRegions.Encloses (Function.support g) Q := by
    change closure (Function.support g) ⊆ interior (Darboux.carrier Q)
    rw [JordanRegions.interior_carrier]
    exact (closure_minimal hs (isClosed_tsupport _)).trans hQ
  have hi : Darboux.Integrable g Q := derivative_integrable Q _ (extendForm_C1 U eta heta hc)
  have hopen : JordanRegions.OpenIntegrable f := by
    refine ⟨heta.1, ?_, Q, ?_, ?_⟩
    · change Bornology.IsBounded (Function.support (JordanRegions.zeroExtension f))
      rw [he]
      exact hce.isBounded.subset hs
    · change JordanRegions.Encloses (Function.support (JordanRegions.zeroExtension f)) Q
      rwa [he]
    · change Darboux.Integrable (JordanRegions.zeroExtension f) Q
      rwa [he]
  refine ⟨hopen, ?_⟩
  obtain ⟨h, hv⟩ := JordanRegions.open_integral_eq_on_enclosing_box f hopen Q (by rwa [he])
  change JordanRegions.openIntegral f = 0
  rw [hv]
  change Darboux.lowerIntegral (JordanRegions.zeroExtension f) Q = 0
  rw [he]
  exact ((compact_interior U eta heta hc).2.2 Q hQ).2

end D04.LocalStokes
