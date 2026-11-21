import MathGenome.Internal.LinearPDE.P201Specs.Heat.ClassicalMaximum
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology ContDiff MatrixOrder
namespace P201.Heat
open P201Specs P201Specs.HeatMaximum

abbrev parabolicBoundary : P201Specs.HeatMaximum.parabolicBoundaryType :=
  @P201Specs.HeatMaximum.parabolicBoundary

/-- A twice differentiable scalar function has nonpositive second derivative
at a local maximum. The positive second derivative test would force it to be
locally both minimal and maximal, hence locally constant. -/
theorem second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hzero : deriv (deriv f) x = 0 := by
    rw [heq.deriv.deriv_eq]
    simp
  linarith

/-- The spatial second differential is nonpositive in every direction at a
local maximum. -/
theorem second_fderiv_nonpos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hm : IsLocalMax f x) (hf : ContDiffAt ℝ 2 f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let line : ℝ → E := fun t => x + t • v
  have hline (t : ℝ) : HasDerivAt line v t := by
    simpa [line] using ((hasDerivAt_id t).smul_const v).const_add x
  have hl0 : line 0 = x := by simp [line]
  have hmline : IsLocalMax (f ∘ line) 0 := by
    apply IsLocalMax.comp_continuous (g := line)
    · simpa [hl0] using hm
    · exact (hline 0).continuousAt
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : deriv (f ∘ line) =ᶠ[𝓝 0] (fun t => fderiv ℝ f (line t) v) := by
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 f (line t) := by
      apply (hline 0).continuousAt.eventually
      simpa [hl0] using hf.eventually (by norm_num)
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hline t)).deriv
  have hsecond : HasDerivAt (fun t => fderiv ℝ f (line t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have hdx : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (line 0) := by
      simpa [hl0] using hd.hasFDerivAt
    have hh := hdx.comp_hasDerivAt 0 (hline 0)
    simpa using hh.clm_apply (hasDerivAt_const 0 v)
  have hvalue : deriv (deriv (f ∘ line)) 0 = fderiv ℝ (fderiv ℝ f) x v v :=
    heq.deriv_eq.trans hsecond.deriv
  rw [← hvalue]
  exact second_deriv_nonpos hmline
    (by
      have hh : ContinuousAt f (line 0) := by simpa [hl0] using hf.continuousAt
      exact hh.comp (hline 0).continuousAt)

/-- Expansion of a bilinear form in the canonical Euclidean coordinates. -/
theorem bilinear_coordinates {n : ℕ}
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) (v : Space n) :
    H v v = ∑ i, ∑ j, v i * v j * H (coordinate n i) (coordinate n j) := by
  have hv : ∑ i : Fin n, v i • coordinate n i = v :=
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Positive semidefinite diffusion contracts a negative semidefinite second
 differential to a nonpositive scalar. No diagonalization of the Hessian is needed. -/
theorem diffusion_nonpos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (H : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (hH : ∀ v, H v v ≤ 0) :
    (∑ i, ∑ j, A i j * H (coordinate n i) (coordinate n j)) ≤ 0 := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hentry (i j : Fin n) : A i j = ∑ k, B k i * B k j := by
    rw [hB]
    simp [Matrix.mul_apply, Matrix.star_eq_conjTranspose]
  simp_rw [hentry, Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ k, (B k i * B k j) * H (coordinate n i) (coordinate n j)) =
        ∑ k, ∑ i, ∑ j, (B k i * B k j) * H (coordinate n i) (coordinate n j) := by
      calc
        _ = ∑ i, ∑ k, ∑ j, (B k i * B k j) * H (coordinate n i) (coordinate n j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
        _ = _ := Finset.sum_comm
    _ ≤ 0 := by
      apply Finset.sum_nonpos
      intro k _
      simpa only [bilinear_coordinates] using hH (WithLp.toLp 2 (fun i => B k i))

theorem admissible_posSemidef {n : ℕ} {Ω : Domain n} {T : ℝ}
    {C : Coefficients n} (hC : Admissible Ω T C) {z : Point n}
    (hz : z ∈ activeCylinder Ω T) : (C.a z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact Matrix.isHermitian_iff_isSymm.mpr (hC.symmetric z hz)
  · intro ξ
    obtain ⟨μ, hμ, he⟩ := hC.elliptic
    have h := he z hz ξ
    have hp : 0 ≤ μ * ∑ i, (ξ i)^2 :=
      mul_nonneg hμ.le (Finset.sum_nonneg fun i _ => sq_nonneg (ξ i))
    have heq : dotProduct (star ξ) (Matrix.mulVec (C.a z) ξ) =
        ∑ i, ∑ j, C.a z i j * ξ i * ξ j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    exact hp.trans h

/-- The derivative from the past is nonnegative at a maximum. The same
statement applies at t=T without assuming a derivative from future times. -/
theorem time_derivative_nonneg {f : ℝ → ℝ} {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T)
    (hm : ∀ s ∈ Icc 0 T, f s ≤ f t)
    (hd : DifferentiableWithinAt ℝ f (Iic T) t) :
    0 ≤ derivWithin f (Iic T) t := by
  have hl : IsLocalMaxOn f (Iic T) t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds] with s hs hs0
    exact hm s ⟨hs0.le, hs⟩
  have htan : (-1 : ℝ) ∈ posTangentConeAt (Iic T) t := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic T).segment_subset htT
    change t + -1 ≤ T
    linarith
  have hh := hl.hasFDerivWithinAt_nonpos hd.hasFDerivWithinAt htan
  have hu := uniqueDiffOn_Iic T t htT
  rw [← hd.hasFDerivWithinAt.fderivWithin hu] at hh
  change (fderivWithin ℝ f (Iic T) t) (-1) ≤ 0 at hh
  have heq : (fderivWithin ℝ f (Iic T) t) (-1) = -derivWithin f (Iic T) t := by
    simp [derivWithin]
  rw [heq] at hh
  linarith

/-- A strict subsolution cannot have a positive maximum away from the
parabolic boundary. Only pointwise positive semidefiniteness is needed. -/
theorem strict_maximum {n : ℕ} {Ω : Domain n} {T : ℝ}
    (hΩ : Bornology.IsBounded (Ω : Set (Space n)))
    (hne : (Ω : Set (Space n)).Nonempty) (hT : 0 < T)
    {C : Coefficients n}
    (hA : ∀ z ∈ activeCylinder Ω T, (C.a z).PosSemidef)
    (hc : ∀ z ∈ activeCylinder Ω T, C.c z ≤ 0)
    {w : Function n} (hw : ContinuousOn w (closedCylinder Ω T))
    (hs : ∀ t ∈ Ioc 0 T, ContDiffOn ℝ 2 (fun x => w (x,t)) Ω)
    (hd : ∀ z ∈ activeCylinder Ω T,
      DifferentiableWithinAt ℝ (fun t => w (z.1,t)) (Iic T) z.2)
    (hL : ∀ z ∈ activeCylinder Ω T, operator C T w z < 0)
    (hb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω T, w z ≤ 0) :
    ∀ z ∈ closedCylinder Ω T, w z ≤ 0 := by
  have hcompact : IsCompact (closedCylinder Ω T) :=
    hΩ.isCompact_closure.prod isCompact_Icc
  have hnonempty : (closedCylinder Ω T).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨(x,0), subset_closure hx, ⟨le_rfl, hT.le⟩⟩
  obtain ⟨z, hz, hm⟩ := hcompact.exists_isMaxOn hnonempty hw
  suffices hnonpos : w z ≤ 0 from fun y hy => (hm hy).trans hnonpos
  by_contra hneg
  have hpos : 0 < w z := lt_of_not_ge hneg
  have hnb : z ∉ P201Specs.HeatMaximum.parabolicBoundary Ω T := by
    intro h
    exact (not_le_of_gt hpos) (hb z h)
  have hx : z.1 ∈ Ω := by
    by_contra hh
    apply hnb
    right
    refine ⟨?_, hz.2⟩
    rw [frontier, Ω.isOpen.interior_eq]
    exact ⟨hz.1, hh⟩
  have ht : 0 < z.2 := by
    have htne : z.2 ≠ 0 := by
      intro hh
      exact hnb (Or.inl ⟨hz.1, hh⟩)
    exact lt_of_le_of_ne hz.2.1 htne.symm
  have hactive : z ∈ activeCylinder Ω T := ⟨hx, ht, hz.2.2⟩
  have hlocal : IsLocalMax (fun x => w (x,z.2)) z.1 := by
    apply IsMaxOn.isLocalMax (s := (Ω : Set (Space n)))
    · intro y hy
      exact hm ⟨subset_closure hy, hz.2⟩
    · exact Ω.isOpen.mem_nhds hx
  have hgrad : spatialFirst w z = 0 := hlocal.fderiv_eq_zero
  have hess : ∀ v, spatialSecond w z v v ≤ 0 :=
    second_fderiv_nonpos hlocal ((hs z.2 ⟨ht,hz.2.2⟩).contDiffAt
      (Ω.isOpen.mem_nhds hx))
  have hdiff := diffusion_nonpos (C.a z) (hA z hactive) (spatialSecond w z) hess
  have htime : 0 ≤ timeDerivative T w z :=
    time_derivative_nonneg ht hz.2.2 (fun s hs => hm ⟨hz.1,hs⟩) (hd z hactive)
  have hzero : (∑ i, C.b z i * spatialFirst w z (coordinate n i)) = 0 := by
    simp [hgrad]
  have hlow : C.c z * w z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hc z hactive) hpos.le
  have hh := hL z hactive
  unfold operator at hh
  rw [hzero] at hh
  linarith

/-- The weak bound with an arbitrary boundary level M. The condition cM≤0
allows both M≥0 and the sharper arbitrary-sign level when c=0. -/
theorem bound_of_boundary_bound {n : ℕ} {Ω : Domain n} {T : ℝ}
    (hΩ : Bornology.IsBounded (Ω : Set (Space n)))
    (hne : (Ω : Set (Space n)).Nonempty) (hT : 0 < T)
    {C : Coefficients n}
    (hA : ∀ z ∈ activeCylinder Ω T, (C.a z).PosSemidef)
    (hc : ∀ z ∈ activeCylinder Ω T, C.c z ≤ 0)
    {u : Function n} (hu : ContinuousOn u (closedCylinder Ω T))
    (hs : ∀ t ∈ Ioc 0 T, ContDiffOn ℝ 2 (fun x => u (x,t)) Ω)
    (hd : ∀ z ∈ activeCylinder Ω T,
      DifferentiableWithinAt ℝ (fun t => u (z.1,t)) (Iic T) z.2)
    (hL : ∀ z ∈ activeCylinder Ω T, operator C T u z ≤ 0)
    (M : ℝ) (hM : ∀ z ∈ activeCylinder Ω T, C.c z * M ≤ 0)
    (hb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω T, u z ≤ M) :
    ∀ z ∈ closedCylinder Ω T, u z ≤ M := by
  intro y hy
  apply le_of_forall_pos_le_add
  intro ε hε
  let e : ℝ := ε / T
  have he : 0 < e := div_pos hε hT
  let w : Function n := fun z => u z - M - e * z.2
  have hw1 : spatialFirst w = spatialFirst u := by
    funext z
    simp [spatialFirst, w, fderiv_sub_const]
  have hw2 : spatialSecond w = spatialSecond u := by
    funext z
    unfold spatialSecond
    rw [hw1]
  have hwt (z : Point n) (hz : z ∈ activeCylinder Ω T) :
      timeDerivative T w z = timeDerivative T u z - e := by
    have hh := ((hd z hz).hasDerivWithinAt.sub_const M).sub
      (((hasDerivAt_id z.2).const_mul e).hasDerivWithinAt)
    have hv := hh.derivWithin (uniqueDiffOn_Iic T z.2 hz.2.2)
    change derivWithin (fun t => u (z.1,t) - M - e*t) (Iic T) z.2 =
      derivWithin (fun t => u (z.1,t)) (Iic T) z.2 - e
    convert hv using 1 <;> first | rfl | simp only [mul_one]
  have hwL : ∀ z ∈ activeCylinder Ω T, operator C T w z < 0 := by
    intro z hz
    have hh := hL z hz
    have hcm := hM z hz
    have hce : C.c z * (e * z.2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hc z hz) (mul_nonneg he.le hz.2.1.le)
    unfold operator at *
    rw [hw1, hw2, hwt z hz]
    dsimp only [w]
    nlinarith
  have hwb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω T, w z ≤ 0 := by
    intro z hz
    have htz : 0 ≤ z.2 := by
      rcases hz with h | h
      · have : z.2 = 0 := h.2
        exact this ▸ le_rfl
      · exact h.2.1
    have hh := hb z hz
    have hh' := mul_nonneg he.le htz
    dsimp only [w]
    linarith
  have hws : ∀ t ∈ Ioc 0 T, ContDiffOn ℝ 2 (fun x => w (x,t)) Ω := by
    intro t ht
    change ContDiffOn ℝ 2 (fun x => u (x,t) - M - e*t) Ω
    exact ((hs t ht).sub contDiffOn_const).sub (contDiffOn_const (c := e*t))
  have hwd : ∀ z ∈ activeCylinder Ω T,
      DifferentiableWithinAt ℝ (fun t => w (z.1,t)) (Iic T) z.2 := by
    intro z hz
    change DifferentiableWithinAt ℝ (fun t => u (z.1,t) - M - e*t) (Iic T) z.2
    exact (((hd z hz).sub (differentiableWithinAt_const M)).sub
      ((differentiableWithinAt_const e).mul differentiableWithinAt_id))
  have hwc : ContinuousOn w (closedCylinder Ω T) :=
    (hu.sub continuousOn_const).sub (continuousOn_const.mul continuousOn_snd)
  have hh := strict_maximum hΩ hne hT hA hc hwc hws hwd hwL hwb y hy
  have hey : e * y.2 ≤ ε := by
    calc
      e * y.2 ≤ e * T := mul_le_mul_of_nonneg_left hy.2.2 he.le
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hT)
  dsimp only [w] at hh
  linarith

theorem boundary_subset_closed {n : ℕ} (Ω : Domain n) {T : ℝ} (hT : 0 ≤ T) :
    P201Specs.HeatMaximum.parabolicBoundary Ω T ⊆ closedCylinder Ω T := by
  intro z hz
  rcases hz with h | h
  · exact ⟨h.1, by simpa only [mem_singleton_iff.mp h.2] using (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)⟩
  · exact ⟨frontier_subset_closure h.1, h.2⟩

theorem boundary_compact {n : ℕ} {Ω : Domain n} (T : ℝ)
    (hΩ : Bornology.IsBounded (Ω : Set (Space n))) :
    IsCompact (P201Specs.HeatMaximum.parabolicBoundary Ω T) := by
  exact (hΩ.isCompact_closure.prod (isCompact_singleton (x := (0 : ℝ)))).union
    ((hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure).prod
      isCompact_Icc)

theorem closed_nonempty {n : ℕ} {Ω : Domain n} {T : ℝ}
    (hne : (Ω : Set (Space n)).Nonempty) (hT : 0 ≤ T) :
    (closedCylinder Ω T).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨(x,0), subset_closure hx, le_rfl, hT⟩

/-- On a compact nonempty set our supremum notation denotes an attained
maximum, as in the source's displayed formulas. -/
theorem maximum_attained {n : ℕ} (u : Function n) {S : Set (Point n)}
    (hS : IsCompact S) (hne : S.Nonempty) (hu : ContinuousOn u S) :
    ∃ z ∈ S, u z = P201Specs.HeatMaximum.maximum u S := by
  exact hS.image_of_continuousOn hu |>.sSup_mem (hne.image u)

theorem maximum : P201Specs.HeatMaximum.maximumStatement := by
  intro n hn Ω T hΩ hne hT C hC u hu hL
  have hbdd : BddAbove (u '' P201Specs.HeatMaximum.parabolicBoundary Ω T) :=
    ((boundary_compact T hΩ).image_of_continuousOn
      (hu.continuous.mono (boundary_subset_closed Ω hT.le))).bddAbove
  have hb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω T,
      u z ≤ max 0 (P201Specs.HeatMaximum.maximum u
        (P201Specs.HeatMaximum.parabolicBoundary Ω T)) := by
    intro z hz
    exact (le_csSup hbdd ⟨z,hz,rfl⟩).trans (le_max_right _ _)
  have hbound := bound_of_boundary_bound hΩ hne hT
    (fun z hz => admissible_posSemidef hC hz) hC.nonpositive
    hu.continuous hu.spatial hu.temporal hL
    (max 0 (P201Specs.HeatMaximum.maximum u
      (P201Specs.HeatMaximum.parabolicBoundary Ω T)))
    (fun z hz => mul_nonpos_of_nonpos_of_nonneg (hC.nonpositive z hz) (le_max_left _ _)) hb
  apply csSup_le ((closed_nonempty hne hT.le).image u)
  rintro r ⟨z,hz,rfl⟩
  exact hbound z hz

theorem maximum_zero : P201Specs.HeatMaximum.maximumZeroStatement := by
  intro n hn Ω T hΩ hne hT C hC hc u hu hL
  have hbdd : BddAbove (u '' P201Specs.HeatMaximum.parabolicBoundary Ω T) :=
    ((boundary_compact T hΩ).image_of_continuousOn
      (hu.continuous.mono (boundary_subset_closed Ω hT.le))).bddAbove
  have hb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω T,
      u z ≤ P201Specs.HeatMaximum.maximum u
        (P201Specs.HeatMaximum.parabolicBoundary Ω T) := by
    intro z hz
    exact le_csSup hbdd ⟨z,hz,rfl⟩
  have hbound := bound_of_boundary_bound hΩ hne hT
    (fun z hz => admissible_posSemidef hC hz) hC.nonpositive
    hu.continuous hu.spatial hu.temporal hL
    (P201Specs.HeatMaximum.maximum u (P201Specs.HeatMaximum.parabolicBoundary Ω T))
    (fun z hz => by rw [hc z hz]; simp) hb
  apply csSup_le ((closed_nonempty hne hT.le).image u)
  rintro r ⟨z,hz,rfl⟩
  exact hbound z hz

/-- Linearity of the nondivergence operator on classical functions. -/
theorem operator_sub {n : ℕ} {Ω : Domain n} {T : ℝ}
    (C : Coefficients n) {u v : Function n}
    (hu : Classical Ω T u) (hv : Classical Ω T v)
    {z : Point n} (hz : z ∈ activeCylinder Ω T) :
    operator C T (fun y => u y - v y) z = operator C T u z - operator C T v z := by
  let w : Function n := fun y => u y - v y
  have hxu : ContDiffAt ℝ 2 (fun x => u (x,z.2)) z.1 :=
    (hu.spatial z.2 hz.2).contDiffAt (Ω.isOpen.mem_nhds hz.1)
  have hxv : ContDiffAt ℝ 2 (fun x => v (x,z.2)) z.1 :=
    (hv.spatial z.2 hz.2).contDiffAt (Ω.isOpen.mem_nhds hz.1)
  have hfirst (x : Space n) (hx : x ∈ Ω) :
      spatialFirst w (x,z.2) = spatialFirst u (x,z.2) - spatialFirst v (x,z.2) := by
    apply fderiv_sub
    · exact ((hu.spatial z.2 hz.2).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt
        (by norm_num)
    · exact ((hv.spatial z.2 hz.2).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt
        (by norm_num)
  have heq : (fun x => spatialFirst w (x,z.2)) =ᶠ[𝓝 z.1]
      (fun x => spatialFirst u (x,z.2) - spatialFirst v (x,z.2)) := by
    filter_upwards [Ω.isOpen.mem_nhds hz.1] with x hx
    exact hfirst x hx
  have hsecond : spatialSecond w z = spatialSecond u z - spatialSecond v z := by
    unfold spatialSecond
    rw [heq.fderiv_eq]
    exact fderiv_sub
      ((hxu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hxv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have ht : timeDerivative T w z = timeDerivative T u z - timeDerivative T v z := by
    exact ((hu.temporal z hz).hasDerivWithinAt.sub (hv.temporal z hz).hasDerivWithinAt).derivWithin
      (uniqueDiffOn_Iic T z.2 hz.2.2)
  change operator C T w z = _
  unfold operator
  rw [hsecond, ht, show spatialFirst w z = spatialFirst u z - spatialFirst v z from hfirst z.1 hz.1]
  simp only [sub_apply, mul_sub, Finset.sum_sub_distrib, w]
  ring

theorem comparison : P201Specs.HeatMaximum.comparisonStatement := by
  intro n hn Ω T hΩ hne hT C hC u v hu hv hL hb
  have hwc : ContinuousOn (fun y => u y - v y) (closedCylinder Ω T) :=
    hu.continuous.sub hv.continuous
  have hws : ∀ t ∈ Ioc 0 T, ContDiffOn ℝ 2 (fun x => u (x,t) - v (x,t)) Ω :=
    fun t ht => (hu.spatial t ht).sub (hv.spatial t ht)
  have hwd : ∀ z ∈ activeCylinder Ω T,
      DifferentiableWithinAt ℝ (fun t => u (z.1,t) - v (z.1,t)) (Iic T) z.2 :=
    fun z hz => (hu.temporal z hz).sub (hv.temporal z hz)
  have hwL : ∀ z ∈ activeCylinder Ω T, operator C T (fun y => u y - v y) z ≤ 0 := by
    intro z hz
    rw [operator_sub C hu hv hz]
    exact sub_nonpos.mpr (hL z hz)
  have hwb : ∀ z ∈ P201Specs.HeatMaximum.parabolicBoundary Ω T, u z - v z ≤ 0 :=
    fun z hz => sub_nonpos.mpr (hb z hz)
  have hbound := bound_of_boundary_bound hΩ hne hT
    (fun z hz => admissible_posSemidef hC hz) hC.nonpositive
    hwc hws hwd hwL 0 (fun z hz => by simp) hwb
  intro z hz
  exact sub_nonpos.mp (hbound z hz)

theorem uniqueness : P201Specs.HeatMaximum.uniquenessStatement := by
  intro n hn Ω T hΩ hne hT C hC u v hu hv hL hb
  have huv := comparison hn Ω T hΩ hne hT C hC u v hu hv
    (fun z hz => (hL z hz).le) (fun z hz => (hb z hz).le)
  have hvu := comparison hn Ω T hΩ hne hT C hC v u hv hu
    (fun z hz => (hL z hz).ge) (fun z hz => (hb z hz).ge)
  intro z hz
  exact le_antisymm (huv z hz) (hvu z hz)

end P201.Heat
