import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ActiveConstraints
import MathGenome.Internal.MultivariableAnalysis.D04.C05.ActiveConstraintCoordinates
import MathGenome.Internal.MultivariableAnalysis.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.Ext
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.ActiveConstraints
open Specs.D04.C05.ActiveConstraintCoordinates
open Specs.D04.C05.ActiveConstraints

/-- The positive orthant condition on the active block; the equality block
is fixed and the final block is free. -/
private def coordinateFeasible {ι κ W : Type}
    (y : (ι → ℝ) × ((κ → ℝ) × W)) : Prop :=
  y.1 = 0 ∧ ∀ i, 0 ≤ y.2.1 i

private theorem orthant_derivative {ι κ W : Type} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : ((ι → ℝ) × ((κ → ℝ) × W)) → ℝ)
    (d : ((ι → ℝ) × ((κ → ℝ) × W)) →L[ℝ] ℝ) (w : W)
    (hd : HasFDerivAt F d (0, (0, w)))
    (hm : IsLocalMinOn F {y | coordinateFeasible y} (0, (0, w))) :
    ∃ (lam : ι → ℝ) (μ : κ → ℝ), (∀ i, 0 ≤ μ i) ∧
      ∀ y, d y = (∑ j, lam j * y.1 j) + ∑ i, μ i * y.2.1 i := by
  classical
  have ht (v : (ι → ℝ) × ((κ → ℝ) × W))
      (hu : v.1 = 0) (hv : ∀ i, 0 ≤ v.2.1 i) :
      v ∈ posTangentConeAt {y | coordinateFeasible y} (0, (0, w)) := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    apply (hp.mono ?_).frequently
    intro t ht
    constructor
    · simp [hu]
    · intro i
      simpa using mul_nonneg ht.le (hv i)
  have hz (z : W) : d (0, (0, z)) = 0 := by
    apply hm.hasFDerivWithinAt_eq_zero hd.hasFDerivWithinAt
    · exact ht _ rfl (fun _ => le_rfl)
    · exact ht _ (by simp) (fun _ => by simp)
  let lam : ι → ℝ := fun j => d (Pi.single j 1, (0, 0))
  let μ : κ → ℝ := fun i => d (0, (Pi.single i 1, 0))
  refine ⟨lam, μ, ?_, ?_⟩
  · intro i
    apply hm.hasFDerivWithinAt_nonneg hd.hasFDerivWithinAt
    exact ht _ rfl (fun j => by simp [Pi.single_apply]; split_ifs <;> norm_num)
  · rintro ⟨u,v,z⟩
    have hu : (u, (0, (0 : W))) = ∑ j : ι, u j • (Pi.single j 1, ((0 : κ → ℝ), (0 : W))) := by
      ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    have hv : ((0 : ι → ℝ), (v, (0 : W))) =
        ∑ i : κ, v i • ((0 : ι → ℝ), (Pi.single i 1, (0 : W))) := by
      ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    have he : (u, (v,z)) = (u, (0, (0 : W))) + (0, (v, 0)) + (0, (0, z)) := by simp
    conv_lhs => rw [he]
    rw [map_add, map_add, hz, add_zero, hu, hv, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, lam, μ]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Independence makes the coefficient representation unique. The joint row
map is onto even when either finite index set is empty. -/
theorem multiplier_unique {n q s : ℕ} (f : E n → ℝ)
    (g : E n → E q) (h : E n → E s) (a : E n)
    (hli : LinearIndependent ℝ (constraintRows g h a))
    {p p' : (Fin q → ℝ) × (Active h a → ℝ)}
    (hp : MultiplierEquation f g h a p)
    (hp' : MultiplierEquation f g h a p') : p = p' := by
  classical
  let R : E n →ₗ[ℝ] ((Fin q ⊕ Active h a) → ℝ) :=
    LinearMap.pi (constraintRows g h a)
  have hR : Function.Surjective R := by
    apply rows_surjective
    convert hli using 1
    rfl
  have he (y : (Fin q ⊕ Active h a) → ℝ) :
      (∑ j, p.1 j * y (.inl j)) + (∑ i, p.2 i * y (.inr i)) =
      (∑ j, p'.1 j * y (.inl j)) + ∑ i, p'.2 i * y (.inr i) := by
    obtain ⟨v, hv⟩ := hR y
    have hgj (j : Fin q) : totalDerivative (fun x => g x j) a v = y (.inl j) :=
      congrFun hv (.inl j)
    have hhi (i : Active h a) : totalDerivative (fun x => h x i.val) a v = y (.inr i) :=
      congrFun hv (.inr i)
    have heq := (hp.2 v).symm.trans (hp'.2 v)
    change (∑ j, p.1 j * totalDerivative (fun x => g x j) a v) +
      (∑ i : Active h a, p.2 i * totalDerivative (fun x => h x i.val) a v) =
      (∑ j, p'.1 j * totalDerivative (fun x => g x j) a v) +
      (∑ i : Active h a, p'.2 i * totalDerivative (fun x => h x i.val) a v) at heq
    simpa only [hgj, hhi] using heq
  apply Prod.ext
  · funext j
    simpa [Pi.single_apply] using he (Pi.single (.inl j) 1)
  · funext i
    simpa [Pi.single_apply] using he (Pi.single (.inr i) 1)

private theorem c1_derivative {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {U : Set X} {f : X → Y} {a : X} (hU : IsOpen U) (hf : CrOn 1 U f) (ha : a ∈ U) :
    HasFDerivAt f (totalDerivative f a) a := by
  exact (((crOn_iff_contDiffOn 1 U f hU).mp hf).contDiffAt
    (hU.mem_nhds ha)).differentiableAt (by norm_num) |>.hasFDerivAt

private theorem component_derivative {n m : ℕ} {U : Set (E n)}
    {f : E n → E m} {a : E n} (hU : IsOpen U) (hf : CrOn 1 U f) (ha : a ∈ U)
    (j : Fin m) : HasFDerivAt (fun x => f x j) (totalDerivative (fun x => f x j) a) a := by
  have hc := (contDiffOn_piLp 2).mp ((crOn_iff_contDiffOn 1 U f hU).mp hf) j
  exact (hc.contDiffAt (hU.mem_nhds ha)).differentiableAt (by norm_num) |>.hasFDerivAt

end D04.ActiveConstraints

namespace D04
open Specs.D04.C05.ActiveConstraintCoordinates
open Specs.D04.C05.ActiveConstraints
open ActiveConstraints

theorem active_constraints_minimum :
    Specs.D04.C05.ActiveConstraints.active_constraints_minimumType := by
  classical
  intro n q s U f g h c a hU hf hg hh hli hm
  have haS : a ∈ Feasible U g h c := hm.1
  obtain ⟨k, w, X, A, B, C, inv, hchart⟩ :=
    active_constraint_coordinates 1 U g h c a (by norm_num) hU hg hh
      haS.1 haS.2.1 haS.2.2 hli
  rcases hchart with ⟨hdim, hX, hA, hB, hC, haX, h0A, h0B, hwC, hXU,
    hφa, hbij, hInv, hleft, hright, hφCr, hInvCr, hpos, hfeas, hfeasInv⟩
  let φ := coordinateMap g h c a w
  let Y := A ×ˢ (B ×ˢ C)
  let y0 : (Fin q → ℝ) × ((Active h a → ℝ) × E k) := (0, (0, w a))
  have hY : IsOpen Y := hA.prod (hB.prod hC)
  have hy0 : y0 ∈ Y := ⟨h0A, h0B, hwC⟩
  have hIa : inv y0 = a := by change inv (0, (0, w a)) = a; rw [← hφa]; exact hleft haX
  have hdI := c1_derivative hY hInvCr hy0
  have hdf := c1_derivative hU hf haS.1
  have hdg := component_derivative hU hg haS.1
  have hdh := component_derivative hU hh haS.1
  let P := (ContinuousLinearMap.pi (fun j : Fin q =>
      totalDerivative (fun x => g x j) a)).prod
    ((ContinuousLinearMap.pi (fun i : Active h a =>
      totalDerivative (fun x => h x i.val) a)).prod w.toContinuousLinearMap)
  have hdφ : HasFDerivAt φ P a :=
    (hasFDerivAt_pi.mpr (fun j => (hdg j).sub_const (c j))).prodMk
      ((hasFDerivAt_pi.mpr (fun i : Active h a => hdh i.val)).prodMk
        w.toContinuousLinearMap.hasFDerivAt)
  let d := (totalDerivative f a).comp (totalDerivative inv y0)
  have hdF : HasFDerivAt (f ∘ inv) d y0 := by
    have hdff : HasFDerivAt f (totalDerivative f a) (inv y0) := by rwa [hIa]
    exact hdff.comp y0 hdI
  have ht : Tendsto inv (𝓝[{y | ActiveConstraints.coordinateFeasible y}] y0)
      (𝓝[Feasible U g h c] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [hIa] using hdI.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · have heY : ∀ᶠ y in 𝓝[{y | ActiveConstraints.coordinateFeasible y}] y0, y ∈ Y :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (hY.mem_nhds hy0)
      filter_upwards [heY, self_mem_nhdsWithin] with y hy hK
      exact (hfeasInv y hy).mpr hK
  have hmF : IsLocalMinOn (f ∘ inv) {y | ActiveConstraints.coordinateFeasible y} y0 := by
    have hb := ht.eventually ((localMinimumOn_iff (Feasible U g h c) f a).mp hm).2
    simpa only [IsLocalMinOn, IsMinFilter, Function.comp_apply, hIa] using hb
  obtain ⟨lam, μ, hμ, he⟩ := ActiveConstraints.orthant_derivative (f ∘ inv) d (w a) hdF hmF
  have hchain : totalDerivative f a = d.comp P := by
    have hhcomp : HasFDerivAt ((f ∘ inv) ∘ φ) (d.comp P) a := by
      apply HasFDerivAt.comp a _ hdφ
      simpa only [φ, hφa] using hdF
    have hhf : HasFDerivAt f (d.comp P) a := by
      apply hhcomp.congr_of_eventuallyEq
      filter_upwards [hX.mem_nhds haX] with x hx
      simp only [Function.comp_apply, φ, hleft hx]
    exact hhf.fderiv
  have hp : MultiplierEquation f g h a (lam, μ) := by
    refine ⟨hμ, fun v => ?_⟩
    change totalDerivative f a v = _
    rw [hchain]
    exact he (P v)
  exact ⟨(lam, μ), hp, fun p hp' => multiplier_unique f g h a hli hp' hp⟩

private theorem extended_sum {n s : ℕ} (h : E n → E s) (a : E n)
    (μ : Active h a → ℝ) (t : Fin s → ℝ) :
    (∑ i, extendMultiplier h a μ i * t i) = ∑ i : Active h a, μ i * t i.val := by
  classical
  apply Finset.sum_congr_set {i | h a i = 0}
  · intro i hi
    change h a i = 0 at hi
    simp [extendMultiplier, hi]
  · intro i hi
    change h a i ≠ 0 at hi
    simp [extendMultiplier, hi]

theorem active_constraints_extension :
    Specs.D04.C05.ActiveConstraints.active_constraints_extensionType := by
  classical
  intro n q s U f g h a p hU ha hf hg hh hp
  let μ := extendMultiplier h a p.2
  have hμ (i : Fin s) : 0 ≤ μ i := by
    dsimp [μ, extendMultiplier]
    split_ifs with hi
    · exact hp.1 ⟨i, hi⟩
    · exact le_rfl
  have hinactive (i : Fin s) (hi : h a i ≠ 0) : μ i = 0 := by
    simp [μ, extendMultiplier, hi]
  have hcomp (i : Fin s) : μ i * h a i = 0 := by
    by_cases hi : h a i = 0
    · simp [hi]
    · rw [hinactive i hi, zero_mul]
  have heq (v : E n) : totalDerivative f a v =
      (∑ j, p.1 j * totalDerivative (fun x => g x j) a v) +
      ∑ i, μ i * totalDerivative (fun x => h x i) a v := by
    rw [show (∑ i, μ i * totalDerivative (fun x => h x i) a v) =
      ∑ i : Active h a, p.2 i * totalDerivative (fun x => h x i.val) a v from
        extended_sum h a p.2 (fun i => totalDerivative (fun x => h x i) a v)]
    exact hp.2 v
  refine ⟨hμ, hinactive, hcomp, heq, ?_⟩
  apply (hasTotalDerivative_iff_hasFDerivAt U _ 0 a hU ha).mpr
  have hdf := c1_derivative hU hf ha
  have hdg := component_derivative hU hg ha
  have hdh := component_derivative hU hh ha
  have hd := (hdf.sub (HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (hdg j).const_mul (p.1 j)))).sub
      (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hdh i).const_mul (μ i)))
  have hz : totalDerivative f a - (∑ j, p.1 j • totalDerivative (fun x => g x j) a) -
      (∑ i, μ i • totalDerivative (fun x => h x i) a) = 0 := by
    ext v
    simp only [sub_apply, sum_apply,
      smul_apply, smul_eq_mul, zero_apply]
    rw [heq]
    ring
  rw [hz] at hd
  exact hd

theorem active_constraints_maximum :
    Specs.D04.C05.ActiveConstraints.active_constraints_maximumType := by
  intro n q s U f g h c a hU hf hg hh hli hm
  have hfn : CrOn 1 U (fun x => -f x) :=
    (crOn_iff_contDiffOn 1 U _ hU).mpr (((crOn_iff_contDiffOn 1 U f hU).mp hf).neg)
  have hmn : LocalMinimumOn (Feasible U g h c) (fun x => -f x) a := by
    rcases hm with ⟨ha, r, hr, hb⟩
    exact ⟨ha, r, hr, fun x hx hxr => neg_le_neg (hb x hx hxr)⟩
  exact active_constraints_minimum U (fun x => -f x) g h c a hU hfn hg hh hli hmn

theorem active_constraints_no_active :
    Specs.D04.C05.ActiveConstraints.active_constraints_no_activeType := by
  classical
  intro n q s U f g h c a hU hf hg hh hli hnone hm
  have : IsEmpty (Active h a) := ⟨fun i => hnone i.val i.property⟩
  have hmin : ∀ F : E n → ℝ, CrOn 1 U F →
      LocalMinimumOn (Feasible U g h c) F a →
      ∃! lam : Fin q → ℝ, ∀ v : E n,
        totalDerivative F a v = ∑ j, lam j * totalDerivative (fun x => g x j) a v := by
    intro F hF hmF
    obtain ⟨p, hp, hup⟩ := active_constraints_minimum U F g h c a hU hF hg hh hli hmF
    refine ⟨p.1, ?_, ?_⟩
    · intro v
      simpa [D04.totalDerivative, Specs.D04.C02.DerivativeInterfaces.totalDerivativeValue] using hp.2 v
    · intro lam hlam
      have he : (lam, p.2) = p := by
        apply hup
        exact ⟨hp.1, fun v => by simpa [D04.totalDerivative, Specs.D04.C02.DerivativeInterfaces.totalDerivativeValue] using hlam v⟩
      exact congrArg Prod.fst he
  rcases hm with hm | hm
  · exact hmin f hf hm
  · have hfn : CrOn 1 U (fun x => -f x) :=
      (crOn_iff_contDiffOn 1 U _ hU).mpr (((crOn_iff_contDiffOn 1 U f hU).mp hf).neg)
    have hmn : LocalMinimumOn (Feasible U g h c) (fun x => -f x) a := by
      rcases hm with ⟨ha, r, hr, hb⟩
      exact ⟨ha, r, hr, fun x hx hxr => neg_le_neg (hb x hx hxr)⟩
    obtain ⟨lam, hlam, hu⟩ := hmin (fun x => -f x) hfn hmn
    have hdf := c1_derivative hU hf hmn.1.1
    have hneg : totalDerivative (fun x => -f x) a = -totalDerivative f a := hdf.neg.fderiv
    refine ⟨fun j => -lam j, ?_, ?_⟩
    · intro v
      change totalDerivative f a v = ∑ j, (-lam j) * totalDerivative (fun x => g x j) a v
      have he := hlam v
      rw [hneg] at he
      simp only [neg_apply] at he
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
    · intro lam' hlam'
      change ∀ v : E n, totalDerivative f a v = ∑ j, lam' j * totalDerivative (fun x => g x j) a v at hlam'
      have hu' : (fun j => -lam' j) = lam := by
        apply hu
        intro v
        rw [hneg]
        simp only [neg_apply, neg_mul, Finset.sum_neg_distrib, hlam' v]
      funext j
      have hej := congrFun hu' j
      change -lam' j = lam j at hej
      linarith

end D04
