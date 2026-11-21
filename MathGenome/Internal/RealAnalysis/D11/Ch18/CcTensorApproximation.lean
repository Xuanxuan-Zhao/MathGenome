import MathGenome.Internal.RealAnalysis.D11.Ch19.FiniteCompactPartition
import MathGenome.Internal.RealAnalysis.D11.Ch08.ProductSigma
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.CcTensorApproximation
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

namespace D11.Ch18.CcTensorApproximation
universe u v w
open Set Filter
open scoped BigOperators Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  {𝕜 : Type w} [RCLike 𝕜]

omit [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
/-- A section has compact support in the original first factor. -/
private theorem section_support (f : D11.Ch19.Cc (X × Y) 𝕜) (y : Y) :
    tsupport (fun x => f (x,y)) ⊆ Prod.fst '' tsupport f := by
  apply closure_minimal
  · intro x hx
    exact ⟨(x,y), subset_tsupport f hx, rfl⟩
  · exact (f.hasCompactSupport.image continuous_fst).isClosed

private def ccSection (f : D11.Ch19.Cc (X × Y) 𝕜) (y : Y) : D11.Ch19.Cc X 𝕜 where
  toFun x := f (x,y)
  continuous_toFun := f.continuous.comp (continuous_id.prodMk continuous_const)
  hasCompactSupport' := (f.hasCompactSupport.image continuous_fst).of_isClosed_subset
    (isClosed_tsupport _) (section_support f y)

omit [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
/-- Compactness of the first support projection upgrades continuity in the second
variable to locally uniform continuity of the entire sections. -/
private theorem section_neighborhood (f : D11.Ch19.Cc (X × Y) 𝕜)
    (y : Y) (η : ℝ) (hη : 0 < η) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      ∀ z ∈ V, ∀ x : X, ‖f (x,z) - f (x,y)‖ < η := by
  let K := Prod.fst '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_fst
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : C(Y × K, 𝕜) :=
    ⟨fun p => f (p.2.1, p.1),
      f.continuous.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)⟩
  let V : Set Y := {z | dist (F.curry z) (F.curry y) < η}
  refine ⟨V, isOpen_lt (F.curry.continuous.dist continuous_const) continuous_const, ?_, ?_⟩
  · change dist (F.curry y) (F.curry y) < η
    simpa using hη
  · intro z hz x
    by_cases hx : x ∈ K
    · have h := lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist
        (f := F.curry z) (g := F.curry y) (⟨x,hx⟩ : K)) hz
      simpa only [ContinuousMap.curry_apply, F, ContinuousMap.coe_mk, dist_eq_norm] using h
    · have hzero (z : Y) : f (x,z) = 0 := by
        by_contra hn
        exact hx ⟨(x,z), subset_tsupport f hn, rfl⟩
      simp [hzero, hη]

/-- Casting real partition weights preserves compact support. -/
private def scalarWeight (φ : D11.Ch19.Cc Y ℝ) : D11.Ch19.Cc Y 𝕜 where
  toFun y := (φ y : 𝕜)
  continuous_toFun := RCLike.continuous_ofReal.comp φ.continuous
  hasCompactSupport' := φ.hasCompactSupport.comp_left (by simp)

omit [T2Space X] [LocallyCompactSpace X] [T2Space Y] [LocallyCompactSpace Y] in
private theorem tensor_support (g : D11.Ch19.Cc X 𝕜) (h : D11.Ch19.Cc Y 𝕜) :
    tsupport (fun p : X × Y => g p.1 * h p.2) ⊆ tsupport g ×ˢ tsupport h := by
  apply closure_minimal _ ((isClosed_tsupport g).prod (isClosed_tsupport h))
  intro p hp
  exact ⟨subset_tsupport g (left_ne_zero_of_mul hp),
    subset_tsupport h (right_ne_zero_of_mul hp)⟩

omit [LocallyCompactSpace X] in
/-- Approximate using sections and a finite partition in the second variable.
The neighborhoods O and P are fixed parameters throughout this construction. -/
private theorem approximation_on (f : D11.Ch19.Cc (X × Y) 𝕜)
    (O : Set X) (P : Set Y) (hP : IsOpen P)
    (hO : Prod.fst '' tsupport f ⊆ O) (hLP : Prod.snd '' tsupport f ⊆ P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (g : Fin n → D11.Ch19.Cc X 𝕜)
      (h : Fin n → D11.Ch19.Cc Y 𝕜),
      (∀ j, tsupport (g j) ⊆ O) ∧ (∀ j, tsupport (h j) ⊆ P) ∧
      tsupport (fun p : X × Y => ∑ j, g j p.1 * h j p.2) ⊆ O ×ˢ P ∧
      ∀ p : X × Y, ‖f p - ∑ j, g j p.1 * h j p.2‖ ≤ ε / 2 := by
  classical
  let L := Prod.snd '' tsupport f
  have hL : IsCompact L := f.hasCompactSupport.image continuous_snd
  choose V hVo hyV hV using fun y : Y => section_neighborhood f y (ε / 2) (half_pos hε)
  obtain ⟨s, hs⟩ := hL.elim_finite_subcover (fun y : L => V y ∩ P)
    (fun y => (hVo y).inter hP) (by
      intro y hy
      exact mem_iUnion.mpr ⟨⟨y, hy⟩, hyV y, hLP hy⟩)
  let n := Fintype.card s
  let e : Fin n ≃ s := (Fintype.equivFin s).symm
  let c (j : Fin n) : Y := (e j).1.1
  let U (j : Fin n) : Set Y := V (c j) ∩ P
  have hcover : L ⊆ ⋃ j, U j := by
    intro y hy
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hs hy)
    obtain ⟨has, hya⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨e.symm ⟨a,has⟩, by simpa [U, c] using hya⟩
  obtain ⟨φ, hφ, hφU, hφsum, hφle⟩ :=
    D11.Ch19.finite_compact_partition Y (Fin n) L U hL
      (fun j => (hVo (c j)).inter hP) hcover
  let g (j : Fin n) := ccSection f (c j)
  let h (j : Fin n) : D11.Ch19.Cc Y 𝕜 := scalarWeight (φ j)
  have hg (j : Fin n) : tsupport (g j) ⊆ O := (section_support f (c j)).trans hO
  have hh (j : Fin n) : tsupport (h j) ⊆ tsupport (φ j) := by
    apply tsupport_comp_subset (g := (fun r : ℝ => (r : 𝕜))) (by simp)
  have hhP (j : Fin n) : tsupport (h j) ⊆ P :=
    (hh j).trans ((hφU j).trans inter_subset_right)
  refine ⟨n, g, h, hg, hhP, ?_, ?_⟩
  · have hts : tsupport (fun p : X × Y => ∑ j, g j p.1 * h j p.2) ⊆
          ⋃ j, tsupport (fun p : X × Y => g j p.1 * h j p.2) := by
      apply closure_minimal _ (isClosed_iUnion_of_finite fun j => isClosed_tsupport _)
      intro p hp
      obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact mem_iUnion.mpr ⟨j, subset_tsupport _ hj⟩
    exact hts.trans (iUnion_subset fun j =>
      (tensor_support (g j) (h j)).trans (Set.prod_mono (hg j) (hhP j)))
  · intro p
    have hsum : f p * ∑ j, (φ j p.2 : 𝕜) = f p := by
      by_cases hp : f p = 0
      · simp [hp]
      · have hpL : p.2 ∈ L := ⟨p, subset_tsupport f hp, rfl⟩
        rw [← RCLike.ofReal_sum, hφsum p.2 hpL]
        simp
    have hid : f p - ∑ j, g j p.1 * h j p.2 =
        ∑ j, (f p - f (p.1,c j)) * (φ j p.2 : 𝕜) := by
      change f p - ∑ j, f (p.1,c j) * (φ j p.2 : 𝕜) = _
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hsum]
    rw [hid]
    calc
      _ ≤ ∑ j, ‖(f p - f (p.1,c j)) * (φ j p.2 : 𝕜)‖ := norm_sum_le _ _
      _ ≤ ∑ j, (ε / 2) * φ j p.2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hφ j p.2).1]
        by_cases hj : φ j p.2 = 0
        · simp [hj]
        · have hpU := hφU j (subset_tsupport (φ j) hj)
          exact mul_le_mul_of_nonneg_right (le_of_lt (hV (c j) p.2 hpU.1 p.1)) (hφ j p.2).1
      _ = (ε / 2) * ∑ j, φ j p.2 := (Finset.mul_sum _ _ _).symm
      _ ≤ ε / 2 := mul_le_of_le_one_right (half_pos hε).le (hφle p.2)

/-- The support projections have open neighborhoods with compact closures;
these are chosen once, independently of every requested approximation error. -/
theorem tensor_approximation : Specs.D11.Ch18.CcTensorApproximation.tensor_approximation := by
  intro X _ _ _ Y _ _ _ 𝕜 _ f
  have hK := f.hasCompactSupport.image continuous_fst
  have hL := f.hasCompactSupport.image continuous_snd
  obtain ⟨A, hA, hKA, _⟩ := exists_compact_between hK isOpen_univ (subset_univ _)
  obtain ⟨B, hB, hLB, _⟩ := exists_compact_between hL isOpen_univ (subset_univ _)
  let O := interior A
  let P := interior B
  have hcO : IsCompact (closure O) :=
    hA.of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset hA.isClosed)
  have hcP : IsCompact (closure P) :=
    hB.of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset hB.isClosed)
  refine ⟨O, P, isOpen_interior, isOpen_interior, hcO, hcP, ?_, ?_⟩
  · intro p hp
    exact ⟨hKA ⟨p,hp,rfl⟩, hLB ⟨p,hp,rfl⟩⟩
  · intro ε hε
    obtain ⟨n,g,h,hg,hh,hs,herr⟩ := approximation_on f O P isOpen_interior hKA hLB ε hε
    exact ⟨n,g,h,ε/2,hg,hh,hs,(half_pos hε).le,half_lt_self hε,herr⟩

/-- Sequential tensor approximation proves measurability for the factor Borel
product, without identifying that product with the product topology's Borel space. -/
theorem product_borel_measurable :
    Specs.D11.Ch18.CcTensorApproximation.product_borel_measurable := by
  intro X _ _ _ Y _ _ _ 𝕜 _ f
  classical
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  let : MeasurableSpace Y := borel Y
  have : BorelSpace Y := ⟨rfl⟩
  obtain ⟨O,P,_,_,_,_,_,happ⟩ := tensor_approximation X Y 𝕜 f
  have happn (k : ℕ) := happ (1 / ((k : ℝ) + 1)) (by positivity)
  choose n g h δ hg hh hs hδ hδε herr using happn
  let F (k : ℕ) (p : X × Y) : 𝕜 := ∑ j, g k j p.1 * h k j p.2
  have hm (k : ℕ) : Measurable (F k) := by
    exact Finset.measurable_sum _ fun j _ =>
      ((g k j).continuous.measurable.comp measurable_fst).mul
        ((h k j).continuous.measurable.comp measurable_snd)
  apply measurable_of_tendsto_metrizable hm
  rw [tendsto_pi_nhds]
  intro p
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 ε hε)
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (herr k p).trans_lt ((hδε k).trans (hN k hk))

end D11.Ch18.CcTensorApproximation
