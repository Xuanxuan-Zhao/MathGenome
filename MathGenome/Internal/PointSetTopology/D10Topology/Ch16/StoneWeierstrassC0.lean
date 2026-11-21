import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.StoneWeierstrassC0
import MathGenome.Internal.PointSetTopology.D10Topology.Ch16.C0Algebra
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Nonunital Stone--Weierstrass on LCH spaces, real and complex.
We unitize the zero extensions on the source one-point construction,
including its isolated extra point when the domain is compact. -/
noncomputable section
open Set
open scoped Topology
universe u v

namespace D10Topology.Ch16

/-- Adding scalar constants to the image of a nonunital algebra. -/
def c0UnitizedAlgebra {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (A : NonUnitalSubalgebra 𝕜 (C0 X 𝕜))
    (E : C0 X 𝕜 →ₙₐ[𝕜] C(OnePoint X, 𝕜)) : Subalgebra 𝕜 C(OnePoint X, 𝕜) where
  carrier := {g | ∃ a ∈ A, ∃ c : 𝕜, g = E a + ContinuousMap.const _ c}
  zero_mem' := ⟨0, A.zero_mem, 0, by simp⟩
  one_mem' := ⟨0, A.zero_mem, 1, by simp⟩
  add_mem' := by
    rintro f g ⟨a, ha, c, rfl⟩ ⟨b, hb, d, rfl⟩
    refine ⟨a + b, A.add_mem ha hb, c + d, ?_⟩
    ext z
    simp only [map_add, ContinuousMap.add_apply, ContinuousMap.const_apply]
    ring
  mul_mem' := by
    rintro f g ⟨a, ha, c, rfl⟩ ⟨b, hb, d, rfl⟩
    refine ⟨a * b + d • a + c • b,
      A.add_mem (A.add_mem (A.mul_mem ha hb) (A.smul_mem d ha)) (A.smul_mem c hb),
      c * d, ?_⟩
    ext z
    simp only [map_add, map_mul, map_smul, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.const_apply,
      smul_eq_mul]
    ring
  algebraMap_mem' c := ⟨0, A.zero_mem, c, by ext z; simp⟩

/-- The nowhere-vanishing assumption separates an ordinary point from infinity. -/
theorem c0UnitizedAlgebra_separatesPoints
    {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (A : NonUnitalSubalgebra 𝕜 (C0 X 𝕜))
    (E : C0 X 𝕜 →ₙₐ[𝕜] C(OnePoint X, 𝕜))
    (hE : ∀ a, (E a : OnePoint X → 𝕜) = zeroExtension (a : X → 𝕜))
    (hsep : ∀ x y : X, x ≠ y → ∃ a ∈ A, a x ≠ a y)
    (hnv : ∀ x : X, ∃ a ∈ A, a x ≠ 0) :
    (c0UnitizedAlgebra A E).SeparatesPoints := by
  have hmem : ∀ a ∈ A, E a ∈ c0UnitizedAlgebra A E := by
    intro a ha
    exact ⟨a, ha, 0, by simp⟩
  intro x y hxy
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => exact (hxy rfl).elim
    | coe y =>
      obtain ⟨a, ha, hay⟩ := hnv y
      refine ⟨E a, ⟨E a, hmem a ha, rfl⟩, ?_⟩
      rw [hE]
      exact hay.symm
  | coe x =>
    induction y using OnePoint.rec with
    | infty =>
      obtain ⟨a, ha, hax⟩ := hnv x
      refine ⟨E a, ⟨E a, hmem a ha, rfl⟩, ?_⟩
      rw [hE]
      exact hax
    | coe y =>
      have hne : x ≠ y := fun h => hxy (congrArg OnePoint.some h)
      obtain ⟨a, ha, haxy⟩ := hsep x y hne
      refine ⟨E a, ⟨E a, hmem a ha, rfl⟩, ?_⟩
      rw [hE]
      exact haxy

/-- Simultaneous scalar proof: self-adjoint nonunital algebras of C₀. -/
theorem stone_weierstrass_c0_rclike
    {X : Type u} {𝕜 : Type v} [TopologicalSpace X] [RCLike 𝕜]
    (hX : Ch11.LCH X) (A : NonUnitalSubalgebra 𝕜 (C0 X 𝕜))
    (hsep : ∀ x y : X, x ≠ y → ∃ a ∈ A, a x ≠ a y)
    (hnv : ∀ x : X, ∃ a ∈ A, a x ≠ 0)
    (hstar : ∀ a ∈ A, star a ∈ A)
    (f : C0 X 𝕜) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, ‖f - a‖ < ε := by
  obtain ⟨E, hE, -, -, hnorm⟩ := c0_extension_algebra_bridge (𝕜 := 𝕜) hX
  let : CompactSpace (OnePoint X) := (Ch11.one_point_compact_hausdorff X hX).1
  let : T2Space (OnePoint X) := (Ch11.one_point_compact_hausdorff X hX).2
  have hEs : ∀ a, E (star a) = star (E a) := by
    intro a
    apply ContinuousMap.ext
    intro z
    change (E (star a) : OnePoint X → 𝕜) z = star ((E a : OnePoint X → 𝕜) z)
    rw [hE, hE]
    induction z using OnePoint.rec with
    | infty => exact (star_zero 𝕜).symm
    | coe x => rfl
  let B : StarSubalgebra 𝕜 C(OnePoint X, 𝕜) :=
    { c0UnitizedAlgebra A E with
      star_mem' := by
        rintro g ⟨a, ha, c, rfl⟩
        refine ⟨star a, hstar a ha, star c, ?_⟩
        rw [star_add, hEs]
        rfl }
  have hB : B.SeparatesPoints := c0UnitizedAlgebra_separatesPoints A E hE hsep hnv
  have hdense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints B hB
  have hf : E f ∈ closure (B : Set C(OnePoint X, 𝕜)) := by
    change E f ∈ B.topologicalClosure
    rw [hdense]
    trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 2) (half_pos hε)
  obtain ⟨a, ha, c, rfl⟩ := hg
  have herr : ‖E f - (E a + ContinuousMap.const _ c)‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hfg
  have hc : ‖c‖ < ε / 2 := by
    have hi := (E f - (E a + ContinuousMap.const _ c)).norm_coe_le_norm OnePoint.infty
    have hz : (E f - (E a + ContinuousMap.const _ c) : C(OnePoint X, 𝕜))
        OnePoint.infty = -c := by
      change (E f : OnePoint X → 𝕜) _ - ((E a : OnePoint X → 𝕜) _ + c) = -c
      rw [hE, hE]
      simp [Specs.D10Topology.Ch16.C0Algebra.zeroExtension]
    rw [hz, norm_neg] at hi
    exact hi.trans_lt herr
  refine ⟨a, ha, ?_⟩
  rw [← hnorm]
  have heq : E (f - a) =
      (E f - (E a + ContinuousMap.const _ c)) + ContinuousMap.const _ c := by
    rw [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖E f - (E a + ContinuousMap.const _ c)‖ + ‖ContinuousMap.const (OnePoint X) c‖ :=
      norm_add_le _ _
    _ ≤ ‖E f - (E a + ContinuousMap.const _ c)‖ + ‖c‖ := by
      exact add_le_add le_rfl
        ((ContinuousMap.norm_le (ContinuousMap.const (OnePoint X) c)
          (norm_nonneg c)).mpr fun _ => le_rfl)
    _ < ε / 2 + ε / 2 := add_lt_add herr hc
    _ = ε := add_halves ε

theorem stone_weierstrass_c0_real :
    Specs.D10Topology.Ch16.StoneWeierstrassC0.stone_weierstrass_c0_real := by
  intro X _ hX A hsep hnv f ε hε
  exact stone_weierstrass_c0_rclike hX A hsep hnv
    (fun a ha => by
      have hs : star a = a := ZeroAtInftyContinuousMap.ext fun x => star_trivial (a x)
      simpa only [hs] using ha) f ε hε

theorem stone_weierstrass_c0_complex :
    Specs.D10Topology.Ch16.StoneWeierstrassC0.stone_weierstrass_c0_complex := by
  intro X _ hX A hsep hnv hstar f ε hε
  exact stone_weierstrass_c0_rclike hX A hsep hnv hstar f ε hε

theorem stone_weierstrass_c0_real_dense :
    Specs.D10Topology.Ch16.StoneWeierstrassC0.stone_weierstrass_c0_real_dense := by
  intro X _ hX A hsep hnv f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨a, ha, herr⟩ := stone_weierstrass_c0_real hX A hsep hnv f ε hε
  exact ⟨a, ha, by simpa only [dist_eq_norm] using herr⟩

theorem stone_weierstrass_c0_complex_dense :
    Specs.D10Topology.Ch16.StoneWeierstrassC0.stone_weierstrass_c0_complex_dense := by
  intro X _ hX A hsep hnv hstar f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨a, ha, herr⟩ := stone_weierstrass_c0_complex hX A hsep hnv hstar f ε hε
  exact ⟨a, ha, by simpa only [dist_eq_norm] using herr⟩

end D10Topology.Ch16
