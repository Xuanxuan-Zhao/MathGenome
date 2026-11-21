import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.RungeAllowedPoles
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.RationalRiemannSums
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.PoleMovement

noncomputable section
open Set TopologicalSpace
open scoped BigOperators

namespace D12Complex.RungeAllowedPoles
open PoleMovement RationalRiemannSums

/-- The continuous restriction of an oriented tagged path sum is a finite
linear combination of resolvents. The minus sign changes (w-z) to (z-w). -/
private theorem path_sum_in_algebra (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (γ : PiecewiseC1Path) (s : PathSampling γ) (f : ℂ → ℂ)
    (hγ : Disjoint (K : Set ℂ) γ.trace)
    (hres : ∀ a (ha : a ∉ (K : Set ℂ)), resolvent K a ha ∈ S) :
    ∃ g : C(K, ℂ), g ∈ S ∧ ∀ z : K, g z = pathSum γ s f z := by
  classical
  have htag (i : Fin s.1.n) : γ (s.2 i) ∉ (K : Set ℂ) := by
    intro hz
    exact disjoint_left.mp hγ hz
      ⟨s.2 i, SingleVariableAnalysis.Stieltjes.tag_mem_interval s.1 s.2 i, rfl⟩
  let c (i : Fin s.1.n) : ℂ :=
    -(f (γ (s.2 i)) * (γ (s.1.point i.succ) - γ (s.1.point i.castSucc)))
  let g : C(K, ℂ) := ∑ i : Fin s.1.n, c i • resolvent K (γ (s.2 i)) (htag i)
  refine ⟨g, S.sum_mem (fun i _ => S.smul_mem (hres _ (htag i)) (c i)), ?_⟩
  intro z
  simp only [g, ContinuousMap.sum_apply, ContinuousMap.smul_apply, PoleMovement.resolvent,
    ContinuousMap.coe_mk, smul_eq_mul, pathSum, Stieltjes.taggedSum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [c]
  rw [← neg_sub (γ (s.2 i)) (z : ℂ), inv_neg]
  ring

private theorem cycle_sum_in_algebra (K : Compacts ℂ) (S : Subalgebra ℂ C(K, ℂ))
    (Γ : IntegralCycle) (s : CycleSampling Γ) (f : ℂ → ℂ)
    (hΓ : Disjoint (K : Set ℂ) Γ.trace)
    (hres : ∀ a (ha : a ∉ (K : Set ℂ)), resolvent K a ha ∈ S) :
    ∃ g : C(K, ℂ), g ∈ S ∧ ∀ z : K, g z = cycleSum Γ s f z := by
  classical
  have hh (γ : {γ : PiecewiseC1Path // γ ∈ Γ.chain.support}) :
      ∃ g : C(K, ℂ), g ∈ S ∧ ∀ z : K, g z = pathSum γ.val (s γ) f z := by
    apply path_sum_in_algebra K S γ.val (s γ) f _ hres
    exact disjoint_left.mpr (fun z hz ht =>
      disjoint_left.mp hΓ hz ⟨γ.val, γ.property, ht⟩)
  choose g hg he using hh
  refine ⟨(2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∑ γ, (Γ.chain γ.val : ℂ) • g γ,
    S.smul_mem (S.sum_mem (fun γ _ => S.smul_mem (hg γ) _)) _, ?_⟩
  intro z
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul,
    he, cycleSum]

theorem holomorphic_mem_uniformClosure :
    Specs.D12Complex.Ch15.RungeAllowedPoles.holomorphic_mem_uniformClosure_type := by
  intro K U f hU hKU hf A hA hmeet F hF
  obtain ⟨S, hS⟩ := uniformClosure_algebra K A hA
  have hres (a : ℂ) (ha : a ∉ (K : Set ℂ)) : resolvent K a ha ∈ S := by
    change resolvent K a ha ∈ (S : Set C(K, ℂ))
    rw [hS]
    exact resolvent_mem_uniformClosure K A hA a ha
      (hmeet (sphereFinite a) ((finite_mem_sphericalComplement_iff K a).mpr ha))
  have hlim : F ∈ closure (S : Set C(K, ℂ)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨Γ, s, P, Q, _, htrace, _, _, _, _, heq, hb, _⟩ :=
      rational_riemann_approximation (K : Set ℂ) U f K.isCompact hU hKU hf ε hε
    have hd : Disjoint (K : Set ℂ) Γ.trace :=
      disjoint_left.mpr (fun z hz ht => (htrace ht).2 hz)
    obtain ⟨g, hg, heg⟩ := cycle_sum_in_algebra K S Γ s f hd hres
    refine ⟨g, hg, ?_⟩
    rw [dist_eq_norm]
    apply (ContinuousMap.norm_lt_iff (F - g) hε).mpr
    intro z
    change ‖F z - g z‖ < ε
    rw [hF, heg, heq z (fun hz => disjoint_left.mp hd z.2 hz)]
    exact (hb z z.2).trans_lt (by linarith)
  have hc : IsClosed (S : Set C(K, ℂ)) := by
    rw [hS]
    exact uniformClosure_isClosed K A
  rw [hc.closure_eq, hS] at hlim
  exact hlim

theorem runge_allowed_poles :
    Specs.D12Complex.Ch15.RungeAllowedPoles.runge_allowed_poles_type := by
  intro K U f A hK hU hKU hf hA hmeet ε hε
  let KC : Compacts ℂ := ⟨K, hK⟩
  let F : C(KC, ℂ) := ⟨fun z => f z,
    continuous_iff_continuousAt.mpr (fun z =>
      (hf.2 z (hKU z.2)).continuousAt.comp continuous_subtype_val.continuousAt)⟩
  have hm : F ∈ uniformClosure KC A :=
    holomorphic_mem_uniformClosure KC U f hU hKU hf A hA hmeet F (fun _ => rfl)
  obtain ⟨g, ⟨P, Q, hQ, hp, he⟩, hg⟩ :=
    (uniformClosure_iff_approximation KC A F).mp hm (ε / 2) (by positivity)
  have hval (z : KC) : finiteCoordinate
      (Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q (sphereFinite z)) = g z := by
    rw [he z]
    rfl
  have hb : ∀ z ∈ K, ‖f z - finiteCoordinate
      (Specs.D12Complex.Ch07.RationalInfinity.Objects.extension P Q (sphereFinite z))‖ ≤ ε / 2 := by
    intro z hz
    rw [hval ⟨z, hz⟩]
    exact (hg ⟨z, hz⟩).le
  refine ⟨P, Q, hQ, hp, ?_, ?_, ?_⟩
  · intro z hz
    rw [hval ⟨z, hz⟩]
    exact he ⟨z, hz⟩
  · intro z hz
    exact (hb z hz).trans_lt (by linarith)
  · by_cases hn : K.Nonempty
    · apply lt_of_le_of_lt (csSup_le (hn.image _) ?_) (by linarith : ε / 2 < ε)
      rintro _ ⟨z, hz, rfl⟩
      exact hb z hz
    · simp [Set.not_nonempty_iff_eq_empty.mp hn, hε]

end D12Complex.RungeAllowedPoles
