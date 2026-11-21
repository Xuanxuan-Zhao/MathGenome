import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.EqualityMultipliers
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch06.EqualityChart

open Set
open scoped Topology ContDiff

noncomputable section
namespace VariationalNotes.Ch06.EqualityMultipliers

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Two-sided feasible curves force stationarity along the kernel. -/
theorem derivative_vanishes_on_kernel (B : X →L[ℝ] Y) (r : ℕ∞ω)
    (U : Set X) (h : X → Y) (a : X)
    (hcurves : EqualityChart.Specs.FeasibleCurves B r U h a)
    (f : X → ℝ) (hf : DifferentiableAt ℝ f a)
    (hmin : IsLocalMinOn f (U ∩ h ⁻¹' {0}) a) :
    ∀ d : B.ker, fderiv ℝ f a (d : X) = 0 := by
  intro d
  obtain ⟨ε, γ, hε, hγ0, hγC, hγD, hγS⟩ := hcurves d
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hm : IsLocalMinOn f (U ∩ h ⁻¹' {0}) (γ 0) := by
    simpa only [hγ0] using hmin
  have hmγ : IsLocalMin (f ∘ γ) 0 :=
    (hm.comp_continuousOn (fun t ht => hγS t ht) hγC.continuousOn h0).isLocalMin
      (isOpen_Ioo.mem_nhds h0)
  have hfγ : HasFDerivAt f (fderiv ℝ f a) (γ 0) := by
    simpa only [hγ0] using hf.hasFDerivAt
  exact hmγ.hasDerivAt_eq_zero (hfγ.comp_hasDerivAt 0 hγD)

/-- A continuous functional vanishing on the kernel factors through a map
with a bounded right inverse. The negative factor is the unique multiplier. -/
theorem unique_multiplier_of_kernel (B : X →L[ℝ] Y) (R : Y →L[ℝ] X)
    (hBR : B.comp R = ContinuousLinearMap.id ℝ Y) (F : X →L[ℝ] ℝ)
    (hF : ∀ d : B.ker, F (d : X) = 0) :
    ∃! ν : Y →L[ℝ] ℝ, F + ν.comp B = 0 := by
  have hright (y : Y) : B (R y) = y :=
    congrArg (fun L : Y →L[ℝ] Y => L y) hBR
  have hfactor (x : X) : F x = F (R (B x)) := by
    have hk : x - R (B x) ∈ B.ker := by simp [hright]
    have hz := hF ⟨x - R (B x), hk⟩
    simpa only [map_sub, sub_eq_zero] using hz
  refine ⟨-(F.comp R), ?_, ?_⟩
  · ext x
    simp [hfactor x]
  · intro ν hν
    ext y
    have hy := congrArg (fun L : X →L[ℝ] ℝ => L (R y)) hν
    have heq : F (R y) + ν y = 0 := by simpa [hright] using hy
    simpa using (eq_neg_of_add_eq_zero_right heq)

/-- Equality multiplier rule, `paper.tex`, Theorem 6.3. -/
theorem equalityMultipliers : Specs.EqualityMultipliersType := by
  intro X Y _ _ _ _ _ _ r hr U hU h hh a ha hzero B hB R hBR f hf hmin
  have hcurves := (EqualityChart.localEqualityChart X Y r hr U hU h hh a ha hzero B hB R hBR).2.2
  exact unique_multiplier_of_kernel B R hBR (fderiv ℝ f a)
    (derivative_vanishes_on_kernel B r U h a hcurves f hf hmin)

/-- Surjectivity is enough for any finite-dimensional target, even when
there are infinitely many ambient directions. -/
theorem finiteTargetEqualityMultipliers : Specs.FiniteTargetEqualityMultipliersType := by
  intro X Y _ _ _ _ _ _ r hr U hU h hh a ha hzero B hB hsurj f hf hmin
  obtain ⟨R, hBR⟩ := EqualityChart.finiteTargetRightInverse X Y B hsurj
  exact equalityMultipliers X Y r hr U hU h hh a ha hzero B hB R hBR f hf hmin

end VariationalNotes.Ch06.EqualityMultipliers
