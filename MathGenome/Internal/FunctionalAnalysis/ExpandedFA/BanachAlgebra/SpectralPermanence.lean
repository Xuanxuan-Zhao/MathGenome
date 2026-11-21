import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.NonemptySpectrum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.SpectralPermanence

/-!
Spectral permanence for a closed unital subalgebra, without any assumption
that the subalgebra is inverse closed. For polynomial hulls we use Gelfand's
formula and polynomial spectral mapping: the inherited norm makes the
spectral radii of every polynomial in a identical in both algebras.
-/

namespace ExpandedFA.BanachAlgebra

open Specs.ExpandedFA.BanachAlgebra.SpectralPermanence
open scoped Topology ENNReal

universe u

abbrev polynomialHull : PolynomialHullType := PolynomialHullValue

theorem polynomialHull_modulus : PolynomialHullModulus := by
  intro K hK hne z
  have hb (p : Polynomial ℂ) : BddAbove ((fun w => ‖p.eval w‖) '' K) :=
    (hK.image (p.continuous.norm)).bddAbove
  constructor
  · intro hz p
    exact hz p _ (fun w hw => le_csSup (hb p) ⟨w, hw, rfl⟩)
  · intro hz p M hM
    exact (hz p).trans (csSup_le (hne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact hM w hw))

theorem subalgebra_spectrum_inclusion : SpectrumInclusion.{u} := by
  intro A _ _ _ B _ a
  exact spectrum.subset_subalgebra a

theorem subalgebra_spectrum_boundary_inclusion : SpectrumBoundaryInclusion.{u} := by
  intro A _ _ hA B hB a
  let : CompleteSpace A := hA.1
  let : IsClosed (B : Set A) := hB
  exact Subalgebra.frontier_subset_frontier B a

/-- The power norms are unchanged by inclusion, so Gelfand's formula gives
identical spectral radii in a closed subalgebra and its ambient algebra. -/
theorem spectralRadius_subalgebra_eq {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (B : Subalgebra ℂ A) [CompleteSpace B] (b : B) :
    spectralRadius ℂ b = spectralRadius ℂ (b : A) := by
  apply tendsto_nhds_unique (spectrum.gelfand_formula b)
  convert spectrum.gelfand_formula (b : A) using 1
  ext n
  rw [← Subalgebra.coe_pow]
  rfl

/-- Any polynomial bound on the ambient spectrum holds on the subalgebra
spectrum as well. The ambient maximum is attained by compactness. -/
theorem polynomial_bound_subalgebra {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [Nontrivial A] (B : Subalgebra ℂ A) [CompleteSpace B]
    (a : B) (z : ℂ) (hz : z ∈ spectrum ℂ a) (p : Polynomial ℂ) (M : ℝ)
    (hM : ∀ w ∈ spectrum ℂ (a : A), ‖p.eval w‖ ≤ M) : ‖p.eval z‖ ≤ M := by
  have hpz : p.eval z ∈ spectrum ℂ (Polynomial.aeval a p) := by
    rw [spectrum.map_polynomial_aeval]
    exact ⟨z, hz, rfl⟩
  have hr := spectralRadius_subalgebra_eq B (Polynomial.aeval a p)
  have heval : ((Polynomial.aeval a p : B) : A) = Polynomial.aeval (a : A) p :=
    (Polynomial.aeval_algHom_apply B.val a p).symm
  rw [heval] at hr
  obtain ⟨v, hv, hvmax⟩ := spectrum.exists_nnnorm_eq_spectralRadius
    (Polynomial.aeval (a : A) p)
  rw [spectrum.map_polynomial_aeval] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  have hle : (‖p.eval z‖₊ : ℝ≥0∞) ≤ (‖p.eval w‖₊ : ℝ≥0∞) := by
    rw [hvmax, ← hr, spectralRadius_eq_of_unital]
    exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (Polynomial.aeval a p)) =>
      (‖k‖₊ : ℝ≥0∞)) (p.eval z) hpz
  have hnorm : ‖p.eval z‖ ≤ ‖p.eval w‖ := by exact_mod_cast hle
  exact hnorm.trans (hM w hw)

theorem subalgebra_spectrum_polynomial_hulls : SpectrumPolynomialHulls.{u} := by
  intro A _ _ hA B hB a
  let : CompleteSpace A := hA.1
  let : Nontrivial A := hA.2.1
  let : CompleteSpace B := hB.completeSpace_coe
  change polynomialHull (spectrum ℂ (a : A)) = polynomialHull (spectrum ℂ a)
  apply Set.Subset.antisymm
  · intro z hz p M hM
    exact hz p M (fun w hw => hM w (spectrum.subset_subalgebra a hw))
  · intro z hz p M hM
    exact hz p M (fun w hw => polynomial_bound_subalgebra B a w hw p M hM)

theorem subalgebra_spectrum_components : SpectrumComponents.{u} := by
  intro A _ _ hA B hB a z hz
  let : CompleteSpace A := hA.1
  let : IsClosed (B : Set A) := hB
  classical
  have hcomponent {w : ℂ} (hw : w ∈ spectrum ℂ a)
      (hwa : w ∉ spectrum ℂ (a : A)) :
      connectedComponentIn (spectrum ℂ (a : A))ᶜ w ⊆ spectrum ℂ a := by
    rw [Subalgebra.spectrum_sUnion_connectedComponentIn B a]
    intro v hv
    exact Or.inr (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨⟨hw, hwa⟩, hv⟩⟩)
  by_cases hzB : z ∈ spectrum ℂ a
  · exact Or.inl (hcomponent hzB hz)
  · right
    refine Set.disjoint_left.mpr ?_
    intro w hw hwB
    have hwa : w ∉ spectrum ℂ (a : A) := connectedComponentIn_subset _ _ hw
    have heq := connectedComponentIn_eq hw
    exact hzB (hcomponent hwB hwa (heq ▸ mem_connectedComponentIn hz))

end ExpandedFA.BanachAlgebra
