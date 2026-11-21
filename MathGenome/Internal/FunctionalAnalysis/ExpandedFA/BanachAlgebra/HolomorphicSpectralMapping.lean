import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.HolomorphicHomomorphism
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping
import Mathlib.Algebra.Group.Commute.Units

/-! Full spectral mapping for the manuscript's Riesz–Dunford contour calculus. -/

noncomputable section
namespace ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping

open Set Filter
open scoped Topology
open ContourCalculus HolomorphicHomomorphism
open Specs.ExpandedFA.BanachAlgebra.Conventions

universe u

section Helpers
variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]

lemma holomorphicValue_const (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} (hU : IsOpen U) (hKU : algebraSpectrum ℂ A a ⊆ U) (c : ℂ) :
    holomorphicValue A a U (fun _ => c) = algebraMap ℂ A c := by
  simpa only [Polynomial.eval_C, Polynomial.aeval_C] using
    polynomial_agreement A hA a U (Polynomial.C c) hU hKU

lemma holomorphicValue_const_sub (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hKU : algebraSpectrum ℂ A a ⊆ U) (hf : DifferentiableOn ℂ f U) (c : ℂ) :
    holomorphicValue A a U (fun z => c - f z) =
      algebraMap ℂ A c - holomorphicValue A a U f := by
  have h := scalar_linearity A hA a U (fun _ => c) f 1 (-1) hU hKU
    (differentiableOn_const c) hf
  simpa only [one_mul, neg_one_mul, one_smul, neg_one_smul, ← sub_eq_add_neg,
    holomorphicValue_const hA a hU hKU] using h

/-- Restriction does not change the calculus value: it depends only on the germ
near the spectrum, even when the original neighborhood is disconnected. -/
lemma holomorphicValue_restrict (hA : IsUnitalBanachAlgebra A) (a : A)
    {U V : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hKU : algebraSpectrum ℂ A a ⊆ U) (hKV : algebraSpectrum ℂ A a ⊆ V)
    (hVU : V ⊆ U) (hf : DifferentiableOn ℂ f U) :
    holomorphicValue A a U f = holomorphicValue A a V f := by
  exact neighborhood_independence A hA a U V V f f hU hV hV hKV
    (fun _ hz => ⟨hVU hz, hz⟩) hf (hf.mono hVU) (fun _ _ => rfl)
    _ _ (selected_cycle_admissible A hA a U hU hKU)
    (selected_cycle_admissible A hA a V hV hKV)

/-- A function nonvanishing throughout a holomorphy neighborhood has an invertible
calculus value. Both inverse identities follow from multiplication in the calculus. -/
lemma isUnit_holomorphicValue (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hKU : algebraSpectrum ℂ A a ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hne : ∀ z ∈ U, f z ≠ 0) : IsUnit (holomorphicValue A a U f) := by
  have hg : DifferentiableOn ℂ (fun z => (f z)⁻¹) U := hf.inv hne
  refine isUnit_iff_exists.mpr ⟨holomorphicValue A a U (fun z => (f z)⁻¹), ?_, ?_⟩
  · calc
      _ = holomorphicValue A a U (fun z => f z * (f z)⁻¹) :=
        (multiplicativity A hA a U _ _ hU hKU hf hg).symm
      _ = holomorphicValue A a U (fun _ => 1) :=
        holomorphicValue_congr hA a hU hKU (fun z hz => mul_inv_cancel₀ (hne z hz))
      _ = 1 := unitality A hA a U hU hKU
  · calc
      _ = holomorphicValue A a U (fun z => (f z)⁻¹ * f z) :=
        (multiplicativity A hA a U _ _ hU hKU hg hf).symm
      _ = holomorphicValue A a U (fun _ => 1) :=
        holomorphicValue_congr hA a hU hKU (fun z hz => inv_mul_cancel₀ (hne z hz))
      _ = 1 := unitality A hA a U hU hKU

/-- The reciprocal may require shrinking the neighborhood, but never a global
holomorphic extension of the original function. -/
lemma spectrum_holomorphicValue_subset (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hKU : algebraSpectrum ℂ A a ⊆ U) (hf : DifferentiableOn ℂ f U) :
    algebraSpectrum ℂ A (holomorphicValue A a U f) ⊆ f '' algebraSpectrum ℂ A a := by
  intro μ hμ
  by_contra hnot
  let V := U ∩ f ⁻¹' ({μ}ᶜ)
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have hKV : algebraSpectrum ℂ A a ⊆ V := by
    intro z hz
    exact ⟨hKU hz, fun he => hnot ⟨z, hz, he⟩⟩
  have hfv := hf.mono (show V ⊆ U from inter_subset_left)
  have hne : ∀ z ∈ V, μ - f z ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr (fun he => hz.2 he.symm)
  have hi := isUnit_holomorphicValue hA a hV hKV
    ((differentiableOn_const μ).sub hfv) hne
  change IsUnit (holomorphicValue A a V (fun z => μ - f z)) at hi
  rw [holomorphicValue_const_sub hA a hV hKV hfv μ,
    ← holomorphicValue_restrict hA a hU hV hKU hKV inter_subset_left hf] at hi
  exact hμ hi

/-- The removable divided difference supplies a factor at every spectral point,
including zeros of arbitrary multiplicity and locally constant functions. -/
lemma image_spectrum_subset (hA : IsUnitalBanachAlgebra A) (a : A)
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hKU : algebraSpectrum ℂ A a ⊆ U) (hf : DifferentiableOn ℂ f U) :
    f '' algebraSpectrum ℂ A a ⊆ algebraSpectrum ℂ A (holomorphicValue A a U f) := by
  rintro _ ⟨lam, hlam, rfl⟩ hi
  let g := dslope f lam
  have hg : DifferentiableOn ℂ g U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds (hKU hlam))).mpr hf
  have hfactor : EqOn (fun z => (lam - z) * g z) (fun z => f lam - f z) U := by
    intro z _
    have he : (z - lam) * g z = f z - f lam := sub_smul_dslope f lam z
    linear_combination -he
  have heval : (algebraMap ℂ A lam - a) * holomorphicValue A a U g =
      algebraMap ℂ A (f lam) - holomorphicValue A a U f := by
    calc
      _ = holomorphicValue A a U (fun z => lam - z) * holomorphicValue A a U g := by
        have hc := holomorphicValue_const_sub hA a hU hKU differentiableOn_id lam
        change holomorphicValue A a U (fun z => lam - z) =
          algebraMap ℂ A lam - holomorphicValue A a U id at hc
        exact congrArg (fun x : A => x * holomorphicValue A a U g)
          (hc.trans (congrArg (fun x : A => algebraMap ℂ A lam - x)
            (coordinate A hA a U hU hKU))).symm
      _ = holomorphicValue A a U (fun z => (lam - z) * g z) :=
        (multiplicativity A hA a U _ _ hU hKU
          ((differentiableOn_const lam).sub differentiableOn_id) hg).symm
      _ = holomorphicValue A a U (fun z => f lam - f z) :=
        holomorphicValue_congr hA a hU hKU hfactor
      _ = _ := holomorphicValue_const_sub hA a hU hKU hf (f lam)
  have hc : Commute (algebraMap ℂ A lam - a) (holomorphicValue A a U g) :=
    Commute.sub_left (Algebra.commutes lam _)
      (commutation A hA a a U g hU hKU hg (Commute.refl a))
  exact hlam ((hc.isUnit_mul_iff.mp (heval.symm ▸ hi)).1)

end Helpers

/-- Full spectral mapping for arbitrary holomorphic germs near the spectrum. -/
theorem spectral_mapping : Spec.SpectralMapping.{u} := by
  intro A _ _ hA a U f hU hKU hf
  exact Set.Subset.antisymm (spectrum_holomorphicValue_subset hA a hU hKU hf)
    (image_spectrum_subset hA a hU hKU hf)

/-- Fixed-contour convergence for the actual calculus values, even if the
holomorphy neighborhoods of the approximants vary. -/
theorem holomorphic_fixed_contour_convergence : Spec.HolomorphicFixedContourConvergence.{u} := by
  intro A _ _ hA a U V f F hU hV hKU hKV hf hF Γ hΓ hΓF hlim
  letI : CompleteSpace A := hA.1
  have ht := fixed_contour_convergence A Γ a f F
    (fun z hz => not_not.mp (hΓ.1 hz).2)
    (hf.continuousOn.mono (fun z hz => (hΓ.1 hz).1))
    (fun n => (hF n).continuousOn.mono (fun z hz => ((hΓF n).1 hz).1)) hlim
  have he := holomorphic_formula A hA a U f hU hKU hf Γ hΓ
  have heF (n : ℕ) := holomorphic_formula A hA a (V n) (F n)
    (hV n) (hKV n) (hF n) Γ (hΓF n)
  simp_rw [heF, he]
  exact ht

/-- The complete source theorem, retaining all properties of the actual contour
integral established by the accepted contour and homomorphism stages. -/
theorem riesz_dunford_calculus : Spec.RieszDunfordCalculus.{u} :=
  ⟨admissible_cycles_exist, selected_cycle_admissible, holomorphic_formula,
    cycle_independence, neighborhood_independence, scalar_linearity, unitality,
    coordinate, multiplicativity, polynomial_agreement, resolvent_agreement,
    spectral_mapping, contour_norm_estimate, fixed_contour_convergence,
    holomorphic_fixed_contour_convergence, commutation, operator_commutation⟩

end ExpandedFA.BanachAlgebra.HolomorphicSpectralMapping
