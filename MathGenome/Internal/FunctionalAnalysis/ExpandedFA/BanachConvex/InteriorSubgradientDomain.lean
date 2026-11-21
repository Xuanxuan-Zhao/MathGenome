import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.InteriorSubgradientDomain
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.LocalLipschitzSubgradients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire

/-! The interior-domain assertion of paper.tex:8087–8088, 8133–8143.
Baire applied to the closed sublevels on the open finite domain produces
one local upper bound. Convexity propagates it throughout that interior.
The accepted local subgradient theorem then supplies a continuous support.
-/
namespace ExpandedFA.BanachConvex

open P1.ExtendedConvexFunctions LocalSpec
open Filter Set Metric
open scoped Topology
universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
/-- A lower semicontinuous extended function finite on a nonempty open subset
of a Banach space has a finite upper bound near some point of that subset. -/
lemma exists_local_upper_bound [CompleteSpace X] (φ : ExtendedFunction X)
    (hls : P1.ExtendedConvexFunctions.LowerSemicontinuous X φ)
    {C : Set X} (hC : IsOpen C) (hne : C.Nonempty)
    (hfin : ∀ x ∈ C, φ x ≠ ⊤) :
    ∃ x ∈ C, ∃ M : ℝ, ∀ᶠ y in 𝓝 x, φ y ≤ (M : WithTop ℝ) := by
  classical
  let : BaireSpace X := P1.C07Baire.baireSpace_of_completeMetric X
  let : BaireSpace C := hC.baireSpace
  let : Nonempty C := hne.to_subtype
  let F : ℕ → Set C := fun n => {x | φ x ≤ ((n : ℝ) : WithTop ℝ)}
  have hclosed (n : ℕ) : IsClosed (F n) :=
    (hls (n : ℝ)).preimage continuous_subtype_val
  have hcover : (⋃ n, F n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hfin x x.property)
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact mem_iUnion.mpr ⟨n, by
      change φ x ≤ ((n : ℝ) : WithTop ℝ)
      rw [← hr]
      exact WithTop.coe_le_coe.mpr hn⟩
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  let V : Set X := Subtype.val '' interior (F n)
  have hV : IsOpen V := hC.isOpenMap_subtype_val _ isOpen_interior
  refine ⟨x, x.property, n, ?_⟩
  filter_upwards [hV.mem_nhds (show (x : X) ∈ V from ⟨x, hx, rfl⟩)] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact interior_subset (s := F n) hz

/-- The domain-interior equality, including the empty-interior case. -/
theorem interior_subgradientDomain : InteriorSpec.InteriorSubgradientDomain.{u} := by
  intro X _ _ _ φ _ hc hls
  apply subset_antisymm
  · exact interior_mono (subgradientDomain_subset_finiteDomain X φ)
  · apply interior_maximal ?_ isOpen_interior
    intro x hx
    let C := interior (finiteDomain X φ)
    have hC : IsOpen C := isOpen_interior
    have hCconv : Convex ℝ C := (convex_finiteDomain X φ hc).interior
    have hfin : ∀ y ∈ C, φ y ≠ ⊤ := fun y hy => interior_subset hy
    have hval : ∀ y ∈ C, φ y = (realValue φ y : WithTop ℝ) := by
      intro y hy
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hfin y hy)
      simp [realValue, ← hr]
    have hreal : ConvexOn ℝ C (realValue φ) :=
      realValue_convexOn φ hc hCconv hfin
    obtain ⟨z, hz, M, hM⟩ := exists_local_upper_bound φ hls hC ⟨x, hx⟩ hfin
    have hbound : (𝓝 z).IsBoundedUnder (· ≤ ·) (realValue φ) := by
      refine ⟨M, ?_⟩
      change ∀ᶠ y in 𝓝 z, realValue φ y ≤ M
      filter_upwards [hM, hC.mem_nhds hz] with y hy hyC
      rwa [hval y hyC, WithTop.coe_le_coe] at hy
    have hLip : LocallyLipschitzOn C (realValue φ) := by
      apply ((hreal.continuousOn_tfae hC ⟨x, hx⟩).out 4 1).mp
      exact ⟨z, hz, hbound⟩
    obtain ⟨d, hd, ⟨f, hf, hfd⟩, hmax⟩ :=
      directional_maximum_of_local_lipschitz φ (realValue φ) C hC hCconv hc hval hLip x hx 0
    exact ⟨f, hf⟩

end ExpandedFA.BanachConvex
