import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionSupport
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionOperations
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions Topology Manifold
namespace P102.U4

/-- Compactly supported tests reduce an arbitrary open cover to a finite smooth
partition. No continuity of the functional is needed for this gluing step. -/
theorem vanishesOn_iUnion {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) {ι : Type*} (U : ι → Set (Space d))
    (hU : ∀ i, IsOpen (U i)) (hT : ∀ i, VanishesOn T (U i)) :
    VanishesOn T (⋃ i, U i) := by
  classical
  intro φ hφ
  obtain ⟨s, hs⟩ := φ.hasCompactSupport.elim_finite_subcover U hU hφ
  have hcover : tsupport φ ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Space d)) (isClosed_tsupport φ) (fun i : s => U i)
    (fun i => hU i) hcover
  let a : s → SmoothCoefficient 𝕜 Ω := fun i =>
    ⟨fun x => (ρ i x : 𝕜),
      ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (ρ i).contMDiff.contDiff).contDiffOn⟩
  have heq : φ = ∑ i : s, coefficientTestProduct (a i) φ := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · have hsum : ∑ i : s, ρ i x = 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      have heval : (∑ i : s, coefficientTestProduct (a i) φ) x =
          ∑ i : s, (ρ i x : 𝕜) * φ x := by
        change (FunLike.coeAddMonoidHom (TestSpace 𝕜 Ω) (Space d) 𝕜 (∑ i : s, coefficientTestProduct (a i) φ)) x = _
        rw [map_sum, Finset.sum_apply]
        rfl
      rw [heval]
      rw [← Finset.sum_mul]
      have hk : ∑ i : s, (ρ i x : 𝕜) = 1 := by exact_mod_cast hsum
      rw [hk, one_mul]
    · have hz := image_eq_zero_of_notMem_tsupport hx
      have heval : (∑ i : s, coefficientTestProduct (a i) φ) x =
          ∑ i : s, (ρ i x : 𝕜) * φ x := by
        change (FunLike.coeAddMonoidHom (TestSpace 𝕜 Ω) (Space d) 𝕜 (∑ i : s, coefficientTestProduct (a i) φ)) x = _
        rw [map_sum, Finset.sum_apply]
        rfl
      rw [heval, hz]
      simp
  rw [heq, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply hT i (coefficientTestProduct (a i) φ)
  change tsupport (fun x => (ρ i x : 𝕜) * φ x) ⊆ U i
  exact tsupport_mul_subset_left.trans
    ((tsupport_comp_subset (map_zero (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜)) (ρ i)).trans (hρ i))


abbrev distributionSupport : SupportExpected.SupportType := @relativeSupport

theorem vanishingRegion_isOpen {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) : IsOpen (vanishingRegion T) :=
  isOpen_sUnion fun _ h => h.1

theorem vanishingRegion_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) : vanishingRegion T ⊆ Ω := by
  rintro x ⟨U, hU, hx⟩
  exact hU.2.1 hx

theorem subset_vanishingRegion {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) {U : Set (Space d)} (ho : IsOpen U)
    (hU : U ⊆ Ω) (hT : VanishesOn T U) : U ⊆ vanishingRegion T :=
  subset_sUnion_of_mem ⟨ho, hU, hT⟩

theorem vanishingRegion_vanishes {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) : VanishesOn T (vanishingRegion T) := by
  let S := {U : Set (Space d) | IsOpen U ∧ U ⊆ Ω ∧ VanishesOn T U}
  have heq : vanishingRegion T = ⋃ U : S, (U : Set (Space d)) := by
    ext x
    simp [vanishingRegion, S]
  rw [heq]
  exact vanishesOn_iUnion T (fun U : S => U.val) (fun U => U.property.1)
    (fun U => U.property.2.2)

theorem largestVanishing : SupportExpected.LargestVanishing := by
  intro d 𝕜 _ Ω T
  exact ⟨vanishingRegion_isOpen T, vanishingRegion_subset T,
    vanishingRegion_vanishes T, fun _ => subset_vanishingRegion T⟩

theorem relativelyClosed : SupportExpected.RelativelyClosed := by
  intro d 𝕜 _ Ω T
  have heq : (Subtype.val : Ω → Space d) ⁻¹' relativeSupport T =
      (Subtype.val : Ω → Space d) ⁻¹' (vanishingRegion T)ᶜ := by
    ext x
    simp [relativeSupport]
  rw [heq]
  exact (vanishingRegion_isOpen T).isClosed_compl.preimage continuous_subtype_val

/-- An open region of vanishing cannot meet the relative support. -/
theorem notMem_relativeSupport_of_vanishes {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω) {U : Set (Space d)}
    (ho : IsOpen U) (hU : U ⊆ Ω) (hT : VanishesOn T U) {x : Space d}
    (hx : x ∈ U) : x ∉ relativeSupport T := by
  exact fun h => h.2 (subset_vanishingRegion T ho hU hT hx)

/-- Away from relative support there is a neighborhood of vanishing inside Ω. -/
theorem exists_vanishing_nhds {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) {x : Space d} (hx : x ∈ Ω)
    (h : x ∉ relativeSupport T) :
    ∃ U : Set (Space d), IsOpen U ∧ U ⊆ Ω ∧ VanishesOn T U ∧ x ∈ U := by
  have : x ∈ vanishingRegion T := by simpa [relativeSupport, hx] using h
  obtain ⟨U, hU, hxU⟩ := this
  exact ⟨U, hU.1, hU.2.1, hU.2.2, hxU⟩

/-- A test vanishing near support is supported in the largest vanishing region. -/
theorem pairing_zero_of_eqOn_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω) (φ : TestSpace 𝕜 Ω)
    {U : Set (Space d)} (ho : IsOpen U) (hU : relativeSupport T ⊆ U)
    (hz : EqOn φ 0 U) : T φ = 0 := by
  apply vanishingRegion_vanishes T φ
  have hs : tsupport φ ⊆ Uᶜ := by
    apply closure_minimal _ ho.isClosed_compl
    intro x hx hxU
    exact hx (hz hxU)
  intro x hx
  by_contra hn
  exact hs hx (hU ⟨φ.tsupport_subset hx, hn⟩)

theorem supportLocality : SupportExpected.Locality := by
  intro d 𝕜 _ Ω T φ ψ U ho hU heq
  have hz := pairing_zero_of_eqOn_zero T (φ - ψ) ho hU (by
    intro x hx
    change φ x - ψ x = 0
    exact sub_eq_zero.mpr (heq hx))
  simpa only [map_sub, sub_eq_zero] using hz

theorem supportCutoffPairing : SupportExpected.CutoffPairing := by
  intro d 𝕜 _ Ω T a φ U ho hU ha
  apply supportLocality d 𝕜 Ω T (coefficientTestProduct a φ) φ U ho hU
  intro x hx
  simp [ha x hx]


/-- Comparing local annihilation compares relative supports. -/
theorem relativeSupport_mono {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (S T : DistributionSpace 𝕜 Ω)
    (h : ∀ U : Set (Space d), IsOpen U → U ⊆ Ω → VanishesOn T U → VanishesOn S U) :
    relativeSupport S ⊆ relativeSupport T := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rintro ⟨U, hU, hxU⟩
  exact hx.2 (subset_vanishingRegion S hU.1 hU.2.1 (h U hU.1 hU.2.1 hU.2.2) hxU)

/-- Smooth multiplication preserves annihilation on every region. -/
theorem vanishesOn_multiplier {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (M : TestMultiplierFamily 𝕜 Ω) (hM : HasMultiplierGraph M)
    (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω) {U : Set (Space d)}
    (hT : VanishesOn T U) : VanishesOn (transposeMultiplier M a T) U := by
  intro φ hφ
  apply hT (M a φ)
  have heq : ⇑(M a φ) = fun x => a.val x * φ x := funext (hM a φ)
  rw [heq]
  exact tsupport_mul_subset_right.trans hφ

theorem multiplierSupport : SupportExpected.MultiplierSupport := by
  intro d 𝕜 _ Ω M hM a T x hx
  have hxT : x ∈ relativeSupport T :=
    relativeSupport_mono _ T (fun _ _ _ h => vanishesOn_multiplier M hM a T h) hx
  refine ⟨⟨hx.1, ?_⟩, hxT⟩
  by_contra hxa
  let U : Set (Space d) := (Ω : Set (Space d)) ∩ (tsupport a.val)ᶜ
  have hU : IsOpen U := Ω.isOpen.inter (isClosed_tsupport a.val).isOpen_compl
  have hvan : VanishesOn (transposeMultiplier M a T) U := by
    intro φ hφ
    have hz : M a φ = 0 := by
      ext y
      rw [hM]
      by_cases hy : y ∈ U
      · rw [image_eq_zero_of_notMem_tsupport hy.2, zero_mul]
        rfl
      · rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hφ ht)), mul_zero]
        rfl
    change T (M a φ) = 0
    rw [hz, map_zero]
  exact notMem_relativeSupport_of_vanishes _ hU inter_subset_left hvan ⟨hx.1, hxa⟩ hx

/-- Coordinate differentiation does not enlarge the closed support of a test. -/
theorem testPartialWord_tsupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (l : List (Fin d)) (φ : TestSpace 𝕜 Ω) :
    tsupport (testPartialWord Ω l φ) ⊆ tsupport φ := by
  rw [testPartialWord_coe]
  induction l with
  | nil => exact Subset.rfl
  | cons i l ih =>
    exact (tsupport_fderiv_apply_subset ℝ (coordinateVector d i)).trans ih

theorem derivativeSupport : SupportExpected.DerivativeSupport := by
  intro d 𝕜 _ Ω α T
  apply relativeSupport_mono _ T
  intro U _ _ hT φ hφ
  have hz := hT (testPartialWord Ω (α.sort (· ≤ ·)) φ)
    ((testPartialWord_tsupport _ φ).trans hφ)
  simp [distributionPartial, hz]

/-- The operations in the proposition are the canonical upstream constructions. -/
theorem supportOperations : SupportExpected.Operations :=
  ⟨multiplicationOperations, restrictionOperations, restrictionTransitive⟩


/-- Restriction inherits every region of vanishing of the original distribution. -/
theorem vanishesOn_restriction {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {V Ω : Opens (Space d)} (h : V ≤ Ω) (T : DistributionSpace 𝕜 Ω)
    {U : Set (Space d)} (hT : VanishesOn T U) :
    VanishesOn (restrictDistribution h T) U := by
  intro φ hφ
  apply hT (zeroExtension 𝕜 h φ)
  have heq : ⇑(zeroExtension 𝕜 h φ) = ⇑φ := by
    simp [zeroExtension, TestFunction.monoCLM_apply, h]
  rwa [heq]

/-- A test compactly supported in V is also a test on V; zero extension recovers
its original representative. Thus vanishing of the restriction is local vanishing
of the original functional. -/
theorem vanishesOn_of_restriction {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {V Ω : Opens (Space d)} (h : V ≤ Ω) (T : DistributionSpace 𝕜 Ω)
    {U : Set (Space d)} (hU : U ⊆ V)
    (hT : VanishesOn (restrictDistribution h T) U) : VanishesOn T U := by
  intro φ hφ
  let ψ : TestSpace 𝕜 V := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ.trans hU⟩
  have heq : zeroExtension 𝕜 h ψ = φ := by
    ext x
    have heq' : ⇑(zeroExtension 𝕜 h ψ) = ⇑ψ := by
      simp [zeroExtension, TestFunction.monoCLM_apply, h]
    exact congrFun heq' x
  have hz := hT ψ (show tsupport ψ ⊆ U from hφ)
  change T (zeroExtension 𝕜 h ψ) = 0 at hz
  rwa [heq] at hz

theorem restrictionSupport : SupportExpected.RestrictionSupport := by
  intro d 𝕜 _ V Ω h T
  apply subset_antisymm
  · intro x hx
    refine ⟨hx.1, h hx.1, ?_⟩
    rintro ⟨U, hU, hxU⟩
    have hvan : VanishesOn T (U ∩ V) := fun φ hφ => hU.2.2 φ (hφ.trans inter_subset_left)
    exact hx.2 (subset_vanishingRegion (restrictDistribution h T)
      (hU.1.inter V.isOpen) inter_subset_right (vanishesOn_restriction h T hvan)
      ⟨hxU, hx.1⟩)
  · rintro x ⟨hxV, hxT⟩
    refine ⟨hxV, ?_⟩
    rintro ⟨U, hU, hxU⟩
    exact hxT.2 (subset_vanishingRegion T hU.1 (hU.2.1.trans h)
      (vanishesOn_of_restriction h T hU.2.1 hU.2.2) hxU)

end P102.U4
