import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.ClosedZeroSets
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Extension
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.SmoothExhaustion

namespace SmoothManifolds
open Set Filter
open scoped Topology
universe u
variable {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- An ambient smooth function detects the complement of a closed set inside
one chart. Lifting the relative open complement to an ambient open set ensures
actual Euclidean smoothness even along the model boundary. -/
theorem exists_chart_zero_function (S : SmoothManifold n a M) (A : Set M)
    (hA : IsClosed A) (e : ModelChart n a M) (he : e ∈ S.smoothStructure.val) :
    ∃ h : M → ℝ, (∀ x, 0 ≤ h x) ∧
      (∀ x ∈ e.source, ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val h x) ∧
      ∀ x ∈ e.source, h x = 0 ↔ x ∈ A := by
  let V : Set (ModelSpace n a) := e.target ∩ e.symm ⁻¹' Aᶜ
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hA.isOpen_compl
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  obtain ⟨f, hfO, hf, hf01⟩ := hO.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  refine ⟨fun x => f (e x).val, fun x => (hf01 (mem_range_self _)).1, ?_, ?_⟩
  · intro x hx
    exact scalarContDiffAt_of_chart S.smoothStructure.property.1 he hx
      ⟨univ, isOpen_univ, mem_univ _, f, hf.contDiffOn, Eventually.of_forall (fun _ => rfl)⟩
  · intro x hx
    have hxO : (e x).val ∈ O ↔ x ∉ A := by
      change e x ∈ Subtype.val ⁻¹' O ↔ x ∉ A
      rw [hOV]
      simp [V, e.map_source hx, e.left_inv hx]
    have hzero : f (e x).val = 0 ↔ (e x).val ∉ O := by
      rw [← hfO]
      exact Function.notMem_support.symm
    rw [hzero, hxO, not_not]

/-- Every closed subset, with no geometric restriction, is the zero set of a
globally smooth nonnegative function. The chart sum is locally finite. -/
theorem exists_smooth_nonnegative_zero_set (S : SmoothManifold n a M)
    (A : Set M) (hA : IsClosed A) :
    ∃ g : M → ℝ, ScalarSmooth S.smoothStructure.val g ∧
      (∀ x, 0 ≤ g x) ∧ g ⁻¹' {0} = A := by
  classical
  let I := {e : ModelChart n a M // e ∈ S.smoothStructure.val}
  let U : I → Set M := fun e => e.val.source
  have hcover : ∀ x : M, ∃ i, x ∈ U i := by
    intro x
    obtain ⟨e, he, hx⟩ := S.smoothStructure.property.1.1 x
    exact ⟨⟨e, he⟩, hx⟩
  obtain ⟨ρ, ⟨hρsmooth, hρnonneg, hρlf, hρsum⟩, hρsub⟩ :=
    exists_smooth_partition S U (fun e => e.val.open_source) hcover
  have hchart (i : I) := exists_chart_zero_function S A hA i.val i.property
  choose h hnonneg hsmooth hzero using hchart
  let t : I → M → ℝ := fun i x => ρ i x * h i x
  have htsupp (i : I) : sectionSupport (t i) ⊆ sectionSupport (ρ i) := by
    apply closure_mono
    intro x hx
    exact left_ne_zero_of_mul hx
  have htlf : LocallyFinite (fun i => sectionSupport (t i)) := hρlf.subset htsupp
  have htsmooth (i : I) : ScalarSmooth S.smoothStructure.val (t i) :=
    scalarContDiff_mul_of_support_subset (hρsmooth i) (hsmooth i) (hρsub i)
  have htpos (i : I) (x : M) : 0 ≤ t i x := mul_nonneg (hρnonneg i x) (hnonneg i x)
  refine ⟨fun x => ∑ᶠ i, t i x, scalarContDiff_finsum htsmooth htlf,
    fun x => finsum_nonneg (fun i => htpos i x), ?_⟩
  ext x
  change (∑ᶠ i, t i x) = 0 ↔ x ∈ A
  constructor
  · intro hx
    by_contra hxA
    have hactive : ∃ i, ρ i x ≠ 0 := by
      by_contra hn
      have hz : (∑ᶠ i, ρ i x) = 0 :=
        finsum_eq_zero_of_forall_eq_zero (fun i => by simpa using not_exists.mp hn i)
      rw [hρsum x] at hz
      exact one_ne_zero hz
    obtain ⟨i, hi⟩ := hactive
    have hxi := hρsub i (subset_closure hi)
    have hhi : h i x ≠ 0 := fun hz => hxA ((hzero i x hxi).mp hz)
    have hpositive : 0 < ∑ᶠ i, t i x := by
      apply finsum_pos (fun i => htpos i x)
      · exact ⟨i, mul_pos (lt_of_le_of_ne (hρnonneg i x) hi.symm)
          (lt_of_le_of_ne (hnonneg i x) hhi.symm)⟩
      · exact (htlf.point_finite x).subset (fun _ hj => subset_closure hj)
    exact (ne_of_gt hpositive) hx
  · intro hxA
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases hi : ρ i x = 0
    · simp [t, hi]
    · have hz := (hzero i x (hρsub i (subset_closure hi))).mpr hxA
      simp [t, hz]

/-- M01.07(a), (b), and (c), under their original hypotheses. -/
theorem extension_exhaustion_zero_sets (S : SmoothManifold n a M) (A U : Set M)
    (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (f : A → Euclidean k) (hf : LocallySmoothOnSubset S.smoothStructure.val A f) :
    ∃ (F : M → Euclidean k) (ρ g : M → ℝ),
      ((∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val F x) ∧
        (∀ x : A, F x.val = f x) ∧ sectionSupport F ⊆ U) ∧
      (ScalarSmooth S.smoothStructure.val ρ ∧ (∀ x, 0 ≤ ρ x) ∧
        ∀ c : ℝ, IsCompact {x | ρ x ≤ c}) ∧
      (ScalarSmooth S.smoothStructure.val g ∧ (∀ x, 0 ≤ g x) ∧ g ⁻¹' {0} = A) := by
  obtain ⟨F, hF⟩ := exists_supported_smooth_extension S A U hA hU hAU f hf
  obtain ⟨ρ, hρ⟩ := exists_smooth_exhaustion S
  obtain ⟨g, hg⟩ := exists_smooth_nonnegative_zero_set S A hA
  exact ⟨F, ρ, g, hF, hρ, hg⟩

end SmoothManifolds
