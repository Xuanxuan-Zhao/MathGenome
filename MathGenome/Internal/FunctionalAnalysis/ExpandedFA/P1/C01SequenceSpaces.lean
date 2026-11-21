import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces

/-! Canonical scalar sequence spaces, with their exact membership and norm formulas. -/

noncomputable section
open Filter
open scoped Topology ENNReal

universe u
namespace ExpandedFA.P1.C01SequenceSpaces

abbrev scalarLp : Spec.LpType.{u} := fun 𝕜 _ p => SequenceLp 𝕜 p
abbrev scalarLInfinity : Spec.LInfinityType.{u} := fun 𝕜 _ => SequenceLInfinity 𝕜
abbrev scalarC0 : Spec.C0Type.{u} := fun 𝕜 _ => SequenceC0 𝕜
abbrev scalarC00 : Spec.C00Type.{u} := fun 𝕜 _ => SequenceC00 𝕜

theorem finite_lp_identification : Spec.FiniteLpIdentification.{u} := by
  intro 𝕜 _ p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp' : 0 < (ENNReal.ofReal p).toReal := by
    simpa [ENNReal.toReal_ofReal hp0.le] using hp0
  constructor
  · intro x
    constructor
    · rintro ⟨y, rfl⟩
      simpa [ENNReal.toReal_ofReal hp0.le] using (lp.memℓp y).summable hp'
    · intro hx
      exact ⟨⟨x, memℓp_gen (by simpa [ENNReal.toReal_ofReal hp0.le] using hx)⟩, rfl⟩
  · intro y
    simpa [ENNReal.toReal_ofReal hp0.le] using lp.norm_eq_tsum_rpow hp' y

theorem bounded_identification : Spec.BoundedIdentification.{u} := by
  intro 𝕜 _
  refine ⟨?_, lp.norm_eq_ciSup, lp.isLUB_norm⟩
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    rcases (lp.memℓp y).bddAbove with ⟨C, hC⟩
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  · rintro ⟨C, hC⟩
    exact ⟨⟨x, memℓp_infty ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩⟩, rfl⟩

theorem c0_identification : Spec.C0Identification.{u} := by
  intro 𝕜 _
  refine ⟨?_, fun y => ⟨rfl, lp.norm_eq_ciSup y.val⟩, ?_⟩
  · intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      have hb : BddAbove (Set.range fun n => ‖x n‖) := hx.norm.bddAbove_range
      exact ⟨⟨⟨x, memℓp_infty hb⟩, hx⟩, rfl⟩
  · exact fun _ _ => rfl

theorem c00_identification : Spec.C00Identification.{u} := by
  intro 𝕜 _ x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.hasFiniteSupport
  · intro hx
    exact ⟨Finsupp.ofSupportFinite x hx, rfl⟩

def c00ToLp : Spec.C00ToLpType.{u} := Spec.C00ToLpValue

/-- A finite-support scalar sequence is eventually identically zero. -/
theorem c00_coordinates_tendsto_zero (𝕜 : Type u) [RCLike 𝕜] (x : SequenceC00 𝕜) :
    Tendsto (fun n => x n) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  rw [← Nat.cofinite_eq_atTop]
  filter_upwards [x.hasFiniteSupport.eventually_cofinite_notMem] with n hn
  simpa [Function.mem_support, eq_comm] using hn

def c00ToC0 : Spec.C00ToC0Type.{u} := fun 𝕜 _ =>
  { toFun := fun x => ⟨c00ToLp 𝕜 ∞ x, c00_coordinates_tendsto_zero 𝕜 x⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- For a finite positive exponent, summability of the powered norms forces
the coordinates to vanish. Taking the continuous inverse power recovers norms. -/
theorem lp_coordinates_tendsto_zero (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : SequenceLp 𝕜 p) :
    Tendsto (fun n => x n) atTop (𝓝 0) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt
    (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have h := ((lp.memℓp x).summable hp0).tendsto_atTop_zero
  have hroot := (Real.continuous_rpow_const (inv_nonneg.mpr hp0.le)).tendsto 0 |>.comp h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.rpow_rpow_inv (norm_nonneg _) hp0.ne', Real.zero_rpow
    (inv_ne_zero hp0.ne')] using hroot

def lpToC0 : Spec.LpToC0Type.{u} := fun 𝕜 _ p _ hp =>
  { toFun := fun x =>
      ⟨lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top x,
        lp_coordinates_tendsto_zero 𝕜 p hp x⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem sequence_coercions : Spec.Coercions.{u} := by
  intro 𝕜 _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p
    refine ⟨c00ToLp 𝕜 p, fun _ _ => rfl, ?_⟩
    intro x y h
    exact Finsupp.ext fun n => congrArg (fun z : SequenceLp 𝕜 p => z n) h
  · refine ⟨c00ToC0 𝕜, fun _ _ => rfl, ?_⟩
    intro x y h
    exact Finsupp.ext fun n => congrArg (fun z : SequenceC0 𝕜 => z.val n) h
  · intro p _ hp
    refine ⟨lpToC0 𝕜 p hp, fun _ _ => rfl, ?_⟩
    intro x y h
    exact lp.ext (funext fun n => congrArg (fun z : SequenceC0 𝕜 => z.val n) h)
  · intro p q h
    refine ⟨fun _ _ => rfl, ?_⟩
    intro x y hxy
    exact lp.ext (funext fun n => congrArg (fun z : SequenceLp 𝕜 q => z n) hxy)

theorem zero_sequences : Spec.ZeroSequences.{u} := by
  intro 𝕜 _
  exact ⟨fun _ _ => ⟨fun _ => rfl, norm_zero⟩, ⟨fun _ => rfl, norm_zero⟩,
    fun _ => rfl⟩

theorem sequence_reindexing : Spec.Reindexing.{u} := by
  refine ⟨fun n => rfl, ?_, ?_, ?_, ?_⟩
  · intro 𝕜 _ x p
    exact ⟨Equiv.pnatEquivNat.symm.summable_iff (f := fun j => ‖x j‖ ^ p),
      Equiv.pnatEquivNat.symm.tsum_eq (fun j => ‖x j‖ ^ p)⟩
  · intro 𝕜 _ x
    change sSup (Set.range (fun n : ℕ => ‖x (Equiv.pnatEquivNat.symm n)‖)) =
      sSup (Set.range (fun j : ℕ+ => ‖x j‖))
    congr 1
    exact Equiv.pnatEquivNat.symm.surjective.range_comp (fun j => ‖x j‖)
  · intro 𝕜 _ x
    change Tendsto (x ∘ (OrderIso.pnatIsoNat.symm : ℕ → ℕ+)) atTop (𝓝 0) ↔ _
    rw [← tendsto_map'_iff, OrderIso.map_atTop]
  · intro 𝕜 _ x
    change (Equiv.pnatEquivNat.symm ⁻¹' Function.support x).Finite ↔ _
    constructor
    · intro h
      exact h.of_preimage Equiv.pnatEquivNat.symm.surjective
    · intro h
      exact h.preimage Equiv.pnatEquivNat.symm.injective.injOn

end ExpandedFA.P1.C01SequenceSpaces
