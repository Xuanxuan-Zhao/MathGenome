import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.MapCounterexamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps

/-! The elementary map counterexamples, retaining their exact topologies
and the hyperbola and closed unit interval witnesses. -/

open Set
open scoped Topology
universe u v

namespace D10Topology.Ch02
namespace MapCounterexamples

private theorem reverse_identity_not_continuous : ¬ @Continuous Bool Bool ⊤ ⊥ id := by
  intro h
  have hopen : IsOpen[(⊤ : TopologicalSpace Bool)] ({true} : Set Bool) :=
    @Continuous.isOpen_preimage Bool Bool ⊤ ⊥ id h _
      (show IsOpen[(⊥ : TopologicalSpace Bool)] {true} from trivial)
  rcases (TopologicalSpace.isOpen_top_iff _).mp hopen with he | hu
  · have := congrArg (fun s : Set Bool => true ∈ s) he
    simp at this
  · have := congrArg (fun s : Set Bool => false ∈ s) hu
    simp at this

theorem discrete_indiscrete_identity :
    @Continuous Bool Bool ⊥ ⊤ id ∧ Function.Bijective (id : Bool → Bool) ∧
      ¬ @Continuous Bool Bool ⊤ ⊥ id := by
  exact ⟨continuous_top, Function.bijective_id, reverse_identity_not_continuous⟩

theorem indiscrete_discrete_identity :
    @IsOpenMap Bool Bool ⊤ ⊥ id ∧ @IsClosedMap Bool Bool ⊤ ⊥ id ∧
      ¬ @Continuous Bool Bool ⊤ ⊥ id := by
  refine ⟨?_, ?_, reverse_identity_not_continuous⟩
  · intro U _
    trivial
  · intro F _
    exact ⟨trivial⟩

/-- Even in a non-T1 target, a singleton's own point is never an
accumulation point of that singleton. Other points may be. -/
theorem point_not_in_derivedSet_singleton {Y : Type v} [TopologicalSpace Y] (c : Y) :
    c ∉ derivedSet ({c} : Set Y) := by
  intro hc
  obtain ⟨y, hy, hne⟩ := (accPt_iff_nhds.mp hc) univ (Filter.univ_mem)
  exact hne (mem_singleton_iff.mp hy.2)

theorem constant_accumulation_failure {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (x : X) (c : Y)
    (hx : x ∈ derivedSet A) :
    Continuous (fun _ : X => c) ∧ (fun _ : X => c) '' A = {c} ∧
      c ∉ derivedSet ((fun _ : X => c) '' A) ∧
      ¬ (fun _ : X => c) '' derivedSet A ⊆ derivedSet ((fun _ : X => c) '' A) := by
  obtain ⟨a, ha, _⟩ := (accPt_iff_nhds.mp hx) univ Filter.univ_mem
  have himage : (fun _ : X => c) '' A = {c} := by
    ext y
    constructor
    · rintro ⟨_, _, rfl⟩
      rfl
    · intro hy
      exact ⟨a, ha.2, (mem_singleton_iff.mp hy).symm⟩
  have hn : c ∉ derivedSet ((fun _ : X => c) '' A) := by
    rw [himage]
    exact point_not_in_derivedSet_singleton c
  exact ⟨continuous_const, himage, hn, fun h => hn (h ⟨x, hx, rfl⟩)⟩

theorem real_constant_counterexample :
    (0 : ℝ) ∈ derivedSet (univ : Set ℝ) ∧
      Continuous (fun _ : ℝ => (0 : ℝ)) ∧
      (fun _ : ℝ => (0 : ℝ)) '' univ = {0} ∧
      (0 : ℝ) ∉ derivedSet ((fun _ : ℝ => (0 : ℝ)) '' univ) ∧
      ¬ (fun _ : ℝ => (0 : ℝ)) '' derivedSet univ ⊆
        derivedSet ((fun _ : ℝ => (0 : ℝ)) '' univ) := by
  have hx : (0 : ℝ) ∈ derivedSet (univ : Set ℝ) := by
    rw [mem_derivedSet, accPt_principal_iff_nhdsWithin]
    simpa only [← Set.compl_eq_univ_sdiff] using
      (inferInstance : (nhdsWithin (0 : ℝ) {0}ᶜ).NeBot)
  exact ⟨hx, constant_accumulation_failure univ 0 0 hx⟩

theorem hyperbola_closed : IsClosed {z : ℝ × ℝ | z.1 * z.2 = 1} :=
  isClosed_eq (continuous_fst.mul continuous_snd) continuous_const

theorem hyperbola_projection :
    Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1} = (univ : Set ℝ) \ {0} := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    intro ha
    have ha0 : a = 0 := mem_singleton_iff.mp ha
    change a * b = 1 at hab
    simp [ha0] at hab
  · rintro ⟨_, hx⟩
    have hx0 : x ≠ 0 := by simpa using hx
    exact ⟨(x, x⁻¹), mul_inv_cancel₀ hx0, rfl⟩

theorem hyperbola_projection_not_closed :
    ¬ IsClosed (Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1}) := by
  rw [hyperbola_projection, ← Set.compl_eq_univ_sdiff]
  intro h
  exact not_isOpen_singleton (0 : ℝ) (isClosed_compl_iff.mp h)

theorem real_projection_open_not_closed :
    IsOpenMap (Prod.fst : ℝ × ℝ → ℝ) ∧ ¬ IsClosedMap (Prod.fst : ℝ × ℝ → ℝ) := by
  exact ⟨isOpenMap_fst, fun h => hyperbola_projection_not_closed (h _ hyperbola_closed)⟩

theorem unit_interval_inclusion_closed_not_open :
    IsClosedMap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ∧
      ¬ IsOpenMap (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ∧
      (Subtype.val : Icc (0 : ℝ) 1 → ℝ) '' univ = Icc (0 : ℝ) 1 ∧
      ¬ IsOpen (Icc (0 : ℝ) 1) := by
  have hn : ¬ IsOpen (Icc (0 : ℝ) 1) := by
    intro ho
    have hmem := Icc_mem_nhds_iff.mp (ho.mem_nhds (show (0 : ℝ) ∈ Icc 0 1 by simp))
    exact (lt_irrefl (0 : ℝ)) hmem.1
  have hi : (Subtype.val : Icc (0 : ℝ) 1 → ℝ) '' univ = Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  refine ⟨isClosed_Icc.isClosedMap_subtype_val, ?_, hi, hn⟩
  intro h
  exact hn (hi ▸ h univ isOpen_univ)

end MapCounterexamples
end D10Topology.Ch02
