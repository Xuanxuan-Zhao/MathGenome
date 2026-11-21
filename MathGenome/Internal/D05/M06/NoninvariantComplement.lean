import MathGenome.Internal.Specs.D05.M06.NoninvariantComplement
import MathGenome.Internal.D05.M06.Invariant
import MathGenome.Internal.D05.M06.DirectSum

/-! The nilpotent coordinate-plane counterexample over an arbitrary field. -/

namespace D05.M06.NoninvariantComplement

open Specs.D05.M06.NoninvariantComplement

theorem operator_values : Specs.D05.M06.NoninvariantComplement.operator_values := by
  intro K _
  exact ⟨rfl, rfl⟩

theorem operator_formula : Specs.D05.M06.NoninvariantComplement.operator_formula := by
  intro K _ a b
  simp [nilpotentMap, e1, e2]

theorem square_zero : Specs.D05.M06.NoninvariantComplement.square_zero := by
  intro K _
  apply LinearMap.ext
  intro x
  rfl

theorem mem_line_iff {K : Type*} [Field K] (x : K × K) :
    x ∈ line K ↔ x.2 = 0 := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    simpa [e1] using (congrArg Prod.snd ha).symm
  · intro hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x.1, ?_⟩
    ext <;> simp [e1, hx]

theorem mem_transverseLine_iff {K : Type*} [Field K] (x : K × K) :
    x ∈ transverseLine K ↔ x.1 = 0 := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    simpa [e2] using (congrArg Prod.fst ha).symm
  · intro hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x.2, ?_⟩
    ext <;> simp [e2, hx]

theorem invariant_line : Specs.D05.M06.NoninvariantComplement.invariant_line := by
  intro K _ x _
  exact (mem_line_iff _).mpr rfl

theorem ordinary_complement : Specs.D05.M06.NoninvariantComplement.ordinary_complement := by
  intro K _
  apply (D05.M06.DirectSum.pair_internal_iff_sup_inf (line K) (transverseLine K)).mpr
  constructor
  · apply top_unique
    intro x _
    apply Submodule.mem_sup.mpr
    exact ⟨(x.1, 0), (mem_line_iff _).mpr rfl,
      (0, x.2), (mem_transverseLine_iff _).mpr rfl, by ext <;> simp⟩
  · apply bot_unique
    intro x hx
    have hs := (mem_line_iff x).mp hx.1
    have hf := (mem_transverseLine_iff x).mp hx.2
    change x = 0
    ext <;> assumption

theorem no_invariant_complement :
    Specs.D05.M06.NoninvariantComplement.no_invariant_complement := by
  intro K _ h
  obtain ⟨W, hdecomp, hinv⟩ := h
  obtain ⟨hsup, hinf⟩ :=
    (D05.M06.DirectSum.pair_internal_iff_sup_inf (line K) W).mp hdecomp
  -- Decompose e₂ = u + w. Its second coordinate forces w₂ = 1.
  have he2 : e2 K ∈ line K ⊔ W := by rw [hsup]; trivial
  obtain ⟨u, hu, w, hw, heq⟩ := Submodule.mem_sup.mp he2
  have hu2 := (mem_line_iff u).mp hu
  have hw2 : w.2 = 1 := by
    simpa [e2, hu2] using congrArg Prod.snd heq
  -- Invariance puts Nw in both summands, so Nw = 0.
  have hN : nilpotentMap K w ∈ line K ⊓ W :=
    ⟨(mem_line_iff _).mpr rfl, hinv w hw⟩
  rw [hinf] at hN
  have hz : nilpotentMap K w = 0 := hN
  have hw0 : w.2 = 0 := congrArg Prod.fst hz
  exact one_ne_zero (hw2.symm.trans hw0)

end D05.M06.NoninvariantComplement
