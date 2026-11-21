import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.VectorLatticeStone

/-! Real vector lattices and Stone truncation, including the empty domain. -/

universe u

namespace D11.Ch23

/-- A real vector lattice is a subspace closed under pointwise min and max. -/
abbrev IsVectorLattice {X : Type u} (V : Submodule ℝ (X → ℝ)) : Prop :=
  Specs.IsVectorLattice V

/-- Stone truncation, without a constant-unit hypothesis. -/
abbrev IsStone {X : Type u} (V : Submodule ℝ (X → ℝ)) : Prop :=
  Specs.IsStone V

namespace IsVectorLattice

variable {X : Type u} {V : Submodule ℝ (X → ℝ)}

lemma min_mem (hV : IsVectorLattice V) {f g : X → ℝ} (hf : f ∈ V) (hg : g ∈ V) :
    (fun x => min (f x) (g x)) ∈ V :=
  hV.1 f hf g hg

lemma max_mem (hV : IsVectorLattice V) {f g : X → ℝ} (hf : f ∈ V) (hg : g ∈ V) :
    (fun x => max (f x) (g x)) ∈ V :=
  hV.2 f hf g hg

end IsVectorLattice

/-- The positive part f⁺ belongs to the original subspace. -/
theorem positivePart_mem {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (f : X → ℝ) (hf : f ∈ V) :
    (fun x => max (f x) 0) ∈ V :=
  hV.max_mem hf V.zero_mem

/-- The negative part f⁻ belongs to the original subspace. -/
theorem negativePart_mem {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (f : X → ℝ) (hf : f ∈ V) :
    (fun x => max (-f x) 0) ∈ V :=
  hV.max_mem (V.neg_mem hf) V.zero_mem

/-- The pointwise absolute value belongs to the original subspace. -/
theorem abs_mem {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (f : X → ℝ) (hf : f ∈ V) :
    (fun x => |f x|) ∈ V := by
  simpa only [abs_eq_max_neg, Pi.neg_apply] using hV.max_mem hf (V.neg_mem hf)

/-- Positive scaling transports truncation at one to truncation at b > 0. -/
theorem min_const_mem {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hStone : IsStone V) (f : X → ℝ) (hf : f ∈ V) (b : ℝ) (hb : 0 < b) :
    (fun x => min (f x) b) ∈ V := by
  have h := V.smul_mem b (hStone (b⁻¹ • f) (V.smul_mem b⁻¹ hf))
  have hscale : b • (fun x => min ((b⁻¹ • f) x) 1) = (fun x => min (f x) b) := by
    funext x
    change b * min (b⁻¹ * f x) 1 = min (f x) b
    rw [mul_min_of_nonneg _ _ hb.le, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul,
      mul_one]
  rw [hscale] at h
  exact h

theorem empty_domain_function {X : Type u} [IsEmpty X] (f : X → ℝ) : f = 0 := by
  funext x
  exact isEmptyElim x

theorem empty_domain_conditions {X : Type u} [IsEmpty X]
    (V : Submodule ℝ (X → ℝ)) : IsVectorLattice V ∧ IsStone V := by
  have hmem (f : X → ℝ) : f ∈ V := by
    rw [empty_domain_function f]
    exact V.zero_mem
  exact ⟨⟨fun f _ g _ => hmem _, fun f _ g _ => hmem _⟩, fun f _ => hmem _⟩

theorem stone_without_unit :
    IsVectorLattice (⊥ : Submodule ℝ (Unit → ℝ)) ∧
      IsStone (⊥ : Submodule ℝ (Unit → ℝ)) ∧
      (fun _ : Unit => (1 : ℝ)) ∉ (⊥ : Submodule ℝ (Unit → ℝ)) := by
  have hlattice : IsVectorLattice (⊥ : Submodule ℝ (Unit → ℝ)) := by
    constructor <;> intro f hf g hg
    all_goals
      rw [Submodule.mem_bot] at hf hg ⊢
      subst f
      subst g
      funext x
      simp
  refine ⟨hlattice, ?_, ?_⟩
  · intro f hf
    rw [Submodule.mem_bot] at hf ⊢
    subst f
    funext x
    exact min_eq_left zero_le_one
  · intro h
    have hfun := (Submodule.mem_bot ℝ).mp h
    have hval := congrFun hfun ()
    exact one_ne_zero hval

end D11.Ch23
