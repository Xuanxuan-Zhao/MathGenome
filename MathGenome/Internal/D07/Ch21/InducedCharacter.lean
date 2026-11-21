import MathGenome.Internal.Specs.D07.Ch21.InducedCharacter
import MathGenome.Internal.D07.Ch17.Characters
import MathGenome.Internal.D07.Ch21.InductionCosetModel

namespace D07.Ch21.InducedCharacter
universe u v
noncomputable section
open scoped BigOperators Classical
open Specs.D07.Ch21.InducedCharacter
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.InductionCosetModelCosetCoordinateEquivalence
open D07.Ch21.InductionCosetModelInductionConventionBridge
open D07.Ch21.InductionCosetModelCosetCoordinateEquivalence

/-- Trace on a finite direct sum is the sum of the diagonal block traces. -/
lemma trace_finsupp {ι : Type*} [Fintype ι]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ (ι →₀ V)) :
    LinearMap.trace ℂ (ι →₀ V) T =
      ∑ i, LinearMap.trace ℂ V ((Finsupp.lapply i).comp (T.comp (Finsupp.lsingle i))) := by
  classical
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ (Finsupp.basis fun _ : ι => b)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    Finsupp.basis_repr, Finsupp.coe_basis, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply]


variable {G : Type u} [Group G] (H : Subgroup G)

lemma extendByZero_conj (ψ : H → ℂ) (hψ : IsClassFunction ψ)
    (y : G) (h : H) :
    extendByZero H ψ ((h : G)⁻¹ * y * h) = extendByZero H ψ y := by
  classical
  have hm : (h : G)⁻¹ * y * h ∈ H ↔ y ∈ H := by
    rw [H.mul_mem_cancel_right h.property, H.mul_mem_cancel_left (H.inv_mem h.property)]
  by_cases hy : y ∈ H
  · rw [extendByZero, dite_eq_left (hm.mpr hy), extendByZero, dite_eq_left hy]
    convert hψ ⟨y, hy⟩ h⁻¹ using 1
    congr 1
    apply Subtype.ext
    simp
  · simp [extendByZero, hy, mt hm.mp hy]

/-- The unique decomposition x = r(q)h, for an arbitrary transversal. -/
def cosetProductEquiv (r : G ⧸ H → G) (hr : IsTransversal H r) :
    (G ⧸ H) × H ≃ G where
  toFun p := r p.1 * p.2
  invFun x := (QuotientGroup.mk x, coefficient H r hr x)
  left_inv p := by
    rcases p with ⟨q, h⟩
    simp [coset_rep_mul H r hr, coefficient_rep_mul H r hr]
  right_inv x := rep_mul_coefficient H r hr x

lemma sum_conjugates [Fintype G] (ψ : H → ℂ) (hψ : IsClassFunction ψ)
    (r : G ⧸ H → G) (hr : IsTransversal H r) (g : G) :
    (∑ x : G, extendByZero H ψ (x⁻¹ * g * x)) =
      (Nat.card H : ℂ) * cosetSum H r ψ g := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let := Fintype.ofFinite H
  rw [← (cosetProductEquiv H r hr).sum_comp]
  simp only [cosetProductEquiv, Equiv.coe_fn_mk, mul_inv_rev]
  simp_rw [show ∀ (q : G ⧸ H) (h : H),
      ((h : G)⁻¹ * (r q)⁻¹) * g * (r q * h) =
      (h : G)⁻¹ * ((r q)⁻¹ * g * r q) * h by intros; group]
  simp_rw [extendByZero_conj H ψ hψ]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  simp [cosetSum, Nat.card_eq_fintype_card]

theorem class_function_coset_formula : ClassFunctionCosetFormula.{u} := by
  intro G _ _ H ψ hψ r hr g
  rw [induceClassFunction, sum_conjugates H ψ hψ r hr g, ← mul_assoc,
    inv_mul_cancel₀, one_mul]
  exact_mod_cast Nat.card_pos (α := H).ne'

theorem class_function_induction : ClassFunctionInduction.{u} := by
  intro G _ _ H ψ _ g k
  classical
  unfold induceClassFunction
  congr 1
  let e : G ≃ G := Equiv.mulLeft k
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change (k * x)⁻¹ * (k * g * k⁻¹) * (k * x) = x⁻¹ * g * x
  group


lemma coset_fixed_iff (r : G ⧸ H → G) (hr : IsTransversal H r) (g : G)
    (q : G ⧸ H) :
    (QuotientGroup.mk (g * r q) : G ⧸ H) = q ↔ (r q)⁻¹ * g * r q ∈ H := by
  calc
    _ ↔ (QuotientGroup.mk (r q) : G ⧸ H) = QuotientGroup.mk (g * r q) := by
      rw [hr q]
      exact eq_comm
    _ ↔ (r q)⁻¹ * (g * r q) ∈ H := QuotientGroup.eq
    _ ↔ _ := by rw [mul_assoc]

lemma diagonal_block {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ))
    (hσ : ∀ k x v, σ k (notesMk H ρ x v) = notesMk H ρ (k * x) v)
    (r : G ⧸ H → G) (hr : IsTransversal H r) (g : G) (q : G ⧸ H) :
    (Finsupp.lapply q).comp
        (((coordinateEquiv H ρ r hr).symm.conj (σ g)).comp (Finsupp.lsingle q)) =
      if hy : (r q)⁻¹ * g * r q ∈ H then ρ ⟨(r q)⁻¹ * g * r q, hy⟩ else 0 := by
  classical
  ext v
  change ((coordinateEquiv H ρ r hr).symm
      (σ g (coordinateEquiv H ρ r hr (Finsupp.single q v)))) q = _
  rw [coordinateEquiv_single, hσ, coordinateEquiv_symm_mk]
  by_cases hy : (r q)⁻¹ * g * r q ∈ H
  · have hq := (coset_fixed_iff H r hr g q).mpr hy
    have hc : coefficient H r hr (g * r q) = ⟨(r q)⁻¹ * g * r q, hy⟩ := by
      apply Subtype.ext
      simp [coefficient, hq, mul_assoc]
    simp [hq, hc, hy]
  · have hq := mt (coset_fixed_iff H r hr g q).mp hy
    simp [hq, hy]

/-- The source quotient's trace is computed from exactly its fixed coset blocks. -/
lemma character_coset_formula [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (σ : Representation ℂ G (NotesInd H ρ))
    (hσ : ∀ k x v, σ k (notesMk H ρ x v) = notesMk H ρ (k * x) v)
    (r : G ⧸ H → G) (hr : IsTransversal H r) (g : G) :
    LinearMap.trace ℂ (NotesInd H ρ) (σ g) =
      cosetSum H r (Specs.D07.Ch17.Characters.characterValue ℂ H V ρ) g := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  rw [← LinearMap.trace_conj' (σ g) (coordinateEquiv H ρ r hr).symm, trace_finsupp]
  unfold cosetSum
  apply Finset.sum_congr rfl
  intro q _
  rw [diagonal_block H ρ σ hσ r hr g q]
  split_ifs with hy <;>
    simp [extendByZero, hy, Specs.D07.Ch17.Characters.characterValue]

theorem character_formulas : CharacterFormulas.{u,v} := by
  intro G _ _ H V _ _ _ ρ σ hσ r hr g
  have hψ : IsClassFunction (Specs.D07.Ch17.Characters.characterValue ℂ H V ρ) :=
    fun a b => D07.Ch17.Characters.character_conjugate ℂ H V ρ a b
  have hc := character_coset_formula H ρ σ hσ r hr g
  exact ⟨hc, hc.trans (class_function_coset_formula G H _ hψ r hr g)⟩


/-- Induction of functions by the normalized conjugacy sum. -/
def inducedClassFunction : InductionType.{u} := inductionValue

theorem induced_action_exists : InducedActionExists.{u,v} := by
  intro G _ _ H V _ _ _ ρ
  exact ⟨(D07.Ch21.InductionCosetModel.dimension G H V ρ).1,
    notesRep H ρ, notesRep_mk H ρ⟩

theorem vanishing : Vanishing.{u,v} := by
  intro G _ _ H V _ _ _ ρ σ hσ g hg
  rw [(character_formulas G H V ρ σ hσ Quotient.out QuotientGroup.out_eq' g).2]
  simp [induceClassFunction, extendByZero, hg]

theorem value_at_one : ValueAtOne.{u,v} := by
  intro G _ _ H V _ _ _ ρ σ hσ
  have := (D07.Ch21.InductionCosetModel.dimension G H V ρ).1
  rw [map_one, LinearMap.trace_one,
    (D07.Ch21.InductionCosetModel.dimension G H V ρ).2,
    Specs.D07.Ch17.Characters.characterValue, map_one, LinearMap.trace_one, Nat.cast_mul]

theorem zero_space : ZeroSpace.{u,v} := by
  intro G _ _ H V _ _ _ _ ρ σ hσ g
  have := D07.Ch21.InductionCosetModel.zero_induction G H V ρ
  have hz : σ g = 0 := Subsingleton.elim _ _
  rw [hz, map_zero]

end
end D07.Ch21.InducedCharacter
