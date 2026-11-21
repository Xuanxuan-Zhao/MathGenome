import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.MaximalSubfield
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.CentralizerDimension
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SeparableSubfield
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SubfieldSplitting

/-! Maximal subfields of central division algebras (RM03-C04.09). -/

namespace RM03.CSA

universe u v

variable {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]

abbrev IsMaximalSubfield (E : Subalgebra k D) : Prop :=
  Specs.RM03.CSA.isMaximalSubfield E

private theorem subfield_le_centralizer (E F : Subalgebra k D) (hF : IsField F)
    (hEF : E ≤ F) : F ≤ Subalgebra.centralizer k (E : Set D) := by
  intro x hx
  exact (Subalgebra.mem_centralizer_iff k).2 fun y hy =>
    congrArg Subtype.val (hF.mul_comm ⟨y, hEF hy⟩ ⟨x, hx⟩)

private theorem isField_adjoin_insert (E : Subalgebra k D) (hE : IsField E)
    [FiniteDimensional k D] {x : D} (hx : x ∈ Subalgebra.centralizer k (E : Set D)) :
    IsField (Algebra.adjoin k (insert x (E : Set D))) := by
  let F := Algebra.adjoin k (insert x (E : Set D))
  have hcomm (y : D) (hy : y ∈ E) : Commute y x :=
    (Subalgebra.mem_centralizer_iff k).mp hx y hy
  have hpair : (E : Set D).Pairwise Commute := fun a ha b hb _ =>
    congrArg Subtype.val (hE.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
  let : IsMulCommutative F :=
    Algebra.isMulCommutative_adjoin k (hpair.insert fun y hy _ => ⟨(hcomm y hy).symm, hcomm y hy⟩)
  let : CommRing F := { (inferInstance : Ring F) with mul_comm := mul_comm' }
  let : IsDomain F := Function.Injective.isDomain F.val Subtype.val_injective
  let : Field F := fieldOfFiniteDimensional k F
  exact Field.toIsField F

/-- A subfield is maximal exactly when it is its own centralizer. -/
theorem maximal_subfield_iff_centralizer_eq (hD : IsCentralDivision k D)
    (E : Subalgebra k D) (hE : IsField E) :
    IsMaximalSubfield E ↔ Subalgebra.centralizer k (E : Set D) = E := by
  constructor
  · intro hmax
    let : FiniteDimensional k D := hD.2
    refine le_antisymm (fun x hx => ?_) (subfield_le_centralizer E E hE le_rfl)
    let F := Algebra.adjoin k (insert x (E : Set D))
    have hEF : E ≤ F := fun _ hy => Algebra.subset_adjoin (Set.mem_insert_of_mem x hy)
    exact hmax.2 F (isField_adjoin_insert E hE hx) hEF
      (Algebra.subset_adjoin (Set.mem_insert x (E : Set D)))
  · intro hC
    refine ⟨hE, fun F hF hEF => ?_⟩
    exact hC ▸ subfield_le_centralizer E F hF hEF

/-- The maximal subfields are precisely the subfields whose degree equals that of the algebra. -/
theorem maximal_subfield_iff_degree (hD : IsCentralDivision k D)
    (E : Subalgebra k D) (hE : IsField E) :
    IsMaximalSubfield E ↔ Module.finrank k E = degree k D := by
  let : FiniteDimensional k D := hD.2
  let : Field E := hE.toField
  have hD' := isCentralSimple_of_isCentralDivision k D hD
  have hdim := (centralizer_simple_and_finrank hD' E inferInstance).2
  rw [maximal_subfield_iff_centralizer_eq hD E hE]
  constructor
  · intro hC
    rw [hC, ← pow_two] at hdim
    exact ((degree_eq_iff hD').2 ⟨Module.finrank_pos, hdim.symm⟩).symm
  · intro hdeg
    have hCdim : Module.finrank k (Subalgebra.centralizer k (E : Set D)) = degree k D := by
      rw [hdeg, finrank_eq_degree_sq hD', pow_two] at hdim
      exact Nat.eq_of_mul_eq_mul_left (degree_pos hD') hdim
    exact (Subalgebra.eq_of_le_of_finrank_eq
      (subfield_le_centralizer E E hE le_rfl) (hdeg.trans hCdim.symm)).symm

/-- A maximal subfield splits the division algebra over its inherited field structure. -/
theorem maximal_subfield_splits (hD : IsCentralDivision k D) (E : Subalgebra k D)
    (hE : IsMaximalSubfield E) :
    letI := hE.1.toField
    Nonempty (BaseChange k E D ≃ₐ[E] Matrix (Fin (degree k D)) (Fin (degree k D)) E) := by
  let := hE.1.toField
  exact subfield_splits E.val hD ((maximal_subfield_iff_degree hD E hE.1).mp hE)

/-- The degree-sized separable subfield supplied by RM03-C04.05 is maximal. -/
theorem exists_separable_maximal_subfield (hD : IsCentralDivision k D) :
    ∃ E : Subalgebra k D, IsMaximalSubfield E ∧ Algebra.IsSeparable k E ∧
      Module.finrank k E = degree k D := by
  obtain ⟨E, hfield, hsep, hdeg⟩ := exists_separable_subfield hD
  exact ⟨E, (maximal_subfield_iff_degree hD E hfield).mpr hdeg, hsep, hdeg⟩

end RM03.CSA
