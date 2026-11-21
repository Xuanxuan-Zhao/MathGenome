import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.ColumnAlternation
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.DominanceMultiplicity

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev spechtHomSpace := @Specs.AdvancedFiniteGroupRepresentations.spechtHomSpace
abbrev SpechtHom := @Specs.AdvancedFiniteGroupRepresentations.SpechtHom
abbrev spechtInclusion := @Specs.AdvancedFiniteGroupRepresentations.spechtInclusion

variable {n : ℕ} {p q : Partition n}

/-- Agreement with the usual intertwining condition for the inherited action. -/
theorem mem_spechtHomSpace_iff (f : SpechtModule p →ₗ[ℂ] PermutationModule q) :
    f ∈ spechtHomSpace p q ↔
      ∀ (g : SymmetricGroup n) (v : SpechtModule p),
        f ((spechtSubrepresentation p).toRepresentation g v) =
          permutationRepresentation q g (f v) := by
  constructor
  · intro hf g v
    exact hf g v _ rfl
  · intro hf g v w hw
    have he : w = (spechtSubrepresentation p).toRepresentation g v := Subtype.ext hw
    rw [he]
    exact hf g v

/-- A polytabloid, regarded as an element of the original Specht subspace. -/
def spechtPolytabloid (t : Tableau p) : SpechtModule p :=
  ⟨polytabloid t, polytabloid_mem_specht t⟩

@[simp] theorem spechtPolytabloid_val (t : Tableau p) :
    (spechtPolytabloid t).val = polytabloid t := rfl

theorem spechtHom_polytabloid_equivariant (f : SpechtHom p q)
    (g : SymmetricGroup n) (t : Tableau p) :
    f.val (spechtPolytabloid (g • t)) =
      permutationRepresentation q g (f.val (spechtPolytabloid t)) :=
  f.property g _ _ (polytabloid_equivariant g t).symm

/-- Evaluation on any polytabloid determines an intertwiner. -/
theorem spechtHom_ext_polytabloid (t : Tableau p) (f h : SpechtHom p q)
    (he : f.val (spechtPolytabloid t) = h.val (spechtPolytabloid t)) : f = h := by
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  obtain ⟨x, hx⟩ := v
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨g, hg, _⟩ := tableau_existsUnique t u
    subst u
    exact (spechtHom_polytabloid_equivariant f g t).trans
      ((congrArg (permutationRepresentation q g) he).trans
        (spechtHom_polytabloid_equivariant h g t).symm)
  | zero => exact (map_zero f.val).trans (map_zero h.val).symm
  | add x y hx hy ihx ihy =>
    change f.val (⟨x, hx⟩ + ⟨y, hy⟩) = h.val (⟨x, hx⟩ + ⟨y, hy⟩)
    simp only [map_add, ihx, ihy]
  | smul a x hx ih =>
    change f.val (a • (⟨x, hx⟩ : SpechtModule p)) =
      h.val (a • (⟨x, hx⟩ : SpechtModule p))
    simp only [map_smul, ih]

/-- The alternating eigenvalue is preserved by every intertwiner. -/
theorem spechtHom_alternator (f : SpechtHom p q) (t : Tableau p) :
    groupAlgebraAction q (columnAlternator t) (f.val (spechtPolytabloid t)) =
      (Fintype.card (columnSubgroup t) : ℂ) • f.val (spechtPolytabloid t) := by
  classical
  rw [columnAlternator_action_sum]
  have hc (c : columnSubgroup t) :
      permutationRepresentation q c.val (f.val (spechtPolytabloid t)) =
        permutationSign c.val • f.val (spechtPolytabloid t) := by
    rw [← spechtHom_polytabloid_equivariant]
    have he : spechtPolytabloid (c.val • t) =
        permutationSign c.val • spechtPolytabloid t :=
      Subtype.ext (polytabloid_column t c)
    rw [he, map_smul]
  simp only [hc, smul_smul, permutationSign_sq, one_smul, Finset.sum_const,
    Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

/-- In forbidden dominance, the alternator vanishes on the whole target. -/
theorem columnAlternator_eq_zero_of_not_dominates (t : Tableau p)
    (hpq : ¬ dominates p q) (x : PermutationModule q) :
    groupAlgebraAction q (columnAlternator t) x = 0 := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact map_zero _
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | single r z =>
    induction r using Quotient.inductionOn with
    | _ u =>
      change groupAlgebraAction q (columnAlternator t)
        (MonoidAlgebra.single (tabloid u) z) = 0
      have hz : MonoidAlgebra.single (tabloid u) z =
          z • MonoidAlgebra.single (tabloid u) (1 : ℂ) := by simp
      rw [hz, map_smul, columnAlternator_collision t u (row_column_test t u hpq), smul_zero]

/-- The group order eigenvalue is invertible over the stated coefficient field. -/
theorem columnSubgroup_card_ne_zero (t : Tableau p) :
    (Fintype.card (columnSubgroup t) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

theorem spechtInclusion_ne_zero (p : Partition n) : spechtInclusion p ≠ 0 := by
  intro h
  have he := congrArg (fun f : SpechtHom p p =>
    f.val (spechtPolytabloid (canonicalTableau p))) h
  exact polytabloid_ne_zero _ he

/-- Off the dominance order every equivariant map vanishes. -/
theorem spechtHom_eq_zero_of_not_dominates (hpq : ¬ dominates p q)
    (f : SpechtHom p q) : f = 0 := by
  let t := canonicalTableau p
  apply spechtHom_ext_polytabloid t
  have he := spechtHom_alternator f t
  rw [columnAlternator_eq_zero_of_not_dominates t hpq] at he
  exact (smul_eq_zero.mp he.symm).resolve_left (columnSubgroup_card_ne_zero t)

theorem dominance_of_nonzero_hom (p q : Partition n)
    (h : Nontrivial (SpechtHom p q)) : dominates p q := by
  letI := h
  by_contra hpq
  obtain ⟨f, hf⟩ := exists_ne (0 : SpechtHom p q)
  exact hf (spechtHom_eq_zero_of_not_dominates hpq f)

/-- In equal shape, each intertwiner is a scalar multiple of the inclusion. -/
theorem diagonal_hom_scalar (p : Partition n) (f : SpechtHom p p) :
    ∃ a : ℂ, a • spechtInclusion p = f := by
  let t := canonicalTableau p
  let c : ℂ := Fintype.card (columnSubgroup t)
  let a : ℂ := c⁻¹ * tabloidHermitian (f.val (spechtPolytabloid t)) (polytabloid t)
  have hc : c ≠ 0 := columnSubgroup_card_ne_zero t
  have he : c • f.val (spechtPolytabloid t) =
      tabloidHermitian (f.val (spechtPolytabloid t)) (polytabloid t) • polytabloid t :=
    (spechtHom_alternator f t).symm.trans (columnAlternator_rank_one t _)
  refine ⟨a, spechtHom_ext_polytabloid t _ _ ?_⟩
  change a • polytabloid t = f.val (spechtPolytabloid t)
  calc
    a • polytabloid t = c⁻¹ • (c • f.val (spechtPolytabloid t)) := by
      rw [he, smul_smul]
    _ = f.val (spechtPolytabloid t) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem diagonal_hom_finrank (p : Partition n) :
    Module.finrank ℂ (SpechtHom p p) = 1 :=
  (finrank_eq_one_iff_of_nonzero' (spechtInclusion p) (spechtInclusion_ne_zero p)).mpr
    (diagonal_hom_scalar p)

end AdvancedFiniteGroupRepresentations
