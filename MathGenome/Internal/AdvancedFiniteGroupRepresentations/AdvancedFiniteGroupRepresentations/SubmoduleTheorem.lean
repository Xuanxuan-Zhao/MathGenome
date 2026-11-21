import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.ColumnAlternation
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SubmoduleTheorem

noncomputable section
namespace AdvancedFiniteGroupRepresentations

abbrev tabloidOrthogonal := @Specs.AdvancedFiniteGroupRepresentations.tabloidOrthogonal

variable {n : ℕ} {p : Partition n}

/-- The first assertion of the submodule theorem, with the source's first-linear form. -/
theorem submodule_rank_one (t : Tableau p) (x : PermutationModule p) :
    groupAlgebraAction p (columnAlternator t) x =
      tabloidHermitian x (polytabloid t) • polytabloid t :=
  columnAlternator_rank_one t x

/-- An invariant complex subspace is closed under column alternation. -/
theorem columnAlternator_mem (t : Tableau p)
    (U : Subrepresentation (permutationRepresentation p))
    {x : PermutationModule p} (hx : x ∈ U) :
    groupAlgebraAction p (columnAlternator t) x ∈ U := by
  classical
  rw [columnAlternator_action_sum]
  exact U.toSubmodule.sum_mem (fun c _ =>
    U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule c.val hx))

/-- Nonzero pairing with a polytabloid places that polytabloid in the submodule. -/
theorem polytabloid_mem_of_pairing (t : Tableau p)
    (U : Subrepresentation (permutationRepresentation p))
    {x : PermutationModule p} (hx : x ∈ U)
    (h : tabloidHermitian x (polytabloid t) ≠ 0) : polytabloid t ∈ U := by
  have hm := columnAlternator_mem t U hx
  rw [submodule_rank_one] at hm
  have hi := U.toSubmodule.smul_mem (tabloidHermitian x (polytabloid t))⁻¹ hm
  change polytabloid t ∈ U.toSubmodule
  simpa only [smul_smul, inv_mul_cancel₀ h, one_smul] using hi

/-- The full submodule dichotomy in the original permutation module. -/
theorem submodule_theorem (U : Subrepresentation (permutationRepresentation p)) :
    spechtSpan p ≤ U.toSubmodule ∨ U.toSubmodule ≤ tabloidOrthogonal (spechtSpan p) := by
  classical
  by_cases h : ∃ (x : PermutationModule p) (_hx : x ∈ U) (t : Tableau p),
      tabloidHermitian x (polytabloid t) ≠ 0
  · obtain ⟨x, hx, t, ht⟩ := h
    exact Or.inl (specht_generated t U (polytabloid_mem_of_pairing t U hx ht))
  · right
    intro x hx y hy
    change tabloidHermitian x y = 0
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, rfl⟩ := hy
      exact not_ne_iff.mp (fun hn => h ⟨x, hx, t, hn⟩)
    | zero =>
      simp [tabloidHermitian_library, tabloidCoordinates_zero]
    | add y z hy hz ihy ihz =>
      rw [tabloidHermitian_add_right, ihy, ihz, add_zero]
    | smul a y hy ih =>
      rw [tabloidHermitian_smul_right, ih, mul_zero]

/-- Positive definiteness eliminates the orthogonal alternative inside Specht. -/
theorem specht_invariant_subspace (U : Subrepresentation (permutationRepresentation p))
    (hU : U.toSubmodule ≤ spechtSpan p) :
    U.toSubmodule = ⊥ ∨ U.toSubmodule = spechtSpan p := by
  rcases submodule_theorem U with h | h
  · exact Or.inr (le_antisymm hU h)
  · left
    apply le_antisymm ?_ bot_le
    intro x hx
    exact (tabloidHermitian_definite x).mp (h hx x (hU hx))

/-- Any realization of the inherited Specht action is irreducible. -/
theorem specht_irreducible (p : Partition n)
    (ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (hρ : ∀ g v, (ρ g v).val = permutationRepresentation p g v.val) :
    ρ.IsIrreducible := by
  classical
  let e : SpechtModule p := ⟨polytabloid (canonicalTableau p), polytabloid_mem_specht _⟩
  have he : e ≠ 0 := by
    intro hz
    exact polytabloid_ne_zero _ (congrArg Subtype.val hz)
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hm : e ∈ (⊥ : Subrepresentation ρ) := by rw [h]; trivial
    exact he hm
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbt⟩⟩
  constructor
  intro V
  let U : Subrepresentation (permutationRepresentation p) :=
    { toSubmodule := V.toSubmodule.map (spechtSpan p).subtype
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨v, hv, rfl⟩ := hx
        exact ⟨ρ g v, V.apply_mem_toSubmodule g hv, hρ g v⟩ }
  have hU : U.toSubmodule ≤ spechtSpan p := by
    rintro x ⟨v, hv, rfl⟩
    exact v.property
  rcases specht_invariant_subspace U hU with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm ?_ bot_le
    intro v hv
    have hm : v.val ∈ U.toSubmodule := ⟨v, hv, rfl⟩
    rw [show U.toSubmodule = ⊥ from h] at hm
    exact Subtype.ext hm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm le_top
    intro v _
    have hm : v.val ∈ U.toSubmodule := by rw [show U.toSubmodule = spechtSpan p from h]; exact v.property
    obtain ⟨w, hw, hwv⟩ := hm
    have hwv' : w = v := Subtype.ext hwv
    exact hwv' ▸ hw

/-- Nonzero irreducibility, including existence of the actual inherited action. -/
theorem specht_nonzero_irreducible (p : Partition n) :
    spechtSpan p ≠ ⊥ ∧
    ∃ ρ : Representation ℂ (SymmetricGroup n) (SpechtModule p),
      (∀ g v, (ρ g v).val = permutationRepresentation p g v.val) ∧ ρ.IsIrreducible := by
  obtain ⟨ρ, hρ⟩ := specht_inheritedAction p
  exact ⟨specht_nonzero p, ρ, hρ, specht_irreducible p ρ hρ⟩

end AdvancedFiniteGroupRepresentations
