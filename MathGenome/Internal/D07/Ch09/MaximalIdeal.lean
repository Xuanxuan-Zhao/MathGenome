import MathGenome.Internal.Specs.D07.Ch09.MaximalIdeal

/-! K07.09.maximal_ideal: properness and the absence of intermediate ideals. -/

universe u

namespace D07.Ch09.MaximalIdeal

open Specs.D07.Ch09.MaximalIdeal

/-- Maximal ideals in the commutative part of the source. -/
def isMaximal {R : Type u} [CommRing R] (M : Ideal R) : Prop :=
  M.IsMaximal

/-- Without commutativity the library lattice describes left ideals. -/
def isMaximalLeft {R : Type u} [Ring R] (M : Ideal R) : Prop :=
  M.IsMaximal

/-- Maximality among proper two-sided ideals, for a general ring. -/
def isMaximalTwoSided {R : Type u} [Ring R] (M : Ideal R) : Prop :=
  M.IsTwoSided ∧ M ≠ ⊤ ∧
    ∀ J : Ideal R, J.IsTwoSided → M < J → J = ⊤

/-- The coatom condition is exactly properness and no intermediate ideal. -/
private theorem left_iff_no_intermediate {R : Type u} [Ring R] (M : Ideal R) :
    M.IsMaximal ↔ M ≠ ⊤ ∧ ¬ ∃ J : Ideal R, M < J ∧ J < ⊤ := by
  rw [Ideal.isMaximal_def]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rintro ⟨J, hMJ, hJ⟩
    exact (ne_of_lt hJ) (h.2 J hMJ)
  · rintro ⟨hproper, h⟩
    refine ⟨hproper, ?_⟩
    intro J hMJ
    by_contra hJ
    exact h ⟨J, hMJ, lt_top_iff_ne_top.mpr hJ⟩

theorem maximalCharacterization : MaximalCharacterization.{u} := by
  intro R _ M
  exact left_iff_no_intermediate M

theorem containingIdealCharacterization : ContainingIdealCharacterization.{u} := by
  intro R _ M
  constructor
  · intro h
    refine ⟨h.ne_top, ?_⟩
    intro J hMJ
    by_cases hJM : J = M
    · exact Or.inl hJM
    · exact Or.inr (h.out.2 J (lt_of_le_of_ne hMJ (Ne.symm hJM)))
  · rintro ⟨hproper, h⟩
    apply Ideal.isMaximal_def.mpr
    refine ⟨hproper, ?_⟩
    intro J hMJ
    exact (h J hMJ.le).resolve_left (Ne.symm (ne_of_lt hMJ))

theorem maximalLeftCharacterization : MaximalLeftCharacterization.{u} := by
  intro R _ M
  exact left_iff_no_intermediate M

theorem maximalTwoSidedCharacterization : MaximalTwoSidedCharacterization.{u} := by
  intro R _ M
  constructor
  · rintro ⟨htwo, hproper, hmax⟩
    refine ⟨htwo, hproper, ?_⟩
    rintro ⟨J, hJtwo, hMJ, hJproper⟩
    exact (ne_of_lt hJproper) (hmax J hJtwo hMJ)
  · rintro ⟨htwo, hproper, hmax⟩
    refine ⟨htwo, hproper, ?_⟩
    intro J hJtwo hMJ
    by_contra hJ
    exact hmax ⟨J, hJtwo, hMJ, lt_top_iff_ne_top.mpr hJ⟩

theorem commutativeCoincidence : CommutativeCoincidence.{u} := by
  intro R _ M
  refine ⟨Iff.rfl, ?_⟩
  constructor
  · intro h
    exact ⟨inferInstance, h.ne_top, fun J _ hMJ => h.out.2 J hMJ⟩
  · rintro ⟨_, hproper, hmax⟩
    exact Ideal.isMaximal_def.mpr ⟨hproper, fun J hMJ => hmax J inferInstance hMJ⟩

theorem properness : Properness.{u} := by
  intro R _ M h
  exact ⟨h.ne_top, (Ideal.ne_top_iff_one M).mp h.ne_top⟩

theorem zeroRing : ZeroRing.{u} := by
  intro R _ _ M h
  apply (properness R M h).2
  rw [Subsingleton.elim (1 : R) 0]
  exact M.zero_mem

end D07.Ch09.MaximalIdeal
