import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Quotients
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DerivedLowerSeries

/-! LA-A02: arbitrary fields, with no dimension or characteristic assumption.
The lower central series uses the source's positive indexing; its value at zero
is defined to be the whole algebra. Upper central series and the nilpotent
extension counterexample are allocated separately to LA-A02-Upper and LA-U02. -/

universe u v w
namespace LieAlgebrasAndRepresentations

variable (k : Type u) (L : Type v) [Field k] [LieRing L] [LieAlgebra k L]

def derivedSeries (n : ℕ) : LieIdeal k L := LieAlgebra.derivedSeries k L n

def lowerCentralSeries (n : ℕ) : LieIdeal k L :=
  LieModule.lowerCentralSeries k L L (n - 1)

variable {k L}

theorem bracket_span (I J : LieIdeal k L) :
    (⁅I, J⁆ : LieIdeal k L).toSubmodule =
      Submodule.span k { ⁅x, y⁆ | (x ∈ I) (y ∈ J) } :=
  LieSubmodule.lieIdeal_oper_eq_linear_span' J I

theorem derivedSeries_zero : derivedSeries k L 0 = ⊤ := rfl

theorem derivedSeries_succ (n : ℕ) :
    derivedSeries k L (n + 1) = ⁅derivedSeries k L n, derivedSeries k L n⁆ :=
  LieAlgebra.derivedSeriesOfIdeal_succ k L ⊤ n

theorem lowerCentralSeries_one : lowerCentralSeries k L 1 = ⊤ := rfl

theorem lowerCentralSeries_succ (n : ℕ) (hn : 0 < n) :
    lowerCentralSeries k L (n + 1) = ⁅(⊤ : LieIdeal k L), lowerCentralSeries k L n⁆ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact LieModule.lowerCentralSeries_succ k L L m

theorem series_are_ideals (n : ℕ) (x y : L) :
    (y ∈ derivedSeries k L n → ⁅x, y⁆ ∈ derivedSeries k L n) ∧
    (y ∈ lowerCentralSeries k L n → ⁅x, y⁆ ∈ lowerCentralSeries k L n) :=
  ⟨fun h => (derivedSeries k L n).lie_mem h,
   fun h => (lowerCentralSeries k L n).lie_mem h⟩

theorem solvable_iff : LieAlgebra.IsSolvable L ↔ ∃ n, derivedSeries k L n = ⊥ :=
  LieAlgebra.isSolvable_iff k L

theorem nilpotent_iff : LieRing.IsNilpotent L ↔
    ∃ n, 0 < n ∧ lowerCentralSeries k L n = ⊥ := by
  rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff k]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.zero_lt_succ n, hn⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n - 1, hn⟩

theorem solvable_subalgebra (S : LieSubalgebra k L) (h : LieAlgebra.IsSolvable L) :
    LieAlgebra.IsSolvable S := by
  exact (show Function.Injective S.incl from Subtype.val_injective).lieAlgebra_isSolvable

theorem nilpotent_subalgebra (S : LieSubalgebra k L) (h : LieRing.IsNilpotent L) :
    LieRing.IsNilpotent S := by
  exact (show Function.Injective S.incl from Subtype.val_injective).lieAlgebra_isNilpotent

theorem solvable_quotient (I : LieIdeal k L) (h : LieAlgebra.IsSolvable L) :
    LieAlgebra.IsSolvable (L ⧸ I) := by
  obtain ⟨q, _, hq, _⟩ := quotient_projection I
  exact hq.lieAlgebra_isSolvable

theorem nilpotent_quotient (I : LieIdeal k L) (h : LieRing.IsNilpotent L) :
    LieRing.IsNilpotent (L ⧸ I) := by
  obtain ⟨q, _, hq, _⟩ := quotient_projection I
  exact hq.lieAlgebra_isNilpotent

theorem solvable_extension (I : LieIdeal k L) (hI : LieAlgebra.IsSolvable I)
    (hQ : LieAlgebra.IsSolvable (L ⧸ I)) : LieAlgebra.IsSolvable L := by
  obtain ⟨r, hr⟩ := (LieAlgebra.isSolvable_iff k (L ⧸ I)).mp hQ
  obtain ⟨s, hs⟩ := (LieAlgebra.isSolvable_iff k I).mp hI
  obtain ⟨q, _, hq, hker⟩ := quotient_projection I
  have hle : LieAlgebra.derivedSeries k L r ≤ I := by
    rw [← hker, ← LieIdeal.map_eq_bot_iff]
    rw [LieIdeal.derivedSeries_map_eq r hq, hr]
  apply LieAlgebra.IsSolvable.mk (R := k) (k := s + r)
  rw [LieAlgebra.derivedSeries_def, LieAlgebra.derivedSeriesOfIdeal_add]
  apply le_bot_iff.mp
  calc
    LieAlgebra.derivedSeriesOfIdeal k L s (LieAlgebra.derivedSeries k L r) ≤
        LieAlgebra.derivedSeriesOfIdeal k L s I :=
      LieAlgebra.derivedSeriesOfIdeal_mono hle s
    _ = ⊥ := (I.derivedSeries_eq_bot_iff s).mp hs

private theorem bracket_jacobi_le (I J K : LieIdeal k L) :
    ⁅⁅I, J⁆, K⁆ ≤ ⁅I, ⁅J, K⁆⁆ ⊔ ⁅J, ⁅I, K⁆⁆ := by
  rw [LieSubmodule.lie_le_iff]
  intro x hx
  change x ∈ (⁅I, J⁆ : LieIdeal k L).toSubmodule at hx
  rw [bracket_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    intro c hc
    rw [lie_lie]
    apply sub_mem
    · exact LieSubmodule.mem_sup_left (LieSubmodule.lie_mem_lie ha (LieSubmodule.lie_mem_lie hb hc))
    · exact LieSubmodule.mem_sup_right (LieSubmodule.lie_mem_lie hb (LieSubmodule.lie_mem_lie ha hc))
  | zero => intro c _; simp
  | add x y _ _ hx hy =>
    intro c hc
    rw [add_lie]
    exact add_mem (hx c hc) (hy c hc)
  | smul a x _ hx =>
    intro c hc
    rw [smul_lie]
    exact Submodule.smul_mem (⁅I, ⁅J, K⁆⁆ ⊔ ⁅J, ⁅I, K⁆⁆).toSubmodule a (hx c hc)

private theorem lowerCentralSeries_bracket_aux (i j : ℕ) :
    ⁅LieModule.lowerCentralSeries k L L i, LieModule.lowerCentralSeries k L L j⁆ ≤
      LieModule.lowerCentralSeries k L L (i + j + 1) := by
  induction i generalizing j with
  | zero =>
    rw [Nat.zero_add, LieModule.lowerCentralSeries_zero, LieModule.lowerCentralSeries_succ]
  | succ i ih =>
    rw [LieModule.lowerCentralSeries_succ]
    apply (bracket_jacobi_le _ _ _).trans
    apply sup_le
    · simpa only [← LieModule.lowerCentralSeries_succ, Nat.succ_add] using
        (LieSubmodule.mono_lie_right (⊤ : LieIdeal k L) (ih j) :
          ⁅(⊤ : LieIdeal k L),
            ⁅LieModule.lowerCentralSeries k L L i, LieModule.lowerCentralSeries k L L j⁆⁆ ≤
          ⁅(⊤ : LieIdeal k L), LieModule.lowerCentralSeries k L L (i + j + 1)⁆)
    · simpa only [← LieModule.lowerCentralSeries_succ, Nat.succ_add, Nat.add_succ] using
        ih (j + 1)

theorem lowerCentralSeries_bracket (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    ⁅lowerCentralSeries k L i, lowerCentralSeries k L j⁆ ≤
      lowerCentralSeries k L (i + j) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  simpa only [lowerCentralSeries, Nat.succ_sub_one, Nat.succ_add, Nat.add_succ] using
    lowerCentralSeries_bracket_aux (k := k) (L := L) a b

end LieAlgebrasAndRepresentations
