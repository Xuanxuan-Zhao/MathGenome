import MathGenome.Internal.Specs.D07.Ch06.CompositionSeriesDefinition

/-!
Composition series and their factors (`K07.06.composition_series_definition`,
paper.tex:1130–1135). The shared representation imposes normality only in
the next term. A factor list has one quotient for every strict step, so
multiplicities are retained. The definition applies to all groups, while
the statements below retain this chapter's finite-group setting.
-/

namespace D07.Ch06.CompositionSeriesDefinition

open Specs.D07.Ch06.CompositionSeriesDefinition

universe u

/-- A finite strictly increasing subnormal chain from the identity subgroup
to the whole group, with simple adjacent quotients. -/
abbrev CompositionSeries (G : Type u) [Group G] : Type u := Series G

/-- The defining conditions for an unbundled finite chain. -/
def IsCompositionSeries {G : Type u} [Group G] (r : ℕ)
    (term : Fin (r + 1) → Subgroup G) : Prop :=
  chainPredicateValue r term

/-- Factors are indexed by ALL steps, including repetitions. -/
abbrev compositionFactor {G : Type u} [Group G] (s : CompositionSeries G)
    (i : Fin s.length) : Type u := factorValue s i

/-- The quotient factors in their chain order, counted with multiplicity. -/
def compositionFactors {G : Type u} [Group G] (s : CompositionSeries G) : List (Type u) :=
  List.ofFn (compositionFactor s)

theorem series_conditions (G : Type u) [Group G] [Finite G] (s : CompositionSeries G) :
    IsCompositionSeries s.length s.term :=
  ⟨s.first_eq_bot, s.last_eq_top, s.strictMono, fun i => ⟨s.normal i, s.simple i⟩⟩

/-- The representation accepts every chain satisfying exactly the source
conditions, without any additional ambient-normality assumption. -/
theorem chain_characterization (G : Type u) [Group G] [Finite G] (r : ℕ)
    (term : Fin (r + 1) → Subgroup G) :
    IsCompositionSeries r term ↔
      ∃ s : CompositionSeries G, ∃ h : s.length = r,
        ∀ i : Fin (s.length + 1), s.term i = term (Fin.cast (congrArg (· + 1) h) i) := by
  constructor
  · rintro ⟨hfirst, hlast, hstrict, hsteps⟩
    let s : CompositionSeries G := {
      length := r
      term := term
      first_eq_bot := hfirst
      last_eq_top := hlast
      strictMono := hstrict
      normal := fun i => (hsteps i).choose
      simple := fun i => (hsteps i).choose_spec }
    exact ⟨s, rfl, fun _ => rfl⟩
  · rintro ⟨s, h, ht⟩
    cases h
    have heq : s.term = term := funext ht
    have hs := series_conditions G s
    simpa only [heq] using hs

theorem adjacent_strict (G : Type u) [Group G] [Finite G]
    (s : CompositionSeries G) (i : Fin s.length) :
    s.term i.castSucc < s.term i.succ :=
  s.strictMono Fin.castSucc_lt_succ

theorem adjacent_normal (G : Type u) [Group G] [Finite G]
    (s : CompositionSeries G) (i : Fin s.length) :
    ((s.term i.castSucc).subgroupOf (s.term i.succ)).Normal :=
  s.normal i

theorem factor_simple (G : Type u) [Group G] [Finite G]
    (s : CompositionSeries G) (i : Fin s.length) :
    IsSimpleGroup (compositionFactor s i) :=
  s.simple i

theorem factor_list_length (G : Type u) [Group G] [Finite G] (s : CompositionSeries G) :
    (compositionFactors s).length = s.length :=
  List.length_ofFn

theorem factor_list_entry (G : Type u) [Group G] [Finite G]
    (s : CompositionSeries G) (i : Fin s.length) :
    (compositionFactors s)[i.val]'(by simp [compositionFactors]) =
      compositionFactor s i := by
  simp [compositionFactors]

/-- The one-term chain, with no factors, for a trivial group. -/
theorem trivial_series (G : Type u) [Group G] [Finite G] [Subsingleton G] :
    ∃ s : CompositionSeries G, s.length = 0 ∧ compositionFactors s = [] := by
  let s : CompositionSeries G := {
    length := 0
    term := fun _ => ⊥
    first_eq_bot := rfl
    last_eq_top := Subsingleton.elim _ _
    strictMono := fun i j hij =>
      (Nat.not_lt_zero i.val (lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt))).elim
    normal := fun i => Fin.elim0 i
    simple := fun i => Fin.elim0 i }
  exact ⟨s, rfl, List.ofFn_zero⟩

theorem zero_length_iff_trivial (G : Type u) [Group G] [Finite G]
    (s : CompositionSeries G) : s.length = 0 ↔ Subsingleton G := by
  constructor
  · intro h
    have hindex : (0 : Fin (s.length + 1)) = Fin.last s.length := by
      apply Fin.ext
      simpa using h.symm
    have hbt : (⊥ : Subgroup G) = ⊤ :=
      s.first_eq_bot.symm.trans ((congrArg s.term hindex).trans s.last_eq_top)
    have hone : ∀ x : G, x = 1 := fun x =>
      Subgroup.mem_bot.mp (hbt.symm ▸ Subgroup.mem_top x)
    exact ⟨fun x y => (hone x).trans (hone y).symm⟩
  · intro h
    haveI : Subsingleton G := h
    by_contra hne
    have hpos : 0 < s.length := Nat.pos_of_ne_zero hne
    have hstep := adjacent_strict G s ⟨0, hpos⟩
    exact (ne_of_lt hstep) (Subsingleton.elim _ _)

end D07.Ch06.CompositionSeriesDefinition
