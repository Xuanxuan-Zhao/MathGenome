import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Series

/-! Chief series and their equivariant factors for a fixed ambient group. -/

namespace ALG02GroupTheory.Chief

open Specs.ALG02GroupTheory.Chief.Series
universe u v w

/-- The cover relation between normal subgroups of the ambient group. -/
abbrev AmbientCovBy : AmbientCovByType.{u} := ambientCovByValue

/-- The source conditions on a chain with a specified length. -/
abbrev IsChiefSeries : IsChiefSeriesType.{u} := isChiefSeriesValue

/-- A chief series of a finite group, with its length and terms. -/
abbrev ChiefSeries (G : Type u) [Group G] [Finite G] : Type u := chiefSeriesValue G

/-- A group with an action of G by group automorphisms. -/
abbrev GGroup (G : Type u) (A : Type v) [Group G] [Group A] : Type (max u v) :=
  gGroupValue G A

/-- An equivariant group isomorphism for a fixed acting group G. -/
abbrev GEquiv (G : Type u) (A : Type v) (B : Type w)
    [Group G] [Group A] [Group B] [GGroup G A] [GGroup G B] : Type (max v w) :=
  gEquivValue G A B

/-- Stability of a subgroup under the G-action. -/
abbrev GInvariant {G : Type u} {A : Type v} [Group G] [Group A] [GGroup G A]
    (H : Subgroup A) : Prop :=
  gInvariantValue (G := G) H

/-- The factor L/K, using the restriction of K to L. -/
abbrev Factor {G : Type u} [Group G] (K L : Subgroup G) : Type u := factorValue K L

/-- The quotient projection from L to the factor. -/
abbrev factorMk {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] : L →* Factor K L :=
  factorMkValue K L

/-- Conjugation by G on the factor. -/
abbrev factorAction {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] [L.Normal] :
    GGroup G (Factor K L) :=
  factorActionValue K L

/-- The chief factor indexed by an adjacent pair in the series. -/
abbrev chiefFactor {G : Type u} [Group G] [Finite G]
    (s : ChiefSeries G) (i : Fin s.length) : Type u :=
  chiefFactorValue s i

/-- Each chief factor carries the same ambient G-action. -/
abbrev chiefFactorAction {G : Type u} [Group G] [Finite G]
    (s : ChiefSeries G) (i : Fin s.length) : GGroup G (chiefFactor s i) :=
  chiefFactorActionValue s i

/-- The quotient types in chain order, retaining all steps. -/
abbrev chiefFactorTypes {G : Type u} [Group G] [Finite G]
    (s : ChiefSeries G) : List (Type u) :=
  chiefFactorTypesValue s

theorem chain_characterization (G : Type u) [Group G] [Finite G]
    (r : ℕ) (N : Fin (r + 1) → Subgroup G) :
    IsChiefSeries r N ↔
      ∃ s : ChiefSeries G, ∃ h : s.length = r,
        ∀ i : Fin (s.length + 1), s.term i = N (Fin.cast (congrArg (· + 1) h) i) := by
  constructor
  · rintro ⟨hfirst, hlast, hnormal, hsteps⟩
    let s : ChiefSeries G := ⟨r, N, hfirst, hlast, hnormal, hsteps⟩
    exact ⟨s, rfl, fun _ => rfl⟩
  · rintro ⟨s, rfl, hterm⟩
    have hN : s.term = N := funext hterm
    rw [← hN]
    exact ⟨s.first_eq_bot, s.last_eq_top, s.normal, s.step⟩

theorem ChiefSeries.strictMono {G : Type u} [Group G] [Finite G]
    (s : ChiefSeries G) : StrictMono s.term :=
  Fin.strictMono_iff_lt_succ.mpr fun i => (s.step i).1

@[simp]
theorem factor_smul_mk {G : Type u} [Group G] (K L : Subgroup G)
    [K.Normal] [hL : L.Normal] (g : G) (x : L) :
    g • factorMk K L x =
      factorMk K L ⟨g * (x : G) * g⁻¹, hL.conj_mem x x.property g⟩ :=
  rfl

theorem restricted_action_is_inner {G : Type u} [Group G] (K L : Subgroup G)
    [K.Normal] [L.Normal] (x : L) :
    MulDistribMulAction.toMulAut G (Factor K L) (x : G) = MulAut.conj (factorMk K L x) := by
  apply MulEquiv.ext
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
  change (x : G) • factorMk K L y =
    factorMk K L x * factorMk K L y * (factorMk K L x)⁻¹
  rw [factor_smul_mk]
  change factorMk K L (x * y * x⁻¹) = _
  simp only [map_mul, map_inv]

theorem every_inner_automorphism_occurs {G : Type u} [Group G] (K L : Subgroup G)
    [K.Normal] [L.Normal] (z : Factor K L) :
    ∃ x : L, MulDistribMulAction.toMulAut G (Factor K L) (x : G) = MulAut.conj z := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
  exact ⟨x, restricted_action_is_inner K L x⟩

theorem invariant_subgroup_normal {G : Type u} [Group G] (K L : Subgroup G)
    [K.Normal] [L.Normal] (H : Subgroup (Factor K L)) (hH : GInvariant (G := G) H) :
    H.Normal := by
  constructor
  intro z hz q
  obtain ⟨x, hx⟩ := every_inner_automorphism_occurs K L q
  change MulAut.conj q z ∈ H
  rw [← hx]
  exact hH (x : G) z hz

theorem factor_list_length {G : Type u} [Group G] [Finite G] (s : ChiefSeries G) :
    (chiefFactorTypes s).length = s.length :=
  List.length_ofFn

theorem zero_length_iff_trivial {G : Type u} [Group G] [Finite G] (s : ChiefSeries G) :
    s.length = 0 ↔ Subsingleton G := by
  constructor
  · intro h
    have hindex : (0 : Fin (s.length + 1)) = Fin.last s.length :=
      Fin.ext (by simpa using h.symm)
    have hbt : (⊥ : Subgroup G) = ⊤ :=
      s.first_eq_bot.symm.trans ((congrArg s.term hindex).trans s.last_eq_top)
    exact Subgroup.subsingleton_iff.mp (subsingleton_of_bot_eq_top hbt)
  · intro h
    let _ : Subsingleton G := h
    by_contra hne
    have hstep := (s.step ⟨0, Nat.pos_of_ne_zero hne⟩).1
    exact hstep.ne (Subsingleton.elim _ _)

/-- The trivial group has the one-term chief series and no chief factors. -/
theorem trivial_series (G : Type u) [Group G] [Finite G] [Subsingleton G] :
    ∃ s : ChiefSeries G, s.length = 0 ∧ chiefFactorTypes s = [] := by
  let s : ChiefSeries G := {
    length := 0
    term := fun _ => ⊥
    first_eq_bot := rfl
    last_eq_top := Subsingleton.elim _ _
    normal := fun _ => inferInstance
    step := Fin.elim0 }
  exact ⟨s, rfl, List.ofFn_zero⟩

end ALG02GroupTheory.Chief
