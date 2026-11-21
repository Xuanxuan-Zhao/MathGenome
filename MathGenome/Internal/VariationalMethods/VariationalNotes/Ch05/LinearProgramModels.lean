import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramModels

noncomputable section
open Matrix Set
universe u v
namespace VariationalNotes.Ch05.LinearProgramModels

def primalFeasible {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (x : n → ℝ) : Prop := Specs.primalFeasible A b x

def dualFeasible {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (c : n → ℝ) (y : m → ℝ) : Prop := Specs.dualFeasible A c y

def primalObjective {n : Type u} [Fintype n] (c x : n → ℝ) : ℝ := Specs.primalObjective c x

def dualObjective {m : Type u} [Fintype m] (b y : m → ℝ) : ℝ := Specs.dualObjective b y

def primalValue {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : EReal := Specs.primalValue A b c

def dualValue {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : EReal := Specs.dualValue A b c

def PrimalUnbounded {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop := Specs.PrimalUnbounded A b c

def DualUnbounded {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) : Prop := Specs.DualUnbounded A b c

def PrimalOptimal {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (x : n → ℝ) : Prop := Specs.PrimalOptimal A b c x

def DualOptimal {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (y : m → ℝ) : Prop := Specs.DualOptimal A b c y

def PrimalAttains {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ) : Prop := Specs.PrimalAttains A b c p

def DualAttains {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (p : ℝ) : Prop := Specs.DualAttains A b c p

theorem gap_identity : Specs.gap_identity.{u,v} := by
  intro m n _ _ A b c x y hx
  have hpair : x ⬝ᵥ (Aᵀ *ᵥ y) = b ⬝ᵥ y := by
    rw [Matrix.dotProduct_transpose_mulVec, hx.1, dotProduct_comm]
  change c ⬝ᵥ x - b ⬝ᵥ y = _
  rw [← hpair, dotProduct_comm c x, ← dotProduct_sub]
  rfl

theorem gap_nonnegative : Specs.gap_nonnegative.{u,v} := by
  intro m n _ _ A b c x y hx hy
  rw [gap_identity A b c x y hx]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx.2 i) (sub_nonneg.mpr (hy i)))

theorem weakDuality : Specs.weakDuality.{u,v} := by
  intro m n _ _ A b c x y hx hy
  exact sub_nonneg.mp (gap_nonnegative A b c x y hx hy)

theorem gap_eq_zero_iff : Specs.gap_eq_zero_iff.{u,v} := by
  intro m n _ _ A b c x y hx hy
  rw [gap_identity A b c x y hx]
  simpa only [Finset.mem_univ, forall_const] using
    (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (fun i _ => mul_nonneg (hx.2 i) (sub_nonneg.mpr (hy i))))

theorem primalValue_le : Specs.primalValue_le.{u,v} := by
  intro m n _ _ A b c x hx
  exact sInf_le ⟨x, hx, rfl⟩

theorem le_dualValue : Specs.le_dualValue.{u,v} := by
  intro m n _ _ A b c y hy
  exact le_sSup ⟨y, hy, rfl⟩

theorem weakDuality_values : Specs.weakDuality_values.{u,v} := by
  intro m n _ _ A b c
  apply sSup_le
  rintro _ ⟨y, hy, rfl⟩
  apply le_sInf
  rintro _ ⟨x, hx, rfl⟩
  exact EReal.coe_le_coe (weakDuality A b c x y hx hy)

theorem primalValue_eq_top_iff : Specs.primalValue_eq_top_iff.{u,v} := by
  intro m n _ _ A b c
  constructor
  · intro h ⟨x, hx⟩
    have hle := primalValue_le A b c x hx
    rw [h] at hle
    exact (EReal.coe_lt_top _).not_ge hle
  · intro h
    change sInf _ = ⊤
    apply top_unique
    apply le_sInf
    rintro _ ⟨x, hx, rfl⟩
    exact (h ⟨x, hx⟩).elim

theorem dualValue_eq_bot_iff : Specs.dualValue_eq_bot_iff.{u,v} := by
  intro m n _ _ A b c
  constructor
  · intro h ⟨y, hy⟩
    have hle := le_dualValue A b c y hy
    rw [h] at hle
    exact (EReal.bot_lt_coe _).not_ge hle
  · intro h
    change sSup _ = ⊥
    apply bot_unique
    apply sSup_le
    rintro _ ⟨y, hy, rfl⟩
    exact (h ⟨y, hy⟩).elim

theorem primalUnbounded_iff_value_eq_bot : Specs.primalUnbounded_iff_value_eq_bot.{u,v} := by
  intro m n _ _ A b c
  constructor
  · intro h
    apply bot_unique
    by_contra hnot
    have hpos : (⊥ : EReal) < Specs.primalValue A b c := lt_of_not_ge hnot
    obtain ⟨r, _, hr⟩ := EReal.lt_iff_exists_real_btwn.mp hpos
    obtain ⟨x, hx, hxr⟩ := h r
    exact (hr.trans_le (primalValue_le A b c x hx)).not_ge (EReal.coe_le_coe hxr.le)
  · intro h r
    have hlt : Specs.primalValue A b c < (r : EReal) := by
      rw [h]
      exact EReal.bot_lt_coe r
    obtain ⟨_, ⟨x, hx, rfl⟩, hxr⟩ := sInf_lt_iff.mp hlt
    exact ⟨x, hx, EReal.coe_lt_coe_iff.mp hxr⟩

theorem dualUnbounded_iff_value_eq_top : Specs.dualUnbounded_iff_value_eq_top.{u,v} := by
  intro m n _ _ A b c
  constructor
  · intro h
    apply top_unique
    by_contra hnot
    have hlt : Specs.dualValue A b c < (⊤ : EReal) := lt_of_not_ge hnot
    obtain ⟨r, hr, _⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    obtain ⟨y, hy, hry⟩ := h r
    exact (hr.trans_le (EReal.coe_le_coe hry.le)).not_ge (le_dualValue A b c y hy)
  · intro h r
    have hlt : (r : EReal) < Specs.dualValue A b c := by
      rw [h]
      exact EReal.coe_lt_top r
    obtain ⟨_, ⟨y, hy, rfl⟩, hry⟩ := lt_sSup_iff.mp hlt
    exact ⟨y, hy, EReal.coe_lt_coe_iff.mp hry⟩

theorem primalOptimal_iff : Specs.primalOptimal_iff.{u,v} := by
  intro m n _ _ A b c x
  constructor
  · rintro ⟨hx, heq⟩
    refine ⟨hx, fun z hz => ?_⟩
    have hle := primalValue_le A b c z hz
    rw [heq] at hle
    exact EReal.coe_le_coe_iff.mp hle
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, le_antisymm (primalValue_le A b c x hx) ?_⟩
    apply le_sInf
    rintro _ ⟨z, hz, rfl⟩
    exact EReal.coe_le_coe (hmin z hz)

theorem dualOptimal_iff : Specs.dualOptimal_iff.{u,v} := by
  intro m n _ _ A b c y
  constructor
  · rintro ⟨hy, heq⟩
    refine ⟨hy, fun z hz => ?_⟩
    have hle := le_dualValue A b c z hz
    rw [heq] at hle
    exact EReal.coe_le_coe_iff.mp hle
  · rintro ⟨hy, hmax⟩
    refine ⟨hy, le_antisymm ?_ (le_dualValue A b c y hy)⟩
    apply sSup_le
    rintro _ ⟨z, hz, rfl⟩
    exact EReal.coe_le_coe (hmax z hz)

theorem primalAttains_value : Specs.primalAttains_value.{u,v} := by
  intro m n _ _ A b c p h
  obtain ⟨x, ⟨_, hx⟩, hp⟩ := h
  rw [hx, hp]

theorem dualAttains_value : Specs.dualAttains_value.{u,v} := by
  intro m n _ _ A b c p h
  obtain ⟨y, ⟨_, hy⟩, hp⟩ := h
  rw [hy, hp]

end VariationalNotes.Ch05.LinearProgramModels
