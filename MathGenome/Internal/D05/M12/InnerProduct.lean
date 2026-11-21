import MathGenome.Internal.Specs.D05.M12.InnerProduct

/-! K05.12.inner_product: axioms, their algebraic bridge, and coordinate examples. -/

noncomputable section

namespace D05.M12.InnerProduct

open D05

theorem firstInner_linear : Specs.D05.M12.InnerProduct.firstInner_linear := by
  intro F V _ _ _ a b u v w
  simp only [firstInner, inner_add_right, inner_smul_right]

theorem firstInner_conjugate : Specs.D05.M12.InnerProduct.firstInner_conjugate := by
  intro F V _ _ _ u v
  exact (inner_conj_symm u v).symm

theorem firstInner_diagonal : Specs.D05.M12.InnerProduct.firstInner_diagonal := by
  intro F V _ _ _ v
  exact ⟨inner_self_im v, re_inner_self_pos⟩

theorem firstInner_axioms : Specs.D05.M12.InnerProduct.firstInner_axioms := by
  intro F V _ _ _
  exact ⟨firstInner_linear, firstInner_conjugate, fun v => (firstInner_diagonal v).1,
    fun v hv => (firstInner_diagonal v).2.mpr hv⟩

theorem second_slot_of_axioms : Specs.D05.M12.InnerProduct.second_slot_of_axioms := by
  intro F V _ _ _ h hh a b u v w
  rcases hh with ⟨hl, hs, _, _⟩
  rw [hs (a • v + b • w) u, hl, map_add, map_mul, map_mul,
    ← hs v u, ← hs w u]

theorem zero_of_axioms : Specs.D05.M12.InnerProduct.zero_of_axioms := by
  intro F V _ _ _ h hh v
  have hz : h 0 v = 0 := by
    simpa using hh.1 0 0 0 0 v
  exact ⟨hz, by rw [hh.2.1 0 v, hz, map_zero]⟩

theorem firstInner_second_slot : Specs.D05.M12.InnerProduct.firstInner_second_slot := by
  intro F V _ _ _
  exact second_slot_of_axioms _ firstInner_axioms

theorem firstInner_zero : Specs.D05.M12.InnerProduct.firstInner_zero := by
  intro F V _ _ _
  exact zero_of_axioms _ firstInner_axioms

theorem axioms_iff_core : Specs.D05.M12.InnerProduct.axioms_iff_core := by
  intro F V _ _ _ h
  constructor
  · intro hh
    have hsecond := second_slot_of_axioms h hh
    have hzero := zero_of_axioms h hh
    refine ⟨{
      inner := fun u v => h v u
      conj_inner_symm := fun x y => (hh.2.1 x y).symm
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_
      definite := ?_ }, fun _ _ => rfl⟩
    · intro x
      by_cases hx : x = 0
      · subst x
        simp only [(hzero 0).1, map_zero, le_refl]
      · exact (hh.2.2.2 x hx).le
    · intro x y z
      simpa using hsecond 1 1 z x y
    · intro x y r
      simpa using hsecond r 0 y x 0
    · intro x hx
      by_contra hne
      have hpos := hh.2.2.2 x hne
      rw [hx, map_zero] at hpos
      exact (lt_irrefl 0) hpos
  · rintro ⟨c, hc⟩
    let : InnerProductSpace.Core F V := c
    let : Inner F V := c.toInner
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b u v w
      simp only [← hc]
      exact (InnerProductSpace.Core.inner_add_right w (a • u) (b • v)).trans
        (congrArg₂ (· + ·) (InnerProductSpace.Core.inner_smul_right w u)
          (InnerProductSpace.Core.inner_smul_right w v))
    · intro u v
      rw [← hc, ← hc]
      exact (c.conj_inner_symm u v).symm
    · intro v
      rw [← hc]
      exact InnerProductSpace.Core.inner_self_im v
    · intro v hv
      rw [← hc]
      have hre : RCLike.re (c.inner v v) ≠ 0 := by
        intro hz
        apply hv
        apply c.definite v
        rw [← InnerProductSpace.Core.inner_self_ofReal_re v, hz]
        exact map_zero _
      exact lt_of_le_of_ne (c.re_inner_nonneg v) hre.symm

theorem real_symmetric_bilinear : Specs.D05.M12.InnerProduct.real_symmetric_bilinear := by
  intro V _ _ h hh
  refine ⟨?_, hh.1, ?_, hh.2.2.2⟩
  · intro u v
    simpa using hh.2.1 v u
  · simpa using second_slot_of_axioms h hh

theorem coordinateInner_eq_firstInner :
    Specs.D05.M12.InnerProduct.coordinateInner_eq_firstInner := by
  intro F ι _ _ x y
  rfl

theorem coordinateInner_axioms : Specs.D05.M12.InnerProduct.coordinateInner_axioms := by
  intro F ι _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b u v w
    change firstInner (F := F) (WithLp.toLp 2 (a • u + b • v)) (WithLp.toLp 2 w) = _
    exact firstInner_linear a b (WithLp.toLp 2 u) (WithLp.toLp 2 v) (WithLp.toLp 2 w)
  · intro u v
    exact firstInner_conjugate (F := F) (WithLp.toLp 2 u) (WithLp.toLp 2 v)
  · intro v
    rw [coordinateInner_eq_firstInner]
    exact (firstInner_diagonal (WithLp.toLp 2 v)).1
  · intro v hv
    rw [coordinateInner_eq_firstInner]
    apply (firstInner_diagonal (WithLp.toLp 2 v)).2.mpr
    intro hz
    apply hv
    exact congrArg (WithLp.ofLp) hz

theorem coordinateInner_diagonal : Specs.D05.M12.InnerProduct.coordinateInner_diagonal := by
  intro F ι _ _ x
  have heq : coordinateInner x x = ((∑ j, ‖x j‖ ^ 2 : ℝ) : F) := by
    simp only [coordinateInner, RCLike.mul_conj, ← RCLike.ofReal_pow, map_sum]
  have hpos : 0 < (∑ j, ‖x j‖ ^ 2 : ℝ) ↔ x ≠ 0 := by
    have h := (firstInner_diagonal (F := F) (WithLp.toLp 2 x)).2
    rw [← coordinateInner_eq_firstInner, heq, RCLike.ofReal_re] at h
    simpa only [ne_eq, WithLp.toLp_eq_zero] using h
  refine ⟨heq, hpos, ?_⟩
  rw [coordinateInner_eq_firstInner]
  change inner F (WithLp.toLp 2 x) (WithLp.toLp 2 x) = 0 ↔ ∀ j, x j = 0
  rw [inner_self_eq_zero, WithLp.toLp_eq_zero]
  exact ⟨fun hx j => congrFun hx j, fun hx => funext hx⟩

theorem zero_space : Specs.D05.M12.InnerProduct.zero_space := by
  intro F V _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    simp
  · intros
    simp
  · intro v
    exact map_zero _
  · intro v hv
    exact (hv (Subsingleton.elim v 0)).elim

/-- Candidate-owned witness for the shared first-slot convention.
The canonical operation remains `D05.firstInner` in the independent Spec. -/
abbrev firstInnerConvention : Specs.D05.M12.InnerProduct.firstInner_type :=
  @_root_.D05.firstInner

/-- Candidate-owned witness for the paper's algebraic definition. -/
abbrev innerProductAxioms : Specs.D05.M12.InnerProduct.IsFirstInnerProduct_type :=
  @_root_.D05.IsFirstInnerProduct

/-- Candidate-owned witness for the raw finite-coordinate formula. -/
abbrev coordinateInnerFormula : Specs.D05.M12.InnerProduct.coordinateInner_type :=
  @_root_.D05.coordinateInner

end D05.M12.InnerProduct
