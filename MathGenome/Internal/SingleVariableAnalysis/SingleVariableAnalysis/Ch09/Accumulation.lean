import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Accumulation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Oriented

/-! Lipschitz continuity of the proper Darboux accumulation integral.
Restrictions and splitting use chapter 08. The integral over the interval
between x and y is bounded using the global supremum of the norm, so no
attainment of that supremum or continuity of the integrand is required.
-/
namespace SingleVariableAnalysis.Riemann

theorem real_accumulation_restrictions :
    Specs.SingleVariableAnalysis.Ch09.Accumulation.realRestrictions := by
  intro f a b hf x y hx hy
  exact oriented_real_integrable_of_mem hf hx hy

theorem complex_accumulation_restrictions :
    Specs.SingleVariableAnalysis.Ch09.Accumulation.complexRestrictions := by
  intro f a b hf x y hx hy
  exact oriented_complex_integrable_of_mem hf hx hy

/-- A bounded norm image on a nonempty interval has a nonnegative real
supremum, bounding every point of the interval. -/
theorem norm_supremum_bounds {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hb : BddAbove ((fun t => ‖f t‖) '' Set.Icc a b)) :
    0 ≤ sSup ((fun t => ‖f t‖) '' Set.Icc a b) ∧
      ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ sSup ((fun t => ‖f t‖) '' Set.Icc a b) := by
  have hbound : ∀ t ∈ Set.Icc a b,
      ‖f t‖ ≤ sSup ((fun t => ‖f t‖) '' Set.Icc a b) :=
    fun t ht => le_csSup hb (Set.mem_image_of_mem _ ht)
  exact ⟨(norm_nonneg (f a)).trans (hbound a ⟨le_rfl, hab⟩), hbound⟩

/-- The ordered form of the real accumulation estimate, for arbitrary
integrability witnesses on the initial segments. -/
theorem real_accumulation_bound_of_le {f : ℝ → ℝ} {a b x y : ℝ}
    (hf : RealIntegrable f a b) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hxy : x ≤ y) (hax : RealIntegrable f a x) (hay : RealIntegrable f a y) :
    ‖realIntegral f hay - realIntegral f hax‖ ≤
      sSup ((fun t => ‖f t‖) '' Set.Icc a b) * (y - x) := by
  have h := hf.subinterval hx.1 hxy hy.2
  have he := ((real_split f hx.1 hxy (RealIntegrable.bounded hay)).2 hay hax h).symm
  have hd : realIntegral f hay - realIntegral f hax = realIntegral f h := by
    linarith [he]
  rw [hd]
  obtain ⟨hn, hnorm, _⟩ := real_norm_estimate f h
  apply hnorm.trans
  rw [mul_comm]
  apply realIntegral_le_mul_bound hn
  intro t ht
  exact le_csSup (RealIntegrable.bounded hf.norm).2
    (Set.mem_image_of_mem _ ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩)

/-- The complex estimate uses the complex norm inequality directly, avoiding
any extra constant from separate component bounds. -/
theorem complex_accumulation_bound_of_le {f : ℝ → ℂ} {a b x y : ℝ}
    (hf : ComplexIntegrable f a b) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hxy : x ≤ y) (hax : ComplexIntegrable f a x) (hay : ComplexIntegrable f a y) :
    ‖complexIntegral f hay - complexIntegral f hax‖ ≤
      sSup ((fun t => ‖f t‖) '' Set.Icc a b) * (y - x) := by
  have h := hf.subinterval hx.1 hxy hy.2
  have he := ((complex_split f hx.1 hxy (ComplexIntegrable.norm_bound hay)).2 hay hax h).symm
  have hd : complexIntegral f hay - complexIntegral f hax = complexIntegral f h := by
    exact sub_eq_of_eq_add (he.symm.trans (add_comm _ _))
  rw [hd]
  obtain ⟨hn, hnorm, _⟩ := complex_norm_estimate f h
  apply hnorm.trans
  rw [mul_comm]
  apply realIntegral_le_mul_bound hn
  intro t ht
  exact le_csSup (RealIntegrable.bounded hf.norm).2
    (Set.mem_image_of_mem _ ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩)

theorem real_accumulation : Specs.SingleVariableAnalysis.Ch09.Accumulation.realAccumulation := by
  intro f a b hf
  let M := sSup ((fun t => ‖f t‖) '' Set.Icc a b)
  let H (x : Set.Icc a b) : RealIntegrable f a x :=
    RealIntegrable.subinterval hf le_rfl x.property.1 x.property.2
  have hM : 0 ≤ M :=
    (norm_supremum_bounds f (RealIntegrable.ordered hf) (RealIntegrable.bounded (RealIntegrable.norm hf)).2).1
  have hb (x y : Set.Icc a b) :
      ‖realIntegral f (H y) - realIntegral f (H x)‖ ≤ M * |(y : ℝ) - (x : ℝ)| := by
    rcases le_total (x : ℝ) (y : ℝ) with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact real_accumulation_bound_of_le hf x.property y.property hxy (H x) (H y)
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact real_accumulation_bound_of_le hf y.property x.property hyx (H y) (H x)
  have hLip : LipschitzWith ⟨M, hM⟩ (fun x : Set.Icc a b => realIntegral f (H x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist _ _ ≤ M * dist x y
    simpa only [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hb y x
  exact ⟨H, hb, hM, hLip, hLip.continuous⟩

theorem complex_accumulation : Specs.SingleVariableAnalysis.Ch09.Accumulation.complexAccumulation := by
  intro f a b hf
  let M := sSup ((fun t => ‖f t‖) '' Set.Icc a b)
  let H (x : Set.Icc a b) : ComplexIntegrable f a x :=
    ComplexIntegrable.subinterval hf le_rfl x.property.1 x.property.2
  have hM : 0 ≤ M :=
    (norm_supremum_bounds f (RealIntegrable.ordered hf.1) (RealIntegrable.bounded (ComplexIntegrable.norm hf)).2).1
  have hb (x y : Set.Icc a b) :
      ‖complexIntegral f (H y) - complexIntegral f (H x)‖ ≤ M * |(y : ℝ) - (x : ℝ)| := by
    rcases le_total (x : ℝ) (y : ℝ) with hxy | hyx
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact complex_accumulation_bound_of_le hf x.property y.property hxy (H x) (H y)
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact complex_accumulation_bound_of_le hf y.property x.property hyx (H y) (H x)
  have hLip : LipschitzWith ⟨M, hM⟩ (fun x : Set.Icc a b => complexIntegral f (H x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist _ _ ≤ M * dist x y
    simpa only [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hb y x
  exact ⟨H, hb, hM, hLip, hLip.continuous⟩

end SingleVariableAnalysis.Riemann
