import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.PositiveRoots
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.RootVectorReduction
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! The finite real root system determined by the integral quiver reflections. -/

open scoped BigOperators Matrix

universe u v

namespace RepTheorySurvey.Quiver.PositiveRoots

open Forms SimpleReflections

noncomputable abbrev weylGroup := @PositiveRootsSpec.weylGroup
noncomputable abbrev roots := @PositiveRootsSpec.roots
noncomputable abbrev positiveRoots := @PositiveRootsSpec.positiveRoots

variable {Q : Type u} [Quiver.{v} Q] [Fintype Q]

private theorem simpleReflection_mem_weylGroup (i : Q) :
    simpleReflection ℤ i ∈ weylGroup Q :=
  Subgroup.subset_closure (Set.mem_range_self i)

private theorem weyl_preserves_titsForm [Fintype (RM03.Arrow Q)]
    (h : ¬ RM03.HasOrientedCycle Q) (w : weylGroup Q) (d : DimensionVector Q) :
    titsForm (w.val d) = titsForm d := by
  refine Subgroup.closure_induction
    (p := fun g _ => ∀ x : DimensionVector Q, titsForm (g x) = titsForm x)
    ?_ ?_ ?_ ?_ w.property d
  · rintro _ ⟨i, rfl⟩ x
    exact simpleReflection_preservesTitsForm h i x
  · intro x
    rfl
  · intro g k _ _ hg hk x
    exact (hg (k x)).trans (hk x)
  · intro g _ hg x
    simpa using (hg (g.symm x)).symm

private theorem unitVector_mem_roots (i : Q) : unitVector i ∈ roots Q :=
  ⟨i, 1, rfl⟩

private theorem neg_mem_roots {d : DimensionVector Q} (hd : d ∈ roots Q) :
    -d ∈ roots Q := by
  obtain ⟨i, w, rfl⟩ := hd
  have hs : simpleReflection ℤ i (unitVector i) = -unitVector i := by
    change simpleReflection ℤ i (FormsSpec.unitVector i) = -FormsSpec.unitVector i
    rw [← vertexUnit_int i]
    change simpleReflection ℤ i (vertexUnit ℤ i) = -vertexUnit ℤ i
    rw [simpleReflection_apply, vertexUnit_squareLength, two_smul]
    abel
  refine ⟨i, w * ⟨simpleReflection ℤ i, simpleReflection_mem_weylGroup i⟩, ?_⟩
  change w.val (simpleReflection ℤ i (unitVector i)) = -w.val (unitVector i)
  rw [hs, map_neg]

variable [Fintype (RM03.Arrow Q)]

private theorem twice_titsForm_int (h : ¬ RM03.HasOrientedCycle Q) (d : DimensionVector Q) :
    2 * titsForm d = d ⬝ᵥ (polarizationMatrix ℤ *ᵥ d) := by
  rw [← eulerForm_add_swap_eq_pairing h, two_mul]
  rfl

theorem roots_have_titsValueOne : PositiveRootsSpec.RootsHaveTitsValueOne.{u, v} := by
  intro Q _ _ _ h d hd
  obtain ⟨i, w, rfl⟩ := hd
  change titsForm (w.val (unitVector i)) = 1
  rw [weyl_preserves_titsForm h]
  have hlen := (twice_titsForm_int h (unitVector i)).trans
    (show FormsSpec.unitVector i ⬝ᵥ (polarizationMatrix ℤ *ᵥ FormsSpec.unitVector i) = 2 by
      rw [← vertexUnit_int i]
      exact vertexUnit_squareLength ℤ i)
  omega

theorem finite_roots : PositiveRootsSpec.FiniteRoots.{u, v} := by
  intro Q _ _ _ h hpos
  exact (CoxeterDynamics.integralLevel_finite h hpos 1).subset (roots_have_titsValueOne h)

omit [Fintype (RM03.Arrow Q)] in
private theorem vectorAtStep_in_orbit (number : Q ≃ Fin (Fintype.card Q))
    (hcard : 0 < Fintype.card Q) (d : DimensionVector Q) (m : ℕ) :
    ∃ w : weylGroup Q, w.val d = RootVectorReduction.vectorAtStep number m d := by
  induction m with
  | zero => exact ⟨1, (RootVectorReduction.vectorAtStep_zero number d).symm⟩
  | succ m ih =>
    obtain ⟨w, hw⟩ := ih
    let i : Fin (Fintype.card Q) := ⟨m % Fintype.card Q, Nat.mod_lt m hcard⟩
    let s : weylGroup Q :=
      ⟨simpleReflection ℤ (number.symm i), simpleReflection_mem_weylGroup (number.symm i)⟩
    refine ⟨s * w, ?_⟩
    change simpleReflection ℤ (number.symm i) (w.val d) =
      RootVectorReduction.vectorAtStep number (m + 1) d
    rw [hw]
    exact (RootVectorReduction.vectorAtStep_succ number m i rfl d).symm

theorem positiveRoots_characterization : PositiveRootsSpec.PositiveRootsCharacterization.{u, v} := by
  intro Q _ _ _ h hpos
  ext d
  change (d ∈ roots Q ∧ (∀ j, 0 ≤ d j)) ↔ ((∀ j, 0 ≤ d j) ∧ titsForm d = 1)
  constructor
  · rintro ⟨hd, hnonneg⟩
    exact ⟨hnonneg, roots_have_titsValueOne h d hd⟩
  · rintro ⟨hnonneg, hq⟩
    obtain ⟨number, hnumber⟩ := (CoxeterDynamics.fullSinkCycle.{u, v, 0} h).1
    obtain ⟨m, i, _, _, hi, _⟩ :=
      RootVectorReduction.firstNegativeStep h hpos number hnumber d hnonneg hq
    obtain ⟨w, hw⟩ := vectorAtStep_in_orbit number (Nat.zero_lt_of_lt i.isLt) d m
    refine ⟨⟨number.symm i, w⁻¹, ?_⟩, hnonneg⟩
    apply w.val.symm_apply_eq.mpr
    exact (hw.trans hi).symm

private noncomputable def quiverPairing (R : Type*) [CommRing R] :
    (Q → R) →ₗ[R] (Q → R) →ₗ[R] R := by
  classical
  exact (polarizationMatrix R).toBilin'

omit [Fintype (RM03.Arrow Q)] in
private theorem quiverPairing_apply {R : Type*} [CommRing R] (x y : Q → R) :
    quiverPairing R x y = x ⬝ᵥ (polarizationMatrix R *ᵥ y) := by
  classical
  exact Matrix.toBilin'_apply' _ _ _

omit [Fintype (RM03.Arrow Q)] in
private theorem quiverPairing_symm {R : Type*} [CommRing R] (x y : Q → R) :
    quiverPairing R x y = quiverPairing R y x := by
  rw [quiverPairing_apply, quiverPairing_apply]
  simpa only [polarizationMatrix, polarizationMatrix_transpose] using
    Matrix.dotProduct_transpose_mulVec (polarizationMatrix R) x y

omit [Fintype (RM03.Arrow Q)] in
private theorem quiverPairing_flip {R : Type*} [CommRing R] :
    (quiverPairing (Q := Q) R).flip = quiverPairing R := by
  ext x y
  exact quiverPairing_symm _ _

private abbrev realVector (d : DimensionVector Q) : Q → ℝ := fun i => (d i : ℝ)

omit [Quiver.{v} Q] [Fintype Q] [Fintype (RM03.Arrow Q)] in
private theorem realVector_injective : Function.Injective (realVector (Q := Q)) := by
  intro d e h
  funext i
  exact Int.cast_inj.mp (congrFun h i)

private theorem integral_titsForm_pos (hp : PositiveDefinite Q) {d : DimensionVector Q}
    (hd : d ≠ 0) : 0 < titsForm d := by
  have hc : realVector d ≠ 0 := by
    intro hz
    exact hd (realVector_injective (hz.trans (by ext; simp [realVector])))
  have h := hp (realVector d) hc
  rw [real_titsForm_intCast] at h
  exact_mod_cast h

/-- The two sign parts have disjoint supports, so the arrow contribution
makes their cross term nonpositive. -/
private theorem nonneg_or_nonpos (h : ¬ RM03.HasOrientedCycle Q) (hp : PositiveDefinite Q)
    {d : DimensionVector Q} (hd : titsForm d = 1) :
    (∀ i, 0 ≤ d i) ∨ (∀ i, d i ≤ 0) := by
  classical
  by_contra! hsign
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hsign
  let p : DimensionVector Q := fun k => max (d k) 0
  let n : DimensionVector Q := fun k => max (-d k) 0
  have hp0 (k : Q) : 0 ≤ p k := le_max_right _ _
  have hn0 (k : Q) : 0 ≤ n k := le_max_right _ _
  have hparts : d = p - n := by
    funext k
    change d k = max (d k) 0 - max (-d k) 0
    omega
  have hdisj (k : Q) : p k * n k = 0 := by
    by_cases hk : 0 ≤ d k
    · simp [n, max_eq_right (neg_nonpos.mpr hk)]
    · simp [p, max_eq_right (le_of_not_ge hk)]
  have hqpos : 0 < titsForm p := integral_titsForm_pos hp (by
    intro he
    have he' : max (d j) 0 = 0 := congrFun he j
    omega)
  have hqneg : 0 < titsForm n := integral_titsForm_pos hp (by
    intro he
    have he' : max (-d i) 0 = 0 := congrFun he i
    omega)
  have heuler {a b : DimensionVector Q} (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
      (hab : ∀ k, a k * b k = 0) : eulerForm a b ≤ 0 := by
    change (∑ k, a k * b k) - ∑ e : RM03.Arrow Q, a e.1 * b e.2.1 ≤ 0
    simp_rw [hab, Finset.sum_const_zero, zero_sub, neg_nonpos]
    exact Finset.sum_nonneg (fun e _ => mul_nonneg (ha e.1) (hb e.2.1))
  have hcross : quiverPairing ℤ p n ≤ 0 := by
    rw [quiverPairing_apply, ← eulerForm_add_swap_eq_pairing h]
    exact add_nonpos (heuler hp0 hn0 hdisj)
      (heuler hn0 hp0 (fun k => by rw [mul_comm, hdisj]))
  have hdiag (x : DimensionVector Q) :
      quiverPairing ℤ x x = 2 * titsForm x := by
    rw [quiverPairing_apply, twice_titsForm_int h]
  have hx : quiverPairing ℤ d d =
      quiverPairing ℤ p p + quiverPairing ℤ n n - 2 * quiverPairing ℤ p n := by
    rw [hparts]
    simp only [map_sub, LinearMap.sub_apply, quiverPairing_symm n p]
    ring
  rw [hdiag, hdiag, hdiag, hd] at hx
  omega

private theorem mem_roots_of_titsValueOne (h : ¬ RM03.HasOrientedCycle Q)
    (hp : PositiveDefinite Q) {d : DimensionVector Q} (hd : titsForm d = 1) :
    d ∈ roots Q := by
  have from_pos {x : DimensionVector Q} (hx : ∀ k, 0 ≤ x k) (hq : titsForm x = 1) :
      x ∈ roots Q := by
    have hmem : x ∈ positiveRoots Q := by
      change x ∈ PositiveRootsSpec.positiveRoots Q
      rw [positiveRoots_characterization h hp]
      exact ⟨hx, hq⟩
    exact hmem.1
  rcases nonneg_or_nonpos h hp hd with hpos | hneg
  · exact from_pos hpos hd
  · have hnq : titsForm (-d) = 1 := by
      simpa only [FormsSpec.titsForm, FormsSpec.eulerForm, Pi.neg_apply, neg_mul_neg] using hd
    have hnn (i : Q) : 0 ≤ (-d) i := neg_nonneg.mpr (hneg i)
    simpa only [neg_neg] using neg_mem_roots (from_pos hnn hnq)

private theorem real_pairing_intCast (h : ¬ RM03.HasOrientedCycle Q) (x y : DimensionVector Q) :
    quiverPairing ℝ (realVector x) (realVector y) = (quiverPairing ℤ x y : ℝ) := by
  rw [quiverPairing_apply, quiverPairing_apply, ← eulerForm_add_swap_eq_pairing h,
    ← eulerForm_add_swap_eq_pairing h]
  simp [FormsSpec.eulerForm, Int.cast_add, Int.cast_sub, Int.cast_sum, Int.cast_mul]

private theorem real_pairing_self (h : ¬ RM03.HasOrientedCycle Q) (d : DimensionVector Q) :
    quiverPairing ℝ (realVector d) (realVector d) = 2 * ((titsForm (R := ℤ) d : ℤ) : ℝ) := by
  rw [quiverPairing_apply, ← real_quadratic_matrix h, real_titsForm_intCast]

private theorem quiverPairing_isPerfPair (h : ¬ RM03.HasOrientedCycle Q)
    (hp : PositiveDefinite Q) : (quiverPairing (Q := Q) ℝ).IsPerfPair := by
  have hinj : Function.Injective (quiverPairing (Q := Q) ℝ) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro x hx
    rw [LinearMap.mem_ker] at hx
    change x = 0
    by_contra hne
    have hz : quiverPairing ℝ x x = 0 := by rw [hx]; rfl
    rw [quiverPairing_apply, ← real_quadratic_matrix h] at hz
    linarith [hp x hne]
  have hflip := quiverPairing_flip (Q := Q) (R := ℝ)
  exact LinearMap.IsPerfPair.of_injective hinj (hflip.symm ▸ hinj)

private def rootEmbedding (Q : Type u) [Quiver.{v} Q] [Fintype Q] :
    ↥(roots Q) ↪ (Q → ℝ) where
  toFun a := realVector a.val
  inj' := fun _ _ h => Subtype.ext (realVector_injective h)

private theorem root_pairing_self (h : ¬ RM03.HasOrientedCycle Q) (a : ↥(roots Q)) :
    quiverPairing ℝ (rootEmbedding Q a) (rootEmbedding Q a) = 2 := by
  change quiverPairing ℝ (realVector a.val) (realVector a.val) = 2
  have hq : titsForm a.val = 1 := roots_have_titsValueOne h a.val a.property
  rw [real_pairing_self h, hq]
  norm_num

/-- Reflection in a length-two lattice vector stays on the integral Tits level one. -/
private theorem reflection_mapsTo_roots (h : ¬ RM03.HasOrientedCycle Q) (hp : PositiveDefinite Q)
    (a : ↥(roots Q)) :
    Set.MapsTo (Module.preReflection (rootEmbedding Q a)
      ((quiverPairing ℝ).flip (rootEmbedding Q a)))
      (Set.range (rootEmbedding Q)) (Set.range (rootEmbedding Q)) := by
  rintro _ ⟨b, rfl⟩
  let c : ℤ := quiverPairing ℤ b.val a.val
  let z : DimensionVector Q := b.val - c • a.val
  have hc : quiverPairing ℝ (rootEmbedding Q b) (rootEmbedding Q a) = (c : ℝ) :=
    real_pairing_intCast h b.val a.val
  have hz : realVector z = rootEmbedding Q b - (c : ℝ) • rootEmbedding Q a := by
    funext i
    change ((b.val i - c * a.val i : ℤ) : ℝ) = (b.val i : ℝ) - (c : ℝ) * (a.val i : ℝ)
    push_cast
    rfl
  have hlen : quiverPairing ℝ (realVector z) (realVector z) = 2 := by
    rw [hz]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      quiverPairing_symm (rootEmbedding Q a) (rootEmbedding Q b),
      hc, root_pairing_self h]
    ring
  rw [real_pairing_self h] at hlen
  have hqreal : ((titsForm (R := ℤ) z : ℤ) : ℝ) = 1 := by linarith
  have hq : titsForm z = 1 := by exact_mod_cast hqreal
  refine ⟨⟨z, mem_roots_of_titsValueOne h hp hq⟩, ?_⟩
  rw [Module.preReflection_apply, LinearMap.flip_apply, hc]
  exact hz

private theorem rootEmbedding_reduced (h : ¬ RM03.HasOrientedCycle Q)
    (a b : ↥(roots Q)) (hdep : ¬ LinearIndependent ℝ ![rootEmbedding Q a, rootEmbedding Q b]) :
    rootEmbedding Q a = rootEmbedding Q b ∨ rootEmbedding Q a = -rootEmbedding Q b := by
  have ha : rootEmbedding Q a ≠ 0 := by
    intro hz
    have hlen := root_pairing_self h a
    simp [hz] at hlen
  obtain ⟨c, hc⟩ := not_forall.mp (fun hh => hdep ((LinearIndependent.pair_iff' ha).mpr hh))
  have hc' : c • rootEmbedding Q a = rootEmbedding Q b := not_not.mp hc
  have hlen := root_pairing_self h b
  simp only [← hc', map_smul, LinearMap.smul_apply, smul_eq_mul, root_pairing_self h a] at hlen
  have hcprod : (c - 1) * (c + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hcprod with hc₁ | hc₂
  · have : c = 1 := by linarith
    exact Or.inl (by simpa [this] using hc')
  · have : c = -1 := by linarith
    exact Or.inr (by simpa [this, neg_eq_iff_eq_neg] using hc')

private noncomputable def simpleIndex (i : Q) : ↥(roots Q) :=
  ⟨unitVector i, unitVector_mem_roots i⟩

omit [Fintype (RM03.Arrow Q)] in
private theorem rootEmbedding_simpleIndex (i : Q) :
    rootEmbedding Q (simpleIndex i) = vertexUnit ℝ i := by
  classical
  funext j
  change (FormsSpec.unitVector i j : ℝ) = SimpleReflectionsSpec.vertexUnit ℝ i j
  by_cases hij : j = i <;> simp [FormsSpec.unitVector, SimpleReflectionsSpec.vertexUnit, hij]

omit [Quiver.{v} Q] [Fintype (RM03.Arrow Q)] in
private theorem vertexUnit_eq_basisFun :
    (vertexUnit ℝ : Q → Q → ℝ) = Pi.basisFun ℝ Q := by
  classical
  funext i
  rw [Pi.basisFun_apply]
  rfl

omit [Quiver.{v} Q] [Fintype (RM03.Arrow Q)] in
private theorem realVector_mem_closure (d : DimensionVector Q) (hd : ∀ i, 0 ≤ d i) :
    realVector d ∈ AddSubmonoid.closure (Set.range (vertexUnit ℝ : Q → Q → ℝ)) := by
  classical
  have hsum : (∑ i : Q, (d i).toNat • vertexUnit ℝ i) = realVector d := by
    funext j
    simp only [Finset.sum_apply]
    rw [Fintype.sum_eq_single j]
    · simp [vertexUnit, SimpleReflectionsSpec.vertexUnit, realVector, nsmul_eq_mul]
      exact_mod_cast Int.toNat_of_nonneg (hd j)
    · intro i hi
      simp [vertexUnit, SimpleReflectionsSpec.vertexUnit, Ne.symm hi]
  rw [← hsum]
  exact sum_mem (fun i _ => nsmul_mem (AddSubmonoid.subset_closure (Set.mem_range_self i)) _)

theorem rootSystemRealisation : PositiveRootsSpec.RootSystemRealisation.{u, v} := by
  classical
  intro Q _ _ _ h hp
  have : Finite ↥(roots Q) := (finite_roots h hp).to_subtype
  have : (quiverPairing (Q := Q) ℝ).IsPerfPair := quiverPairing_isPerfPair h hp
  let e := rootEmbedding Q
  let P := RootPairing.mk' (quiverPairing ℝ) e e (root_pairing_self h)
    (reflection_mapsTo_roots h hp)
    (by simpa only [quiverPairing_flip] using reflection_mapsTo_roots h hp)
  have hspan : Submodule.span ℝ (Set.range e) = ⊤ := by
    apply top_unique
    have hle : Set.range (vertexUnit ℝ : Q → Q → ℝ) ⊆ Set.range e := by
      rintro _ ⟨i, rfl⟩
      exact ⟨simpleIndex i, rootEmbedding_simpleIndex i⟩
    simpa only [vertexUnit_eq_basisFun, Module.Basis.span_eq] using Submodule.span_mono (R := ℝ) hle
  refine ⟨P, ⟨hspan, hspan⟩, ⟨rootEmbedding_reduced h⟩, ⟨?_⟩,
    quiverPairing_apply, fun _ => ⟨rfl, rfl⟩, ?_⟩
  · intro a b
    exact ⟨quiverPairing ℤ a.val b.val, (real_pairing_intCast h a.val b.val).symm⟩
  let support : Finset ↥(roots Q) := Finset.univ.image simpleIndex
  have hsimple : e '' (support : Set ↥(roots Q)) = Set.range (vertexUnit ℝ : Q → Q → ℝ) := by
    have he : (e ∘ simpleIndex) = (vertexUnit ℝ : Q → Q → ℝ) :=
      funext rootEmbedding_simpleIndex
    rw [show (support : Set ↥(roots Q)) = Set.range simpleIndex by simp [support],
      ← Set.range_comp, he]
  have hindep : LinearIndepOn ℝ e (support : Set ↥(roots Q)) := by
    apply (linearIndepOn_iff_image e.injective.injOn).mpr
    rw [hsimple, vertexUnit_eq_basisFun]
    exact (Pi.basisFun ℝ Q).linearIndependent.linearIndepOn_id
  have hclosure (a : ↥(roots Q)) :
      e a ∈ AddSubmonoid.closure (e '' (support : Set ↥(roots Q))) ∨
      -e a ∈ AddSubmonoid.closure (e '' (support : Set ↥(roots Q))) := by
    rw [hsimple]
    rcases nonneg_or_nonpos h hp (roots_have_titsValueOne h a.val a.property) with hpos | hneg
    · exact Or.inl (realVector_mem_closure a.val hpos)
    · exact Or.inr (by
        have hmem := realVector_mem_closure (-a.val) (fun i => neg_nonneg.mpr (hneg i))
        convert hmem using 1
        funext i
        exact (Int.cast_neg (a.val i)).symm)
  exact ⟨⟨support, hindep, hindep, hclosure, hclosure⟩, hsimple⟩

end RepTheorySurvey.Quiver.PositiveRoots
