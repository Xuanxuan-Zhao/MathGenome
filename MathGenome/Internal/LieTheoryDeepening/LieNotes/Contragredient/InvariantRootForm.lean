import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.ReflectionAutomorphisms
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.InvariantRootForm
import Mathlib.Tactic.Ring

namespace LieNotes.Contragredient.InvariantRootForm

noncomputable section

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {d : I → ℝ}
variable {H : Type v} [AddCommGroup H] [Module ℂ H]

abbrev RealRootSpan (I : Type u) := Specs.LieNotes.Contragredient.InvariantRootForm.RealRootSpan I

abbrev SymmetrizingFamily (A : Matrix I I ℤ) (d : I → ℝ) :=
  Specs.LieNotes.Contragredient.InvariantRootForm.SymmetrizingFamily A d

abbrev simpleRoot (i : I) : RealRootSpan I :=
  Specs.LieNotes.Contragredient.InvariantRootForm.simpleRoot i

abbrev latticeToReal : Q I →+ RealRootSpan I :=
  Specs.LieNotes.Contragredient.InvariantRootForm.latticeToReal

abbrev realRootWeight [Finite I] (R : Realization A H) :
    RealRootSpan I →ₗ[ℝ] Module.Dual ℂ H :=
  Specs.LieNotes.Contragredient.InvariantRootForm.realRootWeight R

abbrev realCorootPairing (A : Matrix I I ℤ) (i : I) : RealRootSpan I →ₗ[ℝ] ℝ :=
  Specs.LieNotes.Contragredient.InvariantRootForm.realCorootPairing A i

abbrev realRootReflection (A : Matrix I I ℤ) (i : I) :
    RealRootSpan I →ₗ[ℝ] RealRootSpan I :=
  Specs.LieNotes.Contragredient.InvariantRootForm.realRootReflection A i

abbrev rootForm (A : Matrix I I ℤ) (d : I → ℝ) : LinearMap.BilinForm ℝ (RealRootSpan I) :=
  Specs.LieNotes.Contragredient.InvariantRootForm.rootForm A d

@[simp]
theorem latticeToReal_single (j : I) (m : ℤ) :
    latticeToReal (Finsupp.single j m) = Finsupp.single j (m : ℝ) :=
  Finsupp.mapRange_single (hf := Int.cast_zero (R := ℝ))

@[simp]
theorem latticeToReal_simple (j : I) : latticeToReal (simpleDegree j) = simpleRoot j := by
  change latticeToReal (Finsupp.single j 1) = Finsupp.single j 1
  simp

@[simp]
theorem realCorootPairing_simple (A : Matrix I I ℤ) (i j : I) :
    realCorootPairing A i (simpleRoot j) = (A i j : ℝ) := by
  change Finsupp.linearCombination ℝ (fun k ↦ (A i k : ℝ)) (Finsupp.single j 1) = _
  simp

theorem realCorootPairing_lattice (A : Matrix I I ℤ) (i : I) (q : Q I) :
    realCorootPairing A i (latticeToReal q) = (corootPairing A i q : ℝ) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Int.cast_add, hp, hq]
  | single j m =>
    change Finsupp.linearCombination ℝ (fun k ↦ (A i k : ℝ))
      (latticeToReal (Finsupp.single j m)) = _
    simp [smul_eq_mul, Int.cast_mul]

theorem realRootReflection_apply (A : Matrix I I ℤ) (i : I) (x : RealRootSpan I) :
    realRootReflection A i x = x - realCorootPairing A i x • simpleRoot i :=
  rfl

theorem realRootReflection_lattice (A : Matrix I I ℤ) (i : I) (q : Q I) :
    realRootReflection A i (latticeToReal q) = latticeToReal (rootReflection A i q) := by
  rw [realRootReflection_apply, realCorootPairing_lattice, rootReflection_apply, map_sub,
    latticeToReal_single]
  simp [Specs.LieNotes.Contragredient.InvariantRootForm.simpleRoot, Finsupp.smul_single]

section Realization

variable [Finite I]

@[simp]
theorem realRootWeight_simple (R : Realization A H) (i : I) :
    realRootWeight R (simpleRoot i) = R.α i := by
  change Finsupp.linearCombination ℝ R.α (Finsupp.single i 1) = _
  simp

theorem realRootWeight_lattice (R : Realization A H) (q : Q I) :
    realRootWeight R (latticeToReal q) = R.rootWeight q := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single j m =>
    rw [latticeToReal_single, Realization.rootWeight_single]
    change Finsupp.linearCombination ℝ R.α (Finsupp.single j (m : ℝ)) = _
    simp only [Finsupp.linearCombination_single, ← Complex.coe_smul, Complex.ofReal_intCast]

theorem realRootWeight_range (R : Realization A H) :
    (realRootWeight R).range = Submodule.span ℝ (Set.range R.rootWeight) := by
  apply le_antisymm
  · change (Finsupp.linearCombination ℝ R.α).range ≤ _
    rw [Finsupp.range_linearCombination]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨simpleDegree i, Realization.rootWeight_simple R i⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact ⟨latticeToReal q, realRootWeight_lattice R q⟩

theorem realRootWeight_apply_coroot (R : Realization A H) (i : I) (x : RealRootSpan I) :
    realRootWeight R x (R.h i) = (realCorootPairing A i x : ℂ) := by
  have h : ((Module.Dual.eval ℂ H (R.h i)).restrictScalars ℝ).comp (realRootWeight R) =
      Complex.ofRealAm.toLinearMap.comp (realCorootPairing A i) := by
    apply Finsupp.basisSingleOne.ext
    intro j
    change realRootWeight R (simpleRoot j) (R.h i) = (realCorootPairing A i (simpleRoot j) : ℂ)
    simp [R.pairing]
  exact LinearMap.congr_fun h x

theorem realRootWeight_reflection (R : Realization A H) (i : I) (x : RealRootSpan I) :
    realRootWeight R (realRootReflection A i x) = R.weightReflection i (realRootWeight R x) := by
  rw [realRootReflection_apply, map_sub, map_smul, realRootWeight_simple,
    Realization.weightReflection_apply, realRootWeight_apply_coroot, Complex.coe_smul]

theorem realRootWeight_orbit (R : Realization A H) (j : I) (w : List I) :
    realRootWeight R (latticeToReal (w.foldr (fun i q ↦ rootReflection A i q) (simpleDegree j))) =
      w.foldr (fun i β ↦ R.weightReflection i β) (R.α j) := by
  rw [realRootWeight_lattice]
  induction w with
  | nil => exact Realization.rootWeight_simple R j
  | cons i w ih =>
    simp only [List.foldr_cons, Realization.rootWeight_rootReflection, ih]

theorem realRootSpan_identification :
    Specs.LieNotes.Contragredient.InvariantRootForm.RealRootSpanIdentification.{u, v} := by
  intro I A H _ _ _ R
  exact ⟨(R.α_independent.restrict_scalars' ℝ).finsuppLinearCombination_injective,
    realRootWeight_range R, latticeToReal_simple, realRootWeight_lattice R,
    realRootWeight_apply_coroot R, realRootReflection_lattice A, realRootWeight_reflection R,
    realRootWeight_orbit R⟩

end Realization

theorem rootForm_simple_left (A : Matrix I I ℤ) (d : I → ℝ) (i : I) (x : RealRootSpan I) :
    rootForm A d (simpleRoot i) x = d i * realCorootPairing A i x := by
  change (Finsupp.linearCombination ℝ (fun j ↦ d j • realCorootPairing A j)
    (Finsupp.single i 1)) x = _
  simp [smul_eq_mul]

theorem rootForm_simple (A : Matrix I I ℤ) (d : I → ℝ) (i j : I) :
    rootForm A d (simpleRoot i) (simpleRoot j) = d i * (A i j : ℝ) := by
  rw [rootForm_simple_left, realCorootPairing_simple]

theorem rootForm_isSymm (hd : SymmetrizingFamily A d) : (rootForm A d).IsSymm := by
  have h : rootForm A d = (rootForm A d).flip := by
    apply Finsupp.basisSingleOne.ext
    intro i
    apply Finsupp.basisSingleOne.ext
    intro j
    change rootForm A d (simpleRoot i) (simpleRoot j) = rootForm A d (simpleRoot j) (simpleRoot i)
    rw [rootForm_simple, rootForm_simple]
    exact hd.2 i j
  exact ⟨fun x y ↦ congrArg (fun B : LinearMap.BilinForm ℝ (RealRootSpan I) ↦ B x y) h⟩

theorem realCorootPairing_eq_form_div (hd : SymmetrizingFamily A d) (i : I) (x : RealRootSpan I) :
    realCorootPairing A i x = rootForm A d (simpleRoot i) x / d i := by
  rw [eq_div_iff (ne_of_gt (hd.1 i)), rootForm_simple_left, mul_comm]

variable [Finite I]

theorem rootForm_simple_sq (hA : IsGeneralizedCartanMatrix A) (d : I → ℝ) (i : I) :
    rootForm A d (simpleRoot i) (simpleRoot i) = 2 * d i := by
  rw [rootForm_simple, hA.1 i, mul_comm]
  norm_num

theorem rootForm_reflection (hA : IsGeneralizedCartanMatrix A) (hd : SymmetrizingFamily A d)
    (i : I) (x y : RealRootSpan I) :
    rootForm A d (realRootReflection A i x) (realRootReflection A i y) = rootForm A d x y := by
  rw [realRootReflection_apply, realRootReflection_apply]
  simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
  rw [(rootForm_isSymm hd).eq x (simpleRoot i), rootForm_simple_sq hA]
  simp only [rootForm_simple_left]
  ring

theorem rootForm_orbit_sq (hA : IsGeneralizedCartanMatrix A) (hd : SymmetrizingFamily A d)
    (j : I) (w : List I) :
    let β := latticeToReal (w.foldr (fun i q ↦ rootReflection A i q) (simpleDegree j))
    rootForm A d β β = 2 * d j := by
  induction w with
  | nil => simpa only [List.foldr_nil, latticeToReal_simple] using rootForm_simple_sq hA d j
  | cons i w ih =>
    simp only [List.foldr_cons, ← realRootReflection_lattice, rootForm_reflection hA hd]
    exact ih

theorem invariantFormAndLengths :
    Specs.LieNotes.Contragredient.InvariantRootForm.InvariantFormAndLengths.{u} := by
  intro I A _ hA d hd
  exact ⟨rootForm_isSymm hd, rootForm_simple A d, realCorootPairing_eq_form_div hd,
    rootForm_simple_sq hA d, rootForm_reflection hA hd, rootForm_orbit_sq hA hd⟩

theorem reflectionAutomorphismsAndRealRoots :
    Specs.LieNotes.Contragredient.InvariantRootForm.ReflectionAutomorphismsAndRealRoots.{u, v} :=
  ⟨ReflectionAutomorphisms.reflectionAutomorphism_existsUnique,
    ReflectionAutomorphisms.cartanReflection_involutive,
    ReflectionAutomorphisms.reflectionAutomorphism_onCartan,
    ReflectionAutomorphisms.reflectionAutomorphism_onWeightSpaces,
    ReflectionAutomorphisms.rootLattice_preserved,
    ReflectionAutomorphisms.realRoot_multiplicity,
    realRootSpan_identification, invariantFormAndLengths⟩

end

end LieNotes.Contragredient.InvariantRootForm
