import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactCentralizer
import LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

noncomputable section

open Topology
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn asMatrix)
open LinearAlgebraicGroups.Specs.ExceptionalOuterCompactCentralizer
open LinearAlgebraicGroups.Specs.ExceptionalCompactInner (fixedSubgroup)

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactCentralizer

section ExponentialChart

open Filter
open Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

private theorem chart_tangent_mono {U V : Subgroup Rˣ} (h : U ≤ V)
    (cU : ClosedSubgroupChart U) (cV : ClosedSubgroupChart V) :
    cU.tangent ≤ cV.tangent := by
  intro x hx
  exact (cV.mem_tangent x).2 fun t => h ((cU.mem_tangent x).1 hx t)

private theorem le_of_expLines {J U : Subgroup Rˣ} (C : ClosedSubgroupChart U)
    [ConnectedSpace U] (h : ∀ x : R, x ∈ C.tangent → x ∈ exponentialLines J) :
    U ≤ J := by
  let U₀ := J.subgroupOf U
  have hOne : (1 : U) ∈ C.expOpen.target := by
    have h0 := C.expOpen.map_source C.zero_mem
    have he : C.expOpen 0 = (1 : U) := Subtype.ext (by simpa using C.exp_chart 0 C.zero_mem)
    simpa only [he] using h0
  have hOpen : IsOpen (U₀ : Set U) := by
    apply U₀.isOpen_of_mem_nhds (g := 1)
    refine mem_of_superset (C.expOpen.open_target.mem_nhds hOne) ?_
    intro g hg
    let x := C.expOpen.symm g
    have he := C.exp_chart x (C.expOpen.map_target hg)
    rw [C.expOpen.right_inv hg] at he
    change (g : Rˣ) ∈ J
    rw [he]
    simpa only [one_smul] using h x x.property 1
  have hEq : (U₀ : Set U) = Set.univ :=
    (show IsClopen (U₀ : Set U) from ⟨U₀.isClosed_of_isOpen hOpen, hOpen⟩).eq_univ ⟨1, U₀.one_mem⟩
  intro g hg
  have hx : (⟨g, hg⟩ : U) ∈ (U₀ : Set U) := hEq.symm ▸ Set.mem_univ _
  exact hx

end ExponentialChart

private theorem scaledCircleExp_eq_one (r : ℝ) :
    Circle.exp (2 * Real.pi * r) = 1 ↔ ∃ n : ℤ, r = n := by
  rw [Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_left_cancel₀ (by positivity : 2 * Real.pi ≠ 0)
      (hn.trans (mul_comm _ _))⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, mul_comm _ _⟩

section CompactAbelianQuotients

open Filter Module

variable {V D : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup D] [TopologicalSpace D] [CompactSpace D]

private theorem span_ker_eq_top (f : V →+ D) (hf : IsQuotientMap f) :
    Submodule.span ℝ (f.ker : Set V) = ⊤ := by
  by_contra h
  obtain ⟨l, hl, hlker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr h) inferInstance
  have hle : f.ker ≤ l.toAddMonoidHom.ker := by
    intro x hx
    have hx' := Submodule.mem_map_of_mem (f := l) (Submodule.subset_span hx)
    rwa [hlker, Submodule.mem_bot] at hx'
  let e := QuotientAddGroup.quotientKerEquivOfSurjective f hf.surjective
  let q : D → ℝ := QuotientAddGroup.lift f.ker l.toAddMonoidHom hle ∘ e.symm
  have hq (x : V) : q (f x) = l x := by
    change QuotientAddGroup.lift f.ker l.toAddMonoidHom hle (e.symm (e (x : V ⧸ f.ker))) = l x
    rw [e.symm_apply_apply]
    rfl
  have hc : Continuous q := hf.continuous_iff.mpr (by
    simpa only [Function.comp_def, hq] using l.continuous_of_finiteDimensional)
  have hsurj : Function.Surjective l := by
    obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
      by_contra! hz
      exact hl (LinearMap.ext fun x => hz x)
    intro y
    refine ⟨(y / l x) • x, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx]
  have hqs : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨f x, hq x⟩
  exact (not_compactSpace_iff.mpr inferInstance) (hqs.compactSpace hc)

/-- The compact quotient of a finite-dimensional real vector space by a
discrete additive kernel is a product of unit circles. -/
private theorem compactQuotient_circleProduct (f : V →+ D) (hf : IsQuotientMap f)
    [DiscreteTopology f.ker] :
    ∃ (n : ℕ) (e : Additive (Fin n → Circle) ≃+ D), Continuous e ∧ Continuous e.symm := by
  let L : Submodule ℤ V := f.ker.toIntSubmodule
  let : DiscreteTopology L := inferInstanceAs (DiscreteTopology f.ker)
  let : IsZLattice ℝ L := ⟨span_ker_eq_top f hf⟩
  let n := finrank ℤ L
  let b : Basis (Fin n) ℤ L := Module.finBasis ℤ L
  let c := b.ofZLatticeBasis ℝ L
  let T := Additive (Fin n → Circle)
  let q : V →+ T :=
    { toFun := fun x j => Circle.exp (2 * Real.pi * c.equivFun x j)
      map_zero' := funext fun j => by
        change Circle.exp (2 * Real.pi * c.equivFun (0 : V) j) = 1
        simp
      map_add' := fun x y => funext fun j => by
        change Circle.exp (2 * Real.pi * c.equivFun (x + y) j) = _
        simp only [map_add, Pi.add_apply, mul_add, Circle.exp_add]
        rfl }
  have hq (x : V) (j : Fin n) :
      (q x).toMul j = Circle.exp (2 * Real.pi * c.equivFun x j) := rfl
  have hqC : Continuous q := continuous_pi fun j =>
    Circle.exp.continuous.comp (continuous_const.mul
      ((continuous_apply j).comp c.equivFun.toLinearMap.continuous_of_finiteDimensional))
  have hqS : Function.Surjective q := by
    intro y
    refine ⟨c.equivFun.symm (fun j => (Complex.arg (y.toMul j)) / (2 * Real.pi)), funext fun j => ?_⟩
    change (q (c.equivFun.symm (fun j => (Complex.arg (y.toMul j)) / (2 * Real.pi)))).toMul j =
      y.toMul j
    rw [hq, LinearEquiv.apply_symm_apply]
    have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hπ, Circle.exp_arg]
  have hqK : q.ker = f.ker := by
    ext x
    have hL : x ∈ f.ker ↔ x ∈ Submodule.span ℤ (Set.range c) := by
      change x ∈ L ↔ _
      rw [b.ofZLatticeBasis_span ℝ L]
    rw [hL, c.mem_span_iff_repr_mem ℤ]
    constructor
    · intro hx j
      have h : (q x).toMul j = 1 :=
        congrArg (fun y : T => y.toMul j) (AddMonoidHom.mem_ker.mp hx)
      rw [hq, scaledCircleExp_eq_one] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨z, hz.symm⟩
    · intro hx
      apply AddMonoidHom.mem_ker.mpr
      funext j
      change (q x).toMul j = 1
      rw [hq, scaledCircleExp_eq_one]
      obtain ⟨z, hz⟩ := hx j
      exact ⟨z, hz.symm⟩
  have hqQ : IsQuotientMap q :=
    (AddMonoidHom.isOpenMap_of_sigmaCompact q hqS hqC).isQuotientMap hqC hqS
  let eF := QuotientAddGroup.liftEquiv f.ker hf.surjective rfl
  let eQ := QuotientAddGroup.liftEquiv f.ker hqS hqK.symm
  let e := eQ.symm.trans eF
  have hc (x : V) : e (q x) = f x := by
    change eF (eQ.symm (eQ (x : V ⧸ f.ker))) = _
    rw [eQ.symm_apply_apply]
    rfl
  have hc' (x : V) : e.symm (f x) = q x := e.symm_apply_eq.mpr (hc x).symm
  exact ⟨n, e, hqQ.continuous_iff.mpr (by
    simpa only [Function.comp_def, hc] using hf.continuous),
    hf.continuous_iff.mpr (by simpa only [Function.comp_def, hc'] using hqC)⟩

end CompactAbelianQuotients

section AbelianMatrixSubgroups

open Filter NormedSpace
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
variable {U : Subgroup Rˣ} (C : ClosedSubgroupChart U)

private theorem tangent_commute (hU : ∀ g h : U, Commute g h) (x y : C.tangent) :
    Commute (x : R) (y : R) := by
  have hx := (C.mem_tangent x).mp x.property
  have hy := (C.mem_tangent y).mp y.property
  have hY : HasDerivAt (fun s : ℝ => (expUnit (s • (y : R))).val) (y : R) 0 := by
    simpa using hasDerivAt_exp_smul_const (y : R) (0 : ℝ)
  have hConst (t : ℝ) : conjugate (expUnit (t • (x : R))) (y : R) = y := by
    let g := expUnit (t • (x : R))
    have hD := (hY.const_mul (g : R)).mul_const (g⁻¹ : Rˣ).val
    have hfun (s : ℝ) : (g : R) * (expUnit (s • (y : R))).val * (g⁻¹ : Rˣ).val =
        (expUnit (s • (y : R))).val := by
      let z := expUnit (s • (y : R))
      have hu : Commute g z := (hU ⟨g, hx t⟩ ⟨z, hy s⟩).map U.subtype
      change (g * z * g⁻¹).val = z.val
      rw [hu.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact (hD.congr_of_eventuallyEq (Eventually.of_forall fun s => (hfun s).symm)).unique hY
  have hD := (conjugation_derivative (x : R) (y : R)).congr_of_eventuallyEq
    (Eventually.of_forall fun t => (hConst t).symm)
  exact sub_eq_zero.mp (hD.unique (hasDerivAt_const _ _))

private def abelianExponential [CommGroup U] (hU : ∀ g h : U, Commute g h) :
    C.tangent →+ Additive U where
  toFun x := Additive.ofMul ⟨expUnit (x : R), by
    simpa only [one_smul] using (C.mem_tangent x).mp x.property 1⟩
  map_zero' := by
    change (⟨expUnit ((0 : C.tangent) : R), _⟩ : U) = 1
    exact Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by
    apply Units.ext
    simp only [Submodule.coe_add]
    apply exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (tangent_commute C hU x y) <;>
      rw [expSeries_radius_eq_top] <;> exact edist_lt_top _ _)

private theorem abelianExponential_surjective [CommGroup U] [ConnectedSpace U]
    (hU : ∀ g h : U, Commute g h) : Function.Surjective (abelianExponential C hU) := by
  let f := abelianExponential C hU
  have hchart (x : C.tangent) (hx : x ∈ C.expOpen.source) :
      f x = Additive.ofMul (C.expOpen x) := Subtype.ext (C.exp_chart x hx).symm
  have hOne : (0 : Additive U) ∈ C.expOpen.target := by
    change (1 : U) ∈ C.expOpen.target
    have h0 := C.expOpen.map_source C.zero_mem
    have he : C.expOpen 0 = (1 : U) := Subtype.ext (by simpa using C.exp_chart 0 C.zero_mem)
    simpa only [he] using h0
  have hOpen : IsOpen (f.range : Set (Additive U)) := by
    apply f.range.isOpen_of_mem_nhds (g := 0)
    refine mem_of_superset (C.expOpen.open_target.mem_nhds hOne) ?_
    intro g hg
    refine ⟨C.expOpen.symm g, ?_⟩
    rw [hchart _ (C.expOpen.map_target hg), C.expOpen.right_inv hg]
    rfl
  let : ConnectedSpace (Additive U) := inferInstanceAs (ConnectedSpace U)
  have hAll : (f.range : Set (Additive U)) = Set.univ :=
    (show IsClopen (f.range : Set (Additive U)) from ⟨f.range.isClosed_of_isOpen hOpen, hOpen⟩).eq_univ
      ⟨0, f.range.zero_mem⟩
  intro g
  have : g ∈ (f.range : Set (Additive U)) := hAll.symm ▸ Set.mem_univ _
  exact this

private theorem abelianExponential_discreteKer [CommGroup U] (hU : ∀ g h : U, Commute g h) :
    DiscreteTopology (abelianExponential C hU).ker := by
  let f := abelianExponential C hU
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  have hEq : (Subtype.val : f.ker → C.tangent) ⁻¹' C.expOpen.source = {0} := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · change (x : C.tangent) ∈ C.expOpen.source at hx
      have he : C.expOpen (x : C.tangent) = C.expOpen 0 := by
        apply Subtype.ext
        rw [C.exp_chart _ hx, C.exp_chart _ C.zero_mem]
        exact congrArg (fun t : Additive U => (t.toMul : Rˣ))
          ((AddMonoidHom.mem_ker.mp x.property).trans f.map_zero.symm)
      exact Set.mem_singleton_iff.mpr (Subtype.ext (C.expOpen.injOn hx C.zero_mem he))
    · rw [Set.mem_singleton_iff.mp hx]
      exact C.zero_mem
  rw [← hEq]
  exact C.expOpen.open_source.preimage continuous_subtype_val

/-- A compact connected abelian matrix subgroup is a compact torus in
the induced topology. -/
theorem compactTorus_of_abelianMatrixSubgroup
    [FiniteDimensional ℝ R] [ConnectedSpace U] [CompactSpace U]
    (C : ClosedSubgroupChart U) (hU : ∀ g h : U, Commute g h) : IsCompactTorus U := by
  let : CommGroup U := { (inferInstance : Group U) with mul_comm := fun x y => (hU x y).eq }
  let f := abelianExponential C hU
  have hc : Continuous f := continuous_induced_rng.mpr
    (continuous_expUnit.comp continuous_subtype_val)
  have hs := abelianExponential_surjective C hU
  let : DiscreteTopology f.ker := abelianExponential_discreteKer C hU
  let : CompactSpace (Additive U) := inferInstanceAs (CompactSpace U)
  let : T2Space (Additive U) := inferInstanceAs (T2Space U)
  have hq : IsQuotientMap f := (AddMonoidHom.isOpenMap_of_sigmaCompact f hs hc).isQuotientMap hc hs
  obtain ⟨n, e, he, he'⟩ := compactQuotient_circleProduct f hq
  let e' : (Fin n → Circle) ≃* U :=
    { toEquiv := e.toEquiv
      map_mul' := fun x y => e.map_add (Additive.ofMul x) (Additive.ofMul y) }
  exact ⟨n, e', he, he'⟩

end AbelianMatrixSubgroups


section MaximalTorusTangent

open Filter NormedSpace
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
open private exp_add_commuting from LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

private theorem expUnit_add_of_commute {x y : R} (h : Commute x y) :
    expUnit (x + y) = expUnit x * expUnit y := by
  apply Units.ext
  simp only [expUnit_val, Units.val_mul]
  exact exp_add_commuting h

private theorem expUnit_commute {x y : R} (h : Commute x y) :
    Commute (expUnit x) (expUnit y) := by
  change expUnit x * expUnit y = expUnit y * expUnit x
  rw [← expUnit_add_of_commute h, add_comm, expUnit_add_of_commute h.symm]

private def expLine (x : R) : Multiplicative ℝ →* Rˣ where
  toFun t := expUnit (t.toAdd • x)
  map_one' := by change expUnit ((0 : ℝ) • x) = 1; simp
  map_mul' t s := by
    change expUnit ((t.toAdd + s.toAdd) • x) = _
    rw [add_smul, expUnit_add_of_commute (((Commute.refl x).smul_left t.toAdd).smul_right s.toAdd)]

/-- The tangent of a maximal compact torus contains every direction of the
ambient compact matrix subgroup commuting with its tangent. -/
theorem maximalTorus_tangent_centralizer [FiniteDimensional ℝ R]
    {J S : Subgroup Rˣ} (hJ : IsCompact (J : Set Rˣ))
    (hS : IsMaximalCompactTorus (J : Set Rˣ) S) (C : ClosedSubgroupChart S)
    {x : R} (hx : x ∈ exponentialLines J) (hcomm : ∀ y : C.tangent, Commute x (y : R)) :
    x ∈ C.tangent := by
  obtain ⟨n, e, he, _⟩ := hS.1
  let : CommGroup S := {
    (inferInstance : Group S) with
    mul_comm := fun a b => by
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [← map_mul, mul_comm, map_mul] }
  let : ConnectedSpace S := e.surjective.connectedSpace he
  have hSexp : Function.Surjective (abelianExponential C (fun a b => mul_comm a b)) :=
    abelianExponential_surjective C _
  have hcross (a : S) (t : Multiplicative ℝ) : Commute (a : Rˣ) (expLine x t) := by
    obtain ⟨y, hy⟩ := hSexp (Additive.ofMul a)
    have hy' : expUnit (y : R) = (a : Rˣ) :=
      congrArg (fun v : Additive S => (v.toMul : Rˣ)) hy
    rw [← hy']
    exact expUnit_commute ((hcomm y).smul_left t.toAdd).symm
  let f := S.subtype.noncommCoprod (expLine x) hcross
  let L := f.range.topologicalClosure
  have hle : f.range ≤ J := by
    rintro _ ⟨⟨a, t⟩, rfl⟩
    exact J.mul_mem (hS.2.1 a.property) (hx t.toAdd)
  have hLJ : L ≤ J := f.range.topologicalClosure_minimal hle hJ.isClosed
  have hLclosed : IsClosed (L : Set Rˣ) := f.range.isClosed_topologicalClosure
  let : CompactSpace L :=
    isCompact_iff_compactSpace.mp (hJ.of_isClosed_subset hLclosed hLJ)
  let : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  have hLcon : IsConnected (L : Set Rˣ) := by
    have ht : Continuous (fun a : S × Multiplicative ℝ => a.2.toAdd • x) :=
      (show Continuous (fun a : S × Multiplicative ℝ => a.2.toAdd) from
        continuous_snd).smul continuous_const
    have hf : Continuous f := continuous_fst.subtype_val.mul (continuous_expUnit.comp ht)
    exact (isConnected_range hf).closure
  let : ConnectedSpace L := isConnected_iff_connectedSpace.mp hLcon
  have hLt : IsCompactTorus L := compactTorus_of_abelianMatrixSubgroup
    (closedSubgroupExponential R L hLclosed).some (fun a b => mul_comm' a b)
  have hSL : S ≤ L := by
    intro a ha
    apply f.range.le_topologicalClosure
    refine ⟨(⟨a, ha⟩, 1), ?_⟩
    change a * expLine x 1 = a
    rw [map_one, mul_one]
  have hLS : L = S := hS.2.2 L hLt hLJ hSL
  apply (C.mem_tangent x).mpr
  intro t
  rw [← hLS]
  apply f.range.le_topologicalClosure
  refine ⟨(1, Multiplicative.ofAdd t), ?_⟩
  change 1 * expUnit (t • x) = expUnit (t • x)
  exact one_mul _

end MaximalTorusTangent

section HaarAverage
open Topology MeasureTheory Module

variable {P V : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Averaging a positive symmetric form gives an invariant form for a
continuous finite-dimensional real representation of a compact group. -/
theorem invariantBilinear_of_compact (ρ : P →* (V ≃ₗ[ℝ] V))
    (hρ : ∀ x : V, Continuous (fun g : P => ρ g x)) :
    ∃ B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ,
      (∀ x y, B x y = B y x) ∧
      (∀ x, x ≠ 0 → 0 < B x x) ∧
      ∀ g x y, B (ρ g x) (ρ g y) = B x y := by
  let : MeasurableSpace P := borel P
  let : BorelSpace P := ⟨rfl⟩
  let μ : Measure P := Measure.haar
  let b := Module.finBasis ℝ V
  let B₀ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    ∑ j, (b.coord j).smulRight (b.coord j)
  have hB₀ (x y : V) : B₀ x y = ∑ j, b.coord j x * b.coord j y := by
    simp [B₀, smul_eq_mul]
  have hSymm (x y : V) : B₀ x y = B₀ y x := by simp [hB₀, mul_comm]
  have hPos (x : V) (hx : x ≠ 0) : 0 < B₀ x x := by
    rw [hB₀]
    have hj : ∃ j, b.coord j x ≠ 0 := by
      by_contra! h
      apply hx
      apply b.repr.injective
      ext j
      simpa using h j
    obtain ⟨j, hj⟩ := hj
    apply Finset.sum_pos' (fun k _ => mul_self_nonneg _) ⟨j, Finset.mem_univ _, ?_⟩
    exact mul_self_pos.mpr hj
  let F (x y : V) (g : P) := B₀ (ρ g⁻¹ x) (ρ g⁻¹ y)
  have hF (x y : V) : Continuous (F x y) := by
    simp only [F, hB₀]
    apply continuous_finsetSum
    intro j _
    have hc := (b.coord j).continuous_of_finiteDimensional
    exact (hc.comp ((hρ x).comp continuous_inv)).mul (hc.comp ((hρ y).comp continuous_inv))
  have hInt (x y : V) : Integrable (F x y) μ :=
    (hF x y).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let b₁ (x : V) : V →ₗ[ℝ] ℝ :=
    { toFun := fun y => ∫ g, F x y g ∂μ
      map_add' := fun y z => by
        simpa only [F, map_add] using integral_add (hInt x y) (hInt x z)
      map_smul' := fun t y => by
        simp only [F, map_smul, RingHom.id_apply, smul_eq_mul, integral_const_mul] }
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    { toFun := b₁
      map_add' := fun x y => LinearMap.ext fun z => by
        simpa only [b₁, F, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]
          using integral_add (hInt x z) (hInt y z)
      map_smul' := fun t x => LinearMap.ext fun z => by
        simp only [b₁, F, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          map_smul, RingHom.id_apply, smul_eq_mul, integral_const_mul] }
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x y
    change (∫ g, F x y g ∂μ) = ∫ g, F y x g ∂μ
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => hSymm _ _)
  · intro x hx
    change 0 < ∫ g, F x x g ∂μ
    have h (g : P) : 0 < F x x g := hPos _ (fun h =>
      hx ((ρ g⁻¹).injective (h.trans (map_zero (ρ g⁻¹)).symm)))
    exact (hF x x).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun g => (h g).le) (h 1).ne'
  · intro k x y
    change (∫ g, F (ρ k x) (ρ k y) g ∂μ) = ∫ g, F x y g ∂μ
    have h (g : P) : F (ρ k x) (ρ k y) g = F x y (k⁻¹ * g) := by
      simp only [F, mul_inv_rev, inv_inv, map_mul, LinearEquiv.mul_apply]
    simpa only [h] using integral_mul_left_eq_self (μ := μ) (F x y) k⁻¹

end HaarAverage

section MatrixCommutators

open Filter NormedSpace Module Algebra
open Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

private def conjugationRepresentation : Rˣ →* (R ≃ₗ[ℝ] R) where
  toFun g :=
    { toFun := conjugate g
      invFun := conjugate g⁻¹
      left_inv := fun x => by simp [conjugate, mul_assoc]
      right_inv := fun x => by simp [conjugate, mul_assoc]
      map_add' := fun x y => by simp [conjugate, mul_add, add_mul]
      map_smul' := fun t x => by simp [conjugate] }
  map_one' := by
    ext x
    change conjugate 1 x = x
    simp [conjugate]
  map_mul' g h := by
    ext x
    change conjugate (g * h) x = conjugate g (conjugate h x)
    simp [conjugate, mul_inv_rev, mul_assoc]

private def commutatorMap (x : R) : R →ₗ[ℝ] R :=
  LinearMap.mulLeft ℝ x - LinearMap.mulRight ℝ x

private theorem commutatorMap_skew [FiniteDimensional ℝ R] {J : Subgroup Rˣ}
    (B : R →ₗ[ℝ] R →ₗ[ℝ] ℝ)
    (hInv : ∀ g ∈ J, ∀ x y : R, B (conjugate g x) (conjugate g y) = B x y)
    {a : R} (ha : a ∈ exponentialLines J) (x y : R) :
    B (commutatorMap a x) y = -B x (commutatorMap a y) := by
  let l := (B.flip y).toContinuousLinearMap
  let r := (B x).toContinuousLinearMap
  have hl := l.hasFDerivAt.comp_hasDerivAt 0 (conjugation_derivative a x)
  have hr := r.hasFDerivAt.comp_hasDerivAt 0 (conjugation_derivative (-a) y)
  have hEq (t : ℝ) :
      l (conjugate (expUnit (t • a)) x) = r (conjugate (expUnit (t • -a)) y) := by
    let g := expUnit (t • a)
    have h := hInv g (ha t) x (conjugate g⁻¹ y)
    change B (conjugate g x) y = B x (conjugate (expUnit (t • -a)) y)
    rw [smul_neg, expUnit_neg]
    change B (conjugate g x) y = B x (conjugate g⁻¹ y)
    simpa [conjugate, mul_assoc] using h
  have hval := (hl.congr_of_eventuallyEq
    (Eventually.of_forall fun t => (hEq t).symm)).unique hr
  change B (a * x - x * a) y = B x ((-a) * y - y * (-a)) at hval
  change B (a * x - x * a) y = -B x (a * y - y * a)
  have harg : (-a) * y - y * (-a) = -(a * y - y * a) := by
    rw [neg_mul, mul_neg]
    abel
  rw [harg, map_neg] at hval
  exact hval

end MatrixCommutators

section CompactCentralizer

open Filter NormedSpace
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
open Specs.ExceptionalCompactInner (fixedSubgroup)

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

private def componentOne (J : Subgroup P) : Subgroup P :=
  (Subgroup.connectedComponentOfOne J).map J.subtype

private theorem componentOne_le (J : Subgroup P) : componentOne J ≤ J := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

private theorem componentOne_isConnected (J : Subgroup P) :
    IsConnected (componentOne J : Set P) :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn

private theorem componentOne_isCompact (J : Subgroup P) (hJ : IsCompact (J : Set P)) :
    IsCompact (componentOne J : Set P) := by
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

private theorem le_componentOne_of_connected {J U : Subgroup P} (hU : U ≤ J)
    [ConnectedSpace U] : U ≤ componentOne J := by
  let ι : U → J := Subgroup.inclusion hU
  have hι : Continuous ι := continuous_induced_rng.mpr continuous_subtype_val
  have hConn := isConnected_range hι
  have hOne : (1 : J) ∈ Set.range ι := ⟨1, rfl⟩
  intro g hg
  let a : U := ⟨g, hg⟩
  exact ⟨ι a, hConn.isPreconnected.subset_connectedComponent hOne (Set.mem_range_self a), rfl⟩

end CompactCentralizer

section CompactTori

variable {P : Type*} [Group P] [TopologicalSpace P]

private theorem commutes_of_torus (S : Subgroup P) (hS : IsCompactTorus S)
    {s t : P} (hs : s ∈ S) (ht : t ∈ S) : Commute s t := by
  obtain ⟨n, e, _, _⟩ := hS
  obtain ⟨a, ha⟩ := e.surjective ⟨s, hs⟩
  obtain ⟨b, hb⟩ := e.surjective ⟨t, ht⟩
  have h : Commute (⟨s, hs⟩ : S) ⟨t, ht⟩ := by
    rw [← ha, ← hb]
    exact (Commute.all a b).map e.toMonoidHom
  exact h.map S.subtype

variable [IsTopologicalGroup P]

private theorem torus_le_centralizerComponent {K S : Subgroup P}
    (hS : IsCompactTorus S) (hSK : S ≤ K) :
    S ≤ componentOne (K ⊓ Subgroup.centralizer (S : Set P)) := by
  let : ConnectedSpace S := by
    obtain ⟨n, e, he, _⟩ := hS
    exact e.surjective.connectedSpace he
  apply le_componentOne_of_connected
  intro s hs
  exact ⟨hSK hs, Subgroup.mem_centralizer_iff.mpr fun t ht => commutes_of_torus S hS ht hs⟩

end CompactTori

section CompactMatrixCentralizer

open Filter NormedSpace
open LinearAlgebraicGroups.Specs.ArchimedeanLieChart
open LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

private theorem exponentialLines_componentOne {J : Subgroup Rˣ} {x : R}
    (hx : x ∈ exponentialLines J) : x ∈ exponentialLines (componentOne J) := by
  let f : ℝ → J := fun t => ⟨expUnit (t • x), hx t⟩
  have hf : Continuous f := continuous_induced_rng.mpr
    (continuous_expUnit.comp (continuous_id.smul continuous_const))
  have hOne : (1 : J) ∈ Set.range f := ⟨0, Subtype.ext (by simp [f])⟩
  intro t
  exact ⟨f t, (isConnected_range hf).isPreconnected.subset_connectedComponent hOne
    (Set.mem_range_self t), rfl⟩

private theorem commute_of_commute_expUnits (a x : R)
    (h : ∀ t : ℝ, Commute a (expUnit (t • x)).val) : Commute a x := by
  have hd : HasDerivAt (fun t : ℝ => (expUnit (t • x)).val) x 0 := by
    simpa only [expUnit_val, zero_smul, exp_zero, one_mul] using
      hasDerivAt_exp_smul_const x (0 : ℝ)
  exact ((hd.const_mul a).congr_of_eventuallyEq
    (Eventually.of_forall fun t => (h t).eq.symm)).unique (hd.mul_const a)

private theorem exponentialLines_centralizer_commute {S J : Subgroup Rˣ}
    {x y : R} (hx : x ∈ exponentialLines (J ⊓ Subgroup.centralizer (S : Set Rˣ)))
    (hy : y ∈ exponentialLines S) : Commute x y := by
  apply commute_of_commute_expUnits
  intro t
  have ht : expUnit (t • y) ∈ S := hy t
  apply Commute.symm
  apply commute_of_commute_expUnits
  intro u
  have h := Subgroup.mem_centralizer_iff.mp (hx u).2 (expUnit (t • y)) ht
  exact congrArg Units.val h

private theorem expUnit_map_algEquiv (σ : R ≃ₐ[ℝ] R) [FiniteDimensional ℝ R] (x : R) :
    Units.map σ.toMonoidHom (expUnit x) = expUnit (σ x) := by
  apply Units.ext
  change σ (expUnit x).val = (expUnit (σ x)).val
  simp only [expUnit_val]
  apply map_exp_of_mem_ball (𝕂 := ℝ) σ.toRingHom
    σ.toLinearMap.continuous_of_finiteDimensional
  rw [expSeries_radius_eq_top]
  exact edist_lt_top _ _

private theorem commute_of_tangent_commute {J : Subgroup Rˣ} [ConnectedSpace J]
    (CJ : ClosedSubgroupChart J) (h : ∀ x y : CJ.tangent, Commute (x : R) (y : R))
    (a b : J) : Commute a b := by
  let X : Set Rˣ := Set.range fun x : CJ.tangent => expUnit (x : R)
  let L := Subgroup.closure X
  have hX : X.Pairwise Commute := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _
    exact expUnit_commute (h x y)
  let : IsMulCommutative L := Subgroup.isMulCommutative_closure hX
  have hL : J ≤ L := by
    apply le_of_expLines CJ
    intro x hx t
    exact Subgroup.subset_closure ⟨⟨t • x, CJ.tangent.smul_mem t hx⟩, rfl⟩
  apply Subtype.ext
  exact congrArg (Subtype.val : L → Rˣ)
    (mul_comm' (⟨a, hL a.property⟩ : L) ⟨b, hL b.property⟩)

private theorem compactCentralizer_tangent_commutes [FiniteDimensional ℝ R]
    (K : Subgroup Rˣ) (hK : IsCompact (K : Set Rˣ))
    (a : R ≃ₐ[ℝ] R) (ha : Function.Involutive a)
    (hKstable : Set.MapsTo (Units.mapEquiv a.toMulEquiv) (K : Set Rˣ) K)
    (S : Subgroup Rˣ)
    (hS : IsMaximalCompactTorus (identityComponent
      (K ⊓ fixedSubgroup (Units.mapEquiv a.toMulEquiv))) S)
    (CS : ClosedSubgroupChart S)
    (CC : ClosedSubgroupChart (K ⊓ Subgroup.centralizer (S : Set Rˣ))) :
    ∀ x y : CC.tangent, Commute (x : R) (y : R) := by
  let θ := Units.mapEquiv a.toMulEquiv
  let J := K ⊓ fixedSubgroup θ
  let C := K ⊓ Subgroup.centralizer (S : Set Rˣ)
  let L := CC.tangent
  have hθS (s : Rˣ) (hs : s ∈ S) : θ s = s :=
    (componentOne_le J (hS.2.1 hs)).2
  have hC : IsCompact (C : Set Rˣ) := hK.inter_right (S : Set Rˣ).isClosed_centralizer
  have hJ : IsCompact (J : Set Rˣ) := hK.inter_right (isClosed_eq (by
    rw [Units.continuous_iff]
    exact ⟨a.toLinearMap.continuous_of_finiteDimensional.comp Units.continuous_val,
      a.toLinearMap.continuous_of_finiteDimensional.comp (Units.continuous_val.comp continuous_inv)⟩)
    continuous_id)
  have hJ₀ := componentOne_isCompact J hJ
  have h_a_L (x : R) (hx : x ∈ L) : a x ∈ L := by
    apply (CC.mem_tangent _).mpr
    intro t
    have hg := (CC.mem_tangent x).mp hx t
    have he : θ (expUnit (t • x)) = expUnit (t • a x) := by
      change Units.map a.toMonoidHom (expUnit (t • x)) = _
      rw [expUnit_map_algEquiv, map_smul]
    rw [← he]
    refine ⟨hKstable hg.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have h := congrArg θ (Subgroup.mem_centralizer_iff.mp hg.2 s hs)
    simpa only [map_mul, hθS s hs] using h
  have hCentral (x : R) (hx : x ∈ L) (hax : a x = x) (y : R) (hy : y ∈ L) :
      Commute x y := by
    have hxJ : x ∈ exponentialLines J := by
      intro t
      refine ⟨((CC.mem_tangent x).mp hx t).1, ?_⟩
      change Units.map a.toMonoidHom (expUnit (t • x)) = expUnit (t • x)
      rw [expUnit_map_algEquiv, map_smul, hax]
    have hxS : x ∈ CS.tangent := maximalTorus_tangent_centralizer hJ₀ hS CS
      (exponentialLines_componentOne hxJ)
      (fun z => exponentialLines_centralizer_commute ((CC.mem_tangent x).mp hx)
        ((CS.mem_tangent z).mp z.property))
    exact (exponentialLines_centralizer_commute ((CC.mem_tangent y).mp hy)
      ((CS.mem_tangent x).mp hxS)).symm
  have hLeft (x y : R) (hx : x ∈ L) (hy : y ∈ L) :
      commutatorMap (a x) y = -commutatorMap x y := by
    have he : a (x + a x) = x + a x := by rw [map_add, ha, add_comm]
    have hm := hCentral (x + a x) (L.add_mem hx (h_a_L x hx)) he y hy
    have hn : commutatorMap (a x) y + commutatorMap x y = 0 := by
      calc
        _ = (x + a x) * y - y * (x + a x) := by
          change (a x * y - y * a x) + (x * y - y * x) = _
          rw [add_mul, mul_add]
          abel
        _ = 0 := sub_eq_zero.mpr hm.eq
    exact add_eq_zero_iff_eq_neg.mp hn
  have hSkew (x y : R) : commutatorMap x y = -commutatorMap y x := by
    change x * y - y * x = -(y * x - x * y)
    abel
  have hRight (x y : R) (hx : x ∈ L) (hy : y ∈ L) :
      commutatorMap x (a y) = -commutatorMap x y := by
    rw [hSkew x (a y), hLeft y x hy hx, neg_neg, hSkew y x]
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let ρ := conjugationRepresentation.comp C.subtype
  obtain ⟨B, _, hpos, hB⟩ := invariantBilinear_of_compact ρ (fun x => by
    change Continuous (fun g : C => (g : Rˣ).val * x * ((g : Rˣ)⁻¹ : Rˣ).val)
    fun_prop)
  have hInv (g : Rˣ) (hg : g ∈ C) (x y : R) :
      B (conjugate g x) (conjugate g y) = B x y := hB ⟨g, hg⟩ x y
  intro x y
  let z := commutatorMap (x : R) (y : R)
  have hz : z ∈ L := CC.bracket_mem x y
  have hFix : a z = z := by
    change a ((x : R) * (y : R) - (y : R) * (x : R)) = _
    rw [map_sub, map_mul, map_mul]
    change commutatorMap (a x) (a y) = _
    rw [hLeft x (a y) x.property (h_a_L y y.property), hRight x y x.property y.property, neg_neg]
  have hComm : Commute z (x : R) := hCentral z hz hFix x x.property
  have hZero : commutatorMap (x : R) z = 0 := sub_eq_zero.mpr hComm.symm.eq
  have hForm : B z z = 0 := by
    change B (commutatorMap (x : R) (y : R)) z = 0
    rw [commutatorMap_skew B hInv ((CC.mem_tangent x).mp x.property), hZero, map_zero, neg_zero]
  have hz0 : z = 0 := by
    by_contra hn
    exact (hpos z hn).ne' hForm
  exact sub_eq_zero.mp hz0

/-- The identity component of the centralizer is a maximal compact torus.
The involution in this version is induced by a linear algebra automorphism
of the ambient algebra. -/
theorem compactCentralizer_componentOne_maximalTorus [FiniteDimensional ℝ R]
    (K : Subgroup Rˣ) (hK : IsCompact (K : Set Rˣ))
    (a : R ≃ₐ[ℝ] R) (ha : Function.Involutive a)
    (hKstable : Set.MapsTo (Units.mapEquiv a.toMulEquiv) (K : Set Rˣ) K)
    (S : Subgroup Rˣ)
    (hS : IsMaximalCompactTorus (identityComponent
      (K ⊓ fixedSubgroup (Units.mapEquiv a.toMulEquiv))) S) :
    IsMaximalCompactTorus (K : Set Rˣ)
      (componentOne (K ⊓ Subgroup.centralizer (S : Set Rˣ))) := by
  let C := K ⊓ Subgroup.centralizer (S : Set Rˣ)
  let T := componentOne C
  let J := K ⊓ fixedSubgroup (Units.mapEquiv a.toMulEquiv)
  have hSclosed : IsClosed (S : Set Rˣ) := by
    obtain ⟨n, e, he, _⟩ := hS.1
    exact (isCompact_iff_compactSpace.mpr (e.surjective.compactSpace he)).isClosed
  let CS := (closedSubgroupExponential R S hSclosed).some
  have hC : IsCompact (C : Set Rˣ) := hK.inter_right (S : Set Rˣ).isClosed_centralizer
  let CC := (closedSubgroupExponential R C hC.isClosed).some
  have hT := componentOne_isCompact C hC
  let CT := (closedSubgroupExponential R T hT.isClosed).some
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let : ConnectedSpace T := isConnected_iff_connectedSpace.mp (componentOne_isConnected C)
  have hle := chart_tangent_mono (componentOne_le C) CT CC
  have hab := compactCentralizer_tangent_commutes K hK a ha hKstable S hS CS CC
  have hTtorus := compactTorus_of_abelianMatrixSubgroup CT
    (commute_of_tangent_commute CT fun x y => hab ⟨x, hle x.property⟩ ⟨y, hle y.property⟩)
  refine ⟨hTtorus, (componentOne_le C).trans inf_le_left, ?_⟩
  intro V hV hVK hTV
  have hSK : S ≤ K := fun _ hs => (componentOne_le J (hS.2.1 hs)).1
  have hST : S ≤ T := torus_le_centralizerComponent hS.1 hSK
  let : ConnectedSpace V := by
    obtain ⟨_, e, he, _⟩ := hV
    exact e.surjective.connectedSpace he
  have hVC : V ≤ C := by
    intro v hv
    refine ⟨hVK hv, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    exact commutes_of_torus V hV (hTV (hST hs)) hv
  exact le_antisymm (le_componentOne_of_connected hVC) hTV

end CompactMatrixCentralizer

section Transport

variable {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]

private theorem subgroupMap_isInducing (f : P →* Q) (hf : IsEmbedding f) (S : Subgroup P) :
    IsInducing (S.equivMapOfInjective f hf.injective) := by
  apply (IsInducing.of_comp_iff (g := (Subtype.val : S.map f → Q))
    IsInducing.subtypeVal).mp
  exact hf.isInducing.comp IsInducing.subtypeVal

private theorem isCompactTorus_map_iff (f : P →* Q) (hf : IsEmbedding f) (S : Subgroup P) :
    IsCompactTorus (S.map f) ↔ IsCompactTorus S := by
  let e := S.equivMapOfInjective f hf.injective
  let E := e.toEquiv.toHomeomorphOfIsInducing (subgroupMap_isInducing f hf S)
  have he : Continuous e := E.continuous
  have he' : Continuous e.symm := E.symm.continuous
  constructor
  · rintro ⟨n, a, ha, ha'⟩
    exact ⟨n, a.trans e.symm, he'.comp ha, ha'.comp he⟩
  · rintro ⟨n, a, ha, ha'⟩
    exact ⟨n, a.trans e, he.comp ha, ha'.comp he'⟩

private theorem isMaximalCompactTorus_map_iff (f : P →* Q) (hf : IsEmbedding f)
    (J S : Subgroup P) :
    IsMaximalCompactTorus (J.map f : Set Q) (S.map f) ↔ IsMaximalCompactTorus (J : Set P) S := by
  have htorus := isCompactTorus_map_iff f hf
  have hle {U V : Subgroup P} : U.map f ≤ V.map f ↔ U ≤ V :=
    Subgroup.map_le_map_iff_of_injective hf.injective
  constructor
  · intro h
    refine ⟨(htorus S).mp h.1, hle.mp h.2.1, ?_⟩
    intro V hV hVJ hSV
    exact Subgroup.map_injective hf.injective
      (h.2.2 (V.map f) ((htorus V).mpr hV) (hle.mpr hVJ) (hle.mpr hSV))
  · intro h
    refine ⟨(htorus S).mpr h.1, hle.mpr h.2.1, ?_⟩
    intro V hV hVJ hSV
    let U := V.comap f
    have hUV : U.map f = V := Subgroup.map_comap_eq_self (hVJ.trans (J.map_le_range f))
    have hU : IsCompactTorus U := (htorus U).mp (hUV.symm ▸ hV)
    have hUJ : U ≤ J := hle.mp (hUV.symm ▸ hVJ)
    have hSU : S ≤ U := hle.mp (hUV.symm ▸ hSV)
    exact hUV.symm.trans (congrArg (Subgroup.map f) (h.2.2 U hU hUJ hSU))

variable [IsTopologicalGroup P] [IsTopologicalGroup Q]

private theorem componentOne_map (f : P →* Q) (hf : IsEmbedding f) (J : Subgroup P) :
    (componentOne J).map f = componentOne (J.map f) := by
  let e := J.equivMapOfInjective f hf.injective
  let E := e.toEquiv.toHomeomorphOfIsInducing (subgroupMap_isInducing f hf J)
  have he : Continuous e := E.continuous
  have he' : Continuous e.symm := E.symm.continuous
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e x, ?_, rfl⟩
    change e x ∈ connectedComponent (1 : J.map f)
    simpa only [map_one] using he.mapsTo_connectedComponent (1 : J) hx
  · rintro ⟨y, hy, rfl⟩
    have h : e.symm y ∈ connectedComponent (1 : J) := by
      simpa only [map_one] using he'.mapsTo_connectedComponent (1 : J.map f) hy
    exact ⟨(e.symm y).val, ⟨e.symm y, h, rfl⟩,
      congrArg Subtype.val (e.apply_symm_apply y)⟩

omit [TopologicalSpace P] [TopologicalSpace Q] [IsTopologicalGroup P] [IsTopologicalGroup Q] in
private theorem map_inf_fixedSubgroup (f : P →* Q) (hf : Function.Injective f)
    (K : Subgroup P) (θ : MulAut P) (σ : MulAut Q) (h : ∀ x, f (θ x) = σ (f x)) :
    (K ⊓ fixedSubgroup θ).map f = K.map f ⊓ fixedSubgroup σ := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, (h x).symm.trans (congrArg f hx.2)⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := hz.1
    exact ⟨x, ⟨hx, hf ((h x).trans hz.2)⟩, rfl⟩

omit [TopologicalSpace P] [TopologicalSpace Q] [IsTopologicalGroup P] [IsTopologicalGroup Q] in
private theorem map_inf_centralizer (f : P →* Q) (hf : Function.Injective f)
    (K S : Subgroup P) :
    (K ⊓ Subgroup.centralizer (S : Set P)).map f =
      K.map f ⊓ Subgroup.centralizer (S.map f : Set Q) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp hx.2 s hs)
  · intro hz
    obtain ⟨x, hx, rfl⟩ := hz.1
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro s hs
    apply hf
    simpa only [map_mul] using Subgroup.mem_centralizer_iff.mp hz.2 (f s) ⟨s, hs, rfl⟩

private theorem centralizerComponent_map_involution {K S : Subgroup P} (θ : MulAut P)
    (hθ : Continuous θ) (hi : Function.Involutive θ) (hK : Set.MapsTo θ (K : Set P) K)
    (hS : S ≤ fixedSubgroup θ) :
    (componentOne (K ⊓ Subgroup.centralizer (S : Set P))).map θ.toMonoidHom =
      componentOne (K ⊓ Subgroup.centralizer (S : Set P)) := by
  let C := K ⊓ Subgroup.centralizer (S : Set P)
  have hC : ∀ x ∈ C, θ x ∈ C := by
    intro x hx
    refine ⟨hK hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have he : θ s = s := hS hs
    simpa only [map_mul, he] using congrArg θ (Subgroup.mem_centralizer_iff.mp hx.2 s hs)
  have hmap : C.map θ.toMonoidHom = C := by
    ext x
    exact ⟨fun ⟨y, hy, e⟩ => e ▸ hC y hy, fun hx => ⟨θ x, hC x hx, hi x⟩⟩
  have hs : θ.symm = θ := DFunLike.ext _ _ fun x => by
    have hx := hi (θ.symm x)
    rw [MulEquiv.apply_symm_apply] at hx
    exact hx.symm
  let e : P ≃ₜ P := ⟨θ.toEquiv, hθ, hs.symm ▸ hθ⟩
  change (componentOne C).map θ.toMonoidHom = componentOne C
  rw [componentOne_map θ.toMonoidHom e.isEmbedding, hmap]

end Transport

section GraphEmbedding

variable {P R : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] [FiniteDimensional ℝ R]

private def swapAlgebra : (R × R) ≃ₐ[ℝ] (R × R) :=
  { (RingEquiv.prodComm : (R × R) ≃+* (R × R)) with
    commutes' := fun _ => rfl }

private def graphMatrix (f : P →* Rˣ) (θ : MulAut P) : P →* (R × R)ˣ :=
  (MulEquiv.prodUnits.symm.toMonoidHom).comp (f.prod (f.comp θ.toMonoidHom))

omit [IsTopologicalGroup P] [NormedAlgebra ℝ R] [CompleteSpace R] [FiniteDimensional ℝ R] in
private theorem graphMatrix_isEmbedding (f : P →* Rˣ) (hf : IsEmbedding f) (θ : MulAut P)
    (hθ : Continuous θ) : IsEmbedding (graphMatrix f θ) := by
  have hc : Continuous (graphMatrix f θ) := by
    rw [Units.continuous_iff]
    exact ⟨(Units.continuous_val.comp hf.continuous).prodMk
      (Units.continuous_val.comp (hf.continuous.comp hθ)),
      (Units.continuous_coe_inv.comp hf.continuous).prodMk
        (Units.continuous_coe_inv.comp (hf.continuous.comp hθ))⟩
  let π₁ : (R × R)ˣ → Rˣ := Units.map (MonoidHom.fst R R)
  have hπ : Continuous π₁ := Units.continuous_iff.mpr
    ⟨continuous_fst.comp Units.continuous_val, continuous_fst.comp Units.continuous_coe_inv⟩
  exact IsEmbedding.of_comp hc hπ (show IsEmbedding (π₁ ∘ graphMatrix f θ) from hf)

omit [TopologicalSpace P] [IsTopologicalGroup P] [CompleteSpace R] [FiniteDimensional ℝ R] in
private theorem graphMatrix_intertwines (f : P →* Rˣ) (θ : MulAut P)
    (hi : Function.Involutive θ) (x : P) :
    graphMatrix f θ (θ x) =
      Units.mapEquiv (swapAlgebra (R := R)).toMulEquiv (graphMatrix f θ x) := by
  apply Units.ext
  exact Prod.ext rfl (congrArg (fun y => (f y).val) (hi x))

/-- For an embedded compact matrix group, the centralizer of a maximal torus
of the connected fixed group has an invariant maximal torus as its identity
component. The graph embedding handles continuous involutions. -/
theorem compactCentralizer_of_embedding
    (f : P →* Rˣ) (hf : IsEmbedding f)
    (K : Subgroup P) (hK : IsCompact (K : Set P)) (θ : MulAut P)
    (hθ : Continuous θ) (hi : Function.Involutive θ) (hθK : Set.MapsTo θ (K : Set P) K)
    (S : Subgroup P)
    (hS : IsMaximalCompactTorus (identityComponent (K ⊓ fixedSubgroup θ)) S) :
    let T := componentOne (K ⊓ Subgroup.centralizer (S : Set P))
    S ≤ T ∧ T.map θ.toMonoidHom = T ∧ IsMaximalCompactTorus (K : Set P) T := by
  let m := graphMatrix f θ
  let a := swapAlgebra (R := R)
  let σ := Units.mapEquiv a.toMulEquiv
  have hm := graphMatrix_isEmbedding f hf θ hθ
  have hσ (x : P) : m (θ x) = σ (m x) := graphMatrix_intertwines f θ hi x
  have hKmap : IsCompact (K.map m : Set (R × R)ˣ) := hK.image hm.continuous
  have hKstable : Set.MapsTo σ (K.map m : Set (R × R)ˣ) (K.map m) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨θ x, hθK hx, hσ x⟩
  have hJ := map_inf_fixedSubgroup m hm.injective K θ σ hσ
  have hSmap : IsMaximalCompactTorus
      (identityComponent (K.map m ⊓ fixedSubgroup σ)) (S.map m) := by
    change IsMaximalCompactTorus
      (componentOne (K.map m ⊓ fixedSubgroup σ) : Set (R × R)ˣ) (S.map m)
    rw [← hJ, ← componentOne_map m hm]
    exact (isMaximalCompactTorus_map_iff m hm _ _).mpr hS
  have hT := compactCentralizer_componentOne_maximalTorus
    (K.map m) hKmap a (fun _ => rfl) hKstable (S.map m) hSmap
  rw [← map_inf_centralizer m hm.injective K S, ← componentOne_map m hm] at hT
  have hSJ : S ≤ K ⊓ fixedSubgroup θ :=
    fun _ hx => componentOne_le _ (hS.2.1 hx)
  exact ⟨torus_le_centralizerComponent hS.1 (hSJ.trans inf_le_left),
    centralizerComponent_map_involution θ hθ hi hθK (hSJ.trans inf_le_right),
    (isMaximalCompactTorus_map_iff m hm _ _).mp hT⟩

end GraphEmbedding

open private asMatrix_isClosedEmbedding from LinearAlgebraicGroups.Arithmetic.AdelicGroups

open scoped Matrix.Norms.Operator

/-- The compact centralizer statement on the given complex point group. -/
theorem compactCentralizer : CompactCentralizer := by
  intro G i _ _ _ ω θ _ hθ _ hi hcomm hCompact _ S hS
  let m := asMatrix i ℂ
  have hm := (asMatrix_isClosedEmbedding i ℂ).isEmbedding
  let : IsTopologicalGroup (PointsIn i ℂ) :=
    IsInducing.isTopologicalGroup m (.induced _)
  let K := fixedSubgroup ω
  have hK : IsCompact (K : Set (PointsIn i ℂ)) := isCompact_iff_compactSpace.mpr hCompact
  have hθK : Set.MapsTo θ (K : Set (PointsIn i ℂ)) K := by
    intro x hx
    exact (hcomm x).symm.trans (congrArg θ hx)
  exact ⟨componentOne (K ⊓ Subgroup.centralizer (S : Set (PointsIn i ℂ))), rfl,
    compactCentralizer_of_embedding m hm K hK θ hθ hi hθK S hS⟩

end LinearAlgebraicGroups.Arithmetic.ExceptionalOuterCompactCentralizer
