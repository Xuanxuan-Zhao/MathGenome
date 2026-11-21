/-
The torus periodization proof is adapted from the Apache-2.0 project
https://github.com/math-inc/Sphere-Packing-Lean, revision
1e98fb493088948ca7bbf47d7faed49cc5b39fc4, files
  SpherePacking/CohnElkies/PoissonSummationLattices/UnitAddTorus.lean
  SpherePacking/CohnElkies/PoissonSummationLattices/PoissonSummation.lean
  SpherePacking/CohnElkies/PoissonSummationSchwartz/Basic.lean
  SpherePacking/CohnElkies/PoissonSummationSchwartz/PoissonSummation.lean
  SpherePacking/ForMathlib/FourierLinearEquiv.lean
All proof bodies needed here are included and checked locally. The final
statements and the matrix/absolute-convergence bridges use this project's
canonical Euclidean and Fourier definitions.
-/
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.RCLike.Inner
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PoissonSummation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000


/-!
Helper lemmas about the quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n` used in the Poisson summation
development.
-/

open scoped BigOperators Real
open MeasureTheory

namespace SchwartzMap.UnitAddTorus

/-- The coordinatewise quotient map `(Fin n → ℝ) → (ℝ/ℤ)^n`. -/
def coeFun (n : ℕ) : (Fin n → ℝ) → UnitAddTorus (Fin n) :=
  fun x i => (x i : UnitAddCircle)

/-- Continuity of the coordinatewise quotient map `coeFun`. -/
@[continuity]
theorem continuous_coeFun {n : ℕ} : Continuous (coeFun n) := by
  exact
    (continuous_pi fun i => (AddCircle.continuous_mk' (p := (1 : ℝ))).comp (continuous_apply i))

/-- A homeomorphism `α × (Fin n → α) ≃ (Fin (n+1) → α)`, specialized to constant families. -/
def finSuccPiHomeomorph (α : Type*) [TopologicalSpace α] (n : ℕ) :
    (α × (Fin n → α)) ≃ₜ (Fin n.succ → α) where
  toEquiv := Fin.consEquiv (fun _ ↦ α)
  continuous_toFun := by
    simpa [Fin.consEquiv] using Continuous.finCons (by fun_prop) (by fun_prop)
  continuous_invFun := by fun_prop

/-- `coeFun` is an open quotient map, so it presents `(ℝ/ℤ)^n` as a quotient of `ℝ^n`. -/
theorem isOpenQuotientMap_coeFun (n : ℕ) : IsOpenQuotientMap (coeFun n) := by
  induction n with
  | zero =>
      have h : coeFun 0 =
          (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0)) : _ → _) := by
        funext x; exact Subsingleton.elim _ _
      simpa [h] using
        (Homeomorph.homeomorphOfUnique (Fin 0 → ℝ) (UnitAddTorus (Fin 0))).isOpenQuotientMap
  | succ n ih =>
      -- Reduce to the product case using `finSuccPiHomeomorph`.
      have h₁ : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) := by
        simpa using
          (QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ)))
      let eX := (finSuccPiHomeomorph (α := ℝ) n).symm
      let eY := finSuccPiHomeomorph (α := UnitAddCircle) n
      have heX : IsOpenQuotientMap (eX : (Fin n.succ → ℝ) → ℝ × (Fin n → ℝ)) :=
        eX.isOpenQuotientMap
      have hprod :
          IsOpenQuotientMap (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coeFun n)) :=
        IsOpenQuotientMap.prodMap h₁ (ih)
      -- `coeFun (n+1)` is conjugate to `Prod.map` by these homeomorphisms.
      have hconj :
          coeFun n.succ =
            (fun x =>
              eY
                (Prod.map (fun x : ℝ => (x : UnitAddCircle)) (coeFun n) (eX x))) := by
        funext x
        ext i
        cases i using Fin.cases with
        | zero => simp [coeFun, eY, finSuccPiHomeomorph, eX, Prod.map]
        | succ i => simp [coeFun, eY, finSuccPiHomeomorph, eX, Prod.map, Fin.tail]
      have hhomeoY : IsOpenQuotientMap eY := eY.isOpenQuotientMap
      -- Compose: `Fin n.succ → ℝ` --eX--> `ℝ × (Fin n → ℝ)` --Prod.map--> ...
      --   --> `Fin n.succ → UnitAddCircle` via the homeomorphism.
      rw [hconj]
      exact (IsOpenQuotientMap.comp hhomeoY (IsOpenQuotientMap.comp hprod heX))

theorem measurePreserving_coeFun (n : ℕ) (t : ℝ) :
    MeasurePreserving (coeFun n)
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (volume : Measure (UnitAddTorus (Fin n))) := by
  -- `coeFun` is the product of the coordinatewise quotient maps `ℝ → UnitAddCircle`,
  -- each of which is measure-preserving on a fundamental interval.
  exact
    (MeasureTheory.measurePreserving_pi
      (μ := fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)))
      (ν := fun _ : Fin n => (volume : Measure UnitAddCircle))
      (hf := fun _ => UnitAddCircle.measurePreserving_mk t))

theorem volume_restrict_pi_eq_pi_restrict (n : ℕ) (t : ℝ) :
    (volume : Measure (Fin n → ℝ)).restrict (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) =
      Measure.pi fun _ : Fin n => (volume : Measure ℝ).restrict (Set.Ioc t (t + 1)) := by
  exact (Measure.restrict_pi_pi
    (μ := fun _ : Fin n => (volume : Measure ℝ)) (s := fun _ : Fin n => Set.Ioc t (t + 1)))

theorem mFourier_apply_coeFun (n : ℕ) (k : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier k (coeFun n x) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  -- Unfold, then rewrite `fourier` explicitly on real representatives and use `exp_sum`.
  simpa [UnitAddTorus.mFourier, ContinuousMap.coe_mk, coeFun, fourier_coe_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => 2 * π * Complex.I * ((k i : ℝ) * x i))).symm

/--
Evaluate the additive character `mFourier k` on a point `x : ℝ^n`
viewed in the torus via `coeFun`.
-/
theorem mFourier_apply_coeFun_ofLp (n : ℕ) (k : Fin n → ℤ) (x : EuclideanSpace ℝ (Fin n)) :
    UnitAddTorus.mFourier k (coeFun n (WithLp.ofLp x)) =
      Complex.exp
        (2 * π * Complex.I *
          (∑ i : Fin n, (k i : ℝ) * x i)) := by
  simpa using (mFourier_apply_coeFun (n := n) (k := k) (x := WithLp.ofLp x))

/--
Pull back Haar integration on `(ℝ/ℤ)^n` to the fundamental cube `∏ i, (t, t+1] ⊆ ℝ^n`.
-/
theorem integral_eq_integral_preimage_coeFun (n : ℕ) (t : ℝ) (g : UnitAddTorus (Fin n) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin n)))) :
    (∫ y : UnitAddTorus (Fin n), g y) =
      ∫ x, g (coeFun n x) ∂(volume : Measure (Fin n → ℝ)).restrict
        (Set.univ.pi fun _ : Fin n => Set.Ioc t (t + 1)) := by
  have hmp := measurePreserving_coeFun n t
  have h1 :
      (∫ y : UnitAddTorus (Fin n), g y) =
        ∫ x, g (coeFun n x) ∂(Measure.pi fun _ : Fin n =>
          (volume : Measure ℝ).restrict (Set.Ioc t (t + 1))) := by
    rw [← hmp.map_eq]
    simpa using (MeasureTheory.integral_map (hφ := hmp.aemeasurable) (f := g)
      (hfm := by simpa [hmp.map_eq] using hg))
  simpa [(volume_restrict_pi_eq_pi_restrict n t).symm] using h1

end SchwartzMap.UnitAddTorus


/-!
# Poisson summation for `ℤ`-lattices

Poisson summation for full-rank `ℤ`-lattices in Euclidean space, in the form needed by the
Cohn-Elkies argument.
-/

open scoped BigOperators
open MeasureTheory

namespace SchwartzMap

variable {d : ℕ}
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

local notation "E" => EuclideanSpace ℝ (Fin d)

-- This file is intentionally minimal; its purpose is to provide a reusable proof of Poisson
-- summation for `ℤ`-lattices, used by `SpherePacking/CohnElkies/Prereqs.lean`.

section StandardLattice

/-- The standard `ℤ`-lattice in `E = ℝ^d`, i.e. the span of the standard basis over `ℤ`. -/
noncomputable def standardLattice (d : ℕ) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))

namespace standardLattice

/-- The standard lattice has the discrete topology. -/
instance instDiscreteTopology : DiscreteTopology (standardLattice d) := by
  simpa [standardLattice] using
    (inferInstance :
      DiscreteTopology
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

/-- The standard lattice is a full-rank `ℤ`-lattice in `ℝ^d`. -/
instance instIsZLattice : IsZLattice ℝ (standardLattice d) := by
  simpa [standardLattice] using
    (inferInstance :
      IsZLattice ℝ
        (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

end StandardLattice.standardLattice
/-!
## Poisson summation for lattices

We prove a Poisson summation formula for Schwartz functions on `E = ℝ^d`, for any full-rank
`ℤ`-lattice `Λ ⊆ E`.

The proof follows the standard Fourier-series-on-the-torus argument:
- periodize a Schwartz function along the lattice;
- descend it to the quotient torus;
- compute Fourier coefficients by pulling back to a fundamental domain and using the
  fundamental-domain tiling lemma;
- sum the Fourier series using absolute summability of Fourier coefficients (Schwartz decay).
-/

section PoissonSummation

namespace PoissonSummation

/-! ### The standard lattice `ℤ^d` -/

namespace Standard

/-- Embed an integer vector `k : ℤ^d` into `E = ℝ^d`. -/
noncomputable def intVec (k : Fin d → ℤ) : E :=
  WithLp.toLp (2 : ENNReal) (fun i : Fin d => (k i : ℝ))

/-- Coordinatewise evaluation of `intVec`. -/
@[simp]
lemma intVec_apply (k : Fin d → ℤ) (i : Fin d) :
    intVec (d := d) k i = (k i : ℝ) := by
  simp [intVec]

/-- The image of `intVec` lies in the standard lattice. -/
lemma intVec_mem_standardLattice (k : Fin d → ℤ) :
    intVec (d := d) k ∈ SchwartzMap.standardLattice d := by
  have hsum :
      intVec (d := d) k =
        ∑ i : Fin d, (k i) • ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i) := by
    ext j
    simp [intVec, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [hsum]
  refine (SchwartzMap.standardLattice d).sum_mem ?_
  intro i hi
  refine (SchwartzMap.standardLattice d).smul_mem (k i) ?_
  exact Submodule.subset_span ⟨i, rfl⟩

end SchwartzMap.PoissonSummation.PoissonSummation.Standard
/-!
### Poisson summation for the standard lattice

We specialize to the standard lattice in `E = ℝ^d` and use Fourier series on the torus
`(ℝ/ℤ)^d`. The proof is a multi-dimensional analogue of `Mathlib.Analysis.Fourier.PoissonSummation`
and follows the usual steps:
- periodize a Schwartz function along the integer lattice;
- descend to a continuous function on the torus;
- compute Fourier coefficients as Fourier transforms by swapping `tsum` and `integral` and using a
  fundamental domain;
- apply uniform convergence of the Fourier series (summable Fourier coefficients).
-/

namespace SchwartzMap

open TopologicalSpace MeasureTheory

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace PoissonSummation.Standard
open _root_.SchwartzMap.UnitAddTorus

/-! #### The integer cube as a fundamental domain -/

/-- The half-open cube `(0,1]^d`, used as a fundamental domain for the action of `ℤ^d` on `ℝ^d`. -/
def iocCube : Set E := {x | ∀ i : Fin d, x i ∈ Set.Ioc (0 : ℝ) 1}

/-- Measurability of the fundamental cube `iocCube`. -/
lemma measurableSet_iocCube : MeasurableSet (iocCube (d := d)) := by
  -- `iocCube` is an intersection of coordinate preimages of a measurable interval.
  have hset :
      iocCube (d := d) = ⋂ i : Fin d, {x : E | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    ext x
    simp [iocCube]
  -- Coordinate projections are measurable, and `Ioc` is measurable.
  have hcoord :
      ∀ i : Fin d, MeasurableSet {x : E | x i ∈ Set.Ioc (0 : ℝ) 1} := by
    intro i
    have hproj : Measurable fun x : E => x i := by
      simpa using
        (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ) i).measurable
    exact hproj measurableSet_Ioc
  simpa [hset] using MeasurableSet.iInter (ι := Fin d) hcoord

/-- `iocCube` is null-measurable (useful for integrals over its indicator). -/
lemma nullMeasurableSet_iocCube : NullMeasurableSet (iocCube (d := d)) :=
  (measurableSet_iocCube (d := d)).nullMeasurableSet

/--
Every point `x : ℝ^d` has a unique translate by an integer vector that lies in `iocCube`.

This is the usual "fractional part" decomposition used to identify `ℝ^d / ℤ^d` with a cube.
-/
lemma existsUnique_add_intVec_mem_iocCube (x : E) :
    ∃! n : Fin d → ℤ, x + SchwartzMap.PoissonSummation.Standard.intVec (d := d) n ∈
      iocCube (d := d) := by
  -- Choose the unique `n i` sending `x i` into `(0,1]`.
  have hxcoord :
      ∀ i : Fin d, ∃! m : ℤ, (x i : ℝ) + m • (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    intro i
    simpa [one_smul, add_assoc] using
      (existsUnique_add_zsmul_mem_Ioc (G := ℝ) (ha := zero_lt_one) (b := (x i : ℝ))
        (c := (0 : ℝ)))
  choose n hn hn_unique using hxcoord
  refine ⟨n, ?_, ?_⟩
  · -- membership
    intro i
    simpa [SchwartzMap.PoissonSummation.Standard.intVec_apply, iocCube, zsmul_one] using hn i
  · -- uniqueness
    intro n' hn'
    funext i
    have hcoords : ∀ i : Fin d,
        (x + SchwartzMap.PoissonSummation.Standard.intVec (d := d) n') i ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [iocCube] using hn'
    exact hn_unique i (n' i) (by
      simpa [SchwartzMap.PoissonSummation.Standard.intVec_apply, zsmul_one] using hcoords i)

/-! #### Elements of the standard lattice are integer vectors -/

/-- Every element of the standard lattice comes from an integer vector via `intVec`. -/
lemma exists_intVec_eq_of_mem_standardLattice (x : E)
    (hx : x ∈ SchwartzMap.standardLattice d) :
    ∃ n : Fin d → ℤ, x = SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
  let b : OrthonormalBasis (Fin d) ℝ E := EuclideanSpace.basisFun (Fin d) ℝ
  have hx_span :
      x ∈ Submodule.span ℤ (Set.range fun j : Fin d => (b.toBasis j : E)) := by
    -- Avoid rewriting `basisFun` into `single` (this can confuse `simp` through `Set.range`).
    simpa [SchwartzMap.standardLattice, standardLattice] using hx
  have hx_repr :=
    (Module.Basis.mem_span_iff_repr_mem (R := ℤ) (b := b.toBasis) x).1 hx_span
  choose n hn using hx_repr
  have hn' : ∀ i : Fin d, (n i : ℝ) = x i := by
    intro i
    simpa [b] using hn i
  refine ⟨n, ?_⟩
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.intVec_apply, hn' i]

/-! #### Dual lattice of the standard lattice -/

/-- The dual of the standard lattice (for the Euclidean inner product) is the standard lattice. -/
lemma dualSubmodule_standardLattice_eq :
    LinearMap.BilinForm.dualSubmodule (B := (innerₗ E : LinearMap.BilinForm ℝ E))
        (SchwartzMap.standardLattice d) =
      SchwartzMap.standardLattice d := by
  ext x
  constructor
  · intro hx
    have hxcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = x i := by
      intro i
      have hinner :
          inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∈ (1 : Submodule ℤ ℝ) := by
        simpa [innerₗ_apply_apply] using
          hx _ (Submodule.subset_span ⟨i, by simp⟩)
      rcases Submodule.mem_one.mp hinner with ⟨n, hn⟩
      exact ⟨n, by simpa [-EuclideanSpace.basisFun_apply] using hn⟩
    choose n hn using hxcoord
    have hx' : x = SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
      ext i
      simp [SchwartzMap.PoissonSummation.Standard.intVec_apply, hn i]
    simpa [hx'] using
      SchwartzMap.PoissonSummation.Standard.intVec_mem_standardLattice (d := d) n
  · intro hx y hy
    rcases exists_intVec_eq_of_mem_standardLattice (d := d) x hx with ⟨n, rfl⟩
    rcases exists_intVec_eq_of_mem_standardLattice (d := d) y hy with ⟨m, rfl⟩
    refine Submodule.mem_one.mpr ⟨∑ i : Fin d, n i * m i, ?_⟩
    simp [innerₗ_apply_apply, SchwartzMap.PoissonSummation.Standard.intVec,
      PiLp.inner_apply, map_sum, Int.cast_mul, mul_comm]

end SchwartzMap.PoissonSummation.Standard
namespace SchwartzMap

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace PoissonSummation.Standard
open _root_.SchwartzMap.UnitAddTorus

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d`. -/
def coeFunE : E → UnitAddTorus (Fin d) :=
  fun x => UnitAddTorus.coeFun d ((WithLp.ofLp : E → (Fin d → ℝ)) x)

/-- Continuity of the quotient map `coeFunE`. -/
@[continuity]
theorem continuous_coeFunE : Continuous (coeFunE (d := d)) := by
  exact (UnitAddTorus.continuous_coeFun (n := d)).comp
    (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ))

/-- `coeFunE` is an open quotient map (so `UnitAddTorus` is the quotient `ℝ^d/ℤ^d`). -/
theorem isOpenQuotientMap_coeFunE : IsOpenQuotientMap (coeFunE (d := d)) := by
  exact
    IsOpenQuotientMap.comp (UnitAddTorus.isOpenQuotientMap_coeFun d)
      (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ)).isOpenQuotientMap

/-- Adding an integer vector does not change the image in `(ℝ/ℤ)^d`. -/
@[simp]
theorem coeFunE_add_intVec (x : E) (n : Fin d → ℤ) :
    coeFunE (d := d) (x + SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) =
      coeFunE (d := d) x := by
  ext i
  simp [coeFunE, UnitAddTorus.coeFun]

/-- If two points map to the same torus point, their difference is an integer vector. -/
theorem exists_intVec_eq_sub_of_coeFunE_eq {x y : E}
    (h : coeFunE (d := d) x = coeFunE (d := d) y) :
    ∃ n : Fin d → ℤ, x - y = SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
  have hcoord : ∀ i : Fin d, ∃ n : ℤ, (n : ℝ) = (x i - y i : ℝ) := by
    intro i
    have hsub : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      simpa [UnitAddCircle, AddCircle.coe_sub, coeFunE, UnitAddTorus.coeFun] using
        sub_eq_zero.2 (congrArg (fun t => t i) h)
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (x i - y i : ℝ))).1 hsub with ⟨n, hn⟩
    exact ⟨n, by simpa using hn⟩
  choose n hn using hcoord
  refine ⟨n, ?_⟩
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.intVec, hn i]

/-- The cube `iocCube` is a fundamental domain for translation by the standard lattice. -/
theorem isAddFundamentalDomain_iocCube :
    MeasureTheory.IsAddFundamentalDomain (SchwartzMap.standardLattice d)
      (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) (volume : Measure E) := by
  refine MeasureTheory.IsAddFundamentalDomain.mk'
      (SchwartzMap.PoissonSummation.Standard.nullMeasurableSet_iocCube (d := d)) ?_
  intro x
  rcases SchwartzMap.PoissonSummation.Standard.existsUnique_add_intVec_mem_iocCube (d := d) x with
    ⟨n, hn, hn_unique⟩
  refine
    ⟨(⟨SchwartzMap.PoissonSummation.Standard.intVec (d := d) n,
        SchwartzMap.PoissonSummation.Standard.intVec_mem_standardLattice (d := d) n⟩), ?_, ?_⟩
  · -- membership
    simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc] using hn
  · -- uniqueness
    intro ℓ hℓ
    rcases
        SchwartzMap.PoissonSummation.Standard.exists_intVec_eq_of_mem_standardLattice (d := d)
          (ℓ : E) ℓ.property with
      ⟨n', hn'⟩
    have : n' = n := hn_unique n' (by
      simpa [Submodule.vadd_def, vadd_eq_add, add_comm, add_left_comm, add_assoc, hn'] using hℓ)
    apply Subtype.ext
    simp [hn', this]

/-- Pull back Haar integration on `(ℝ/ℤ)^d` to `iocCube` in `E = ℝ^d`. -/
theorem integral_eq_integral_preimage_coeFunE (g : UnitAddTorus (Fin d) → ℂ)
    (hg : AEStronglyMeasurable g (volume : Measure (UnitAddTorus (Fin d)))) :
    (∫ y : UnitAddTorus (Fin d), g y) =
      ∫ x, g (coeFunE (d := d) x) ∂(volume : Measure E).restrict
        (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) := by
  have h1 :
      (∫ y : UnitAddTorus (Fin d), g y) =
        ∫ x, g (UnitAddTorus.coeFun d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1)) := by
    simpa using
      (UnitAddTorus.integral_eq_integral_preimage_coeFun (n := d) (t := (0 : ℝ)) g hg)
  let f : (Fin d → ℝ) ≃ᵐ E := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  have hmp : MeasurePreserving (⇑f) (volume : Measure (Fin d → ℝ)) (volume : Measure E) := by
    simpa [f, MeasurableEquiv.coe_toLp] using (PiLp.volume_preserving_toLp (ι := Fin d))
  have hpre :
      f ⁻¹' (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) =
        Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1) := by
    ext x
    simp [f, SchwartzMap.PoissonSummation.Standard.iocCube, MeasurableEquiv.coe_toLp]
  have hmpR :
      MeasurePreserving (⇑f)
        ((volume : Measure (Fin d → ℝ)).restrict
          (f ⁻¹' SchwartzMap.PoissonSummation.Standard.iocCube (d := d)))
        ((volume : Measure E).restrict
          (SchwartzMap.PoissonSummation.Standard.iocCube (d := d))) :=
    MeasurePreserving.restrict_preimage hmp
      (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d))
  have h2 :
      (∫ x, g (UnitAddTorus.coeFun d x) ∂(volume : Measure (Fin d → ℝ)).restrict
          (Set.univ.pi fun _ : Fin d => Set.Ioc (0 : ℝ) (0 + 1))) =
        ∫ y, g (coeFunE (d := d) y) ∂(volume : Measure E).restrict
          (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) := by
    simpa [hpre, coeFunE, f] using
      (MeasurePreserving.integral_comp' hmpR
        (g := fun y : E => g (UnitAddTorus.coeFun d (WithLp.ofLp y))))
  exact h1.trans h2

end SchwartzMap.PoissonSummation.Standard

/-!
Basic definitions and lemmas for Poisson summation of Schwartz functions on `ℝ^d` over full-rank
`ℤ`-lattices.
-/

open scoped BigOperators FourierTransform
open MeasureTheory

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

open _root_.SchwartzMap.UnitAddTorus

/-- Equivalence between integer vectors `Fin d → ℤ` and the standard lattice `Λ = ℤ^d ⊆ ℝ^d`. -/
noncomputable def equivIntVec : (Fin d → ℤ) ≃ Λ := by
  refine Equiv.ofBijective
    (fun n : Fin d → ℤ =>
      ⟨SchwartzMap.PoissonSummation.Standard.intVec (d := d) n,
        SchwartzMap.PoissonSummation.Standard.intVec_mem_standardLattice (d := d) n⟩)
    ?_
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hab' :
        SchwartzMap.PoissonSummation.Standard.intVec (d := d) a =
          SchwartzMap.PoissonSummation.Standard.intVec (d := d) b := by
      simpa using congrArg Subtype.val hab
    funext i
    have := congrArg (fun x : E => x i) hab'
    simpa [SchwartzMap.PoissonSummation.Standard.intVec_apply] using this
  · intro ℓ
    rcases
        SchwartzMap.PoissonSummation.Standard.exists_intVec_eq_of_mem_standardLattice (d := d)
          (x := (ℓ : E)) ℓ.property with
      ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa using hn.symm

/-- Coercion lemma for `equivIntVec`. -/
@[simp] lemma coe_equivIntVec (n : Fin d → ℤ) :
    ((equivIntVec (d := d) n : Λ) : E) =
      SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := rfl

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

/-- Measurability of the additive action of the standard lattice on `E = ℝ^d`. -/
instance instMeasurableVAdd_standardLattice :
    MeasurableVAdd Λ E := by
  refine { measurable_const_vadd := ?_, measurable_vadd_const := ?_ }
  · intro c
    exact (continuous_const.add continuous_id).measurable
  · intro x
    exact
      (continuous_subtype_val.add continuous_const).measurable

/-- Invariance of Lebesgue measure under translations by standard lattice vectors. -/
instance instVAddInvariantMeasure_standardLattice :
    MeasureTheory.VAddInvariantMeasure Λ E (volume : Measure E) where
  measure_preimage_vadd c s hs := by
    simp [Submodule.vadd_def, vadd_eq_add, MeasureTheory.measure_preimage_add]

/-- Translate the Schwartz function `f` by a lattice vector, as a continuous map. -/
noncomputable def translate (ℓ : Λ) : C(E, ℂ) :=
  (⟨(fun x => f x), f.continuous⟩ : C(E, ℂ)).comp (ContinuousMap.addRight (ℓ : E))

/-- Pointwise formula for `translate`. -/
@[simp] lemma translate_apply (ℓ : Λ) (x : E) :
    translate (d := d) f ℓ x = f (x + (ℓ : E)) := rfl

/-- Only finitely many standard lattice points lie in a closed ball of radius `r`. -/
lemma finite_norm_le_lattice (r : ℝ) :
    ( {ℓ : Λ | ‖(ℓ : E)‖ ≤ r} : Set _ ).Finite := by
  -- In a proper metric space, a bounded set intersects a discrete closed subgroup in a finite set.
  have : DiscreteTopology ((Λ).toAddSubgroup) := (inferInstance : DiscreteTopology Λ)
  have hfinE : Set.Finite (Metric.closedBall (0 : E) r ∩ ((Λ).toAddSubgroup : Set E)) :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall AddSubgroup.isClosed_of_discreteTopology
  let e : Λ ↪ E := ⟨fun ℓ => (ℓ : E), Subtype.coe_injective⟩
  have hfin_pre : (e ⁻¹' (Metric.closedBall (0 : E) r ∩ (Λ : Set E))).Finite := by
    exact Set.Finite.preimage_embedding e (by
      simpa [Submodule.coe_toAddSubgroup] using hfinE)
  have :
      (e ⁻¹' (Metric.closedBall (0 : E) r ∩ (Λ : Set E))) = {ℓ : Λ | ‖(ℓ : E)‖ ≤ r} := by
    ext ℓ
    simp [e, Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_zero]
  simpa [this] using hfin_pre

/--
Schwartz decay implies that the sup norms of translates, restricted to a compact set, are summable
over the standard lattice.
-/
lemma summable_norm_translate_restrict (K : TopologicalSpace.Compacts E) :
    Summable (fun ℓ : Λ => ‖(translate (d := d) f ℓ).restrict K‖) := by
  -- Choose a power larger than the rank.
  let k : ℕ := Module.finrank ℤ Λ + 1
  obtain ⟨C, hCpos, hC⟩ := f.decay k 0
  have hC' : ∀ x : E, ‖x‖ ^ k * ‖f x‖ ≤ C := by
    simpa [norm_iteratedFDeriv_zero] using hC
  -- Bound the compact set `K` by a closed ball with nonnegative radius.
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  let r0 : ℝ := max r 0
  have hrK0 : (K : Set E) ⊆ Metric.closedBall (0 : E) r0 := by
    have hr_le : r ≤ r0 := le_max_left r 0
    have hball : Metric.closedBall (0 : E) r ⊆ Metric.closedBall (0 : E) r0 :=
      Metric.closedBall_subset_closedBall hr_le
    exact fun x hx => hball (hrK hx)
  -- Outside the finite set of lattice points in `closedBall 0 (max (2*r0) 1)`, we have
  -- `‖ℓ‖ > 2*r0` and `‖ℓ‖ > 1`, so in particular `ℓ ≠ 0`.
  let R : ℝ := max (2 * r0) 1
  have hfin :
      ( {ℓ : Λ | ‖(ℓ : E)‖ ≤ R} : Set _ ).Finite :=
    finite_norm_le_lattice (d := d) (r := R)
  have h_event :
      ∀ᶠ ℓ : Λ in Filter.cofinite,
        ‖(translate (d := d) f ℓ).restrict K‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k) := by
    filter_upwards [hfin.eventually_cofinite_notMem] with ℓ hℓ
    have hRlt : R < ‖(ℓ : E)‖ := lt_of_not_ge (by simpa using hℓ)
    have hnorm_lt : 2 * r0 < ‖(ℓ : E)‖ := lt_of_le_of_lt (le_max_left _ _) hRlt
    have hnorm_pos : 0 < ‖(ℓ : E)‖ := lt_trans (by positivity) hRlt
    refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
    rintro ⟨x, hxK⟩
    have hxball : (x : E) ∈ Metric.closedBall (0 : E) r0 := hrK0 hxK
    have hxnorm : ‖(x : E)‖ ≤ r0 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_zero] using hxball
    -- Lower bound: `‖x + ℓ‖ ≥ ‖ℓ‖ / 2`.
    have hnorm_ge : (1 / 2 : ℝ) * ‖(ℓ : E)‖ ≤ ‖(x + (ℓ : E))‖ := by
      have hsub : ‖(ℓ : E)‖ - ‖(x : E)‖ ≤ ‖(ℓ : E) + x‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using (norm_sub_norm_le (ℓ : E) (-x))
      have hxlt : ‖(x : E)‖ < (1 / 2 : ℝ) * ‖(ℓ : E)‖ := by
        grind
      have : (1 / 2 : ℝ) * ‖(ℓ : E)‖ ≤ ‖(ℓ : E)‖ - ‖(x : E)‖ := by
        nlinarith [le_of_lt hxlt]
      have : (1 / 2 : ℝ) * ‖(ℓ : E)‖ ≤ ‖(ℓ : E) + x‖ := le_trans this hsub
      simpa [add_comm, add_left_comm, add_assoc] using this
    have hnorm_xℓ_pos : 0 < ‖(x + (ℓ : E))‖ :=
      (by positivity : 0 < (1 / 2 : ℝ) * ‖(ℓ : E)‖).trans_le hnorm_ge
    have hpow_pos : 0 < ‖(x + (ℓ : E))‖ ^ k := pow_pos hnorm_xℓ_pos _
    -- `‖f(x+ℓ)‖ ≤ C / ‖x+ℓ‖^k`
    have hdiv : ‖f (x + (ℓ : E))‖ ≤ C / (‖(x + (ℓ : E))‖ ^ k) :=
      (le_div_iff₀' hpow_pos).2 (hC' (x + (ℓ : E)))
    -- Compare `1 / ‖x+ℓ‖^k` with `2^k * ‖ℓ‖⁻¹^k`.
    have hpow_le : C / (‖(x + (ℓ : E))‖ ^ k) ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k) := by
      have hpow_ge : ((1 / 2 : ℝ) * ‖(ℓ : E)‖) ^ k ≤ ‖(x + (ℓ : E))‖ ^ k :=
        pow_le_pow_left₀ (by positivity) hnorm_ge _
      have hinv :
          (‖(x + (ℓ : E))‖ ^ k)⁻¹ ≤ (2 ^ k : ℝ) * (‖(ℓ : E)‖⁻¹ ^ k) := by
        have hapos : 0 < ((1 / 2 : ℝ) * ‖(ℓ : E)‖) ^ k := by
          exact pow_pos (mul_pos (by positivity) hnorm_pos) _
        have :
            (‖(x + (ℓ : E))‖ ^ k)⁻¹ ≤ (((1 / 2 : ℝ) * ‖(ℓ : E)‖) ^ k)⁻¹ := by
          simpa [one_div] using (one_div_le_one_div_of_le hapos hpow_ge)
        simpa [mul_assoc, mul_comm, inv_pow, mul_inv_rev, mul_pow] using this
      have := mul_le_mul_of_nonneg_left hinv (le_of_lt hCpos)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have : ‖f (x + (ℓ : E))‖ ≤ (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k) :=
      le_trans hdiv hpow_le
    exact this
  -- Summability of the comparison series.
  have hsum_pow : Summable (fun ℓ : Λ => (‖(ℓ : E)‖⁻¹ ^ k : ℝ)) := by
    simpa [k] using
      (ZLattice.summable_norm_pow_inv (L := Λ) (n := k) (Nat.lt_succ_self _))
  have hsum_bd :
      Summable (fun ℓ : Λ => (C * (2 ^ k : ℝ)) * (‖(ℓ : E)‖⁻¹ ^ k)) :=
    hsum_pow.mul_left (C * (2 ^ k : ℝ))
  -- Apply eventual domination.
  refine Summable.of_norm_bounded_eventually hsum_bd ?_
  filter_upwards [h_event] with ℓ hℓ
  simpa [Real.norm_of_nonneg (by positivity)] using hℓ

/-- Periodization of a Schwartz function along the standard lattice. -/
noncomputable def periodized : C(E, ℂ) :=
  ∑' ℓ : Λ, translate (d := d) f ℓ

/-- Pointwise formula for `periodized`. -/
lemma periodized_apply (x : E) :
    periodized (d := d) f x = ∑' ℓ : Λ, f (x + (ℓ : E)) := by
  have hsum := ContinuousMap.summable_of_locally_summable_norm
    (summable_norm_translate_restrict (d := d) f)
  simpa [periodized, translate_apply] using (ContinuousMap.tsum_apply hsum x).symm

@[simp] lemma periodized_vadd_eq (x : E) (ℓ₀ : Λ) :
    periodized (d := d) f (x + ℓ₀) = periodized (d := d) f x := by
  simpa [periodized_apply (d := d) f, add_assoc] using
    (Equiv.addLeft ℓ₀).tsum_eq fun ℓ => f (x + (ℓ : E))

/-- The quotient map `E = ℝ^d → (ℝ/ℤ)^d`, bundled as a continuous map. -/
noncomputable def coeFunEC : C(E, UnitAddTorus (Fin d)) :=
  ⟨PoissonSummation.Standard.coeFunE (d := d),
    PoissonSummation.Standard.continuous_coeFunE (d := d)⟩

/-- `coeFunEC` is a quotient map. -/
lemma isQuotientMap_coeFunEC : Topology.IsQuotientMap (coeFunEC (d := d)) := by
  let h := PoissonSummation.Standard.isOpenQuotientMap_coeFunE (d := d)
  simpa [coeFunEC] using h.isQuotientMap

/-- The periodization is invariant under lattice translates, so it factors through the torus. -/
lemma periodized_factorsThrough :
    Function.FactorsThrough (periodized (d := d) f) (coeFunEC (d := d)) := by
  intro x y hxy
  rcases PoissonSummation.Standard.exists_intVec_eq_sub_of_coeFunE_eq (d := d) (x := x) (y := y)
      (by simpa [coeFunEC] using hxy) with ⟨n, hn⟩
  have hx : x = y + SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg (fun t => t + y) hn
  simpa [hx] using
    (periodized_vadd_eq (d := d) (f := f) y
      ⟨SchwartzMap.PoissonSummation.Standard.intVec (d := d) n,
        SchwartzMap.PoissonSummation.Standard.intVec_mem_standardLattice (d := d) n⟩)

/--
The descended function on the torus `(ℝ/ℤ)^d`, obtained by quotient-lifting the periodization.
-/
noncomputable def descended : C(UnitAddTorus (Fin d), ℂ) :=
  Topology.IsQuotientMap.lift
    (hf := isQuotientMap_coeFunEC (d := d))
    (g := periodized (d := d) f)
    (periodized_factorsThrough (d := d) (f := f))

/-- Compatibility of `descended` with `coeFunE`: pulling back gives `periodized`. -/
lemma descended_comp (x : E) :
    descended (d := d) f (PoissonSummation.Standard.coeFunE (d := d) x) =
      periodized (d := d) f x := by
  have hcomp : (descended (d := d) f).comp (coeFunEC (d := d)) = periodized (d := d) f := by
    simp [descended]
  simpa [coeFunEC] using congrArg (fun g : C(E, ℂ) => g x) hcomp

/-- Evaluate `mFourier (-n)` after composing with `coeFunE`, in terms of an inner product. -/
lemma mFourier_neg_apply_coeFunE (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) =
      (𝐞 (-(inner ℝ x (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n))) : ℂ) := by
  -- Expand both sides as complex exponentials.
  simp [PoissonSummation.Standard.coeFunE, UnitAddTorus.mFourier_apply_coeFun_ofLp,
    Real.fourierChar_apply, SchwartzMap.PoissonSummation.Standard.intVec, PiLp.inner_apply,
    Finset.sum_neg_distrib, mul_assoc, mul_comm]

@[simp] lemma intVec_neg (n : Fin d → ℤ) :
    SchwartzMap.PoissonSummation.Standard.intVec (d := d) (-n) =
      -SchwartzMap.PoissonSummation.Standard.intVec (d := d) n := by
  ext i
  simp [SchwartzMap.PoissonSummation.Standard.intVec_apply]

lemma mFourier_apply_coeFunE (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier n (PoissonSummation.Standard.coeFunE (d := d) x) =
      (𝐞 (inner ℝ x (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)) : ℂ) := by
  -- Reduce to the `(-n)`-formula and simplify the signs.
  simpa [intVec_neg (d := d) (n := n), inner_neg_right, neg_neg] using
    (mFourier_neg_apply_coeFunE (d := d) (n := -n) (x := x))

/-- The same character evaluation as `mFourier_apply_coeFunE`, written with `Complex.exp`. -/
lemma mFourier_apply_coeFunE_exp (n : Fin d → ℤ) (x : E) :
    UnitAddTorus.mFourier n (PoissonSummation.Standard.coeFunE (d := d) x) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          ⟪x, SchwartzMap.PoissonSummation.Standard.intVec (d := d) n⟫_[ℝ]) := by
  have hinner :
      inner ℝ x (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) =
        RCLike.wInner (𝕜 := ℝ) 1 x.ofLp
          (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n).ofLp :=
    RCLike.inner_eq_wInner_one x (intVec n)
  simpa [Real.fourierChar_apply, mul_assoc, mul_comm, hinner] using
    (mFourier_apply_coeFunE (d := d) (n := n) (x := x))

/-- `mFourier (-n) ∘ coeFunE` is invariant under adding an element of the standard lattice. -/
lemma mFourier_neg_apply_coeFunE_add_standardLattice (n : Fin d → ℤ)
    (ℓ : Λ) (x : E) :
    UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) (x + (ℓ : E))) =
      UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) := by
  rcases
      PoissonSummation.Standard.exists_intVec_eq_of_mem_standardLattice (d := d) (x := (ℓ : E))
        ℓ.property with ⟨m, hm⟩
  simp [hm]

/-- The fundamental cube `iocCube` is contained in the closed ball of radius `sqrt d`. -/
lemma iocCube_subset_closedBall :
    SchwartzMap.PoissonSummation.Standard.iocCube (d := d) ⊆
      Metric.closedBall (0 : E) (Real.sqrt d) := by
  intro x hx
  have hsum : (∑ i : Fin d, ‖x i‖ ^ 2) ≤ (d : ℝ) := by
    have hterm : ∀ i : Fin d, ‖x i‖ ^ 2 ≤ (1 : ℝ) := by
      intro i
      have hi : x i ∈ Set.Ioc (0 : ℝ) 1 := hx i
      have hxle : ‖x i‖ ≤ (1 : ℝ) := by
        have hxnonneg : 0 ≤ x i := le_of_lt hi.1
        simpa [Real.norm_eq_abs, abs_of_nonneg hxnonneg] using hi.2
      simpa [pow_two] using mul_le_mul hxle hxle (norm_nonneg _) (by positivity)
    simpa using (Finset.sum_le_sum fun i _ => hterm i).trans_eq (by simp)
  simpa [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq] using (Real.sqrt_le_sqrt hsum)

/-- The fundamental cube `iocCube` has finite Lebesgue measure. -/
lemma volume_iocCube_lt_top :
    (volume : Measure E) (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) < ⊤ := by
  simpa using ((Metric.isBounded_closedBall (x := (0 : E)) (r := Real.sqrt d)).subset
    (iocCube_subset_closedBall (d := d))).measure_lt_top

/--
Integrability of `mFourier (-n) * translate` on the fundamental cube `iocCube`.

This is one of the analytic inputs needed to compute Fourier coefficients of the descended
periodization.
-/
lemma integrableOn_mFourier_mul_translate_iocCube (n : Fin d → ℤ)
    (ℓ : Λ) :
    IntegrableOn
        (fun x : E =>
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
            f (x + (ℓ : E)))
        (SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) (volume : Measure E) := by
  -- Bound by the sup norm on a compact closed ball containing the cube.
  let K : TopologicalSpace.Compacts E :=
    ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩
  have hK : SchwartzMap.PoissonSummation.Standard.iocCube (d := d) ⊆ (K : Set E) :=
    (iocCube_subset_closedBall (d := d))
  have hbound :
      ∀ x ∈ SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
            f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict K‖ := by
    intro x hx
    have hxK : x ∈ (K : Set E) := hK hx
    have hmFourier :
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ ≤ 1 := by
      simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
        (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
          (PoissonSummation.Standard.coeFunE (d := d) x))
    have hsup :
        ‖f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict K‖ := by
      exact
        (ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict K) ⟨x, hxK⟩)
    calc
      ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
            f (x + (ℓ : E))‖
          = ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ *
              ‖f (x + (ℓ : E))‖ := by simp
      _ ≤ 1 * ‖f (x + (ℓ : E))‖ := by gcongr
      _ = ‖f (x + (ℓ : E))‖ := by simp
      _ ≤ ‖(translate (d := d) f ℓ).restrict K‖ := hsup
  -- Conclude integrability on the cube using a boundedness criterion.
  refine Measure.integrableOn_of_bounded (μ := (volume : Measure E))
      (s := SchwartzMap.PoissonSummation.Standard.iocCube (d := d))
      (s_finite := (volume_iocCube_lt_top (d := d)).ne)
      ?_
      (M := ‖(translate (d := d) f ℓ).restrict K‖)
      ?_
  · -- measurability
    exact
      (((UnitAddTorus.mFourier (-n)).continuous.comp
            (PoissonSummation.Standard.continuous_coeFunE (d := d))).mul
          (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
  · -- boundedness (a.e. on the restricted measure)
    exact ae_restrict_of_forall_mem
      (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d)) hbound


end SchwartzMap.PoissonSummation.Standard


/-!
#### Fourier coefficients of the descended periodization

We compute the Fourier coefficient of the descended, periodized Schwartz function and identify it
with the Fourier transform of the original Schwartz function at integer frequencies.

Main result: `poissonSummation_standard`.
-/

open scoped BigOperators FourierTransform

open MeasureTheory

namespace SchwartzMap.PoissonSummation.Standard

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Λ" => SchwartzMap.standardLattice d

open _root_.SchwartzMap.UnitAddTorus

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))


noncomputable def ball : TopologicalSpace.Compacts E :=
  ⟨Metric.closedBall (0 : E) (Real.sqrt d), isCompact_closedBall (0 : E) (Real.sqrt d)⟩

lemma norm_mFourier_mul_translate_le (n : Fin d → ℤ) (ℓ : Λ)
    (x : E) (hx : x ∈ SchwartzMap.PoissonSummation.Standard.iocCube (d := d)) :
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
          f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
  have hxK : x ∈ (ball (d := d) : Set E) := (iocCube_subset_closedBall (d := d)) hx
  have hmFourier :
      ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ ≤ 1 := by
    simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
      (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
        (PoissonSummation.Standard.coeFunE (d := d) x))
  have hsup :
      ‖f (x + (ℓ : E))‖ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
    exact
      (ContinuousMap.norm_coe_le_norm ((translate (d := d) f ℓ).restrict (ball (d := d))) ⟨x, hxK⟩)
  calc
    ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
          f (x + (ℓ : E))‖
        = ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ *
            ‖f (x + (ℓ : E))‖ := by simp
    _ ≤ 1 * ‖f (x + (ℓ : E))‖ := by gcongr
    _ = ‖f (x + (ℓ : E))‖ := by simp
    _ ≤ ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := hsup

lemma summable_integral_norm_mFourier_mul_translate_iocCube (n : Fin d → ℤ) :
    Summable
        (fun ℓ : Λ =>
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂(volume : Measure E)) := by
  let s : Set E := SchwartzMap.PoissonSummation.Standard.iocCube (d := d)
  let μ : Measure E := (volume : Measure E).restrict s
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, s] using (volume_iocCube_lt_top (d := d))
  have hsum_norm :
      Summable (fun ℓ : Λ =>
        μ.real Set.univ * ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (summable_norm_translate_restrict (d := d) f (ball (d := d))).mul_left (μ.real Set.univ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ℓ => ?_) hsum_norm
  have hle_ae :
      (fun x : E =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E))‖) ≤ᵐ[μ] fun _ : E =>
        ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
    refine ae_restrict_of_forall_mem
      (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d)) ?_
    intro x hx
    exact norm_mFourier_mul_translate_le (d := d) (f := f) n ℓ x hx
  have hnonneg :
      (0 : E → ℝ) ≤ᵐ[μ] fun x : E =>
        ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E))‖ :=
    ae_of_all _ (fun _ => by positivity)
  have hle' :
      (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E))‖ ∂μ) ≤
        μ.real Set.univ * ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ := by
    -- Bound by the integral of a constant function.
    have hle :
        (∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂μ) ≤
          ∫ x, ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖ ∂μ :=
      integral_mono_of_nonneg hnonneg
        (integrable_const ‖(translate (d := d) f ℓ).restrict (ball (d := d))‖) hle_ae
    simpa [MeasureTheory.integral_const (μ := μ), smul_eq_mul, mul_comm] using hle
  -- Convert back to `∫ x in s, ...`.
  simpa [μ, s, mul_comm, mul_left_comm, mul_assoc] using hle'

lemma mFourierCoeff_descended (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n =
      𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) := by
  -- Pull back Haar integration on the torus to the cube in `E`.
  have hmeas :
      AEStronglyMeasurable
          (fun y : UnitAddTorus (Fin d) =>
            UnitAddTorus.mFourier (-n) y • (descended (d := d) f y))
          (volume : Measure (UnitAddTorus (Fin d))) :=
    ((UnitAddTorus.mFourier (-n)).continuous.smul (descended (d := d) f).continuous)
      |> fun h => h.aestronglyMeasurable
  have hpull :
      (∫ y : UnitAddTorus (Fin d),
            UnitAddTorus.mFourier (-n) y • (descended (d := d) f y)) =
        ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) •
            (descended (d := d) f (PoissonSummation.Standard.coeFunE (d := d) x))
            ∂(volume : Measure E) := integral_eq_integral_preimage_coeFunE
              (fun y => (UnitAddTorus.mFourier (-n)) y • (descended f) y) hmeas
  -- Expand `descended` back to the periodization on `E`, and swap `tsum` and integral.
  have hsum_int :
      (∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E)) =
        ∑' ℓ : Λ,
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
    let s : Set E := SchwartzMap.PoissonSummation.Standard.iocCube (d := d)
    have hInt :
        ∀ ℓ : Λ,
          Integrable
              (fun x : E =>
                UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                  f (x + (ℓ : E)))
              ((volume : Measure E).restrict s) := by
      intro ℓ
      simpa [IntegrableOn, s] using
        (integrableOn_mFourier_mul_translate_iocCube (d := d) (f := f) n ℓ)
    have hSum :
        Summable (fun ℓ : Λ =>
          ∫ x, ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E))‖ ∂((volume : Measure E).restrict s)) := by
      -- This is the required absolute convergence to justify Fubini.
      simpa [s] using
        (summable_integral_norm_mFourier_mul_translate_iocCube (d := d) (f := f) n)
    have :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm
          (μ := (volume : Measure E).restrict s)
          (F := fun ℓ : Λ =>
            fun x : E =>
              UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E)))
          hInt hSum)
    -- `integral_tsum_of_summable_integral_norm` gives `tsum (∫...) = ∫ (tsum ...)`; rearrange.
    simpa [s, tsum_mul_left, mul_assoc] using this.symm
  -- Identify the sum of integrals with the integral over the whole space using the cube
  -- as a fundamental domain, exploiting periodicity of the kernel factor.
  have hFD :=
    (PoissonSummation.Standard.isAddFundamentalDomain_iocCube (d := d))
  have hint :
      Integrable
          (fun x : E =>
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x)
          (volume : Measure E) := by
    have hf : Integrable (fun x : E => f x) (volume : Measure E) :=
      SchwartzMap.integrable (μ := (volume : Measure E)) f
    have hmeas :
        AEStronglyMeasurable
            (fun x : E =>
              UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x))
            (volume : Measure E) :=
      ((UnitAddTorus.mFourier (-n)).continuous.comp
        (PoissonSummation.Standard.continuous_coeFunE (d := d))).aestronglyMeasurable
    have hbound :
        ∀ᵐ x : E ∂(volume : Measure E),
          ‖UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x)‖ ≤ (1 : ℝ) :=
      ae_of_all _ fun x => by
        simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := -n)] using
          (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-n))
            (PoissonSummation.Standard.coeFunE (d := d) x))
    simpa using (Integrable.bdd_mul (μ := (volume : Measure E)) hf hmeas hbound)
  have hFD' :
      ∑' ℓ : Λ,
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) =
        ∫ x : E,
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x
            ∂(volume : Measure E) := by
    -- Use `integral_eq_tsum''` for the fundamental domain on the integrable function
    -- `g x = mFourier(-n)(coeFunE x) * f x`, and rewrite each translate using periodicity.
    let g : E → ℂ :=
      fun x : E => UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x
    have hmain :
        (∫ x : E, g x ∂(volume : Measure E)) =
          ∑' ℓ : Λ,
            ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d), g (ℓ +ᵥ x)
              ∂(volume : Measure E) := by
      simpa [g] using
        (MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum'' (μ := (volume : Measure E))
          hFD (f := g) hint)
    -- Rewrite the integrand `g (ℓ +ᵥ x)` as `mFourier(-n)(x) * f(x+ℓ)`.
    have hterm :
        ∀ ℓ : Λ,
          (∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d), g (ℓ +ᵥ x)
              ∂(volume : Measure E)) =
            ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
              UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
                f (x + (ℓ : E)) ∂(volume : Measure E) := by
      intro ℓ
      refine integral_congr_ae ?_
      refine ae_restrict_of_forall_mem
        (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d)) ?_
      intro x hx
      have hper' :
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) (x + (ℓ : E))) =
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) := by
        simpa using
          (mFourier_neg_apply_coeFunE_add_standardLattice (d := d) (n := n) (ℓ := ℓ) (x := x))
      calc
        g (ℓ +ᵥ x) =
            UnitAddTorus.mFourier (-n)
                (PoissonSummation.Standard.coeFunE (d := d) ((ℓ : E) + x)) *
              f ((ℓ : E) + x) := by
          simp [g, Submodule.vadd_def, vadd_eq_add]
        _ =
            UnitAddTorus.mFourier (-n)
                (PoissonSummation.Standard.coeFunE (d := d) (x + (ℓ : E))) *
              f (x + (ℓ : E)) := by
          simp [add_comm]
        _ =
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) := by
          simp [hper']
    -- Combine.
    have hmain' := hmain.symm
    -- Replace the `tsum` termwise using `hterm`.
    simpa [g, hterm] using hmain'
  -- Put everything together and recognize the Fourier integral.
  calc
    UnitAddTorus.mFourierCoeff (descended (d := d) f) n
        = ∫ y : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-n) y • descended (d := d) f y := by
            -- The Fourier-theory `mFourierCoeff` in Mathlib is defined using the probability Haar
            -- measure on `UnitAddCircle`, while this project works with the standard measure on
            -- `AddCircle 1`. These coincide as measures, but are not definitional equal as
            -- `MeasureSpace` instances, so we bridge them via equality of the induced `volume`s.
            simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
            have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
            have hμ_circle :
                (@volume UnitAddCircle instMeasureSpaceUnitAddCircle) =
                  (@volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ))) := by
              change (AddCircle.haarAddCircle (T := (1 : ℝ)) : Measure UnitAddCircle) =
                (@volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ)))
              simp [UnitAddCircle, AddCircle.volume_eq_smul_haarAddCircle]
            have hμ_torus :
                (@volume (UnitAddTorus (Fin d))
                    (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                      (fun _ => instMeasureSpaceUnitAddCircle))) =
                  (@volume (UnitAddTorus (Fin d))
                    (@MeasureSpace.pi (Fin d) (Fin.fintype d) (fun _ => UnitAddCircle)
                      (fun _ => AddCircle.measureSpace (1 : ℝ)))) := by
              -- Unfold `volume` on a finite product and rewrite each component by `hμ_circle`.
              change
                Measure.pi (fun _ : Fin d => @volume UnitAddCircle instMeasureSpaceUnitAddCircle) =
                  Measure.pi
                    (fun _ : Fin d =>
                      @volume UnitAddCircle (AddCircle.measureSpace (1 : ℝ)))
              exact congrArg Measure.pi (funext fun _ => hμ_circle)
            -- Rewrite the measure on the LHS; the remaining goal is definitional.
            simp [hμ_torus]
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) •
            descended (d := d) f (PoissonSummation.Standard.coeFunE (d := d) x)
            ∂(volume : Measure E) := by
          simpa using hpull
    _ = ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
            (∑' ℓ : Λ, f (x + (ℓ : E))) ∂(volume : Measure E) := by
          -- `ℂ`-scalar multiplication is multiplication.
          refine integral_congr_ae ?_
          refine ae_restrict_of_forall_mem
            (SchwartzMap.PoissonSummation.Standard.measurableSet_iocCube (d := d)) ?_
          intro x hx
          simp [descended_comp (d := d) (f := f), periodized_apply (d := d) (f := f),
            smul_eq_mul]
    _ = ∑' ℓ : Λ,
          ∫ x in SchwartzMap.PoissonSummation.Standard.iocCube (d := d),
            UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) *
              f (x + (ℓ : E)) ∂(volume : Measure E) := by
          simpa using hsum_int
    _ = ∫ x : E,
          UnitAddTorus.mFourier (-n) (PoissonSummation.Standard.coeFunE (d := d) x) * f x
            ∂(volume : Measure E) := by
          simpa using hFD'
    _ = 𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n) := by
          -- Unfold the Fourier transform integral and identify the phase factor.
          simp [Real.fourier_eq, Circle.smul_def, smul_eq_mul,
            mFourier_neg_apply_coeFunE (d := d) (n := n)]

lemma summable_mFourierCoeff_descended :
    Summable (UnitAddTorus.mFourierCoeff (descended (d := d) f)) := by
  -- Reduce to summability of the Fourier transform on integer frequencies, using Schwartz decay.
  have hsum_norm :
      Summable (fun n : Fin d → ℤ =>
        ‖𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)‖) := by
    -- Prove absolute summability over the standard lattice and reindex by `intVec`.
    let k : ℕ := d + 1
    have hk : Module.finrank ℤ Λ < k := by
      have hrank : Module.finrank ℤ Λ = d := by
        have h := (ZLattice.rank (K := ℝ) (L := Λ))
        simpa using (h.trans (by simp))
      simp [hrank, k]
    -- Use decay of the Fourier transform (which is again a Schwartz function).
    obtain ⟨C, hCpos, hC⟩ := (FourierTransform.fourierCLE ℂ (SchwartzMap E ℂ) f).decay k 0
    have hC' : ∀ x : E, ‖x‖ ^ k * ‖𝓕 (fun y : E => f y) x‖ ≤ C := by
      simpa [FourierTransform.fourierCLE_apply, fourier_coe, norm_iteratedFDeriv_zero] using hC
    have hsum_pow :
        Summable (fun ℓ : Λ => (‖(ℓ : E)‖⁻¹ ^ k : ℝ)) := by
      simpa [k] using (ZLattice.summable_norm_pow_inv (L := Λ) (n := k) hk)
    have hsum_bd : Summable (fun ℓ : Λ => (C : ℝ) * (‖(ℓ : E)‖⁻¹ ^ k)) :=
      hsum_pow.mul_left C
    have hsum_lattice : Summable (fun ℓ : Λ => ‖𝓕 (fun y : E => f y) (ℓ : E)‖) := by
      -- Control the tail using the decay estimate (away from the finite set `‖ℓ‖ ≤ 1`).
      have hfin : ({ℓ : Λ | ‖(ℓ : E)‖ ≤ (1 : ℝ)} : Set _).Finite :=
        finite_norm_le_lattice (d := d) 1
      refine Summable.of_norm_bounded_eventually hsum_bd ?_
      filter_upwards [hfin.compl_mem_cofinite] with ℓ hℓ
      have hnorm_gt : (1 : ℝ) < ‖(ℓ : E)‖ := lt_of_not_ge (by simpa using hℓ)
      have hnorm_pos : 0 < ‖(ℓ : E)‖ := lt_trans (by positivity) hnorm_gt
      have hpow_pos : 0 < ‖(ℓ : E)‖ ^ k := pow_pos hnorm_pos _
      have hmain := hC' (ℓ : E)
      have : ‖𝓕 (fun y : E => f y) (ℓ : E)‖ ≤ C / (‖(ℓ : E)‖ ^ k) :=
        (le_div_iff₀' hpow_pos).2 hmain
      have hdiv :
          ‖𝓕 (fun y : E => f y) (ℓ : E)‖ ≤ (C : ℝ) * (‖(ℓ : E)‖⁻¹ ^ k) := by
        simpa [div_eq_mul_inv, inv_pow, one_div] using this
      -- Convert `‖‖z‖‖` to `‖z‖` (as a real number).
      simpa [Real.norm_of_nonneg (norm_nonneg _)] using hdiv
    -- Reindex from the standard lattice to integer vectors using `equivIntVec`.
    let e := (PoissonSummation.Standard.equivIntVec (d := d))
    have : Summable (fun n : Fin d → ℤ => ‖𝓕 (fun y : E => f y) ((e n : Λ) : E)‖) := by
      exact (Summable.comp_injective (f := fun ℓ : Λ => ‖𝓕 (fun y : E => f y) (ℓ : E)‖)
        (i := e) hsum_lattice e.injective)
    exact this
  -- Convert from absolute summability to summability in `ℂ`, using the coefficient identity.
  refine (Summable.of_norm ?_)
  simpa [mFourierCoeff_descended (d := d) (f := f)] using hsum_norm

/-- Poisson summation for Schwartz functions over the standard lattice `ℤ^d`. -/
theorem poissonSummation_standard (v : E) :
    (∑' ℓ : Λ, f (v + (ℓ : E))) =
      ∑' n : Fin d → ℤ,
        (𝓕 (fun x : E => f x) (SchwartzMap.PoissonSummation.Standard.intVec (d := d) n)) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              ⟪v, SchwartzMap.PoissonSummation.Standard.intVec (d := d) n⟫_[ℝ]) := by
  simpa [descended_comp (d := d) (f := f) v, periodized_apply (d := d) (f := f), smul_eq_mul,
    mFourierCoeff_descended (d := d) (f := f), mFourier_apply_coeFunE_exp (d := d), mul_assoc,
    mul_left_comm, mul_comm] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
        (f := descended (d := d) f)
        (summable_mFourierCoeff_descended (d := d) (f := f))
        (coeFunE (d := d) v)).tsum_eq.symm

end SchwartzMap.PoissonSummation.Standard


/-!
# Fourier linear equivalences

This file proves results such as `fourier_comp_linearEquiv`.
-/

namespace ExpandedFA.PartIV.FourierChange

open scoped FourierTransform
open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Change-of-variables formula for the Fourier transform under an invertible linear map.

For `A : V ≃ₗ[ℝ] V`, we have
`𝓕 (f ∘ A) w = |det A|⁻¹ • 𝓕 f ((A.symm).adjoint w)`.
-/
theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
        𝓕 f (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w) := by
  simp only [Real.fourier_eq]
  have hmap :
      Measure.map (⇑A) (volume : Measure V) =
        ENNReal.ofReal |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| • (volume : Measure V) := by
    simpa using
      (Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure V))
        (LinearEquiv.isUnit_det' A).ne_zero)
  let g : V → ℂ := fun y ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y
  have hsub :
      (∫ x : V, Real.fourierChar (-(inner ℝ x w)) • f (A x)) =
        ∫ y : V, g y ∂Measure.map (⇑A) (volume : Measure V) := by
    let e : V ≃ᵐ V := A.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
    simpa [g, e] using (MeasureTheory.integral_map_equiv (μ := (volume : Measure V)) e g).symm
  have hscale :
      (∫ y : V, g y ∂Measure.map (⇑A) (volume : Measure V)) =
        (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ • ∫ y : V, g y := by
    rw [hmap, MeasureTheory.integral_smul_measure]
    simp [abs_inv]
  have hadj :
      (fun y : V ↦ Real.fourierChar (-(inner ℝ (A.symm y) w)) • f y) =
        fun y : V ↦
          Real.fourierChar (-(inner ℝ y (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w))) • f y := by
    funext y
    simp [LinearMap.adjoint_inner_right]
  calc
    (∫ x : V, Real.fourierChar (-(inner ℝ x w)) • f (A x)) =
        ∫ y : V, g y ∂Measure.map (⇑A) (volume : Measure V) := hsub
    _ = (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ • ∫ y : V, g y := hscale
    _ = (abs (LinearMap.det (A : V →ₗ[ℝ] V)))⁻¹ •
          ∫ y : V,
            Real.fourierChar (-(inner ℝ y (((A.symm : V ≃ₗ[ℝ] V).toLinearMap).adjoint w))) •
              f y := by
          simp [g, hadj]

end ExpandedFA.PartIV.FourierChange
namespace ExpandedFA.PartIV.PoissonSummation
open ExpandedFA.Fourier
open scoped FourierTransform SchwartzMap
open SchwartzMap.PoissonSummation.Standard

/-- Schwartz decay makes restriction to the integer lattice absolutely summable. -/
theorem summable_integerPoint {d : ℕ} (f : Schwartz ℂ d) :
    Summable (fun n : Fin d → ℤ => ‖f (integerPoint n)‖) := by
  have h := (summable_mFourierCoeff_descended (𝓕⁻ f)).norm
  simpa only [mFourierCoeff_descended, ← SchwartzMap.fourier_coe,
    FourierTransform.fourier_fourierInv_eq, integerPoint, intVec] using h

theorem standard_formula : Specs.ExpandedFA.PartIV.PoissonSummation.StandardFormula := by
  intro d f
  refine ⟨summable_integerPoint f, summable_integerPoint (schwartzFourier f), ?_⟩
  have h := poissonSummation_standard f (0 : Euclidean d)
  have he := (equivIntVec (d := d)).tsum_eq (fun ℓ => f (ℓ : Euclidean d))
  simpa only [zero_add, WithLp.ofLp_zero, inner_zero_left, RCLike.wInner_zero_left, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, ← he, coe_equivIntVec, integerPoint, intVec,
    schwartzFourier, FourierTransform.fourierCLM_apply, SchwartzMap.fourier_coe] using h

end ExpandedFA.PartIV.PoissonSummation

namespace ExpandedFA.PartIV.PoissonSummation
open ExpandedFA.Fourier
open scoped FourierTransform SchwartzMap

noncomputable def matrixEquiv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) : Euclidean d ≃ₗ[ℝ] Euclidean d :=
  A.toLinearEquiv (EuclideanSpace.basisFun (Fin d) ℝ).toBasis (isUnit_iff_ne_zero.mpr hA)

@[simp] theorem matrixEquiv_apply {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) (x : Euclidean d) : matrixEquiv A hA x = matrixAction A x := rfl

@[simp] theorem matrixEquiv_det {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) : LinearMap.det (matrixEquiv A hA).toLinearMap = A.det :=
  LinearMap.det_toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis A

@[simp] theorem matrixEquiv_inverse_adjoint {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.det ≠ 0) (x : Euclidean d) :
    (matrixEquiv A hA).symm.toLinearMap.adjoint x =
      matrixAction A⁻¹.transpose x := by
  have h : (matrixEquiv A hA).symm.toLinearMap = A⁻¹.toEuclideanLin := rfl
  rw [h, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have ht : A⁻¹.conjTranspose = A⁻¹.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [ht]
  rfl

/-- Absolute convergence after any invertible real matrix substitution. -/
theorem summable_matrix {d : ℕ} (f : Schwartz ℂ d)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.det ≠ 0) :
    Summable (fun n : Fin d → ℤ => ‖f (matrixAction A (integerPoint n))‖) := by
  exact summable_integerPoint
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (matrixEquiv A hA).toContinuousLinearEquiv f)

theorem lattice_formula : Specs.ExpandedFA.PartIV.PoissonSummation.LatticeFormula := by
  intro d f A hA
  have hdual : A⁻¹.transpose.det ≠ 0 := by simpa using inv_ne_zero hA
  refine ⟨summable_matrix f A hA, summable_matrix (schwartzFourier f) A⁻¹.transpose hdual, ?_⟩
  let g : Schwartz ℂ d :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (matrixEquiv A hA).toContinuousLinearEquiv f
  have hF (n : Fin d → ℤ) : schwartzFourier g (integerPoint n) =
      |A.det|⁻¹ • schwartzFourier f (matrixAction A⁻¹.transpose (integerPoint n)) := by
    have h := FourierChange.fourier_comp_linearEquiv (matrixEquiv A hA) f (integerPoint n)
    change 𝓕 (fun x => f (matrixEquiv A hA x)) (integerPoint n) =
      |A.det|⁻¹ • 𝓕 (f : Euclidean d → ℂ)
        (matrixAction A⁻¹.transpose (integerPoint n))
    rw [matrixEquiv_det, matrixEquiv_inverse_adjoint] at h
    exact h
  calc
    (∑' n : Fin d → ℤ, f (matrixAction A (integerPoint n))) =
        ∑' n : Fin d → ℤ, schwartzFourier g (integerPoint n) := (standard_formula d g).2.2
    _ = ∑' n : Fin d → ℤ,
        |A.det|⁻¹ • schwartzFourier f (matrixAction A⁻¹.transpose (integerPoint n)) :=
      tsum_congr hF
    _ = _ := tsum_const_smul'' _

end ExpandedFA.PartIV.PoissonSummation
