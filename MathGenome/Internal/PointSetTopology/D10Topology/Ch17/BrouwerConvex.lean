import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch17.BrouwerConvex
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.BrouwerSimplex
import MathGenome.Internal.PointSetTopology.D10Topology.Ch17.MetricProjection
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Finite-dimensional Brouwer (paper.tex, d10:17:brouwer-convex).
We explicitly encode a bounded set into a standard simplex. Decoding is a
continuous affine left inverse of encoding. Composing decoding with the proved
metric projection makes the convex set a retract of the simplex. This works
also in dimension zero and for sets of lower affine dimension.
The final theorem transports this result through a continuous linear coordinate
equivalence, whose inverse is continuous by finite dimensionality. -/
noncomputable section
open Set
open scoped BigOperators
namespace D10Topology.Ch17
namespace BrouwerConvex

/-- Denominator for the affine embedding into barycentric coordinates. -/
def scale (m : ℕ) (R : ℝ) : ℝ := 2 * R * (m + 1)

theorem scale_pos (m : ℕ) {R : ℝ} (hR : 0 < R) : 0 < scale m R := by
  unfold scale
  positivity

/-- The first coordinate is the unused mass; the others encode the point. -/
def encode {m : ℕ} (R : ℝ) (x : Euclidean m) : Euclidean (m + 1) :=
  WithLp.toLp 2 (Fin.cons
    (1 - ∑ i, (x i + R) / scale m R)
    (fun i => (x i + R) / scale m R))

/-- Affine decoding is defined on the entire ambient barycentric space. -/
def decode {m : ℕ} (R : ℝ) (t : Euclidean (m + 1)) : Euclidean m :=
  WithLp.toLp 2 (fun i => scale m R * t i.succ - R)

theorem decode_encode {m : ℕ} {R : ℝ} (hR : 0 < R) (x : Euclidean m) :
    decode R (encode R x) = x := by
  apply PiLp.ext
  intro i
  change scale m R * ((x i + R) / scale m R) - R = x i
  field_simp [ne_of_gt (scale_pos m hR)]
  ring

theorem continuous_encode {m : ℕ} (R : ℝ) : Continuous (@encode m R) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i using Fin.cases with
  | zero =>
    exact continuous_const.sub (continuous_finsetSum _ (fun j _ =>
      ((EuclideanSpace.proj j).continuous.add continuous_const).div_const _))
  | succ i =>
    exact ((EuclideanSpace.proj i).continuous.add continuous_const).div_const _

theorem continuous_decode {m : ℕ} (R : ℝ) : Continuous (@decode m R) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact (continuous_const.mul (EuclideanSpace.proj i.succ).continuous).sub continuous_const

theorem encode_mem_simplex {m : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Euclidean m} (hx : ∀ i, |x i| ≤ R) : encode R x ∈ standardSimplex m := by
  have hD := scale_pos m hR
  have hsum : (∑ i, (x i + R) / scale m R) ≤ 1 := by
    rw [← Finset.sum_div]
    apply (div_le_one hD).mpr
    calc
      ∑ i, (x i + R) ≤ ∑ _i : Fin m, (2 * R) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (abs_le.mp (hx i)).2
        linarith
      _ ≤ scale m R := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold scale
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
  constructor
  · intro i
    cases i using Fin.cases with
    | zero => exact sub_nonneg.mpr hsum
    | succ i =>
      change 0 ≤ (x i + R) / scale m R
      exact div_nonneg (by have := (abs_le.mp (hx i)).1; linarith) hD.le
  · change (∑ i : Fin (m + 1), (Fin.cons
      (1 - ∑ i, (x i + R) / scale m R)
      (fun i => (x i + R) / scale m R)) i) = 1
    rw [Fin.sum_univ_succ]
    simp

/-- Fixed-point existence passes to continuous retracts of the simplex. -/
theorem fixedPoint_of_retract {m : ℕ} {X : Type*} [TopologicalSpace X]
    (a : X → standardSimplex m) (b : standardSimplex m → X)
    (ha : Continuous a) (hb : Continuous b) (hba : Function.LeftInverse b a)
    (f : X → X) (hf : Continuous f) : ∃ x, f x = x := by
  obtain ⟨t, ht⟩ := brouwer_simplex m (a ∘ f ∘ b) (ha.comp (hf.comp hb))
  refine ⟨b t, ?_⟩
  calc
    f (b t) = b (a (f (b t))) := (hba _).symm
    _ = b t := congrArg b ht

end BrouwerConvex

/-- Every continuous self-map of a nonempty compact convex Euclidean set has
a fixed point, in every natural dimension. -/
theorem brouwer_euclidean : Specs.D10Topology.Ch17.BrouwerConvex.brouwer_euclidean := by
  intro m K hne hK hconv f hf
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  have hcoord (x : K) (i : Fin m) : |(x : Euclidean m) i| ≤ R := by
    calc
      |(x : Euclidean m) i| = ‖(x : Euclidean m) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(x : Euclidean m)‖ := PiLp.norm_apply_le (p := 2) x.val i
      _ ≤ R := hbound x x.property
  let a : K → standardSimplex m := fun x =>
    ⟨BrouwerConvex.encode R x, BrouwerConvex.encode_mem_simplex hR (hcoord x)⟩
  let b : standardSimplex m → K := fun t =>
    projection K hK hne (BrouwerConvex.decode R t)
  apply BrouwerConvex.fixedPoint_of_retract a b ?_ ?_ ?_ f hf
  · exact ((BrouwerConvex.continuous_encode R).comp continuous_subtype_val).subtype_mk _
  · exact (projection_continuous_retraction K hK hne hconv).1.comp
      ((BrouwerConvex.continuous_decode R).comp continuous_subtype_val)
  · intro x
    change projection K hK hne (BrouwerConvex.decode R (BrouwerConvex.encode R x)) = x
    rw [BrouwerConvex.decode_encode hR]
    exact projection_fixes K hK hne hconv x

universe u

/-- Brouwer for every finite-dimensional real normed space, with its given
norm topology. Linear coordinates and their inverse are continuous. -/
theorem brouwer_finiteDimensional :
    Specs.D10Topology.Ch17.BrouwerConvex.brouwer_finiteDimensional.{u} := by
  intro V _ _ _ K hne hK hconv f hf
  let m := Module.finrank ℝ V
  let e : V ≃L[ℝ] Euclidean m :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let L : Set (Euclidean m) := e '' K
  have hLne : L.Nonempty := hne.image e
  have hLc : IsCompact L := hK.image e.continuous
  have hLv : Convex ℝ L := hconv.linear_image e.toLinearMap
  let h : K ≃ₜ L := e.toHomeomorph.image K
  let g : L → L := h ∘ f ∘ h.symm
  have hg : Continuous g := h.continuous.comp (hf.comp h.symm.continuous)
  obtain ⟨y, hy⟩ := brouwer_euclidean m L hLne hLc hLv g hg
  refine ⟨h.symm y, ?_⟩
  have heq := congrArg h.symm hy
  simpa only [g, Function.comp_apply, Homeomorph.symm_apply_apply] using heq

end D10Topology.Ch17
