import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OAlgebra
import Mathlib.Analysis.Asymptotics.Ring

/-!
# Calculus of error bounds

K03.02.o_algebra, paper.tex:449–456. All estimates use the same filter,
which fixes the common domain and approach. The upstream bridges identify
the source inequality definitions with Mathlib's asymptotic relations.
The mixed transitivity and multiplication rules also cover two little-o
estimates, using `scalarLittleO_isBigO` on either one.

Comparison functions may vanish. For division, the eventual nonzero divisor
has positive norm, so the original pointwise inequality can be divided by it.
-/

namespace SingleVariableAnalysis

open Filter
universe u v

variable {X : Type u} {K : Type v} [NormedField K]

theorem scalarBigO_trans (l : Filter X) (f g h : X → K)
    (hfg : ScalarBigO l f g) (hgh : ScalarBigO l g h) : ScalarBigO l f h := by
  apply (scalarBigO_iff_isBigO l f h).mpr
  exact ((scalarBigO_iff_isBigO l f g).mp hfg).trans
    ((scalarBigO_iff_isBigO l g h).mp hgh)

theorem scalarLittleO_trans_bigO (l : Filter X) (f g h : X → K)
    (hfg : ScalarLittleO l f g) (hgh : ScalarBigO l g h) : ScalarLittleO l f h := by
  apply (scalarLittleO_iff_isLittleO l f h).mpr
  exact ((scalarLittleO_iff_isLittleO l f g).mp hfg).trans_isBigO
    ((scalarBigO_iff_isBigO l g h).mp hgh)

theorem scalarBigO_trans_littleO (l : Filter X) (f g h : X → K)
    (hfg : ScalarBigO l f g) (hgh : ScalarLittleO l g h) : ScalarLittleO l f h := by
  apply (scalarLittleO_iff_isLittleO l f h).mpr
  exact ((scalarBigO_iff_isBigO l f g).mp hfg).trans_isLittleO
    ((scalarLittleO_iff_isLittleO l g h).mp hgh)

theorem scalarBigO_add (l : Filter X) (f u g : X → K)
    (hf : ScalarBigO l f g) (hu : ScalarBigO l u g) :
    ScalarBigO l (fun x => f x + u x) g := by
  apply (scalarBigO_iff_isBigO l _ g).mpr
  exact ((scalarBigO_iff_isBigO l f g).mp hf).add
    ((scalarBigO_iff_isBigO l u g).mp hu)

theorem scalarLittleO_add (l : Filter X) (f u g : X → K)
    (hf : ScalarLittleO l f g) (hu : ScalarLittleO l u g) :
    ScalarLittleO l (fun x => f x + u x) g := by
  apply (scalarLittleO_iff_isLittleO l _ g).mpr
  exact ((scalarLittleO_iff_isLittleO l f g).mp hf).add
    ((scalarLittleO_iff_isLittleO l u g).mp hu)

theorem scalarBigO_mul (l : Filter X) (f g u v : X → K)
    (hf : ScalarBigO l f g) (hu : ScalarBigO l u v) :
    ScalarBigO l (fun x => f x * u x) (fun x => g x * v x) := by
  apply (scalarBigO_iff_isBigO l _ _).mpr
  exact ((scalarBigO_iff_isBigO l f g).mp hf).mul
    ((scalarBigO_iff_isBigO l u v).mp hu)

theorem scalarLittleO_mul_bigO (l : Filter X) (f g u v : X → K)
    (hf : ScalarLittleO l f g) (hu : ScalarBigO l u v) :
    ScalarLittleO l (fun x => f x * u x) (fun x => g x * v x) := by
  apply (scalarLittleO_iff_isLittleO l _ _).mpr
  exact ((scalarLittleO_iff_isLittleO l f g).mp hf).mul_isBigO
    ((scalarBigO_iff_isBigO l u v).mp hu)

theorem scalarBigO_mul_littleO (l : Filter X) (f g u v : X → K)
    (hf : ScalarBigO l f g) (hu : ScalarLittleO l u v) :
    ScalarLittleO l (fun x => f x * u x) (fun x => g x * v x) := by
  apply (scalarLittleO_iff_isLittleO l _ _).mpr
  exact ((scalarBigO_iff_isBigO l f g).mp hf).mul_isLittleO
    ((scalarLittleO_iff_isLittleO l u v).mp hu)

theorem scalarBigO_const_mul (l : Filter X) (f g : X → K) (c : K)
    (hf : ScalarBigO l f g) : ScalarBigO l (fun x => c * f x) g := by
  apply (scalarBigO_iff_isBigO l _ g).mpr
  exact ((scalarBigO_iff_isBigO l f g).mp hf).const_mul_left c

theorem scalarLittleO_const_mul (l : Filter X) (f g : X → K) (c : K)
    (hf : ScalarLittleO l f g) : ScalarLittleO l (fun x => c * f x) g := by
  apply (scalarLittleO_iff_isLittleO l _ g).mpr
  exact ((scalarLittleO_iff_isLittleO l f g).mp hf).const_mul_left c

theorem scalarBigO_div (l : Filter X) (f g v : X → K)
    (hv : ∀ᶠ x in l, v x ≠ 0) (hf : ScalarBigO l f g) :
    ScalarBigO l (fun x => f x / v x) (fun x => g x / v x) := by
  obtain ⟨C, hC, h⟩ := hf
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, hv] with x hx hne
  rw [norm_div, norm_div, ← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hne)).mpr hx

theorem scalarLittleO_div (l : Filter X) (f g v : X → K)
    (hv : ∀ᶠ x in l, v x ≠ 0) (hf : ScalarLittleO l f g) :
    ScalarLittleO l (fun x => f x / v x) (fun x => g x / v x) := by
  intro ε hε
  filter_upwards [hf ε hε, hv] with x hx hne
  rw [norm_div, norm_div, ← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hne)).mpr hx

end SingleVariableAnalysis
