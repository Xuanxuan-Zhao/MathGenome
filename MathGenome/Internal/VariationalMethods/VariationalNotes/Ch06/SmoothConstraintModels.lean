import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SmoothConstraintModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolyhedralTangentNormal
import Mathlib.Tactic.Linarith

noncomputable section
universe u v w
namespace VariationalNotes.Ch06

def SmoothConstraintData : Specs.SmoothConstraintDataType := @Specs.SmoothConstraintData

def feasibleSet : Specs.feasibleSetType := @Specs.feasibleSet

def activeSet : Specs.activeSetType := @Specs.activeSet

def equalityDerivative : Specs.equalityDerivativeType := @Specs.equalityDerivative

def linearizedCone : Specs.linearizedConeType := @Specs.linearizedCone

def constraintTangentCone : Specs.constraintTangentConeType := @Specs.constraintTangentCone

def LICQ : Specs.LICQType := @Specs.LICQ

def MFCQ : Specs.MFCQType := @Specs.MFCQ

def KKT : Specs.KKTType := @Specs.KKT

def FritzJohn : Specs.FritzJohnType := @Specs.FritzJohn

def lagrangian : Specs.lagrangianType := @Specs.lagrangian

def criticalCone : Specs.criticalConeType := @Specs.criticalCone

theorem smoothConstraintData_hasFDerivAt : Specs.smoothConstraintData_hasFDerivAt.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x hs hx
  exact ⟨hs.2.1.differentiableOn_one.hasFDerivAt (hs.1.mem_nhds hx),
    (fun i => (hs.2.2.1 i).differentiableOn_one.hasFDerivAt (hs.1.mem_nhds hx)),
    (fun j => (hs.2.2.2 j).differentiableOn_one.hasFDerivAt (hs.1.mem_nhds hx))⟩

theorem equalityDerivative_hasFDerivAt : Specs.equalityDerivative_hasFDerivAt.{u,w} := by
  intro X _ _ J _ h x hd
  exact hasFDerivAt_pi.mpr (fun j => (hd j).hasFDerivAt)

theorem constraintTangentCone_eq : Specs.constraintTangentCone_eq.{u,v,w} := by
  intro X _ _ I J _ _ U g h x
  rfl

theorem kkt_inactive_multiplier : Specs.kkt_inactive_multiplier.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x lam nu hk i hi
  change g i x ≠ 0 at hi
  exact (mul_eq_zero.mp (hk.2.2.1 i)).resolve_right hi

/-- Evaluate stationarity on a linearized direction; all equality terms vanish. -/
private lemma kkt_linearized_full_sum
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    {U : Set X} {f : X → ℝ} {g : I → X → ℝ} {h : J → X → ℝ}
    {x : X} {lam : I → ℝ} {nu : J → ℝ}
    (hk : KKT U f g h x lam nu) {d : X} (hd : d ∈ linearizedCone g h x) :
    fderiv ℝ f x d = -(∑ i, lam i * fderiv ℝ (g i) x d) ∧
      ∀ i, lam i * fderiv ℝ (g i) x d ≤ 0 := by
  have heq (j : J) : fderiv ℝ (h j) x d = 0 := by
    exact congrFun hd.1 j
  have hs := congrArg (fun l : X →L[ℝ] ℝ => l d) hk.2.2.2
  simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at hs
  have hsum : (∑ j, nu j * fderiv ℝ (h j) x d) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [heq j, mul_zero]
  rw [hsum, add_zero] at hs
  refine ⟨by linarith only [hs], ?_⟩
  intro i
  by_cases hi : i ∈ activeSet g x
  · exact mul_nonpos_of_nonneg_of_nonpos (hk.2.1 i) (hd.2 i hi)
  · rw [kkt_inactive_multiplier U f g h x lam nu hk i hi, zero_mul]

theorem kkt_linearized_identity : Specs.kkt_linearized_identity.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x lam nu hk d hd
  classical
  obtain ⟨hf, hprod⟩ := kkt_linearized_full_sum hk hd
  have hinactive : (∑ i : {i // i ∉ activeSet g x},
      lam i.val * fderiv ℝ (g i.val) x d) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [kkt_inactive_multiplier U f g h x lam nu hk i.val i.property, zero_mul]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun i => i ∈ activeSet g x) (fun i => lam i * fderiv ℝ (g i) x d)
  rw [hinactive, add_zero] at hsplit
  constructor
  · exact hf.trans (congrArg Neg.neg hsplit.symm)
  · rw [hf]
    exact neg_nonneg.mpr (Finset.sum_nonpos (fun i _ => hprod i))

theorem criticalCone_eq_zero : Specs.criticalCone_eq_zero.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x lam nu hk
  ext d
  constructor
  · intro hd
    exact ⟨hd.1, le_antisymm hd.2 (kkt_linearized_identity U f g h x lam nu hk d hd.1).2⟩
  · rintro ⟨hd, hf⟩
    exact ⟨hd, hf.le⟩

theorem criticalCone_eq_positive_multipliers : Specs.criticalCone_eq_positive_multipliers.{u,v,w} := by
  intro X _ _ I J _ _ U f g h x lam nu hk
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨hf, hprod⟩ := kkt_linearized_full_sum hk hd.1
    have hsum : (∑ i, lam i * fderiv ℝ (g i) x d) = 0 := by
      have hnonneg := (kkt_linearized_identity U f g h x lam nu hk d hd.1).2
      linarith only [hf, hd.2, hnonneg]
    refine ⟨hd.1, ?_⟩
    intro i hi
    have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hprod i)).mp hsum i
      (Finset.mem_univ i)
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hi)
  · rintro ⟨hd, hp⟩
    obtain ⟨hf, _⟩ := kkt_linearized_full_sum hk hd
    have hsum : (∑ i, lam i * fderiv ℝ (g i) x d) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : lam i = 0
      · rw [hi, zero_mul]
      · rw [hp i (lt_of_le_of_ne (hk.2.1 i) (Ne.symm hi)), mul_zero]
    exact ⟨hd, by rw [hf, hsum, neg_zero]⟩

end VariationalNotes.Ch06
