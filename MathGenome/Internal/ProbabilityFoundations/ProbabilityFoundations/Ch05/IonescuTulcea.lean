import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.IonescuTulcea
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.CylinderFramework
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.KernelMeasure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
The Ionescu--Tulcea theorem for the shared prefix spaces. We transport the
given kernels along the inclusive-prefix equivalence and apply Mathlib's
trajectory construction. Its marginals satisfy the recursive kernel-product
laws; projective-limit uniqueness then determines the full law.
-/

open MeasureTheory ProbabilityTheory
open ProbabilityFoundations.Ch05.CylinderFramework
open Finset Preorder

namespace ProbabilityFoundations.Ch05.IonescuTulcea

universe u
variable {S : ℕ → Type u} [∀ n, MeasurableSpace (S n)]

@[fun_prop] theorem measurable_initialPrefix : Measurable (initialPrefix S) :=
  (prefixSplit S 0).symm.measurable.comp (measurable_const.prodMk measurable_id)

instance nonemptyPrefixLaw_probability (μ₁ : Measure (S 0)) [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsProbabilityMeasure (nonemptyPrefixLaw S μ₁ K n) := by
  induction n with
  | zero => exact (Measure.isProbabilityMeasure_map_iff measurable_initialPrefix.aemeasurable).2 inferInstance
  | succ n ih =>
    have := ih
    exact (Measure.isProbabilityMeasure_map_iff (prefixSplit S (n+1)).symm.measurable.aemeasurable).2 inferInstance

instance prefixLaw_probability (μ₁ : Measure (S 0)) [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsProbabilityMeasure (prefixLaw S μ₁ K n) := by
  cases n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))
  | succ n => exact nonemptyPrefixLaw_probability μ₁ K n

/-- The library's inclusive prefix is the shared prefix of length `n+1`. -/
def inclusivePrefix (n : ℕ) : (Π i : Iic n, S i) ≃ᵐ PrefixSpace S (n+1) where
  toFun x i := x ⟨i, mem_Iic.mpr (Nat.le_of_lt_succ (mem_range.mp i.2))⟩
  invFun x i := x ⟨i, mem_range.mpr (Nat.lt_succ_of_le (mem_Iic.mp i.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := Measurable.of_eval (fun _ => measurable_pi_apply _)
  measurable_invFun := Measurable.of_eval (fun _ => measurable_pi_apply _)

private noncomputable def adaptedKernels
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    (n : ℕ) : Kernel (Π i : Iic n, S i) (S (n+1)) :=
  (K n).comap (inclusivePrefix n) (inclusivePrefix n).measurable

private instance adaptedKernels_markov
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) : IsMarkovKernel (adaptedKernels K n) := by
  unfold adaptedKernels
  infer_instance

/-- Change the base coordinate of a kernel-induced product by a measurable map. -/
theorem compProd_map_base {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [SFinite μ] (K : Kernel B C)
    [IsSFiniteKernel K] (f : A → B) (hf : Measurable f) :
    (μ.map f).compProd K =
      (μ.compProd (K.comap f hf)).map (Prod.map f id) := by
  ext t ht
  rw [Measure.compProd_apply ht,
    lintegral_map (Kernel.measurable_kernel_prodMk_left ht) hf,
    Measure.map_apply (hf.prodMap measurable_id) ht,
    Measure.compProd_apply ((hf.prodMap measurable_id) ht)]
  rfl

private noncomputable def extensionMeasure (μ₁ : Measure (S 0))
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)] : Measure (ProductSpace S) :=
  Kernel.trajMeasure μ₁ (adaptedKernels K)

private instance extensionMeasure_probability (μ₁ : Measure (S 0))
    [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)] : IsProbabilityMeasure (extensionMeasure μ₁ K) := by
  unfold extensionMeasure
  infer_instance

variable (μ₁ : Measure (S 0)) [IsProbabilityMeasure μ₁]
    (K : (n : ℕ) → Kernel (PrefixSpace S (n+1)) (S (n+1)))
    [∀ n, IsMarkovKernel (K n)]

omit [IsProbabilityMeasure μ₁] in
private theorem extensionMeasure_initial_inclusive :
    (extensionMeasure μ₁ K).map (frestrictLe 0) =
      μ₁.map (MeasurableEquiv.piUnique _).symm := by
  rw [extensionMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

omit [IsProbabilityMeasure μ₁] in
private theorem extensionMeasure_initial :
    (extensionMeasure μ₁ K).map (fun x => x 0) = μ₁ := by
  have h := congrArg (fun m : Measure (Π i : Iic 0, S i) =>
    m.map (fun x => x ⟨0, mem_Iic.mpr (Nat.zero_le 0)⟩))
    (extensionMeasure_initial_inclusive μ₁ K)
  rw [Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe 0),
    Measure.map_map (measurable_pi_apply _) (MeasurableEquiv.piUnique _).symm.measurable] at h
  simpa [Function.comp_def, MeasurableEquiv.piUnique, Equiv.piUnique, uniqueElim] using h

private theorem extensionMeasure_step (n : ℕ) :
    ((extensionMeasure μ₁ K).map (prefixProjection S (n+1))).compProd (K n) =
      (extensionMeasure μ₁ K).map (fun x => (prefixProjection S (n+1) x, x (n+1))) := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (μ₀ := μ₁) (κ := adaptedKernels K) (a := n)
  change ((extensionMeasure μ₁ K).map (frestrictLe n)).compProd
    ((K n).comap (inclusivePrefix n) (inclusivePrefix n).measurable) =
    (extensionMeasure μ₁ K).map (fun x => (frestrictLe n x, x (n+1))) at h
  have h' := congrArg (fun m => m.map (Prod.map (inclusivePrefix (S := S) n) id)) h
  rw [Measure.map_map ((inclusivePrefix n).measurable.prodMap measurable_id)
    ((measurable_frestrictLe n).prodMk (measurable_pi_apply _))] at h'
  have : SFinite ((extensionMeasure μ₁ K).map (frestrictLe n)) := by infer_instance
  rw [← compProd_map_base _ (K n) (inclusivePrefix n) (inclusivePrefix n).measurable,
    Measure.map_map (inclusivePrefix n).measurable (measurable_frestrictLe n)] at h'
  exact h'

private theorem extensionMeasure_prefix (n : ℕ) :
    (extensionMeasure μ₁ K).map (prefixProjection S n) = prefixLaw S μ₁ K n := by
  cases n with
  | zero =>
    have heq : prefixProjection S 0 = fun _ => emptyPrefix S :=
      funext fun _ => funext fun i => False.elim (by simpa using i.2)
    rw [heq, Measure.map_const, measure_univ, one_smul]
    rfl
  | succ n =>
    change (extensionMeasure μ₁ K).map (prefixProjection S (n+1)) = nonemptyPrefixLaw S μ₁ K n
    induction n with
    | zero =>
      have heq : prefixProjection S 1 = initialPrefix S ∘ (fun x : ProductSpace S => x 0) := by
        funext x
        apply (prefixSplit S 0).injective
        apply Prod.ext
        · funext i
          exact False.elim (by simpa using i.2)
        · rfl
      rw [heq, ← Measure.map_map measurable_initialPrefix (measurable_pi_apply _),
        extensionMeasure_initial]
      rfl
    | succ n ih =>
      rw [nonemptyPrefixLaw, ← ih, extensionMeasure_step,
        Measure.map_map (prefixSplit S (n+1)).symm.measurable
          ((measurable_prefixProjection S (n+1)).prodMk (measurable_pi_apply _))]
      congr 1
      funext x
      apply (prefixSplit S (n+1)).injective
      simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
      rfl

/-- Finite measures on the product sigma-algebra are determined by their prefix laws. -/
theorem measure_eq_of_prefix_marginals (μ ν : Measure (ProductSpace S)) [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (prefixProjection S n) = ν.map (prefixProjection S n)) : μ = ν := by
  let P := fun n => μ.map (frestrictLe n)
  have hP : IsProjectiveMeasureFamily (inducedFamily P) :=
    isProjectiveMeasureFamily_inducedFamily P (by
      intro a b hab
      dsimp [P]
      rw [Measure.map_map (measurable_frestrictLe₂ hab) (measurable_frestrictLe b)]
      rfl)
  have hμ : IsProjectiveLimit μ (inducedFamily P) :=
    (isProjectiveLimit_nat_iff hP μ).2 (fun n => by rw [inducedFamily_Iic])
  have hν : IsProjectiveLimit ν (inducedFamily P) := by
    apply (isProjectiveLimit_nat_iff hP ν).2
    intro n
    rw [inducedFamily_Iic]
    have hn := congrArg (fun m => m.map (inclusivePrefix (S := S) n).symm) (h (n+1))
    rw [Measure.map_map (inclusivePrefix n).symm.measurable (measurable_prefixProjection S (n+1)),
      Measure.map_map (inclusivePrefix n).symm.measurable (measurable_prefixProjection S (n+1))] at hn
    exact hn.symm
  exact hμ.unique hν

/-- Every recursively constructed prefix law is a probability, including length zero. -/
theorem prefixProbability :
    Specs.ProbabilityFoundations.Ch05.IonescuTulcea.PrefixProbability.{u} := by
  intro S inst μ₁ hμ K hK n
  exact prefixLaw_probability μ₁ K n

/-- All nested prefix restrictions have the prescribed shorter law. -/
theorem prefixConsistency :
    Specs.ProbabilityFoundations.Ch05.IonescuTulcea.PrefixConsistency.{u} := by
  intro S inst μ₁ hμ K hK m n hmn
  rw [← extensionMeasure_prefix μ₁ K m, ← extensionMeasure_prefix μ₁ K n,
    Measure.map_map (measurable_prefixRestriction S hmn) (measurable_prefixProjection S n)]
  rfl

/-- Nonemptiness is a consequence of the probability and kernel data. -/
theorem coordinateNonempty :
    Specs.ProbabilityFoundations.Ch05.IonescuTulcea.CoordinateNonempty.{u} := by
  intro S inst μ₁ hμ K hK n
  obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure (extensionMeasure μ₁ K)
  exact ⟨x n⟩

/-- Ionescu--Tulcea for arbitrary measurable coordinate spaces, on the common
product sigma-algebra, with the literal kernel-product prefix recursion. -/
theorem ionescuTulcea :
    Specs.ProbabilityFoundations.Ch05.IonescuTulcea.Extension.{u} := by
  intro S inst μ₁ hμ K hK
  refine ⟨extensionMeasure μ₁ K, ⟨inferInstance,
    extensionMeasure_initial μ₁ K, extensionMeasure_prefix μ₁ K⟩, ?_⟩
  intro ν hν
  exact (measure_eq_of_prefix_marginals (extensionMeasure μ₁ K) ν
    (fun n => (extensionMeasure_prefix μ₁ K n).trans (hν.2.2 n).symm)).symm

end ProbabilityFoundations.Ch05.IonescuTulcea
