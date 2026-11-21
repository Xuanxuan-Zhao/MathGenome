import MathGenome.Internal.MultivariableAnalysis.D04.C01.SequentialContinuity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.ContinuousOperations
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! Continuous operations on the specified relative domains. The shared
bridges identify the source's epsilon-delta topology with the subtype topology.
Matrix multiplication retains its row/column dimensions and factor order. -/
noncomputable section
open Set Topology
open scoped BigOperators
namespace D04

def scalarVector : ℝ → E 1 :=
  Specs.D04.C01.ContinuousOperations.Model.scalarVector

def matrixChainProduct :=
  Specs.D04.C01.ContinuousOperations.Model.matrixChainProduct

theorem relativeContinuous_coordinates_iff :
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m),
    RelativeContinuous A f ↔ ∀ i : Fin m, Continuous (fun x => f x i) := by
  intro n m A f
  rw [relativeContinuous_iff]
  constructor
  · intro h i
    exact (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).comp h
  · intro h
    exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp (continuous_pi h)

theorem relativeContinuous_scalarVector_iff :
  ∀ {n : ℕ} (A : Set (E n)) (f : A → ℝ),
    RelativeContinuous A (fun x => scalarVector (f x)) ↔ Continuous f := by
  intro n A f
  rw [relativeContinuous_coordinates_iff]
  constructor
  · intro h
    exact h 0
  · intro h i
    exact h

theorem relativeContinuous_comp :
  ∀ {n m p : ℕ} (A : Set (E n)) (B : Set (E m))
    (f : A → E m) (g : B → E p)
    (hmap : ∀ x : A, f x ∈ B),
    RelativeContinuous A f → RelativeContinuous B g →
    RelativeContinuous A (fun x => g ⟨f x, hmap x⟩) := by
  intro n m p A B f g hmap hf hg
  apply (relativeContinuous_iff A _).mpr
  exact ((relativeContinuous_iff B g).mp hg).comp
    (((relativeContinuous_iff A f).mp hf).subtype_mk hmap)

theorem relativeContinuous_iff_open_preimages :
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m),
    RelativeContinuous A f ↔
      ∀ O : Set (E m), Open O →
        RelativelyOpen A ((Subtype.val : A → E n) '' (f ⁻¹' O)) := by
  intro n m A f
  rw [relativeContinuous_iff]
  have he (O : Set (E m)) :
      (Subtype.val : A → E n) ⁻¹'
        ((Subtype.val : A → E n) '' (f ⁻¹' O)) = f ⁻¹' O := by
    ext x
    simp
  constructor
  · intro hf O hO
    apply (relativelyOpen_subtype_iff A _).mpr
    refine ⟨?_, ?_⟩
    · rintro x ⟨a, ha, rfl⟩
      exact a.property
    · rw [he]
      exact ((open_iff_isOpen O).mp hO).preimage hf
  · intro h
    apply continuous_def.mpr
    intro O hO
    have hp := (relativelyOpen_subtype_iff A _).mp
      (h O ((open_iff_isOpen O).mpr hO))
    simpa only [he] using hp.2

theorem relativeContinuous_add :
  ∀ {n m : ℕ} (A : Set (E n)) (f g : A → E m),
    RelativeContinuous A f → RelativeContinuous A g →
    RelativeContinuous A (fun x => f x + g x) := by
  intro n m A f g hf hg
  exact (relativeContinuous_iff A _).mpr
    (((relativeContinuous_iff A f).mp hf).add ((relativeContinuous_iff A g).mp hg))

theorem relativeContinuous_finset_sum :
  ∀ {n m : ℕ} {ι : Type} (A : Set (E n)) (s : Finset ι)
    (f : ι → A → E m),
    (∀ i ∈ s, RelativeContinuous A (f i)) →
    RelativeContinuous A (fun x => ∑ i ∈ s, f i x) := by
  intro n m ι A s f hf
  apply (relativeContinuous_iff A _).mpr
  exact continuous_finsetSum s (fun i hi => (relativeContinuous_iff A (f i)).mp (hf i hi))

theorem relativeContinuous_const_smul :
  ∀ {n m : ℕ} (A : Set (E n)) (f : A → E m) (c : ℝ),
    RelativeContinuous A f → RelativeContinuous A (fun x => c • f x) := by
  intro n m A f c hf
  exact (relativeContinuous_iff A _).mpr
    (((relativeContinuous_iff A f).mp hf).const_smul c)

theorem relativeContinuous_smul :
  ∀ {n m : ℕ} (A : Set (E n)) (c : A → ℝ) (f : A → E m),
    RelativeContinuous A (fun x => scalarVector (c x)) →
    RelativeContinuous A f → RelativeContinuous A (fun x => c x • f x) := by
  intro n m A c f hc hf
  exact (relativeContinuous_iff A _).mpr
    (((relativeContinuous_scalarVector_iff A c).mp hc).smul
      ((relativeContinuous_iff A f).mp hf))

theorem relativeContinuous_inner :
  ∀ {n m : ℕ} (A : Set (E n)) (f g : A → E m),
    RelativeContinuous A f → RelativeContinuous A g →
    RelativeContinuous A (fun x => scalarVector (inner ℝ (f x) (g x))) := by
  intro n m A f g hf hg
  exact (relativeContinuous_scalarVector_iff A _).mpr
    (((relativeContinuous_iff A f).mp hf).inner ((relativeContinuous_iff A g).mp hg))

theorem continuous_matrix_iff_relativeContinuous_rows :
  ∀ {n r c : ℕ} (A : Set (E n))
    (F : A → Matrix (Fin r) (Fin c) ℝ),
    Continuous F ↔
      ∀ i : Fin r, RelativeContinuous A (fun x => WithLp.toLp 2 (F x i)) := by
  intro n r c A F
  simp_rw [relativeContinuous_coordinates_iff]
  exact ⟨fun h i j => h.matrix_elem i j, continuous_matrix⟩

theorem relativeContinuous_matrix_mul :
  ∀ {n r s c : ℕ} (A : Set (E n))
    (F : A → Matrix (Fin r) (Fin s) ℝ)
    (G : A → Matrix (Fin s) (Fin c) ℝ),
    (∀ i : Fin r, RelativeContinuous A (fun x => WithLp.toLp 2 (F x i))) →
    (∀ i : Fin s, RelativeContinuous A (fun x => WithLp.toLp 2 (G x i))) →
    ∀ i : Fin r,
      RelativeContinuous A (fun x => WithLp.toLp 2 ((F x * G x) i)) := by
  intro n r s c A F G hf hg
  apply (continuous_matrix_iff_relativeContinuous_rows A _).mp
  exact ((continuous_matrix_iff_relativeContinuous_rows A F).mpr hf).matrix_mul
    ((continuous_matrix_iff_relativeContinuous_rows A G).mpr hg)

theorem relativeContinuous_matrixChainProduct :
  ∀ {n : ℕ} (A : Set (E n)) (d : ℕ → ℕ)
    (F : (i : ℕ) → A → Matrix (Fin (d i)) (Fin (d (i + 1))) ℝ)
    (k : ℕ),
    (∀ j < k, ∀ i : Fin (d j),
      RelativeContinuous A (fun x => WithLp.toLp 2 (F j x i))) →
    ∀ i : Fin (d 0), RelativeContinuous A
      (fun x => WithLp.toLp 2 (matrixChainProduct d (fun j => F j x) k i)) := by
  intro n A d F k
  induction k with
  | zero =>
    intro _ i
    apply (relativeContinuous_iff A _).mpr
    change Continuous (fun _ : A =>
      (WithLp.toLp 2 ((1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ) i) : E (d 0)))
    exact continuous_const
  | succ k ih =>
    intro h
    have hp := ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self k)))
    exact relativeContinuous_matrix_mul A
      (fun x => matrixChainProduct d (fun j => F j x) k) (F k)
      hp (h k (Nat.lt_succ_self k))

theorem relativeContinuous_quotient :
  ∀ {n : ℕ} (A : Set (E n)) (p q : A → ℝ),
    RelativeContinuous A (fun x => scalarVector (p x)) →
    RelativeContinuous A (fun x => scalarVector (q x)) →
    ∀ (B : Set (E n)) (hBA : B ⊆ A),
      (∀ x : B, q ⟨x.val, hBA x.property⟩ ≠ 0) →
      RelativeContinuous B (fun x => scalarVector
        (p ⟨x.val, hBA x.property⟩ / q ⟨x.val, hBA x.property⟩)) := by
  intro n A p q hp hq B hBA hne
  apply (relativeContinuous_scalarVector_iff B _).mpr
  have hi : Continuous (fun x : B => (⟨x.val, hBA x.property⟩ : A)) :=
    continuous_subtype_val.subtype_mk _
  exact (((relativeContinuous_scalarVector_iff A p).mp hp).comp hi).div
    (((relativeContinuous_scalarVector_iff A q).mp hq).comp hi) hne

theorem relativeContinuousAt_quotient :
  ∀ {n : ℕ} (A : Set (E n)) (p q : A → ℝ),
    RelativeContinuous A (fun x => scalarVector (p x)) →
    RelativeContinuous A (fun x => scalarVector (q x)) →
    ∀ a : A, q a ≠ 0 →
      RelativeContinuousAt A (fun x => scalarVector (p x / q x)) a := by
  intro n A p q hp hq a hne
  apply (relativeContinuousAt_iff A _ a).mpr
  have hdiv : ContinuousAt (fun x => p x / q x) a :=
    ((relativeContinuous_scalarVector_iff A p).mp hp).continuousAt.div
      ((relativeContinuous_scalarVector_iff A q).mp hq).continuousAt hne
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).continuousAt.comp
    (continuousAt_pi.mpr (fun _ => hdiv))

end D04
