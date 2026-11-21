import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.ModularObstruction
import MathGenome.Internal.AlgebraCore.P103.Ch08.RepresentationModules

noncomputable section
namespace P103.Ch08
open scoped MonoidAlgebra
variable {k G : Type*} [Field k] [Group G]

/-- The augmentation is the sum of the finitely many nonzero coefficients. -/
def augmentation : k[G] →ₗ[k] k := Specs.augmentationMap k G

@[simp] theorem augmentation_apply (x : k[G]) :
    augmentation x = x.coeff.sum (fun _ c => c) := by
  simp [augmentation, Specs.augmentationMap, Finsupp.linearCombination_apply]

@[simp] theorem augmentation_single (g : G) (c : k) :
    augmentation (MonoidAlgebra.single g c) = c := by
  simp [augmentation, Specs.augmentationMap]

theorem augmentation_surjective : Function.Surjective (augmentation (k := k) (G := G)) := by
  intro c
  exact ⟨MonoidAlgebra.single 1 c, augmentation_single 1 c⟩

theorem augmentation_equivariant (g : G) (x : k[G]) :
    augmentation (Representation.leftRegular k G g x) =
      Representation.trivial k G k g (augmentation x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Representation.trivial_apply] at *
    rw [hx, hy]
  | single h c => simp [Representation.leftRegular]

/-- A fixed vector in the left regular representation has constant coefficients. -/
theorem leftRegular_fixed_coeff (x : k[G])
    (hx : ∀ g : G, Representation.leftRegular k G g x = x) (h : G) :
    x.coeff h = x.coeff 1 := by
  have e := congrArg (fun y : k[G] => y.coeff h) (hx h)
  simpa [Representation.leftRegular, Representation.coeff_ofMulAction] using e.symm

/-- Its augmentation is the group order times its coefficient at the identity. -/
theorem augmentation_fixed [Finite G] (x : k[G])
    (hx : ∀ g : G, Representation.leftRegular k G g x = x) :
    augmentation x = (Nat.card G : k) * x.coeff 1 := by
  let := Fintype.ofFinite G
  rw [augmentation_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [leftRegular_fixed_coeff x hx]
  simp [Nat.card_eq_fintype_card, nsmul_eq_mul]

/-- In modular characteristic the surjective equivariant augmentation does not split. -/
theorem augmentation_no_section [Finite G] (hcard : (Nat.card G : k) = 0) :
    ¬ ∃ s : (Representation.trivial k G k).IntertwiningMap
      (Representation.leftRegular k G),
      Function.RightInverse s (augmentation (k := k) (G := G)) := by
  rintro ⟨s, hs⟩
  have hx : ∀ g : G, Representation.leftRegular k G g (s 1) = s 1 := by
    intro g
    simpa using (Representation.IntertwiningMap.isIntertwining _ _ s g 1).symm
  have hz : augmentation (s 1) = 0 := by
    rw [augmentation_fixed (s 1) hx, hcard, zero_mul]
  exact one_ne_zero ((hs 1).symm.trans hz)

end P103.Ch08
