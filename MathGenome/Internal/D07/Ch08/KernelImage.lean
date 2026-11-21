import MathGenome.Internal.Specs.D07.Ch08.KernelImage
import MathGenome.Internal.D07.Ch08.IdealDefinition
import MathGenome.Internal.D07.Ch08.Subring
import MathGenome.Internal.D07.Ch09.QuotientProjection

/-!
K07.08.kernel_image, paper.tex:1311–1325.
The canonical kernel is the zero fibre, and is a two-sided ideal.
The canonical range is a subring containing the ambient identity.
The converse uses the accepted quotient projection, without a properness
or commutativity hypothesis.
-/

universe u v

namespace D07.Ch08.KernelImage

open Specs.D07.Ch08.KernelImage

theorem kernel_carrier : KernelCarrier.{u, v} := by
  intro R S _ _ f
  exact Set.ext (fun _ => RingHom.mem_ker)

theorem image_carrier : ImageCarrier.{u, v} := by
  intro R S _ _ f
  exact RingHom.coe_range f

theorem kernel_is_two_sided : KernelTwoSided.{u, v} := by
  intro R S _ _ f
  infer_instance

theorem kernel_absorption : KernelAbsorption.{u, v} := by
  intro R S _ _ f
  exact (D07.Ch08.IdealDefinition.twoSidedIdealCharacterization R (RingHom.ker f)).mp
    (kernel_is_two_sided R S f)

theorem image_is_unital_subring : ImageIsUnitalSubring.{u, v} := by
  intro R S _ _ f
  exact ⟨f.range, image_carrier R S f⟩

theorem image_closure : ImageClosure.{u, v} := by
  intro R S _ _ f
  exact (D07.Ch08.Subring.unitalSubringCharacterization S (Set.range f)).mpr
    (image_is_unital_subring R S f)

theorem every_two_sided_ideal_is_kernel : EveryTwoSidedIdealIsKernel.{u} := by
  intro R _ I _
  exact ⟨R ⧸ I, inferInstance, Ideal.Quotient.mk I,
    D07.Ch09.QuotientProjection.projection_surjective R I,
    D07.Ch09.QuotientProjection.projection_kernel R I⟩

end D07.Ch08.KernelImage
