import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.LocalDetection
import MathGenome.Internal.AlgebraCore.P103.Ch04.ModuleLocalization
import Mathlib.RingTheory.LocalProperties.Exactness

namespace P103.Ch04.LocalDetection

universe u v w x

theorem nonzeroWitness : LocalDetectionSpecs.NonzeroWitness.{u,v} := by
  intro R _ M _ _ m hm
  let I := (Submodule.span R ({m} : Set M)).annihilator
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ I := h ▸ Submodule.mem_top
    exact hm (by simpa using (Submodule.mem_annihilator_span_singleton m 1).mp h1)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  refine ⟨P, hP, hIP, ?_⟩
  intro hz
  obtain ⟨s, hs⟩ := (ModuleLocalization.fractionZero R P.primeCompl M m 1).mp hz
  exact s.property (hIP ((Submodule.mem_annihilator_span_singleton m (s : R)).mpr hs))

theorem zeroDetection : LocalDetectionSpecs.ZeroDetection.{u,v} := by
  intro R _ M _ _
  constructor
  · intro h P _
    let := h
    infer_instance
  · intro h
    apply (subsingleton_iff_forall_eq (0 : M)).mpr
    intro m
    by_contra hm
    obtain ⟨P, hP, _, hn⟩ := nonzeroWitness R M m hm
    exact hn (@Subsingleton.elim _ (h P) _ _)

theorem injectivityDetection : LocalDetectionSpecs.InjectivityDetection.{u,v,w} := by
  intro R _ M N _ _ _ _ f
  exact ⟨fun h P _ => ModuleLocalization.preservesInjectivity R P.primeCompl M N f h,
    injective_of_localized_maximal f⟩

theorem surjectivityDetection : LocalDetectionSpecs.SurjectivityDetection.{u,v,w} := by
  intro R _ M N _ _ _ _ f
  exact ⟨fun h P _ => ModuleLocalization.preservesSurjectivity R P.primeCompl M N f h,
    surjective_of_localized_maximal f⟩

theorem bijectivityDetection : LocalDetectionSpecs.BijectivityDetection.{u,v,w} := by
  intro R _ M N _ _ _ _ f
  constructor
  · intro h P _
    exact ⟨(injectivityDetection R M N f).mp h.1 P,
      (surjectivityDetection R M N f).mp h.2 P⟩
  · intro h
    exact ⟨(injectivityDetection R M N f).mpr (fun P _ => (h P).1),
      (surjectivityDetection R M N f).mpr (fun P _ => (h P).2)⟩

theorem exactnessDetection : LocalDetectionSpecs.ExactnessDetection.{u,v,w,x} := by
  intro R _ L M N _ _ _ _ _ _ f g
  exact ⟨fun h P _ => ModuleLocalization.preservesExactness R P.primeCompl L M N f g h,
    exact_of_localized_maximal f g⟩

theorem sequenceExactnessDetection :
    LocalDetectionSpecs.SequenceExactnessDetection.{u,v,w} := by
  intro R _ ι next M _ _ d
  constructor
  · intro h P _ i
    exact (exactnessDetection R _ _ _ (d i) (d (next i))).mp (h i) P
  · intro h i
    exact (exactnessDetection R _ _ _ (d i) (d (next i))).mpr (fun P _ => h P i)

theorem zeroRingCase : LocalDetectionSpecs.ZeroRingCase.{u,v} := by
  intro R _ _ M _ _
  refine ⟨Module.subsingleton R M, ?_⟩
  rintro ⟨P, hP⟩
  exact hP.ne_top (Subsingleton.elim _ _)

end P103.Ch04.LocalDetection
