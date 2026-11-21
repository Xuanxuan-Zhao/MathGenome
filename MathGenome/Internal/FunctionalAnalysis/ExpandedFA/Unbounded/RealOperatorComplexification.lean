import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealOperatorComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.RealComplexification

noncomputable section
namespace ExpandedFA.Unbounded.RealOperatorComplexification
open TraceIdeals.RealComplexification
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification (complexPair csmul ip)
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Extension on exactly D(A) + iD(A), on the existing Hilbert model. -/
abbrev complexify (A : Operator ℝ H K) : Operator ℂ (Space H) (Space K) :=
  Spec.complexifyValue A

@[simp] theorem mem_domain (A : Operator ℝ H K) (p : Space H) :
    p ∈ (complexify A).domain ↔ p.1 ∈ A.domain ∧ p.2 ∈ A.domain := Iff.rfl

@[simp] theorem apply_complexify (A : Operator ℝ H K) (p : (complexify A).domain) :
    complexify A p = complexPair K (A ⟨p.1.1, p.2.1⟩) (A ⟨p.1.2, p.2.2⟩) := rfl

theorem graph_iff (A : Operator ℝ H K) (p : Space H) (q : Space K) :
    (p, q) ∈ (complexify A).graph ↔
      (p.1, q.1) ∈ A.graph ∧ (p.2, q.2) ∈ A.graph := by
  constructor
  · intro h
    obtain ⟨hp, hq⟩ := (mem_graph_iff (complexify A) (p, q)).mp h
    exact ⟨(mem_graph_iff A (p.1, q.1)).mpr ⟨hp.1, congrArg Prod.fst hq⟩,
      (mem_graph_iff A (p.2, q.2)).mpr ⟨hp.2, congrArg Prod.snd hq⟩⟩
  · rintro ⟨h₁, h₂⟩
    obtain ⟨hx, hu⟩ := (mem_graph_iff A (p.1, q.1)).mp h₁
    obtain ⟨hy, hv⟩ := (mem_graph_iff A (p.2, q.2)).mp h₂
    exact (mem_graph_iff (complexify A) (p, q)).mpr ⟨⟨hx, hy⟩, Prod.ext hu hv⟩


theorem denselyDefined_iff (A : Operator ℝ H K) :
    DenselyDefined (complexify A) ↔ DenselyDefined A := by
  constructor
  · intro h
    apply (show Function.Surjective (realPart (H := H)) from
      fun x => ⟨inclusion x, rfl⟩).denseRange.dense_of_mapsTo realPart.continuous h
    intro p hp
    exact hp.1
  · intro h
    exact (h.prod h).preimage
      (Hilbert.PreHilbertCompactSpectral.Complexification.pairEquiv H).isOpenMap

theorem isClosed_iff (A : Operator ℝ H K) :
    IsClosed (complexify A) ↔ IsClosed A := by
  change _root_.IsClosed ((complexify A).graph : Set (Space H × Space K)) ↔
    _root_.IsClosed (A.graph : Set (H × K))
  constructor
  · intro h
    have hc : Continuous (fun p : H × K => (inclusion p.1, inclusion p.2)) :=
      (inclusion.continuous.comp continuous_fst).prodMk
        (inclusion.continuous.comp continuous_snd)
    have he : (fun p : H × K => (inclusion p.1, inclusion p.2)) ⁻¹'
        ((complexify A).graph : Set (Space H × Space K)) = A.graph := by
      ext p
      rw [Set.mem_preimage, SetLike.mem_coe, graph_iff]
      change (p ∈ A.graph ∧ (0, 0) ∈ A.graph) ↔ p ∈ A.graph
      simp only [show ((0 : H), (0 : K)) = (0 : H × K) from rfl,
        A.graph.zero_mem, and_true]
    rw [← he]
    exact h.preimage hc
  · intro h
    have hr : Continuous (fun p : Space H × Space K => (realPart p.1, realPart p.2)) :=
      (realPart.continuous.comp continuous_fst).prodMk
        (realPart.continuous.comp continuous_snd)
    have hi : Continuous (fun p : Space H × Space K => (imagPart p.1, imagPart p.2)) :=
      (imagPart.continuous.comp continuous_fst).prodMk
        (imagPart.continuous.comp continuous_snd)
    have he : ((complexify A).graph : Set (Space H × Space K)) =
        (fun p : Space H × Space K => (realPart p.1, realPart p.2)) ⁻¹'
          (A.graph : Set (H × K)) ∩
        (fun p : Space H × Space K => (imagPart p.1, imagPart p.2)) ⁻¹'
          (A.graph : Set (H × K)) := by
      ext p
      exact graph_iff A p.1 p.2
    rw [he]
    exact (h.preimage hr).inter (h.preimage hi)


/-- Equality of the full adjoint graphs, tested first on real inclusions. -/
theorem adjoint_graph_iff [CompleteSpace H] [CompleteSpace K]
    (A : Operator ℝ H K) (hA : DenselyDefined A) (p : Space K) (q : Space H) :
    (p, q) ∈ (hilbertAdjoint (complexify A)).graph ↔
      (p.1, q.1) ∈ (hilbertAdjoint A).graph ∧
      (p.2, q.2) ∈ (hilbertAdjoint A).graph := by
  rw [mem_hilbertAdjoint_graph_iff _ ((denselyDefined_iff A).mpr hA),
    mem_hilbertAdjoint_graph_iff A hA, mem_hilbertAdjoint_graph_iff A hA]
  constructor
  · intro h
    have ht (x : A.domain) := h (⟨inclusion x, ⟨x.2, A.domain.zero_mem⟩⟩ :
      (complexify A).domain)
    have he (x : A.domain) :
        (⟨inner ℝ (A x) p.1, inner ℝ (A x) p.2⟩ : ℂ) =
          ⟨inner ℝ (x : H) q.1, inner ℝ (x : H) q.2⟩ := by
      have hh := ht x
      change ip K (complexPair K (A x) (A (0 : A.domain))) p =
        ip H (complexPair H x 0) q at hh
      simpa only [A.map_zero, ip, complexPair, inner_zero_left, add_zero, sub_zero] using hh
    exact ⟨fun x => congrArg Complex.re (he x), fun x => congrArg Complex.im (he x)⟩
  · rintro ⟨hr, hi⟩ x
    let xr : A.domain := ⟨x.1.1, x.2.1⟩
    let xi : A.domain := ⟨x.1.2, x.2.2⟩
    change ip K (complexPair K (A xr) (A xi)) p = ip H x.1 q
    apply Complex.ext
    · change inner ℝ (A xr) p.1 + inner ℝ (A xi) p.2 =
        inner ℝ (xr : H) q.1 + inner ℝ (xi : H) q.2
      rw [hr xr, hi xi]
    · change inner ℝ (A xr) p.2 - inner ℝ (A xi) p.1 =
        inner ℝ (xr : H) q.2 - inner ℝ (xi : H) q.1
      rw [hi xr, hr xi]

theorem adjoint_eq [CompleteSpace H] [CompleteSpace K]
    (A : Operator ℝ H K) (hA : DenselyDefined A) :
    hilbertAdjoint (complexify A) = complexify (hilbertAdjoint A) := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨p, q⟩
  rw [adjoint_graph_iff A hA, graph_iff]

theorem complexify_injective : Function.Injective
    (complexify (H := H) (K := K)) := by
  intro A B h
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  have ht : ((inclusion x, inclusion y) ∈ (complexify A).graph) ↔
      ((inclusion x, inclusion y) ∈ (complexify B).graph) := by rw [h]
  have ha := graph_iff A (inclusion x) (inclusion y)
  have hb := graph_iff B (inclusion x) (inclusion y)
  change ((inclusion x, inclusion y) ∈ (complexify A).graph ↔
    (x, y) ∈ A.graph ∧ (0, 0) ∈ A.graph) at ha
  change ((inclusion x, inclusion y) ∈ (complexify B).graph ↔
    (x, y) ∈ B.graph ∧ (0, 0) ∈ B.graph) at hb
  have he := ha.symm.trans (ht.trans hb)
  simpa only [show ((0 : H), (0 : K)) = (0 : H × K) from rfl,
    A.graph.zero_mem, B.graph.zero_mem, and_true] using he


theorem selfAdjoint_iff [CompleteSpace H] (A : Operator ℝ H H)
    (hA : DenselyDefined A) :
    hilbertAdjoint (complexify A) = complexify A ↔ hilbertAdjoint A = A := by
  rw [adjoint_eq A hA]
  exact complexify_injective.eq_iff

theorem conjugation_domain (A : Operator ℝ H K) (p : Space H) :
    conjugation p ∈ (complexify A).domain ↔ p ∈ (complexify A).domain := by
  change (p.1 ∈ A.domain ∧ -p.2 ∈ A.domain) ↔ (p.1 ∈ A.domain ∧ p.2 ∈ A.domain)
  rw [Submodule.neg_mem_iff]

theorem conjugation_apply (A : Operator ℝ H K) (p : (complexify A).domain) :
    complexify A ⟨conjugation p.1, (conjugation_domain A p.1).mpr p.2⟩ =
      conjugation (complexify A p) := by
  change complexPair K (A ⟨p.1.1, _⟩) (A (- (⟨p.1.2, p.2.2⟩ : A.domain))) =
    complexPair K (A ⟨p.1.1, _⟩) (- A ⟨p.1.2, p.2.2⟩)
  exact congrArg (complexPair K (A ⟨p.1.1, p.2.1⟩)) (A.map_neg _)

theorem bounded_eq (T : H →L[ℝ] K) :
    complexify (T.toLinearMap.toPMap ⊤) = (operator T).toLinearMap.toPMap ⊤ := by
  apply LinearPMap.ext
  · ext p
    change (p.1 ∈ (⊤ : Submodule ℝ H) ∧ p.2 ∈ (⊤ : Submodule ℝ H)) ↔
      p ∈ (⊤ : Submodule ℂ (Space H))
    simp
  · intro p hp hq
    rfl

/-- The domain has the literal x + iy description as well as coordinate tests. -/
theorem domain_decomposition (A : Operator ℝ H K) (p : Space H) :
    p ∈ (complexify A).domain ↔ ∃ x y : A.domain,
      p = inclusion (x : H) + Complex.I • inclusion (y : H) := by
  constructor
  · intro hp
    exact ⟨⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩, decomposition p⟩
  · rintro ⟨x, y, h⟩
    have he : p = complexPair H x y := h.trans (decomposition (complexPair H x y)).symm
    rw [he]
    exact ⟨x.2, y.2⟩

theorem conjugation_evaluation : Spec.ConjugationEvaluation.{u,v} := by
  intro H K _ _ _ _ A p
  exact ⟨(conjugation_domain A p.1).mpr p.2, conjugation_apply A p⟩

lemma real_smul_pair (r : ℝ) (p : Space H) :
    (r : ℂ) • p = complexPair H (r • p.1) (r • p.2) := by
  rw [csmul]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero, zero_add]

/-- Transport the entire bounded inverse, including both original-domain laws. -/
def complexifyResolventInverse (A : Operator ℝ H H) (r : ℝ)
    (R : ResolventInverse A r) : ResolventInverse (complexify A) (r : ℂ) where
  inverse := operator R.inverse
  mem_domain y := ⟨R.mem_domain y.1, R.mem_domain y.2⟩
  right_inverse y := by
    rw [real_smul_pair]
    exact Prod.ext (R.right_inverse y.1) (R.right_inverse y.2)
  left_inverse x := by
    rw [real_smul_pair]
    exact Prod.ext (R.left_inverse ⟨x.1.1, x.2.1⟩) (R.left_inverse ⟨x.1.2, x.2.2⟩)

/-- Recover a bounded real inverse by the actual inclusion and real projection.
The left inverse is tested on the original domain, without a density assumption. -/
def realResolventInverse (A : Operator ℝ H H) (r : ℝ)
    (R : ResolventInverse (complexify A) (r : ℂ)) : ResolventInverse A r where
  inverse := realPart.comp ((R.inverse.restrictScalars ℝ).comp inclusion.toContinuousLinearMap)
  mem_domain y := (R.mem_domain (inclusion y)).1
  right_inverse y := by
    have h := R.right_inverse (inclusion y)
    rw [real_smul_pair] at h
    exact congrArg Prod.fst h
  left_inverse x := by
    have h := R.left_inverse (⟨inclusion x, ⟨x.2, A.domain.zero_mem⟩⟩ : (complexify A).domain)
    have he : (r : ℂ) • inclusion (x : H) -
        complexify A ⟨inclusion x, ⟨x.2, A.domain.zero_mem⟩⟩ =
        inclusion (r • (x : H) - A x) := by
      rw [real_smul_pair]
      change (r • (x : H) - A x, r • (0 : H) - A (0 : A.domain)) =
        (r • (x : H) - A x, 0)
      rw [smul_zero, A.map_zero, sub_self]
    rw [he] at h
    exact congrArg Prod.fst h

theorem resolvent_equivalence (A : Operator ℝ H H) (r : ℝ) :
    Nonempty (ResolventInverse A r) ↔ Nonempty (ResolventInverse (complexify A) (r : ℂ)) :=
  ⟨fun ⟨R⟩ => ⟨complexifyResolventInverse A r R⟩,
    fun ⟨R⟩ => ⟨realResolventInverse A r R⟩⟩

theorem resolvent_inverse_identification (A : Operator ℝ H H) (r : ℝ)
    (R : ResolventInverse A r) (S : ResolventInverse (complexify A) (r : ℂ)) :
    S.inverse = operator R.inverse :=
  resolvent_inverse_unique (r : ℂ) (complexify A) S (complexifyResolventInverse A r R)

/-- Identification of the canonical totalized resolvents at real resolvent points. -/
theorem resolvent_eq (A : Operator ℝ H H) (r : ℝ)
    (hr : r ∈ resolventSet A) :
    resolvent (r : ℂ) (complexify A) = operator (resolvent r A) := by
  have hc : (r : ℂ) ∈ resolventSet (complexify A) := (resolvent_equivalence A r).mp hr
  change OperatorDomainsSpec.resolventValue (r : ℂ) (complexify A) =
    operator (OperatorDomainsSpec.resolventValue r A)
  change Nonempty (ResolventInverse A r) at hr
  change Nonempty (ResolventInverse (complexify A) (r : ℂ)) at hc
  simp only [OperatorDomainsSpec.resolventValue, dite_eq_left hc, dite_eq_left hr]
  exact resolvent_inverse_identification A r hr.some hc.some

end ExpandedFA.Unbounded.RealOperatorComplexification
