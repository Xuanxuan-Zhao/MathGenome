import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.SmoothDescent
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps

namespace SmoothManifolds.SmoothDescent
open Set Filter
open scoped Topology
universe u v w

abbrev HasSmoothLocalSections := @SmoothDescentData.HasSmoothLocalSections

section
variable {m n p : ℕ} {a b c : ModelKind}
  {M : Type u} {N : Type v} {P : Type w}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]

/-- Smoothness can be tested after precomposition with a map with local sections. -/
theorem smooth_of_comp (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (R : SmoothManifold p c P) (q : M → N) (f : N → P)
    (hsec : HasSmoothLocalSections S T q) (hf : IsSmoothMap S R (f ∘ q)) :
    IsSmoothMap T R f := by
  intro y
  obtain ⟨U, hU, hy, s, hs, hqs⟩ := hsec y
  have hcomp := manifoldContDiff_comp (⊤ : ℕ∞)
    (openSubsetAtlas T.smoothStructure.val U hU) S.smoothStructure.val
    R.smoothStructure.val S.smoothStructure.property.1.1 s (f ∘ q) hs hf
  have hrestr : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val U hU)
      R.smoothStructure.val (fun z : U => f z.val) := by
    convert hcomp using 1
    funext z
    exact congrArg f (hqs z).symm
  exact ((manifoldContDiff_restrict_open (⊤ : ℕ∞) T.smoothStructure.val
    R.smoothStructure.val f U hU).mpr hrestr) y hy

end

/-- The local inverse-image test recovers openness on each section neighborhood. -/
theorem quotient : Specs.SmoothManifolds.Ch03.SmoothDescent.quotientType.{u,v} := by
  intro m n a b M N _ _ S T q _hq hq hsec B
  constructor
  · intro hB
    exact hB.preimage (continuous_iff_continuousAt.mpr (fun x => (hq x).1))
  · intro hB
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hU, hyU, s, hs, hqs⟩ := hsec y
    have hscont : Continuous s := continuous_iff_continuousAt.mpr (fun z => (hs z).1)
    have hopen := hU.isOpenEmbedding_subtypeVal.isOpenMap
      (s ⁻¹' (q ⁻¹' B)) (hB.preimage hscont)
    apply Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
    · exact ⟨⟨y, hyU⟩, by simpa only [mem_preimage, hqs] using hy, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      simpa only [mem_preimage, hqs] using hw

/-- Choose fiber representatives, then use sections to prove their descent smooth. -/
theorem descent : Specs.SmoothManifolds.Ch03.SmoothDescent.descentType.{u,v,w} := by
  classical
  intro m n p a b c M N P _ _ _ S T R q hsurj _hq hsec h hh hfiber
  let f : N → P := fun y => h (Classical.choose (hsurj y))
  have hfactor : f ∘ q = h := by
    funext x
    exact hfiber _ x (Classical.choose_spec (hsurj (q x)))
  have hf : IsSmoothMap T R f := smooth_of_comp S T R q f hsec (by rw [hfactor]; exact hh)
  refine ⟨f, ⟨hf, hfactor⟩, ?_⟩
  rintro g ⟨_, hg⟩
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  exact (congrFun hg x).trans (congrFun hfactor x).symm

/-- The two descents are inverse because their composites agree after the
surjective maps from the common source. -/
theorem sameFibers_diffeomorph :
    Specs.SmoothManifolds.Ch03.SmoothDescent.sameFibers_diffeomorphType.{u,v,w} := by
  intro m n p a b c M N P _ _ _ S T R q₁ q₂ hsurj₁ hsurj₂ hq₁ hq₂ hsec₁ hsec₂ hfibers
  obtain ⟨f, ⟨hf, hfeq⟩, _⟩ := descent S T R q₁ hsurj₁ hq₁ hsec₁ q₂ hq₂
    (fun x x' h => (hfibers x x').mp h)
  obtain ⟨g, ⟨hg, hgeq⟩, _⟩ := descent S R T q₂ hsurj₂ hq₂ hsec₂ q₁ hq₁
    (fun x x' h => (hfibers x x').mpr h)
  have hgf : Function.LeftInverse g f := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj₁ y
    change g ((f ∘ q₁) x) = q₁ x
    rw [hfeq]
    exact congrFun hgeq x
  have hfg : Function.RightInverse g f := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj₂ y
    change f ((g ∘ q₂) x) = q₂ x
    rw [hgeq]
    exact congrFun hfeq x
  let e : Diffeomorph T.smoothStructure.val R.smoothStructure.val :=
    { toEquiv := { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg }
      contDiff_toFun := hf
      contDiff_invFun := hg }
  refine ⟨e, hfeq, hgeq, ?_⟩
  intro d hd
  have hfun : d.toEquiv = e.toEquiv := by
    apply Equiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hsurj₁ y
    exact (congrFun hd x).trans (congrFun hfeq x).symm
  have hext : ∀ d e : Diffeomorph T.smoothStructure.val R.smoothStructure.val,
      d.toEquiv = e.toEquiv → d = e := by
    intro d e h
    cases d
    cases e
    cases h
    rfl
  exact hext d e hfun

end SmoothManifolds.SmoothDescent
