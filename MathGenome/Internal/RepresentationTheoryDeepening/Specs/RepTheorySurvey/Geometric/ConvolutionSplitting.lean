import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedLocalSheaves

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace

namespace RepTheorySurvey.Geometric.ConvolutionSplittingSpecs

open Analytic LocalSheaf
open ConvolutionUnitConeSpecs

/-- The open two-dimensional orbit of the terminal-lattice surface. -/
def openOrbitStratum (x : surface) (hx : IsClosed ({x} : Set surface)) : Stratum surface where
  ambientOpen := complementOpen {x} hx
  subset := Set.univ
  closed := isClosed_univ
  complexDimension := 2

/-- The closed zero-dimensional orbit of the terminal-lattice surface. -/
def closedOrbitStratum (x : surface) (hx : IsClosed ({x} : Set surface)) : Stratum surface where
  ambientOpen := ⊤
  subset := Subtype.val ⁻¹' {x}
  closed := hx.preimage continuous_subtype_val
  complexDimension := 0

theorem openOrbitStratum_range (x : surface) (hx : IsClosed ({x} : Set surface)) :
    Set.range (openOrbitStratum x hx).inclusion = ({x} : Set surface)ᶜ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.val.property
  · intro hy
    exact ⟨⟨⟨y, hy⟩, Set.mem_univ _⟩, rfl⟩

theorem closedOrbitStratum_range (x : surface) (hx : IsClosed ({x} : Set surface)) :
    Set.range (closedOrbitStratum x hx).inclusion = {x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact z.property
  · intro hy
    exact ⟨⟨⟨y, Set.mem_univ _⟩, hy⟩, rfl⟩

/-- The two orbit strata in the analytic scheme model used by the unit triangle. -/
def orbitStratification (x : surface) (hx : IsClosed ({x} : Set surface)) :
    Stratification surface where
  Index := Bool
  stratum b := if b then openOrbitStratum x hx else closedOrbitStratum x hx
  partition y := by
    have hopen : y ∈ Set.range (openOrbitStratum x hx).inclusion ↔
        y ∉ ({x} : Set surface) := by rw [openOrbitStratum_range]; rfl
    have hclosed : y ∈ Set.range (closedOrbitStratum x hx).inclusion ↔
        y ∈ ({x} : Set surface) := by rw [closedOrbitStratum_range]
    by_cases hy : y ∈ ({x} : Set surface)
    · refine ⟨false, hclosed.mpr hy, ?_⟩
      rintro (_ | _) hb
      · rfl
      · exact (hopen.mp hb hy).elim
    · refine ⟨true, hopen.mpr hy, ?_⟩
      rintro (_ | _) hb
      · exact (hy (hclosed.mp hb)).elim
      · rfl

/-- Cohomology of the actual extraordinary inverse image of the unshifted
rational constant sheaf, evaluated at the unique point of its domain. -/
abbrev pointCostalk (x : surface) (hx : IsClosed ({x} : Set surface)) (q : ℤ) : Coeff.{0} :=
  (DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk (⟨x, rfl⟩ : ({x} : Set surface))).obj
    ((derivedExtraordinaryInverseImage hx).obj (sheafInDegreeZero (rational surface)))

/-- The Hom group from the skyscraper to the shifted constant sheaf, with its
identification with the unshifted costalk cohomology and its vanishing. -/
def VanishingCostalkHom (x : surface) (hx : IsClosed ({x} : Set surface)) (d : ℕ) : Prop :=
  let Hom := pointSkyscraper x hx ⟶ (IntersectionComplex.shiftedConstant surface d).obj
  Nonempty (Hom ≃+ pointCostalk x hx (d : ℤ)) ∧
    IsZero (pointCostalk x hx (d : ℤ)) ∧ Subsingleton Hom

/-- The quotient map obtained from the fixed unit triangle and the chosen
identification of its cone with the rational skyscraper. -/
abbrev quotientMap {x : surface} {hx : IsClosed ({x} : Set surface)}
    (e : unitCone ≅ pointSkyscraper x hx) : convolution.obj ⟶ pointSkyscraper x hx :=
  unitTriangle.mor₂ ≫ e.hom

/-- The section is unique for this identification. Together with the
unit it gives the two components of the splitting isomorphism. -/
def SplittingFor {x : surface} {hx : IsClosed ({x} : Set surface)}
    (e : unitCone ≅ pointSkyscraper x hx) : Prop :=
  ∃ s : pointSkyscraper x hx ⟶ convolution.obj,
    s ≫ quotientMap e = 𝟙 _ ∧
    (∀ s' : pointSkyscraper x hx ⟶ convolution.obj, s' ≫ quotientMap e = 𝟙 _ → s' = s) ∧
    ∃ f : ((IntersectionComplex.shiftedConstant surface 2).obj ⊞ pointSkyscraper x hx) ≅
        convolution.obj,
      biprod.inl ≫ f.hom = unit ∧ biprod.inr ≫ f.hom = s

namespace Expected

/-- The ordinary derived splitting on the terminal-lattice surface and the
middle-perverse bounds of the two summands and their convolution. -/
def ConvolutionSplitting : Prop :=
  ∃ (x : surface) (hx : IsClosed ({x} : Set surface)),
    ConvolutionSurfaceSpecs.ScalarTerminalPoint x ∧
    Nonempty (unitCone ≅ pointSkyscraper x hx) ∧
    VanishingCostalkHom x hx 2 ∧ VanishingCostalkHom x hx 3 ∧
    unitTriangle.mor₃ = 0 ∧
    (∀ e : unitCone ≅ pointSkyscraper x hx, SplittingFor e) ∧
    IsMiddlePerverse (orbitStratification x hx) (IntersectionComplex.shiftedConstant surface 2).obj ∧
    IsMiddlePerverse (orbitStratification x hx) (pointSkyscraper x hx) ∧
    IsMiddlePerverse (orbitStratification x hx) convolution.obj

end Expected
end RepTheorySurvey.Geometric.ConvolutionSplittingSpecs
