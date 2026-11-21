import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SimplicialChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SimplicialRelativeParametrizations

/-! Assembly of paper.tex §T19's finite simplicial and Δ chain models.
The prerequisite proofs use the same canonical objects throughout: increasing
representatives for the oriented model, ordered simplex labels for Δ chains,
actual face-closed selections for pairs, and the shared singular chain complex.
These declarations expose their complete formulas and chain-map laws together.
No new order, topology, chain object, or quotient is introduced by assembly. -/

noncomputable section
universe u v w w' u_1
namespace P202.SimplicialChains

theorem Oriented.oriented_repeated : P202Specs.SimplicialChains.Oriented.oriented_repeated_type.{v, w} :=
  @P202.OrientedSimplicialAlgebra.oriented_repeated

theorem Oriented.oriented_permute : P202Specs.SimplicialChains.Oriented.oriented_permute_type.{v, w} :=
  @P202.OrientedSimplicialAlgebra.oriented_permute

theorem Oriented.oriented_increasing : P202Specs.SimplicialChains.Oriented.oriented_increasing_type.{v, w} :=
  @P202.OrientedSimplicialAlgebra.oriented_increasing

theorem Oriented.boundary_single : P202Specs.SimplicialChains.Oriented.boundary_single_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.boundary_single

theorem Oriented.boundary_oriented : P202Specs.SimplicialChains.Oriented.boundary_oriented_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.boundary_oriented

theorem Oriented.boundary_squared : P202Specs.SimplicialChains.Oriented.boundary_squared_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.boundary_squared

theorem Oriented.boundary_zero : P202Specs.SimplicialChains.Oriented.boundary_zero_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.boundary_zero

theorem Oriented.boundary_eq : P202Specs.SimplicialChains.Oriented.boundary_eq_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.boundary_eq

theorem Oriented.pushforward_single : P202Specs.SimplicialChains.Oriented.pushforward_single_type.{u, v, w, w'} :=
  @P202.OrientedSimplicialAlgebra.pushforward_single

theorem Oriented.pushforward_collapse : P202Specs.SimplicialChains.Oriented.pushforward_collapse_type.{u, v, w, w'} :=
  @P202.OrientedSimplicialAlgebra.pushforward_collapse

theorem Oriented.pushforward_oriented : P202Specs.SimplicialChains.Oriented.pushforward_oriented_type.{u, v, w, w'} :=
  @P202.OrientedSimplicialAlgebra.pushforward_oriented

theorem Oriented.pushforward_boundary : P202Specs.SimplicialChains.Oriented.pushforward_boundary_type.{u, v, w, w'} :=
  @P202.OrientedSimplicialAlgebra.pushforward_boundary

theorem Oriented.pushforward_id : P202Specs.SimplicialChains.Oriented.pushforward_id_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.pushforward_id

theorem Oriented.pushforward_comp : P202Specs.SimplicialChains.Oriented.pushforward_comp_type.{u, v, w, w', u_1} :=
  @P202.OrientedSimplicialAlgebra.pushforward_comp

theorem Oriented.pushforward_chainMap : P202Specs.SimplicialChains.Oriented.pushforward_chainMap_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.pushforward_chainMap

theorem Oriented.pushforward_inclusion_single : P202Specs.SimplicialChains.Oriented.pushforward_inclusion_single_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.pushforward_inclusion_single

theorem Oriented.pushforward_inclusion_injective : P202Specs.SimplicialChains.Oriented.pushforward_inclusion_injective_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.pushforward_inclusion_injective

theorem Oriented.increasingBasis_apply : P202Specs.SimplicialChains.Oriented.increasingBasis_apply_type.{u, w} :=
  @P202.OrientedSimplicialAlgebra.increasingBasis_apply

theorem Oriented.coefficientEquiv_single : P202Specs.SimplicialChains.Oriented.coefficientEquiv_single_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.coefficientEquiv_single

theorem Oriented.coefficientEquiv_tmul_single : P202Specs.SimplicialChains.Oriented.coefficientEquiv_tmul_single_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.coefficientEquiv_tmul_single

theorem Oriented.coefficientEquiv_boundary : P202Specs.SimplicialChains.Oriented.coefficientEquiv_boundary_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.coefficientEquiv_boundary

def Oriented.chainComplex : P202Specs.SimplicialChains.Oriented.chainComplex_type.{u, v, w} :=
  @P202.OrientedSimplicialAlgebra.chainComplex

def deltaChainComplex : P202Specs.SimplicialChains.deltaChainComplex_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaChainComplex

theorem deltaBoundary_zero : P202Specs.SimplicialChains.deltaBoundary_zero_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaBoundary_zero

theorem deltaBoundary_eq : P202Specs.SimplicialChains.deltaBoundary_eq_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaBoundary_eq

theorem deltaBoundary_single : P202Specs.SimplicialChains.deltaBoundary_single_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaBoundary_single

theorem deltaBoundary_squared : P202Specs.SimplicialChains.deltaBoundary_squared_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaBoundary_squared

theorem deltaCoefficientEquiv_single : P202Specs.SimplicialChains.deltaCoefficientEquiv_single_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaCoefficientEquiv_single

theorem deltaCoefficientEquiv_boundary : P202Specs.SimplicialChains.deltaCoefficientEquiv_boundary_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaCoefficientEquiv_boundary

theorem deltaSingularSimplex_face : P202Specs.SimplicialChains.deltaSingularSimplex_face_type.{w} :=
  @P202.RelativeParametrizations.deltaSingularSimplex_face

theorem deltaParametrizationLinear_single : P202Specs.SimplicialChains.deltaParametrizationLinear_single_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaParametrizationLinear_single

theorem deltaAffineChainMap : P202Specs.SimplicialChains.deltaAffineChainMap_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaAffineChainMap

theorem deltaPushforward_single : P202Specs.SimplicialChains.deltaPushforward_single_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaPushforward_single

theorem deltaPushforward_chainMap : P202Specs.SimplicialChains.deltaPushforward_chainMap_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaPushforward_chainMap

theorem Simplicial.parametrization_value : P202Specs.SimplicialChains.Simplicial.parametrization_value_type.{w} :=
  @P202.RelativeParametrizations.Simplicial.parametrization_value

theorem Simplicial.singularSimplex_face : P202Specs.SimplicialChains.Simplicial.singularSimplex_face_type.{w} :=
  @P202.RelativeParametrizations.Simplicial.singularSimplex_face

theorem Simplicial.affineLinear_single : P202Specs.SimplicialChains.Simplicial.affineLinear_single_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.affineLinear_single

theorem Simplicial.affineChainMap : P202Specs.SimplicialChains.Simplicial.affineChainMap_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.affineChainMap

theorem Quotient.inclusion_injective : P202Specs.SimplicialChains.Quotient.inclusion_injective_type.{u, w} :=
  @P202.RelativeParametrizations.Quotient.inclusion_injective

theorem Quotient.projection_surjective : P202Specs.SimplicialChains.Quotient.projection_surjective_type.{u, w} :=
  @P202.RelativeParametrizations.Quotient.projection_surjective

theorem Quotient.projection_kernel : P202Specs.SimplicialChains.Quotient.projection_kernel_type.{u, w} :=
  @P202.RelativeParametrizations.Quotient.projection_kernel

theorem Quotient.boundary_mk : P202Specs.SimplicialChains.Quotient.boundary_mk_type.{u, w} :=
  @P202.RelativeParametrizations.Quotient.boundary_mk

theorem Quotient.boundary_zero : P202Specs.SimplicialChains.Quotient.boundary_zero_type.{u, w} :=
  @P202.RelativeParametrizations.Quotient.boundary_zero

theorem Quotient.boundary_squared : P202Specs.SimplicialChains.Quotient.boundary_squared_type.{u, w} :=
  @P202.RelativeParametrizations.Quotient.boundary_squared

theorem Quotient.map_mk : P202Specs.SimplicialChains.Quotient.map_mk_type.{u, w} :=
  @P202.RelativeParametrizations.Quotient.map_mk

theorem singularSelection_range : P202Specs.SimplicialChains.singularSelection_range_type.{u, v, w} :=
  @P202.RelativeParametrizations.singularSelection_range

theorem deltaEmpty_module : P202Specs.SimplicialChains.deltaEmpty_module_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaEmpty_module

def deltaSelectedEquiv : P202Specs.SimplicialChains.deltaSelectedEquiv_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaSelectedEquiv

def deltaPairComplex : P202Specs.SimplicialChains.deltaPairComplex_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaPairComplex

theorem deltaRelativeBoundary_single : P202Specs.SimplicialChains.deltaRelativeBoundary_single_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaRelativeBoundary_single

theorem deltaAffine_preserves : P202Specs.SimplicialChains.deltaAffine_preserves_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaAffine_preserves

theorem deltaRelativeAffineChainMap : P202Specs.SimplicialChains.deltaRelativeAffineChainMap_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaRelativeAffineChainMap

theorem deltaInclusion : P202Specs.SimplicialChains.deltaInclusion_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaInclusion

theorem deltaPushforward_preserves : P202Specs.SimplicialChains.deltaPushforward_preserves_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaPushforward_preserves

theorem deltaRelativePushforward : P202Specs.SimplicialChains.deltaRelativePushforward_type.{u, v, w} :=
  @P202.RelativeParametrizations.deltaRelativePushforward

def Simplicial.pairComplex : P202Specs.SimplicialChains.Simplicial.pairComplex_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.pairComplex

theorem Simplicial.empty_module : P202Specs.SimplicialChains.Simplicial.empty_module_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.empty_module

theorem Simplicial.relativeBoundary_single : P202Specs.SimplicialChains.Simplicial.relativeBoundary_single_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.relativeBoundary_single

theorem Simplicial.parametrization_lands : P202Specs.SimplicialChains.Simplicial.parametrization_lands_type.{w} :=
  @P202.RelativeParametrizations.Simplicial.parametrization_lands

theorem Simplicial.affine_preserves : P202Specs.SimplicialChains.Simplicial.affine_preserves_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.affine_preserves

theorem Simplicial.relativeAffineChainMap : P202Specs.SimplicialChains.Simplicial.relativeAffineChainMap_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.relativeAffineChainMap

theorem Simplicial.inclusion_range : P202Specs.SimplicialChains.Simplicial.inclusion_range_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.inclusion_range

theorem Simplicial.inclusion_chainMap : P202Specs.SimplicialChains.Simplicial.inclusion_chainMap_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.inclusion_chainMap

theorem Simplicial.pushforward_preserves : P202Specs.SimplicialChains.Simplicial.pushforward_preserves_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.pushforward_preserves

theorem Simplicial.relativePushforward : P202Specs.SimplicialChains.Simplicial.relativePushforward_type.{u, v, w} :=
  @P202.RelativeParametrizations.Simplicial.relativePushforward

end P202.SimplicialChains
