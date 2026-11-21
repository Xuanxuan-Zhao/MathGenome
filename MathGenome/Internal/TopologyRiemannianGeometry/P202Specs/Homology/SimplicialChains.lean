import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SimplicialRelativeParametrizations

/-! The chain constructions of paper.tex §T19, assembled on the canonical
objects of the two prerequisite interfaces. All chains have finite support;
coefficients are arbitrary modules over a commutative unital ring. The chosen
vertex order exists for every vertex type. Both realization topologies are the
weak topologies of Definition 2.1, and every face index contributes separately.

The expected propositions below are transparent aliases of full independent
Specs. This file imports no candidate implementation and assumes no certificate.
The homology comparison theorem is a separate obligation. -/

noncomputable section
universe u v w w' u_1
namespace P202Specs.SimplicialChains

/-- Canonical ordered Δ chains and the shared relative quotient construction. -/
abbrev DeltaChains := @P202Specs.RelativeParametrizations.DeltaChains
abbrev deltaCoefficientEquiv := @P202Specs.RelativeParametrizations.deltaCoefficientEquiv
abbrev deltaFace := @P202Specs.RelativeParametrizations.deltaFace
abbrev deltaBoundary := @P202Specs.RelativeParametrizations.deltaBoundary
abbrev deltaFace_comp := @P202Specs.RelativeParametrizations.deltaFace_comp
abbrev deltaComplex := @P202Specs.RelativeParametrizations.deltaComplex
abbrev deltaParametrization := @P202Specs.RelativeParametrizations.deltaParametrization
abbrev deltaSingularSimplex := @P202Specs.RelativeParametrizations.deltaSingularSimplex
abbrev deltaParametrizationLinear := @P202Specs.RelativeParametrizations.deltaParametrizationLinear
abbrev ChainSelection := @P202Specs.RelativeParametrizations.ChainSelection
abbrev DeltaSubcomplex := @P202Specs.RelativeParametrizations.DeltaSubcomplex
abbrev DeltaMap := @P202Specs.RelativeParametrizations.DeltaMap
abbrev deltaPushforward := @P202Specs.RelativeParametrizations.deltaPushforward
abbrev deltaSelection := @P202Specs.RelativeParametrizations.deltaSelection
abbrev deltaRelativeComplex := @P202Specs.RelativeParametrizations.deltaRelativeComplex
abbrev singularSelection := @P202Specs.RelativeParametrizations.singularSelection
abbrev subspaceInclusion := @P202Specs.RelativeParametrizations.subspaceInclusion
abbrev singularRelativeComplex := @P202Specs.RelativeParametrizations.singularRelativeComplex

/-- The oriented model uses exactly the prerequisite increasing representatives. -/
abbrev Oriented.vertexOrder := @P202Specs.OrientedSimplicialAlgebra.vertexOrder
abbrev Oriented.Simplex := @P202Specs.OrientedSimplicialAlgebra.Simplex
abbrev Oriented.UnorderedSimplex := @P202Specs.OrientedSimplicialAlgebra.UnorderedSimplex
abbrev Oriented.simplexEquiv := @P202Specs.OrientedSimplicialAlgebra.simplexEquiv
abbrev Oriented.VertexTuple := @P202Specs.OrientedSimplicialAlgebra.VertexTuple
abbrev Oriented.Chains := @P202Specs.OrientedSimplicialAlgebra.Chains
abbrev Oriented.face := @P202Specs.OrientedSimplicialAlgebra.face
abbrev Oriented.sorted := @P202Specs.OrientedSimplicialAlgebra.sorted
abbrev Oriented.permute := @P202Specs.OrientedSimplicialAlgebra.permute
abbrev Oriented.tupleFace := @P202Specs.OrientedSimplicialAlgebra.tupleFace
abbrev Oriented.increasingBasis := @P202Specs.OrientedSimplicialAlgebra.increasingBasis
abbrev Oriented.coefficientEquiv := @P202Specs.OrientedSimplicialAlgebra.coefficientEquiv
abbrev Oriented.oriented := @P202Specs.OrientedSimplicialAlgebra.oriented
abbrev Oriented.boundary := @P202Specs.OrientedSimplicialAlgebra.boundary
abbrev Oriented.complex := @P202Specs.OrientedSimplicialAlgebra.complex
abbrev Oriented.SimplicialMap := @P202Specs.OrientedSimplicialAlgebra.SimplicialMap
abbrev Oriented.inclusionSimplex := @P202Specs.OrientedSimplicialAlgebra.inclusionSimplex
abbrev Oriented.pushforward := @P202Specs.OrientedSimplicialAlgebra.pushforward

abbrev Simplicial.parametrization := @P202Specs.RelativeParametrizations.Simplicial.parametrization
abbrev Simplicial.singularSimplex := @P202Specs.RelativeParametrizations.Simplicial.singularSimplex
abbrev Simplicial.affineLinear := @P202Specs.RelativeParametrizations.Simplicial.affineLinear
abbrev Simplicial.Subcomplex := @P202Specs.RelativeParametrizations.Simplicial.Subcomplex
abbrev Simplicial.selection := @P202Specs.RelativeParametrizations.Simplicial.selection
abbrev Simplicial.relativeComplex := @P202Specs.RelativeParametrizations.Simplicial.relativeComplex

/-! Full expected types and canonical values for the assembly bindings. -/

abbrev Oriented.oriented_repeated_type := P202Specs.OrientedSimplicialAlgebra.oriented_repeated_type.{v, w}
abbrev Oriented.oriented_permute_type := P202Specs.OrientedSimplicialAlgebra.oriented_permute_type.{v, w}
abbrev Oriented.oriented_increasing_type := P202Specs.OrientedSimplicialAlgebra.oriented_increasing_type.{v, w}
abbrev Oriented.boundary_single_type := P202Specs.OrientedSimplicialAlgebra.boundary_single_type.{u, v, w}
abbrev Oriented.boundary_oriented_type := P202Specs.OrientedSimplicialAlgebra.boundary_oriented_type.{u, v, w}
abbrev Oriented.boundary_squared_type := P202Specs.OrientedSimplicialAlgebra.boundary_squared_type.{u, v, w}
abbrev Oriented.boundary_zero_type := P202Specs.OrientedSimplicialAlgebra.boundary_zero_type.{u, v, w}
abbrev Oriented.boundary_eq_type := P202Specs.OrientedSimplicialAlgebra.boundary_eq_type.{u, v, w}
abbrev Oriented.pushforward_single_type := P202Specs.OrientedSimplicialAlgebra.pushforward_single_type.{u, v, w, w'}
abbrev Oriented.pushforward_collapse_type := P202Specs.OrientedSimplicialAlgebra.pushforward_collapse_type.{u, v, w, w'}
abbrev Oriented.pushforward_oriented_type := P202Specs.OrientedSimplicialAlgebra.pushforward_oriented_type.{u, v, w, w'}
abbrev Oriented.pushforward_boundary_type := P202Specs.OrientedSimplicialAlgebra.pushforward_boundary_type.{u, v, w, w'}
abbrev Oriented.pushforward_id_type := P202Specs.OrientedSimplicialAlgebra.pushforward_id_type.{u, v, w}
abbrev Oriented.pushforward_comp_type := P202Specs.OrientedSimplicialAlgebra.pushforward_comp_type.{u, v, w, w', u_1}
abbrev Oriented.pushforward_chainMap_type := P202Specs.OrientedSimplicialAlgebra.pushforward_chainMap_type.{u, v, w}
abbrev Oriented.pushforward_inclusion_single_type := P202Specs.OrientedSimplicialAlgebra.pushforward_inclusion_single_type.{u, v, w}
abbrev Oriented.pushforward_inclusion_injective_type := P202Specs.OrientedSimplicialAlgebra.pushforward_inclusion_injective_type.{u, v, w}
abbrev Oriented.increasingBasis_apply_type := P202Specs.OrientedSimplicialAlgebra.increasingBasis_apply_type.{u, w}
abbrev Oriented.coefficientEquiv_single_type := P202Specs.OrientedSimplicialAlgebra.coefficientEquiv_single_type.{u, v, w}
abbrev Oriented.coefficientEquiv_tmul_single_type := P202Specs.OrientedSimplicialAlgebra.coefficientEquiv_tmul_single_type.{u, v, w}
abbrev Oriented.coefficientEquiv_boundary_type := P202Specs.OrientedSimplicialAlgebra.coefficientEquiv_boundary_type.{u, v, w}
abbrev Oriented.chainComplex_type := P202Specs.OrientedSimplicialAlgebra.chainComplex_type.{u, v, w}
abbrev Oriented.chainComplex_value := @P202Specs.OrientedSimplicialAlgebra.chainComplex_value.{u, v, w}
abbrev deltaChainComplex_type := P202Specs.RelativeParametrizations.Expected.deltaChainComplex_type.{u, v, w}
abbrev deltaChainComplex_value := @P202Specs.RelativeParametrizations.Expected.deltaChainComplex_value.{u, v, w}
abbrev deltaBoundary_zero_type := P202Specs.RelativeParametrizations.Expected.deltaBoundary_zero_type.{u, v, w}
abbrev deltaBoundary_eq_type := P202Specs.RelativeParametrizations.Expected.deltaBoundary_eq_type.{u, v, w}
abbrev deltaBoundary_single_type := P202Specs.RelativeParametrizations.Expected.deltaBoundary_single_type.{u, v, w}
abbrev deltaBoundary_squared_type := P202Specs.RelativeParametrizations.Expected.deltaBoundary_squared_type.{u, v, w}
abbrev deltaCoefficientEquiv_single_type := P202Specs.RelativeParametrizations.Expected.deltaCoefficientEquiv_single_type.{u, v, w}
abbrev deltaCoefficientEquiv_boundary_type := P202Specs.RelativeParametrizations.Expected.deltaCoefficientEquiv_boundary_type.{u, v, w}
abbrev deltaSingularSimplex_face_type := P202Specs.RelativeParametrizations.Expected.deltaSingularSimplex_face_type.{w}
abbrev deltaParametrizationLinear_single_type := P202Specs.RelativeParametrizations.Expected.deltaParametrizationLinear_single_type.{u, v, w}
abbrev deltaAffineChainMap_type := P202Specs.RelativeParametrizations.Expected.deltaAffineChainMap_type.{u, v, w}
abbrev deltaPushforward_single_type := P202Specs.RelativeParametrizations.Expected.deltaPushforward_single_type.{u, v, w}
abbrev deltaPushforward_chainMap_type := P202Specs.RelativeParametrizations.Expected.deltaPushforward_chainMap_type.{u, v, w}
abbrev Simplicial.parametrization_value_type := P202Specs.RelativeParametrizations.Expected.Simplicial.parametrization_value_type.{w}
abbrev Simplicial.singularSimplex_face_type := P202Specs.RelativeParametrizations.Expected.Simplicial.singularSimplex_face_type.{w}
abbrev Simplicial.affineLinear_single_type := P202Specs.RelativeParametrizations.Expected.Simplicial.affineLinear_single_type.{u, v, w}
abbrev Simplicial.affineChainMap_type := P202Specs.RelativeParametrizations.Expected.Simplicial.affineChainMap_type.{u, v, w}
abbrev Quotient.inclusion_injective_type := P202Specs.RelativeParametrizations.Expected.Quotient.inclusion_injective_type.{u, w}
abbrev Quotient.projection_surjective_type := P202Specs.RelativeParametrizations.Expected.Quotient.projection_surjective_type.{u, w}
abbrev Quotient.projection_kernel_type := P202Specs.RelativeParametrizations.Expected.Quotient.projection_kernel_type.{u, w}
abbrev Quotient.boundary_mk_type := P202Specs.RelativeParametrizations.Expected.Quotient.boundary_mk_type.{u, w}
abbrev Quotient.boundary_zero_type := P202Specs.RelativeParametrizations.Expected.Quotient.boundary_zero_type.{u, w}
abbrev Quotient.boundary_squared_type := P202Specs.RelativeParametrizations.Expected.Quotient.boundary_squared_type.{u, w}
abbrev Quotient.map_mk_type := P202Specs.RelativeParametrizations.Expected.Quotient.map_mk_type.{u, w}
abbrev singularSelection_range_type := P202Specs.RelativeParametrizations.Expected.singularSelection_range_type.{u, v, w}
abbrev deltaEmpty_module_type := P202Specs.RelativeParametrizations.Expected.deltaEmpty_module_type.{u, v, w}
abbrev deltaSelectedEquiv_type := P202Specs.RelativeParametrizations.Expected.deltaSelectedEquiv_type.{u, v, w}
abbrev deltaSelectedEquiv_value := @P202Specs.RelativeParametrizations.Expected.deltaSelectedEquiv_value.{u, v, w}
abbrev deltaPairComplex_type := P202Specs.RelativeParametrizations.Expected.deltaPairComplex_type.{u, v, w}
abbrev deltaPairComplex_value := @P202Specs.RelativeParametrizations.Expected.deltaPairComplex_value.{u, v, w}
abbrev deltaRelativeBoundary_single_type := P202Specs.RelativeParametrizations.Expected.deltaRelativeBoundary_single_type.{u, v, w}
abbrev deltaAffine_preserves_type := P202Specs.RelativeParametrizations.Expected.deltaAffine_preserves_type.{u, v, w}
abbrev deltaRelativeAffineChainMap_type := P202Specs.RelativeParametrizations.Expected.deltaRelativeAffineChainMap_type.{u, v, w}
abbrev deltaInclusion_type := P202Specs.RelativeParametrizations.Expected.deltaInclusion_type.{u, v, w}
abbrev deltaPushforward_preserves_type := P202Specs.RelativeParametrizations.Expected.deltaPushforward_preserves_type.{u, v, w}
abbrev deltaRelativePushforward_type := P202Specs.RelativeParametrizations.Expected.deltaRelativePushforward_type.{u, v, w}
abbrev Simplicial.pairComplex_type := P202Specs.RelativeParametrizations.Expected.Simplicial.pairComplex_type.{u, v, w}
abbrev Simplicial.pairComplex_value := @P202Specs.RelativeParametrizations.Expected.Simplicial.pairComplex_value.{u, v, w}
abbrev Simplicial.empty_module_type := P202Specs.RelativeParametrizations.Expected.Simplicial.empty_module_type.{u, v, w}
abbrev Simplicial.relativeBoundary_single_type := P202Specs.RelativeParametrizations.Expected.Simplicial.relativeBoundary_single_type.{u, v, w}
abbrev Simplicial.parametrization_lands_type := P202Specs.RelativeParametrizations.Expected.Simplicial.parametrization_lands_type.{w}
abbrev Simplicial.affine_preserves_type := P202Specs.RelativeParametrizations.Expected.Simplicial.affine_preserves_type.{u, v, w}
abbrev Simplicial.relativeAffineChainMap_type := P202Specs.RelativeParametrizations.Expected.Simplicial.relativeAffineChainMap_type.{u, v, w}
abbrev Simplicial.inclusion_range_type := P202Specs.RelativeParametrizations.Expected.Simplicial.inclusion_range_type.{u, v, w}
abbrev Simplicial.inclusion_chainMap_type := P202Specs.RelativeParametrizations.Expected.Simplicial.inclusion_chainMap_type.{u, v, w}
abbrev Simplicial.pushforward_preserves_type := P202Specs.RelativeParametrizations.Expected.Simplicial.pushforward_preserves_type.{u, v, w}
abbrev Simplicial.relativePushforward_type := P202Specs.RelativeParametrizations.Expected.Simplicial.relativePushforward_type.{u, v, w}

end P202Specs.SimplicialChains
