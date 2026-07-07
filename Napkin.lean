import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Lint
import Napkin.Frontmatter.Colophon
import Napkin.Frontmatter.Preface
import Napkin.Frontmatter.Advice
import Napkin.Frontmatter.SalesPitches
import Napkin.StartingOut.Groups
import Napkin.StartingOut.MetricSpaces
import Napkin.BasicTopology.MetricProperties
import Napkin.BasicTopology.TopologicalSpaces
import Napkin.BasicTopology.Compactness
import Napkin.AbstractAlgebra.Quotient
import Napkin.AbstractAlgebra.Rings
import Napkin.AbstractAlgebra.Flavors
import Napkin.LinearAlgebra.VectorSpaces
import Napkin.LinearAlgebra.Eigenthings
import Napkin.LinearAlgebra.DualTrace
import Napkin.LinearAlgebra.Determinant
import Napkin.LinearAlgebra.InnerProduct
import Napkin.LinearAlgebra.Fourier
import Napkin.LinearAlgebra.Adjoints
import Napkin.MoreOnGroups.GroupActions
import Napkin.MoreOnGroups.Sylow
import Napkin.MoreOnGroups.PIDStructure
import Napkin.RepresentationTheory.RepAlgebras
import Napkin.RepresentationTheory.Semisimple
import Napkin.RepresentationTheory.Characters
import Napkin.RepresentationTheory.Applications
import Napkin.Quantum.Vectors
import Napkin.Quantum.Circuits
import Napkin.Quantum.Shor
import Napkin.Calculus.Limits
import Napkin.Calculus.PAdic
import Napkin.Calculus.Differentiate
import Napkin.Calculus.Taylor
import Napkin.Calculus.Integrate
import Napkin.ComplexAnalysis.Holomorphic
import Napkin.ComplexAnalysis.Meromorphic
import Napkin.ComplexAnalysis.Log
import Napkin.ComplexAnalysis.Quintic
import Napkin.MeasureTheory.MeasureSpace
import Napkin.MeasureTheory.Caratheodory
import Napkin.MeasureTheory.LebesgueInt
import Napkin.MeasureTheory.SwapSum
import Napkin.MeasureTheory.Pontryagin
import Napkin.Probability.RandomVariables
import Napkin.Probability.LargeLaws
import Napkin.Probability.Martingales
import Napkin.DifferentialGeometry.Multivariable
import Napkin.DifferentialGeometry.Forms
import Napkin.DifferentialGeometry.Stokes
import Napkin.DifferentialGeometry.Manifolds
import Napkin.RiemannSurfaces.ComplexStructure
import Napkin.RiemannSurfaces.Morphisms
import Napkin.RiemannSurfaces.AffineProjective
import Napkin.RiemannSurfaces.Forms
import Napkin.RiemannSurfaces.RiemannRoch
import Napkin.RiemannSurfaces.LineBundles
import Napkin.AlgebraicNT.AlgebraicIntegers
import Napkin.AlgebraicNT.NormTrace
import Napkin.AlgebraicNT.Dedekind
import Napkin.AlgebraicNT.ClassGroup
import Napkin.AlgebraicNT.Discriminant
import Napkin.AlgebraicNT.Pell
import Napkin.AlgebraicNT.Galois
import Napkin.AlgebraicNT.FiniteFields
import Napkin.AlgebraicNT.Ramification
import Napkin.AlgebraicNT.FrobeniusElements
import Napkin.Backmatter.References

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "An Infinitely Large Napkin" =>

%%%
authors := ["Evan Chen"]
authorshipNote := "Lean preparation by Julian."
htmlToc := false
%%%

:::subtitle
A Lean Companion
:::

![Cover artwork](cover-art.jpg)

{include 1 Napkin.Frontmatter.Colophon}

{include 1 Napkin.Frontmatter.Preface}

{include 1 Napkin.Frontmatter.Advice}

# Starting Out

%%%
file := "Starting-Out"
%%%

{include 2 Napkin.Frontmatter.SalesPitches}

{include 2 Napkin.StartingOut.Groups}

{include 2 Napkin.StartingOut.MetricSpaces}

# Basic Abstract Algebra

%%%
file := "Basic-Abstract-Algebra"
%%%

{include 2 Napkin.AbstractAlgebra.Quotient}

{include 2 Napkin.AbstractAlgebra.Rings}

{include 2 Napkin.AbstractAlgebra.Flavors}

# Basic Topology

%%%
file := "Basic-Topology"
%%%

{include 2 Napkin.BasicTopology.MetricProperties}

{include 2 Napkin.BasicTopology.TopologicalSpaces}

{include 2 Napkin.BasicTopology.Compactness}

# Linear Algebra

%%%
file := "Linear-Algebra"
%%%

{include 2 Napkin.LinearAlgebra.VectorSpaces}

{include 2 Napkin.LinearAlgebra.Eigenthings}

{include 2 Napkin.LinearAlgebra.DualTrace}

{include 2 Napkin.LinearAlgebra.Determinant}

{include 2 Napkin.LinearAlgebra.InnerProduct}

{include 2 Napkin.LinearAlgebra.Fourier}

{include 2 Napkin.LinearAlgebra.Adjoints}

# More on Groups

%%%
file := "More-on-Groups"
%%%

{include 2 Napkin.MoreOnGroups.GroupActions}

{include 2 Napkin.MoreOnGroups.Sylow}

{include 2 Napkin.MoreOnGroups.PIDStructure}

# Representation Theory

%%%
file := "Representation-Theory"
%%%

{include 2 Napkin.RepresentationTheory.RepAlgebras}

{include 2 Napkin.RepresentationTheory.Semisimple}

{include 2 Napkin.RepresentationTheory.Characters}

{include 2 Napkin.RepresentationTheory.Applications}

# Quantum Algorithms

%%%
file := "Quantum-Algorithms"
%%%

{include 2 Napkin.Quantum.Vectors}

{include 2 Napkin.Quantum.Circuits}

{include 2 Napkin.Quantum.Shor}

# Calculus 101

%%%
file := "Calculus-101"
%%%

{include 2 Napkin.Calculus.Limits}

{include 2 Napkin.Calculus.PAdic}

{include 2 Napkin.Calculus.Differentiate}

{include 2 Napkin.Calculus.Taylor}

{include 2 Napkin.Calculus.Integrate}

# Complex Analysis

%%%
file := "Complex-Analysis"
%%%

{include 2 Napkin.ComplexAnalysis.Holomorphic}

{include 2 Napkin.ComplexAnalysis.Meromorphic}

{include 2 Napkin.ComplexAnalysis.Log}

{include 2 Napkin.ComplexAnalysis.Quintic}

# Measure Theory

%%%
file := "Measure-Theory"
%%%

{include 2 Napkin.MeasureTheory.MeasureSpace}

{include 2 Napkin.MeasureTheory.Caratheodory}

{include 2 Napkin.MeasureTheory.LebesgueInt}

{include 2 Napkin.MeasureTheory.SwapSum}

{include 2 Napkin.MeasureTheory.Pontryagin}

# Probability

%%%
file := "Probability"
%%%

{include 2 Napkin.Probability.RandomVariables}

{include 2 Napkin.Probability.LargeLaws}

{include 2 Napkin.Probability.Martingales}

# Differential Geometry

%%%
file := "Differential-Geometry"
%%%

{include 2 Napkin.DifferentialGeometry.Multivariable}

{include 2 Napkin.DifferentialGeometry.Forms}

{include 2 Napkin.DifferentialGeometry.Stokes}

{include 2 Napkin.DifferentialGeometry.Manifolds}

# Riemann Surfaces

%%%
file := "Riemann-Surfaces"
%%%

{include 2 Napkin.RiemannSurfaces.ComplexStructure}

{include 2 Napkin.RiemannSurfaces.Morphisms}

{include 2 Napkin.RiemannSurfaces.AffineProjective}

{include 2 Napkin.RiemannSurfaces.Forms}

{include 2 Napkin.RiemannSurfaces.RiemannRoch}

{include 2 Napkin.RiemannSurfaces.LineBundles}

# Algebraic NT I: Rings of Integers

%%%
file := "Algebraic-Number-Theory-I"
%%%

{include 2 Napkin.AlgebraicNT.AlgebraicIntegers}

{include 2 Napkin.AlgebraicNT.NormTrace}

{include 2 Napkin.AlgebraicNT.Dedekind}

{include 2 Napkin.AlgebraicNT.ClassGroup}

{include 2 Napkin.AlgebraicNT.Discriminant}

{include 2 Napkin.AlgebraicNT.Pell}

# Algebraic NT II: Galois and Ramification Theory

%%%
file := "Algebraic-Number-Theory-II"
%%%

{include 2 Napkin.AlgebraicNT.Galois}

{include 2 Napkin.AlgebraicNT.FiniteFields}

{include 2 Napkin.AlgebraicNT.Ramification}

{include 2 Napkin.AlgebraicNT.FrobeniusElements}

# Backmatter

%%%
number := false
%%%

{include 2 Napkin.Backmatter.References}
