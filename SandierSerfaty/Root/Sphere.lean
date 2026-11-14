/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Bridge.Input63
public import SandierSerfaty.Sphere.Bridge.Input63Field
public import SandierSerfaty.Sphere.Bridge.LogEnergy
public import SandierSerfaty.Sphere.Bridge.NeumannProjection
public import SandierSerfaty.Sphere.Bridge.Quadrants
public import SandierSerfaty.Sphere.Bridge.ReflectGlue
public import SandierSerfaty.Sphere.Bridge.RingConstant
public import SandierSerfaty.Sphere.Bridge.Transport
public import SandierSerfaty.Sphere.Bridge.TruncLogGreen
public import SandierSerfaty.Sphere.ChartDecay
public import SandierSerfaty.Sphere.ChartGreen
public import SandierSerfaty.Sphere.ChartIntegrable
public import SandierSerfaty.Sphere.ChartLaplacian
public import SandierSerfaty.Sphere.ChartPotential
public import SandierSerfaty.Sphere.Chordal
public import SandierSerfaty.Sphere.CutoffFamily
public import SandierSerfaty.Sphere.Defs
public import SandierSerfaty.Sphere.Density
public import SandierSerfaty.Sphere.GreenCutoff
public import SandierSerfaty.Sphere.GreenPlane
public import SandierSerfaty.Sphere.InversionChange
public import SandierSerfaty.Sphere.InversionDisc
public import SandierSerfaty.Sphere.InversionEnergy
public import SandierSerfaty.Sphere.LogPotential
public import SandierSerfaty.Sphere.Lower.AdmissibleSmul
public import SandierSerfaty.Sphere.Lower.Apriori
public import SandierSerfaty.Sphere.Lower.BlowupLaplacian
public import SandierSerfaty.Sphere.Lower.BlowupWeak
public import SandierSerfaty.Sphere.Lower.CellData
public import SandierSerfaty.Sphere.Lower.CellFamily
public import SandierSerfaty.Sphere.Lower.CellSums
public import SandierSerfaty.Sphere.Lower.ChartAgg
public import SandierSerfaty.Sphere.Lower.ChartAlgebra
public import SandierSerfaty.Sphere.Lower.ChartLarge
public import SandierSerfaty.Sphere.Lower.ChartLargeError
public import SandierSerfaty.Sphere.Lower.ChartLower
public import SandierSerfaty.Sphere.Lower.ChartLowerBound
public import SandierSerfaty.Sphere.Lower.ChartLowerFinal
public import SandierSerfaty.Sphere.Lower.ChartPartition
public import SandierSerfaty.Sphere.Lower.ChartPartitionAux
public import SandierSerfaty.Sphere.Lower.ChartSetup
public import SandierSerfaty.Sphere.Lower.ChartTruncation
public import SandierSerfaty.Sphere.Lower.ChooseRadius
public import SandierSerfaty.Sphere.Lower.Constants
public import SandierSerfaty.Sphere.Lower.Counting
public import SandierSerfaty.Sphere.Lower.Cutoff
public import SandierSerfaty.Sphere.Lower.DensityFreeze
public import SandierSerfaty.Sphere.Lower.Discrepancy
public import SandierSerfaty.Sphere.Lower.DiscrepancyAux
public import SandierSerfaty.Sphere.Lower.GoodCell
public import SandierSerfaty.Sphere.Lower.GoodSquare
public import SandierSerfaty.Sphere.Lower.GoodSquareAlg
public import SandierSerfaty.Sphere.Lower.GoodSquareAux
public import SandierSerfaty.Sphere.Lower.GoodSquareWeak
public import SandierSerfaty.Sphere.Lower.GridCounting
public import SandierSerfaty.Sphere.Lower.GridFamily
public import SandierSerfaty.Sphere.Lower.GridOffset
public import SandierSerfaty.Sphere.Lower.GridSelect
public import SandierSerfaty.Sphere.Lower.GridStrips
public import SandierSerfaty.Sphere.Lower.LipschitzWeak
public import SandierSerfaty.Sphere.Lower.LogKernel
public import SandierSerfaty.Sphere.Lower.LogWindow
public import SandierSerfaty.Sphere.Lower.LowerBound
public import SandierSerfaty.Sphere.Lower.Neumann
public import SandierSerfaty.Sphere.Lower.Pigeonhole
public import SandierSerfaty.Sphere.Lower.Quantize
public import SandierSerfaty.Sphere.Lower.ReflectBasic
public import SandierSerfaty.Sphere.Lower.ReflectDomain
public import SandierSerfaty.Sphere.Lower.ReflectEnergy
public import SandierSerfaty.Sphere.Lower.ReflectInvariance
public import SandierSerfaty.Sphere.Lower.ReflectLimit
public import SandierSerfaty.Sphere.Lower.ReflectPotential
public import SandierSerfaty.Sphere.Lower.Reflection
public import SandierSerfaty.Sphere.Lower.RestCount
public import SandierSerfaty.Sphere.Lower.SquareData
public import SandierSerfaty.Sphere.Lower.Statements
public import SandierSerfaty.Sphere.Lower.TruncIntegrable
public import SandierSerfaty.Sphere.Lower.TruncPotential
public import SandierSerfaty.Sphere.Lower.TwoChartAssemble
public import SandierSerfaty.Sphere.Lower.WallDist
public import SandierSerfaty.Sphere.Minimizer
public import SandierSerfaty.Sphere.Puncture
public import SandierSerfaty.Sphere.PunctureLimit
public import SandierSerfaty.Sphere.PunctureLocal
public import SandierSerfaty.Sphere.PunctureSplit
public import SandierSerfaty.Sphere.RadialGreen
public import SandierSerfaty.Sphere.Ring.Aspect
public import SandierSerfaty.Sphere.Ring.Band
public import SandierSerfaty.Sphere.Ring.BandBound
public import SandierSerfaty.Sphere.Ring.Bands
public import SandierSerfaty.Sphere.Ring.Barycentre
public import SandierSerfaty.Sphere.Ring.Cell
public import SandierSerfaty.Sphere.Ring.Construction
public import SandierSerfaty.Sphere.Ring.Count
public import SandierSerfaty.Sphere.Ring.Depth
public import SandierSerfaty.Sphere.Ring.Geometry
public import SandierSerfaty.Sphere.Ring.Identity
public import SandierSerfaty.Sphere.Ring.InBand
public import SandierSerfaty.Sphere.Ring.MinBound
public import SandierSerfaty.Sphere.Ring.OnSphere
public import SandierSerfaty.Sphere.Ring.PerRow
public import SandierSerfaty.Sphere.Ring.PerRowBand
public import SandierSerfaty.Sphere.Ring.Polar
public import SandierSerfaty.Sphere.Ring.RingBound
public import SandierSerfaty.Sphere.Ring.RingConstant
public import SandierSerfaty.Sphere.Ring.RowSum
public import SandierSerfaty.Sphere.Ring.Rows
public import SandierSerfaty.Sphere.Ring.Slab
public import SandierSerfaty.Sphere.Ring.Spacing
public import SandierSerfaty.Sphere.Ring.Theta
public import SandierSerfaty.Sphere.Ring.UpperBound
public import SandierSerfaty.Sphere.Scaling
public import SandierSerfaty.Sphere.Separation
public import SandierSerfaty.Sphere.SeparationAverage
public import SandierSerfaty.Sphere.SeparationChart
public import SandierSerfaty.Sphere.Splitting
public import SandierSerfaty.Sphere.TruncCenter
public import SandierSerfaty.Sphere.TruncIdentity
public import SandierSerfaty.Sphere.TruncShift
public import SandierSerfaty.Sphere.TruncationIdentity
public import SandierSerfaty.Sphere.TwoChart

/-!
# Root part

Part of the generated root `SandierSerfaty.lean`. It imports the modules of one area of the library (the imports
above), except those that the root skips. It is generated; do not edit it by hand, and never import it.
-/

public section
