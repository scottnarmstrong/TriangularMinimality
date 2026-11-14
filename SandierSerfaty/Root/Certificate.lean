/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.Examples
public import SandierSerfaty.Certificate.Arith.Fx
public import SandierSerfaty.Certificate.Arith.FxLemmas
public import SandierSerfaty.Certificate.Arith.IV
public import SandierSerfaty.Certificate.Arith.IVLemmas
public import SandierSerfaty.Certificate.Arith.Interface
public import SandierSerfaty.Certificate.Arith.Log
public import SandierSerfaty.Certificate.Arith.LogLemmas
public import SandierSerfaty.Certificate.Arith.Pi
public import SandierSerfaty.Certificate.Arith.PiHigh
public import SandierSerfaty.Certificate.Arith.SInt
public import SandierSerfaty.Certificate.Arith.SIntLemmas
public import SandierSerfaty.Certificate.Arith
public import SandierSerfaty.Certificate.Assemble.Coeff
public import SandierSerfaty.Certificate.Assemble.Defs
public import SandierSerfaty.Certificate.Assemble.Lists
public import SandierSerfaty.Certificate.Assemble.Realize
public import SandierSerfaty.Certificate.Assemble.Table
public import SandierSerfaty.Certificate.Basis.CoeffEval
public import SandierSerfaty.Certificate.Basis.CoeffSound
public import SandierSerfaty.Certificate.Basis.Core
public import SandierSerfaty.Certificate.Basis.CoreSound
public import SandierSerfaty.Certificate.Basis.Data
public import SandierSerfaty.Certificate.Basis.DataSound
public import SandierSerfaty.Certificate.Basis.Deriv
public import SandierSerfaty.Certificate.Basis.Eval
public import SandierSerfaty.Certificate.Basis.Sound
public import SandierSerfaty.Certificate.Basis
public import SandierSerfaty.Certificate.Box.A7
public import SandierSerfaty.Certificate.Box.A7Idx
public import SandierSerfaty.Certificate.Box.Cert
public import SandierSerfaty.Certificate.Box.CertIdx
public import SandierSerfaty.Certificate.Box.CtxDef
public import SandierSerfaty.Certificate.Box.CtxIdx
public import SandierSerfaty.Certificate.Box.CtxIdxSound
public import SandierSerfaty.Certificate.Box.CtxSound
public import SandierSerfaty.Certificate.Box.CtxSound2
public import SandierSerfaty.Certificate.Box.Encl2
public import SandierSerfaty.Certificate.Box.Eval
public import SandierSerfaty.Certificate.Box.EvalData
public import SandierSerfaty.Certificate.Box.EvalSound
public import SandierSerfaty.Certificate.Box.Goal
public import SandierSerfaty.Certificate.Box.Grid
public import SandierSerfaty.Certificate.Box.HessCell
public import SandierSerfaty.Certificate.Box.HessDef
public import SandierSerfaty.Certificate.Box.HessIdx
public import SandierSerfaty.Certificate.Box.HessIdxSound
public import SandierSerfaty.Certificate.Box.HessLocal
public import SandierSerfaty.Certificate.Box.HessSound
public import SandierSerfaty.Certificate.Box.Hessian
public import SandierSerfaty.Certificate.Box.Inner
public import SandierSerfaty.Certificate.Box.InnerIdx
public import SandierSerfaty.Certificate.Box.Interp
public import SandierSerfaty.Certificate.Box.KBound
public import SandierSerfaty.Certificate.Box.KRowDef
public import SandierSerfaty.Certificate.Box.LoopSound
public import SandierSerfaty.Certificate.Box.Negative
public import SandierSerfaty.Certificate.Box.NumCheck
public import SandierSerfaty.Certificate.Box.NumCheckIdx
public import SandierSerfaty.Certificate.Box.NumDef
public import SandierSerfaty.Certificate.Box.NumGoal
public import SandierSerfaty.Certificate.Box.NumScalar
public import SandierSerfaty.Certificate.Box.NumSound
public import SandierSerfaty.Certificate.Box.Outer
public import SandierSerfaty.Certificate.Box.Prim
public import SandierSerfaty.Certificate.Box.Radial2
public import SandierSerfaty.Certificate.Box.Rows
public import SandierSerfaty.Certificate.Box.SecondDeriv
public import SandierSerfaty.Certificate.Box
public import SandierSerfaty.Certificate.Jet.Comp
public import SandierSerfaty.Certificate.Jet.Encl
public import SandierSerfaty.Certificate.Jet.IJet
public import SandierSerfaty.Certificate.Jet.Poly
public import SandierSerfaty.Certificate.Jet
public import SandierSerfaty.Certificate.Lambda.Calculus
public import SandierSerfaty.Certificate.Lambda.Deriv
public import SandierSerfaty.Certificate.Lambda.Eval
public import SandierSerfaty.Certificate.Lambda.GoalIdx
public import SandierSerfaty.Certificate.Lambda.LoopSound
public import SandierSerfaty.Certificate.Lambda.Model
public import SandierSerfaty.Certificate.Lambda.Point
public import SandierSerfaty.Certificate.Lambda.Shard
public import SandierSerfaty.Certificate.Lambda.Sound
public import SandierSerfaty.Certificate.Lambda
public import SandierSerfaty.Certificate.Query.Cell
public import SandierSerfaty.Certificate.Query.CellSound
public import SandierSerfaty.Certificate.Query.Const
public import SandierSerfaty.Certificate.Query.ConstSound
public import SandierSerfaty.Certificate.Query.DerivG
public import SandierSerfaty.Certificate.Query.DerivGSound
public import SandierSerfaty.Certificate.Query.ExteriorSigns
public import SandierSerfaty.Certificate.Query.FxG
public import SandierSerfaty.Certificate.Query.FxGReal
public import SandierSerfaty.Certificate.Query.FxGSound
public import SandierSerfaty.Certificate.Query.Lam
public import SandierSerfaty.Certificate.Query.LamSound
public import SandierSerfaty.Certificate.Query.Lookup
public import SandierSerfaty.Certificate.Query.LookupIdx
public import SandierSerfaty.Certificate.Query.LookupIdxSound
public import SandierSerfaty.Certificate.Query.LookupSound
public import SandierSerfaty.Certificate.Query.Table
public import SandierSerfaty.Certificate.Query.TableBridge
public import SandierSerfaty.Certificate.Query.Taylor
public import SandierSerfaty.Certificate.Query
public import SandierSerfaty.Certificate.Table.Bridge
public import SandierSerfaty.Certificate.Table.Eval
public import SandierSerfaty.Certificate.Table.Init
public import SandierSerfaty.Certificate.Table.Inner
public import SandierSerfaty.Certificate.Table.InnerBridge
public import SandierSerfaty.Certificate.Table.Midpoint
public import SandierSerfaty.Certificate.Table.Model
public import SandierSerfaty.Certificate.Table.StepSound
public import SandierSerfaty.Certificate.Table

/-!
# Root part

Part of the generated root `SandierSerfaty.lean`. It imports the modules of one area of the library (the imports
above), except those that the root skips. It is generated; do not edit it by hand, and never import it.
-/

public section
