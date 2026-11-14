/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Root.Analysis
public import SandierSerfaty.Root.Assembly
public import SandierSerfaty.Root.Calibration
public import SandierSerfaty.Root.Certificate
public import SandierSerfaty.Root.ClosedForm
public import SandierSerfaty.Root.Dual
public import SandierSerfaty.Root.Geometry
public import SandierSerfaty.Root.Jellium
public import SandierSerfaty.Root.Proofs
public import SandierSerfaty.Root.Screening
public import SandierSerfaty.Root.Sphere
public import SandierSerfaty.Root.Statements
public import SandierSerfaty.Root.Tails
public import SandierSerfaty.Root.Torus
public import SandierSerfaty.Root.Whole

/-!
# SandierSerfaty

Root module of the formalization of triangular minimality for the planar Coulomb renormalized energy
(OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, 2026) and of the main theorem on the
jellium energy of S. Serfaty, *Lectures on Coulomb and Riesz gases*, Chapter 11.

In the comments of the library, "the paper" is the paper above (cited by theorem number or LaTeX label), "the
book" is Serfaty's lectures, and the screening, comparison, closed-form and sphere notes are the supplementary
notes shipped in `notes/`.

This file imports the generated parts `SandierSerfaty.Root.*`, which together import every module of the core
library, that is, every module except those of the certificate applications (opt-in libraries with their own
roots). It is generated; do not edit it by hand, and never import it.
-/

public section
