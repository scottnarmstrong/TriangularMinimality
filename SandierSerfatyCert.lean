/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfatyCert.CertData
public import SandierSerfatyCert.Proofs
public import SandierSerfatyCert.Statements

/-!
# SandierSerfatyCert

Root of the certificate application `SandierSerfatyCert`: the literal data, kernel shards and
assembled theorems of the certificate for the square-torus bound. An opt-in library: a plain `lake
build` does not build it; `lake build SandierSerfatyCert` does. This file imports the generated
parts `SandierSerfatyCert.*`, which together import every module of `SandierSerfatyCert`. It is
generated; do not edit it by hand, and never import it.
-/

public section
