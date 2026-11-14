/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.Midpoint
public import SandierSerfaty.Certificate.Table.Eval
public import SandierSerfaty.Certificate.Table.Model
public import SandierSerfaty.Certificate.Table.StepSound
public import SandierSerfaty.Certificate.Table.Inner
public import SandierSerfaty.Certificate.Table.Init
public import SandierSerfaty.Certificate.Table.Bridge
public import SandierSerfaty.Certificate.Table.InnerBridge

/-!
# The radial table of the certificate

Facade of the table layer of the kernel-checked certificate:

* `Midpoint`: the midpoint rule with its error bound `(b - a)³/24 · sup|f''|` (not in Mathlib);
* `Eval`: the evaluator — order-two jets of `S̃₁, S̃₂, H̃_k` from their ODEs, the tuple
  `(f̃₀, f̃₀', f̃₀'', ẽ, ẽ', ẽ'')` (`fh`), the midpoint propagation and the cell states, the chunk check;
* `Model`: the real model on a segment (`Bp`, `B1p`, `F0m`, `Em`, `SectorODE`) and the soundness of `fh`;
* `StepSound`: the soundness of one step and of a chunk (`chunkCheck_sound`, `TableEncloses`);
* `Inner`: the first segment `[b, p - c]` from the exact inner form (`innerCheck_sound`, `InnerEncloses`);
* `Init`: the initial checkpoint at `p - c` from the closed forms of `comp:initial-integrals`
  (`initCheck_sound`);
* `Bridge`: the model is the truncated calibration `Cal.Trunc` on every segment (`sectorODE_trunc`,
  `trunc_f₀_eq_F0m`, `trunc_e_eq_Em`); chunks and chains of chunks enclose `Trunc.f₀`, `Trunc.e`
  (`chunkCheck_sound_trunc`, `chunks_sound_trunc`, `TruncEncloses`);
* `InnerBridge`: on `(0, p - c]` the truncated sector functions have the closed forms of
  `comp:initial-integrals` and `f̃₀`, `ẽ` those of `comp:inner-exact` (`trunc_f₀_inner`); the initial
  checkpoint encloses the truncated calibration (`initCheck_sound_trunc`).

The regression module `Examples` was removed by the dead-code sweep DEAD-1.
-/

public section
