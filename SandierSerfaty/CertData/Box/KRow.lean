/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The `K` row (kernel)

The sum row at the dyadic node near `p` (`Box.KBound`): segments with literal checkpoints (`sumSeg`).
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem k_0 : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm 400 0 ⟨false, 0⟩ ⟨true, 23157450204984913503241213973972086427272068603570967158134040749104419144⟩ = true := by
  decide +kernel

theorem k_400 : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm 400 400 ⟨true, 23157450204984913503241213973972086427272068603570967158134040749104419144⟩ ⟨true, 49724707219738490542669644982270277752544244407464757552181670458146309512⟩ = true := by
  decide +kernel

theorem k_800 : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm 400 800 ⟨true, 49724707219738490542669644982270277752544244407464757552181670458146309512⟩ ⟨true, 81323475350640575265226360786771552344719184810779014236069925114840447410⟩ = true := by
  decide +kernel

theorem k_1200 : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm 400 1200 ⟨true, 81323475350640575265226360786771552344719184810779014236069925114840447410⟩ ⟨true, 116684775327534864035608489321339795478540822444560752687542326561111403136⟩ = true := by
  decide +kernel

theorem k_1600 : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm 400 1600 ⟨true, 116684775327534864035608489321339795478540822444560752687542326561111403136⟩ ⟨true, 151668076107181772057984603189515274184289768783881210681033985322987405074⟩ = true := by
  decide +kernel

theorem k_2000 : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm 400 2000 ⟨true, 151668076107181772057984603189515274184289768783881210681033985322987405074⟩ ⟨true, 180466214048863042699837440066750489053242086694748310975513235300252866480⟩ = true := by
  decide +kernel

theorem k_2400 : sumSeg evalE kGrid.idx kGrid.dm kGrid.sm 400 2400 ⟨true, 180466214048863042699837440066750489053242086694748310975513235300252866480⟩ ⟨true, 197734349376308038144593154191846053888579215560674580494951202030731253060⟩ = true := by
  decide +kernel

theorem k_2800 : sumLoop evalE kGrid.idx kGrid.dm kGrid.sm kGrid.thr 303 2800 ⟨true, 197734349376308038144593154191846053888579215560674580494951202030731253060⟩ = true := by
  decide +kernel

theorem k_row : kGrid.row evalE = true :=
  (sumLoop_of_seg (m := 2703) k_0 (sumLoop_of_seg (m := 2303) k_400 (sumLoop_of_seg (m := 1903) k_800 (sumLoop_of_seg (m := 1503) k_1200 (sumLoop_of_seg (m := 1103) k_1600 (sumLoop_of_seg (m := 703) k_2000 (sumLoop_of_seg (m := 303) k_2400 k_2800)))))))

end SandierSerfaty.CertData.Box
