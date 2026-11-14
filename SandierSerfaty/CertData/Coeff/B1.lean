/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Coeff.Rows

/-!
# Assertion A1, block 1 (kernel shards)

`decide +kernel` shards: the rows of the box `|n|, |q| ≤ 256` for the modes from `1` (8 rows per declaration), and the final enclosure test.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem rows_b1_0 : rowsB 1 256 1 rowCk1 0 8 = true := by
  decide +kernel

theorem rows_b1_8 : rowsB 1 256 1 rowCk1 8 8 = true := by
  decide +kernel

theorem rows_b1_16 : rowsB 1 256 1 rowCk1 16 8 = true := by
  decide +kernel

theorem rows_b1_24 : rowsB 1 256 1 rowCk1 24 8 = true := by
  decide +kernel

theorem rows_b1_32 : rowsB 1 256 1 rowCk1 32 8 = true := by
  decide +kernel

theorem rows_b1_40 : rowsB 1 256 1 rowCk1 40 8 = true := by
  decide +kernel

theorem rows_b1_48 : rowsB 1 256 1 rowCk1 48 8 = true := by
  decide +kernel

theorem rows_b1_56 : rowsB 1 256 1 rowCk1 56 8 = true := by
  decide +kernel

theorem rows_b1_64 : rowsB 1 256 1 rowCk1 64 8 = true := by
  decide +kernel

theorem rows_b1_72 : rowsB 1 256 1 rowCk1 72 8 = true := by
  decide +kernel

theorem rows_b1_80 : rowsB 1 256 1 rowCk1 80 8 = true := by
  decide +kernel

theorem rows_b1_88 : rowsB 1 256 1 rowCk1 88 8 = true := by
  decide +kernel

theorem rows_b1_96 : rowsB 1 256 1 rowCk1 96 8 = true := by
  decide +kernel

theorem rows_b1_104 : rowsB 1 256 1 rowCk1 104 8 = true := by
  decide +kernel

theorem rows_b1_112 : rowsB 1 256 1 rowCk1 112 8 = true := by
  decide +kernel

theorem rows_b1_120 : rowsB 1 256 1 rowCk1 120 8 = true := by
  decide +kernel

theorem rows_b1_128 : rowsB 1 256 1 rowCk1 128 8 = true := by
  decide +kernel

theorem rows_b1_136 : rowsB 1 256 1 rowCk1 136 8 = true := by
  decide +kernel

theorem rows_b1_144 : rowsB 1 256 1 rowCk1 144 8 = true := by
  decide +kernel

theorem rows_b1_152 : rowsB 1 256 1 rowCk1 152 8 = true := by
  decide +kernel

theorem rows_b1_160 : rowsB 1 256 1 rowCk1 160 8 = true := by
  decide +kernel

theorem rows_b1_168 : rowsB 1 256 1 rowCk1 168 8 = true := by
  decide +kernel

theorem rows_b1_176 : rowsB 1 256 1 rowCk1 176 8 = true := by
  decide +kernel

theorem rows_b1_184 : rowsB 1 256 1 rowCk1 184 8 = true := by
  decide +kernel

theorem rows_b1_192 : rowsB 1 256 1 rowCk1 192 8 = true := by
  decide +kernel

theorem rows_b1_200 : rowsB 1 256 1 rowCk1 200 8 = true := by
  decide +kernel

theorem rows_b1_208 : rowsB 1 256 1 rowCk1 208 8 = true := by
  decide +kernel

theorem rows_b1_216 : rowsB 1 256 1 rowCk1 216 8 = true := by
  decide +kernel

theorem rows_b1_224 : rowsB 1 256 1 rowCk1 224 8 = true := by
  decide +kernel

theorem rows_b1_232 : rowsB 1 256 1 rowCk1 232 8 = true := by
  decide +kernel

theorem rows_b1_240 : rowsB 1 256 1 rowCk1 240 8 = true := by
  decide +kernel

theorem rows_b1_248 : rowsB 1 256 1 rowCk1 248 8 = true := by
  decide +kernel

theorem rows_b1_256 : rowsB 1 256 1 rowCk1 256 8 = true := by
  decide +kernel

theorem rows_b1_264 : rowsB 1 256 1 rowCk1 264 8 = true := by
  decide +kernel

theorem rows_b1_272 : rowsB 1 256 1 rowCk1 272 8 = true := by
  decide +kernel

theorem rows_b1_280 : rowsB 1 256 1 rowCk1 280 8 = true := by
  decide +kernel

theorem rows_b1_288 : rowsB 1 256 1 rowCk1 288 8 = true := by
  decide +kernel

theorem rows_b1_296 : rowsB 1 256 1 rowCk1 296 8 = true := by
  decide +kernel

theorem rows_b1_304 : rowsB 1 256 1 rowCk1 304 8 = true := by
  decide +kernel

theorem rows_b1_312 : rowsB 1 256 1 rowCk1 312 8 = true := by
  decide +kernel

theorem rows_b1_320 : rowsB 1 256 1 rowCk1 320 8 = true := by
  decide +kernel

theorem rows_b1_328 : rowsB 1 256 1 rowCk1 328 8 = true := by
  decide +kernel

theorem rows_b1_336 : rowsB 1 256 1 rowCk1 336 8 = true := by
  decide +kernel

theorem rows_b1_344 : rowsB 1 256 1 rowCk1 344 8 = true := by
  decide +kernel

theorem rows_b1_352 : rowsB 1 256 1 rowCk1 352 8 = true := by
  decide +kernel

theorem rows_b1_360 : rowsB 1 256 1 rowCk1 360 8 = true := by
  decide +kernel

theorem rows_b1_368 : rowsB 1 256 1 rowCk1 368 8 = true := by
  decide +kernel

theorem rows_b1_376 : rowsB 1 256 1 rowCk1 376 8 = true := by
  decide +kernel

theorem rows_b1_384 : rowsB 1 256 1 rowCk1 384 8 = true := by
  decide +kernel

theorem rows_b1_392 : rowsB 1 256 1 rowCk1 392 8 = true := by
  decide +kernel

theorem rows_b1_400 : rowsB 1 256 1 rowCk1 400 8 = true := by
  decide +kernel

theorem rows_b1_408 : rowsB 1 256 1 rowCk1 408 8 = true := by
  decide +kernel

theorem rows_b1_416 : rowsB 1 256 1 rowCk1 416 8 = true := by
  decide +kernel

theorem rows_b1_424 : rowsB 1 256 1 rowCk1 424 8 = true := by
  decide +kernel

theorem rows_b1_432 : rowsB 1 256 1 rowCk1 432 8 = true := by
  decide +kernel

theorem rows_b1_440 : rowsB 1 256 1 rowCk1 440 8 = true := by
  decide +kernel

theorem rows_b1_448 : rowsB 1 256 1 rowCk1 448 8 = true := by
  decide +kernel

theorem rows_b1_456 : rowsB 1 256 1 rowCk1 456 8 = true := by
  decide +kernel

theorem rows_b1_464 : rowsB 1 256 1 rowCk1 464 8 = true := by
  decide +kernel

theorem rows_b1_472 : rowsB 1 256 1 rowCk1 472 8 = true := by
  decide +kernel

theorem rows_b1_480 : rowsB 1 256 1 rowCk1 480 8 = true := by
  decide +kernel

theorem rows_b1_488 : rowsB 1 256 1 rowCk1 488 8 = true := by
  decide +kernel

theorem rows_b1_496 : rowsB 1 256 1 rowCk1 496 8 = true := by
  decide +kernel

theorem rows_b1_504 : rowsB 1 256 1 rowCk1 504 8 = true := by
  decide +kernel

theorem rows_b1_512 : rowsB 1 256 1 rowCk1 512 1 = true := by
  decide +kernel

theorem fin_b1 : coeffFinB s3lo s3hi 1 256 rowCk1 cosB1 = true := by
  decide +kernel

end SandierSerfaty.CertData
