/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The enclosure of λ (data)

The literal enclosure of `λ` and the widening radius of the exterior test A6.
-/

@[expose] public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The widening `⌈2^128/10^11⌉` (the infinite-mode error, `Tails.uniform_error_of_finiteCore`). -/
def lamRad : Nat := 3402823669209384634633746075

/-- The coarse enclosure of `λ` (`lamEnc iTbl dLit 64 lamRad`, as computed). -/
def lamLit : IV 128 := ⟨⟨true, 2299835313977563032759672460423238932794⟩, ⟨true, 2281004871431816180101682654394651505397⟩⟩

end SandierSerfaty.CertData
