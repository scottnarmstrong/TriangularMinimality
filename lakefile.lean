import Lake

open Lake DSL

package «SandierSerfaty» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- The core library: the formalization of triangular minimality for the planar Coulomb (jellium)
renormalized energy. It builds its root `SandierSerfaty.lean` with the import closure of that root, and is the
default target. The five theorems that rest on the kernel certificate are in `SandierSerfatyCert`. -/
@[default_target]
lean_lib «SandierSerfaty» where
  roots := #[`SandierSerfaty]
  globs := #[.one `SandierSerfaty]
  leanOptions := projectLeanOptions

/-- The kernel certificate of the square-torus bound: literal data, `decide +kernel` shards and the
assembled theorems (`SandierSerfaty.CertData.*`), with the five theorems that rest on it. An opt-in library,
not a default target: `lake build SandierSerfatyCert` (about 14 CPU-hours), or one shard module at a time. -/
lean_lib «SandierSerfatyCert» where
  roots := #[`SandierSerfatyCert]
  globs := #[.one `SandierSerfatyCert]
  leanOptions := projectLeanOptions

/-- Mathlib-only statement of the main results, with one intentional `sorry` per theorem. -/
lean_lib «SandierSerfatyChallenge» where
  roots := #[`SandierSerfatyChallenge]

/-- The Challenge statements proved from the library. -/
lean_lib «SandierSerfatySolution» where
  roots := #[`SandierSerfatySolution]

/-- The untrusted generator of the certificate (`lake exe certgen`): natively compiled from the same
evaluator definitions the kernel checks; it writes the literal data files and the Lean proof scripts of the
shards (their `decide +kernel` checks), and the kernel checks everything it writes (`CertGen/Main.lean`). -/
lean_exe certgen where
  root := `CertGen.Main
