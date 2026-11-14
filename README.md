# Triangular minimality for the planar Coulomb renormalized energy, in Lean

[![Build and verify](https://github.com/scottnarmstrong/TriangularMinimality/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/TriangularMinimality/actions/workflows/build.yml)

A complete Lean 4 and Mathlib formalization of

> OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, preprint, 23 September 2026
> ([OpenAI Math Release](https://github.com/openai/math/tree/main/preprints/Triangular-minimality-for-planar-Coulomb-renormalized-energy-September-23-2026)),

together with the lower bound for the jellium energy in Chapter 11 of

> S. Serfaty, *Lectures on Coulomb and Riesz gases*, [arXiv:2407.21194](https://arxiv.org/abs/2407.21194),

in the case of the preprint (dimension two, logarithmic interaction, density one).

Infinitely many unit point charges in the plane, together with a uniform neutralizing background, have
infinite electrostatic energy. Removing the logarithmic self-energy of each charge and averaging over large
regions gives the renormalized energy $W$ of Sandier and Serfaty. They conjectured that $W$ is minimized by the
triangular lattice. The preprint proves this, and this repository proves it in Lean, from Mathlib alone:

- **Theorem 1.1** (`triangularEnergy_le_wholeEnergy`, `paperTriangularField_spec`). For every admissible field
  $E$, $W(E)\ge W(E_\triangle)$, where $E_\triangle$ is the field of the triangular lattice of covolume one.
- **Theorem 1.2** (`mul_triangularEnergy_le_torusEnergy`). For $n\ge2$ distinct points on the square torus of area
  $n$, the energy is at least $n\,W_\triangle$, where $W_\triangle$ is the energy of one point on the triangular
  torus.
- **Corollary 1.3** (`sphereLogEnergy_asymptotics`). The minimal logarithmic energy of $n$ points on the unit sphere
  is $\bigl(\tfrac12-\log2\bigr)n^2-\tfrac n2\log n+C_{\mathrm{BHS}}\,n+o(n)$. This is the conjecture of Brauchart,
  Hardin and Saff for the logarithmic energy on $S^2$.
- **Chapter 11 of the lectures** (`div_two_pi_triangularEnergy_le_neutralEnergy`,
  `configEnergy_triangularLattice`). The jellium energy of every field, and of every configuration, is at least
  $W_\triangle/(2\pi)$, the value of the triangular lattice.

The one numerical step of the preprint, a computer-assisted interval verification, is replaced by a certificate
that the Lean kernel checks. Theorem 1.1 and Corollary 1.3 are proved by routes that do not use the papers of
Sandier and Serfaty or of Bétermin and Sandier that the preprint cites. The library contains no `sorry`
and uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). It has about 245,000 lines of
Lean in 1,125 files, of which 139,000 lines are the generated data of the certificate.

## Main results

Results are cited by the numbering of the preprint and of the lectures (arXiv:2407.21194v1). Each theorem is in
its own file in [`SandierSerfaty/Statements`](SandierSerfaty/Statements), in the namespace `SandierSerfaty`,
together with the 28 definitions the theorems use.

| Result | Lean theorem |
|---|---|
| Theorem 1.2: the lower bound on square tori | `mul_triangularEnergy_le_torusEnergy` |
| Theorem 1.1: $W(E)\ge W_\triangle$ for every admissible field and every cutoff family | `triangularEnergy_le_wholeEnergy` |
| Theorem 1.1: $E_\triangle$ is admissible and $W(E_\triangle)=W_\triangle$ | `paperTriangularField_spec` |
| Corollary 1.3: the spherical logarithmic energy | `sphereLogEnergy_asymptotics` |
| Chapter 11: the jellium lower bound for fields | `div_two_pi_triangularEnergy_le_neutralEnergy` |
| Chapter 11, Definition 11.6: the lower bound for configurations | `configEnergy_triangularLattice` |
| Chapter 11, Definition 11.4: the energy $W_{C_0}$ equals the neutral energy for large $C_0$ | `exists_jelliumEnergy_eq_neutralEnergy` |
| The triangular field of the lectures and its energy | `triangularField_spec` |
| The fundamental domain of a lattice | `torusDomain_spec` |
| Existence and uniqueness of the periodic potential | `existsUnique_isTorusPotential` |
| The chosen potential is that potential | `torusPotential_spec` |
| The puncture limit defining the torus energy exists | `tendsto_torusEnergy` |
| The local puncture limit of the whole-plane energy exists | `tendsto_punctureFunctional` |

The last five theorems concern the choices made by the definitions (a fundamental domain, the periodic potential,
the puncture limits): they show that these exist and are the intended objects.

Theorem 1.2 reads as follows:

```lean
theorem mul_triangularEnergy_le_torusEnergy (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    n * triangularEnergy ≤ torusEnergy (squareLattice n) a
```

In words:
- `squareLattice n` is the lattice $\sqrt n\,\mathbb Z[i]$ of the torus $T_n=\mathbb C/\sqrt n\,\mathbb Z[i]$, of
  area $n$.
- The hypothesis `ha` says that the points $a_1,\dots,a_n$ are distinct on $T_n$.
- `torusEnergy` is the energy (1.6) of the preprint,
  $\lim_{\eta\downarrow0}\bigl[\tfrac12\int_{T_n\setminus\bigcup_iB(a_i,\eta)}\vert\nabla h\vert^2+\pi n\log\eta\bigr]$,
  where $h$ is the mean-zero periodic potential with $-\Delta h=2\pi\bigl(\sum_i\delta_{a_i}-1\bigr)$.
- `triangularEnergy` is $W_\triangle$, the same energy for one point on the torus of the triangular lattice of
  covolume one.

**[docs/STATEMENTS.md](docs/STATEMENTS.md)** gives all 13 statements in Lean and in words. It also gives the 28
definitions, written out in ordinary mathematics and compared with the preprint and the lectures.

## What is formalized

- **The torus bound** (Theorem 1.2; Sections 3–8 of the preprint). The steps:
  - the periodic potential and its Green representation, here built from Jacobi theta functions;
  - existence of minimizing configurations and their separation;
  - periodic Voronoi cells and their sectors, with at most $6n$ incidences, proved by an angle-packing argument
    instead of the Euler characteristic;
  - a glued trial potential and the exact dual identity, which reduce the bound to two scalar estimates on one
    sector;
  - the local Green function of the triangular lattice and the constants of the comparison on the triangular cell;
  - the tail estimates for the truncated series;
  - the finite verification, as a certificate checked by the kernel.
- **The jellium bound** (Chapter 11 of the lectures). A field on a large square is screened with explicit fields
  and projected onto a square torus, and Theorem 1.2 applies there. This route replaces the lectures' argument,
  whose Lemma 11.2 is false in the boundary layer. The energy $W_{C_0}$ of Definition 11.4 equals the neutral energy
  for every large enough $C_0$ (the proof gives $C_0\ge\log2+\pi/32$).
- **The whole plane** (Theorem 1.1). Theorem 1.1 follows from the jellium bound by a comparison inequality,
  $W^{\mathrm{neu}}(-E,1)\le W(E)/(2\pi)$ for every admissible field and every cutoff family. The triangular
  field is admissible, with energy $W_\triangle$.
- **The sphere** (Corollary 1.3). The steps:
  - exact splitting of the energy in stereographic charts;
  - separation of minimizers;
  - an upper bound by configurations on latitude rings;
  - a lower bound by localization, screening and reflection onto square tori.

  The constant comes from the closed form
  $W_\triangle=\pi\log\bigl(2\sqrt2\,\pi/(\sqrt3\,\Gamma(1/3)^3)\bigr)$, proved through the Weierstrass periods of
  the equianharmonic lattice. Existence of minimizers, for every $n$, is proved too.

Four notes in **[notes/](notes)** write out, with complete proofs, the mathematics that the formalization uses
beyond the preprint: the comparison inequality, the screening argument, the route to the sphere and the closed form.
The Lean comments cite them.

**The certificate.** The finite inequalities of the preprint's Section 7 are discharged by `decide +kernel` on
Boolean checks whose soundness is proved in the library. The 548 modules under `SandierSerfaty/CertData` are
mostly literal data. The data files and the proof scripts of the checks are produced by the generator
`lake exe certgen` ([CertGen](CertGen)), which is untrusted: the kernel checks everything it writes, so a defect in
the generator can make the build fail but cannot make a false theorem pass.

## Errata and deviations

The formalization found errors and gaps in the printed sources; none changes a stated theorem. The headline
items:
- Lemma 11.2 of the lectures, the monotonicity inequality behind Proposition 11.3, is false in the boundary layer.
  The formalization does not use it.
- The preprint's verification rests on a C++ program, with no argument in the text that the program implements the
  procedure. The certificate checked by the kernel replaces it.
- Theorems 1.1 and 1.2 are stated with $W_\triangle$ in place of $W(E_\triangle)$, and their identification is a
  separate theorem (`paperTriangularField_spec`).

[docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md) lists every defect found in the sources, with a status,
and every place where the formalization departs from them.

| Source | Errors | Gaps | Misprints | Unverified | Deviations |
|---|---:|---:|---:|---:|---:|
| Serfaty, *Lectures on Coulomb and Riesz gases* | 4 | 9 | 2 | 0 | 4 |
| OpenAI preprint | 0 | 8 | 1 | 0 | 8 |
| Bétermin–Sandier | 0 | 1 | 2 | 1 | 0 |
| Sandier–Serfaty | 0 | 0 | 1 | 0 | 0 |
| Brauchart–Hardin–Saff | 0 | 0 | 0 | 0 | 0 |

## Verification

- **Axiom audit.** `scripts/check-axioms.py` runs `#print axioms` on the 13 theorems and on the certificate
  (`SandierSerfaty.CertData.certificateGoal`). It checks that each depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- **Comparator.** [SandierSerfatyChallenge.lean](SandierSerfatyChallenge.lean) states the 13 theorems from Mathlib
  alone, together with the 28 definitions they use, in one file with one `sorry` per theorem.
  [SandierSerfatySolution.lean](SandierSerfatySolution.lean) proves the same statements from the library.
  [leanprover/comparator](https://github.com/leanprover/comparator), configured by [comparator.json](comparator.json),
  checks that the two files state the same theorems about the same definitions and that the Solution uses only the
  standard axioms. It then replays the Solution's proofs in the Lean kernel and in the independent kernels bundled
  with the toolchain.
- **Source rules.** `scripts/check_lean_modules.py` checks that every `.lean` file is a Lean module of at most
  1,500 lines. The library contains no `sorry`, `admit`, `axiom`, `native_decide` or `unsafe`, and no heartbeat or
  recursion-depth override.
- **Kernel rules.** `scripts/check_kernel_rules.py` checks that every Boolean check of the certificate is
  discharged by `decide +kernel`, never by native evaluation. It also checks that the definitions the kernel
  evaluates in its hot loops use only natural-number primitives and structural recursion. This guards against slow or vacuous checks
  and adds nothing to the trust base.

**Trust base.** The Lean 4 kernel and Mathlib are trusted, and nothing else; the library never uses
`native_decide` or `Lean.ofReduceBool`. A reader has to check that the 41 declarations of
[SandierSerfaty/Statements](SandierSerfaty/Statements) say what is intended: a wrong definition, hypothesis or
quantifier could make a theorem say less than intended without Lean noticing.
[docs/STATEMENTS.md](docs/STATEMENTS.md) presents them for that purpose.

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.35.0` is selected by
`lean-toolchain`, and Mathlib v4.35.0 is pinned in `lake-manifest.json`.

```bash
lake exe cache get              # Mathlib's compiled files
lake build                      # the core library: the 28 definitions and 8 of the 13 theorems
lake build SandierSerfatyCert   # the certificate and the 5 theorems that rest on it
```

Then the checks:

```bash
python3 scripts/check-axioms.py --core    # after `lake build`: the eight core theorems
python3 scripts/check-axioms.py           # after `lake build SandierSerfatyCert`: all 13 and the certificate
python3 scripts/check_lean_modules.py --root .
python3 scripts/check_kernel_rules.py
./scripts/verify-comparator.sh            # a local comparator run; see the script header
```

On a 16-core machine, `lake build` takes about 4 minutes from a fresh checkout (peak memory 1.7 GB). The
certificate library is not a default target: it takes about 2 hours 35 minutes (14 to 17 CPU-hours, at most
3.7 GB per Lean process). One shard can be built alone, for example
`lake build SandierSerfaty.CertData.Box.Both.S000`. The comparator replays the whole dependency closure in the
kernel, so for the five theorems that rest on the certificate a run takes roughly the certificate's CPU time
(estimated at about 15 hours, not measured). The eight other theorems replay in about 4 minutes.
`verify-comparator.sh` approximates the check of the Palomar registry but is not the registry's official
verification.

## Repository layout

- `SandierSerfaty/Statements/`: the 13 theorems and the 28 definitions, one declaration per file.
- `SandierSerfaty/Proofs/`: the proofs of the 13 theorems, assembled in `SandierSerfaty/Assembly/` from:
  - `Torus/`: the periodic potential and the torus energy;
  - `Geometry/`: Voronoi cells and sectors;
  - `Dual/`: the glued potential and the dual identity;
  - `Calibration/`: the comparison on the triangular cell;
  - `Tails/`: the tail estimates;
  - `Certificate/` and `CertData/`: the finite verification and its generated data;
  - `Screening/` and `Jellium/`: Chapter 11;
  - `Whole/`: the whole plane;
  - `Sphere/`: the sphere;
  - `ClosedForm/`: the closed form of $W_\triangle$;
  - `Analysis/`: potential theory.
- `CertGen/`: the untrusted generator of the certificate data.
- `SandierSerfatyChallenge.lean`, `SandierSerfatySolution.lean`, `comparator.json`: the comparator files.
- `scripts/`: the axiom audit, the source and kernel rules, the local comparator run.
- `docs/`: the statements, and the errata and deviations.
- `notes/`: the four supplementary notes (TeX and PDF).

## Authors, AI use and acknowledgements

The formalization is by **Scott Armstrong** (CNRS & Laboratoire Jacques-Louis Lions, Sorbonne Université and
Courant Institute School of Mathematics, Computing, and Data Science, New York University) and **Sylvia Serfaty**
(Laboratoire Jacques-Louis Lions, Sorbonne Université and Courant Institute School of Mathematics, Computing, and
Data Science, New York University).

The Lean code was written by AI agents (Claude Opus 5.5 and Claude Sonnet 5.5 in Claude Code) under their
supervision:
- A Claude Opus 5.5 session planned bounded proof tasks, assigned them to parallel agents, and adjudicated the
  statement and proof reviews.
- Every definition and theorem statement was checked against the sources by an independent model review and
  accepted by Scott Armstrong before its proof was developed.

The Lean kernel checks every proof; see [formalization.yaml](formalization.yaml) for details.

The mathematics is that of the OpenAI preprint and of Chapter 11 of the lectures. The preprint's interval
certificate (in its `verification` folder) is replaced here by the certificate checked in Lean. The preprint
cites the following works, which are used here as references only:
- É. Sandier and S. Serfaty, *From the Ginzburg–Landau model to vortex lattice problems*, Comm. Math. Phys. 313
  (2012), [arXiv:1011.4617](https://arxiv.org/abs/1011.4617);
- L. Bétermin and É. Sandier, *Renormalized energy and asymptotic expansion of optimal logarithmic energy on the
  sphere*, Constr. Approx. 47 (2018), [arXiv:1404.4485](https://arxiv.org/abs/1404.4485);
- J. S. Brauchart, D. P. Hardin and E. B. Saff, *The next-order term for optimal Riesz and logarithmic energy
  asymptotics on the sphere*, Contemp. Math. 578 (2012), [arXiv:1202.4037](https://arxiv.org/abs/1202.4037).

The authors of the preprint have not reviewed this formalization. The two arithmetic files whose headers name
Zohar Komargodski, [Interface.lean](SandierSerfaty/Certificate/Arith/Interface.lean) and
[PiHigh.lean](SandierSerfaty/Certificate/Arith/PiHigh.lean), are adapted from the
[KAM repository](https://github.com/scottnarmstrong/KAM-dev) of S. Armstrong and Z. Komargodski.

To cite this formalization, use [CITATION.cff](CITATION.cff), and please also cite the preprint. S. Armstrong was
supported by the European Research Council (ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828. S. Serfaty was supported by a Simons Investigator award, NSF grant
DMS-2247846, and the Institut Universitaire de France.

## License

All files of this repository, including the notes in [notes/](notes) (TeX sources and PDFs), are released under the
[Apache License 2.0](LICENSE). The preprint and the works cited above are not included and are not covered by this
license.
