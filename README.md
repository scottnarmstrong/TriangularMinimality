# Triangular minimality for planar Coulomb renormalized energy, formalized in Lean 4

[![Build](https://github.com/scottnarmstrong/TriangularMinimality/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/TriangularMinimality/actions/workflows/build.yml)

A complete, machine-checked proof, in Lean 4 with Mathlib, that the triangular lattice minimizes the planar
Coulomb renormalized energy, following

> OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, preprint, 23 September 2026
> ([OpenAI Math Release](https://github.com/openai/math/tree/main/preprints/Triangular-minimality-for-planar-Coulomb-renormalized-energy-September-23-2026)),

together with the corresponding lower bound for the jellium energy of Chapter 11 of S. Serfaty,
*Lectures on Coulomb and Riesz gases* ([arXiv:2407.21194](https://arxiv.org/abs/2407.21194)), in the case
of the paper (dimension two, logarithmic interaction, density one). The proofs
use only Lean's standard axioms. The one numerical step of the paper, a computer-assisted interval
verification, is replaced by a certificate that the Lean kernel checks.

Infinitely many unit point charges in the plane, together with a uniform neutralizing background, have
infinite electrostatic energy. Removing the logarithmic self-energy of each charge and averaging over large
regions gives the renormalized energy $W$. The theorem states that among all admissible fields it is
minimized by the field of the triangular (hexagonal) lattice of covolume one. As a corollary, the second term
of the minimal logarithmic energy of $n$ points on the sphere $S^2$ is the constant of Brauchart, Hardin and
Saff. The proof reduces both statements to a lower bound for the energy of $n$ points on a square torus,
which is established by the paper's calibration argument and a finite certificate.

Statement and equation numbers below are those of the OpenAI preprint (Theorem 1.1, Theorem 1.2,
Corollary 1.3) and of Serfaty's lectures.

## What is proved

| Result | Lean declaration |
|---|---|
| Theorem 1.2 (lower bound on square tori) | `SandierSerfaty.mul_triangularEnergy_le_torusEnergy` |
| Theorem 1.1 (minimality among admissible fields) | `SandierSerfaty.triangularEnergy_le_wholeEnergy`, with `SandierSerfaty.paperTriangularField_spec` |
| Corollary 1.3 (spherical logarithmic energy) | `SandierSerfaty.sphereLogEnergy_asymptotics` |
| Lower bound for the jellium energy of fields (Chapter 11) | `SandierSerfaty.div_two_pi_triangularEnergy_le_neutralEnergy` |
| The same for configurations (Chapter 11, Definition 11.6) | `SandierSerfaty.configEnergy_triangularLattice` |
| The energy of Definition 11.4 equals the neutral energy for large $C_0$ | `SandierSerfaty.exists_jelliumEnergy_eq_neutralEnergy` |

The remaining stated theorems show that the objects of the statements are well defined, and are proved as
well: the fundamental domain of a lattice (`torusDomain_spec`), the existence and uniqueness of the periodic
potential (`existsUnique_isTorusPotential`), its characterization (`torusPotential_spec`), the existence of the
puncture limit that defines the torus energy (`tendsto_torusEnergy`), the existence of the local puncture
limit (`tendsto_punctureFunctional`), and the facts about the triangular field of the lectures
(`triangularField_spec`). In all, the statements are 13 theorems and 28 definitions, in
[SandierSerfaty/Statements](SandierSerfaty/Statements) (module names `SandierSerfaty.Statements.*`). These are the only
files that have to be read to know what has been proved; everything else is proof. The comment lines
`-- PREFIX_BEGIN`, `-- PROOF_BEGIN`, `-- PROOF_END`, `-- SUFFIX_BEGIN` and `-- SUFFIX_END` in those files delimit
the proof of each theorem, so that a checker can confirm that the text of the statement is unchanged.

The statements are quoted verbatim from [SandierSerfatyChallenge.lean](SandierSerfatyChallenge.lean), which
depends on Mathlib only, and are proved in [SandierSerfatySolution.lean](SandierSerfatySolution.lean).

The Lean blocks below are copied from the Challenge up to the `:=` that ends each statement, with their
docstrings omitted; they sit inside `namespace SandierSerfatyChallenge` there, with the definitions of
[the table below](#the-definitions). The library states the same theorems in the namespace `SandierSerfaty`.

### Theorem 1.2 (square tori)

> For every integer $n\ge2$ and every $n$ points $a_1,\dots,a_n$ of the torus $T_n=\mathbb C/(\sqrt n\,\mathbb Z[i])$
> that are pairwise distinct modulo the lattice, the mean-zero periodic potential $h$ with
> $-\Delta h=2\pi\bigl(\sum_i\delta_{a_i}-1\bigr)$ has energy
> $\mathcal W_n(h)=\lim_{\eta\downarrow0}\bigl[\tfrac12\int_{T_n\setminus\bigcup_iB(a_i,\eta)}\vert\nabla h\vert^2+\pi n\log\eta\bigr]\ge n\,W_\triangle$.

Here $W_\triangle$ is the energy of the one-point torus of the triangular lattice, which equals the energy
$W(E_\triangle)$ of the paper (this identification is `paperTriangularField_spec`). Lean:
`mul_triangularEnergy_le_torusEnergy`, in
[MulTriangularEnergyLeTorusEnergy.lean](SandierSerfaty/Statements/Torus/Theorems/MulTriangularEnergyLeTorusEnergy.lean).

```lean
theorem mul_triangularEnergy_le_torusEnergy (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    n * triangularEnergy ≤ torusEnergy (squareLattice n) a
```

### Theorem 1.1 (the whole plane)

> For every cutoff family $(\chi_R)$ with $0\le\chi_R\le1$, $\mathrm{supp}\,\chi_R\subset[-R,R]^2$, $\chi_R=1$ on
> $[-R+1,R-1]^2$ and $\sup_R\Vert\nabla\chi_R\Vert_\infty\lt\infty$, and every field $E$ of the admissible class
> $\mathcal A_1$ (locally integrable, $\mathrm{div}\,E=2\pi(\nu_\Lambda-1)$, $\mathrm{curl}\,E=0$, bounded density
> of $\Lambda$), the energy $W(E)=\limsup_{R\to\infty}W(E,\chi_R)/\vert K_R\vert$ satisfies $W(E)\ge W(E_\triangle)$.
> The triangular value is finite, so $\inf_{\mathcal A_1}W=W(E_\triangle)$.

Lean: `triangularEnergy_le_wholeEnergy` (valued in the extended reals, so infinite energies are covered) in
[TriangularEnergyLeWholeEnergy.lean](SandierSerfaty/Statements/Whole/Theorems/TriangularEnergyLeWholeEnergy.lean),
and `paperTriangularField_spec` in
[PaperTriangularFieldSpec.lean](SandierSerfaty/Statements/Whole/Theorems/PaperTriangularFieldSpec.lean), which says
that $E_\triangle\in\mathcal A_1$ and $W(E_\triangle)=W_\triangle$, both for every cutoff family. The first
gives $W(E)\ge W_\triangle$; together they give $\inf_{\mathcal A_1}W=W(E_\triangle)$, which is not stated as
one Lean formula.

```lean
theorem triangularEnergy_le_wholeEnergy (χ : ℝ → ℂ → ℝ) (hχ : IsCutoffFamily χ)
    (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E) :
    (triangularEnergy : EReal) ≤ wholeEnergy χ Λ E
```

```lean
theorem paperTriangularField_spec :
    IsAdmissibleField (triangularLattice : Set ℂ) paperTriangularField ∧
      ∀ χ : ℝ → ℂ → ℝ, IsCutoffFamily χ →
        wholeEnergy χ (triangularLattice : Set ℂ) paperTriangularField = (triangularEnergy : EReal)
```

### Corollary 1.3 (the sphere)

> Let $E_{\log}(n)$ be the minimum, over $n$ points of the unit sphere $S^2\subset\mathbb R^3$, of
> $-\sum_{i\ne j}\log\Vert y_i-y_j\Vert$ (ordered pairs). Then
> $E_{\log}(n)=\bigl(\tfrac12-\log2\bigr)n^2-\tfrac n2\log n+C_{\mathrm{BHS}}\,n+o(n)$, with
> $C_{\mathrm{BHS}}=2\log2+\tfrac12\log\tfrac23+3\log\frac{\sqrt\pi}{\Gamma(1/3)}$.

Lean: `sphereLogEnergy_asymptotics` in
[SphereLogEnergyAsymptotics.lean](SandierSerfaty/Statements/Sphere/Theorems/SphereLogEnergyAsymptotics.lean). The
formal statement gives a remainder $r(n)=o(n)$ with an exact identity for every $n\ge2$. In Lean $E_{\log}(n)$
is the infimum, `sphereLogEnergy n`. That it is attained is proved in the library, though it is not one of
the 13 stated theorems: `SandierSerfaty.Sphere.exists_isSphereMinimizer` (in
[Sphere/Minimizer.lean](SandierSerfaty/Sphere/Minimizer.lean)) gives a minimizer for every $n$, and
`SandierSerfaty.Sphere.Bridge.sphereLogEnergy_eq` (in
[Sphere/Bridge/LogEnergy.lean](SandierSerfaty/Sphere/Bridge/LogEnergy.lean)) shows that the energy of every
minimizer equals `sphereLogEnergy n`.

```lean
theorem sphereLogEnergy_asymptotics :
    ∃ r : ℕ → ℝ, (r =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 2 ≤ n →
      sphereLogEnergy n =
        ((((1 / 2 : ℝ) - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + bhsConstant * n + r n : ℝ) :
          EReal)
```

### Chapter 11 of the lectures (jellium)

For a configuration $C$ of points of $\mathbb C$ (a set) and an electric field $E$ in $\mathrm{Elec}(C,1)$, that
is, $-\mathrm{div}\,E=2\pi(\sum_{p\in C}\delta_p-1)$ (the sign convention of the lectures; as in their
Definition 11.1, no curl condition is imposed), the neutral energy
$W^{\mathrm{neu}}(E,1)$ is the renormalized energy of Definition 11.4 without its term
$C_0(\#(C\cap\square_R)-R^2)$, and is $+\infty$ when $C$ does not have density one. Then
$W^{\mathrm{neu}}(E,1)\ge W_\triangle/(2\pi)$, in the extended reals (`div_two_pi_triangularEnergy_le_neutralEnergy`),
and the energy of the configuration satisfies $\mathbb W(C,1)\ge\mathbb W(\Lambda_\triangle,1)=W_\triangle/(2\pi)$
(`configEnergy_triangularLattice`). The energy $W_{C_0}$ of Definition 11.4 equals $W^{\mathrm{neu}}$ for every
sufficiently large $C_0$ (`exists_jelliumEnergy_eq_neutralEnergy`; the proof gives $C_0\ge\log2+\pi/32$), so
both bounds hold for $W_{C_0}$ too. Only the case $d=2$, $s=0$, $m=1$ of Chapter 11 is formalized.

```lean
theorem div_two_pi_triangularEnergy_le_neutralEnergy (C : Set ℂ) (E : ℂ → ℂ) (hE : E ∈ elec C) :
    ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ≤ neutralEnergy C E
```

```lean
theorem configEnergy_triangularLattice :
    configEnergy (triangularLattice : Set ℂ) = ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ∧
      ∀ C : Set ℂ, configEnergy (triangularLattice : Set ℂ) ≤ configEnergy C
```

```lean
theorem exists_jelliumEnergy_eq_neutralEnergy :
    ∃ C0star : ℝ, ∀ C0 : ℝ, C0star ≤ C0 → ∀ (C : Set ℂ), ∀ E ∈ elec C,
      jelliumEnergy C0 C E = neutralEnergy C E
```

### The statements that make the definitions meaningful

The definitions of the torus and of the puncture limits are given by choices (`Classical.epsilon`, `limUnder`,
`limsup`), so the following theorems show that the choices are the intended objects. For the lattice `Γ` the
fundamental domain `torusDomain Γ` is one, and the integral of a periodic function over it does not depend on
the choice (`torusDomain_spec`):

```lean
theorem torusDomain_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    IsAddFundamentalDomain Γ (torusDomain Γ) volume ∧
      ∀ (F : Set ℂ), IsAddFundamentalDomain Γ F volume → ∀ f : ℂ → ℝ,
        (∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) → ∫ x in torusDomain Γ, f x = ∫ x in F, f x
```

For $N$ charges with distinct classes on a torus of area $N$ the potential exists and is unique
(`existsUnique_isTorusPotential`), and `torusPotential` is that potential (`torusPotential_spec`):

```lean
theorem existsUnique_isTorusPotential (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    ∃! h : ℂ → ℝ, IsTorusPotential Γ a h
```

```lean
theorem torusPotential_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    IsTorusPotential Γ a (torusPotential Γ a) ∧
      ∀ h : ℂ → ℝ, IsTorusPotential Γ a h → h = torusPotential Γ a
```

The puncture limit that defines the torus energy exists, and is finite (`tendsto_torusEnergy`); so does the
local puncture limit of the whole-plane energy for every admissible field and every smooth compactly
supported weight (`tendsto_punctureFunctional`):

```lean
theorem tendsto_torusEnergy (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    Tendsto (fun η : ℝ ↦
        (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
          ‖gradient (torusPotential Γ a) x‖ ^ 2) + Real.pi * N * Real.log η)
      (𝓝[>] 0) (𝓝 (torusEnergy Γ a))
```

```lean
theorem tendsto_punctureFunctional (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E)
    (ξ : ℂ → ℝ) (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ) :
    ∃ w : ℝ, Tendsto (punctureFunctional Λ E ξ) (𝓝[>] 0) (𝓝 (w : EReal))
```

Finally, the triangular field of the lectures lies in $\mathrm{Elec}(\Lambda_\triangle,1)$ and has neutral energy
$W_\triangle/(2\pi)$ (`triangularField_spec`; the sign of $\nabla h_\triangle=-E_\triangle$ is that of the
lectures):

```lean
theorem triangularField_spec :
    triangularField ∈ elec (triangularLattice : Set ℂ) ∧
      neutralEnergy (triangularLattice : Set ℂ) triangularField =
        ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal)
```

## The definitions

The statements use 28 definitions, all written out in [SandierSerfatyChallenge.lean](SandierSerfatyChallenge.lean)
(and in `SandierSerfaty/Statements/*/Defs`). The plane is $\mathbb C$ with its Euclidean norm and Lebesgue measure; a
field is a map $E:\mathbb C\to\mathbb C$, $E=E_1+iE_2$, and $\nabla f=\partial_1f+i\partial_2f$; a configuration is a
set. Numbers (1.1)–(1.8) are those of the preprint, and Definitions 11.1, 11.4 and 11.6 and the formulas
(11.2.x) and (4.1.18) are those of Serfaty's lectures. Energies that can be infinite take values in the extended
reals.

**Lattices, tori and the torus energy.**

| Name | Meaning |
|---|---|
| `squareLattice` | `squareLattice n` is $\sqrt n\,\mathbb Z[i]\subset\mathbb C$, the lattice of the torus $T_n$ of Theorem 1.2. |
| `triangularLattice` | $\Lambda_\triangle=\sqrt{2/\sqrt3}\,(\mathbb Z+\mathbb Z\,e^{i\pi/3})$ of covolume one, as in (1.5). |
| `torusDomain` | `torusDomain Γ` is a fundamental domain of $\Gamma$ acting on $\mathbb C$ by translation, chosen by `Classical.epsilon`; `torusDomain_spec` shows that it is one and that integrals of periodic functions over it do not depend on the choice. |
| `IsTorusPotential` | `IsTorusPotential Γ a h`: $h$ is the mean-zero $\Gamma$-periodic solution of $-\Delta h=2\pi(\sum_i\delta_{a_i}-1)$, in classical form: periodic, smooth off the charges $a_i+\Gamma$ with $\Delta h=2\pi$ there, $h+\log\Vert x-a_i\Vert$ has a finite limit at each charge, integral zero over the fundamental domain, and $h=0$ at the charges by convention. Equivalent to the distributional form of the paper. |
| `torusPotential` | `torusPotential Γ a` is a function with `IsTorusPotential Γ a`, chosen by `Classical.epsilon`; the unique one when $\Gamma$ has covolume $N$ and the $N$ charges have distinct classes. |
| `torusEnergy` | `torusEnergy Γ a` is the energy (1.6) of $N$ charges on $\mathbb C/\Gamma$: the limit as $\eta\downarrow0$ of $\tfrac12\int_{T\setminus\bigcup B(a_i+\gamma,\eta)}\Vert\nabla h\Vert^2+\pi N\log\eta$ for the potential $h$ and $T=$ `torusDomain Γ`. For $\Gamma=\sqrt n\,\mathbb Z[i]$ and $N=n$ it is $\mathcal W_n(h)$ of Theorem 1.2. |
| `triangularEnergy` | $W_\triangle$, the torus energy of $\mathbb C/\Lambda_\triangle$ with one charge at $0$. |

**The whole-plane energy.**

| Name | Meaning |
|---|---|
| `IsCutoffFamily` | `IsCutoffFamily χ` is condition (1.1): for every $R>1$, $\chi_R$ is smooth with compact support, $0\le\chi_R\le1$, $\mathrm{supp}\,\chi_R\subset K_R=[-R,R]^2$, $\chi_R=1$ on $K_{R-1}$, and $\sup_R\Vert\nabla\chi_R\Vert_\infty\lt\infty$. |
| `IsAdmissibleField` | `IsAdmissibleField Λ E` is membership of $E$ in the class $\mathcal A_1$ of (1.2) with charges $\Lambda$: $\Lambda$ locally finite, $E$ locally integrable, $\mathrm{div}\,E=2\pi(\nu_\Lambda-1)$ and $\mathrm{curl}\,E=0$ in distributions (tested against real $C_c^\infty$ functions), and $\sup_R\nu_\Lambda(B_R)/\vert B_R\vert\lt\infty$. |
| `punctureFunctional` | `punctureFunctional Λ E ξ η` is $\tfrac12\int_{\mathbb C\setminus\bigcup_{p\in\Lambda}B(p,\eta)}\xi\Vert E\Vert^2+\pi\log\eta\sum_{p\in\Lambda}\xi(p)$, the expression inside the limit of (1.3); the integral is the difference of the lower integrals of the positive and negative parts of the integrand. |
| `localEnergy` | `localEnergy Λ E ξ` is $W(E,\xi)$ of (1.3), the $\limsup$ as $\eta\downarrow0$ of `punctureFunctional Λ E ξ η` (a limit by `tendsto_punctureFunctional`). |
| `wholeEnergy` | `wholeEnergy χ Λ E` is $W(E)=\limsup_{R\to\infty}W(E,\chi_R)/\vert K_R\vert$ of (1.4), with $\vert K_R\vert=(2R)^2$. |
| `paperTriangularField` | $E_\triangle=-\nabla h_\triangle$, where $h_\triangle$ is the torus potential of one charge at $0$ on $\mathbb C/\Lambda_\triangle$. |

**The sphere.**

| Name | Meaning |
|---|---|
| `logPairEnergy` | `logPairEnergy x y` is $-\log\Vert x-y\Vert$ for points of $\mathbb R^3$, and $+\infty$ if $x=y$. |
| `logConfigEnergy` | `logConfigEnergy y` is $-\sum_{i\ne j}\log\Vert y_i-y_j\Vert$ over ordered pairs, for $n$ points of the unit sphere $S^2$; $+\infty$ if two points collide. |
| `sphereLogEnergy` | `sphereLogEnergy n` is $E_{\log}(n)$ of Corollary 1.3, the infimum of `logConfigEnergy` over $n$-point configurations of $S^2$. |
| `bhsConstant` | $C_{\mathrm{BHS}}=2\log2+\tfrac12\log\tfrac23+3\log\frac{\sqrt\pi}{\Gamma(1/3)}$, as in (1.8). |

**The jellium energy of Serfaty's lectures** (dimension two, kernel $-\log$, density one).

| Name | Meaning |
|---|---|
| `elec` | `elec C` is the class $\mathrm{Elec}(C,1)$ (Definition 11.1): the fields $E$, locally integrable, with $C$ locally finite and $-\mathrm{div}\,E=2\pi(\sum_{p\in C}\delta_p-1)$ in distributions; no curl condition. |
| `truncLog` | `truncLog η` is $f_\eta(x)=(-\log\Vert x\Vert+\log\eta)_+$, the truncated logarithm of (4.1.18). |
| `truncField` | `truncField C η E` is the truncated field $E_\eta=E-\sum_{p\in C}\nabla f_{\eta_p}(\cdot-p)$ of (11.2.4), with a radius $\eta_p$ for each point. |
| `nnRadius` | `nnRadius C p` is $r_p=\tfrac14\min(\min_{q\in C,q\ne p}\Vert q-p\Vert,1)$ of (11.2.2). |
| `cube` | `cube ℓ` is the closed square $\square_\ell=[-\ell/2,\ell/2]^2$. |
| `cubeRadius` | `cubeRadius C ℓ p` is the radius $\tilde r_p$ of (11.2.3) relative to $\square_\ell$: $r_p$ at distance at least $2$ inside the boundary, $\tfrac14$ outside or within distance $1$ of it, interpolated linearly in between. |
| `cubeEnergy` | `cubeEnergy C E ℓ` is the energy $F^{\square_\ell}(E,1)$ of (11.2.6): $\tfrac1{4\pi}\int_{\square_\ell}\Vert E_{\tilde r}\Vert^2-\tfrac12\sum_{p\in C\cap\square_\ell}g(\tilde r_p)-\sum_{p\in C\cap\square_\ell}\int f_{\tilde r_p}(x-p)\,dx$ with $g=-\log\Vert\cdot\Vert$, in the extended reals. |
| `neutralEnergy` | `neutralEnergy C E` is $W^{\mathrm{neu}}(E,1)=\limsup_{\ell\to\infty}\ell^{-2}F^{\square_\ell}(E,1)$ if $\#(C\cap\square_\ell)/\ell^2\to1$, and $+\infty$ otherwise. |
| `jelliumEnergy` | `jelliumEnergy C0 C E` is $W_{C_0}(E,1)=\limsup_{R\to\infty}R^{-2}[F^{\square_R}(E,1)+C_0(\#(C\cap\square_R)-R^2)]$ of Definition 11.4. |
| `configEnergy` | `configEnergy C` is $\mathbb W(C,1)$ of Definition 11.6: the infimum of $W^{\mathrm{neu}}(E,1)$ over the fields $E\in\mathrm{Elec}(C,1)$ that are distributional gradients, with $\inf\emptyset=+\infty$. |
| `triangularField` | $\nabla h_\triangle=-E_\triangle$, the triangular field in the sign convention of the lectures. |

The energies of the lectures carry the factor $\tfrac1{4\pi}$ where the paper has $\tfrac12$, so the triangular
value there is $W_\triangle/(2\pi)$ (`triangularField_spec`); the two energies also renormalize differently, and
for a general field they are related by an inequality, not an identity.

## Build

Requirements: [elan](https://github.com/leanprover/elan); the toolchain in `lean-toolchain`
(Lean 4.35.0) and Mathlib v4.35.0 are fetched by `lake`.

```bash
lake exe cache get          # Mathlib's compiled files, instead of compiling Mathlib
lake build                  # the core library SandierSerfaty
lake build SandierSerfatyCert   # the certificate library (see below)
```

`lake build` builds the core library: all 28 definitions and 8 of the 13 theorems.
From a fresh checkout (Mathlib from `lake exe cache get`) it takes about 4 minutes on a 16-core machine (about
35 CPU-minutes; peak memory 1.7 GB).

The five theorems that rest on the certificate (Theorems 1.1 and 1.2, Corollary 1.3 and the two Chapter 11
lower bounds) are in the library `SandierSerfatyCert`, which is **not** a default target: its 548 modules
under `SandierSerfaty/CertData` are mostly generated literal data, each family checked by the Lean kernel
(`decide +kernel`). Building it takes
about 2 hours 35 minutes on a 16-core machine with Lake's default parallelism, 14 to 17 CPU-hours in our measured
builds, with at most 3.7 GB of memory per Lean process. One shard can be built alone, for example
`lake build SandierSerfaty.CertData.Box.Both.S000`. The certificate data files and the proof scripts of the
shards are produced by the untrusted generator `lake exe certgen` (see [CertGen/Main.lean](CertGen/Main.lean));
building the library checks everything it wrote in the kernel, so the generator need not be run.

## Verify

```bash
python3 scripts/check-axioms.py --core    # after `lake build`: the eight core theorems
python3 scripts/check-axioms.py           # after `lake build SandierSerfatyCert`: all 13 and the certificate
python3 scripts/check_lean_modules.py --root .    # every .lean file is a module; size limits; comparator.json
python3 scripts/check_kernel_rules.py     # the kernel rules of the certificate modules
./scripts/verify-comparator.sh            # local comparator run: Solution against Challenge, three kernels
```

- **Axioms.** `scripts/Axioms.lean` prints `#print axioms` of every stated theorem and of the certificate
  (`SandierSerfaty.CertData.certificateGoal`); `check-axioms.py` checks that each depends only on
  `propext`, `Classical.choice` and `Quot.sound`.
- **Comparator.** [SandierSerfatyChallenge.lean](SandierSerfatyChallenge.lean) states the theorems with
  every definition they use, in one file that imports Mathlib only; one `sorry` per theorem marks what is to
  be proved. [SandierSerfatySolution.lean](SandierSerfatySolution.lean) proves the same statements from this
  repository. `lake comparator` (with the configuration [comparator.json](comparator.json)) checks that the
  statements and their dependency closures are identical, that only the three standard axioms are used, and
  replays the Solution through the Lean kernel and the independent kernels that ship with the toolchain. The
  Solution depends on the certificate library, so the comparator needs `lake build SandierSerfatyCert`
  first, and the replay of the certificate is as expensive as its check.
  [scripts/verify-comparator.sh](scripts/verify-comparator.sh) is a local verification procedure: it runs
  `lake comparator` from this project's toolchain, with the Lean kernel and the two independent kernels that
  the toolchain bundles, and requires all three to accept. It approximates the registry's check but is not the
  registry's official verification, which runs its own protected tool versions under its own rules.
  The comparator replays the whole dependency closure in the kernel, one declaration at a time, so for the five
  theorems that rest on the certificate a run takes roughly the certificate's CPU time as wall-clock time (we
  estimate about 15 hours; not measured). The eight theorems that do not depend on the certificate replay in
  about 4 minutes under all three kernels.
- **Source rules.** Every `.lean` file is a Lean module, none exceeds 1,500 lines, and the library contains
  no `sorry`, `admit`, `axiom`, `native_decide` or `unsafe`, and no `maxHeartbeats` or recursion-depth
  override.
- **Kernel rules.** `scripts/check_kernel_rules.py` lints the certificate modules (`SandierSerfaty/Certificate`
  and `SandierSerfaty/CertData`): every Boolean check is discharged by `decide +kernel`, never by
  `native_decide`, `decide +native`, plain `decide` or `rfl`, and the definitions the kernel evaluates in its hot
  loops use only `Nat` primitives, `cond` and structural recursion. Its docstring states the six rules. It is
  untrusted tooling and adds nothing to the trust base: it guards against slow or vacuous checks.

## Trust base

The Lean 4 kernel (v4.35.0) and Mathlib (v4.35.0, unmodified) are trusted, and nothing else. In particular
the library uses neither `native_decide` nor `Lean.ofReduceBool`: the finite computation of the paper is
carried out by `decide +kernel` on Boolean statements whose soundness is proved in the library, so it is
checked by the kernel. Ordinary `decide` also occurs, outside the certificate, on small decidable goals;
it is elaborator evaluation followed by a kernel check of the resulting proof, not native evaluation. The
generator `certgen` is untrusted native code: it writes the literal data files of `SandierSerfaty/CertData`
and the Lean proof scripts of the shards (the `decide +kernel` checks and the assembly proofs), and the kernel
checks everything it writes, so a defect in the generator can make the build fail but cannot make a false
theorem pass. What a reader must check is that the statements say what is intended: the 41 declarations of
[SandierSerfaty/Statements](SandierSerfaty/Statements), that is, the 28 definitions and the 13 theorem statements.
A mistake in a definition, or in a hypothesis, quantifier or conclusion of a theorem statement, could make a
theorem say less than intended without Lean noticing.

## Errata and deviations

[docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md) records where the Lean statements and proofs
differ from the printed sources, and reports every defect found in them, with a status (confirmed or
unverified) for each. It lists 4 errors, 18 gaps, 6 misprints and 1 unverified candidate in the sources
(29 items), and 12 deviations. Per source, as errors, gaps, misprints, unverified candidates and deviations:
Serfaty's lectures 4, 9, 2, 0 and 4; the OpenAI preprint 0, 8, 1, 0 and 8; Bétermin–Sandier 0, 1, 2, 1 and 0;
Sandier–Serfaty 0, 0, 1, 0 and 0; Brauchart–Hardin–Saff none. No entry changes a stated theorem. Headline
items:

- Lemma 11.2 of the lectures, the monotonicity inequality behind Proposition 11.3, is false in the boundary
  layer; the formalization does not use it.
- The lower bound for the jellium energy is proved by a different route from the lectures' (a screening
  construction with explicit fields, followed by Theorem 1.2), and Theorem 1.1 and Corollary 1.3 are proved
  by routes that do not use the papers of Sandier and Serfaty or Bétermin and Sandier that the preprint cites.
- Theorems 1.1 and 1.2 are stated with $W_\triangle$, the energy of the one-point triangular torus, in place
  of $W(E_\triangle)$; their identification is a separate theorem, and Theorem 1.1 is split into the lower
  bound and the triangular value.

## Credits and citation

The mathematics is that of the OpenAI preprint cited above, whose interval-arithmetic certificate (in its
`verification` folder) is replaced here by a certificate checked in Lean; of Serfaty's lectures, Chapter 11;
and of the following works, which are cited by those two and used here as references:

- É. Sandier and S. Serfaty, *From the Ginzburg–Landau model to vortex lattice problems*, Comm. Math. Phys.
  313 (2012), [arXiv:1011.4617](https://arxiv.org/abs/1011.4617).
- L. Bétermin and É. Sandier, *Renormalized energy and asymptotic expansion of optimal logarithmic energy on
  the sphere*, Constr. Approx. 47 (2018), [arXiv:1404.4485](https://arxiv.org/abs/1404.4485).
- J. S. Brauchart, D. P. Hardin and E. B. Saff, *The next-order term for optimal Riesz and logarithmic energy
  asymptotics on the sphere*, Contemp. Math. 578 (2012), [arXiv:1202.4037](https://arxiv.org/abs/1202.4037).

If you use this formalization, please cite it as in [CITATION.cff](CITATION.cff), together with the preprint.
The preprint and these works are not part of this repository and are not covered by its license.

The two arithmetic files whose headers name Zohar Komargodski,
[Interface.lean](SandierSerfaty/Certificate/Arith/Interface.lean) and
[PiHigh.lean](SandierSerfaty/Certificate/Arith/PiHigh.lean), are adapted from an earlier, unpublished
formalization by S. Armstrong and Z. Komargodski.

S. Armstrong was supported by the European Research Council (ERC) under the European Union's Horizon
Europe research and innovation programme, grant agreement number 101200828. S. Serfaty was supported by a
Simons Investigator award, NSF grant DMS-2247846, and the Institut Universitaire de France. The authors of the
preprint have not reviewed this formalization.

## Authors and license

- Scott Armstrong, CNRS & Laboratoire Jacques-Louis Lions, Sorbonne Université and Courant Institute School
  of Mathematics, Computing, and Data Science, New York University.
- Sylvia Serfaty, Laboratoire Jacques-Louis Lions, Sorbonne Université and Courant Institute School of
  Mathematics, Computing, and Data Science, New York University.

All files of this repository, including the notes in [notes/](notes) (TeX sources and PDFs), are released
under the [Apache License 2.0](LICENSE).
