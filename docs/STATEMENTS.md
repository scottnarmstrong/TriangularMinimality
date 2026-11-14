# The statements

This page sets out what the Lean proves: 13 theorem statements and the 28 definitions they use. Each is a file of
[SandierSerfaty/Statements](../SandierSerfaty/Statements) (namespace `SandierSerfaty`, theorems in `*/Theorems/`,
definitions in `*/Defs/`), and all 41 are repeated, verbatim and with nothing else, in
[SandierSerfatyChallenge.lean](../SandierSerfatyChallenge.lean), a single file that imports only Mathlib (namespace
`SandierSerfatyChallenge`). These 41 declarations are what a reader has to check to know what has been proved;
everything else in the repository is proof.

Each Lean block below is copied from the Challenge up to the `:=` that ends the statement, with its docstring
omitted. In the files of `SandierSerfaty/Statements`, the comment lines `-- PREFIX_BEGIN`, `-- PROOF_BEGIN`,
`-- PROOF_END`, `-- SUFFIX_BEGIN` and `-- SUFFIX_END` delimit the proof of each theorem, so that a checker can confirm
that the text of the statement is unchanged.

Statement and equation numbers are those of the OpenAI preprint and of Serfaty's lectures
([arXiv:2407.21194](https://arxiv.org/abs/2407.21194)).

1. [The main results](#1-the-main-results)
2. [The statements that make the definitions meaningful](#2-the-statements-that-make-the-definitions-meaningful)
3. [The definitions](#3-the-definitions)

## 1. The main results

### Theorem 1.2 (square tori)

> For every integer $n\ge2$ and every $n$ points $a_1,\dots,a_n$ of the torus $T_n=\mathbb C/(\sqrt n\,\mathbb Z[i])$
> that are pairwise distinct modulo the lattice, the mean-zero periodic potential $h$ with
> $-\Delta h=2\pi\bigl(\sum_i\delta_{a_i}-1\bigr)$ has energy
> $\mathcal W_n(h)=\lim_{\eta\downarrow0}\bigl[\tfrac12\int_{T_n\setminus\bigcup_iB(a_i,\eta)}\vert\nabla h\vert^2+\pi n\log\eta\bigr]\ge n\,W_\triangle$.

Here $W_\triangle$ is the energy of the one-point torus of the triangular lattice, which equals the energy
$W(E_\triangle)$ of the paper (this identification is `paperTriangularField_spec`). Lean:
`mul_triangularEnergy_le_torusEnergy`, in
[MulTriangularEnergyLeTorusEnergy.lean](../SandierSerfaty/Statements/Torus/Theorems/MulTriangularEnergyLeTorusEnergy.lean).

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
[TriangularEnergyLeWholeEnergy.lean](../SandierSerfaty/Statements/Whole/Theorems/TriangularEnergyLeWholeEnergy.lean),
and `paperTriangularField_spec` in
[PaperTriangularFieldSpec.lean](../SandierSerfaty/Statements/Whole/Theorems/PaperTriangularFieldSpec.lean), which says
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
[SphereLogEnergyAsymptotics.lean](../SandierSerfaty/Statements/Sphere/Theorems/SphereLogEnergyAsymptotics.lean). The
formal statement gives a remainder $r(n)=o(n)$ with an exact identity for every $n\ge2$. In Lean $E_{\log}(n)$
is the infimum, `sphereLogEnergy n`. That it is attained is proved in the library, though it is not one of
the 13 stated theorems: `SandierSerfaty.Sphere.exists_isSphereMinimizer` (in
[Sphere/Minimizer.lean](../SandierSerfaty/Sphere/Minimizer.lean)) gives a minimizer for every $n$, and
`SandierSerfaty.Sphere.Bridge.sphereLogEnergy_eq` (in
[Sphere/Bridge/LogEnergy.lean](../SandierSerfaty/Sphere/Bridge/LogEnergy.lean)) shows that the energy of every
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
$C_0(\mathrm{card}(C\cap\square_R)-R^2)$, and is $+\infty$ when $C$ does not have density one. Then
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

## 2. The statements that make the definitions meaningful

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

## 3. The definitions

The statements use 28 definitions, all written out in [SandierSerfatyChallenge.lean](../SandierSerfatyChallenge.lean)
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
| `neutralEnergy` | `neutralEnergy C E` is $W^{\mathrm{neu}}(E,1)=\limsup_{\ell\to\infty}\ell^{-2}F^{\square_\ell}(E,1)$ if $\mathrm{card}(C\cap\square_\ell)/\ell^2\to1$, and $+\infty$ otherwise. |
| `jelliumEnergy` | `jelliumEnergy C0 C E` is $W_{C_0}(E,1)=\limsup_{R\to\infty}R^{-2}[F^{\square_R}(E,1)+C_0(\mathrm{card}(C\cap\square_R)-R^2)]$ of Definition 11.4. |
| `configEnergy` | `configEnergy C` is $\mathbb W(C,1)$ of Definition 11.6: the infimum of $W^{\mathrm{neu}}(E,1)$ over the fields $E\in\mathrm{Elec}(C,1)$ that are distributional gradients, with $\inf\emptyset=+\infty$. |
| `triangularField` | $\nabla h_\triangle=-E_\triangle$, the triangular field in the sign convention of the lectures. |

The energies of the lectures carry the factor $\tfrac1{4\pi}$ where the paper has $\tfrac12$, so the triangular
value there is $W_\triangle/(2\pi)$ (`triangularField_spec`); the two energies also renormalize differently, and
for a general field they are related by an inequality, not an identity.
