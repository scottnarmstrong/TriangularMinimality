# Errata and deviations

This record lists every defect found in the printed sources of this formalization, and every place where the
Lean statements or proofs deliberately differ from them. It is written for a reader who knows nothing of the
project and wants to compare a Lean theorem with the paper or the book it formalizes.

## How to read this record

For each source the entries come in five groups, always in this order:

1. **Errors.** A printed assertion is false, or a printed formula is wrong in a way that needs a counterexample
   or a non-trivial repair.
2. **Gaps.** The printed statement is true (or believed true), but the written argument does not prove a step
   that a careful reader needs. Each gap says how the formal proof supplies the step or avoids it.
3. **Misprints.** A printed formula, symbol or phrase is wrong or undefined, its intended meaning is clear from
   the surrounding text, and correcting it changes no argument.
4. **Unverified candidates.** A suspected defect that could not be checked, because the material it depends on is
   not among the pinned sources.
5. **Deviations.** A deliberate difference between a Lean statement or proof and the source that is not a source
   defect: a different proof route, a reformulated or strengthened statement, a convention fixed where the
   text is ambiguous, or a reading of an ambiguous phrase.

Every entry gives the source's own numbering, what is printed, why it fails, the correction, the effect on the
formal development, and a status:

- **confirmed:** checked against the pinned source by an independent reader who tried to refute it;
- **candidate:** reported by one reader and not independently confirmed (no entry currently has this status);
- **unverified:** cannot be checked from the pinned sources.

Where an entry has a part that was not checked (for instance a downstream consequence), the status says so.

Sources and the versions pinned:

- **The preprint:** OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, preprint of
  23 September 2026, as published in the repository `openai/math` (commit
  `4eaee87548250b2682affda7d05d947c05554bae`). Locations are given by the title of the section and by the label
  of the statement in its LaTeX source (for example `cal:green-expansion`), because section numbers depend on
  the compiled document.
- **The lectures:** S. Serfaty, *Lectures on Coulomb and Riesz gases*, arXiv:2407.21194v1. Locations are
  given by the printed statement and equation numbers, and by page where a formula had to be read on the page.
- **Bétermin–Sandier:** L. Bétermin and É. Sandier, *Renormalized energy and asymptotic expansion of optimal
  logarithmic energy on the sphere*, arXiv:1404.4485v5. Locations are given by section and page of that
  version.
- **Sandier–Serfaty:** É. Sandier and S. Serfaty, *From the Ginzburg–Landau model to vortex lattice problems*,
  arXiv:1011.4617v2.
- **Brauchart–Hardin–Saff:** J. S. Brauchart, D. P. Hardin and E. B. Saff, *The next-order term for optimal Riesz
  and logarithmic energy asymptotics on the sphere*, arXiv:1202.4037v1.

Counting convention: entries, not occurrences; a grouped entry covers repeated occurrences. A difference of
notation between two sections of a source (for instance the charges called $a_i$ in one section of the preprint
and $v_i$ in another) is not counted. Suspected defects that turned out not to be defects are not listed.

No entry changes a theorem proved in this repository, and none is a defect in a main theorem of a source. The
theorems of the preprint are proved as stated, up to the deviations below. From the lectures, the formal
statements cover one result of Chapter 11, in the case treated by the preprint only: dimension $d=2$, the
logarithmic interaction ($s=0$) and background density $m=1$. That result is the minimality of the triangular
lattice for the jellium energies of Definitions 11.4 and 11.6, which is the preprint's theorem transferred to
the normalization of the lectures. The other results of Chapter 11, and the general cases, are not
formalized. The 13 stated theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. None of the
entries is certified by a Lean theorem: each is explained here, and the Lean statements are the corrected ones
where a correction matters. A passage of a source that an entry calls unused is not used by the formal proofs.

| Source | Errors | Gaps | Misprints | Unverified | Deviations |
|---|---|---|---|---|---|
| Serfaty, *Lectures on Coulomb and Riesz gases* | 4 | 9 | 2 | 0 | 4 |
| The OpenAI preprint | 0 | 8 | 1 | 0 | 8 |
| Bétermin–Sandier | 0 | 1 | 2 | 1 | 0 |
| Sandier–Serfaty | 0 | 0 | 1 | 0 | 0 |
| Brauchart–Hardin–Saff | 0 | 0 | 0 | 0 | 0 |
| **Total** | **4** | **18** | **6** | **1** | **12** |

In all, 29 defects and suspected defects are reported (4 errors, 18 gaps, 6 misprints and 1 unverified
candidate), together with 12 deviations.

## Serfaty, *Lectures on Coulomb and Riesz gases*

The formal statements use the definitions of Chapter 11 (Definitions 11.1, 11.4 and 11.6 and the
truncations (11.2.2)–(11.2.6)) for $d=2$, $s=0$ and $m=1$ only. They prove that the triangular lattice
minimizes the jellium energy, for fields and for configurations, and that its energy is
$W_\triangle/(2\pi)$. They do not formalize the other results of the chapter, such as Lemma 11.2,
Proposition 11.3, Lemma 11.9 and Proposition 11.13, or the cases of other dimensions, kernels and densities.
The entries below were found while reading the passages that these definitions and the proofs of the chapter
use.

### Errors

1. **Lemma 11.2, inequality (11.2.7) (p. 229); the same step in Lemma 4.29, inequality (4.5.7), and in
   (7.1.37).** Printed: for any radii $\eta_p\ge\tilde r_p$, with equality unless $B(p,\eta_p)\subset\square_R$,
   the energy truncated at the radii $\eta$, plus $\tfrac12\sum(g(p-q)-g(\eta_p))_+$ over pairs of points with
   $\mathrm{dist}(p,\partial\square_R)\ge\eta_p$, is at most $F^{\square_R}(E,m)$. Why it fails: the radii
   $\eta=\tilde r$ are allowed, and then the truncated energy is exactly $F^{\square_R}(E,m)$, so the inequality
   forces the pair sum to vanish whenever $F^{\square_R}(E,m)$ is finite. It does not vanish when two points are
   closer than $\tilde r_p$ in the boundary or transition layer. Counterexample ($d=2$, $s=0$, $m=1$): by
   (11.2.3) a point $p$ at distance $0.5$ from $\partial\square_R$ has $\tilde r_p=\tfrac14$; take
   $\eta_p=\tilde r_p$, which is allowed, and a point $q$ at distance $0.01$ from $p$. Then $p$ belongs to the
   pair sum, whose term $(g(0.01)-g(\tfrac14))_+=\log 100-\log 4=\log 25$ is positive, while a field in
   $\mathrm{Elec}(\mathcal C,1)$ with finite energy and these two points exists (a gradient with logarithmic
   singularities). In the proof of (4.5.7) the failure is in (4.5.9) ("the right-hand side of (4.5.8)
   vanishes"), which needs the balls of radii $\tilde r$ to be disjoint; in the layers they are not. The same
   argument excludes the choice $\alpha=\tfrac14\lambda$ used in Proposition 4.28. Correction: with
   $\alpha=\tilde r\le\eta$,
   $F^{\tilde r}-F^{\eta}\ge\tfrac12\sum_{p:\,B(p,\eta_p)\subset\square_R}\sum_{q\ne p}\bigl(g_{\tilde r_p}(\vert p-q\vert+\tilde r_q)-g(\eta_p)\bigr)_+$
   (the functions $g$ and $g_r$ as in the lectures); alternatively the pair sum is restricted to points with
   $\mathrm{dist}(p,\partial\square_R)\ge\eta_p+5/2$ (the second form was checked only in outline). Effect: the
   proof of Proposition 11.3, which applies Lemma 11.2, has to be redone with the corrected inequality; its
   conclusions (11.2.8)–(11.2.10) remain true, as checked for $d=2$, $s=0$, $m=1$ (the case relevant here) and
   not in general. The screening proof of Appendix A uses (7.1.37) at one place, and the corrected inequality
   suffices there if the half-width of the localization strip in (A.0.3), (A.0.4) and (A.0.7) goes from $2$ to
   $4$; this change of constants was not re-derived independently. The same step is used in Proposition 4.28
   (its (4.5.11)–(4.5.13) keep one term of the pair sum to obtain (4.5.4)) and, by copying the argument
   "without change", in (7.1.35)–(7.1.36); the same repair is expected to work there, since the shifts change
   only constants, but this was not checked. The formal proofs do not use Lemma 11.2 (see deviation 4 below).
   Status: confirmed (the defect, the counterexample and the correction); the effect on Proposition 4.28 and on
   (7.1.35)–(7.1.36), and the change of half-width, are not checked.
2. **Lemma 11.9, inequality (11.2.19), and (11.2.21).** Printed:
   $\vert C(\square_R)-mR^d\vert^2\le C R^{2d-\varepsilon}(1+W(E,m))$. Why it fails: the right side is negative
   when $W(E,m)\lt-1$, so the bound is false there, and that case occurs. By the scaling law (11.2.17), for
   $s=0$, $W(E,m)=m\,W(\sigma_mE,1)-\tfrac1{2d}\,m\log m$. For $d=2$, if $w=W(\sigma_mE,1)$ is finite and does
   not depend on $m$ (for instance $E$ the field of a lattice, rescaled with $m$), then
   $W(E,m)=m\bigl(w-\tfrac14\log m\bigr)\lt-1$ for all large $m$. Moreover, in the proof the discrepancy layer
   should be $\square_{R+\delta}\setminus\square_R$ with $\delta=R^{\gamma+\varepsilon}$, the layer width of
   Lemma 4.25 that the proof invokes, which is much larger than $1$ for large $R$; it is not
   $\square_{R\pm1}$ as in (11.2.21). Correction: the bound $C\bigl(W(E,m)+C_0'+1\bigr)$ with a suitable
   constant $C_0'$, with the integral taken over $\square_{2R}$. Effect: none on the formal proofs, which do not
   use Lemma 11.9 (the lectures use it in Corollary 11.10 and in the proof of Proposition 11.13). Status:
   confirmed.
3. **Appendix A, Lemma A.2, last line of its proof.** Printed: $G_R(x,y)\le C g(x-y)$ for the Neumann
   Green function of a hyperrectangle $R$ with background, where $u$ is the mean-zero solution (A.0.11). Why it
   fails: the mean-zero Green function of a rectangle of side $a$ equals $g(x-y)+\log a+O(1)$ (rescaling
   introduces no further shift), so for $d=2$ and $\vert x-y\vert$ of the order of $a\gg1$ it is $O(1)$, whereas
   $C g(x-y)\approx-C\log a\to-\infty$. Correction: $G_R(x,y)\le g(x-y)+\log a+C$, and the term
   $(\#I)^2a^{2-d}$ in (A.0.12) changes accordingly (for $d=2$ it becomes $(\#I)^2\,O(\log a)$). Effect:
   constants only; the formal proofs do not use Lemma A.2. Status: confirmed.
4. **Appendix A, the definition of the second vector field $E_2$ (before (A.0.18), pp. 282–283).** Printed:
   "$-\Delta h_{2,k}=c_d\,m_k$ in $H_k$" with Neumann datum $g_k=-E_{\hat r}\cdot\nu+n_k/\vert F_k\vert$ on
   $\partial H_k$. Why it fails: this Neumann problem is solvable only if
   $c_d m_k\vert H_k\vert=\int E\cdot\nu-n_k$, which follows from (A.0.14) only when $\eta=0$. For $\eta\gt0$ the
   field $E_3$ of (A.0.19) lives in the layer $N_\eta$ only, so in $H_k\setminus H_k^\eta$, which contains no
   points, the field $E_2$ must itself have divergence $-c_d\mu$ for (A.0.20) to hold. Correction:
   $-\Delta h_{2,k}=c_d\bigl(m_k\mathbf 1_{H_k^\eta}-\mu\,\mathbf 1_{H_k\setminus H_k^\eta}\bigr)$, which gives
   both the solvability and (A.0.20). Effect: none on the stated results; the screening construction used in the
   formal proofs (deviation 4) is built from the corrected equation. Status: confirmed.

### Gaps

1. **Proposition 7.10 and Corollary 7.11, as used with (7.1.57) in the screening argument.** Missing: the
   screening argument needs a configuration $Z$ in the thin layer $N_\eta$ with
   $F(Z,\tilde\mu,N_\eta)\le C\vert N_\eta\vert$. The cited bound $\vert E_\infty(\mu,U)\vert\le CN$ gives no
   explicit dependence of $C$ on $U$, and for $s\le0$ its proof tiles with Lemma 5.13, which needs $\mu\ge m$
   and a $C^1$ boundary, hypotheses that Proposition 7.10 does not state. Resolution: in the screening
   construction $\tilde\mu$ is piecewise constant on cells of integer mass, so one cuts each cell into
   unit-mass rectangles of bounded aspect ratio, puts one point in each rectangle and glues by Neumann
   subadditivity ((7.1.29), (7.1.58)). The formal proof avoids the gap: its screening builds the layer
   configuration from explicit integer-mass cuts. Status: confirmed.
2. **Proposition 7.18 and Definition 7.14: gradient fields versus fields.** Missing: screening is stated for
   gradients $E=\nabla w$, but the proof of Proposition 11.13 applies it to arbitrary fields of
   $\mathrm{Elec}(\cdot,1)$ (Definition 11.1 notes that such fields need not be gradients). Resolution: the proof
   of the screening uses only the divergence and the normal data, so it extends to fields; no statement in the
   lectures says so. The formal proof screens fields directly. Status: confirmed.
3. **Proposition 7.18 and Definition 7.14 versus Appendix A: the hypothesis $\ell\ge1$ or $\ell\ge C$.** The
   statements ask only $\tilde\ell\ge\ell\ge1$, whereas the proof in Appendix A assumes "$\tilde\ell\ge\ell\ge C$"
   and $\ell\gt C\gt2\eta$ to build the strips. Resolution: the statement is true, because the
   constants may depend on $d$, $m$ and $\Vert\mu\Vert$. If $\ell\lt C_0$, replace $\ell$ by $\ell'=C_0$:
   screenability (7.2.8) is monotone in $\ell$ and so holds at $\ell'$, the larger cubes cost at most a factor
   $C$, the condition $\eta\le\ell m/(4\Vert\mu\Vert)$ is preserved, and all error terms stay comparable since
   $\ell'\le C_0\ell$. One sentence repairs it. The formal screening works with explicit parameter windows, so
   the needed lower bound on $\ell$ is part of its statement. Status: confirmed.
4. **(7.2.17) and (11.4.5): matching of truncations.** Missing: identifying the right side of (7.2.17) with
   $F^{\square_R}(E_k,1)$ requires that the truncations of the charges outside $\Omega'$ match, which is not
   argued. Minor. The formal proof avoids the gap (it does not use these identifications). Status: confirmed.
5. **Lemma 11.8: "the infimum in (11.2.14) is a minimum".** Missing: attainment of the infimum over the constant
   shift $a$ is not shown. Not used by the formal proofs. Status: confirmed.
6. **Proof of Proposition 11.11, (11.3.5): cell average.** Missing: the identification of
   $\limsup R^{-d}F^{\square_R}(\nabla H)$ over centred cubes with the average over one cell is omitted. It needs
   the boundary layer of $\tilde r$, the fact that cubes are not unions of cells, the $C_0$ term, and also
   $\vert T\vert=N$. The formal proof of the corresponding result carries out this identification. Status:
   confirmed.
7. **Proof of Proposition 11.13: choice of the screening parameters.** Missing: the parameters
   $\ell,\tilde\ell,\eta,\Omega',\Omega''$ are not specified, and the choice of Theorem 8.1 does not give
   $o(R^d)$. Minor: a valid choice exists (the parameter window $\kappa\in(0,2/7)$ of the screening
   proposition). The formal screening states its parameters. Status: confirmed.
8. **Proof of Proposition 11.13: the periodization identity.** Missing: $W(E_{k,R},1)=F(X_R,\square_R)$ is
   asserted "by periodicity". One must show that the periodized field lies in $\mathrm{Elec}$ (no divergence
   across faces), that the screened configuration avoids $\partial\square_R$ (no doubled points), and that the
   Neumann radii $\hat r$ of (7.1.22) agree with the periodic $r_p$. The formal proof avoids the gap: it
   projects the screened configuration onto a square torus explicitly. Status: confirmed.
9. **Appendix A, the partition into hyperrectangles of integer mass (A.0.14)–(A.0.15).** Missing: the partition
   with $\int_{H_k^\eta}(\mu+m_k)\in\mathbb N$ is "obtained by successive strips as in Lemma 5.13" but the
   argument is not carried out. Both the partition and the numbers $m_k$ are constrained: $m_k$ depends on
   the partition through the flux, and the integrality constrains the partition, so the two have to be chosen
   simultaneously. The formal proof constructs the integer-mass cuts explicitly. Status: confirmed.

### Misprints

1. **Theorem 5.2, (5.3.4) (p. 119).** Printed:
   $\min_{i\ne j}\vert x_i-x_j\vert\ge C/(N\Vert(-\Delta V)_+\Vert_{L^\infty})^{1/d}$. The hypothesis is
   $(\Delta V)_+\in L^\infty$, and the proof ((5.3.5)) bounds the separation by $\Vert(\Delta V)_+\Vert_{L^\infty}$.
   As printed the bound is meaningless or false when $\Delta V\ge0$: for $V=\log(1+\vert x\vert^2)$,
   $\Delta V=4/(1+\vert x\vert^2)^2\gt0$, so $(-\Delta V)_+=0$, the denominator is zero, and the bound read
   literally says that the separation is at least $+\infty$. The quantity that appears is $(\Delta V)_+$: for
   $d=2$ the average of $V$ over $\partial B_\eta(x_i)$ minus $V(x_i)$ is at most
   $\tfrac{\eta^2}{4}\Vert(\Delta V)_+\Vert_{L^\infty}$. Correction: $\Vert(\Delta V)_+\Vert_{L^\infty}$. Effect: the corrected bound is the one
   used in the proof of the separation of minimizers on the sphere (the proof of Corollary 1.3 of the
   preprint); the statement of Corollary 1.3 is unaffected. Status: confirmed.
2. **Proof of Proposition 11.13, the display $W(E_{k,R},1)=F(X_R,\square_R)$ (before (11.4.5)).** Printed
   without the normalization $1/R^d$ of (11.2.12), although $W$ is a mean per unit volume and the next line
   (11.4.5) is in the unnormalized form. Correction: $F(X_R,\square_R)/R^d$. Effect: none. Status: confirmed.

### Unverified candidates

None.

### Deviations

1. **Configurations are sets.** In the statements of the Chapter 11 theorems a configuration is a set of
   points of $\mathbb C$ (`Set ℂ`), hence simple, whereas the lectures' $\mathbb X(\mathbb R^2)$ allows
   multiplicities. Effect: none on the content; for a configuration with a multiple point the energy of the
   lectures is $+\infty$ on all large cubes ($r_p=0$ for a multiple point when $s\ge0$, by (11.2.2), and then
   $F^{\square_R}=+\infty$ by (11.2.6)), so the bounds hold trivially there. See
   [DivTwoPiTriangularEnergyLeNeutralEnergy.lean](../SandierSerfaty/Statements/Jellium/Theorems/DivTwoPiTriangularEnergyLeNeutralEnergy.lean).
2. **The lower bound is stated for the neutral energy, with the bridge to Definition 11.4.** For $m=1$,
   Definition 11.4 sets
   $W_{C_0}(E,1)=\limsup_{R\to\infty}R^{-2}\bigl(F^{\square_R}(E,1)+C_0(\mathcal C(\square_R)-R^2)\bigr)$,
   where $\mathcal C(\square_R)$ is the number of points in $\square_R$. The formal statements use instead the
   neutral energy $W^{\mathrm{neu}}(E,1)$ (`neutralEnergy`), in the extended reals. It is
   $\limsup_{R\to\infty}R^{-2}F^{\square_R}(E,1)$ when the configuration has density one, that is
   $\mathcal C(\square_R)/R^2\to1$, and $+\infty$ otherwise. For a configuration without density one the
   lower bound for $W^{\mathrm{neu}}$ therefore holds trivially. A separate theorem,
   `exists_jelliumEnergy_eq_neutralEnergy`, shows that $W_{C_0}(E,1)=W^{\mathrm{neu}}(E,1)$ for every
   configuration, every $E\in\mathrm{Elec}(\mathcal C,1)$ and every sufficiently large $C_0$ (the formal proof
   gives $C_0\ge\log 2+\pi/32$; the lectures only say "the constant of (11.2.8) and (11.2.9)", that is, a
   sufficiently large one). In particular $W_{C_0}(E,1)=+\infty$ as well when the configuration does not have
   density one, consistent with the conclusion of Lemma 11.9 that finite energy forces density one (its
   printed bound is corrected in error 2 above), so the cutoff at density one loses nothing. The energy of a
   configuration $\mathbb W(\mathcal C,1)$ of Definition 11.6, (11.2.14), is likewise formed with
   $W^{\mathrm{neu}}$ in place of $W_{C_0}$ (`configEnergy`). Since the two energies agree field by field for
   large $C_0$, the two infima agree. Effect: the bounds for the energies of Definitions 11.4 and 11.6 follow
   from the stated theorems together with the bridge theorem. See
   [ExistsJelliumEnergyEqNeutralEnergy.lean](../SandierSerfaty/Statements/Jellium/Theorems/ExistsJelliumEnergyEqNeutralEnergy.lean).
3. **Proposition 11.13, (11.4.1)–(11.4.2): minimum, infimum, limit and limit superior.** The proposition prints
   a minimum and a limit: $\lim_R R^{-d}\inf F(\cdot,m,\square_R)\le\min W(\cdot,m)$ and
   $\min W(\cdot,m)=\lim_R\min_{\text{periodic}}W(\cdot,m)$. The "min" anticipates the attainment of minima in
   Corollary 12.4, so it is not an error. For (11.4.2) the proof gives the limit: (11.4.5) with $k,R\to\infty$
   gives $\limsup_R\min_{\text{periodic}}W\le\inf W$, and the converse inequality is "trivial". For (11.4.1) the
   proof bounds only the limit superior, so the existence of the limit is not shown. We read "min" as the
   infimum and, in (11.4.1), "lim" as the limit superior. The formal statements do not formalize Proposition
   11.13: their energies use the limit superior (Definition 11.4) and the infimum (Definition 11.6), as the
   lectures' own definitions do. Effect: none on any formal statement.
4. **A different proof of the lower bound for configurations and fields.** The lectures prove the lower bound
   through Lemma 11.2, Proposition 11.3, Lemma 11.9, the screening Proposition 7.18 with Appendix A (Neumann
   problems), and Proposition 11.13. The formal proof uses none of these; it screens a configuration on a
   square by explicit fields, projects it onto a square torus, and applies Theorem 1.2 of the preprint. The
   printed route needs repairs (errors 1, 3 and 4 above) and arguments that the text omits (gaps 1–4 and 7–9
   above); the formal construction supplies the corresponding statements with explicit constants. Effect: none
   on the statements.

## The OpenAI preprint

### Errors

None.

### Gaps

1. **Section "From square tori to the full plane", Lemma `red:plane-bound`, the choice of the radii $s_\pm$.**
   Missing: radii with the boundary integrals of $\vert j'\vert^r$ at most $Ct^2(\log t)^{r/2}$ and no charge on
   the boundary are asserted. They come from a Chebyshev argument on the coarea average, with the constant
   doubled, intersected with the cofinite set of radii that carry no charge; the text compresses this. Minor.
   Not used by the formal proofs, which reach Theorem 1.1 by a different route (deviation 2 below). Status:
   confirmed.
2. **Section "Voronoi sectors and a glued dual potential", Lemma `geo:voronoi` (periodic Voronoi geometry).**
   Missing: "each vertex has degree at least three, indeed a Voronoi vertex has at least three nearest sites"
   does not argue the passage from nearest sites to edges (a vertex is never defined, and "maximal
   positive-length edge" is not connected to "side of the cell"). The assertion that the cells tile the torus
   with total area $n$ ("summing areas and angles over the $n$ quotient faces") needs that the cells cover the
   plane (a nearest site exists since the lattice of sites is discrete) and have disjoint interiors, so that the
   $n$ representative cells form a fundamental domain up to a null set; neither is stated. "Each open face is a
   disk" is justified only by injectivity of the quotient map, and that a convex open polygon is a disk is a
   separate fact. The formal proof proves the tiling and the total area $n$, and proves the bound of at most
   $6n$ incidences by a sector fan and an angle-packing argument, without the Euler characteristic. Minor.
   Status: confirmed.
3. **Section "Voronoi sectors and a glued dual potential", definition `dual:torus-energy`: the torus version of
   the local puncture lemma.** Missing: the text says "the local calculation in Lemma `red:local`, applied in a
   torus chart, gives the finite puncture limit", but `red:local` is stated for fields on $\mathbb R^2$ with a
   compactly supported cutoff, and the torus statement is not literally an instance of it. The finiteness of
   the limit needs the local expansion at each site, smoothness elsewhere, and the lift of the field to the
   periodic lattice. The formal proof states and proves the torus version. Minor. Status: confirmed.
4. **Section "Calibration on the triangular cell", before `cal:constants` and in the proof of Lemma
   `cal:stationarity`: regularity and differentiation under the integral sign.** Missing: it is used that the
   radial functions $f_0$ and $e$ are $C^1$ on $(0,\infty)$, so that the integrand $(f_0(t)-f_0(p))/s^2$ extends
   continuously to $s=0$ with value $f_0'(p)/(2p)$, and that one may differentiate under the integral sign in
   the stationarity computation; neither is proved. (The termwise integration that produces $f_0$ and $e$ is
   justified by the estimates of the next section.) The formal proof derives both from the tail bounds.
   Status: confirmed.
5. **Section "Calibration on the triangular cell", Lemma `cal:energy-identity`: the regular hexagon.** Missing:
   the proof says that "its regular Voronoi hexagon supplies six compatible sectors with $d=p$ and
   $\alpha=\beta=\pi/6$". This needs three facts, none stated: the Voronoi cell of the triangular lattice
   $a\mathbb Z[\omega]$ is the regular hexagon with normals $a\omega^j$; its incidences are exactly six sectors
   $S(p,\pi/6,\pi/6)$, each of area $1/6$; and the mean-zero torus potential equals $h_\triangle$, so that
   $H=h_\triangle-C_\triangle$ on the cell gives $\nabla H=\nabla h_\triangle$ on the torus. The formal proof
   proves them. Status: confirmed.
6. **Section "Infinite-mode truncation and error propagation", subsection "Uniform derivative bounds for omitted
   modes" (`tail:radial-derivatives`): the binomial comparison.** Missing: "the coefficient comparison that
   proves this is $j(j-1)\cdots(j-\ell+1)\binom{k}{2j}\le k^{2\ell}\binom{k-2\ell}{2j-2\ell}$" is asserted
   without proof, and the bound $597k^5(3/5)^k$ on $[p,p+.01]$ rests on it. The inequality is true: the ratio of
   the two binomials is $k(k-1)\cdots(k-2\ell+1)/\bigl(2j(2j-1)\cdots(2j-2\ell+1)\bigr)$, and
   $j(j-1)\cdots(j-\ell+1)/\bigl(2j(2j-1)\cdots(2j-2\ell+1)\bigr)\le1$ for $j\ge\ell$. The formal proof proves it.
   Status: confirmed.
7. **Section "Infinite-mode truncation and error propagation", subsection "Norms and bounds for retained modes"
   (`tail:norms`): submultiplicativity of the jet norms.** Missing: "these norms are submultiplicative" is
   asserted without proof, and is used in the estimates for the sector functions. It is true: the jet
   coefficients multiply by Cauchy product, and one-sided jets at the knots are handled because both factors
   use the same side. The formal proof proves it. Status: confirmed.
8. **Section "The finite scalar verification": the correspondence between program and mathematics.** Missing:
   Theorem `comp:scalar` and Proposition `comp:finite-soundness` reduce to the assertion that every listed
   finite check holds, and the only support is an external run of a C++ program. The text says that "the
   source-to-code and analytic correspondences are separate arguments", and gives none: nothing in the
   preprint shows that the program implements the procedure described. A reader's check of the correspondence
   found no mismatch that affects soundness. The formal proof replaces the program by a certificate checked in
   Lean (deviation 4 below). Status: confirmed.

### Misprints

1. **Section "Calibration on the triangular cell", Lemma `cal:green-expansion`, display `cal:green-series`.**
   The lemma states the expansion of the triangular Green function for $0\lt\vert z\vert\lt a$ and continues
   "the series and all of its derivatives converge locally away from $\vert z\vert=a$". The series is a power
   series in $z^6$ of radius exactly $a$ (its coefficients satisfy $c_m\sim a^{-6m}/m$); it does not converge
   for $\vert z\vert\gt a$. Correction: it converges locally uniformly, with all its derivatives, for
   $\vert z\vert\lt a$, which is the range in which the expansion is stated and the only one used. (The proof's
   own wording, "converges normally on every smaller disk", is correct.) Effect: none. Status: confirmed.

### Unverified candidates

None.

### Deviations

1. **Theorems 1.1 and 1.2 are stated with the triangular value $W_\triangle$, and Theorem 1.1 is split in
   two.** The preprint states both theorems with $W(E_\triangle)$, the energy of the whole-plane field
   $E_\triangle$. The formal statements use $W_\triangle$, the energy of the one-point triangular torus
   (`triangularEnergy`), which involves no cutoff and is what the proof produces. Theorem 1.2 is stated with
   the right side $n\,W_\triangle$ (`mul_triangularEnergy_le_torusEnergy`). Theorem 1.1 is stated as two
   theorems, each quantified over all cutoff families as in (1.1):
   `triangularEnergy_le_wholeEnergy` says that $W(E)\ge W_\triangle$ for every cutoff family and every
   $E\in\mathcal A_1$; `paperTriangularField_spec` says that $E_\triangle\in\mathcal A_1$ and that
   $W(E_\triangle)=W_\triangle$ for every cutoff family. Together they give the inequality
   $W(E)\ge W(E_\triangle)$ of Theorem 1.1, the finiteness of the triangular value, and
   $\inf_{\mathcal A_1}W=W(E_\triangle)$, attained at $E_\triangle$. The last identity follows at once but is
   not stated as one formula. The identification $W(E_\triangle)=W_\triangle$ also makes the two forms of
   Theorem 1.2 equivalent. See
   [PaperTriangularFieldSpec.lean](../SandierSerfaty/Statements/Whole/Theorems/PaperTriangularFieldSpec.lean) and
   [MulTriangularEnergyLeTorusEnergy.lean](../SandierSerfaty/Statements/Torus/Theorems/MulTriangularEnergyLeTorusEnergy.lean).
2. **Theorem 1.1 is proved by a different route.** The preprint reduces Theorem 1.1 to Theorem 1.2 in the
   section "From square tori to the full plane", using results of Sandier and Serfaty (Theorem 1, Lemma 4.7 and
   Proposition 4.9 of [arXiv:1011.4617](https://arxiv.org/abs/1011.4617)). The formal proof instead proves a
   comparison inequality, $W^{\mathrm{neu}}(-E,1)\le W(E)/(2\pi)$ for every $E\in\mathcal A_1$ and every cutoff
   family, by a layer-cake average, a comparison of puncture and truncation, and the field form of Lemma 4.13 of
   the lectures, together with a density lemma for the charges; it then applies the lower bound for fields,
   which is proved by the route of deviation 4 for the lectures. The statement is the one described in
   deviation 1. See
   [TriangularEnergyLeWholeEnergy.lean](../SandierSerfaty/Statements/Whole/Theorems/TriangularEnergyLeWholeEnergy.lean).
3. **Corollary 1.3 is proved by a different route.** The preprint obtains it from the theorem of Bétermin
   and Sandier, which relies on further results of Sandier and Serfaty. The formal proof splits the energy
   exactly by stereographic projection, bounds it above by latitude-ring configurations, and bounds it below
   by separation of minimizers on the sphere, localization, screening (the construction of deviation 4 for the
   lectures), reflection onto square tori and Theorem 1.2. The constant $C_{\mathrm{BHS}}$ is obtained from a
   closed form of $W_\triangle$ computed in Lean by the route of the closed-form note: $W_\triangle$ is $\pi$
   times the Robin constant of the triangular torus, which an explicit row product and Jensen's formula
   express through the modular discriminant $\Delta(\rho)$; Mathlib's identity $1728\Delta=E_4^3-E_6^2$, the
   vanishing of $E_4(\rho)$ and the Weierstrass equation $\wp'^2=4\wp^3-g_3$ of the lattice reduce
   $\vert\Delta(\rho)\vert$ to $e=\wp(1/2)$, the value of $\wp$ at the real half-period; a change of variables
   in the period integral gives $3\sqrt e=\mathrm B(1/6,1/2)$, and the duplication and reflection formulas of
   the Gamma function turn this Beta value into $\Gamma(1/3)$. No Kronecker limit formula or Chowla–Selberg
   formula is used. The statement is unchanged, except that $E_{\log}(n)$ is an infimum (deviation 8). See
   [SphereLogEnergyAsymptotics.lean](../SandierSerfaty/Statements/Sphere/Theorems/SphereLogEnergyAsymptotics.lean).
4. **The interval computation is replaced by a kernel-checked certificate.** The section "The finite scalar
   verification" relies on a C++ program run with interval arithmetic (see gap 8 above). The formalization
   replaces it by a certificate, a finite family of Boolean checks proved sound in Lean and evaluated by the
   kernel (`decide +kernel`), on enclosures of the same functions: the triangular-lattice coefficients $c_m$,
   the radial tables of $f_0$ and $e$, and the constants $\lambda$, $\mu$ and $K$. Effect: the numerical step
   of Theorem 1.2 is a Lean theorem (`SandierSerfaty.CertData.certificateGoal`). Building the library
   `SandierSerfatyCert` takes 14 to 17 CPU-hours (about 2.5 hours on 16 cores).
5. **The inner continuation of $b_m$ is read for $m\ge1$.** In the section "Calibration on the triangular
   cell" the text defines $b_0=\gamma$ up to $R_0$ and then, for $m\ge1$, $b_m=V_m$ on $[p,R_0]$, with the inner
   continuation below $p$ (`cal:inner-continuation`) given by a formula that involves $c_m$, which is defined
   for $m\ge1$ only. The text is not ambiguous, and we read it as written: $b_0=\gamma$ on $(0,R_0]$ and the
   inner continuation for $m\ge1$. This is recorded as a reading of the text, not as a change. Effect: none.
6. **The puncture functional is defined in the extended reals.** The preprint defines the local energy
   $W(E,\chi_R)$ in (1.3) as a limit, and Lemma `red:local` shows that the limit exists and is finite for every
   smooth compactly supported weight $\xi$. The formal functional `punctureFunctional` is defined for every
   field and every weight, with values in $[-\infty,+\infty]$: the integral of $\xi\vert E\vert^2$ is the
   difference of the lower Lebesgue integrals of its positive and negative parts, so it has no default value.
   The local energy `localEnergy` is the limit superior as $\eta\downarrow0$. The theorem
   `tendsto_punctureFunctional` shows that for $E\in\mathcal A_1$ and every smooth compactly supported weight,
   of any sign, the functional converges to a real number, which is the scope of Lemma `red:local`. So the
   limit superior is the preprint's limit. Effect: none. See
   [TendstoPunctureFunctional.lean](../SandierSerfaty/Statements/Whole/Theorems/TendstoPunctureFunctional.lean).
7. **The torus potential is defined in classical form.** The preprint takes $h_\triangle$, and the potential
   $h$ of Theorem 1.2, to be the mean-zero periodic distributional solution of
   $-\Delta h=2\pi\bigl(\sum_i\delta_{a_i}-1\bigr)$. The formal definition `IsTorusPotential` asks instead that
   $h$ be periodic, smooth off the charges with $\Delta h=2\pi$ there, that $h+\log\vert x-a_i\vert$ have a
   finite limit at each charge, and that $h$ have mean zero over a fundamental domain. By convention $h=0$ at
   the charges, a null set. The two definitions agree. Near a charge $a_i$ the function
   $h+\log\vert x-a_i\vert-\tfrac\pi2\vert x-a_i\vert^2$ is harmonic on a punctured disk and bounded, so it
   extends smoothly across $a_i$. Hence $h$ is $-\log\vert x-a_i\vert$ plus a smooth function, and since
   $\Delta\log\vert x\vert=2\pi\delta_0$ the classical solution is a distributional one. Conversely, a
   distributional solution is smooth off the charges by Weyl's lemma and has this local form at each charge,
   as in the proof of Lemma `red:local`, so it satisfies the classical conditions. Existence and uniqueness of
   the classical solution are Lean theorems (`existsUnique_isTorusPotential`). For uniqueness, two solutions
   differ by a periodic function that is harmonic off the charges and bounded near them, hence harmonic,
   hence constant, and the constant is zero by the mean-zero condition. The potential `torusPotential` is this
   unique solution (`torusPotential_spec`). Effect: none.
8. **$E_{\log}(n)$ is an infimum.** Corollary 1.3 defines $E_{\log}(n)$ as a minimum over $(S^2)^n$. The
   formal definition `sphereLogEnergy` is the infimum, in the extended reals, of the ordered-pair logarithmic
   energy, with value $+\infty$ for a collision. The minimum is attained, since the energy is lower
   semicontinuous on the compact set $(S^2)^n$, and this is proved in the library, though it is not one of
   the stated theorems: `SandierSerfaty.Sphere.exists_isSphereMinimizer`
   ([Sphere/Minimizer.lean](../SandierSerfaty/Sphere/Minimizer.lean)) gives a minimizer for every $n$, and
   `SandierSerfaty.Sphere.Bridge.sphereLogEnergy_eq`
   ([Sphere/Bridge/LogEnergy.lean](../SandierSerfaty/Sphere/Bridge/LogEnergy.lean)) shows that the energy of
   every minimizer equals `sphereLogEnergy n`. The asymptotic expansion concerns only the value, and the
   infimum and the minimum have the same value. Effect: none on the statement.

## Bétermin–Sandier, arXiv:1404.4485v5

### Errors

None.

### Gaps

1. **§6.4, "Proof of the upper bound by compactification and conclusion": even $n$ only.** Printed: "We will
   only construct test configurations with an even number of points, again to simplify exposition", while
   Theorems 1.1 and 7.5 are stated for all $n$. The authors flag this themselves. Resolution: the odd case
   follows from the insertion bound $E(n+1)\le E(n)+(1-2\log2)\,n$, where $E(n)$ is the minimum of
   $\sum_{i\ne j}-\log\vert x_i-x_j\vert$ over $n$ points of the unit sphere: average the added energy over a
   uniformly distributed new point, using $\int\log\vert x-y\vert\,d\sigma(y)=\log2-\tfrac12$ on the sphere. The
   expansion of the claimed formula changes by $(1-2\log2)\,n+O(\log n)$ from $n$ to $n+1$, which matches. The
   formal proof of Corollary 1.3 does not use this construction. Status: confirmed.

### Misprints

1. **§7.3, page 25.** For $\tau=\tfrac12+i\tfrac{\sqrt3}{2}$, which is a root of $z^2-z+1=0$, the text says
   "$b=\sqrt3/2$, $w=6$, $\alpha=\beta=\gamma=1$ because $\tau$ is a root of unity". The coefficients of
   $\alpha z^2+\beta z+\gamma$ are $(1,-1,1)$. Correction: $\beta=-1$. Effect: none; the discriminant
   $D=\beta^2-4\alpha\gamma=-3$ and the value
   $W(\Lambda_1)=\pi\log\bigl(2\sqrt2\,\pi/(\sqrt3\,\Gamma(1/3)^3)\bigr)\approx-4.1504128$ that follows are
   unaffected. The formal route computes this value in Lean without this section (preprint deviation 3).
   Status: confirmed.
2. **§5.1, Lemma 5.1 (pp. 8–9).** The symbol $\Omega$ occurs in "$\mathbf 1_{\Omega\setminus B_\rho}$" and in
   "for any $U\subset\Omega$" and is never defined. The evident meaning is $\Omega=\mathbb R^2$, the space on
   which the lemma is stated. Effect: none. Status: confirmed.

### Unverified candidates

1. **Citations of Sandier–Serfaty, *2D Coulomb gases and the renormalized energy* (their reference [24]).** The
   text cites it as "Proposition 3.4" and "Lemma 3.7" (§5.1), "Lemma 4.4" (§6.2) and "Corollary 4.6" (§6.4). In
   arXiv:1201.3503v2 the corresponding statements appear to be numbered Proposition 3.1, Lemma 3.4,
   Proposition 4.1 and Corollary 4.2. This is probably a difference between versions of that paper and not a
   defect of this one. Not checked: that paper is not among the pinned sources. Effect: none on the formal
   development. Status: unverified.

### Deviations

None.

## Sandier–Serfaty, arXiv:1011.4617v2

### Errors

None.

### Gaps

None.

### Misprints

1. **Proof of Proposition 4.2, the definition of $j_1$.** The text writes "$j_1=-\nabla f_{ik}$", next to
   "$j_2=-\nabla^\perp u_i$". The field $j_1$ has to satisfy (4.48),
   $\mathrm{curl}\,j_1=2\pi\sum\delta_p-\sum_im_i\mathbf 1_{R_i}$, where $f_{ik}$ solves
   $-\Delta f=2\pi\delta_0-m$ (Lemma 4.16); the curl of a gradient is zero, whereas $-\nabla^\perp f_{ik}$ has
   curl $-\Delta f_{ik}$. The remark on the interfaces, that the normal derivative of $f_{ik}$ vanishes so that no
   curl is created, also makes sense only for $\nabla^\perp$. Correction: $j_1=-\nabla^\perp f_{ik}$, as for
   $j_2$ later in the same proof. Effect: none on the proof; the formal development does not use this paper. Status: confirmed.

### Unverified candidates

None.

### Deviations

None.

## Brauchart–Hardin–Saff, arXiv:1202.4037v1

This paper is used only for the statement of the conjectures that Corollary 1.3 of the preprint proves in the
case $d=2$. It was not checked for errors, and no defect is recorded. Errors, gaps, misprints, unverified
candidates and deviations: none.

## The route of the proofs, and the sources used only as references

The formal proof of Theorem 1.2 follows the sections of the preprint on finite tori, Voronoi sectors, calibration,
tails and the certificate: the Green representation of the torus potential, separation of minimizers at distance
$1/\sqrt\pi$, periodic Voronoi cells and their sector decomposition, a glued trial potential and the dual
identity, the calibration constants, the tail estimates, and the certificate. The Green function of the torus is
built from a product of Jacobi theta functions instead of Fourier series, and the angle bound at Voronoi
vertices is proved by a sector fan and an angle-packing argument, which gives the bound of at most $6n$
incidences without the Euler characteristic. The paper's splines are treated as case-wise combinations of
smooth pieces. The other results are proved from Theorem 1.2 as described above.

Outside the scope of the formal statements: the introductory discussion of the preprint, and the conjectures
of Brauchart, Hardin and Saff other than the case $d=2$ proved as Corollary 1.3. The papers of Sandier and
Serfaty ([arXiv:1011.4617](https://arxiv.org/abs/1011.4617),
[arXiv:1011.4616](https://arxiv.org/abs/1011.4616)), of Bétermin and Sandier, and of Brauchart, Hardin and Saff
([arXiv:1202.4037](https://arxiv.org/abs/1202.4037)) are not formalized and are used only as references. They
were not checked systematically: the items listed above are those found while reading the passages that the
preprint and the lectures cite.
