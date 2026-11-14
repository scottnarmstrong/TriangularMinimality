# Supplementary notes

Four notes by Scott Armstrong and Sylvia Serfaty write out, with complete proofs, the mathematics that the
formalization uses beyond the preprint *Triangular minimality for planar Coulomb renormalized energy*. They follow the
notation of the preprint and of S. Serfaty, *Lectures on Coulomb and Riesz gases* (arXiv:2407.21194). Each note is
given as a LaTeX source and a compiled PDF with the same base name; comments in the Lean files cite them by name
(for example "screening note, Proposition 6.2") and by the numbers of the compiled PDF.

| Note | What it proves | Main theorem that uses it |
|---|---|---|
| [comparison note](comparison.pdf) | the comparison inequality between the renormalized energy of a field and its jellium energy, `W^neu(-E,1) <= W(E)/(2 pi)` for every admissible field and every cutoff family, and the deduction of Theorem 1.1 from it | Theorem 1.1, `SandierSerfaty.triangularEnergy_le_wholeEnergy` |
| [closed-form note](closed-form.pdf) | the closed form `W_tri = pi log(2 sqrt(2) pi / (sqrt(3) Gamma(1/3)^3))` of the energy of the triangular lattice, through the Weierstrass period of the equianharmonic lattice | Corollary 1.3, `SandierSerfaty.sphereLogEnergy_asymptotics` (the constant) |
| [screening note](screening.pdf) | the lower bound `W_tri/(2 pi) <= W^neu(E)` for the jellium energy of every field, by an explicit screening and a projection onto square tori, with the identification of Definition 11.4 of the Lectures with the neutral energy and the lower bound for configurations | Chapter 11 of the Lectures, `SandierSerfaty.div_two_pi_triangularEnergy_le_neutralEnergy` (used by Theorem 1.1) |
| [sphere note](sphere.pdf) | the route to the asymptotics of the logarithmic energy of `n` points on the sphere: exact splitting in stereographic charts, separation of minimizers, an upper bound by latitude rings, a lower bound by localization, screening and reflection onto square tori | Corollary 1.3, `SandierSerfaty.sphereLogEnergy_asymptotics` |

To rebuild a note, run `latexmk -pdf` on its source (two passes of `pdflatex` suffice); the notes need only the
standard packages `amsmath`, `amssymb`, `amsthm`, `mathtools`, `enumitem`, `geometry`, `url` and `hyperref`, and the closed-form
note also uses `booktabs`, `hyphenat` and `mathrsfs`.
