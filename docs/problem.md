# The problem

## The equation

We take the nonrelativistic, clamped-nucleus (Born–Oppenheimer) electronic Hamiltonian in atomic units (ħ = mₑ = e = 1, energies in hartree):

$$
H_N \;=\; \sum_{i=1}^{N}\Big(-\tfrac12\Delta_{x_i} \;-\; \sum_{k=1}^{M}\frac{Z_k}{|x_i-R_k|}\Big) \;+\; \sum_{1\le i<j\le N}\frac{1}{|x_i-x_j|}.
$$

- **Particles.** There are $N$ electrons at positions $x_i\in\mathbb R^3$, and $M$ fixed nuclei with charges $Z_k>0$ at positions $R_k$.
- **State space.** $H_N$ acts on the fermionic space $\bigwedge^N L^2(\mathbb R^3\times\{\uparrow,\downarrow\})$: square-integrable functions of $N$ space–spin coordinates that are antisymmetric under swapping any two electrons.
- **Nuclear repulsion.** The term $\sum_{k<l} Z_kZ_l/|R_k-R_l|$ is a constant. We add it only when we say so.

The **ground-state energy** is $E_0 = \inf \sigma(H_N)$. For a neutral atom or molecule this is an isolated eigenvalue below the essential spectrum.

"Solving the many-body Schrödinger equation" is not a single problem. The questions below are where rigorous progress is possible and useful. Every result in this repository states which of them it addresses.

## Questions, from foundational to applied

| # | Question | Status in the literature (short) |
|---|---|---|
| Q1 | **Well-posedness.** Is $H_N$ self-adjoint? On which domain? Is it bounded below? | Solved: Kato (1951). $H_N$ is self-adjoint on $H^2$ and bounded below. |
| Q2 | **Spectral structure.** Where is the essential spectrum? Are there bound states? How many? | HVZ theorem (Hunziker 1966; van Winter 1964; Zhislin 1960). Neutral atoms and positive ions have infinitely many bound states (Zhislin 1960). Ionization bounds, e.g. Lieb (1984): $N<2Z+1$. |
| Q3 | **Stability.** Is the energy extensive in the number of particles? | Dyson–Lenard (1967); Lieb–Thirring (1975). |
| Q4 | **Regularity and structure of eigenfunctions.** | Kato cusp conditions (1957); sharp regularity (Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Østergaard Sørensen 2005); mixed regularity (Yserentant 2004, 2010); exponential decay (Agmon 1982). |
| Q5 | **Approximation theory.** How fast do finite bases (Hylleraas, Gaussians, sparse grids) converge, with *explicit* constants? | Asymptotic rates are known in special cases (Hill 1985; Klahn–Morgan 1984; Yserentant). Fully explicit, uniform constants are largely open. |
| Q6 | **Certified computation.** Can we produce a *guaranteed* interval $[\ell,u]\ni E_0$ of prescribed width? At what cost? | Temple (1928), Kato (1949) and Lehmann-type lower bounds exist. Upper bounds are routine (variational). Rigorous *lower* bounds of chemical accuracy for anything beyond two electrons remain rare. |
| Q7 | **Complexity.** Is certified ground-energy estimation efficient for fixed $N$? Hard as $N$ grows? | Fixed-basis electronic structure is QMA-hard (O'Gorman–Irani–Whitfield–Fefferman 2022). DFT's universal functional is QMA-hard (Schuch–Verstraete 2009). Local Hamiltonian is QMA-complete (Kitaev; Kempe–Kitaev–Regev 2006). Continuum-to-certified-bits complexity at fixed $N$ is largely open. |
| Q8 | **Efficient general methods.** Coupled cluster, DMRG, QMC, and neural ansätze give accurate *numbers*. Which of them can come with a priori or a posteriori guarantees? | Mostly open. |
| Q9 | **Lattice and model reductions.** When do Hubbard-type models capture the continuum physics? | Model-level exact results: Lieb–Wu (1968), Lieb (1989). The continuum connection is mostly open. |

These map onto the repository's sectors S1–S9 (see [`sectors.md`](sectors.md)).

## Benchmark reference values (non-rigorous unless stated)

These are high-precision variational values, used for *sanity checks only*. A certificate in this repository must never assume them.

| System | Energy (Ha) | Source |
|---|---|---|
| H atom | $-1/2$ exactly | analytic |
| He (∞ nuclear mass), ground state | $-2.903\,724\,377\,034\,119\,598\ldots$ | Schwartz (2006); Nakashima–Nakatsuji (2007). These are variational upper bounds and extrapolations, not two-sided certified intervals. |
| He⁺ (ionization threshold for He) | $-2$ exactly | analytic |
| H₂ at $R = 1.4$ bohr, electronic energy (nuclear repulsion excluded) | $\approx -1.888\,761\,4$ | derived from Pachucki (2010), $E_\text{tot}\approx-1.174\,475\,714$ |

## Evidence standard

Physics and chemistry have excellent *numbers* for these systems. What is scarce is **verified** mathematics:
- theorems checked by a proof assistant, and
- energy intervals whose correctness does not depend on floating-point roundoff or unproved convergence assumptions.

This repository only gives a result the label "established" at those evidence levels. See [`../CONTRIBUTING.md`](../CONTRIBUTING.md) §1.
