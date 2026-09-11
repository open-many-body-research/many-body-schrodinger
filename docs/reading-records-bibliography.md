> Compiled during the pre-publication audit of the v1.0 foundation from the reading records in [`archive/v1.0-research-notes/`](../archive/v1.0-research-notes/): **R/** = `research/`, **H/** = `helium_research/`, **N/** = `nogo/`. Two retrieval-log files it mentions (`kb_retrieval.md`, `retrieval_addendum.md`) are not in the archive.

# Bibliography of cited reference literature (raw, verified)

Built 2026-09-11 from the reading records, read-only:
`research/{analytic,certification,classical,complexity,neural,quantum_dft}.md`,
`helium_research/{approximation,helium_method,hp_successors,kb_retrieval,lower_bounds,regularity,retrieval_addendum,theorem_skeleton}.md`,
`nogo/{hardness_status,physical_scales,tractable_target}.md`.

File abbreviations: **R/** = `research/`, **H/** = `helium_research/`, **N/** = `nogo/`.

These files cite no external literature: `H/helium_method.md` (it says no literature search was used), `H/theorem_skeleton.md` (internal cross-references only), and all three `N/` files (`N/physical_scales.md` points to `R/analytic.md` for the Kato-Rellich/HVZ references; the other two say no literature search was done).

Some results are named but never cited as a specific work, so they have no row below: HVZ, Zhislin, Hardy's inequality, Kato–Rellich, Lehmann/Maehly/Goerisch, the Pollak–Martinazzo procedure, Miller's intermediate operator, the Georgescu–Vasy compactification, "earlier sparse-grid theory", and Machin's identity.

## Verification method

* **arXiv:** one batch query to the arXiv API (`export.arxiv.org/api/query?id_list=…`) covering all 57 cited arXiv ids. All 57 resolved. I compared authors, title, submission and version dates, and journal-ref/DOI with each record's claims.
* **DOIs:** 65 cited DOIs checked through `api.crossref.org/works/<doi>`. 64 resolved and matched. The remaining one, a ResearchGate DOI, is registered with DataCite instead of Crossref. `api.datacite.org` resolved it and it matches.
* **Other URLs:** the NIST PDF, the KIT catalog entry, the Edinburgh, DNB, KIT and QCRI PDFs, and the ResearchGate landing page were checked with HTTP requests. All returned 200 except ResearchGate, which returned 403 (it blocks bots; the DataCite record confirms the DOI).
* **Verification column:**
  * **VERIFIED:** the id resolves and matches the stated authors, title and topic.
  * **CLASSIC:** a standard foundational work whose details match standard knowledge. Every CLASSIC entry was also confirmed through Crossref or arXiv.
  * **MISMATCH / NOT FOUND:** none occurred.
* **Access column:** what the reading record says was actually read.
  * **FULL:** full text read, or the named sections were read.
  * **PARTIAL:** only some sections read.
  * **ABSTRACT/META:** abstract or metadata only.
  * **ACCESS FAILURE:** the record reports it could not get the full text.

---

## 1. Operator theory, ionization, and wavefunction regularity

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 1 | T. Kato | Fundamental properties of Hamiltonian operators of Schrödinger type | 1951 | Trans. AMS 70, 195–211 | 10.1090/S0002-9947-1951-0041010-X (also 10.2307/1990366) | R/analytic (indirectly N/physical_scales) | ABSTRACT/META; ACCESS FAILURE (PDF HTTP 403) | CLASSIC (both DOIs confirmed in Crossref) |
| 2 | T. Kato | On the existence of solutions of the helium wave equation | 1951 | Trans. AMS 70, 212–218 | 10.1090/S0002-9947-1951-0041011-1 | H/lower_bounds | ACCESS FAILURE (AMS 403); bibliographic details only | CLASSIC (Crossref) |
| 3 | E. H. Lieb | Bound on the maximum negative ionization of atoms and molecules | 1984 | Phys. Rev. A 29, 3018–3028 | 10.1103/PhysRevA.29.3018 | R/analytic | Not read directly; content checked through Nam | CLASSIC (Crossref) |
| 4 | P. T. Nam | New bounds on the maximum ionization of atoms | 2010 preprint (CMP 312, 427–445, 2012) | arXiv; journal version not cited in the record | arXiv:1009.2367 (journal DOI 10.1007/s00220-012-1479-y, found via Crossref, not in record) | R/analytic | FULL (pp. 1–2, 4, §2.1) | VERIFIED |
| 5 | I. Anapolitanos, M. Olivieri, S. Zalczer | On boundedness of isomerization paths for non- and semirelativistic molecules | 2022/2023 (J. 2025) | J. Funct. Anal. 288, 110713 | arXiv:2212.11938v2; 10.1016/j.jfa.2024.110713 | R/analytic | FULL (arXiv v2, pp. 5–7); journal DOI text failed to load | VERIFIED (arXiv and Crossref) |
| 6 | Y. Goto | The maximal negative ion of molecules in Schrödinger, Hartree–Fock, and Müller theories (withdrawn) | 2021 | arXiv | arXiv:2107.01826 | R/analytic | Record opened; excluded as withdrawn | VERIFIED (v2 comment reads "The proof is incorrect", as the record says) |
| 7 | S. Fournais, M. Hoffmann-Ostenhof, T. Hoffmann-Ostenhof, T. Ø. Sørensen | Sharp regularity results for Coulombic many-electron wave functions | 2003 / 2005 | Commun. Math. Phys. 255, 183–227 | arXiv:math-ph/0312060v1; 10.1007/s00220-004-1257-6 | H/regularity | FULL (pp. 1–8; auxiliary calculations not re-done) | VERIFIED |
| 8 | S. Fournais, M. & T. Hoffmann-Ostenhof, T. Ø. Sørensen | Analytic structure of many-body Coulombic wave functions | 2008 / 2009 | Commun. Math. Phys. 289, 291–310 | arXiv:0806.1004v1; 10.1007/s00220-008-0664-5 | H/regularity | FULL (pp. 1–4, parts of §2) | VERIFIED |
| 9 | S. Fournais, T. Ø. Sørensen | Pointwise estimates on derivatives of Coulombic wave functions and their electron densities | 2018 | arXiv (record: "no journal DOI verified") | arXiv:1803.03495v1 | H/regularity | FULL (pp. 1–7, §§2–4) | VERIFIED. Note: published as "Estimates on derivatives of Coulombic wave functions and their electron densities", J. reine angew. Math. (Crelle) 2021, DOI 10.1515/crelle-2020-0047 (found via Crossref search, not in record) |
| 10 | P. Ming, H. Yu | Sharp Barron regularity results for Coulombic many-electron wave functions | 2026 (23 Aug) | arXiv preprint | arXiv:2608.22252v1 | H/regularity, H/hp_successors | FULL (§§1, 4–7; Fourier residues not re-checked) | VERIFIED |
| 11 | J. D. Morgan III | Convergence properties of Fock's expansion for S-state eigenfunctions of the helium atom | 1986 | Theor. Chim. Acta 69, 181–223 | 10.1007/BF00526420 | H/regularity | ABSTRACT/META; ACCESS FAILURE (subscription) | VERIFIED |
| 12 | B. Ammann, J. Mougel, V. Nistor | A regularity result for the bound states of N-body Schrödinger operators: blow-ups and Lie manifolds | 2020 / 2023 | Lett. Math. Phys. 113:26 | arXiv:2012.13902v3; 10.1007/s11005-023-01648-0 | H/hp_successors | FULL (§§1.1–1.2, Thms 4.22, 6.1, 6.6, App. A) | VERIFIED |
| 13 | B. Ammann, C. Carvalho, V. Nistor | Regularity for eigenfunctions of Schrödinger operators | 2010 / 2012 | Lett. Math. Phys. 101, 49–84 | arXiv:1010.1712v3; 10.1007/s11005-012-0551-z | H/hp_successors | FULL (intro, Thms 4.2–4.6) | VERIFIED |
| 14 | H. Yserentant | The mixed regularity of electronic wave functions multiplied by explicit correlation factors | 2011 | ESAIM:M2AN 45, 803–824 | 10.1051/m2an/2010103 | H/hp_successors | FULL (NUMDAM PDF; §§1–4, 6–7, 9–10) | VERIFIED |
| 15 | H. Yserentant | The regularity of electronic wave functions in Barron spaces | 2025 / 2026 | ESAIM:M2AN 60, 689–699 | arXiv:2502.17950v3; 10.1051/m2an/2026015 | H/hp_successors | FULL (§§1, 3–4) | VERIFIED (arXiv v3 dated 2026-03-18, as the record says) |
| 16 | H.-J. Flad, G. Flad-Harutyunyan, B.-W. Schulze | Explicit Green operators for quantum mechanical Hamiltonians. II. Edge type singularities of the helium atom | 2018 | arXiv (journal version not cited in the record) | arXiv:1801.07552 | H/hp_successors | PARTIAL (§§1.1–1.2, 2.1, 3.1; appendix not re-computed) | VERIFIED. Note: journal version Asian-Eur. J. Math. (2019/20), DOI 10.1142/S1793557120501223 (found via Crossref, not in record) |
| 17 | H.-J. Flad, R. Schneider, B.-W. Schulze | Asymptotic regularity of solutions to Hartree–Fock equations with Coulomb potential | 2008 | Math. Methods Appl. Sci. 31, 2172–2201 | 10.1002/mma.1021 | H/approximation | FULL (author preprint 2007-05-23; Def. 1, Thms 1–2, §§2.2–2.3) | VERIFIED (third author confirmed as Schulze) |

## 2. Temple inequality and eigenvalue lower bounds

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 18 | G. Temple | The theory of Rayleigh's principle as applied to continuous systems | 1928 | Proc. R. Soc. Lond. A 119, 276–293 | 10.1098/rspa.1928.0098 | H/lower_bounds | FULL (scan from a mirror; §§1, 5, 7–8, p. 292) | CLASSIC (Crossref) |
| 19 | D. H. Weinstein | Modified Ritz method | 1934 | PNAS 20, 529–532 | 10.1073/pnas.20.9.529 | H/lower_bounds | FULL (all 4 scan pages through PMC PMC1076472) | CLASSIC (Crossref) |
| 20 | T. Kato | On the upper and lower bounds of eigenvalues | 1949 | J. Phys. Soc. Jpn. 4, 334–339 | 10.1143/JPSJ.4.334 | H/lower_bounds | ACCESS FAILURE (J-STAGE required authentication); metadata only | CLASSIC (Crossref) |
| 21 | T. Kato | Upper and lower bounds of eigenvalues | 1950 | Phys. Rev. 77, 413 | 10.1103/PhysRev.77.413 | H/lower_bounds | ACCESS FAILURE; metadata only | CLASSIC (Crossref) |
| 22 | E. M. Harrell II | Generalizations of Temple's inequality | 1978 | Proc. AMS 69, 271–276 | 10.2307/2042610 | H/lower_bounds | FULL (author-uploaded ResearchGate copy; Thms 1–2, Lemma 4) | VERIFIED |
| 23 | L. Boulton, A. Hobiny | On the quality of complementary bounds for eigenvalues | 2013 / 2014 (v2) | arXiv | arXiv:1311.5181v2 | H/lower_bounds | FULL | VERIFIED (v2 dated 2014-08-11, as the record says) |
| 24 | N. W. Bazley | Lower bounds for eigenvalues with application to the helium atom | 1959 | PNAS 45, 850–853 | 10.1073/pnas.45.6.850 | H/lower_bounds | ABSTRACT/META; full text not retrieved | VERIFIED |
| 25 | N. W. Bazley | Lower bounds for eigenvalues with application to the helium atom | 1960 | Phys. Rev. 120, 144–149 | 10.1103/PhysRev.120.144 | H/lower_bounds | ABSTRACT/META; full text not retrieved | VERIFIED |
| 26 | N. W. Bazley, D. W. Fox | Truncations in the method of intermediate problems for lower bounds to eigenvalues | 1961 | J. Res. NBS 65B, 105–111 | Record gives only the NIST PDF URL (it says the DOI was not verified). Crossref DOI: 10.6028/jres.065B.009 | H/lower_bounds | FULL (NIST PDF) | VERIFIED (URL returns a PDF; Crossref title-search match; DOI not in record) |
| 27 | M. Ireland, P. Jeszenszki, E. Mátyus, R. Martinazzo, M. Ronto, E. Pollak | Lower bounds for nonrelativistic atomic energies | 2021 (online) / 2022 | ACS Phys. Chem. Au 2, 23–37 | 10.1021/acsphyschemau.1c00018 | H/lower_bounds | FULL (Europe PMC XML, PMC8796283) | VERIFIED |
| 28 | M. Ronto, P. Jeszenszki, E. Mátyus, E. Pollak | Lower bounds on par with upper bounds for few-electron atomic energies | 2023 | Phys. Rev. A 107, 012204 | arXiv:2301.02827; 10.1103/PhysRevA.107.012204 | H/lower_bounds | FULL (10-page PDF) | VERIFIED |

## 3. Hylleraas expansions and helium numerics

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 29 | B. Klahn, W. A. Bingel | The convergence of the Rayleigh–Ritz method in quantum chemistry. I. The criteria of convergence | 1977 | Theor. Chim. Acta 44, 9–26 | 10.1007/BF00548026 | H/approximation, H/kb_retrieval, H/retrieval_addendum | ABSTRACT/META; ACCESS FAILURE (subscription) | VERIFIED |
| 30 | B. Klahn, W. A. Bingel | … II. Investigation of the convergence for special systems of Slater, Gauss and two-electron functions | 1977 | Theor. Chim. Acta 44, 27–43 | 10.1007/BF00548027 | H/approximation, H/kb_retrieval, H/retrieval_addendum | ABSTRACT/META; ACCESS FAILURE; exact hypotheses of Theorem 10 not verified | VERIFIED |
| 31 | B. Klahn | Die Konvergenz des Ritz'schen Variationsverfahrens in der Quantenchemie (Göttingen dissertation, 190 pp.) | 1975 | Thesis; KIT Library catalog 538066 | none (catalog URL) | H/kb_retrieval, H/retrieval_addendum | Catalog record only; no digital copy | VERIFIED (catalog page resolves and shows this title and author) |
| 32 | R. N. Hill | Rates of convergence and error estimation formulas for the Rayleigh–Ritz variational method | 1985 | J. Chem. Phys. 83, 1173–1196 | 10.1063/1.449481 | H/approximation, H/retrieval_addendum | ABSTRACT/META plus public reference notes; ACCESS FAILURE (PDF 403) | VERIFIED |
| 33 | R. N. Hill | Dependence of the rate of convergence of the Rayleigh–Ritz method on a nonlinear parameter | 1995 | Phys. Rev. A 51, 4433–4471 | 10.1103/PhysRevA.51.4433 | H/approximation, H/retrieval_addendum | ABSTRACT/META; ACCESS FAILURE | VERIFIED (record gives no title; Crossref title fits its "nonlinear scale parameter" description) |
| 34 | A. D. Goddard | Rate of convergence of the configuration interaction model for the helium ground state | 2009 | SIAM J. Math. Anal. 41, 77–116 | 10.1137/080727956 | H/approximation, H/retrieval_addendum | FULL (Edinburgh repository PDF; pp. 78–83, Thm 3.1, Lemma 4.1, §5.2) | VERIFIED |
| 35 | C. Schwartz | Further computations of the He atom ground state | 2006 | arXiv | arXiv:math-ph/0605018 | H/approximation | FULL | VERIFIED |
| 36 | H. Nakashima, H. Nakatsuji | How accurately does the free complement wave function of a helium atom satisfy the Schrödinger equation? | 2008 | Phys. Rev. Lett. 101, 240406 | 10.1103/PhysRevLett.101.240406 | H/lower_bounds | FULL (author PDF from qcri.or.jp) | VERIFIED |
| 37 | M. D. Mohammadi | Explicit convergence bounds for correlated Hylleraas basis sets | 2026 | ResearchGate preprint (the record rejects its claims) | 10.13140/RG.2.2.24365.35044 | H/approximation | FULL (author-uploaded text, §§4–7) | VERIFIED (DataCite DOI; Crossref returns 404 because the DOI is DataCite-registered) |

## 4. H₂ and H₂⁺ numerics and certified one-electron bounds

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 38 | P. J. Jennings | Lower bounds for some potential-energy curves of H₂ and He₂⁺⁺ | 1967 | J. Chem. Phys. 46, 2442–2443 | 10.1063/1.1841057 | H/lower_bounds | FULL (Murdoch University copy) | VERIFIED |
| 39 | X. Liu | Explicit two-sided eigenvalue bounds for Schrödinger operators with singular potentials via finite element method | 2026 (6 May) | arXiv preprint | arXiv:2605.05177v1 | H/lower_bounds | FULL (HTML) | VERIFIED |
| 40 | X. Liu | From estimate to proof: certified ground-state energy bounds for singular Schrödinger operators | 2026 (26 Aug) | arXiv preprint | arXiv:2608.25760v1 | R/certification, H/lower_bounds | FULL (HTML plus the relevant SI proofs; interval computation not reproduced) | VERIFIED |

## 5. hp / approximation theory, quadrature, and Gaussian approximation

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 41 | H.-J. Flad, W. Hackbusch, R. Schneider | Best N-term approximation in electronic structure calculations. I. One-electron reduced density matrix | 2006 | ESAIM:M2AN 40, 49–61 | 10.1051/m2an:2006007 | H/approximation | FULL | VERIFIED |
| 42 | H.-J. Flad, W. Hackbusch, R. Schneider | Best N-term approximation in electronic structure calculations. II. Jastrow factors | 2007 | ESAIM:M2AN 41, 261–279 | 10.1051/m2an:2007016 | H/approximation | FULL | VERIFIED |
| 43 | H.-J. Flad, R. Schneider | s*-compressibility of the discrete Hartree–Fock equation | 2012 | ESAIM:M2AN 46, 1055–1080 | 10.1051/m2an/2011077 | H/approximation | FULL | VERIFIED |
| 44 | M. Feischl, C. Schwab | Exponential convergence in H¹ of hp-FEM for Gevrey regularity with isotropic singularities | 2019 (online) / 2020 | Numer. Math. 144, 323–346 | 10.1007/s00211-019-01085-z | H/approximation | FULL (2018 CRC 1173 preprint) | VERIFIED |
| 45 | Y. Maday, C. Marcati | Analyticity and hp discontinuous Galerkin approximation of nonlinear Schrödinger eigenproblems | 2019 / 2022 (v2) / J. 2023 | Math. Models Methods Appl. Sci. 33, 2657–2701 | arXiv:1912.07483v2; 10.1142/S0218202523500586 | H/approximation, H/hp_successors (archive mention) | FULL (arXiv); journal landing page inaccessible | VERIFIED (the journal DOI, which the record took from secondary metadata, is correct) |
| 46 | A. Chernov, T. von Petersdorff, C. Schwab | Exponential convergence of hp quadrature for integral operators with Gevrey kernels | 2010 (online) / 2011 | ESAIM:M2AN 45, 387–422 | 10.1051/m2an/2010061 | H/approximation | FULL | VERIFIED |
| 47 | S. Scholz, H. Yserentant | On the approximation of electronic wavefunctions by anisotropic Gauss and Gauss–Hermite functions | 2016 / 2017 | Numer. Math. 136, 841–874 | arXiv:1612.00360; 10.1007/s00211-016-0856-4 | H/hp_successors | FULL (§§1–4, 6–9) | VERIFIED (the record gives no volume or year; Crossref supplies them) |
| 48 | M. Bachmayr, H. Chen, R. Schneider | Error estimates for Hermite and even-tempered Gaussian approximations in quantum chemistry | 2014 | Numer. Math. 128, 137–165 | 10.1007/s00211-014-0605-5 | H/hp_successors | FULL (DNB preprint, "Numerical analysis of Gaussian approximations in quantum chemistry") | VERIFIED |

## 6. Quantum chemistry methods (FCI, FCIQMC, CC, DMRG)

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 49 | Y. Zhang, Z. Wang, J. Lu, Y. Li | CDFCI: High-performance parallel software for many-body large-scale eigenvalue problems | 2026 (6 May) | arXiv | arXiv:2605.04483v1 | R/classical | PARTIAL (§§1–3) | VERIFIED |
| 50 | M. Safari, R. J. Anderson, A. Alavi, G. Li Manni | FCIQMC-CASPT2 with imaginary-time-averaged wave functions | 2024 / 2025 | J. Chem. Theory Comput. 21, 1029–1038 | 10.1021/acs.jctc.4c01462; ChemRxiv 10.26434/chemrxiv-2024-kj11f | R/classical | FULL (ChemRxiv manuscript) | VERIFIED (both DOIs) |
| 51 | L. Fu, H. Shang, J. Yang, C. Guo | Clifford augmented density matrix renormalization group for ab initio quantum chemistry | 2025 | arXiv | arXiv:2506.16026v1 | R/classical | PARTIAL (§§II–III) | VERIFIED (v2 posted 2025-11-13 after the record read v1) |
| 52 | K. Szenes, N. Glaser, M. Erakovic, V. Barandun et al. | QCMaquis 4.0: multipurpose electronic, vibrational, and vibronic structure and dynamics calculations with the DMRG | 2025 | J. Phys. Chem. A 129, 7549–7574 | arXiv:2505.01405; 10.1021/acs.jpca.5c02970 | R/classical | ABSTRACT/META | VERIFIED |
| 53 | K. E. Weflen, M. R. Bentley, J. H. Thorpe, P. R. Franke et al. | Exploiting a shortcoming of coupled-cluster theory: the extent of non-Hermiticity as a diagnostic indicator of computational accuracy | 2025 | arXiv (published in J. Phys. Chem. Lett., not noted in record) | arXiv:2503.20006v1 | R/classical | PARTIAL (derivation and numerical discussion) | VERIFIED. Note: J. Phys. Chem. Lett. 16, 5121–5127 (2025), DOI 10.1021/acs.jpclett.5c00885 (from arXiv journal-ref, not in record) |
| 54 | M. Hassan, Y. Maday | Analysis of the single reference coupled cluster method…: the discrete coupled cluster equations | 2023 / v3 2025 | arXiv | arXiv:2311.00637v3 | R/classical | PARTIAL (§2, §4.2, Thm 35) | VERIFIED (v3 dated 2025-12-02, as the record says) |
| 55 | J. Beck, B. Stamm | On the regularity and interpolation of coupled cluster amplitudes in canonical orbital basis | 2026 (21 May) | arXiv | arXiv:2605.22584v1 | R/classical | PARTIAL (§3, Thm 3.8) | VERIFIED (v2 posted 2026-07-01, so the Thm 3.2 issue flagged in the record may be fixed there; not checked) |
| 56 | S. Upadhyay, A. Shayit, T. Zhang, S. H. Yuwono et al. | Definitive assessment of the accuracy, variationality, and convergence of relativistic CC and DMRG in 100-orbital space | 2026 (2 Apr) | arXiv | arXiv:2604.02144v1 | R/classical | PARTIAL (§2) | VERIFIED |
| 57 | J. Lu, Z. Wang | The full configuration interaction quantum Monte Carlo method through the lens of inexact power iteration | 2017 / 2020 | SIAM J. Sci. Comput. 42, B1–B29 | arXiv:1711.09153; 10.1137/18M1166626 | R/classical | FULL (assumptions, Thms 1–2) | VERIFIED |
| 58 | M. Hassan, Y. Maday, Y. Wang | Analysis of the single reference coupled cluster method…: the full-coupled cluster equations | 2023 | Numer. Math. 155, 121–173 | 10.1007/s00211-023-01371-x | R/classical | FULL (journal text checked) | VERIFIED |

## 7. Neural-network wavefunctions

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 59 | D. Pfau, J. S. Spencer, A. G. de G. Matthews, W. M. C. Foulkes | Ab initio solution of the many-electron Schrödinger equation with deep neural networks (FermiNet) | 2020 | Phys. Rev. Research 2, 033429 | arXiv:1909.02487; 10.1103/PhysRevResearch.2.033429 | R/neural | ABSTRACT/META | VERIFIED |
| 60 | J. Hermann, Z. Schätzle, F. Noé | Deep-neural-network solution of the electronic Schrödinger equation (PauliNet) | 2020 | Nature Chem. 12, 891–897 | arXiv:1909.08423; 10.1038/s41557-020-0544-y | R/neural | ABSTRACT/META | VERIFIED (arXiv comment about new results in the journal version, as the record says) |
| 61 | I. von Glehn, J. S. Spencer, D. Pfau | A self-attention ansatz for ab-initio quantum chemistry (Psiformer) | 2022 / ICLR 2023 | ICLR 2023 | arXiv:2211.13672 | R/neural | ABSTRACT/META | VERIFIED |
| 62 | R. Li, H. Ye, D. Jiang, X. Wen, C. Wang et al. | A computational framework for neural network-based VMC with Forward Laplacian (LapNet) | 2024 | Nature Mach. Intell. 6, 209–219 | 10.1038/s42256-024-00794-x | R/neural | ABSTRACT/META; ACCESS FAILURE (journal full text) | VERIFIED |
| 63 | Z. Li, Z. Lu, R. Li, X. Wen et al. | Spin-symmetry-enforced solution of the many-body Schrödinger equation with a deep neural network | 2024 | Nature Comput. Sci. 4, 910–919 | arXiv:2406.01222; 10.1038/s43588-024-00730-4 | R/neural | ABSTRACT/META | VERIFIED |
| 64 | M. Scherbela, N. Gao, P. Grohs, S. Günnemann | Accurate ab-initio neural-network solutions to large-scale electronic structure problems (FiRE) | 2025 (8 Apr) | arXiv | arXiv:2504.06087v1 | R/neural | PARTIAL (intro, App. J–L) | VERIFIED |
| 65 | A. Foster, Z. Schätzle, P. B. Szabó, L. Cheng et al. | An ab initio foundation model of wavefunctions that accurately describes chemical bond breaking (Orbformer) | 2025 (24 Jun) | arXiv | arXiv:2506.19960v1 | R/neural | PARTIAL (intro, App. C.1) | VERIFIED |
| 66 | L. Gerard, M. Scherbela, H. Sutterud, W. M. C. Foulkes, P. Grohs | Transferable neural wavefunctions for solids | 2025 | Nature Comput. Sci. 5, 1147–1157 | 10.1038/s43588-025-00872-z | R/neural | FULL (journal) | VERIFIED |
| 67 | L. Fu | Fermi Sets: universal and interpretable neural architectures for fermions | 2026 (v2 19 Apr) | arXiv | arXiv:2601.02508v2 | R/neural | FULL (eqs. 1–12) | VERIFIED |
| 68 | Z. Che | A deterministic framework for neural network quantum states in quantum chemistry | 2026 | J. Chem. Theory Comput. 22, 6497–6509 | arXiv:2601.21310v2; 10.1021/acs.jctc.6c00445 | R/neural | PARTIAL (§§2.1–2.4) | VERIFIED |
| 69 | T. Zaklama, M. Geier, L. Fu | Large Electron Model: a universal ground state predictor | 2026 (2 Mar) | arXiv | arXiv:2603.02346v1 | R/neural | PARTIAL (abstract, intro, scope) | VERIFIED (v2 since 2026-06-01) |
| 70 | Y.-S. Li, S. Poldmaa, T. Ong, A. Abouelkomsan et al. | Scaling universal Fermi network toward ground states: a diffusion-Monte-Carlo assessment | 2026 (28 Jul) | arXiv | arXiv:2607.25872v1 | R/neural | PARTIAL (§§I–II.2, eqs. 7–8) | VERIFIED (the record gives no title; the arXiv title matches "Fermi Sets + fixed-phase DMC") |
| 71 | L. Zhang, G. Duan, D. Luo | WF-Bench: a benchmark for neural network wavefunction expressivity and scaling laws | 2026 | arXiv; ICML 2026 | arXiv:2605.29683 | R/neural | Located only; not load-bearing | VERIFIED |
| 72 | N. Renaud | QMCTorch: molecular wavefunctions with neural components for energy and force calculations | 2025 | arXiv | arXiv:2506.09743 | R/neural | Located only; not load-bearing | VERIFIED |
| 73 | D. D. Dai, M. Soljačić | Essentially no energy barrier between independent fermionic neural quantum state minima | 2026 (11 Jan) | arXiv | arXiv:2601.06939 | R/neural (as "mode connectivity") | Located only; not load-bearing | VERIFIED (the topic matches "mode connectivity"; the six-electron quantum-dot detail was not checked) |

## 8. Quantum algorithms, QPE, and state preparation

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 74 | A. Dutkiewicz, A. F. White, G. H. Low, A. E. DePrince et al. | Spectral amplification for ground-state energy estimation of electronic structure in first quantization | 2026 (16 Jul) | arXiv | arXiv:2607.15358v1 | R/quantum_dft | FULL (§§II–IV, eqs. 1–22) | VERIFIED |
| 75 | T. N. Georges, M. Bothe, C. Sünderhauf, B. K. Berntson et al. | Quantum simulations of chemistry in first quantization with any basis set | 2024 / 2025 | npj Quantum Inf. 11, 55 | arXiv:2408.03145; 10.1038/s41534-025-00987-1 | R/quantum_dft | FULL (incl. eq. II.41) | VERIFIED |
| 76 | S. Fomichev, K. Hejazi, M. S. Zini, M. Kiser et al. | Initial state preparation for quantum chemistry on quantum computers | 2023 / 2024 | PRX Quantum 5, 040339 | arXiv:2310.18410v2; 10.1103/PRXQuantum.5.040339 | R/quantum_dft | FULL (published PDF, §III A, eq. 17) | VERIFIED |
| 77 | V. Khinevich, W. Mizukami | Symmetry-adapted state preparation for quantum chemistry on fault-tolerant quantum computers | 2026 (13 Jan) | arXiv | arXiv:2601.08533v1 | R/quantum_dft | FULL (incl. §IV.7) | VERIFIED |
| 78 | N. S. Mande, R. de Wolf | Tight bounds for quantum phase estimation and related problems | 2023 / 2026 | Quantum 10, 2140 | arXiv:2305.04908v3; 10.22331/q-2026-06-15-2140 | R/quantum_dft | FULL (Thm 1.3) | VERIFIED |
| 79 | G. H. Low, I. L. Chuang | Hamiltonian simulation by qubitization | 2016 / 2019 | Quantum 3, 163 | arXiv:1610.06546v3; 10.22331/q-2019-07-12-163 | R/quantum_dft | ABSTRACT/META (abstract bound) | CLASSIC (confirmed) |
| 80 | P. Schleich, L. B. Kristensen, J. A. Campos-Gonzalez-Angulo, D. Avagliano et al. | Chemically motivated simulation problems are efficiently solvable by a quantum computer | 2024 / 2026 | Digital Discovery 5, 64–87 | arXiv:2401.09268; 10.1039/D5DD00377F | R/complexity | ABSTRACT/META (abstract-level scope claim) | VERIFIED |
| 81 | M. Erakovic, F. Witteveen, D. Harley, J. Günther et al. | High ground state overlap via quantum embedding methods | 2024 / 2025 | PRX Life 3, 013003 | arXiv:2408.01940; 10.1103/PRXLife.3.013003 | R/complexity | FULL (journal paper) | VERIFIED (venue "PRX Life" confirmed) |

## 9. Density functional theory

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 82 | P. Hohenberg, W. Kohn | Inhomogeneous electron gas | 1964 | Phys. Rev. 136, B864–B871 | 10.1103/PhysRev.136.B864 | R/quantum_dft | ABSTRACT/META | CLASSIC (Crossref) |
| 83 | M. Levy | Universal variational functionals of electron densities, first-order density matrices, and natural spin-orbitals and solution of the v-representability problem | 1979 | PNAS 76, 6062–6065 | 10.1073/pnas.76.12.6062 | R/quantum_dft | Read through PMC (no scope stated) | CLASSIC (Crossref) |
| 84 | E. H. Lieb | Density functionals for Coulomb systems | 1983 | Int. J. Quantum Chem. 24, 243–277 | 10.1002/qua.560240302 | R/quantum_dft | ABSTRACT/META; full text not obtained | CLASSIC (Crossref) |
| 85 | T. Carvalho Corso | A rigorous formulation of density functional theory for spinless fermions in one dimension | 2026 | Lett. Math. Phys. 116, 27 | 10.1007/s11005-026-02051-1 | R/quantum_dft | FULL (Thm 2.3 and others) | VERIFIED |
| 86 | V. H. Bakkestuen, M. F. Herbst, V. Falmår, M. Penz, A. Laestadius | Moreau–Yosida-based Kohn–Sham inversion for periodic systems | 2026 (17 Jun) | arXiv | arXiv:2606.19471v1 | R/quantum_dft | FULL (incl. Fig. 5) | VERIFIED |
| 87 | N. Sheng | Exact density-functional theory as parallel ensemble variational hierarchies: from Lieb's formulation to Kohn–Sham theory | 2026 (24 Mar) | arXiv | arXiv:2603.23399v1 | R/quantum_dft | PARTIAL (§I) | VERIFIED (v5 dated 2026-07-23 is now current) |

## 10. Complexity, QMA, and N-representability

| # | Author(s) | Title | Year | Venue | DOI / arXiv | Cited in | Access (per record) | Verification |
|---|---|---|---|---|---|---|---|---|
| 88 | J. Kempe, A. Kitaev, O. Regev | The complexity of the local Hamiltonian problem | 2004 / 2006 | SIAM J. Comput. 35, 1070–1097 | arXiv:quant-ph/0406180; 10.1137/S0097539704445226 | R/complexity | Read as a primary source (scope unstated) | CLASSIC (confirmed) |
| 89 | B. O'Gorman, S. Irani, J. Whitfield, B. Fefferman | Intractability of electronic structure in a fixed basis | 2021 / 2022 | PRX Quantum 3, 020322 | arXiv:2103.08215; 10.1103/PRXQuantum.3.020322 | R/complexity | FULL (journal PDF pp. 3–7, App. D, §V) | VERIFIED (arXiv v1 title is "Electronic Structure in a Fixed Basis is QMA-complete") |
| 90 | N. Schuch, F. Verstraete | Computational complexity of interacting electrons and fundamental limitations of density functional theory | 2007 / 2009 | Nature Phys. 5, 732–735 | arXiv:0712.0483; 10.1038/nphys1370 | R/complexity | FULL (preprint incl. supplement) | CLASSIC (confirmed) |
| 91 | Y.-K. Liu, M. Christandl, F. Verstraete | Quantum computational complexity of the N-representability problem: QMA complete | 2006 / 2007 | Phys. Rev. Lett. 98, 110503 | arXiv:quant-ph/0609125; 10.1103/PhysRevLett.98.110503 | R/complexity | FULL (preprint pp. 2–4) | CLASSIC (confirmed) |
| 92 | J. Liebert, F. Castillo, J.-P. Labbé, T. Maciazek, C. Schilling | Solving one-body ensemble N-representability problems with spin | 2024 / 2025 | Quantum 9, 1921 | arXiv:2412.01805v2; 10.22331/q-2025-12-02-1921 | R/complexity | FULL | VERIFIED |
| 93 | M. Stroeks, B. M. Terhal, Y. Herasymenko | Optimizing fermionic Hamiltonians with classical interactions | 2025 / v2 2026 | arXiv | arXiv:2510.02122v2 | R/complexity | FULL (Problems 2.1/2.6, Thms 2.2–2.7) | VERIFIED (v2 dated 2026-02-23, as the record says) |
| 94 | G. E. Massaccesi, O. B. Oña, P. Capuzzi, J. I. Melo et al. | Determining the N-representability of a reduced density matrix via unitary evolution and stochastic sampling | 2024 (J.) / 2025 (arXiv) | J. Chem. Theory Comput. 20, 9968–9976 | arXiv:2503.17303; 10.1021/acs.jctc.4c01166 | R/complexity | Primary preprint (scope unstated) | VERIFIED (journal-before-arXiv dating confirmed) |
| 95 | A. O. Schouten, D. A. Mazziotti | Entanglement complexity in many-body systems from positivity scaling laws | 2025 | arXiv (published in PRA, not noted in record) | arXiv:2509.02944 | R/complexity | FULL (HTML v1); complexity details not audited | VERIFIED. Note: Phys. Rev. A 113, L030401 (2026), DOI 10.1103/6jzd-qqkb (from arXiv journal-ref, not in record) |

---

## Verification tally

* Distinct works: **95**.
* **VERIFIED:** 81.
* **CLASSIC:** 14, all also confirmed by id: #1, 2, 3, 18, 19, 20, 21, 79, 82, 83, 84, 88, 90, 91.
* **MISMATCH:** 0. **NOT FOUND:** 0. **UNCHECKED:** 0.
* Every one of the 26 arXiv ids from 2025–2026 (25xx/26xx) resolved to the stated authors and topic. That includes the two August 2026 preprints, 2608.25760 (Liu) and 2608.22252 (Ming–Yu), and the two July 2026 preprints, 2607.15358 (Dutkiewicz et al.) and 2607.25872 (Li et al.). Every 2025–2026 DOI resolved and matched.
* **Discrepancies that are not mismatches:**
  * Some online-first and print years differ: Feischl–Schwab 2019/2020, Chernov et al. 2010/2011, Fournais et al. 2008/2009, Ireland et al. 2021/2022.
  * Some arXiv titles differ from the journal titles: O'Gorman et al., Li et al. (spin symmetry), Fournais–Sørensen (Crelle).
  * Newer arXiv versions have appeared since the reading: Beck–Stamm v2, Sheng v5, Large Electron Model v2, Clifford DMRG v2.
  * Journal versions exist that the records do not note: Weflen (JPCL 2025), Schouten–Mazziotti (PRA 2026), Fournais–Sørensen (Crelle 2021), Flad et al. II (Asian-Eur. J. Math.), Nam (CMP 2012). Bazley–Fox also has a DOI (10.6028/jres.065B.009) that its record does not give.
* **Works the records say were not read beyond abstract or metadata, or whose full text could not be obtained:** Kato 1949, 1950, and both 1951 papers; Lieb 1984 (read only through Nam); Lieb 1983; Hohenberg–Kohn; Bazley 1959 and 1960; Klahn–Bingel I and II; Klahn thesis; Hill 1985 and 1995; Morgan 1986; LapNet; QCMaquis 4.0; FermiNet; PauliNet; Psiformer; Li et al. 2024 (spin symmetry); Low–Chuang; Schleich et al. The journal versions of Maday–Marcati and Anapolitanos et al. were not read (their arXiv versions were).

## Full-text copies archived under `helium_research/sources/` (filenames only; PDFs not opened)

| File(s) | Work | Probable origin / copyright status |
|---|---|---|
| `approx_chernov_petersdorff_schwab2011.pdf`, `.txt` | Chernov–von Petersdorff–Schwab, M2AN 2011 | Publisher PDF (NUMDAM copy of ESAIM:M2AN). © EDP Sciences/SMAI; free to read but copyrighted |
| `approx_feischl_schwab2018.pdf`, `.txt` | Feischl–Schwab | Institutional preprint (KIT CRC 1173 Preprint 2018-23). Author/institution copyright; not the publisher version |
| `approx_flad_hackbusch_schneider2006.pdf`, `.txt` | Flad–Hackbusch–Schneider I | Publisher PDF (NUMDAM, ESAIM:M2AN). Copyrighted |
| `approx_flad_hackbusch_schneider2007.pdf`, `.txt` | Flad–Hackbusch–Schneider II | Publisher PDF (NUMDAM, ESAIM:M2AN). Copyrighted |
| `approx_flad_schneider2012.pdf`, `.txt` | Flad–Schneider 2012 | Publisher PDF (NUMDAM, ESAIM:M2AN). Copyrighted |
| `approx_flad_schneider_schulze2007.pdf`, `.txt` | Flad–Schneider–Schulze | Author preprint (2007-05-23) from the DNB repository (d-nb.info). Author copyright; not the Wiley version |
| `bazley_fox_1961.pdf` | Bazley–Fox, J. Res. NBS 65B | NIST-hosted scan (nvlpubs.nist.gov). US federal government work, likely public domain in the US |
| `hp_ammann_carvalho_nistor_2010.pdf`, `.txt` | Ammann–Carvalho–Nistor | arXiv preprint 1010.1712 |
| `hp_ammann_mougel_nistor_2020.pdf`, `.txt` | Ammann–Mougel–Nistor | arXiv preprint 2012.13902 |
| `hp_bachmayr_chen_schneider_2012.pdf`, `.txt` | Bachmayr–Chen–Schneider | Preprint from the DNB repository (d-nb.info/1248220269). Author copyright; not the Springer version |
| `hp_flad_harutyunyan_schulze_2018.pdf`, `.txt` | Flad–Flad-Harutyunyan–Schulze II | arXiv preprint 1801.07552 |
| `hp_maday_marcati_2019.pdf`, `.txt` | Maday–Marcati | arXiv preprint 1912.07483 |
| `hp_scholz_yserentant_2016.pdf`, `.txt` | Scholz–Yserentant | arXiv preprint 1612.00360 |
| `hp_yserentant_barron_2025.pdf`, `.txt` | Yserentant (Barron) | arXiv preprint 2502.17950 (inferred from the naming convention) |
| `hp_yserentant_mixed_2011.pdf`, `.txt` | Yserentant, M2AN 2011 | Probably the publisher PDF (the record cites the NUMDAM full text; no arXiv version is cited). Copyrighted |
| `ireland_2021.xml`, `.txt` | Ireland et al., ACS Phys. Chem. Au | Europe PMC full-text XML. The XML carries a CC BY 4.0 license tag, so it is open access and redistributable with attribution |
| `liu_2026.html`, `.txt` | X. Liu, arXiv:2608.25760v1 (the HTML contains this id) | arXiv HTML rendering of a preprint. No CC license string found, so presumably the arXiv default non-exclusive license: readable, not freely redistributable |
| `nakashima_nakatsuji_2008.pdf` | Nakashima–Nakatsuji, PRL 101, 240406 | Publisher PDF hosted by the author institution (qcri.or.jp). © APS; copyrighted |
| `regularity_fournais2005_math-ph0312060.pdf`, `.txt`, `_p3.png` | FHOHOS 2005 | arXiv preprint (manifest URL arxiv.org/pdf/math-ph/0312060); PNG is a page render |
| `regularity_fournais2009_0806.1004.pdf`, `.txt`, `_p4.png` | FHOHOS 2009 | arXiv preprint |
| `regularity_fournais_sorensen2018_1803.03495.pdf`, `.txt`, `_p5.png` | Fournais–Sørensen | arXiv preprint |
| `regularity_ming_yu2026_2608.22252.pdf`, `.txt`, `_p3.png` | Ming–Yu | arXiv preprint |
| `temple_1928.pdf`, `.txt`, `_p292.png` | Temple, Proc. R. Soc. A 1928 | Royal Society journal scan, obtained from a third-party mirror (scispace). Copyright is held by the publisher. It is probably public domain in the US, since 1928 publications entered the US public domain in 2024, but probably still in copyright in the UK (life + 70; Temple died 1992) |
| `weinstein_1934.html` | Weinstein, PNAS 1934 | Saved PMC article/scan-viewer page (PMC1076472). PNAS content; US status for 1934 depends on copyright renewal, so uncertain |

Metadata or abstract evidence only (not full texts): `kb_BF00548026_publisher.html`, `kb_BF00548027_publisher.html`, `kb_BF00548026_openalex.json`, `kb_BF00548027_openalex.json`, `retrieval_hill1985_crossref.json`, `retrieval_hill1985_openalex.json`, `retrieval_hill1985_publisher_abstract.html`, `retrieval_hill1995_openalex.json`, `hp_archive_manifest.json`, `regularity_archive_manifest.json`.
