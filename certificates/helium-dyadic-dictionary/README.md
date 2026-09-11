# Helium ground state: dyadic multi-exponent dictionary (E2–E10)

The dictionary $E_n$ consists of the functions
$$e^{-\alpha_j(r_1+r_2)}\,p(r_1,r_2,r_{12}),\qquad \alpha_j = 2^{j+1},\quad j=0,\dots,\lfloor n/2\rfloor,$$
where $p$ ranges over the symmetric Hylleraas polynomials of degree $n-2j$, each with a rational power-of-two normalization. $E_{10}$ has 336 functions and gives the tightest helium enclosure in the repository:

$$E_\text{He}\in[-2.903724385192751581540207,\ -2.903724377006065467379698]\quad(\text{width }8.19\times10^{-9}\text{ Ha}).$$

## Pipeline

The optimization stage is **untrusted**: `run.py` selects coefficients by minimizing a regularized fixed-shift objective and writes `screen_E_n.json` (the trial) and `matrices_E_n.json` (the pairwise pencil matrices).

The certificate stage, `certify.py E n --bits b`, is the checker. It:

1. Rebuilds the dictionary from its definition.
2. Recomputes $\lVert\Phi\rVert^2$, $\langle\Phi,H\Phi\rangle$ and $\lVert H\Phi\rVert^2$ exactly by grouped polynomial $H$-actions, and asserts that they equal the pairwise-matrix contractions.
3. Evaluates the variance with $b$-bit outward intervals, applies Temple's bound with $\beta=-5/2$, and rounds the endpoints outward to 24 decimal places.
4. Certifies positive-definiteness of the regularized finite pencil by interval LDL. For E10 this fails at 512 bits and passes at 1024 bits.

It imports the exact algebra from `../helium-ground-state/` (`hylleraas.py`, `check_trial.py`, `certified_interval.py`).

## Run

```bash
cd certificates/helium-dyadic-dictionary
python3 certify.py E 10 --bits 1024    # about 6 minutes
```
