> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

| Family | index | residual model | full log-SSE | trailing-five log-SSE | full/trailing alpha | last-two predicted / observed |
|---|---|---|---:|---:|---|---|
| A | n | power | 0.008435 | 0.0002447 | — | 1.060, 1.094 |
| A | n | exponential | 0.362 | 0.00264 | 1/1 | 0.690, 0.561 |
| A | n | stretched | 0.001212 | 1.491e-06 | 0.12/0.23 | 1.020, 1.035 |
| A | m_n | power | 0.02527 | 8.295e-07 | — | 0.928, 0.906 |
| A | m_n | exponential | 1.72 | 0.02263 | 1/1 | 0.391, 0.180 |
| A | m_n | stretched | 0.05031 | 6.802e-05 | 0.05/0.05 | 0.889, 0.848 |
| B | n | power | 0.008994 | 0.005241 | — | 1.069, 1.076 |
| B | n | exponential | 0.3533 | 0.01431 | 1/1 | 0.662, 0.464 |
| B | n | stretched | 0.006704 | 0.003225 | 0.07/0.3 | 1.045, 1.037 |
| B | m_n | power | 0.03461 | 0.003815 | — | 0.925, 0.856 |
| B | m_n | exponential | 1.781 | 0.1118 | 1/1 | 0.313, 0.082 |
| B | m_n | stretched | 0.06172 | 0.0039 | 0.05/0.05 | 0.881, 0.786 |
| C | n | power | 4.844 | 0.1416 | — | 4.174, 8.186 |
| C | n | exponential | 0.04087 | 0.003127 | 1/1 | 0.949, 0.836 |
| C | n | stretched | 0.02578 | 0.002839 | 0.94/0.96 | 1.007, 0.925 |
| C | m_n | power | 1.611 | 0.06911 | — | 2.394, 3.759 |
| C | m_n | exponential | 5.1 | 0.3011 | 1/1 | 0.157, 0.020 |
| C | m_n | stretched | 0.03591 | 0.003463 | 0.31/0.31 | 0.999, 0.900 |
| D-shell | n | power | 2.207 | 0.5473 | — | 2.991, 7.328 |
| D-shell | n | exponential | 0.1179 | 0.02479 | 1/1 | 1.347, 1.788 |
| D-shell | n | stretched | 0.1179 | 0.02479 | 1.0/1.0 | 1.347, 1.788 |
| D-shell | m_n | power | 1.135 | 0.2617 | — | 2.308, 4.728 |
| D-shell | m_n | exponential | 1.679 | 0.7657 | 1/1 | 0.237, 0.013 |
| D-shell | m_n | stretched | 0.01008 | 0.002174 | 0.39/0.34 | 0.964, 0.790 |
| D-tensor | n | power | 0.08398 | — | — | — |
| D-tensor | n | exponential | 0.2404 | — | 1 | — |
| D-tensor | n | stretched | 0.0898 | — | 0.05 | — |
| D-tensor | m_n | power | 0.0883 | — | — | — |
| D-tensor | m_n | exponential | 0.6405 | — | 1 | — |
| D-tensor | m_n | stretched | 0.1061 | — | 0.05 | — |
| E | n | power | 2.905 | 0.07003 | — | 2.773, 4.926 |
| E | n | exponential | 0.01996 | 0.002397 | 1/1 | 1.043, 1.126 |
| E | n | stretched | 0.01996 | 0.002397 | 1.0/1.0 | 1.043, 1.126 |
| E | m_n | power | 1.166 | 0.03806 | — | 1.939, 2.980 |
| E | m_n | exponential | 4.662 | 0.1696 | 1/1 | 0.166, 0.027 |
| E | m_n | stretched | 0.004427 | 0.0002576 | 0.29/0.31 | 0.945, 0.940 |
