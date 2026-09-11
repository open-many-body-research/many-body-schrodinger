> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual physical H12 cutoff schedule, version 1

The formal construction now supplies the twelve spectator cutoff stages and the five spatial recovery cutoff stages on the actual two-electron selected spectator space, for either i:Fin2. It establishes geometry only; the physical weak equation, coefficient/source bounds, and finite iteration remain separately composed results.

Write e_i for the previously verified product linear isometry fixing Y and reindexing the three actual spectator coordinates. For a center (0,t), let delta=1/4352 and r(j)=1/64-j delta. The physical region at gap j is the inverse image under e_i of the rectangular open box with both half-widths r(j). The exact identity r(34)=1/128 is proved. The boxes are open, measurable and antitone in j. Every nonnegative gap is contained in the initial box.

At a stage starting at gap j, eta is the existing actual C-infinity energy cutoff, supported inside the outer box and equal to one on gap j+1; chi is the existing inner cutoff, supported inside gap j+1 and equal to one on gap j+2. For 0<=j<=32, their two-gap width hypotheses are verified. The uniform spatial coefficient radius is S=1/32 since the Y center is zero and every outer half-width is at most 1/64.

The spectator schedule uses gaps 2k for k=0,...,11 and ends at gap 24. Its `SpectatorStepGeometry c` applies at c=4 for either nuclear chart and c=1 for the pair chart. The spatial schedule starts at gap 24 and uses gaps 24+2k for k=0,...,4, ending exactly at gap 34. Its geometry is `SpectatorStepGeometry 0`; this does not replace the physical PDE coefficient, which remains an independent parameter in the Y iterator. The join of the two region arrays is an exact equality.

All stage constants retain M=D=1, A=(4+3*c*S^2)*8*(C2+C1^2)/delta^2 and B=Q=(4+3*c*S^2)*(4*C1/delta)^2. The spatial geometry substitutes c=0. C1 and C2 are explicit hypotheses bounding the first and second derivatives of the actual Real.smoothTransition; no new numerical values are asserted in this unit. No solution, PDE, or assumed regularity appears in these hypotheses.

The API is `physical_h12_T12_geometry`, `physical_h12_Y5_geometry`, `physicalH12Schedule_T12_Y5_join`, and `physicalH12Schedule_terminal`. The arrays are `physicalH12ScheduleRegion`, `physicalH12ScheduleMiddle`, `physicalH12ScheduleInnerCutoff`, and `physicalH12ScheduleEnergyCutoff`, each indexed by the initial gap and stage. Openness, measurability and nesting are explicit theorems.

Three new modules, 46 declarations, passed the pinned Lean 4.34.0-rc2 compiler and strict expanded-statement/axiom audits. Only propext, Classical.choice and Quot.sound occur. Existing pinned dependency objects were reused; this unit is not an isolated source rebuild. Both selected indices are handled by the actual proved coordinate equivalence, not a cardinality coercion. Existing frozen and successful bytes are preserved.

This discharges the concrete cutoff-schedule input to the finite iterators. It does not itself establish a weak-PDE estimate, coefficient-patch inclusion, global H2 approximation, Theorem T, or certified energy computation.
