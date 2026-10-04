#!/usr/bin/env python3
"""Replay the expanded latest-stage Rung 2 snapshot with the original runner."""
import sys
import verify_rung2_recovery_v2 as recovery

recovery.RECOVERY = recovery.ROOT / "recovery/rung2-latest-2026-10-04"

if __name__ == "__main__":
    sys.exit(recovery.main())
