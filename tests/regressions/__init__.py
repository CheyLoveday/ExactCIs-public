"""Frozen evidence baseline for the post-1.0.0 numerics programme.

Every test in this package pins behaviour that was measured against installed
``exactcis==1.0.0``. Tests marked ``xfail(strict=True)`` describe defects that
are expected to be repaired by a later tranche: when the repair lands the test
reports XPASS, the run fails, and the marker must be removed in the same change
that fixes the behaviour. That is the mechanism which stops a repaired defect
from silently regressing to "expected to fail".
"""
