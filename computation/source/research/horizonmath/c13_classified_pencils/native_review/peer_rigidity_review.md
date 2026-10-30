# Independent #700-worker review of the optimal30 rigidity extension

Reviewed 2026-10-01. The mathematical reduction is sound conditional on the
published complete minimum-link classification and the separately verified
complete domain reconstruction. Five degree15 points supply a root and four
other minimum points. Full-star domain construction and literal pair/arc
compatibility do not depend on the outside-block budget. Every surviving
compatible pencil tuple has union15, exhausting a30-block cover's outside
budget. Testing its actual thirty blocks and finding an uncovered quadruple
therefore contradicts coverhood. The known30 control attains four minimum
points, establishing sharpness when the exclusion is combined with it.

I inspected the native domain builder, pair signatures, synchronous arc
filter, exact six-relation join, sorted-vector intersections, coverage helper,
and known30 positive control. No mathematical or transition defect was found.
Checking quadruples avoiding the selected minimum points independently is
sufficient because their complete classified links cover every quadruple
incident to those points. The native full715-quadruple check is stronger as
an implementation crosscheck.

I independently compiled and reran the supplied C++ implementation using
`g++ -O2 -std=c++17 -Wall -Wextra -Werror -pedantic check_30_rigidity.cpp -lcrypto`.
Source SHA256: fd55dfb0a381125dfdd926ff33c9a01c40ab393446cce867a647ee9904bcd7c8.
Fresh output SHA256: cbe121161a06e93d15ad351c09e0d5ae69fe2fbbcd63884f53e421b3346546dc.
The normal and optimized Python receipt checks both pass:816 domains,
33,660 foursets,42 exact joins,280,152 tuples,zero valid30 completions,
minimum two uncovered quadruples,sharp positive control with four minima.
This is an independent rerun and code/algebra review, not a separately authored
native implementation or an external-human/formal proof review.

I flagged a minor input-contract hardening opportunity in the receipt validator:
per-class closure counts should explicitly be nonnegative integers, rather
than relying only on per-class and global sums. This does not alter the native
arithmetic result; any subsequent validator changes need their own controls.

The producer subsequently added explicit per-class integer/range checks and
negative/bool controls. I reran all 11 receipt tests in normal and optimized
Python and validated my fresh native output with the hardened validator: PASS.
The input-contract observation is therefore resolved in this staged packet.
