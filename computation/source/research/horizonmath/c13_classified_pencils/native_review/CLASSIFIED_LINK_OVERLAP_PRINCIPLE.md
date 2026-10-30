# Classified link overlap: a reusable exact reduction

This is a written reduction and a bounded transfer note, not a novelty claim.
It is separate from the frozen C13 proof packet and does not change its inputs.

## Lower-degree version for covers

Let an N-block k-uniform covering family on v points have every point degree
at least L. Put E=Nk-vL and suppose 0<=E<v. At least v-E points have degree
exactly L: every other point contributes at least one unit to the excess sum E.
Assume a complete finite catalog of the admissible L-block point links.

Fix a degree-L root r and choose s other degree-L points, with
1<=s<=v-1-E. The root link fixes the complete r-containing star in each chosen
point's link. For each such point q, enumerate all catalog links, source centers
and unrestricted remaining-point bijections preserving that known star. The
source blocks avoiding the source center, transported and augmented by q, form
all possible complete root-avoiding pencils P_q through q.

Any original family gives choices satisfying, for each q!=u,

    {B in P_q : u in B} = {B in P_u : q in B},
    |union_q P_q| <= N-L.

The first condition follows because both sides are precisely the family's
root-avoiding blocks through both q and u. The second follows because only N-L
blocks avoid r. Exhaustion of these conditions therefore gives a rigorous
exclusion; a surviving tuple alone is not a covering construction.

There is also an exact completion statement. Once a compatible tuple is chosen,
every further root-avoiding block must avoid all s chosen points, since each
pencil was complete. Thus only C(v-1-s,k) block candidates remain outside the
pencil union. Enumerating the required number of these and directly checking
the original covering condition gives a complete finite search, not merely a
necessary relaxation.

For C13 with N=29,k=7,v=13,L=15, E=8 and s=4. The outside budget is14; only
C(8,7)=8 optional blocks could remain after fixing the pencils. In the banked
candidate proof, this last completion stage is unnecessary: every compatible
four-pencil tuple already uses15 outside blocks. The computed domains range
from1 to3532 patterns, despite the initial block space having792 variables.

## Upper-degree version for packings

The same argument reverses degree accounting. If every point degree is at
most U, put F=vU-Nk and suppose 0<=F<v. At least v-F points have degree U.
A complete catalog of saturated U-block links then gives the identical pencil
compatibility and outside-union conditions, with root budget N-U and any
1<=s<=v-1-F other saturated points. The proof is unchanged after replacing
excess by deficit. This applies to any set-family model whose point links and
local admissibility can be stated exactly; it is not automatically an efficient
algorithm.

## Concrete A29 transfer limit

For a38-block linear5-uniform packing on29 points (constant-weight distance8),
every degree is at most floor(28/4)=7. The total deficit is29*7-38*5=13, so at
least16 points are saturated. A saturated point link is a partition of the
other28 points into seven4-sets.

Although that link has one isomorphism type, fixing only its known star at a
second saturated point leaves a raw domain of

    24! / ((4!)^6 * 6!) = 4,509,264,634,875

partitions of the remaining24 points into six unlabeled4-sets. This count is
before filtering against the other root blocks or quotienting their stabilizer;
it is not a lower bound on the final admissible representation size.

Therefore the C13 literal-domain enumeration should not simply be reused for
A29. The abstract reduction transfers, but useful implementation would need
root-block intersection restrictions, a compact symmetry/partition encoding,
or the already developed deficiency structure. A huge raw partition census or
another timeout would not advance that problem. This is a precise representation
obstacle, not a proof that the A29 packing itself is impossible or computationally
intractable.
