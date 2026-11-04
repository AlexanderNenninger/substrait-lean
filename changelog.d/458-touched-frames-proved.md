### Touched frames are proved

Lean now proves the touched-frames strategy, which maintains window
aggregates over bounded RANGE frames of one time column by recomputing only
the rows near a batch's changes
([#458](https://github.com/AlexanderNenninger/substrait-lean/issues/458),
part of [#294](https://github.com/AlexanderNenninger/substrait-lean/issues/294)).
A window row depends only on the rows of its partition whose time lies in
its frame (`TouchedFrames.outRow_local`), so the rows outside
`[t0 - end, t1 - start]` keep their values and the rows inside come out the
same from the narrowed input (`TouchedFrames.framed_batch`). `status()` and
the refresh summary no longer say "tested, not proved", and
`NodeStatus.tested` is now `NodeStatus.framed`.

A window whose frames all end before the row (or start after it) lost the
output rows near the end of a batch's span: the recompute read too few
input rows. The span now always holds the row itself.
