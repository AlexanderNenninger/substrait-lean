### Polars's product of decimals comes from the proved lowering

On Polars, sverify now writes the product of two decimals from a template that
the Lean build proves (`Polars.dmulTemplate`, `Polars.dmul_bound`) instead of a
hand-written helper. The template multiplies the unscaled values in Polars's
`Int128` only where the product stays below 2¹²⁶, and raises an overflow
everywhere else. That bound sits past 38 digits, so the overflow only comes
earlier than the reference's own. Because the entry can raise, a plan that
multiplies decimals runs on Polars with its checks kept, even when its report
is guard-free. This includes a sum of decimals at two scales, which rescales
by a product. The report records this per engine (`exact_lowering`) (#2586).
