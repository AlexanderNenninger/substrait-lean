### A decimal cast to a smaller scale in `to_substrait` now carries ST-8's assumption or refuses

Substrait leaves open how a cast of a decimal to a smaller scale rounds ([ST-8](upstream/bugs/ST-8.json)), and `to_substrait` exported such a cast as exact in every mode. The cast now reads `decimal_rescale`: `shims="apply"` refuses it, since ST-8 has no rewrite, `"annotate"` ships ST-8's assumption, and `"refuse"` refuses ([#2504](https://github.com/AlexanderNenninger/substrait-lean/issues/2504)). A plan whose decimals keep every digit (sums, products, casts to a larger scale) exports as before.
