### A double→integer cast in `to_substrait` now carries ST-6's shim or assumption

Substrait leaves open how a cast of a double or a decimal to an integer rounds ([ST-6](upstream/bugs/ST-6.json)), and `to_substrait` exported such a cast as exact. The cast now reads `float_to_int`: `shims="apply"` truncates first (`floor` for `x >= 0`, `ceil` otherwise, then the cast), `"annotate"` ships ST-6's assumption, and `"refuse"` refuses. Under `semantics="substrait"` such a plan is no longer proved ([#2438](https://github.com/AlexanderNenninger/substrait-lean/issues/2438)).
