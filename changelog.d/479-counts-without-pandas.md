### Checks on data no longer warn through pandas

The checks on data (`on_unproved="runtime"`, `requires` on bound tables, node
refreshes) counted violations with Ibis's `execute()`, which converts the count
through pandas. Under Ibis 12 and pandas 3.1 that printed a `Pandas4Warning`
about `future.infer_string`, in notebooks 4 and 5 of the tour among other
places. The counts are now fetched through Arrow
([#479](https://github.com/AlexanderNenninger/substrait-lean/issues/479)).
