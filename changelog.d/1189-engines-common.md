### Engines-common, a Lean package of its own

What every engine shares moves into `engines/`, the Lake package
`sverify-engines` with modules `Sverify.Engines.*`: the Engine structure,
the table machinery (`EngineProfile`, the observation rows' constructors,
the option-wise transfer), the shared shims `Shim.*` and the
`check_generated` switch ([#1189](https://github.com/AlexanderNenninger/substrait-lean/issues/1189)).
It builds on the core alone, and CI checks that it does. No theorem
changed.
