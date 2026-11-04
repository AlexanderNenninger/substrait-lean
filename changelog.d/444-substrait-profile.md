### Checking under Substrait's own semantics

`verify(semantics="substrait")` checks an Ibis transformation under
`Profile.substrait`, Substrait's semantics as its extension YAMLs state it
([#444](https://github.com/AlexanderNenninger/substrait-lean/issues/444)):
each option at the plan's preference among the YAML's values, any of them
where the plan states none, two zeros and signed NaNs as IEEE 754 has them,
and open wherever the YAMLs say nothing. Lean proves it refines the core
(`Profile.substrait_le_core`). The reference's proof holds there when, at
every option the plan meets, Substrait allows nothing the reference does
not; otherwise `Report.transfer` names the options. `substrait-check
--profile-diff` lists where the two profiles differ, published in
[docs/core-semantics.md](docs/core-semantics.md#the-substrait-profile).
