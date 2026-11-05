### A map of the proofs

[`docs/proofs.md`](docs/proofs.md) names each Lean module's job and the
theorems each guarantee rests on (`contract_sound`, `Rel.keys_sound`, the
delta rules, the engine profiles' shims), with what they trust. Each
generated Lean module's header says how to regenerate it, and
`tests/test_proof_map.py` keeps the map in step with the modules (#733).
