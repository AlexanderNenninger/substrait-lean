### Secrets and Flight: values read as written, errors that say what is wrong

- A `KEY=value` secret file loses only one pair of matching quotes around a value, so `PASSWORD=abc'` reads as `abc'` ([#2429](https://github.com/AlexanderNenninger/substrait-lean/issues/2429)).
- A JSON field that is not a string reads as its JSON: `true`, `null`, `{"a": 1}`. This applies to `file:` secrets and to OpenBao and Vault ([#2429](https://github.com/AlexanderNenninger/substrait-lean/issues/2429)).
- `azure-kv:` takes a vault's URL as well as its name, as in `azure-kv:https://myvault.vault.azure.net/lake` ([#2433](https://github.com/AlexanderNenninger/substrait-lean/issues/2433)).
- A misconfigured secrets backend says what is wrong, such as `[secrets.bao]: unexpected keyword argument 'adress'`, and a `names` table without `ref` says so ([#2428](https://github.com/AlexanderNenninger/substrait-lean/issues/2428)).
- `FlightLog` refuses a ticket whose values have the wrong type with the ticket's shape, and no longer answers with a server traceback ([#2427](https://github.com/AlexanderNenninger/substrait-lean/issues/2427)).
