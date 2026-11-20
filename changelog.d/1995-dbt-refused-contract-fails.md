### sverify-dbt fails a refused model with an enforced contract

`sverify-dbt check` exits 1 under the default `--fail-on contract` when sverify refuses a model whose contract is enforced, and names the refusal on stderr; it used to exit 0 on exactly the model it could not read ([#1995](https://github.com/AlexanderNenninger/substrait-lean/issues/1995)). A refused model without a contract still exits 0.
