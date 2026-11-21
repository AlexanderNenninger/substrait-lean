### An AWS session reports its own scope

`Storage` fills `reads` and `writes` from the session when they are not declared: with `boto3` installed, sverify asks STS who the session is, reads the `GetObject` and `PutObject` grants of that role's or user's policies and keeps the prefixes, once per credential. `sverify check` then warns with `[scope]` about a sink outside `staging/` without a `writes=` declaration. A `Deny`, a condition or a pattern that is not a prefix leaves the scope unknown ([#778](https://github.com/AlexanderNenninger/substrait-lean/issues/778)).
