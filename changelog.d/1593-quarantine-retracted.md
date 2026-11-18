### Quarantine report: published rows a disagreeing duplicate took out

`QuarantineReport` gains `retracted`: of the rows a refresh quarantined, how many the node had already published, because a new row repeated their key with other values. The report line says "N already published", and the refresh JSON has a `retracted` field per source ([#1593](https://github.com/AlexanderNenninger/substrait-lean/issues/1593)).
