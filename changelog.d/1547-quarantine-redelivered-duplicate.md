### A redelivered duplicate no longer takes a published row out of the sink

With `on_violation="quarantine"` and a `unique` key, an exact copy of a row the node already holds sent both copies to quarantine and deleted the published row. Rows identical in every column now count once: the kept row stays and the extra copy is set aside. Copies that disagree on some column still go to quarantine together ([#1547](https://github.com/AlexanderNenninger/substrait-lean/issues/1547)).
