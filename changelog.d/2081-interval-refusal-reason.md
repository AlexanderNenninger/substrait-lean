### The refusal of a duration compared with an interval of days or months gives its own reason

A comparison of a duration (`ts - ts`, `d - d`) with an interval of days or months is still refused, and the message now says why: durations compare as microseconds, and no month length suits every engine. Write the interval in hours or seconds ([#2081](https://github.com/AlexanderNenninger/substrait-lean/issues/2081)).
