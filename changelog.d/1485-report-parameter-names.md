### Reports name the transform's parameter

When the result of one contracted transformation feeds another, the downstream report says `requires orders: …`, the name in its own `requires`, in place of the name of the upstream transformation that feeds it (`requires latest: …`). The same holds for the "needs" text (#1485).
