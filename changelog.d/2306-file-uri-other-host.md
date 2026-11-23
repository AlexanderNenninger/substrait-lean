### A `file:` URI on another host is no local path outside Windows

On Linux and macOS, `file://otherhost/x` was read as the local file `/x`. Such a URI now takes the non-native read path. On Windows the host is a UNC share as before, and `file:///x` and `file://localhost/x` read as before ([#183](https://github.com/AlexanderNenninger/substrait-lean/issues/183), [#2306](https://github.com/AlexanderNenninger/substrait-lean/pull/2306)).
