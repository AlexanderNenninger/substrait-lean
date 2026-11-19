### Spark no longer keeps a view for every change it merges into a state

Merging an Arrow change into a view's state on Spark registered the change as a temporary view that nothing dropped, so the Spark JVM kept the rows of every refresh until the session ended. A pipeline with large changes ran the driver out of its default 1 GB heap, and the JVM then hung instead of failing. The change now goes to Spark as a frame that no view names.
