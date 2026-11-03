### Arrow Flight sources

`sverify.io.flight.FlightSource` reads a table of a numbered batch log on an
Arrow Flight server: each refresh streams the batches after the last one
read, registers them with the engine without a copy, and reads the batches
the server dropped past its retention as deletes. `FlightLog` is a small
in-memory server for that log, and the [guide](docs/guide.md) documents the
protocol for other servers. `pip install 'sverify[flight]'` (#375).
