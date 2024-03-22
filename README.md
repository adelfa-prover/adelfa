# Adelfa


## Building

To build Adelfa, run `make` in the root directory. This will produce an
executable named `adelfa` which can be ran directly or via the command `dune
exec adelfa` to start the system.

Run `make debug` to build a byte code version of the system located at
`_build/default/bin/adelfa.bc`.

Run `make test` to build the unit tests. This will produce and execute
`_build/default/bin/test.exe` as well as a series of crams which run examples
across expected output.

Run `make install` to install Adelfa to your system's `.opam/default/bin/`
directory.

## Usage

```sh
adelfa
```

Starts the system. See [system_reference.txt](./system_reference.txt) for more
information about using the system.

```sh
adelfa -i filename
```

Specifies `filename` as the file from which to read input. This runs each
command from the file and then quits the system.