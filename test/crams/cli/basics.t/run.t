Help message should display when the `--help` flag is given

  $ adelfa --help
  Usage: adelfa [options]
  options are: 
    -i  Specifies a file from which to read input.
    -s  Specified a file from which to read a specification.
    --input  Specifies a file from which to read input.
    -a  Annotate mode
    -help  Display this list of options
    --help  Display this list of options

Error message is shown when an input file is specified that doesn't exist.

  $ adelfa -i non-existant-file.ath
  Fatal error: exception Failure("Error: Invalid input file: `non-existant-file.ath'.")
  [2]

Error message shown when multiple input files given.

  $ adelfa -i file1.ath -i file2.ath
  Fatal error: exception Failure("Error: More than one input file specified.")
  [2]
