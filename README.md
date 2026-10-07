# json2dir-unlambda

json2dir in Unlambda: `json2dir.unl` (s, k, i, c, d, v and the I/O primitives, generated from the lambda-calculus source `json2dir.lam` by the bracket-abstraction compiler `unlc.py`) validates the JSON document and prints a shell script, which the POSIX sh launcher `json2dir` runs.

    python3 unlc.py json2dir.lam > json2dir.unl
    JSON2DIR_UNLAMBDA=/path/to/unlambda ./json2dir < tree.json
