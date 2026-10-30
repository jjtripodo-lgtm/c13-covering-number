# Compiled catalog-relative replay of the C13 pencil obstruction

This is additive assurance for the frozen Python proof, not a new mathematical
assumption or a replacement for the raw-source catalog completeness check.

The C++ implementation independently reconstructs every rooted-star domain
from all68 catalog links and all source centers. It does not reuse the Python
62-star-type cache. Exact signatures only prune impossible partial point maps;
complete maps must preserve the entire star. Every816 canonical domain SHA256
agrees with the separately reconstructed Python domains.

It then enumerates all33,660 labeled four-minimum pointsets, obtaining31,263
pair closures,2,355 arc closures and42 exact union-search closures. No forced
union or nonminimum-point degree pruning is used. The known30-cover passes all
715 direct quadruple checks, and all three of its actual nonroot minimum pencils
remain in their domains. A synthetic compatible14-block tuple survives; a13-block
budget, inconsistent shared pencils, malformed block IDs and duplicate source
blocks reject.

GCC14.2 with strict warnings and optimized code passes. A separate GCC build
with undefined-behavior sanitization and standard-library assertions produces
byte-identical output with no diagnostics. This is two builds of one compiled
implementation, not two independently authored C++ algorithms.

Full output SHA256:
`b06bc67b873b1969da5b0219af89fa9a7c955573084af0855333285e43b368ff`.
The exact final search visits55,813 nodes. Node counts differ from another
implementation's traversal and are not a mathematical claim in themselves.

Reproduce with an installed C++17 compiler and OpenSSL development library:

```
python prepare_catalog.py --proof-dir .. --check
g++ -O2 -std=c++17 -Wall -Wextra -Werror -pedantic check_pencils.cpp -lcrypto -o /tmp/c13-native
/tmp/c13-native > /tmp/c13-native.jsonl
python validate_compiled.py /tmp/c13-native.jsonl --proof-dir ..
g++ -O1 -g -std=c++17 -Wall -Wextra -Werror -pedantic -fsanitize=undefined -fno-sanitize-recover=all -D_GLIBCXX_ASSERTIONS check_pencils.cpp -lcrypto -o /tmp/c13-native-ubsan
/tmp/c13-native-ubsan > /tmp/c13-native-ubsan.jsonl
cmp /tmp/c13-native.jsonl /tmp/c13-native-ubsan.jsonl
```

The source catalog's complete coverage of minimum links still comes from the
credited published classification and the independent raw21952-completion
Python reconstruction. This compiled check deliberately states its narrower
catalog-relative role. No novelty, Lean, external referee or public-release
claim is made.
