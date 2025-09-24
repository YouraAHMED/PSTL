#!/bin/sh

#!/bin/sh
echo "Nettoyage des fichiers de compilation..."
rm -f *.cmo *.cmi parser.ml parser.mli lexer.ml main

echo "Fichiers OCaml nettoyés. Les fichiers .why dans resultat/ sont conservés."
