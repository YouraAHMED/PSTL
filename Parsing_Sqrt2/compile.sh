
#!/bin/sh

ocamllex lexer.mll
ocamlc -c ast.ml
ocamlc -c eval.ml
ocamlc -c conversion2.ml
ocamlyacc parser.mly
ocamlc -c parser.mli
ocamlc -c lexer.ml
ocamlc -c parser.ml
ocamlc -c main.ml
ocamlc -o main ast.cmo eval.cmo conversion2.cmo lexer.cmo parser.cmo main.cmo

echo "Compilation terminée."

if [ "$#" -eq 1 ]; then
    FILE="$1"
    echo "Traitement du fichier $FILE"
    ./main "$FILE" Samples/resultat/$(basename "$FILE" .rew).why  
else
    echo "Traitement de tous les fichiers dans Samples/"
    for file in Samples/*.rew; do
        base=$(basename "$file" .rew)
        echo "→ $file"
        ./main "$file" resultat/$base.why
    done
fi
