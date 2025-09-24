# PSTL – Traducteur .rew → WhyML

## Description
Ce projet a pour objectif de développer un traducteur qui prend en entrée un langage simplifié (`.rew`) et le transforme automatiquement en un fichier **WhyML (`.why`)** utilisable par l’outil de vérification formelle **Why3**.  

Il a été réalisé en **OCaml**, en mettant en place un **lexer**, un **parser** et une génération structurée d’AST (Arbre Syntaxique Abstrait).  

---

## Objectifs
- Lire un fichier `.rew` contenant des fonctions et leurs spécifications.  
- Construire un **AST** représentant le code source.  
- Générer un fichier `.why` correct et vérifiable par Why3.  
- Gérer progressivement des structures complexes :  
  - spécifications partielles (`spec`),  
  - boucles `while` avec invariants et variants,  
  - conditions `if / else`,  
  - opérations comme la division entière.  
- Assurer la validité des transformations via des prouveurs automatiques (Alt-Ergo, CVC4, etc.).  

---

##  Pipeline de transformation
```text
   .rew (langage simplifié)
              │
              ▼
   Lexer + Parser (OCaml)
              │
              ▼
   AST (Arbre Syntaxique Abstrait)
              │
              ▼
   Générateur de code
              │
              ▼
   .why (WhyML vérifiable par Why3)




Ahmed Youra

Koné Daba
