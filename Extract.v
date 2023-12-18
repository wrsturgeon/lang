From Coq Require Import
  Extraction.
From Lang Require Import
  Typecheck.

Extraction Language OCaml.
Extraction "extracted/Typecheck.ml" typecheck.
