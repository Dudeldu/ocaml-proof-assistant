# VSCode Extension - Ocaml Proofing Assistent

This extension is based on the formal proofing language for __OCaml__ as it was introduced in the lexture __Function Programming and Verification__ at TUM. Starting from a peace of code different rules are applied and by this transform the code in order to proof equivalence of expressions. Embedded into induction this ensembles a powerful toolkit for proofing equivalence of __OCaml__ expressions.

The rules:

* `(rule f)` - apply the definition of a function `f`
* `(rule fun)` - apply the rule for function application
* `(rule I.H.)` - apply an induction hypothesis
* `(rule match)` - select a branch in a match expression
* `(rule 'lemma X')` - apply a lemma X
>The following rules do also exist, however the assistent does not support them, as the intention behind the usage of those is hard to figure out for a machine in most cases
* `(rule let)` - expand a let defintion
* `(rule arith)` - simplify an arithmetic expression

## Features
This extension adds syntax highlighting and a general framework for proofs. However, the main support coming from its usage, is the auto completion of right hand sides. As soon as you typed in one of the following rules the extension suggests the transformed code. Basically, you only choose the rules, and the extension does the rest.  
It even allows adding additional auxiliary lemmas and supports there application as well.

```ocaml
let rec nlen n l = match l with [] -> 0
  | h::t -> n + nlen n t

let rec fold_left f a l = match l with [] -> a
  | h::t -> fold_left f (f a h) t

let rec map f l = match l with [] -> []
  | h::t -> f h :: map f t
```
Starting from the above source code one can proof the equivalence of the following statement just by applying the basic rules and some induction as framework as outlined here:
```proof
lemma 1: nlen n l <=> fold_left (+) 0 (map (fun _ -> n) l)
//#proof
induction on size of l:

== size l = 0:
== size l > 0:
//#qed
```
>A possible proof can be found in the _samples_ folder as well as an unproofen auxiliary lemma, which still requires some steps. This is a good point to start ;)

## Requirements

Install an *Ocaml* highlighting, so the input source code and the right-hand sides are highlighted correctly.

### Building

The extension requires the following `opam` packages:
 - vscode (can be installed via `opam pin add vscode https://github.com/ocamllabs/vscode-ocaml-platform.git`)
 - js_of_ocaml + (js_of_ocaml-ppx) (install via `opam install`)

The rest of the process is just the same as for [any other vscode extension in development](https://code.visualstudio.com/api).

## Limitations

 - only a very limited subset of ocaml is actually supported so far
 - the system can not _proof_ anything on it's own, although this could (naively) be added by exhaustively exploring all possibly applicable rules

**Enjoy!**
