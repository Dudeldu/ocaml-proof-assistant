open Rules
open Pprintast

type rule =
  | Nop
  | Match
  | Fun
  | Definition of string
  | RewriteRule of string * string
  | InductionHypothesis of string * string

let parse_string str =
  let buf = Lexing.from_string str in
  Location.init buf "<str>";
  let ast = Parse.implementation buf in
  ast

let to_string expr = String.trim (string_of_expression expr)

let extract_top_level_let_definition
    (statement_list : Parsetree.structure_item list) : Parsetree.expression =
  match (List.nth statement_list 0).pstr_desc with
  | Pstr_eval (expr, _) -> expr
  | _ -> failwith "no top level let definition"

let apply_rule (str : string) (r : rule) =
  match parse_string str with
  | { pstr_desc = Pstr_eval (expr, _); _ } :: _ -> (
      match r with
      | Nop -> to_string expr
      | Match -> to_string (apply_match_rule expr)
      | Fun -> to_string (apply_function_application_rule expr)
      | Definition def -> (
          match parse_string def with
          | { pstr_desc = Pstr_eval (definition, _); _ } :: _ -> (
              match parse_function_definition_rule definition with
              | Some (name, body) ->
                  to_string (apply_function_definition_rule (name, body) expr)
              | _ -> str)
          | _ -> str)
      | RewriteRule (pattern, replacement)
      | InductionHypothesis (pattern, replacement) -> (
          match (parse_string pattern, parse_string replacement) with
          | ( { pstr_desc = Pstr_eval (p, _); _ } :: _,
              { pstr_desc = Pstr_eval (r, _); _ } :: _ ) ->
              to_string (apply_arbitrary_rewrite_rule (p, r) expr)
          | _ -> str))
  | _ -> str

let apply_rules (str : string) (rules : rule list) =
  List.fold_left apply_rule str rules
