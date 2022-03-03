let rec syntactic_match2 exprs pats =
  match (exprs, pats) with
  | [], [] -> Some []
  | e :: es, p :: ps -> (
      match (syntactic_match e p, syntactic_match2 es ps) with
      | Some a, Some b -> Some (List.rev_append a b)
      | _ -> None)
  | _ -> None

and syntactic_match (exp : Parsetree.expression) (case : Parsetree.pattern) =
  match (exp, case) with
  | _, { ppat_desc = Ppat_any; _ } -> Some []
  | _, { ppat_desc = Ppat_var s; _ } -> Some [ (Asttypes.Labelled s.txt, exp) ]
  | { pexp_desc = Pexp_constant c1; _ }, { ppat_desc = Ppat_constant c2; _ } ->
      if c1 = c2 then Some [] else None
  | { pexp_desc = Pexp_tuple l; _ }, { ppat_desc = Ppat_tuple r; _ } ->
      syntactic_match2 l r
  | ( { pexp_desc = Pexp_construct ({ txt = Lident c1; _ }, None); _ },
      { ppat_desc = Ppat_construct ({ txt = Lident c2; _ }, None); _ } ) ->
      if String.equal c1 c2 then Some [] else None
  | ( { pexp_desc = Pexp_construct ({ txt = Lident c1; _ }, Some e); _ },
      { ppat_desc = Ppat_construct ({ txt = Lident c2; _ }, Some (_, p)); _ } )
    ->
      if c1 = c2 then syntactic_match e p else None
  | _ -> None

let replace_arguments_in_expression expr args =
  let replacer =
    {
      Ast_mapper.default_mapper with
      expr =
        (fun mapper expr ->
          match expr with
          | { pexp_desc = Pexp_ident { txt = Lident n; _ }; _ } -> (
              match
                List.find_opt
                  (fun arg ->
                    match arg with
                    | Asttypes.Labelled name, _ -> n = name
                    | _ -> false)
                  args
              with
              | Some (Asttypes.Labelled _, e) -> e
              | _ -> expr)
          | other -> Ast_mapper.default_mapper.expr mapper other);
    }
  in
  replacer.expr replacer expr

let apply_match_rule (expression : Parsetree.expression) =
  let rec matching_case exp (cases : Parsetree.case list) =
    match cases with
    | [] -> None
    | c :: cs -> (
        match syntactic_match exp c.pc_lhs with
        | Some args -> Some (replace_arguments_in_expression c.pc_rhs args)
        | _ -> matching_case exp cs)
  in
  let mapper =
    {
      Ast_mapper.default_mapper with
      expr =
        (fun mapper expr ->
          match expr with
          | { pexp_desc = Pexp_match (exp, cases); _ } -> (
              match matching_case exp cases with Some e -> e | _ -> expr)
          | other -> Ast_mapper.default_mapper.expr mapper other);
    }
  in
  mapper.expr mapper expression

let parse_function_definition_rule (expression : Parsetree.expression) =
  match expression with
  | {
   pexp_desc =
     Pexp_let
       ( _,
         [
           {
             pvb_pat = { ppat_desc = Ppat_var { txt = name; _ }; _ };
             pvb_expr = body;
             _;
           };
         ],
         _ );
   _;
  } ->
      Some (name, body)
  | _ -> None

let rec fun_arg_to_var_mapping (expr : Parsetree.expression)
    (arguments : (Asttypes.arg_label * Parsetree.expression) list) =
  match (expr.pexp_desc, arguments) with
  | ( Parsetree.Pexp_fun
        ( Asttypes.Nolabel,
          _,
          { ppat_desc = Ppat_var { txt = variable; _ }; _ },
          e ),
      (_, a) :: args ) ->
      let e, acc, args_left = fun_arg_to_var_mapping e args in
      (e, (Asttypes.Labelled variable, a) :: acc, args_left)
  | ( Parsetree.Pexp_fun (Asttypes.Nolabel, _, { ppat_desc = Ppat_any; _ }, e),
      _ :: args ) ->
      let e, acc, args_left = fun_arg_to_var_mapping e args in
      (e, acc, args_left)
  | _ -> (expr, [], arguments)

let apply_arguments_to_anonymous_function expression arguments =
  let expr, mapping, args_left = fun_arg_to_var_mapping expression arguments in
  Ast_helper.Exp.apply (replace_arguments_in_expression expr mapping) args_left

let apply_function_definition_rule (function_name, function_body) expression =
  let mapper =
    {
      Ast_mapper.default_mapper with
      expr =
        (fun mapper expr ->
          match expr with
          | {
           pexp_desc =
             Pexp_apply
               ( { pexp_desc = Pexp_ident { txt = Lident name; _ }; _ },
                 arguments );
           _;
          } ->
              if name = function_name then
                apply_arguments_to_anonymous_function function_body arguments
              else Ast_mapper.default_mapper.expr mapper expr
          | other -> Ast_mapper.default_mapper.expr mapper other);
    }
  in
  mapper.expr mapper expression

let apply_function_application_rule (expression : Parsetree.expression) =
  let mapper =
    {
      Ast_mapper.default_mapper with
      expr =
        (fun mapper expr ->
          match expr with
          | { pexp_desc = Pexp_apply (fn, args); _ } ->
              apply_arguments_to_anonymous_function fn
                (List.map
                   (fun (l, e) -> (l, Ast_mapper.default_mapper.expr mapper e))
                   args)
          | other -> Ast_mapper.default_mapper.expr mapper other);
    }
  in
  mapper.expr mapper expression

let rec expression_list_is_matched patterns exprs =
  match (patterns, exprs) with
  | [], _ -> Some []
  | _, [] -> None
  | p :: ps, e :: exps -> (
      match expression_is_matched p e with
      | Some ls -> (
          match expression_list_is_matched ps exps with
          | Some lls -> Some (List.rev_append ls lls)
          | _ -> None)
      | _ -> None)

and expression_is_matched (pattern : Parsetree.expression)
    (expr : Parsetree.expression) :
    (Asttypes.arg_label * Parsetree.expression) list option =
  match (pattern.pexp_desc, expr.pexp_desc) with
  | Pexp_ident { txt = Lident name; _ }, _ ->
      Some [ (Asttypes.Labelled name, Ast_helper.Exp.mk expr.pexp_desc) ]
  | Pexp_construct (a, Some e1), Pexp_construct (b, Some e2) ->
      if a = b then expression_is_matched e1 e2 else None
  | Pexp_constant c1, Pexp_constant c2 -> if c1 = c2 then Some [] else None
  | ( Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident f1; _ }; _ }, args1),
      Pexp_apply ({ pexp_desc = Pexp_ident { txt = Lident f2; _ }; _ }, args2) )
    ->
      if f1 = f2 then
        expression_list_is_matched
          (List.map (fun (_, x) -> x) args1)
          (List.map (fun (_, a) -> a) args2)
      else None
  | Pexp_apply (body1, args1), Pexp_apply (body2, args2) -> (
      match
        ( expression_list_is_matched
            (List.map (fun (_, x) -> x) args1)
            (List.map (fun (_, a) -> a) args2),
          expression_is_matched body1 body2 )
      with
      | Some x, Some y -> Some (List.rev_append x y)
      | _ -> None)
  | Pexp_tuple exprs1, Pexp_tuple exprs2 ->
      expression_list_is_matched exprs1 exprs2
  | Pexp_match (expr1, cases1), Pexp_match (expr2, cases2) -> (
      match
        ( expression_list_is_matched
            (List.map (fun (x : Parsetree.case) -> x.pc_rhs) cases1)
            (List.map (fun (x : Parsetree.case) -> x.pc_rhs) cases2),
          expression_is_matched expr1 expr2 )
      with
      | Some x, Some y -> Some (List.rev_append x y)
      | _ -> None)
  | _ -> None

let apply_arbitrary_rewrite_rule (pattern, replacement) expression =
  let mapper =
    {
      Ast_mapper.default_mapper with
      expr =
        (fun mapper expr ->
          match expression_is_matched pattern expr with
          | Some args -> replace_arguments_in_expression replacement args
          | None -> Ast_mapper.default_mapper.expr mapper expr);
    }
  in
  mapper.expr mapper expression
