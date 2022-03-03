open Proofing.Proof
open Proofing.Rules
open OUnit2

let expect_string_equal str1 str2 test_context =
  let s1 = String.trim str1 in
  let s2 = String.trim str2 in
  assert_equal ~cmp:String.equal ~ctxt:test_context ~printer:(fun s -> s) s1 s2

let rule_match str1 str2 =
  expect_string_equal
    (to_string
       (apply_match_rule (extract_top_level_let_definition (parse_string str1))))
    str2

let rule_fun str1 str2 =
  expect_string_equal
    (to_string
       (apply_function_application_rule
          (extract_top_level_let_definition (parse_string str1))))
    str2

let rule_fn_def func_definition1 func_definition2 str1 str2 =
  match
    parse_function_definition_rule
      (extract_top_level_let_definition (parse_string func_definition1))
  with
  | Some (name, body) ->
      fun test_context ->
        let s1 = String.trim (to_string body) in
        let s2 = String.trim func_definition2 in
        let s3 =
          String.trim
            (to_string
               (apply_function_definition_rule (name, body)
                  (extract_top_level_let_definition (parse_string str1))))
        in
        assert_equal ~cmp:String.equal ~ctxt:test_context
          ~printer:(fun s -> "\"" ^ s ^ "\"")
          s1 s2;
        assert_equal ~cmp:String.equal ~ctxt:test_context
          ~printer:(fun s -> "\"" ^ s ^ "\"")
          s3 (String.trim str2)
  | _ -> failwith "invalid function definition"

let rule_rewrite pattern replacement str1 str2 =
  let p = extract_top_level_let_definition (parse_string pattern) in
  let r = extract_top_level_let_definition (parse_string replacement) in
  let e = extract_top_level_let_definition (parse_string str1) in
  expect_string_equal (to_string (apply_arbitrary_rewrite_rule (p, r) e)) str2

let match_rule_suite =
  "rule match"
  >::: [
         "constant" >:: rule_match "match 2 with 2 -> 1" "1";
         "wildcard" >:: rule_match "match x::xs with [] -> 0 | _ -> 1" "1";
         "empty list" >:: rule_match "match [] with [] -> 0 | x::xs -> 1" "0";
         "list" >:: rule_match "match x::xs with [] -> 0 | x::xs -> 1" "1";
         "tuple"
         >:: rule_match "match (x, y)::zz with [] -> 0 | (x, y)::zz -> 1" "1";
         "list - translate idents"
         >:: rule_match "match x::xs with [] -> 0 | h::t -> 1" "1";
         "list - construct"
         >:: rule_match "match x::xs with [] -> 0 | h::t -> h::t" "x :: xs";
         "list - top wildcard"
         >:: rule_match "match x::xs with [] -> 0 | _::t -> t" "xs";
         "list - base wildcard"
         >:: rule_match "match x::xs with [] -> 0 | h::_ -> fun a -> h::[]"
               "fun a -> [x]";
         "tuple - wildcards" >:: rule_match "match (1, 2) with _, _ -> 1" "1";
         "tuple - constants" >:: rule_match "match (1, 2) with 1, 2 -> 1" "1";
       ]

let fn_def_rule_suite =
  "rule function definition"
  >::: [
         "one arg" >:: rule_fn_def "let add x = x in 0" "fun x -> x" "add 1" "1";
         "two args"
         >:: rule_fn_def "let add x y = x + y in 0" "fun x -> fun y -> x + y"
               "add 1 2" "(1 + 2)";
         "advanced 1"
         >:: rule_fn_def
               "let rec map f arr = match arr with [] -> [] | x::xs -> (f \
                x)::map xs   in 0"
               "fun f -> fun arr -> match arr with | [] -> [] | x::xs -> (f x) \
                :: (map xs)"
               "map (fun x -> x + 1) []"
               "(match [] with | [] -> [] | x::xs -> (((fun x -> x + 1)) x) :: \
                (map xs))";
         "advanced 2"
         >:: rule_fn_def
               "let rec map f l = match l with [] -> []  | h::t -> f h :: map \
                f t in 0"
               "fun f -> fun l -> match l with | [] -> [] | h::t -> (f h) :: \
                (map f t)"
               "map f (h :: t)"
               "(match h :: t with | [] -> [] | h::t -> (f h) :: (map f t))";
         "advanced 3"
         >:: expect_string_equal
               (apply_rule "add 1 2" (Definition "let add x y = x + y in 0"))
               "(1 + 2)";
       ]

let fun_rule_suite =
  "rule fun"
  >::: [
         "constant arg" >:: rule_fun "(fun x -> x + 1) 2" "(2 + 1)";
         "wildcard arg" >:: rule_fun "(fun _ -> 1) 2" "1";
         "ident arg"
         >:: rule_fun "(fun x -> fun y -> x + y) z" "(fun y -> z + y)";
         "many args" >:: rule_fun "(fun x -> x + 1) z l k" "(z + 1) l k";
         "expression arg"
         >:: rule_fun "(fun x -> fun y -> x + 1) (y + 3) x" "((y + 3) + 1)";
         "advanced 1"
         >:: rule_fun
               "fold_left (+) 0 (((fun _ -> n) l) :: (map (fun _ -> n) ls))"
               "fold_left (+) 0 ((n ) :: (map (fun _ -> n) ls))";
       ]

let arbitrary_rewrite_rule_suite =
  "arbitrary rewrite rule"
  >::: [
         "rule chaining"
         >:: expect_string_equal
               (apply_rules "map (fun x -> x + 1) []"
                  [
                    Definition
                      "let rec map f arr = match arr with [] -> [] | x::xs -> \
                       (f x)::map xs   in 0";
                    Match;
                  ])
               "[]";
         "binary operator add"
         >:: rule_rewrite "add a b" "a + b" "add 1 2" "1 + 2";
         "binary list constructor"
         >:: rule_rewrite "con a b" "a :: b" "con 1 2" "1 :: 2";
         "list constructor with subexpression"
         >:: rule_rewrite "con a b" "a :: b" "con (x::xs) 2" "(x :: xs) :: 2";
       ]

let () =
  run_test_tt_main match_rule_suite;
  run_test_tt_main fn_def_rule_suite;
  run_test_tt_main fun_rule_suite;
  run_test_tt_main arbitrary_rewrite_rule_suite
