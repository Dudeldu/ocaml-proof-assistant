open Proofing.Proof
open Vscode
open Js_of_ocaml

let trim_function str =
  let trimmed =
    String.trim
      (Str.replace_first (Str.regexp "rec") ""
         (Str.replace_first (Str.regexp "let") "" str))
  in
  match String.split_on_char ' ' trimmed with [] | [ _ ] -> "" | fn :: _ -> fn

let index_opt str pattern =
  try Some (Str.search_forward pattern str 0) with Not_found -> None

let functionDefinition doc fn =
  let text = TextDocument.getText doc () in
  match
    ( index_opt text (Str.regexp "//#code"),
      index_opt text (Str.regexp "//#endcode") )
  with
  | Some b, Some e -> (
      let code_block = String.sub text (b + 8) (e - b - 8) in
      match
        List.find_opt
          (fun f -> trim_function f = fn)
          (Str.split (Str.regexp "\n\n") code_block)
      with
      | Some s -> s ^ " in 0"
      | _ -> "")
  | _ -> ""

let findLemma doc lemma =
  let text = TextDocument.getText doc () in
  match
    List.find_opt
      (fun s -> String.starts_with ~prefix:(lemma ^ ":") s)
      (String.split_on_char '\n' text)
  with
  | Some l -> (
      let trimmed =
        String.trim
          (String.sub l
             (String.length lemma + 1)
             (String.length l - (String.length lemma + 1)))
      in
      match Str.split (Str.regexp "<=>") trimmed with
      | [ lhs; rhs ] -> (lhs, rhs)
      | _ -> ("", ""))
  | _ -> ("", "")

let findCurrentScopeLemma doc position =
  let line =
    TextDocument.getText doc
      ~range:
        (Range.makePositions
           ~start:(Position.make ~line:0 ~character:0)
           ~end_:position)
      ()
  in
  match
    List.find_opt
      (fun s -> Str.string_match (Str.regexp "lemma [1-9][0-9]*:") s 0)
      (List.rev (String.split_on_char '\n' line))
  with
  | Some s -> (
      let index = String.index s ':' in
      let trimmed =
        String.trim (String.sub s (index + 1) (String.length s - (index + 1)))
      in
      match Str.split (Str.regexp "<=>") trimmed with
      | [ lhs; rhs ] -> (lhs, rhs)
      | _ -> ("", ""))
  | _ -> ("", "")

let extract_rule (line : string) =
  if String.starts_with ~prefix:"(rule fun)" line then Some Fun
  else if String.starts_with ~prefix:"(rule match)" line then Some Match
  else if String.starts_with ~prefix:"(rule I.H.)" line then
    Some (InductionHypothesis ("", ""))
  else if Str.string_match (Str.regexp "(rule \\([A-Za-z0-9_]+\\))") line 0 then
    Some (Definition (Str.matched_group 1 line))
  else if Str.string_match (Str.regexp "(rule '\\(lemma [1-9]\\)')") line 0 then
    Some (RewriteRule (Str.matched_group 1 line, ""))
  else None

let base_statement doc pos =
  let line =
    TextLine.text (TextDocument.lineAt doc ~line:(Position.line pos - 1))
  in
  match String.split_on_char '=' line with
  | [] | [ _ ] -> line
  | _ :: xs -> String.concat "=" xs

let ocamlCompletionItemProvider =
  object%js
    method provideCompletionItems (doc : TextDocument.t) (position : Position.t)
        (_ : CancellationToken.t) (_ : Js.Unsafe.any) =
      let line =
        TextDocument.getText doc
          ~range:
            (Range.makePositions
               ~start:
                 (Position.make ~line:(Position.line position) ~character:0)
               ~end_:position)
          ()
      in
      let rule =
        match extract_rule line with
        | Some Match -> Match
        | Some Fun -> Fun
        | Some (InductionHypothesis _) ->
            let lhs, rhs = findCurrentScopeLemma doc position in
            InductionHypothesis (lhs, rhs)
        | Some (Definition fn) -> Definition (functionDefinition doc fn)
        | Some (RewriteRule (lemma, _)) ->
            let lhs, rhs = findLemma doc lemma in
            RewriteRule (lhs, rhs)
        | _ -> Nop
      in
      if rule != Nop then
        let trimmed_suggestion =
          Str.global_replace (Str.regexp "\n") ""
            (apply_rule (base_statement doc position) rule)
        in
        let item =
          object%js
            val label =
              Js.string
                (if String.ends_with ~suffix:"=" line then
                 " " ^ trimmed_suggestion
                else trimmed_suggestion)
          end
        in
        Js.array (Array.of_list [ item ])
      else Js.array [||]
  end

let activate (_ : ExtensionContext.t) =
  let register =
    Js.Unsafe.global##.vscode##.languages##.registerCompletionItemProvider
  in
  Js.Unsafe.fun_call register
    [|
      Js.Unsafe.inject (Js.string "proof");
      Js.Unsafe.inject ocamlCompletionItemProvider;
    |]

let () = Js.export "activate" (Js.wrap_callback activate)
