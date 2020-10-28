[@@@ocaml.warning "-32"]

(*
 * Copyright (c) 2016 Thomas Refis <trefis@janestreet.com>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Odoc_model.Names
module Location = Odoc_model.Location_
module Paths = Odoc_model.Paths
open Types
module O = Codefmt
open O.Infix

(* TODO: Title formatting should be a renderer decision *)
let format_title kind name =
  let mk title =
    let level = 0 and label = None in
    [ Item.Heading { level; label; title } ]
  in
  let prefix s = mk (inline (Text (s ^ " ")) :: O.code (O.txt name)) in
  match kind with
  | `Mod -> prefix "Module"
  | `Arg -> prefix "Parameter"
  | `Mty -> prefix "Module type"
  | `Cty -> prefix "Class type"
  | `Class -> prefix "Class"
  | `Page -> mk [ inline @@ Text name ]

let make_name_from_path { Url.Path.name; parent; _ } =
  match parent with
  | None -> name
  | Some p -> Printf.sprintf "%s.%s" p.name name

let label t ppf =
  match t with
  | Odoc_model.Lang.TypeExpr.Label s -> O.pf ppf "%s" s
  | Optional s -> O.pf ppf "?%t%s" (O.entity "#8288") s

let tag tag t ppf = O.pf ppf "@{<%s>%t@}" tag t

let type_var tv = tag "type-var" (O.txt tv)

let enclose ~l ~r x = O.span (fun ppf -> O.pf ppf "%s%t%s" l x r)

let path p txt =
  !O.elt
    [ inline @@ InternalLink (InternalLink.Resolved (Url.from_path p, txt)) ]

let resolved p txt =
  !O.elt [ inline @@ InternalLink (InternalLink.Resolved (p, txt)) ]

let unresolved txt =
  !O.elt [ inline @@ InternalLink (InternalLink.Unresolved txt) ]

let path_to_id path =
  match Url.Anchor.from_identifier (path :> Paths.Identifier.t) with
  | Error _ -> None
  | Ok url -> Some url

let attach_expansion ?(status = `Default) (eq, o, e) page text =
  match page with
  | None -> O.documentedSrc text
  | Some (page : Page.t) ->
      let url = page.url in
      let summary = O.render text in
      let expansion =
        O.documentedSrc (O.txt eq ++ O.keyword o)
        @ DocumentedSrc.[ Subpage { status; content = page } ]
        @ O.documentedSrc (O.keyword e)
      in
      DocumentedSrc.
        [ Alternative (Expansion { summary; url; status; expansion }) ]

include Generator_signatures

module Make (Syntax1 : SYNTAX) (Syntax2 : SYNTAX) = struct
  module Link : sig
    val from_path : Paths.Path.t -> text

    val from_fragment :
      base:Paths.Identifier.Signature.t -> Paths.Fragment.t -> text

    val render_fragment : Paths.Fragment.t -> string
  end = struct
    open Paths

    let rec from_path : Path.t -> text =
     fun path ->
      match path with
      | `Identifier (id, _) ->
          unresolved [ inline @@ Text (Identifier.name id) ]
      | `Root root -> unresolved [ inline @@ Text root ]
      | `Forward root -> unresolved [ inline @@ Text root ] (* FIXME *)
      | `Dot (prefix, suffix) ->
          let link = from_path (prefix :> Path.t) in
          link ++ O.txt ("." ^ suffix)
      | `Apply (p1, p2) ->
          let link1 = from_path (p1 :> Path.t) in
          let link2 = from_path (p2 :> Path.t) in
          link1 ++ O.txt "(" ++ link2 ++ O.txt ")"
      | `Resolved _ when Paths.Path.is_hidden path ->
          let txt = Url.render_path path in
          Format.eprintf "Warning, resolved hidden path: %s\n%!" txt;
          unresolved [ inline @@ Text txt ]
      | `Resolved rp -> (
          (* If the path is pointing to an opaque module or module type
             there won't be a page generated - so we stop before; at
             the parent page, and link instead to the anchor representing
             the declaration of the opaque module(_type) *)
          let stop_before =
            match rp with
            | `OpaqueModule _ | `OpaqueModuleType _ -> true
            | _ -> false
          in
          let id = Paths.Path.Resolved.identifier rp in
          let txt = Url.render_path path in
          match Url.from_identifier ~stop_before id with
          | Ok href -> resolved href [ inline @@ Text txt ]
          | Error (Url.Error.Not_linkable _) -> O.txt txt
          | Error exn ->
              Printf.eprintf "Id.href failed: %S\n%!" (Url.Error.to_string exn);
              O.txt txt )

    let dot prefix suffix =
      match prefix with "" -> suffix | _ -> prefix ^ "." ^ suffix

    let rec render_fragment : Fragment.t -> string =
     fun fragment ->
      match fragment with
      | `Resolved rr -> render_resolved_fragment rr
      | `Dot (prefix, suffix) ->
          dot (render_fragment (prefix :> Fragment.t)) suffix
      | `Root -> ""

    and render_resolved_fragment : Fragment.Resolved.t -> string =
      let open Fragment.Resolved in
      fun fragment ->
        match fragment with
        | `Root _ -> ""
        | `Subst (_, rr) -> render_resolved_fragment (rr :> t)
        | `SubstAlias (_, rr) -> render_resolved_fragment (rr :> t)
        | `Module (rr, s) ->
            dot (render_resolved_fragment (rr :> t)) (ModuleName.to_string s)
        | `Type (rr, s) ->
            dot (render_resolved_fragment (rr :> t)) (TypeName.to_string s)
        | `Class (rr, s) ->
            dot (render_resolved_fragment (rr :> t)) (ClassName.to_string s)
        | `ClassType (rr, s) ->
            dot (render_resolved_fragment (rr :> t)) (ClassTypeName.to_string s)
        | `OpaqueModule r -> render_resolved_fragment (r :> t)

    let rec fragment_to_ir :
        stop_before:bool -> base:Identifier.Signature.t -> Fragment.t -> text =
     fun ~stop_before ~base fragment ->
      let open Fragment in
      match fragment with
      | `Root | `Resolved (`Root _) -> (
          let id = (base :> Identifier.t) in
          match Url.from_identifier ~stop_before:true id with
          | Ok href -> resolved href [ inline @@ Text (Identifier.name id) ]
          | Error (Not_linkable _) ->
              unresolved [ inline @@ Text (Identifier.name id) ]
          | Error exn ->
              Printf.eprintf "[FRAG] Id.href failed: %S\n%!"
                (Url.Error.to_string exn);
              unresolved [ inline @@ Text (Identifier.name id) ] )
      | `Resolved rr -> (
          let id = Resolved.identifier (rr :> Resolved.t) in
          let txt = render_resolved_fragment rr in
          match Url.from_identifier ~stop_before id with
          | Ok href -> resolved href [ inline @@ Text txt ]
          | Error (Not_linkable _) -> unresolved [ inline @@ Text txt ]
          | Error exn ->
              Printf.eprintf "[FRAG] Id.href failed: %S\n%!"
                (Url.Error.to_string exn);
              unresolved [ inline @@ Text txt ] )
      | `Dot (prefix, suffix) ->
          let link =
            fragment_to_ir ~stop_before:true ~base (prefix :> Fragment.t)
          in
          link ++ O.txt ("." ^ suffix)

    let from_fragment = fragment_to_ir ~stop_before:false
  end

  module Type_expression : sig
    val type_expr1 : ?needs_parentheses:bool -> Lang.TypeExpr.t -> text

    val type_expr2 : ?needs_parentheses:bool -> Lang.TypeExpr.t -> text

    val format_type_path1 :
      delim:[ `parens | `brackets ] -> Lang.TypeExpr.t list -> text -> text

    val format_type_path2 :
      delim:[ `parens | `brackets ] -> Lang.TypeExpr.t list -> text -> text
  end = struct
    let rec te_variant1 (t : Odoc_model.Lang.TypeExpr.Polymorphic_variant.t) =
      let style_arguments ~constant arguments =
        (* Multiple arguments in a polymorphic variant constructor correspond
           to a conjunction of types, not a product: [`Lbl int&float].
           If constant is [true], the conjunction starts with an empty type,
           for instance [`Lbl &int].
        *)
        let wrapped_type_expr =
          (* type conjunction in Reason is printed as `Lbl (t1)&(t2)` *)
          if Syntax1.Type.Variant.parenthesize_params then fun x ->
            O.span (O.txt "(" ++ type_expr1 x ++ O.txt ")")
          else fun x -> type_expr1 x
        in
        let arguments =
          O.list arguments ~sep:(O.txt " & ") ~f:wrapped_type_expr
        in
        if constant then O.txt "& " ++ arguments else arguments
      in
      let rec style_elements ~add_pipe = function
        | [] -> O.noop
        | first :: rest ->
            let first =
              match first with
              | Odoc_model.Lang.TypeExpr.Polymorphic_variant.Type te ->
                  let res = type_expr1 te in
                  if add_pipe then O.txt " " ++ O.span (O.txt "| " ++ res)
                  else res
              | Constructor { constant; name; arguments; _ } ->
                  let constr =
                    let name = "`" ^ name in
                    if add_pipe then O.span (O.txt ("| " ^ name))
                    else O.txt name
                  in
                  let res =
                    match arguments with
                    | [] -> constr
                    | _ ->
                        let arguments = style_arguments ~constant arguments in
                        O.span
                          ( if Syntax1.Type.Variant.parenthesize_params then
                            constr ++ arguments
                          else constr ++ O.txt " of " ++ arguments )
                  in
                  if add_pipe then O.txt " " ++ res else res
            in
            first ++ style_elements ~add_pipe:true rest
      in
      let elements = style_elements ~add_pipe:false t.elements in
      O.span
        ( match t.kind with
        | Fixed -> O.txt "[ " ++ elements ++ O.txt " ]"
        | Open -> O.txt "[> " ++ elements ++ O.txt " ]"
        | Closed [] -> O.txt "[< " ++ elements ++ O.txt " ]"
        | Closed lst ->
            let constrs = String.concat " " lst in
            O.txt "[< " ++ elements ++ O.txt (" " ^ constrs ^ " ]") )

    and te_variant2 (t : Odoc_model.Lang.TypeExpr.Polymorphic_variant.t) =
      let style_arguments ~constant arguments =
        (* Multiple arguments in a polymorphic variant constructor correspond
           to a conjunction of types, not a product: [`Lbl int&float].
           If constant is [true], the conjunction starts with an empty type,
           for instance [`Lbl &int].
        *)
        let wrapped_type_expr =
          (* type conjunction in Reason is printed as `Lbl (t1)&(t2)` *)
          if Syntax2.Type.Variant.parenthesize_params then fun x ->
            O.span (O.txt "(" ++ type_expr2 x ++ O.txt ")")
          else fun x -> type_expr2 x
        in
        let arguments =
          O.list arguments ~sep:(O.txt " & ") ~f:wrapped_type_expr
        in
        if constant then O.txt "& " ++ arguments else arguments
      in
      let rec style_elements ~add_pipe = function
        | [] -> O.noop
        | first :: rest ->
            let first =
              match first with
              | Odoc_model.Lang.TypeExpr.Polymorphic_variant.Type te ->
                  let res = type_expr2 te in
                  if add_pipe then O.txt " " ++ O.span (O.txt "| " ++ res)
                  else res
              | Constructor { constant; name; arguments; _ } ->
                  let constr =
                    let name = "`" ^ name in
                    if add_pipe then O.span (O.txt ("| " ^ name))
                    else O.txt name
                  in
                  let res =
                    match arguments with
                    | [] -> constr
                    | _ ->
                        let arguments = style_arguments ~constant arguments in
                        O.span
                          ( if Syntax2.Type.Variant.parenthesize_params then
                            constr ++ arguments
                          else constr ++ O.txt " of " ++ arguments )
                  in
                  if add_pipe then O.txt " " ++ res else res
            in
            first ++ style_elements ~add_pipe:true rest
      in
      let elements = style_elements ~add_pipe:false t.elements in
      O.span
        ( match t.kind with
        | Fixed -> O.txt "[ " ++ elements ++ O.txt " ]"
        | Open -> O.txt "[> " ++ elements ++ O.txt " ]"
        | Closed [] -> O.txt "[< " ++ elements ++ O.txt " ]"
        | Closed lst ->
            let constrs = String.concat " " lst in
            O.txt "[< " ++ elements ++ O.txt (" " ^ constrs ^ " ]") )

    and te_object1 (t : Odoc_model.Lang.TypeExpr.Object.t) =
      let fields =
        O.list t.fields ~f:(function
          | Odoc_model.Lang.TypeExpr.Object.Method { name; type_ } ->
              O.txt (name ^ Syntax1.Type.annotation_separator)
              ++ type_expr1 type_
              ++ O.txt Syntax1.Obj.field_separator
          | Inherit type_ ->
              type_expr1 type_ ++ O.txt Syntax1.Obj.field_separator)
      in
      let open_tag =
        if t.open_ then O.txt Syntax1.Obj.open_tag_extendable
        else O.txt Syntax1.Obj.open_tag_closed
      in
      let close_tag =
        if t.open_ then O.txt Syntax1.Obj.close_tag_extendable
        else O.txt Syntax1.Obj.close_tag_closed
      in
      open_tag ++ fields ++ close_tag

    and te_object2 (t : Odoc_model.Lang.TypeExpr.Object.t) =
      let fields =
        O.list t.fields ~f:(function
          | Odoc_model.Lang.TypeExpr.Object.Method { name; type_ } ->
              O.txt (name ^ Syntax2.Type.annotation_separator)
              ++ type_expr2 type_
              ++ O.txt Syntax2.Obj.field_separator
          | Inherit type_ ->
              type_expr2 type_ ++ O.txt Syntax2.Obj.field_separator)
      in
      let open_tag =
        if t.open_ then O.txt Syntax2.Obj.open_tag_extendable
        else O.txt Syntax2.Obj.open_tag_closed
      in
      let close_tag =
        if t.open_ then O.txt Syntax2.Obj.close_tag_extendable
        else O.txt Syntax2.Obj.close_tag_closed
      in
      open_tag ++ fields ++ close_tag

    and format_type_path1 ~delim (params : Odoc_model.Lang.TypeExpr.t list)
        (path : text) : text =
      match params with
      | [] -> path
      | [ param ] ->
          let param = type_expr1 ~needs_parentheses:true param in
          let args =
            if Syntax1.Type.parenthesize_constructor then
              O.txt "(" ++ param ++ O.txt ")"
            else param
          in
          Syntax1.Type.handle_constructor_params path args
      | params ->
          let params = O.list params ~sep:(O.txt ",\194\160") ~f:type_expr1 in
          let params =
            match delim with
            | `parens -> enclose ~l:"(" params ~r:")"
            | `brackets -> enclose ~l:"[" params ~r:"]"
          in
          Syntax1.Type.handle_constructor_params path params

    and format_type_path2 ~delim (params : Odoc_model.Lang.TypeExpr.t list)
        (path : text) : text =
      match params with
      | [] -> path
      | [ param ] ->
          let param = type_expr2 ~needs_parentheses:true param in
          let args =
            if Syntax2.Type.parenthesize_constructor then
              O.txt "(" ++ param ++ O.txt ")"
            else param
          in
          Syntax2.Type.handle_constructor_params path args
      | params ->
          let params = O.list params ~sep:(O.txt ",\194\160") ~f:type_expr2 in
          let params =
            match delim with
            | `parens -> enclose ~l:"(" params ~r:")"
            | `brackets -> enclose ~l:"[" params ~r:"]"
          in
          Syntax2.Type.handle_constructor_params path params

    and type_expr1 ?(needs_parentheses = false) (t : Odoc_model.Lang.TypeExpr.t)
        =
      match t with
      | Var s -> type_var (Syntax1.Type.var_prefix ^ s)
      | Any -> type_var Syntax1.Type.any
      | Alias (te, alias) ->
          type_expr1 ~needs_parentheses:true te
          ++ O.txt " " ++ O.keyword "as" ++ O.txt " '" ++ O.txt alias
      | Arrow (None, src, dst) ->
          let res =
            type_expr1 ~needs_parentheses:true src
            ++ O.txt " " ++ Syntax1.Type.arrow ++ O.txt " " ++ type_expr1 dst
          in
          if not needs_parentheses then res else enclose ~l:"(" res ~r:")"
      | Arrow (Some lbl, src, dst) ->
          let res =
            O.span
              (label lbl ++ O.txt ":" ++ type_expr1 ~needs_parentheses:true src)
            ++ O.txt " " ++ Syntax1.Type.arrow ++ O.txt " " ++ type_expr1 dst
          in
          if not needs_parentheses then res else enclose ~l:"(" res ~r:")"
      | Tuple lst ->
          let res =
            O.list lst
              ~sep:(O.txt Syntax1.Type.Tuple.element_separator)
              ~f:(type_expr1 ~needs_parentheses:true)
          in
          if Syntax1.Type.Tuple.always_parenthesize || needs_parentheses then
            enclose ~l:"(" res ~r:")"
          else res
      | Constr (path, args) ->
          let link = Link.from_path (path :> Paths.Path.t) in
          format_type_path1 ~delim:`parens args link
      | Polymorphic_variant v -> te_variant1 v
      | Object o -> te_object1 o
      | Class (path, args) ->
          format_type_path1 ~delim:`brackets args
            (Link.from_path (path :> Paths.Path.t))
      | Poly (polyvars, t) ->
          O.txt (String.concat " " polyvars ^ ". ") ++ type_expr1 t
      | Package pkg ->
          enclose ~l:"(" ~r:")"
            ( O.keyword "module" ++ O.txt " "
            ++ Link.from_path (pkg.path :> Paths.Path.t)
            ++
            match pkg.substitutions with
            | [] -> O.noop
            | lst ->
                O.txt " " ++ O.keyword "with" ++ O.txt " "
                ++ O.list
                     ~sep:(O.txt " " ++ O.keyword "and" ++ O.txt " ")
                     lst ~f:(package_subst1 pkg.path) )

    and type_expr2 ?(needs_parentheses = false) (t : Odoc_model.Lang.TypeExpr.t)
        =
      match t with
      | Var s -> type_var (Syntax2.Type.var_prefix ^ s)
      | Any -> type_var Syntax2.Type.any
      | Alias (te, alias) ->
          type_expr2 ~needs_parentheses:true te
          ++ O.txt " " ++ O.keyword "as" ++ O.txt " '" ++ O.txt alias
      | Arrow (None, src, dst) ->
          let res =
            type_expr2 ~needs_parentheses:true src
            ++ O.txt " " ++ Syntax2.Type.arrow ++ O.txt " " ++ type_expr2 dst
          in
          if not needs_parentheses then res else enclose ~l:"(" res ~r:")"
      | Arrow (Some lbl, src, dst) ->
          let res =
            O.span
              (label lbl ++ O.txt ":" ++ type_expr2 ~needs_parentheses:true src)
            ++ O.txt " " ++ Syntax2.Type.arrow ++ O.txt " " ++ type_expr2 dst
          in
          if not needs_parentheses then res else enclose ~l:"(" res ~r:")"
      | Tuple lst ->
          let res =
            O.list lst
              ~sep:(O.txt Syntax2.Type.Tuple.element_separator)
              ~f:(type_expr2 ~needs_parentheses:true)
          in
          if Syntax2.Type.Tuple.always_parenthesize || needs_parentheses then
            enclose ~l:"(" res ~r:")"
          else res
      | Constr (path, args) ->
          let link = Link.from_path (path :> Paths.Path.t) in
          format_type_path2 ~delim:`parens args link
      | Polymorphic_variant v -> te_variant2 v
      | Object o -> te_object2 o
      | Class (path, args) ->
          format_type_path2 ~delim:`brackets args
            (Link.from_path (path :> Paths.Path.t))
      | Poly (polyvars, t) ->
          O.txt (String.concat " " polyvars ^ ". ") ++ type_expr2 t
      | Package pkg ->
          enclose ~l:"(" ~r:")"
            ( O.keyword "module" ++ O.txt " "
            ++ Link.from_path (pkg.path :> Paths.Path.t)
            ++
            match pkg.substitutions with
            | [] -> O.noop
            | lst ->
                O.txt " " ++ O.keyword "with" ++ O.txt " "
                ++ O.list
                     ~sep:(O.txt " " ++ O.keyword "and" ++ O.txt " ")
                     lst ~f:(package_subst2 pkg.path) )

    and package_subst1 (pkg_path : Paths.Path.ModuleType.t)
        ((frag_typ, te) : Paths.Fragment.Type.t * Odoc_model.Lang.TypeExpr.t) :
        text =
      let typath =
        match pkg_path with
        | `Resolved rp ->
            let base =
              ( Paths.Path.Resolved.ModuleType.identifier rp
                :> Paths.Identifier.Signature.t )
            in
            Link.from_fragment ~base (frag_typ :> Paths.Fragment.t)
        | _ -> O.txt (Link.render_fragment (frag_typ :> Paths.Fragment.t))
      in
      O.keyword "type" ++ O.txt " " ++ typath ++ O.txt " = " ++ type_expr1 te

    and package_subst2 (pkg_path : Paths.Path.ModuleType.t)
        ((frag_typ, te) : Paths.Fragment.Type.t * Odoc_model.Lang.TypeExpr.t) :
        text =
      let typath =
        match pkg_path with
        | `Resolved rp ->
            let base =
              ( Paths.Path.Resolved.ModuleType.identifier rp
                :> Paths.Identifier.Signature.t )
            in
            Link.from_fragment ~base (frag_typ :> Paths.Fragment.t)
        | _ -> O.txt (Link.render_fragment (frag_typ :> Paths.Fragment.t))
      in
      O.keyword "type" ++ O.txt " " ++ typath ++ O.txt " = " ++ type_expr2 te
  end

  open Type_expression

  (* Also handles constructor declarations for exceptions and extensible
     variants, and exposes a few helpers used in formatting classes and signature
     constraints. *)
  module Type_declaration : sig
    val type_decl :
      ?is_substitution:bool ->
      Lang.Signature.recursive * Lang.TypeDecl.t ->
      Item.t

    val extension1 : Lang.Extension.t -> Item.t

    val extension2 : Lang.Extension.t -> Item.t

    val exn1 : Lang.Exception.t -> Item.t

    val exn2 : Lang.Exception.t -> Item.t

    val format_params1 :
      ?delim:[ `parens | `brackets ] -> Lang.TypeDecl.param list -> text

    val format_params2 :
      ?delim:[ `parens | `brackets ] -> Lang.TypeDecl.param list -> text

    val format_manifest1 :
      ?is_substitution:bool ->
      ?compact_variants:bool ->
      Lang.TypeDecl.Equation.t ->
      text * bool

    val format_manifest2 :
      ?is_substitution:bool ->
      ?compact_variants:bool ->
      Lang.TypeDecl.Equation.t ->
      text * bool

    val format_constraints1 : (Lang.TypeExpr.t * Lang.TypeExpr.t) list -> text

    val format_constraints2 : (Lang.TypeExpr.t * Lang.TypeExpr.t) list -> text
  end = struct
    let record1 fields =
      let field mutable_ id typ =
        match Url.from_identifier ~stop_before:true id with
        | Error e -> failwith (Url.Error.to_string e)
        | Ok url ->
            let name = Paths.Identifier.name id in
            let attrs = [ "def"; "record"; url.kind ] in
            let cell =
              (* O.td ~a:[ O.a_class ["def"; kind ] ]
               *   [O.a ~a:[O.a_href ("#" ^ anchor); O.a_class ["anchor"]] []
               *   ; *)
              O.code
                ( (if mutable_ then O.keyword "mutable" ++ O.txt " " else O.noop)
                ++ O.txt name
                ++ O.txt Syntax1.Type.annotation_separator
                ++ type_expr1 typ
                ++ O.txt Syntax1.Type.Record.field_separator )
              (* ] *)
            in
            (url, attrs, cell)
      in
      let rows =
        fields
        |> List.map (fun fld ->
               let open Odoc_model.Lang.TypeDecl.Field in
               let url, attrs, code =
                 field fld.mutable_ (fld.id :> Paths.Identifier.t) fld.type_
               in
               let anchor = Some url in
               let rhs = Comment.to_ir fld.doc in
               let doc = if not (Comment.has_doc fld.doc) then [] else rhs in
               DocumentedSrc.Documented { anchor; attrs; code; doc })
      in
      let content =
        O.documentedSrc (O.txt "{") @ rows @ O.documentedSrc (O.txt "}")
      in
      content

    let record2 fields =
      let field mutable_ id typ =
        match Url.from_identifier ~stop_before:true id with
        | Error e -> failwith (Url.Error.to_string e)
        | Ok url ->
            let name = Paths.Identifier.name id in
            let attrs = [ "def"; "record"; url.kind ] in
            let cell =
              (* O.td ~a:[ O.a_class ["def"; kind ] ]
               *   [O.a ~a:[O.a_href ("#" ^ anchor); O.a_class ["anchor"]] []
               *   ; *)
              O.code
                ( (if mutable_ then O.keyword "mutable" ++ O.txt " " else O.noop)
                ++ O.txt name
                ++ O.txt Syntax2.Type.annotation_separator
                ++ type_expr2 typ
                ++ O.txt Syntax2.Type.Record.field_separator )
              (* ] *)
            in
            (url, attrs, cell)
      in
      let rows =
        fields
        |> List.map (fun fld ->
               let open Odoc_model.Lang.TypeDecl.Field in
               let url, attrs, code =
                 field fld.mutable_ (fld.id :> Paths.Identifier.t) fld.type_
               in
               let anchor = Some url in
               let rhs = Comment.to_ir fld.doc in
               let doc = if not (Comment.has_doc fld.doc) then [] else rhs in
               DocumentedSrc.Documented { anchor; attrs; code; doc })
      in
      let content =
        O.documentedSrc (O.txt "{") @ rows @ O.documentedSrc (O.txt "}")
      in
      content

    let constructor1 :
        Paths.Identifier.t ->
        Odoc_model.Lang.TypeDecl.Constructor.argument ->
        Odoc_model.Lang.TypeExpr.t option ->
        DocumentedSrc.t =
     fun id args ret_type ->
      let name = Paths.Identifier.name id in
      let kind = Url.kind id in
      let cstr = tag kind (O.txt name) in
      let is_gadt, ret_type =
        match ret_type with
        | None -> (false, O.noop)
        | Some te ->
            let constant = match args with Tuple [] -> true | _ -> false in
            let ret_type =
              O.txt " "
              ++ (if constant then O.txt ":" else Syntax1.Type.GADT.arrow)
              ++ O.txt " " ++ type_expr1 te
            in
            (true, ret_type)
      in
      match args with
      | Tuple [] -> O.documentedSrc (cstr ++ ret_type)
      | Tuple lst ->
          let params =
            O.list lst
              ~sep:(O.txt Syntax1.Type.Tuple.element_separator)
              ~f:(type_expr1 ~needs_parentheses:is_gadt)
          in
          O.documentedSrc
            ( cstr
            ++ ( if Syntax1.Type.Variant.parenthesize_params then
                 O.txt "(" ++ params ++ O.txt ")"
               else
                 ( if is_gadt then O.txt Syntax1.Type.annotation_separator
                 else O.txt " " ++ O.keyword "of" ++ O.txt " " )
                 ++ params )
            ++ ret_type )
      | Record fields ->
          if is_gadt then
            O.documentedSrc (cstr ++ O.txt Syntax1.Type.annotation_separator)
            @ record1 fields @ O.documentedSrc ret_type
          else
            O.documentedSrc (cstr ++ O.txt " " ++ O.keyword "of" ++ O.txt " ")
            @ record1 fields

    let constructor2 :
        Paths.Identifier.t ->
        Odoc_model.Lang.TypeDecl.Constructor.argument ->
        Odoc_model.Lang.TypeExpr.t option ->
        DocumentedSrc.t =
     fun id args ret_type ->
      let name = Paths.Identifier.name id in
      let kind = Url.kind id in
      let cstr = tag kind (O.txt name) in
      let is_gadt, ret_type =
        match ret_type with
        | None -> (false, O.noop)
        | Some te ->
            let constant = match args with Tuple [] -> true | _ -> false in
            let ret_type =
              O.txt " "
              ++ (if constant then O.txt ":" else Syntax2.Type.GADT.arrow)
              ++ O.txt " " ++ type_expr2 te
            in
            (true, ret_type)
      in
      match args with
      | Tuple [] -> O.documentedSrc (cstr ++ ret_type)
      | Tuple lst ->
          let params =
            O.list lst
              ~sep:(O.txt Syntax2.Type.Tuple.element_separator)
              ~f:(type_expr2 ~needs_parentheses:is_gadt)
          in
          O.documentedSrc
            ( cstr
            ++ ( if Syntax2.Type.Variant.parenthesize_params then
                 O.txt "(" ++ params ++ O.txt ")"
               else
                 ( if is_gadt then O.txt Syntax2.Type.annotation_separator
                 else O.txt " " ++ O.keyword "of" ++ O.txt " " )
                 ++ params )
            ++ ret_type )
      | Record fields ->
          if is_gadt then
            O.documentedSrc (cstr ++ O.txt Syntax2.Type.annotation_separator)
            @ record2 fields @ O.documentedSrc ret_type
          else
            O.documentedSrc (cstr ++ O.txt " " ++ O.keyword "of" ++ O.txt " ")
            @ record2 fields

    let variant1 cstrs : DocumentedSrc.t =
      let constructor id args res =
        match Url.from_identifier ~stop_before:true id with
        | Error e -> failwith (Url.Error.to_string e)
        | Ok url ->
            let attrs = [ "def"; "variant"; url.kind ] in
            let content =
              let doc = constructor1 id args res in
              O.documentedSrc (O.txt "| ") @ doc
            in
            (url, attrs, content)
      in
      match cstrs with
      | [] -> O.documentedSrc (O.txt "|")
      | _ :: _ ->
          let rows =
            cstrs
            |> List.map (fun cstr ->
                   let open Odoc_model.Lang.TypeDecl.Constructor in
                   let url, attrs, code =
                     constructor
                       (cstr.id :> Paths.Identifier.t)
                       cstr.args cstr.res
                   in
                   let anchor = Some url in
                   let rhs = Comment.to_ir cstr.doc in
                   let doc =
                     if not (Comment.has_doc cstr.doc) then [] else rhs
                   in
                   DocumentedSrc.Nested { anchor; attrs; code; doc })
          in
          rows

    let variant2 cstrs : DocumentedSrc.t =
      let constructor id args res =
        match Url.from_identifier ~stop_before:true id with
        | Error e -> failwith (Url.Error.to_string e)
        | Ok url ->
            let attrs = [ "def"; "variant"; url.kind ] in
            let content =
              let doc = constructor2 id args res in
              O.documentedSrc (O.txt "| ") @ doc
            in
            (url, attrs, content)
      in
      match cstrs with
      | [] -> O.documentedSrc (O.txt "|")
      | _ :: _ ->
          let rows =
            cstrs
            |> List.map (fun cstr ->
                   let open Odoc_model.Lang.TypeDecl.Constructor in
                   let url, attrs, code =
                     constructor
                       (cstr.id :> Paths.Identifier.t)
                       cstr.args cstr.res
                   in
                   let anchor = Some url in
                   let rhs = Comment.to_ir cstr.doc in
                   let doc =
                     if not (Comment.has_doc cstr.doc) then [] else rhs
                   in
                   DocumentedSrc.Nested { anchor; attrs; code; doc })
          in
          rows

    let extension_constructor1 (t : Odoc_model.Lang.Extension.Constructor.t) =
      let id = (t.id :> Paths.Identifier.t) in
      match Url.from_identifier ~stop_before:true id with
      | Error e -> failwith (Url.Error.to_string e)
      | Ok url ->
          let anchor = Some url in
          let attrs = [ "def"; url.kind ] in
          let code =
            O.documentedSrc (O.txt "| ") @ constructor1 id t.args t.res
          in
          let doc = Comment.to_ir t.doc in
          DocumentedSrc.Nested { anchor; attrs; code; doc }

    let extension_constructor2 (t : Odoc_model.Lang.Extension.Constructor.t) =
      let id = (t.id :> Paths.Identifier.t) in
      match Url.from_identifier ~stop_before:true id with
      | Error e -> failwith (Url.Error.to_string e)
      | Ok url ->
          let anchor = Some url in
          let attrs = [ "def"; url.kind ] in
          let code =
            O.documentedSrc (O.txt "| ") @ constructor2 id t.args t.res
          in
          let doc = Comment.to_ir t.doc in
          DocumentedSrc.Nested { anchor; attrs; code; doc }

    let extension1 (t : Odoc_model.Lang.Extension.t) =
      let content =
        O.documentedSrc
          ( O.keyword "type" ++ O.txt " "
          ++ Link.from_path (t.type_path :> Paths.Path.t)
          ++ O.txt " += " )
        @ List.map extension_constructor1 t.constructors
        @ O.documentedSrc
            (if Syntax1.Type.type_def_semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "extension" in
      let anchor = None in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let extension2 (t : Odoc_model.Lang.Extension.t) =
      let content =
        O.documentedSrc
          ( O.keyword "type" ++ O.txt " "
          ++ Link.from_path (t.type_path :> Paths.Path.t)
          ++ O.txt " += " )
        @ List.map extension_constructor2 t.constructors
        @ O.documentedSrc
            (if Syntax2.Type.type_def_semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "extension" in
      let anchor = None in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let exn1 (t : Odoc_model.Lang.Exception.t) =
      let cstr = constructor1 (t.id :> Paths.Identifier.t) t.args t.res in
      let content =
        O.documentedSrc (O.keyword "exception" ++ O.txt " ")
        @ cstr
        @ O.documentedSrc
            (if Syntax1.Type.Exception.semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "exception" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let exn2 (t : Odoc_model.Lang.Exception.t) =
      let cstr = constructor2 (t.id :> Paths.Identifier.t) t.args t.res in
      let content =
        O.documentedSrc (O.keyword "exception" ++ O.txt " ")
        @ cstr
        @ O.documentedSrc
            (if Syntax2.Type.Exception.semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "exception" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let polymorphic_variant1 ~type_ident
        (t : Odoc_model.Lang.TypeExpr.Polymorphic_variant.t) =
      let row item =
        let kind_approx, cstr, doc =
          match item with
          | Odoc_model.Lang.TypeExpr.Polymorphic_variant.Type te ->
              ("unknown", O.code (type_expr1 te), None)
          | Constructor { constant; name; arguments; doc; _ } -> (
              let cstr = "`" ^ name in
              ( "constructor",
                ( match arguments with
                | [] -> O.code (O.txt cstr)
                | _ ->
                    (* Multiple arguments in a polymorphic variant constructor correspond
                       to a conjunction of types, not a product: [`Lbl int&float].
                       If constant is [true], the conjunction starts with an empty type,
                       for instance [`Lbl &int].
                    *)
                    let wrapped_type_expr =
                      (* type conjunction in Reason is printed as `Lbl (t1)&(t2)` *)
                      if Syntax1.Type.Variant.parenthesize_params then fun x ->
                        O.txt "(" ++ type_expr1 x ++ O.txt ")"
                      else fun x -> type_expr1 x
                    in
                    let params =
                      O.list arguments ~sep:(O.txt " & ") ~f:wrapped_type_expr
                    in
                    let params =
                      if constant then O.txt "& " ++ params else params
                    in
                    O.code
                      ( O.txt cstr
                      ++
                      if Syntax1.Type.Variant.parenthesize_params then params
                      else O.txt " " ++ O.keyword "of" ++ O.txt " " ++ params )
                ),
                match doc with [] -> None | _ -> Some (Comment.to_ir doc) ) )
        in
        try
          let url = Url.Anchor.polymorphic_variant ~type_ident item in
          let attrs = [ "def"; url.kind ] in
          let anchor = Some url in
          let code = O.code (O.txt "| ") @ cstr in
          let doc = match doc with None -> [] | Some doc -> doc in
          DocumentedSrc.Documented { attrs; anchor; code; doc }
        with Failure s ->
          Printf.eprintf "ERROR: %s\n%!" s;
          let code = O.code (O.txt "| ") @ cstr in
          let attrs = [ "def"; kind_approx ] in
          let doc = [] in
          let anchor = None in
          DocumentedSrc.Documented { attrs; anchor; code; doc }
      in
      let variants = List.map row t.elements in
      let intro, ending =
        match t.kind with
        | Fixed -> (O.documentedSrc (O.txt "[ "), O.documentedSrc (O.txt " ]"))
        | Open -> (O.documentedSrc (O.txt "[> "), O.documentedSrc (O.txt " ]"))
        | Closed [] ->
            (O.documentedSrc (O.txt "[< "), O.documentedSrc (O.txt " ]"))
        | Closed lst ->
            let constrs = String.concat " " lst in
            ( O.documentedSrc (O.txt "[< "),
              O.documentedSrc (O.txt (" " ^ constrs ^ " ]")) )
      in
      intro @ variants @ ending

    let polymorphic_variant2 ~type_ident
        (t : Odoc_model.Lang.TypeExpr.Polymorphic_variant.t) =
      let row item =
        let kind_approx, cstr, doc =
          match item with
          | Odoc_model.Lang.TypeExpr.Polymorphic_variant.Type te ->
              ("unknown", O.code (type_expr2 te), None)
          | Constructor { constant; name; arguments; doc; _ } -> (
              let cstr = "`" ^ name in
              ( "constructor",
                ( match arguments with
                | [] -> O.code (O.txt cstr)
                | _ ->
                    (* Multiple arguments in a polymorphic variant constructor correspond
                       to a conjunction of types, not a product: [`Lbl int&float].
                       If constant is [true], the conjunction starts with an empty type,
                       for instance [`Lbl &int].
                    *)
                    let wrapped_type_expr =
                      (* type conjunction in Reason is printed as `Lbl (t1)&(t2)` *)
                      if Syntax2.Type.Variant.parenthesize_params then fun x ->
                        O.txt "(" ++ type_expr2 x ++ O.txt ")"
                      else fun x -> type_expr2 x
                    in
                    let params =
                      O.list arguments ~sep:(O.txt " & ") ~f:wrapped_type_expr
                    in
                    let params =
                      if constant then O.txt "& " ++ params else params
                    in
                    O.code
                      ( O.txt cstr
                      ++
                      if Syntax2.Type.Variant.parenthesize_params then params
                      else O.txt " " ++ O.keyword "of" ++ O.txt " " ++ params )
                ),
                match doc with [] -> None | _ -> Some (Comment.to_ir doc) ) )
        in
        try
          let url = Url.Anchor.polymorphic_variant ~type_ident item in
          let attrs = [ "def"; url.kind ] in
          let anchor = Some url in
          let code = O.code (O.txt "| ") @ cstr in
          let doc = match doc with None -> [] | Some doc -> doc in
          DocumentedSrc.Documented { attrs; anchor; code; doc }
        with Failure s ->
          Printf.eprintf "ERROR: %s\n%!" s;
          let code = O.code (O.txt "| ") @ cstr in
          let attrs = [ "def"; kind_approx ] in
          let doc = [] in
          let anchor = None in
          DocumentedSrc.Documented { attrs; anchor; code; doc }
      in
      let variants = List.map row t.elements in
      let intro, ending =
        match t.kind with
        | Fixed -> (O.documentedSrc (O.txt "[ "), O.documentedSrc (O.txt " ]"))
        | Open -> (O.documentedSrc (O.txt "[> "), O.documentedSrc (O.txt " ]"))
        | Closed [] ->
            (O.documentedSrc (O.txt "[< "), O.documentedSrc (O.txt " ]"))
        | Closed lst ->
            let constrs = String.concat " " lst in
            ( O.documentedSrc (O.txt "[< "),
              O.documentedSrc (O.txt (" " ^ constrs ^ " ]")) )
      in
      intro @ variants @ ending

    let format_params1 :
          'row. ?delim:[ `parens | `brackets ] ->
          Odoc_model.Lang.TypeDecl.param list -> text =
     fun ?(delim = `parens) params ->
      let format_param { Odoc_model.Lang.TypeDecl.desc; variance; injectivity }
          =
        let desc =
          match desc with
          | Odoc_model.Lang.TypeDecl.Any -> [ "_" ]
          | Var s -> [ "'"; s ]
        in
        let var_desc =
          match variance with
          | None -> desc
          | Some Odoc_model.Lang.TypeDecl.Pos -> "+" :: desc
          | Some Odoc_model.Lang.TypeDecl.Neg -> "-" :: desc
        in
        let final = if injectivity then "!" :: var_desc else var_desc in
        String.concat "" final
      in
      O.txt
        ( match params with
        | [] -> ""
        | [ x ] -> format_param x |> Syntax1.Type.handle_format_params
        | lst -> (
            let params = String.concat ", " (List.map format_param lst) in
            (match delim with `parens -> "(" | `brackets -> "[")
            ^ params
            ^ match delim with `parens -> ")" | `brackets -> "]" ) )

    let format_params2 :
          'row. ?delim:[ `parens | `brackets ] ->
          Odoc_model.Lang.TypeDecl.param list -> text =
     fun ?(delim = `parens) params ->
      let format_param { Odoc_model.Lang.TypeDecl.desc; variance; injectivity }
          =
        let desc =
          match desc with
          | Odoc_model.Lang.TypeDecl.Any -> [ "_" ]
          | Var s -> [ "'"; s ]
        in
        let var_desc =
          match variance with
          | None -> desc
          | Some Odoc_model.Lang.TypeDecl.Pos -> "+" :: desc
          | Some Odoc_model.Lang.TypeDecl.Neg -> "-" :: desc
        in
        let final = if injectivity then "!" :: var_desc else var_desc in
        String.concat "" final
      in
      O.txt
        ( match params with
        | [] -> ""
        | [ x ] -> format_param x |> Syntax2.Type.handle_format_params
        | lst -> (
            let params = String.concat ", " (List.map format_param lst) in
            (match delim with `parens -> "(" | `brackets -> "[")
            ^ params
            ^ match delim with `parens -> ")" | `brackets -> "]" ) )

    let format_constraints1 constraints =
      O.list constraints ~f:(fun (t1, t2) ->
          O.txt " " ++ O.keyword "constraint" ++ O.txt " " ++ type_expr1 t1
          ++ O.txt " = " ++ type_expr1 t2)

    let format_constraints2 constraints =
      O.list constraints ~f:(fun (t1, t2) ->
          O.txt " " ++ O.keyword "constraint" ++ O.txt " " ++ type_expr2 t1
          ++ O.txt " = " ++ type_expr2 t2)

    let format_manifest1 :
          'inner_row 'outer_row. ?is_substitution:bool ->
          ?compact_variants:bool -> Odoc_model.Lang.TypeDecl.Equation.t ->
          text * bool =
     fun ?(is_substitution = false) ?(compact_variants = true) equation ->
      let _ = compact_variants in
      (* TODO *)
      let private_ = equation.private_ in
      match equation.manifest with
      | None -> (O.noop, private_)
      | Some t ->
          let manifest =
            O.txt (if is_substitution then " := " else " = ")
            ++ ( if private_ then
                 O.keyword Syntax1.Type.private_keyword ++ O.txt " "
               else O.noop )
            ++ type_expr1 t
          in
          (manifest, false)

    let format_manifest2 :
          'inner_row 'outer_row. ?is_substitution:bool ->
          ?compact_variants:bool -> Odoc_model.Lang.TypeDecl.Equation.t ->
          text * bool =
     fun ?(is_substitution = false) ?(compact_variants = true) equation ->
      let _ = compact_variants in
      (* TODO *)
      let private_ = equation.private_ in
      match equation.manifest with
      | None -> (O.noop, private_)
      | Some t ->
          let manifest =
            O.txt (if is_substitution then " := " else " = ")
            ++ ( if private_ then
                 O.keyword Syntax2.Type.private_keyword ++ O.txt " "
               else O.noop )
            ++ type_expr2 t
          in
          (manifest, false)

    let type_decl1 ?(is_substitution = false)
        ((_recursive, t) : Lang.Signature.recursive * Lang.TypeDecl.t) =
      let tyname = Paths.Identifier.name t.id in
      let constraints = format_constraints1 t.equation.constraints in
      let manifest, need_private =
        match t.equation.manifest with
        | Some (Odoc_model.Lang.TypeExpr.Polymorphic_variant variant) ->
            let code =
              polymorphic_variant1
                ~type_ident:(t.id :> Paths.Identifier.t)
                variant
            in
            let manifest =
              O.documentedSrc
                ( O.txt (if is_substitution then " := " else " = ")
                ++
                if t.equation.private_ then
                  O.keyword Syntax1.Type.private_keyword ++ O.txt " "
                else O.noop )
              @ code
            in
            (manifest, false)
        | _ ->
            let manifest, need_private =
              format_manifest1 ~is_substitution t.equation
            in
            (O.documentedSrc manifest, need_private)
      in
      let representation =
        match t.representation with
        | None -> []
        | Some repr ->
            let content =
              match repr with
              | Extensible -> O.documentedSrc (O.txt "..")
              | Variant cstrs -> variant1 cstrs
              | Record fields -> record1 fields
            in
            O.documentedSrc
              ( O.txt " = "
              ++
              if need_private then
                O.keyword Syntax1.Type.private_keyword ++ O.txt " "
              else O.noop )
            @ content
      in
      let tconstr =
        match t.equation.params with
        | [] -> O.txt tyname
        | l ->
            let params = format_params1 l in
            Syntax1.Type.handle_constructor_params (O.txt tyname) params
      in
      (tconstr, manifest, representation, constraints)

    let type_decl2 ?(is_substitution = false)
        ((_recursive, t) : Lang.Signature.recursive * Lang.TypeDecl.t) =
      let tyname = Paths.Identifier.name t.id in
      let constraints = format_constraints2 t.equation.constraints in
      let manifest, need_private =
        match t.equation.manifest with
        | Some (Odoc_model.Lang.TypeExpr.Polymorphic_variant variant) ->
            let code =
              polymorphic_variant2
                ~type_ident:(t.id :> Paths.Identifier.t)
                variant
            in
            let manifest =
              O.documentedSrc
                ( O.txt (if is_substitution then " := " else " = ")
                ++
                if t.equation.private_ then
                  O.keyword Syntax2.Type.private_keyword ++ O.txt " "
                else O.noop )
              @ code
            in
            (manifest, false)
        | _ ->
            let manifest, need_private =
              format_manifest2 ~is_substitution t.equation
            in
            (O.documentedSrc manifest, need_private)
      in
      let representation =
        match t.representation with
        | None -> []
        | Some repr ->
            let content =
              match repr with
              | Extensible -> O.documentedSrc (O.txt "..")
              | Variant cstrs -> variant2 cstrs
              | Record fields -> record2 fields
            in
            O.documentedSrc
              ( O.txt " = "
              ++
              if need_private then
                O.keyword Syntax2.Type.private_keyword ++ O.txt " "
              else O.noop )
            @ content
      in
      let tconstr =
        match t.equation.params with
        | [] -> O.txt tyname
        | l ->
            let params = format_params2 l in
            Syntax2.Type.handle_constructor_params (O.txt tyname) params
      in
      (tconstr, manifest, representation, constraints)

    let type_decl ?(is_substitution = false)
        ((recursive, t) as decl : Lang.Signature.recursive * Lang.TypeDecl.t) =
      let tconstr1, manifest1, representation1, constraints1 =
        type_decl1 ~is_substitution decl
      in
      let tconstr2, manifest2, representation2, constraints2 =
        type_decl2 ~is_substitution decl
      in
      let keyword' =
          match recursive with
          | Ordinary | Rec -> O.keyword "type"
          | And -> O.keyword "and"
          | Nonrec -> O.keyword "type" ++ O.txt " " ++ O.keyword "nonrec"
        in
      let content1 =
        O.documentedSrc (keyword' ++ O.txt " " ++ tconstr1)
        @ manifest1
        @ representation1
        @ O.documentedSrc constraints1
        @ O.documentedSrc
            (if Syntax1.Type.type_def_semicolon then O.txt ";" else O.noop)
      in
      let content2 =
        O.documentedSrc (keyword' ++ O.txt " " ++ tconstr2)
        @ manifest2
        @ representation2
        @ O.documentedSrc constraints2
        @ O.documentedSrc
            (if Syntax2.Type.type_def_semicolon then O.txt ";" else O.noop)
      in
      let kind = Some (if is_substitution then "type-subst" else "type") in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.DualDeclaration { kind; anchor; doc; content1; content2 }
  end

  open Type_declaration

  module Value : sig
    val value1 : Lang.Value.t -> Item.t

    val value2 : Lang.Value.t -> Item.t

    val external1 : Lang.External.t -> Item.t

    val external2 : Lang.External.t -> Item.t
  end = struct
    let value1 (t : Odoc_model.Lang.Value.t) =
      let name = Paths.Identifier.name t.id in
      let content =
        O.documentedSrc
          ( O.keyword Syntax1.Value.variable_keyword
          ++ O.txt " " ++ O.txt name
          ++ O.txt Syntax1.Type.annotation_separator
          ++ type_expr1 t.type_
          ++ if Syntax1.Value.semicolon then O.txt ";" else O.noop )
      in
      let kind = Some "value" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let value2 (t : Odoc_model.Lang.Value.t) =
      let name = Paths.Identifier.name t.id in
      let content =
        O.documentedSrc
          ( O.keyword Syntax2.Value.variable_keyword
          ++ O.txt " " ++ O.txt name
          ++ O.txt Syntax2.Type.annotation_separator
          ++ type_expr2 t.type_
          ++ if Syntax2.Value.semicolon then O.txt ";" else O.noop )
      in
      let kind = Some "value" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let external1 (t : Odoc_model.Lang.External.t) =
      let name = Paths.Identifier.name t.id in
      let content =
        O.documentedSrc
          ( O.keyword Syntax1.Value.variable_keyword
          ++ O.txt " " ++ O.txt name
          ++ O.txt Syntax1.Type.annotation_separator
          ++ type_expr1 t.type_
          ++ if Syntax1.Type.External.semicolon then O.txt ";" else O.noop )
      in
      let kind = Some "external" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let external2 (t : Odoc_model.Lang.External.t) =
      let name = Paths.Identifier.name t.id in
      let content =
        O.documentedSrc
          ( O.keyword Syntax2.Value.variable_keyword
          ++ O.txt " " ++ O.txt name
          ++ O.txt Syntax2.Type.annotation_separator
          ++ type_expr2 t.type_
          ++ if Syntax2.Type.External.semicolon then O.txt ";" else O.noop )
      in
      let kind = Some "external" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }
  end

  open Value

  (* This chunk of code is responsible for sectioning list of items
     according to headings by extracting headings as Items.

     TODO: This sectioning would be better done as a pass on the model directly.
  *)
  module Sectioning : sig
    open Odoc_model

    val comment_items : Comment.docs -> Item.t list

    val docs : Comment.docs -> Item.t list * Item.t list
  end = struct
    let take_until_heading_or_end (docs : Odoc_model.Comment.docs) =
      let content, _, rest =
        Doctree.Take.until docs ~classify:(fun b ->
            match b.Location.value with
            | `Heading _ -> Stop_and_keep
            | #Odoc_model.Comment.attached_block_element as doc ->
                let content = Comment.attached_block_element doc in
                Accum content)
      in
      (content, rest)

    let comment_items (input0 : Odoc_model.Comment.docs) =
      let rec loop input_comment acc =
        match input_comment with
        | [] -> List.rev acc
        | element :: input_comment -> (
            match element.Location.value with
            | `Heading (level, label, content) ->
                let h = `Heading (level, label, content) in
                let item = Comment.heading h in
                loop input_comment (item :: acc)
            | _ ->
                let content, input_comment =
                  take_until_heading_or_end (element :: input_comment)
                in
                let item = Item.Text content in
                loop input_comment (item :: acc) )
      in
      loop input0 []

    (* For doc pages, we want the header to contain everything until
       the first heading, then everything before the next heading which
       is either lower, or a section.
    *)
    let docs input_comment =
      let items = comment_items input_comment in
      let until_first_heading, o, items =
        Doctree.Take.until items ~classify:(function
          | Item.Heading h as i -> Stop_and_accum ([ i ], Some h.level)
          | i -> Accum [ i ])
      in
      match o with
      | None -> (until_first_heading, items)
      | Some level ->
          let max_level = if level = 1 then 2 else level in
          let before_second_heading, _, items =
            Doctree.Take.until items ~classify:(function
              | Item.Heading h when h.level >= max_level -> Stop_and_keep
              | i -> Accum [ i ])
          in
          let header = until_first_heading @ before_second_heading in
          (header, items)
  end

  module Class : sig
    val class1 : Lang.Signature.recursive -> Lang.Class.t -> Item.t

    val class2 : Lang.Signature.recursive -> Lang.Class.t -> Item.t

    val class_type1 : Lang.Signature.recursive -> Lang.ClassType.t -> Item.t

    val class_type2 : Lang.Signature.recursive -> Lang.ClassType.t -> Item.t
  end = struct
    let class_type_expr1 (cte : Odoc_model.Lang.ClassType.expr) =
      match cte with
      | Constr (path, args) ->
          let link = Link.from_path (path :> Paths.Path.t) in
          format_type_path1 ~delim:`brackets args link
      | Signature _ ->
          Syntax1.Class.open_tag ++ O.txt " ... " ++ Syntax1.Class.close_tag

    let class_type_expr2 (cte : Odoc_model.Lang.ClassType.expr) =
      match cte with
      | Constr (path, args) ->
          let link = Link.from_path (path :> Paths.Path.t) in
          format_type_path2 ~delim:`brackets args link
      | Signature _ ->
          Syntax2.Class.open_tag ++ O.txt " ... " ++ Syntax2.Class.close_tag

    let method1 (t : Odoc_model.Lang.Method.t) =
      let name = Paths.Identifier.name t.id in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in
      let private_ =
        if t.private_ then O.keyword "private" ++ O.txt " " else O.noop
      in
      let content =
        O.documentedSrc
          ( O.keyword "method" ++ O.txt " " ++ private_ ++ virtual_ ++ O.txt name
          ++ O.txt Syntax1.Type.annotation_separator
          ++ type_expr1 t.type_ )
      in
      let kind = Some "method" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let method2 (t : Odoc_model.Lang.Method.t) =
      let name = Paths.Identifier.name t.id in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in
      let private_ =
        if t.private_ then O.keyword "private" ++ O.txt " " else O.noop
      in
      let content =
        O.documentedSrc
          ( O.keyword "method" ++ O.txt " " ++ private_ ++ virtual_ ++ O.txt name
          ++ O.txt Syntax2.Type.annotation_separator
          ++ type_expr2 t.type_ )
      in
      let kind = Some "method" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let instance_variable1 (t : Odoc_model.Lang.InstanceVariable.t) =
      let name = Paths.Identifier.name t.id in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in
      let mutable_ =
        if t.mutable_ then O.keyword "mutable" ++ O.txt " " else O.noop
      in
      let content =
        O.documentedSrc
          ( O.keyword "val" ++ O.txt " " ++ mutable_ ++ virtual_ ++ O.txt name
          ++ O.txt Syntax1.Type.annotation_separator
          ++ type_expr1 t.type_ )
      in
      let kind = Some "instance-variable" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let instance_variable2 (t : Odoc_model.Lang.InstanceVariable.t) =
      let name = Paths.Identifier.name t.id in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in
      let mutable_ =
        if t.mutable_ then O.keyword "mutable" ++ O.txt " " else O.noop
      in
      let content =
        O.documentedSrc
          ( O.keyword "val" ++ O.txt " " ++ mutable_ ++ virtual_ ++ O.txt name
          ++ O.txt Syntax2.Type.annotation_separator
          ++ type_expr2 t.type_ )
      in
      let kind = Some "instance-variable" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let inherit1 cte =
      let content =
        O.documentedSrc
          (O.keyword "inherit" ++ O.txt " " ++ class_type_expr1 cte)
      in
      let kind = Some "inherit" in
      let anchor = None in
      let doc = [] in
      Item.Declaration { kind; anchor; doc; content }

    let inherit2 cte =
      let content =
        O.documentedSrc
          (O.keyword "inherit" ++ O.txt " " ++ class_type_expr2 cte)
      in
      let kind = Some "inherit" in
      let anchor = None in
      let doc = [] in
      Item.Declaration { kind; anchor; doc; content }

    let constraint1 t1 t2 =
      let content = O.documentedSrc (format_constraints1 [ (t1, t2) ]) in
      let kind = None in
      let anchor = None in
      let doc = [] in
      Item.Declaration { kind; anchor; doc; content }

    let constraint2 t1 t2 =
      let content = O.documentedSrc (format_constraints2 [ (t1, t2) ]) in
      let kind = None in
      let anchor = None in
      let doc = [] in
      Item.Declaration { kind; anchor; doc; content }

    let class_signature1 (c : Lang.ClassSignature.t) =
      let rec loop l acc_items =
        match l with
        | [] -> List.rev acc_items
        | item :: rest -> (
            let continue item = loop rest (item :: acc_items) in
            match (item : Lang.ClassSignature.item) with
            | Inherit (Signature _) -> assert false (* Bold. *)
            | Inherit cty -> continue @@ inherit1 cty
            | Method m -> continue @@ method1 m
            | InstanceVariable v -> continue @@ instance_variable1 v
            | Constraint (t1, t2) -> continue @@ constraint1 t1 t2
            | Comment `Stop ->
                let rest =
                  Utils.skip_until rest ~p:(function
                    | Lang.ClassSignature.Comment `Stop -> true
                    | _ -> false)
                in
                loop rest acc_items
            | Comment (`Docs c) ->
                let items = Sectioning.comment_items c in
                loop rest (List.rev_append items acc_items) )
      in
      (* FIXME: use [t.self] *)
      loop c.items []

    let class_signature2 (c : Lang.ClassSignature.t) =
      let rec loop l acc_items =
        match l with
        | [] -> List.rev acc_items
        | item :: rest -> (
            let continue item = loop rest (item :: acc_items) in
            match (item : Lang.ClassSignature.item) with
            | Inherit (Signature _) -> assert false (* Bold. *)
            | Inherit cty -> continue @@ inherit2 cty
            | Method m -> continue @@ method2 m
            | InstanceVariable v -> continue @@ instance_variable2 v
            | Constraint (t1, t2) -> continue @@ constraint2 t1 t2
            | Comment `Stop ->
                let rest =
                  Utils.skip_until rest ~p:(function
                    | Lang.ClassSignature.Comment `Stop -> true
                    | _ -> false)
                in
                loop rest acc_items
            | Comment (`Docs c) ->
                let items = Sectioning.comment_items c in
                loop rest (List.rev_append items acc_items) )
      in
      (* FIXME: use [t.self] *)
      loop c.items []

    let rec class_decl1 (cd : Odoc_model.Lang.Class.decl) =
      match cd with
      | ClassType expr -> class_type_expr1 expr
      (* TODO: factorize the following with [type_expr] *)
      | Arrow (None, src, dst) ->
          type_expr1 ~needs_parentheses:true src
          ++ O.txt " " ++ Syntax1.Type.arrow ++ O.txt " " ++ class_decl1 dst
      | Arrow (Some lbl, src, dst) ->
          label lbl ++ O.txt ":"
          ++ type_expr1 ~needs_parentheses:true src
          ++ O.txt " " ++ Syntax1.Type.arrow ++ O.txt " " ++ class_decl1 dst

    let rec class_decl2 (cd : Odoc_model.Lang.Class.decl) =
      match cd with
      | ClassType expr -> class_type_expr2 expr
      (* TODO: factorize the following with [type_expr] *)
      | Arrow (None, src, dst) ->
          type_expr2 ~needs_parentheses:true src
          ++ O.txt " " ++ Syntax2.Type.arrow ++ O.txt " " ++ class_decl2 dst
      | Arrow (Some lbl, src, dst) ->
          label lbl ++ O.txt ":"
          ++ type_expr2 ~needs_parentheses:true src
          ++ O.txt " " ++ Syntax2.Type.arrow ++ O.txt " " ++ class_decl2 dst

    let class1 recursive (t : Odoc_model.Lang.Class.t) =
      let name = Paths.Identifier.name t.id in
      let params = format_params1 ~delim:`brackets t.params in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in

      let cname, expansion =
        match t.expansion with
        | None -> (O.documentedSrc @@ O.txt name, None)
        | Some csig ->
            let doc = Comment.standalone t.doc in
            let items = class_signature1 csig in
            let url = Url.Path.from_identifier t.id in
            let header = format_title `Class (make_name_from_path url) @ doc in
            let page = { Page.title = name; header; items; url } in
            (O.documentedSrc @@ path url [ inline @@ Text name ], Some page)
      in
      let summary =
        O.txt Syntax1.Type.annotation_separator ++ class_decl1 t.type_
      in
      let cd =
        attach_expansion
          (Syntax1.Type.annotation_separator, "object", "end")
          expansion summary
      in
      let content =
        let open Lang.Signature in
        let keyword' =
          match recursive with
          | Ordinary | Nonrec | Rec -> "class"
          | And -> "and"
        in
        O.documentedSrc
          (O.keyword keyword' ++ O.txt " " ++ virtual_ ++ params ++ O.txt " ")
        @ cname @ cd
      in
      let kind = Some "class" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let class2 recursive (t : Odoc_model.Lang.Class.t) =
      let name = Paths.Identifier.name t.id in
      let params = format_params2 ~delim:`brackets t.params in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in

      let cname, expansion =
        match t.expansion with
        | None -> (O.documentedSrc @@ O.txt name, None)
        | Some csig ->
            let doc = Comment.standalone t.doc in
            let items = class_signature2 csig in
            let url = Url.Path.from_identifier t.id in
            let header = format_title `Class (make_name_from_path url) @ doc in
            let page = { Page.title = name; header; items; url } in
            (O.documentedSrc @@ path url [ inline @@ Text name ], Some page)
      in
      let summary =
        O.txt Syntax2.Type.annotation_separator ++ class_decl2 t.type_
      in
      let cd =
        attach_expansion
          (Syntax2.Type.annotation_separator, "object", "end")
          expansion summary
      in
      let content =
        let open Lang.Signature in
        let keyword' =
          match recursive with
          | Ordinary | Nonrec | Rec -> "class"
          | And -> "and"
        in
        O.documentedSrc
          (O.keyword keyword' ++ O.txt " " ++ virtual_ ++ params ++ O.txt " ")
        @ cname @ cd
      in
      let kind = Some "class" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let class_type1 recursive (t : Odoc_model.Lang.ClassType.t) =
      let name = Paths.Identifier.name t.id in
      let params = format_params1 ~delim:`brackets t.params in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in
      let cname, expansion =
        match t.expansion with
        | None -> (O.documentedSrc @@ O.txt name, None)
        | Some csig ->
            let url = Url.Path.from_identifier t.id in
            let doc = Comment.standalone t.doc in
            let items = class_signature1 csig in
            let header = format_title `Cty (make_name_from_path url) @ doc in
            let page = { Page.title = name; header; items; url } in
            (O.documentedSrc @@ path url [ inline @@ Text name ], Some page)
      in
      let expr =
        attach_expansion (" = ", "object", "end") expansion
          (class_type_expr1 t.expr)
      in
      let content =
        let open Lang.Signature in
        let keyword' =
          match recursive with
          | Ordinary | Nonrec | Rec ->
              O.keyword "class" ++ O.txt " " ++ O.keyword "type"
          | And -> O.keyword "and"
        in
        O.documentedSrc
          (keyword' ++ O.txt " " ++ virtual_ ++ params ++ O.txt " ")
        @ cname @ expr
      in
      let kind = Some "class-type" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    let class_type2 recursive (t : Odoc_model.Lang.ClassType.t) =
      let name = Paths.Identifier.name t.id in
      let params = format_params2 ~delim:`brackets t.params in
      let virtual_ =
        if t.virtual_ then O.keyword "virtual" ++ O.txt " " else O.noop
      in
      let cname, expansion =
        match t.expansion with
        | None -> (O.documentedSrc @@ O.txt name, None)
        | Some csig ->
            let url = Url.Path.from_identifier t.id in
            let doc = Comment.standalone t.doc in
            let items = class_signature2 csig in
            let header = format_title `Cty (make_name_from_path url) @ doc in
            let page = { Page.title = name; header; items; url } in
            (O.documentedSrc @@ path url [ inline @@ Text name ], Some page)
      in
      let expr =
        attach_expansion (" = ", "object", "end") expansion
          (class_type_expr2 t.expr)
      in
      let content =
        let open Lang.Signature in
        let keyword' =
          match recursive with
          | Ordinary | Nonrec | Rec ->
              O.keyword "class" ++ O.txt " " ++ O.keyword "type"
          | And -> O.keyword "and"
        in
        O.documentedSrc
          (keyword' ++ O.txt " " ++ virtual_ ++ params ++ O.txt " ")
        @ cname @ expr
      in
      let kind = Some "class-type" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }
  end

  open Class

  module Module : sig
    val signature : Lang.Signature.t -> Item.t list
  end = struct
    let internal_module m =
      let open Lang.Module in
      match m.id with
      | `Module (_, name) when ModuleName.is_internal name -> true
      | _ -> false

    let internal_type t =
      let open Lang.TypeDecl in
      match t.id with
      | `Type (_, name) when TypeName.is_internal name -> true
      | _ -> false

    let internal_module_type t =
      let open Lang.ModuleType in
      match t.id with
      | `ModuleType (_, name) when ModuleTypeName.is_internal name -> true
      | _ -> false

    let internal_module_substitution t =
      let open Lang.ModuleSubstitution in
      match t.id with
      | `Module (_, name) when ModuleName.is_internal name -> true
      | _ -> false

    let rec signature s : Item.t list =
      let rec loop l acc_items =
        match l with
        | [] -> List.rev acc_items
        | item :: rest -> (
            let continue (item : Item.t) = loop rest (item :: acc_items) in
            match (item : Lang.Signature.item) with
            | Module (_, m) when internal_module m -> loop rest acc_items
            | Type (_, t) when internal_type t -> loop rest acc_items
            | ModuleType m when internal_module_type m -> loop rest acc_items
            | ModuleSubstitution m when internal_module_substitution m ->
                loop rest acc_items
            | Module (recursive, m) -> continue @@ module1 recursive m
            | ModuleType m -> continue @@ module_type1 m
            | Class (recursive, c) -> continue @@ class1 recursive c
            | ClassType (recursive, c) -> continue @@ class_type1 recursive c
            | Include m -> continue @@ include1 m
            | ModuleSubstitution m -> continue @@ module_substitution m
            | TypeSubstitution t ->
                continue @@ type_decl ~is_substitution:true (Ordinary, t)
            | Type (r, t) -> continue @@ type_decl (r, t)
            | TypExt e -> continue @@ extension1 e
            | Exception e -> continue @@ exn1 e
            | Value v -> continue @@ value1 v
            | External e -> continue @@ external1 e
            | Open _ -> loop rest acc_items
            | Comment `Stop ->
                let rest =
                  Utils.skip_until rest ~p:(function
                    | Lang.Signature.Comment `Stop -> true
                    | _ -> false)
                in
                loop rest acc_items
            | Comment (`Docs c) ->
                let items = Sectioning.comment_items c in
                loop rest (List.rev_append items acc_items) )
      in
      loop s []

    and functor_parameter1 :
        Odoc_model.Lang.FunctorParameter.parameter -> DocumentedSrc.t =
     fun arg ->
      let open Odoc_model.Lang.FunctorParameter in
      let name = Paths.Identifier.name arg.id in
      let render_ty = arg.expr in
      let modtyp =
        mty_in_decl1 (arg.id :> Paths.Identifier.Signature.t) render_ty
      in
      let modname, mod_decl =
        match expansion_of_module_type_expr1 arg.expr with
        | None ->
            let modname = O.txt (Paths.Identifier.name arg.id) in
            (modname, O.documentedSrc modtyp)
        | Some items ->
            let url = Url.Path.from_identifier arg.id in
            let modname = path url [ inline @@ Text name ] in
            let type_with_expansion =
              let header = format_title `Arg (make_name_from_path url) in
              let title = name in
              let content = { Page.items; title; header; url } in
              let summary = O.render modtyp in
              let status = `Default in
              let expansion =
                O.documentedSrc
                  (O.txt Syntax1.Type.annotation_separator ++ O.keyword "sig")
                @ DocumentedSrc.[ Subpage { content; status } ]
                @ O.documentedSrc (O.keyword "end")
              in
              DocumentedSrc.
                [
                  Alternative
                    (Expansion { status = `Default; summary; url; expansion });
                ]
            in
            (modname, type_with_expansion)
      in
      O.documentedSrc (O.keyword "module" ++ O.txt " ")
      @ O.documentedSrc modname @ mod_decl

    and functor_parameter2 :
        Odoc_model.Lang.FunctorParameter.parameter -> DocumentedSrc.t =
     fun arg ->
      let open Odoc_model.Lang.FunctorParameter in
      let name = Paths.Identifier.name arg.id in
      let render_ty = arg.expr in
      let modtyp =
        mty_in_decl2 (arg.id :> Paths.Identifier.Signature.t) render_ty
      in
      let modname, mod_decl =
        match expansion_of_module_type_expr2 arg.expr with
        | None ->
            let modname = O.txt (Paths.Identifier.name arg.id) in
            (modname, O.documentedSrc modtyp)
        | Some items ->
            let url = Url.Path.from_identifier arg.id in
            let modname = path url [ inline @@ Text name ] in
            let type_with_expansion =
              let header = format_title `Arg (make_name_from_path url) in
              let title = name in
              let content = { Page.items; title; header; url } in
              let summary = O.render modtyp in
              let status = `Default in
              let expansion =
                O.documentedSrc
                  (O.txt Syntax2.Type.annotation_separator ++ O.keyword "sig")
                @ DocumentedSrc.[ Subpage { content; status } ]
                @ O.documentedSrc (O.keyword "end")
              in
              DocumentedSrc.
                [
                  Alternative
                    (Expansion { status = `Default; summary; url; expansion });
                ]
            in
            (modname, type_with_expansion)
      in
      O.documentedSrc (O.keyword "module" ++ O.txt " ")
      @ O.documentedSrc modname @ mod_decl

    and module_substitution (t : Odoc_model.Lang.ModuleSubstitution.t) =
      let name = Paths.Identifier.name t.id in
      let path = Link.from_path (t.manifest :> Paths.Path.t) in
      let content =
        O.documentedSrc
          (O.keyword "module" ++ O.txt " " ++ O.txt name ++ O.txt " := " ++ path)
      in
      let kind = Some "module-substitution" in
      let anchor = path_to_id t.id in
      let doc = Comment.to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    and simple_expansion1 :
        Odoc_model.Lang.ModuleType.simple_expansion -> Item.t list =
     fun t ->
      let rec extract_functor_params
          (f : Odoc_model.Lang.ModuleType.simple_expansion) =
        match f with
        | Signature sg -> (None, sg)
        | Functor (p, expansion) ->
            let add_to params =
              match p with Unit -> params | Named p -> p :: params
            in
            let params, sg = extract_functor_params expansion in
            let params = match params with None -> [] | Some p -> p in
            (Some (add_to params), sg)
      in
      match extract_functor_params t with
      | None, sg ->
          let expansion = signature sg in
          expansion
      | Some params, sg ->
          let content = signature sg in
          let params =
            Utils.flatmap params ~f:(fun arg ->
                let content = functor_parameter1 arg in
                let kind = Some "parameter" in
                let anchor =
                  Utils.option_of_result
                  @@ Url.Anchor.from_identifier (arg.id :> Paths.Identifier.t)
                in
                let doc = [] in
                [ Item.Declaration { content; anchor; kind; doc } ])
          in
          let prelude =
            Item.Heading
              {
                label = Some "parameters";
                level = 1;
                title = [ inline @@ Text "Parameters" ];
              }
            :: params
          and content =
            Item.Heading
              {
                label = Some "signature";
                level = 1;
                title = [ inline @@ Text "Signature" ];
              }
            :: content
          in
          prelude @ content

    and simple_expansion2 :
        Odoc_model.Lang.ModuleType.simple_expansion -> Item.t list =
     fun t ->
      let rec extract_functor_params
          (f : Odoc_model.Lang.ModuleType.simple_expansion) =
        match f with
        | Signature sg -> (None, sg)
        | Functor (p, expansion) ->
            let add_to params =
              match p with Unit -> params | Named p -> p :: params
            in
            let params, sg = extract_functor_params expansion in
            let params = match params with None -> [] | Some p -> p in
            (Some (add_to params), sg)
      in
      match extract_functor_params t with
      | None, sg ->
          let expansion = signature sg in
          expansion
      | Some params, sg ->
          let content = signature sg in
          let params =
            Utils.flatmap params ~f:(fun arg ->
                let content = functor_parameter2 arg in
                let kind = Some "parameter" in
                let anchor =
                  Utils.option_of_result
                  @@ Url.Anchor.from_identifier (arg.id :> Paths.Identifier.t)
                in
                let doc = [] in
                [ Item.Declaration { content; anchor; kind; doc } ])
          in
          let prelude =
            Item.Heading
              {
                label = Some "parameters";
                level = 1;
                title = [ inline @@ Text "Parameters" ];
              }
            :: params
          and content =
            Item.Heading
              {
                label = Some "signature";
                level = 1;
                title = [ inline @@ Text "Signature" ];
              }
            :: content
          in
          prelude @ content

    and expansion_of_module_type_expr1 :
        Odoc_model.Lang.ModuleType.expr -> Item.t list option =
     fun t ->
      let rec simple_expansion_of (t : Odoc_model.Lang.ModuleType.expr) =
        match t with
        | Path { p_expansion = None; _ }
        | TypeOf { t_expansion = None; _ }
        | With { w_expansion = None; _ } ->
            None
        | Path { p_expansion = Some e; _ }
        | TypeOf { t_expansion = Some e; _ }
        | With { w_expansion = Some e; _ } ->
            Some e
        | Signature sg -> Some (Signature sg)
        | Functor (f_parameter, e) -> (
            match simple_expansion_of e with
            | Some e -> Some (Functor (f_parameter, e))
            | None -> None )
      in
      match simple_expansion_of t with
      | None -> None
      | Some e -> Some (simple_expansion1 e)

    and expansion_of_module_type_expr2 :
        Odoc_model.Lang.ModuleType.expr -> Item.t list option =
     fun t ->
      let rec simple_expansion_of (t : Odoc_model.Lang.ModuleType.expr) =
        match t with
        | Path { p_expansion = None; _ }
        | TypeOf { t_expansion = None; _ }
        | With { w_expansion = None; _ } ->
            None
        | Path { p_expansion = Some e; _ }
        | TypeOf { t_expansion = Some e; _ }
        | With { w_expansion = Some e; _ } ->
            Some e
        | Signature sg -> Some (Signature sg)
        | Functor (f_parameter, e) -> (
            match simple_expansion_of e with
            | Some e -> Some (Functor (f_parameter, e))
            | None -> None )
      in
      match simple_expansion_of t with
      | None -> None
      | Some e -> Some (simple_expansion2 e)

    and module1 :
        Odoc_model.Lang.Signature.recursive ->
        Odoc_model.Lang.Module.t ->
        Item.t =
     fun recursive t ->
      let modname = Paths.Identifier.name t.id in
      let expansion =
        match t.type_ with
        | Alias (_, Some e) -> Some (simple_expansion1 e)
        | Alias (_, None) -> None
        | ModuleType e -> expansion_of_module_type_expr1 e
      in
      let modname, status, expansion =
        match expansion with
        | None -> (O.documentedSrc (O.txt modname), `Default, None)
        | Some items ->
            let doc = Comment.standalone t.doc in
            let status =
              match t.type_ with
              | ModuleType (Signature _) -> `Inline
              | _ -> `Default
            in
            let url = Url.Path.from_identifier t.id in
            let link = path url [ inline @@ Text modname ] in
            let title = modname in
            let header = format_title `Mod (make_name_from_path url) @ doc in
            let page = { Page.items; title; header; url } in
            (O.documentedSrc link, status, Some page)
      in
      let summary = mdexpr_in_decl1 t.id t.type_ in
      let modexpr =
        attach_expansion ~status
          (Syntax1.Type.annotation_separator, "sig", "end")
          expansion summary
      in
      let content =
        let keyword' =
          match recursive with
          | Ordinary | Nonrec -> O.keyword "module"
          | Rec -> O.keyword "module" ++ O.txt " " ++ O.keyword "rec"
          | And -> O.keyword "and"
        in
        O.documentedSrc (keyword' ++ O.txt " ")
        @ modname @ modexpr
        @ O.documentedSrc
            (if Syntax1.Mod.close_tag_semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "module" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    and module2 :
        Odoc_model.Lang.Signature.recursive ->
        Odoc_model.Lang.Module.t ->
        Item.t =
     fun recursive t ->
      let modname = Paths.Identifier.name t.id in
      let expansion =
        match t.type_ with
        | Alias (_, Some e) -> Some (simple_expansion2 e)
        | Alias (_, None) -> None
        | ModuleType e -> expansion_of_module_type_expr2 e
      in
      let modname, status, expansion =
        match expansion with
        | None -> (O.documentedSrc (O.txt modname), `Default, None)
        | Some items ->
            let doc = Comment.standalone t.doc in
            let status =
              match t.type_ with
              | ModuleType (Signature _) -> `Inline
              | _ -> `Default
            in
            let url = Url.Path.from_identifier t.id in
            let link = path url [ inline @@ Text modname ] in
            let title = modname in
            let header = format_title `Mod (make_name_from_path url) @ doc in
            let page = { Page.items; title; header; url } in
            (O.documentedSrc link, status, Some page)
      in
      let summary = mdexpr_in_decl2 t.id t.type_ in
      let modexpr =
        attach_expansion ~status
          (Syntax2.Type.annotation_separator, "sig", "end")
          expansion summary
      in
      let content =
        let keyword' =
          match recursive with
          | Ordinary | Nonrec -> O.keyword "module"
          | Rec -> O.keyword "module" ++ O.txt " " ++ O.keyword "rec"
          | And -> O.keyword "and"
        in
        O.documentedSrc (keyword' ++ O.txt " ")
        @ modname @ modexpr
        @ O.documentedSrc
            (if Syntax2.Mod.close_tag_semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "module" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    and mdexpr_in_decl1 (base : Paths.Identifier.Module.t) md =
      let is_canonical p =
        let i = Paths.Path.Resolved.Module.identifier p in
        i = (base :> Paths.Identifier.Path.Module.t)
      in
      let sig_dotdotdot =
        O.txt Syntax1.Type.annotation_separator
        ++ Syntax1.Mod.open_tag ++ O.txt " ... " ++ Syntax1.Mod.close_tag
      in
      match md with
      | Alias (`Resolved p, _) when is_canonical p -> sig_dotdotdot
      | Alias (p, _) when not Paths.Path.(is_hidden (p :> t)) ->
          O.txt " = " ++ mdexpr1 (base :> Paths.Identifier.Signature.t) md
      | Alias _ -> sig_dotdotdot
      | ModuleType mt -> mty_in_decl1 (base :> Paths.Identifier.Signature.t) mt

    and mdexpr_in_decl2 (base : Paths.Identifier.Module.t) md =
      let is_canonical p =
        let i = Paths.Path.Resolved.Module.identifier p in
        i = (base :> Paths.Identifier.Path.Module.t)
      in
      let sig_dotdotdot =
        O.txt Syntax2.Type.annotation_separator
        ++ Syntax2.Mod.open_tag ++ O.txt " ... " ++ Syntax2.Mod.close_tag
      in
      match md with
      | Alias (`Resolved p, _) when is_canonical p -> sig_dotdotdot
      | Alias (p, _) when not Paths.Path.(is_hidden (p :> t)) ->
          O.txt " = " ++ mdexpr2 (base :> Paths.Identifier.Signature.t) md
      | Alias _ -> sig_dotdotdot
      | ModuleType mt -> mty_in_decl2 (base :> Paths.Identifier.Signature.t) mt

    and extract_path_from_umt ~(default : Paths.Identifier.Signature.t) =
      let open Odoc_model.Lang.ModuleType.U in
      function
      | With (_, umt) -> extract_path_from_umt ~default umt
      | Path (`Resolved r) ->
          ( Paths.Path.Resolved.ModuleType.identifier r
            :> Paths.Identifier.Signature.t )
      | TypeOf { t_desc = ModPath (`Resolved r); _ }
      | TypeOf { t_desc = StructInclude (`Resolved r); _ } ->
          ( Paths.Path.Resolved.Module.identifier r
            :> Paths.Identifier.Signature.t )
      | _ -> default

    and extract_path_from_mt ~(default : Paths.Identifier.Signature.t) =
      let open Odoc_model.Lang.ModuleType in
      function
      | Path { p_path = `Resolved r; _ } ->
          ( Paths.Path.Resolved.ModuleType.identifier r
            :> Paths.Identifier.Signature.t )
      | With { w_expr; _ } -> extract_path_from_umt ~default w_expr
      | TypeOf { t_desc = ModPath (`Resolved r); _ }
      | TypeOf { t_desc = StructInclude (`Resolved r); _ } ->
          ( Paths.Path.Resolved.Module.identifier r
            :> Paths.Identifier.Signature.t )
      | _ -> default

    and mdexpr1 :
        Paths.Identifier.Signature.t -> Odoc_model.Lang.Module.decl -> text =
     fun base -> function
      | Alias (mod_path, _) -> Link.from_path (mod_path :> Paths.Path.t)
      | ModuleType mt -> mty1 (extract_path_from_mt ~default:base mt) mt

    and mdexpr2 :
        Paths.Identifier.Signature.t -> Odoc_model.Lang.Module.decl -> text =
     fun base -> function
      | Alias (mod_path, _) -> Link.from_path (mod_path :> Paths.Path.t)
      | ModuleType mt -> mty2 (extract_path_from_mt ~default:base mt) mt

    and module_type1 (t : Odoc_model.Lang.ModuleType.t) =
      let modname = Paths.Identifier.name t.id in
      let expansion =
        match t.expr with
        | None -> None
        | Some e -> expansion_of_module_type_expr1 e
      in
      let modname, expansion =
        match expansion with
        | None -> (O.documentedSrc @@ O.txt modname, None)
        | Some items ->
            let doc = Comment.standalone t.doc in
            let url = Url.Path.from_identifier t.id in
            let link = path url [ inline @@ Text modname ] in
            let title = modname in
            let header = format_title `Mty (make_name_from_path url) @ doc in
            let page = { Page.items; title; header; url } in
            (O.documentedSrc link, Some page)
      in
      let summary =
        match t.expr with
        | None -> O.noop
        | Some expr ->
            O.txt " = " ++ mty1 (t.id :> Paths.Identifier.Signature.t) expr
      in
      let mty = attach_expansion (" = ", "sig", "end") expansion summary in
      let content =
        O.documentedSrc
          (O.keyword "module" ++ O.txt " " ++ O.keyword "type" ++ O.txt " ")
        @ modname @ mty
        @ O.documentedSrc
            (if Syntax1.Mod.close_tag_semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "module-type" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    and module_type2 (t : Odoc_model.Lang.ModuleType.t) =
      let modname = Paths.Identifier.name t.id in
      let expansion =
        match t.expr with
        | None -> None
        | Some e -> expansion_of_module_type_expr2 e
      in
      let modname, expansion =
        match expansion with
        | None -> (O.documentedSrc @@ O.txt modname, None)
        | Some items ->
            let doc = Comment.standalone t.doc in
            let url = Url.Path.from_identifier t.id in
            let link = path url [ inline @@ Text modname ] in
            let title = modname in
            let header = format_title `Mty (make_name_from_path url) @ doc in
            let page = { Page.items; title; header; url } in
            (O.documentedSrc link, Some page)
      in
      let summary =
        match t.expr with
        | None -> O.noop
        | Some expr ->
            O.txt " = " ++ mty2 (t.id :> Paths.Identifier.Signature.t) expr
      in
      let mty = attach_expansion (" = ", "sig", "end") expansion summary in
      let content =
        O.documentedSrc
          (O.keyword "module" ++ O.txt " " ++ O.keyword "type" ++ O.txt " ")
        @ modname @ mty
        @ O.documentedSrc
            (if Syntax2.Mod.close_tag_semicolon then O.txt ";" else O.noop)
      in
      let kind = Some "module-type" in
      let anchor = path_to_id t.id in
      let doc = Comment.first_to_ir t.doc in
      Item.Declaration { kind; anchor; doc; content }

    and umty_hidden : Odoc_model.Lang.ModuleType.U.expr -> bool = function
      | Path p -> Paths.Path.(is_hidden (p :> t))
      | With (_, expr) -> umty_hidden expr
      | TypeOf { t_desc = ModPath m; _ }
      | TypeOf { t_desc = StructInclude m; _ } ->
          Paths.Path.(is_hidden (m :> t))
      | Signature _ -> false

    and mty_hidden : Odoc_model.Lang.ModuleType.expr -> bool = function
      | Path { p_path = mty_path; _ } -> Paths.Path.(is_hidden (mty_path :> t))
      | With { w_expr; _ } -> umty_hidden w_expr
      | TypeOf { t_desc = ModPath m; _ }
      | TypeOf { t_desc = StructInclude m; _ } ->
          Paths.Path.(is_hidden (m :> t))
      | _ -> false

    and mty_with1 base subs expr =
      umty1 base expr ++ O.txt " " ++ O.keyword "with" ++ O.txt " "
      ++ O.list
           ~sep:(O.txt " " ++ O.keyword "and" ++ O.txt " ")
           ~f:(substitution1 base) subs

    and mty_with2 base subs expr =
      umty2 base expr ++ O.txt " " ++ O.keyword "with" ++ O.txt " "
      ++ O.list
           ~sep:(O.txt " " ++ O.keyword "and" ++ O.txt " ")
           ~f:(substitution2 base) subs

    and mty_typeof t_desc =
      match t_desc with
      | Odoc_model.Lang.ModuleType.ModPath m ->
          O.keyword "module" ++ O.txt " " ++ O.keyword "type" ++ O.txt " "
          ++ O.keyword "of" ++ O.txt " "
          ++ Link.from_path (m :> Paths.Path.t)
      | StructInclude m ->
          O.keyword "module" ++ O.txt " " ++ O.keyword "type" ++ O.txt " "
          ++ O.keyword "of" ++ O.txt " " ++ O.keyword "struct" ++ O.txt " "
          ++ O.keyword "include" ++ O.txt " "
          ++ Link.from_path (m :> Paths.Path.t)
          ++ O.txt " " ++ O.keyword "end"

    and umty1 :
        Paths.Identifier.Signature.t ->
        Odoc_model.Lang.ModuleType.U.expr ->
        text =
     fun base m ->
      match m with
      | Path p -> Link.from_path (p :> Paths.Path.t)
      | With (subs, expr) -> mty_with1 base subs expr
      | TypeOf { t_desc; _ } -> mty_typeof t_desc
      | Signature _ ->
          Syntax1.Mod.open_tag ++ O.txt " ... " ++ Syntax1.Mod.close_tag

    and umty2 :
        Paths.Identifier.Signature.t ->
        Odoc_model.Lang.ModuleType.U.expr ->
        text =
     fun base m ->
      match m with
      | Path p -> Link.from_path (p :> Paths.Path.t)
      | With (subs, expr) -> mty_with2 base subs expr
      | TypeOf { t_desc; _ } -> mty_typeof t_desc
      | Signature _ ->
          Syntax2.Mod.open_tag ++ O.txt " ... " ++ Syntax2.Mod.close_tag

    and mty1 :
        Paths.Identifier.Signature.t -> Odoc_model.Lang.ModuleType.expr -> text
        =
     fun base m ->
      if mty_hidden m then
        Syntax1.Mod.open_tag ++ O.txt " ... " ++ Syntax1.Mod.close_tag
      else
        match m with
        | Path { p_path = mty_path; _ } ->
            Link.from_path (mty_path :> Paths.Path.t)
        | Functor (Unit, expr) ->
            (if Syntax1.Mod.functor_keyword then O.keyword "functor" else O.noop)
            ++ O.txt " () " ++ Syntax1.Type.arrow ++ O.txt " " ++ mty1 base expr
        | Functor (Named arg, expr) ->
            let arg_expr = arg.expr in
            let stop_before = expansion_of_module_type_expr1 arg_expr = None in
            let name =
              let open Odoc_model.Lang.FunctorParameter in
              let name = Paths.Identifier.name arg.id in
              match
                Url.from_identifier ~stop_before (arg.id :> Paths.Identifier.t)
              with
              | Error _ -> O.txt name
              | Ok href -> resolved href [ inline @@ Text name ]
            in
            (if Syntax1.Mod.functor_keyword then O.keyword "functor" else O.noop)
            ++ O.txt " (" ++ name
            ++ O.txt Syntax1.Type.annotation_separator
            ++ mty1 base arg_expr ++ O.txt ")" ++ O.txt " "
            ++ Syntax1.Type.arrow ++ O.txt " " ++ mty1 base expr
        | With { w_substitutions; w_expr; _ } ->
            mty_with1 base w_substitutions w_expr
        | TypeOf { t_desc; _ } -> mty_typeof t_desc
        | Signature _ ->
            Syntax1.Mod.open_tag ++ O.txt " ... " ++ Syntax1.Mod.close_tag

    and mty2 :
        Paths.Identifier.Signature.t -> Odoc_model.Lang.ModuleType.expr -> text
        =
     fun base m ->
      if mty_hidden m then
        Syntax2.Mod.open_tag ++ O.txt " ... " ++ Syntax2.Mod.close_tag
      else
        match m with
        | Path { p_path = mty_path; _ } ->
            Link.from_path (mty_path :> Paths.Path.t)
        | Functor (Unit, expr) ->
            (if Syntax2.Mod.functor_keyword then O.keyword "functor" else O.noop)
            ++ O.txt " () " ++ Syntax2.Type.arrow ++ O.txt " " ++ mty2 base expr
        | Functor (Named arg, expr) ->
            let arg_expr = arg.expr in
            let stop_before = expansion_of_module_type_expr2 arg_expr = None in
            let name =
              let open Odoc_model.Lang.FunctorParameter in
              let name = Paths.Identifier.name arg.id in
              match
                Url.from_identifier ~stop_before (arg.id :> Paths.Identifier.t)
              with
              | Error _ -> O.txt name
              | Ok href -> resolved href [ inline @@ Text name ]
            in
            (if Syntax2.Mod.functor_keyword then O.keyword "functor" else O.noop)
            ++ O.txt " (" ++ name
            ++ O.txt Syntax2.Type.annotation_separator
            ++ mty2 base arg_expr ++ O.txt ")" ++ O.txt " "
            ++ Syntax2.Type.arrow ++ O.txt " " ++ mty2 base expr
        | With { w_substitutions; w_expr; _ } ->
            mty_with2 base w_substitutions w_expr
        | TypeOf { t_desc; _ } -> mty_typeof t_desc
        | Signature _ ->
            Syntax2.Mod.open_tag ++ O.txt " ... " ++ Syntax2.Mod.close_tag

    and mty_in_decl1 :
        Paths.Identifier.Signature.t -> Odoc_model.Lang.ModuleType.expr -> text
        =
     fun base -> function
      | (Path _ | Signature _ | With _ | TypeOf _) as m ->
          O.txt Syntax1.Type.annotation_separator ++ mty1 base m
      | Functor _ as m when not Syntax1.Mod.functor_contraction ->
          O.txt Syntax1.Type.annotation_separator ++ mty1 base m
      | Functor (arg, expr) ->
          let text_arg =
            match arg with
            | Unit -> O.txt "()"
            | Named arg ->
                let arg_expr = arg.expr in
                let stop_before =
                  expansion_of_module_type_expr1 arg_expr = None
                in
                let name =
                  let open Odoc_model.Lang.FunctorParameter in
                  let name = Paths.Identifier.name arg.id in
                  match
                    Url.from_identifier ~stop_before
                      (arg.id :> Paths.Identifier.t)
                  with
                  | Error _ -> O.txt name
                  | Ok href -> resolved href [ inline @@ Text name ]
                in
                O.txt "(" ++ name
                ++ O.txt Syntax1.Type.annotation_separator
                ++ mty1 base arg.expr ++ O.txt ")"
          in
          O.txt " " ++ text_arg ++ mty_in_decl1 base expr

    and mty_in_decl2 :
        Paths.Identifier.Signature.t -> Odoc_model.Lang.ModuleType.expr -> text
        =
     fun base -> function
      | (Path _ | Signature _ | With _ | TypeOf _) as m ->
          O.txt Syntax2.Type.annotation_separator ++ mty2 base m
      | Functor _ as m when not Syntax2.Mod.functor_contraction ->
          O.txt Syntax2.Type.annotation_separator ++ mty2 base m
      | Functor (arg, expr) ->
          let text_arg =
            match arg with
            | Unit -> O.txt "()"
            | Named arg ->
                let arg_expr = arg.expr in
                let stop_before =
                  expansion_of_module_type_expr2 arg_expr = None
                in
                let name =
                  let open Odoc_model.Lang.FunctorParameter in
                  let name = Paths.Identifier.name arg.id in
                  match
                    Url.from_identifier ~stop_before
                      (arg.id :> Paths.Identifier.t)
                  with
                  | Error _ -> O.txt name
                  | Ok href -> resolved href [ inline @@ Text name ]
                in
                O.txt "(" ++ name
                ++ O.txt Syntax2.Type.annotation_separator
                ++ mty2 base arg.expr ++ O.txt ")"
          in
          O.txt " " ++ text_arg ++ mty_in_decl2 base expr

    (* TODO : Centralize the list juggling for type parameters *)
    and type_expr_in_subst1 ~base td typath =
      let typath = Link.from_fragment ~base typath in
      match td.Lang.TypeDecl.Equation.params with
      | [] -> typath
      | l -> Syntax1.Type.handle_substitution_params typath (format_params1 l)

    and type_expr_in_subst2 ~base td typath =
      let typath = Link.from_fragment ~base typath in
      match td.Lang.TypeDecl.Equation.params with
      | [] -> typath
      | l -> Syntax2.Type.handle_substitution_params typath (format_params2 l)

    and substitution1 :
        Paths.Identifier.Signature.t ->
        Odoc_model.Lang.ModuleType.substitution ->
        text =
     fun base -> function
      | ModuleEq (frag_mod, md) ->
          O.keyword "module" ++ O.txt " "
          ++ Link.from_fragment ~base (frag_mod :> Paths.Fragment.t)
          ++ O.txt " = " ++ mdexpr1 base md
      | TypeEq (frag_typ, td) ->
          O.keyword "type" ++ O.txt " "
          ++ type_expr_in_subst1 ~base td (frag_typ :> Paths.Fragment.t)
          ++ fst (format_manifest1 td)
          ++ format_constraints1
               td.Odoc_model.Lang.TypeDecl.Equation.constraints
      | ModuleSubst (frag_mod, mod_path) ->
          O.keyword "module" ++ O.txt " "
          ++ Link.from_fragment ~base (frag_mod :> Paths.Fragment.t)
          ++ O.txt " := "
          ++ Link.from_path (mod_path :> Paths.Path.t)
      | TypeSubst (frag_typ, td) -> (
          O.keyword "type" ++ O.txt " "
          ++ type_expr_in_subst1 ~base td (frag_typ :> Paths.Fragment.t)
          ++ O.txt " := "
          ++
          match td.Lang.TypeDecl.Equation.manifest with
          | None -> assert false (* cf loader/cmti *)
          | Some te -> type_expr1 te )

    and substitution2 :
        Paths.Identifier.Signature.t ->
        Odoc_model.Lang.ModuleType.substitution ->
        text =
     fun base -> function
      | ModuleEq (frag_mod, md) ->
          O.keyword "module" ++ O.txt " "
          ++ Link.from_fragment ~base (frag_mod :> Paths.Fragment.t)
          ++ O.txt " = " ++ mdexpr2 base md
      | TypeEq (frag_typ, td) ->
          O.keyword "type" ++ O.txt " "
          ++ type_expr_in_subst2 ~base td (frag_typ :> Paths.Fragment.t)
          ++ fst (format_manifest2 td)
          ++ format_constraints2
               td.Odoc_model.Lang.TypeDecl.Equation.constraints
      | ModuleSubst (frag_mod, mod_path) ->
          O.keyword "module" ++ O.txt " "
          ++ Link.from_fragment ~base (frag_mod :> Paths.Fragment.t)
          ++ O.txt " := "
          ++ Link.from_path (mod_path :> Paths.Path.t)
      | TypeSubst (frag_typ, td) -> (
          O.keyword "type" ++ O.txt " "
          ++ type_expr_in_subst2 ~base td (frag_typ :> Paths.Fragment.t)
          ++ O.txt " := "
          ++
          match td.Lang.TypeDecl.Equation.manifest with
          | None -> assert false (* cf loader/cmti *)
          | Some te -> type_expr2 te )

    and include1 (t : Odoc_model.Lang.Include.t) =
      let decl_hidden =
        match t.decl with
        | Alias p -> Paths.Path.(is_hidden (p :> t))
        | ModuleType mty -> umty_hidden mty
      in
      let status =
        let is_open_tag element =
          element.Odoc_model.Location_.value = `Tag `Open
        in
        let is_closed_tag element =
          element.Odoc_model.Location_.value = `Tag `Closed
        in
        if t.inline || decl_hidden then `Inline
        else if List.exists is_open_tag t.doc then `Open
        else if List.exists is_closed_tag t.doc then `Closed
        else `Default
      in

      let include_decl =
        match t.decl with
        | Odoc_model.Lang.Include.Alias mod_path ->
            Link.from_path (mod_path :> Paths.Path.t)
        | ModuleType mt -> umty1 (extract_path_from_umt ~default:t.parent mt) mt
      in

      let content = signature t.expansion.content in
      let summary =
        O.render
          ( O.keyword "include" ++ O.txt " " ++ include_decl
          ++ if Syntax1.Mod.include_semicolon then O.keyword ";" else O.noop )
      in
      let content = { Include.content; status; summary } in
      let kind = Some "include" in
      let anchor = None in
      let doc = Comment.first_to_ir t.doc in
      Item.Include { kind; anchor; doc; content }

    and include2 (t : Odoc_model.Lang.Include.t) =
      let decl_hidden =
        match t.decl with
        | Alias p -> Paths.Path.(is_hidden (p :> t))
        | ModuleType mty -> umty_hidden mty
      in
      let status =
        let is_open_tag element =
          element.Odoc_model.Location_.value = `Tag `Open
        in
        let is_closed_tag element =
          element.Odoc_model.Location_.value = `Tag `Closed
        in
        if t.inline || decl_hidden then `Inline
        else if List.exists is_open_tag t.doc then `Open
        else if List.exists is_closed_tag t.doc then `Closed
        else `Default
      in

      let include_decl =
        match t.decl with
        | Odoc_model.Lang.Include.Alias mod_path ->
            Link.from_path (mod_path :> Paths.Path.t)
        | ModuleType mt -> umty2 (extract_path_from_umt ~default:t.parent mt) mt
      in

      let content = signature t.expansion.content in
      let summary =
        O.render
          ( O.keyword "include" ++ O.txt " " ++ include_decl
          ++ if Syntax2.Mod.include_semicolon then O.keyword ";" else O.noop )
      in
      let content = { Include.content; status; summary } in
      let kind = Some "include" in
      let anchor = None in
      let doc = Comment.first_to_ir t.doc in
      Item.Include { kind; anchor; doc; content }
  end

  open Module

  module Page : sig
    val compilation_unit : Lang.Compilation_unit.t -> Page.t

    val page : Lang.Page.t -> Page.t
  end = struct
    let pack : Odoc_model.Lang.Compilation_unit.Packed.t -> Item.t list =
     fun t ->
      let open Odoc_model.Lang in
      let f x =
        let id = x.Compilation_unit.Packed.id in
        let modname = Paths.Identifier.name id in
        let md_def =
          O.keyword "module" ++ O.txt " " ++ O.txt modname ++ O.txt " = "
          ++ Link.from_path (x.path :> Paths.Path.t)
        in
        let content = O.documentedSrc md_def in
        let anchor =
          Utils.option_of_result
          @@ Url.Anchor.from_identifier (id :> Paths.Identifier.t)
        in
        let kind = Some "modules" in
        let doc = [] in
        let decl = { Item.anchor; content; kind; doc } in
        Item.Declaration decl
      in
      List.map f t

    let compilation_unit (t : Odoc_model.Lang.Compilation_unit.t) : Page.t =
      let title = Paths.Identifier.name t.id in
      let header = format_title `Mod title @ Comment.standalone t.doc in
      let url = Url.Path.from_identifier t.id in
      let items =
        match t.content with
        | Module sign -> signature sign
        | Pack packed -> pack packed
      in
      { Page.title; header; items; url }

    let page (t : Odoc_model.Lang.Page.t) : Page.t =
      let name = match t.name with `Page (_, name) -> name in
      let title = Odoc_model.Names.PageName.to_string name in
      let url = Url.Path.from_identifier t.name in
      let header, items = Sectioning.docs t.content in
      { Page.title; header; items; url }
  end

  include Page
end
