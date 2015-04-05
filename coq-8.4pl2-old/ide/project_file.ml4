type target =
  | ML of string (* ML file : foo.ml -> (ML "foo.ml") *)
  | MLI of string (* MLI file : foo.mli -> (MLI "foo.mli") *)
  | ML4 of string (* ML4 file : foo.ml4 -> (ML4 "foo.ml4") *)
  | MLLIB of string (* MLLIB file : foo.mllib -> (MLLIB "foo.mllib") *)
  | MLPACK of string (* MLLIB file : foo.mlpack -> (MLLIB "foo.mlpack") *)
  | V of string  (* V file : foo.v -> (V "foo") *)
  | Arg of string
  | Special of string * string * string (* file, dependencies, command *)
  | Subdir of string
  | Def of string * string (* X=foo -> Def ("X","foo") *)
  | Include of string
  | RInclude of string * string (* -R physicalpath logicalpath *)

type install =
  | NoInstall
  | TraditionalInstall
  | UserInstall
  | UnspecInstall

exception Parsing_error
let rec parse_string = parser
  | [< '' ' | '\n' | '\t' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string s)
  | [< >] -> ""
and parse_string2 = parser
  | [< ''"' >] -> ""
  | [< 'c; s >] -> (String.make 1 c)^(parse_string2 s)
and parse_skip_comment = parser
  | [< ''\n'; s >] -> s
  | [< 'c; s >] -> parse_skip_comment s
  | [< >] -> [< >]
and parse_args = parser
  | [< '' ' | '\n' | '\t'; s >] -> parse_args s
  | [< ''#'; s >] -> parse_args (parse_skip_comment s)
  | [< ''"'; str = parse_string2; s >] -> ("" ^ str) :: parse_args s
  | [< 'c; str = parse_string; s >] -> ((String.make 1 c) ^ str) :: (parse_args s)
  | [< >] -> []


let parse f =
  let c = open_in f in
  let res = parse_args (Stream.of_channel c) in
    close_in c;
    res

let rec process_cmd_line orig_dir ((project_file,makefile,install,opt) as opts) l = function
  | [] -> opts,List.rev l
  | ("-h"|"--help") :: _ ->
    raise Parsing_error
  | ("-no-opt"|"-byte") :: r ->
    process_cmd_line orig_dir (project_file,makefile,install,false) l r
  | ("-full"|"-opt") :: r ->
    process_cmd_line orig_dir (project_file,makefile,install,true) l r
  | "-impredicative-set" :: r ->
    Minilib.safe_prerr_endline "Please now use \"-arg -impredicative-set\" instead of \"-impredicative-set\" alone to be more uniform.";
    process_cmd_line orig_dir opts (Arg "-impredicative-set" :: l) r
  | "-no-install" :: r ->
    Minilib.safe_prerr_endline "Option -no-install is deprecated. Use \"-install none\" instead";
    process_cmd_line orig_dir (project_file,makefile,NoInstall,opt) l r
  | "-install" :: d :: r ->
    if install <> UnspecInstall then Minilib.safe_prerr_endline "Warning: -install sets more than once.";
    let install =
      match d with
	| "user" -> UserInstall
	| "none" -> NoInstall
	| "global" -> TraditionalInstall
	| _ -> Minilib.safe_prerr_endline (String.concat "" ["Warning: invalid option '"; d; "' passed to -install."]);
          install
    in
    process_cmd_line orig_dir (project_file,makefile,install,opt) l r
  | "-custom" :: com :: dependencies :: file :: r ->
    process_cmd_line orig_dir opts (Special (file,dependencies,com) :: l) r
  | "-I" :: d :: r ->
    process_cmd_line orig_dir opts ((Include (Minilib.correct_path d orig_dir)) :: l) r
  | "-R" :: p :: lp :: r ->
    process_cmd_line orig_dir opts (RInclude (Minilib.correct_path p orig_dir,lp) :: l) r
  | ("-I"|"-custom") :: _ ->
    raise Parsing_error
  | "-f" :: file :: r ->
    let file = Minilib.remove_path_dot (Minilib.correct_path file orig_dir) in
    let () = match project_file with
      | None -> ()
      | Some _ -> Minilib.safe_prerr_endline
	"Warning: Several features will not work with multiple project files."
    in
    let (opts',l') = process_cmd_line (Filename.dirname file) (Some file,makefile,install,opt) l (parse file) in
      process_cmd_line orig_dir opts' l' r
  | ["-f"] ->
    raise Parsing_error
  | "-o" :: file :: r ->
      begin try
	let _ = String.index file '/' in
	  raise Parsing_error
      with Not_found ->
	let () = match makefile with
	  |None -> ()
	  |Some f ->
	     Minilib.safe_prerr_endline ("Warning: Only one output file is genererated. "^f^" will not be.")
	in process_cmd_line orig_dir (project_file,Some file,install,opt) l r
      end
  | v :: "=" :: def :: r ->
    process_cmd_line orig_dir opts (Def (v,def) :: l) r
  | "-arg" :: a :: r ->
    process_cmd_line orig_dir opts (Arg a :: l) r
  | f :: r ->
      let f = Minilib.correct_path f orig_dir in
	process_cmd_line orig_dir opts ((
          if Filename.check_suffix f ".v" then V f
	  else if (Filename.check_suffix f ".ml") then ML f
	  else if (Filename.check_suffix f ".ml4") then ML4 f
	  else if (Filename.check_suffix f ".mli") then MLI f
	  else if (Filename.check_suffix f ".mllib") then MLLIB f
	  else if (Filename.check_suffix f ".mlpack") then MLPACK f
	  else Subdir f) :: l) r

let rec post_canonize f =
  if Filename.basename f = Filename.current_dir_name
  then let dir = Filename.dirname f in
    if dir = Filename.current_dir_name then f else post_canonize dir
  else f

(* Return: ((v,(mli,ml4,ml,mllib,mlpack),special,subdir),(i_inc,r_inc),(args,defs)) *)
let split_arguments =
  let rec aux = function
  | V n :: r ->
	let (v,m,o,s),i,d = aux r in ((Minilib.remove_path_dot n::v,m,o,s),i,d)
  | ML n :: r ->
      let (v,(mli,ml4,ml,mllib,mlpack),o,s),i,d = aux r in
      ((v,(mli,ml4,Minilib.remove_path_dot n::ml,mllib,mlpack),o,s),i,d)
  | MLI n :: r ->
      let (v,(mli,ml4,ml,mllib,mlpack),o,s),i,d = aux r in
      ((v,(Minilib.remove_path_dot n::mli,ml4,ml,mllib,mlpack),o,s),i,d)
  | ML4 n :: r ->
      let (v,(mli,ml4,ml,mllib,mlpack),o,s),i,d = aux r in
      ((v,(mli,Minilib.remove_path_dot n::ml4,ml,mllib,mlpack),o,s),i,d)
  | MLLIB n :: r ->
      let (v,(mli,ml4,ml,mllib,mlpack),o,s),i,d = aux r in
      ((v,(mli,ml4,ml,Minilib.remove_path_dot n::mllib,mlpack),o,s),i,d)
  | MLPACK n :: r ->
      let (v,(mli,ml4,ml,mllib,mlpack),o,s),i,d = aux r in
      ((v,(mli,ml4,ml,mllib,Minilib.remove_path_dot n::mlpack),o,s),i,d)
  | Special (n,dep,c) :: r ->
      let (v,m,o,s),i,d = aux r in ((v,m,(n,dep,c)::o,s),i,d)
  | Subdir n :: r ->
      let (v,m,o,s),i,d = aux r in ((v,m,o,n::s),i,d)
  | Include p :: r ->
      let t,(i,r),d = aux r in (t,((Minilib.remove_path_dot (post_canonize p),
				    Minilib.canonical_path_name p)::i,r),d)
  | RInclude (p,l) :: r ->
      let t,(i,r),d = aux r in (t,(i,(Minilib.remove_path_dot (post_canonize p),l,
				      Minilib.canonical_path_name p)::r),d)
  | Def (v,def) :: r ->
      let t,i,(args,defs) = aux r in (t,i,(args,(v,def)::defs))
  | Arg a :: r ->
      let t,i,(args,defs) = aux r in (t,i,(a::args,defs))
  | [] -> ([],([],[],[],[],[]),[],[]),([],[]),([],[])
  in aux

let read_project_file f =
  split_arguments
    (snd (process_cmd_line (Filename.dirname f) (Some f, None, NoInstall, true) [] (parse f)))

let args_from_project file project_files default_name =
  let is_f = Minilib.same_file file in
  let contains_file dir =
      List.exists (fun x -> is_f (Minilib.correct_path x dir))
  in
  let build_cmd_line i_inc r_inc args =
    List.fold_right (fun (_,i) o -> "-I" :: i :: o) i_inc
      (List.fold_right (fun (_,l,p) o -> "-R" :: p :: l :: o) r_inc
	 (List.fold_right (fun a o -> parse_args (Stream.of_string a) @ o) args []))
  in try
      let (_,(_,(i_inc,r_inc),(args,_))) =
	List.find (fun (dir,((v_files,_,_,_),_,_)) ->
		     contains_file dir v_files) project_files in
	build_cmd_line i_inc r_inc args
    with Not_found ->
      let rec find_project_file dir = try
	let ((v_files,_,_,_),(i_inc,r_inc),(args,_)) =
	  read_project_file (Filename.concat dir default_name) in
	  if contains_file dir v_files
	  then build_cmd_line i_inc r_inc args
	  else let newdir = Filename.dirname dir in
	    Minilib.safe_prerr_endline newdir;
	    if dir = newdir then [] else find_project_file newdir
      with Sys_error s ->
	let newdir = Filename.dirname dir in
	  if dir = newdir then [] else find_project_file newdir
      in find_project_file (Filename.dirname file)
