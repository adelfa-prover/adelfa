module F = Filename
module U = Unix

exception InvalidDirectory

let adelfa_root_name = "Adelfa"
let example_dir = "examples/"
let tar_name = "adelfa.tar"
let cram_dir = "test/crams/"
let excluded = [ "regressions"; "README"; "dune" ]
let tar_excluded = [ "test/crams/"; "**/*~" ]

let tar_included =
  [ "Makefile"
  ; "README"
  ; "system_description.txt"
  ; "system_reference.txt"
  ; "dune-project"
  ; "bin/"
  ; "src/"
  ; "test/"
  ; "PG"
  ; "examples/"
  ]
;;

let package_to_tar () =
  let excludes = List.map (fun x -> "--exclude=" ^ x) tar_excluded in
  let args = [ "-cf"; tar_name ] @ excludes @ tar_included in
  let cmd = F.quote_command "tar" args in
  let _ = U.system cmd in
  ()
;;

let rec take_up_to f l =
  match l with
  | [] -> []
  | x :: xs -> if f x then x :: xs else x :: take_up_to f xs
;;

let copy_file src dest =
  let ifd = U.openfile src [ U.O_RDONLY ] 0o644 in
  let size = (U.stat src).st_size in
  let content = Bytes.make size '\x00' in
  let _ = U.read ifd content 0 size in
  U.close ifd;
  let b = F.dirname dest in
  let _ = U.system (F.quote_command "mkdir" [ "-p"; b ]) in
  let ofd = U.openfile dest [ U.O_WRONLY; U.O_TRUNC; U.O_CREAT ] 0o644 in
  let _ = U.write ofd content 0 size in
  U.fsync ofd;
  U.close ofd
;;

let get_crams cram_root =
  let rec aux dir =
    if not (Sys.is_directory dir)
    then [ dir ]
    else (
      let members =
        Sys.readdir dir
        |> Array.to_list
        |> List.filter (fun m -> not (List.mem m excluded))
        |> List.map (fun f -> F.concat dir f)
        |> List.filter (fun f ->
             Sys.is_directory f || not (String.ends_with ~suffix:".t" f))
      in
      List.concat_map aux members)
  in
  List.concat_map aux [ cram_root ]
;;

let cram_to_example path =
  Str.global_substitute (Str.regexp_string cram_dir) (fun _ -> "") path
  |> Str.global_substitute (Str.regexp "\\.t") (fun _ -> "")
  |> F.concat example_dir
;;

let get_adelfa_dir () =
  let paths = U.getcwd () |> Str.split (Str.regexp_string F.dir_sep) in
  if List.mem adelfa_root_name paths
  then
    take_up_to (fun x -> x = adelfa_root_name) paths
    |> List.map (fun s -> "/" ^ s)
    |> String.concat ""
  else raise InvalidDirectory
;;

let () =
  let root = get_adelfa_dir () in
  let cram_files = get_crams cram_dir in
  let transformations = List.map (fun cram -> cram, cram_to_example cram) cram_files in
  let absolute_paths =
    List.map (fun (f, t) -> F.concat root f, F.concat root t) transformations
  in
  List.iter (fun (f, t) -> copy_file f t) absolute_paths;
  package_to_tar ();
  flush_all ()
;;
