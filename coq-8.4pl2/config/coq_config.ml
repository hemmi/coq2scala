(* DO NOT EDIT THIS FILE: automatically generated by ../configure *)

let local = false
let coqrunbyteflags = "-dllib -lcoqrun -dllpath '/usr/local/lib/coq'"
let coqlib = Some "/usr/local/lib/coq"
let configdir = None
let datadir = None
let docdir = "/usr/local/share/doc/coq"
let ocaml = "ocaml"
let ocamlc = "ocamlc"
let ocamlopt = "ocamlopt"
let ocamlmklib = "ocamlmklib"
let ocamldep = "ocamldep"
let ocamldoc = "ocamldoc"
let ocamlyacc = "ocamlyacc"
let ocamllex = "ocamllex"
let camlbin = "/usr/local/bin"
let camllib = "/usr/local/lib/ocaml"
let camlp4 = "camlp5"
let camlp4o = "camlp5o"
let camlp4bin = "/usr/local/bin"
let camlp4lib = "+camlp5"
let camlp4compat = "-loc loc"
let coqideincl = ""
let cflags = "-fno-defer-pop -Wall -Wno-unused"
let best = "byte"
let arch = "Linux"
let has_coqide = "no"
let gtk_platform = `X11
let has_natdynlink = true
let natdynlinkflag = "true"
let osdeplibs = "-cclib -lunix"
let version = "8.4pl2"
let caml_version = "3.12.0"
let date = "September 2014"
let compile_date = "Sep 16 2014 21:39:27"
let vo_magic_number = 08400
let state_magic_number = 58400
let exec_extension = ""
let with_geoproof = ref false
let browser = "firefox -remote \"OpenURL(%s,new-tab)\" || firefox %s &"
let wwwcoq = "http://coq.inria.fr/"
let wwwrefman = wwwcoq ^ "distrib/" ^ version ^ "/refman/"
let wwwstdlib = wwwcoq ^ "distrib/" ^ version ^ "/stdlib/"
let localwwwrefman = "file:/" ^ docdir ^ "html/refman"

let theories_dirs = [
"Arith";
"Bool";
"Classes";
"FSets";
"Init";
"Lists";
"Logic";
"MSets";
"NArith";
"Numbers";
"Numbers/Integer";
"Numbers/Integer/SpecViaZ";
"Numbers/Integer/NatPairs";
"Numbers/Integer/Abstract";
"Numbers/Integer/Binary";
"Numbers/Integer/BigZ";
"Numbers/Natural";
"Numbers/Natural/SpecViaZ";
"Numbers/Natural/Abstract";
"Numbers/Natural/Binary";
"Numbers/Natural/Peano";
"Numbers/Natural/BigN";
"Numbers/Cyclic";
"Numbers/Cyclic/Abstract";
"Numbers/Cyclic/DoubleCyclic";
"Numbers/Cyclic/ZModulo";
"Numbers/Cyclic/Int31";
"Numbers/Rational";
"Numbers/Rational/BigQ";
"Numbers/Rational/SpecViaQ";
"Numbers/NatInt";
"PArith";
"Program";
"QArith";
"Reals";
"Relations";
"Setoids";
"Sets";
"Sorting";
"Strings";
"Structures";
"Unicode";
"Vectors";
"Wellfounded";
"ZArith";
]
let plugins_dirs = [
"cc";
"decl_mode";
"extraction";
"field";
"firstorder";
"fourier";
"funind";
"interface";
"micromega";
"nsatz";
"omega";
"quote";
"ring";
"romega";
"rtauto";
"setoid_ring";
"subtac";
"subtac/test";
"syntax";
"xml";
]