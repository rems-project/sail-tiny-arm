(lang dune 3.21)
(name rocq-sail-tiny-arm)
(using rocq 0.11)

(source (github rems-project/sail-tiny-arm))
(license "BSD-3-Clause")
(authors
  "Shaked Flur"
  "Brian Campbell"
  "Alasdair Armstrong"
  "Thibaut Pérami"
  "Nils Lauermann"
)
(maintainers "Sail Devs <cl-sail-dev@lists.cam.ac.uk>")
; Arm architecture version followed by a dash and a single incrementing number
(version "9.4-4")

(package
 (name rocq-sail-tiny-arm)
 (synopsis " A very simplified and cut down version of the Arm ISA sail specification, handwritten")
 (depends
  (rocq-core (>= 9.0))
  (rocq-stdlib (>= 9.0))
  (sail (>= 0.20.1))
  sail_coq_backend
  sail_lem_backend
  sail_c_backend
  sail_lean_backend
  sail_smt_backend
  sail_sv_backend
  sail_ocaml_backend
  sail_latex_backend
  sail_output
  (rocq-stdpp (>= 1.10.0))
  (rocq-stdpp-bitvector (>= 1.10.0))
  (rocq-sail-stdpp (>= 0.20.1))
  (coq-record-update (>= 0.3.4))
 )
)

(generate_opam_files)
